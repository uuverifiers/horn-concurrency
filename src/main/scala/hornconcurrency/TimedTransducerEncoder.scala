/**
 * Copyright (c) 2026 Traton AB. All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 * 
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * 
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package hornconcurrency

import ap.parser._
import ap.theories.rationals.Rationals
import ap.theories.ADT
import ap.types.MonoSortedPredicate
import lazabs.horn.Util
import lazabs.horn.bottomup.{HornClauses, HornPredAbs}
import org.scalactic.PrettyMethods
import hornconcurrency.VerificationLoop.prettyPrint
import lazabs.horn.global.HornClause
import javax.lang.model.`type`.NoType



object TimedTransducerEncoder {
    import HornClauses._
    import IExpression._
    import System._
    import SignalSystem._
    import Rationals.{geq, leq, gt, minus, int2ring => toRat}
    import ADT._
    import ADT.BoolADT.{True, False}
    import TimedTransducer.{Location, Formula}

    case class EncodedTransducer(name: String,
                                 adt: ADT,
                                 initialLocation: IFunApp,
                                 src: ConstantTerm,
                                 target: ConstantTerm,
                                 inputLabelTerms: Seq[ConstantTerm],
                                 outputLabelsTerms: Seq[ConstantTerm],
                                 clockTerms: Seq[ConstantTerm],
                                 newClockTerms: Seq[ConstantTerm],
                                 resetFlags: Seq[ConstantTerm],
                                 invPred: Predicate,
                                 invariantClauses: Seq[(HornClauses.Clause, NoSync.type)],
                                 stepPred: Predicate,
                                 stepClauses: Seq[(HornClauses.Clause, NoSync.type)],
                                acceptPred: Predicate,
                                acceptClauses: Seq[HornClauses.Clause]
                                 )

    // global clock
    val C = Rationals.dom.newConstant("C")

    def encodeTransducerEquation(teq : TimedTransducer.TimedTransducerEquation): 
        Seq[(lazabs.horn.bottomup.HornClauses.Clause,
            hornconcurrency.System.NoSync.type)]= {
        
        //Converts sequenctial composition to product, returns a list of all base transducers that should be composed woht product
        def seqToProd(teq: TimedTransducer.TimedTransducerEquation, proj_input: Boolean = false, proj_output: Boolean = false):
                Seq[TimedTransducer.TimedTransducer] = {
            teq match {
                case TimedTransducer.Base(t) => 
                    val locs = t.locations.map(l => 
                        l.copy(signalLabel = TimedTransducer.SignalLabel(
                            if (proj_input) Formula.True else l.signalLabel.input, 
                            if (proj_output) Formula.True else l.signalLabel.output
                        ))
                    )
                    val transitions = t.transitions.map(tr => 
                        tr.copy(signalLabel = TimedTransducer.SignalLabel(
                            if (proj_input) Formula.True else tr.signalLabel.input, 
                            if (proj_output) Formula.True else tr.signalLabel.output
                        ))
                    )
                    Seq(t.copy(locations = locs, transitions = transitions))
                case TimedTransducer.Product(t1, t2) => 
                    seqToProd(t1, proj_input, proj_output) ++ seqToProd(t2, proj_input, proj_output)
                case TimedTransducer.Sequential(t1, t2) => 
                        seqToProd(t1, true, proj_output) ++
                        seqToProd(t2, proj_input, true)
            }
        }
        val transducers = seqToProd(teq)
        val hornClauses = encodeTransducerProduct(transducers)
        hornClauses
    }

    def encodeTransducerProduct(
        transducers: Seq[TimedTransducer.TimedTransducer]
    ): Seq[(lazabs.horn.bottomup.HornClauses.Clause,
            hornconcurrency.System.NoSync.type)] = {

        val encodedTransducers = transducers.zipWithIndex.map {
            case (transducer, i) => encodeTransducer(transducer, s"T$i")
        }

        val locSorts = encodedTransducers.map(_.adt.sorts(0))
        // val new_ADT = new ADT(List("Loc"), 
        //     encodedTransducers.map(_.adt.sorts).flatMap(sl => 
        //         sl.map(ps => 
        //         (ps.name, ADT.CtorSignature(List(), ADT.ADTSort(0))))
        //     )
        // )
        // val locSorts = new_ADT.sorts

        // locs.map(l => (prefix + l.label, ADT.CtorSignature(List(), ADT.ADTSort(0))))

        val confDiscSortArgs = createPredicateArgSorts(encodedTransducers, locSorts)
        val confTimeSortArgs = createPredicateArgSorts(encodedTransducers, locSorts)

        val confDisc = MonoSortedPredicate("Discrete Configuration", confDiscSortArgs)
        val confTime = MonoSortedPredicate("Timed Configuration", confTimeSortArgs)

        val encodedInitialLocationTerms =
            encodedTransducers.map(_.initialLocation: ITerm)
        val encodedInputLabelTerms =
            encodedTransducers.flatMap(_.inputLabelTerms: Seq[ITerm])
        val encodedOutputLabelTerms =
            encodedTransducers.flatMap(_.outputLabelsTerms: Seq[ITerm])
        val encodedClockTerms =
            encodedTransducers.flatMap(_.clockTerms: Seq[ITerm])

        val encodedLabels = encodedInputLabelTerms ++ encodedOutputLabelTerms
        val confDiscArgs =
            Seq(C: ITerm) ++
            encodedInitialLocationTerms ++ encodedLabels ++ encodedClockTerms
        val confTimeArgs =
            Seq(C: ITerm) ++
            encodedInitialLocationTerms ++ encodedLabels ++ encodedClockTerms

        val initialClause = (confDisc(confDiscArgs: _*) :- true, NoSync)

        val head = confDisc(confDiscArgs: _*)
        val body = Seq(confTime(confTimeArgs: _*)) ++ encodedTransducers.map(encodeInvariant)

        val pureTimeStepClause =
            (head :-
                (body: _*),
                NoSync)

        val subsets = (0 until transducers.length).foldLeft(Seq(Set.empty[Int])) {
            case (sets, i) => { sets ++ sets.map(_ + i)}
        }.drop(1)

        val globalTransitionClauses = subsets.map { subset =>
            // In subset => discrete transition,
            // Not in subset => time transition
            val confDiscArgs = 
                Seq(C: ITerm) ++
                (encodedTransducers.zipWithIndex.map {
                    case (ec, i) if subset(i) => ec.target
                    case (ec, i) => ec.src
                }: Seq[ITerm]) ++
                encodedLabels ++
                (encodedTransducers.zipWithIndex.flatMap {
                    case (ec, i) if subset(i) => ec.newClockTerms
                    case (ec, i) => ec.clockTerms
                }: Seq[ITerm]) 

            val head = confDisc(confDiscArgs: _*)

            val confTimeArgs = 
                Seq(C: ITerm) ++
                encodedTransducers.map(_.src: ITerm) ++
                encodedLabels ++
                encodedTransducers.flatMap(_.clockTerms: Seq[ITerm])

            val actions = 
                encodedTransducers.zipWithIndex.map {
                    case (ec, i) if subset(i) => encodeStep(ec)
                    case (ec, i) => encodeInvariant(ec)
                }
            val resetClauses =
                encodedTransducers.zipWithIndex.filter {
                    case (_, i) => subset(i) 
                }.map{
                    case(ec, _) =>
                        ec.resetFlags.zip(ec.clockTerms).zip(ec.newClockTerms).map {
                            case ((cr, cp), c) =>
                                ((cr === True) ==> (cp === C)) & ((cr === False) ==> (cp === c))
                        }
                }.flatten

            val body = 
                Seq(confTime(confTimeArgs: _*)) ++
                actions ++
                resetClauses

            val transitionClause =
            (head :- 
                (body: _*),
                NoSync)
            transitionClause
        }

        Seq(initialClause, pureTimeStepClause) ++
        encodedTransducers.flatMap(_.invariantClauses) ++
        encodedTransducers.flatMap(_.stepClauses) ++
        globalTransitionClauses
    }

    def createPredicateArgSorts(ecs: Seq[EncodedTransducer], locSorts: Seq[Sort]): Seq[Sort] = {
        Seq(Rationals.dom) ++
        locSorts ++
        ecs.flatMap(_.inputLabelTerms.map(_ => Sort.Bool)) ++
        ecs.flatMap(_.outputLabelsTerms.map(_ => Sort.Bool)) ++
        ecs.flatMap(_.clockTerms.map(_ => Rationals.dom))
    }
    
    def encodeStep(et: EncodedTransducer): IFormula = {
        val pred_args: Seq[ConstantTerm] = 
            Seq(C) ++
            Seq(et.src) ++
            Seq(et.target) ++
            et.inputLabelTerms ++
            et.outputLabelsTerms ++
            et.clockTerms ++
            et.resetFlags
        et.stepPred(pred_args: _*)
    }

    def encodeInvariant(et: EncodedTransducer): IFormula = {
        val pred_args: Seq[ConstantTerm] = 
            Seq(C) ++
            Seq(et.src) ++
            et.inputLabelTerms ++
            et.outputLabelsTerms ++
            et.clockTerms
        et.invPred(pred_args: _*)
    }

    def encodeTransducer(
        transducer: TimedTransducer.TimedTransducer,
        id: String
    ): EncodedTransducer = {
        val prefix = id + "@"
        val LocADT = createSortsFromStates(transducer.locations, prefix)
        val locSort = LocADT.sorts(0)
        val funApps = transducer.locations.map(_.label).zip(
            LocADT.constructors.map(IFunApp(_, List()))
        ).toMap

        val inv = MonoSortedPredicate(prefix + "Inv",
        List(locSort, // local location
                Sort.Bool, Sort.Bool, // local input and output signals
                Rationals.dom, // global clock
                Rationals.dom // local clock
            ))
        val step = MonoSortedPredicate(prefix + "Step",
        List(locSort, // local source location
                locSort, // local target location
                Sort.Bool, Sort.Bool, // local input and output signals
                Rationals.dom, // global clock
                Rationals.dom, // local clock
                Sort.Bool // local reset instruction
            ))

        val s = locSort.newConstant(prefix + "s")
        val sp = locSort.newConstant(prefix + "sp")

        // signals
        val p = Sort.Bool.newConstant(prefix + transducer.inputLabels(0).label)
        val q = Sort.Bool.newConstant(prefix + transducer.outputLabels(0).label)
        val signal_environment = Map[String, ITerm](
            transducer.inputLabels(0).label -> p,
            transducer.outputLabels(0).label -> q
        )

        // local clocks
        val c1 = Rationals.dom.newConstant(prefix + transducer.clocks(0).label)
        val c1p = Rationals.dom.newConstant(prefix + transducer.clocks(0).label + "p")
        val c1r = Sort.Bool.newConstant(prefix + transducer.clocks(0).label + "r")

        // (inv(FS0, u, q, C, c1, c2) :- (u === True), (q === True),
        //         NoSync),
        // (inv(FS1, u, q, C, c1, c2) :- (minus(C, c1) < toRat(a)), (u === False), (q === True),
        //         NoSync),
        // (inv(FS2, u, q, C, c1, c2) :- (minus(C, c1) < toRat(a)), (u === False), (q === True),
        //         NoSync),
        // (inv(FS3, u, q, C, c1, c2) :- (u === False), (q === False),
        //         NoSync)

        val invariants = 
        transducer.locations.map(
            l => (inv(funApps(l.label), p, q, C, c1) :-
                    (encodeFormula(l.signalLabel.input, signal_environment) &
                     encodeFormula(l.signalLabel.output, signal_environment) &
                     encodeClockConstraint(l.invariant, c1, C)),
                     NoSync)
        )
        // (step(FSi, FS0, u, q, C, c1, c2, False) :- (q === True),
        // NoSync),
        // (step(FSi, FS1, u, q, C, c1, c2, True) :- (q === False),
        // NoSync),
        // (step(FSi, FS2, u, q, C, c1, c2, True) :- (q === True),
        // NoSync),
        // (step(FSi, FS3, u, q, C, c1, c2, c1r) :- (q === False),
        // NoSync),
        // (step(FS0, FS0, u, q, C, c1, c2, c1r) :- (u === False), (q === True),
        // NoSync),
        // (step(FS0, FS1, u, q, C, c1, c2, True) :- (q === False),
        // NoSync),
        

        
        val steps = 
        transducer.transitions.map(
            t => (step(funApps(t.source.label), funApps(t.target.label), p, q, C, c1,
                        encodeClockReset(t.resetInstruction.isEmpty)) :-
                    (encodeFormula(t.signalLabel.input, signal_environment) &
                     encodeFormula(t.signalLabel.output, signal_environment) &
                     encodeClockConstraint(t.guard, c1, C)),
                     NoSync)
        )  

                // The argument is the index of the acceptance set
        val acceptPred = MonoSortedPredicate(prefix + "Accept",List(Sort.Integer))
            /* For each acceptance set with index idx,
       acceptPred(idx) holds if the current transition or target location is 
       in the acceptance set. */ 
        val acceptClauses = transducer.acceptanceCondition.zipWithIndex.flatMap {
            case ((locations, transitions), idx) => {
                //TODO: optimize by not including transitions that are already included by the location clauses
                val loc_clauses = locations.map(l => 
                    acceptPred(idx) :- step(s, funApps(l.label), p, q, C, c1, c1r)
                ) 
                val trans_clauses = transitions.map(t => 
                    acceptPred(idx) :- step(funApps(t.source.label), 
                                        funApps(t.target.label), p, q, C, c1, c1r)
                )
                loc_clauses ++ trans_clauses
            }
        }

        // TODO: implement global transitions
        EncodedTransducer(prefix + transducer.name,
                          LocADT,
                          funApps(transducer.initialLocation.label),
                          s, sp,
                          Seq(p), Seq(q),
                          Seq(c1),
                          Seq(c1p), Seq(c1r),
                          inv, invariants,
                          step, steps,
                          acceptPred, acceptClauses)
    }




    def encodeClockReset(reset: Boolean) : IFunApp = {
        if (reset) False else True
    }

    def encodeClockConstraint(
        clock_constraint: TimedTransducer.ClockConstraint,
        local_clock: ITerm,
        global_clock: ITerm) : IFormula = {
            def encode(clock_constraint: TimedTransducer.ClockConstraint): IFormula =
                clock_constraint match {
                    case TimedTransducer.ClockConstraint.True => true
                    case TimedTransducer.ClockConstraint.Bound(_, TimedTransducer.ClockConstraint.Lt, c) => (minus(global_clock, local_clock) < toRat(c))
                    case TimedTransducer.ClockConstraint.Bound(_, TimedTransducer.ClockConstraint.Leq, c) => (minus(global_clock, local_clock) <= toRat(c))
                    case TimedTransducer.ClockConstraint.Bound(_, TimedTransducer.ClockConstraint.Gt, c) => (minus(global_clock, local_clock) > toRat(c))
                    case TimedTransducer.ClockConstraint.Bound(_, TimedTransducer.ClockConstraint.Geq, c) => (minus(global_clock, local_clock) >= toRat(c))
                    case TimedTransducer.ClockConstraint.Bound(_, TimedTransducer.ClockConstraint.Eq, c) => (minus(global_clock, local_clock) == toRat(c))
                    case TimedTransducer.ClockConstraint.Conjunction(args) => and(args.map(encode))
                }
        encode(clock_constraint)
    }

    def encodeFormula[A <: TimedTransducer.Label](
        formula: Formula[A],
        environment: Map[String, ITerm]) : IFormula = {
            def encode(formula: Formula[A]): IFormula =
                formula match {
                    case TimedTransducer.Formula.True => true
                    case TimedTransducer.Formula.False => false
                    case TimedTransducer.Formula.Atom(v) => environment(v.label) === True
                    case TimedTransducer.Formula.Not(TimedTransducer.Formula.Atom(v)) => environment(v.label) === False
                    case TimedTransducer.Formula.Not(v) => ~encode(v)
                    case TimedTransducer.Formula.And(args) => and(args.map(encode))
                    case TimedTransducer.Formula.Or(args) => or(args.map(encode))
                }
        encode(formula)
    }

    def createSortsFromStates(locs: Seq[Location], prefix: String): ADT = {
        new ADT(
            List("Loc"),
                locs.map(l => (prefix + l.label, ADT.CtorSignature(List(), ADT.ADTSort(0))))
        )
    }
}
