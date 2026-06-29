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
import ap.parser.IExpression._
import ap.theories.rationals.Rationals
import ap.theories.ADT
import ap.types.MonoSortedPredicate
import lazabs.horn.Util
import lazabs.horn.bottomup.{HornClauses, HornPredAbs}
import org.scalactic.PrettyMethods
import hornconcurrency.VerificationLoop.prettyPrint
import lazabs.horn.global.HornClause
import javax.lang.model.`type`.NoType
import hornconcurrency.TimedTransducer.SignalLabel



object TimedTransducerEncoder {
    import HornClauses._
    import IExpression._
    import System._
    import SignalSystem._
    import Rationals.{geq, leq, gt, lt, minus, int2ring => toRat}
    import ADT._
    import ADT.BoolADT.{True, False}
    import TimedTransducer.{Location, Formula}

    case class EncodedTransducer(name: String,
                                 clauses: Seq[(HornClauses.Clause, Synchronisation)],
                                 progressBlock: ProgressBlock,
                                 configurations: Map[String, Predicate],
                                 invariantClauses: Seq[HornClauses.Clause],
                                 acceptPreds: Map[Seq[Predicate], Option[Int]],
                                 globalSignalLabels: Seq[String],
                                 globalSignalTerms: Seq[ConstantTerm],
                                 clockTerms: Seq[ConstantTerm]
                                 )

    // global clock
    val C = Rationals.dom.newConstant("C")

    def encodeTransducerEquation(teq : TimedTransducer.TimedTransducerEquation): 
        (Seq[EncodedTransducer], TimedTransducer.OutputLabel) = {
        
        //Converts sequenctial composition to product, returns a list of all base transducers that should be composed woht product
        def seqToProd(teq: TimedTransducer.TimedTransducerEquation):
                Seq[TimedTransducer.TimedTransducer] = {
            teq match {
                case TimedTransducer.Base(t) => 
                    Seq(t)
                case TimedTransducer.Product(t1, t2) => 
                    seqToProd(t1) ++ seqToProd(t2)
                case TimedTransducer.Sequential(t1, t2) => 
                    seqToProd(t1) ++ seqToProd(t2)
            }
        }
        def getOuterOutputLabel(_teq: TimedTransducer.TimedTransducerEquation): TimedTransducer.OutputLabel = _teq match {
            case TimedTransducer.Base(t) => {
                    assert(t.outputLabels.size == 1)
                    t.outputLabels.head
                }
            case TimedTransducer.Product(_, t2)  => getOuterOutputLabel(t2)
            case TimedTransducer.Sequential(_, t2) => getOuterOutputLabel(t2)
        }
        val outerOutputLabel = getOuterOutputLabel(teq)

        val transducers = seqToProd(teq)
        val globalSignalLabels =
            (transducers.flatMap(_.inputLabels.map(_.label)) ++
             transducers.flatMap(_.outputLabels.map(_.label))).distinct.sorted
        val globalSignalTerms =
            globalSignalLabels.map(Sort.Bool.newConstant)
        val globalSignalEnvironment =
            globalSignalLabels.zip(globalSignalTerms).toMap
        val encodedTransducers = transducers.zipWithIndex.map {
            case (transducer, i) => encodeTransducer(
                transducer,
                s"T$i",
                globalSignalLabels,
                globalSignalTerms,
                globalSignalEnvironment
            )
        }
        (encodedTransducers, outerOutputLabel)
    }

    def toSignalSystem(ets: Seq[EncodedTransducer], output: TimedTransducer.OutputLabel) : 
        (AcceptingSignalSystem, Map[String, Int]) = {
        val globalVarNum = ets.head.globalSignalTerms.size + 1
        val globalSignalLabels = ets.head.globalSignalLabels
        val signalIdxs = 1 until globalVarNum
        val signalToIdx = globalSignalLabels.zip(signalIdxs).toMap


        val system = AcceptingSignalSystem(
            ets.map(t => (t.clauses, System.Singleton)),
            globalVarNum,
            Seq(),
            RationalTime(0),
            (1 until globalVarNum).toSet,
            ets.map(t => List(t.progressBlock)),
            ets.flatMap(_.acceptPreds).toMap,
            Some(signalToIdx(output.label))
        )
        (system, signalToIdx)
    }

    /*  Each transducer is supposed to run in parallel using global signals to synchronize them.
        This method encodes a single local transducer, creating the following clauses:

        Initial transitions:
            confS1(C, p1,…,pn, C) :- (p1 == True & p2 == False)
            ... 

        Transitions:
            confS1(C, p1,…,pn, c) :- (confS0(C, p1,…,pn, c), (p1 == True & p2 == False))
            confS1(C, p1,…,pn, C) :- (confS1(C, p1,…,pn, c), (p1 == False & p2 == False))
            …

        Invariants (placed in a progress block)
        (p1 == True & p2 === True && C - c < 10) :- confS1(C, p1,…,pn, c)
        (p1 == False & p2 === False) :- confS2(C, p1,…,pn, c)
        ...

        Accept clauses:
            ???

        In this encoding, C is the global clock, and p1,...,pn are global signals.
        s0, s1 etc. are represented by one predicate per location.
        c is a local clock.
     */
    def encodeTransducer(
        transducer: TimedTransducer.TimedTransducer,
        id: String,
        globalSignalLabels: Seq[String],
        globalSignalTerms: Seq[ConstantTerm],
        signalEnvironment: Map[String, ConstantTerm]
    ): EncodedTransducer = {
        import ap.parser.IExpression._
        val prefix = id + "@"
        val configurationSorts =
            List(
                Rationals.dom // global clock
            ) ++
            globalSignalTerms.map(_ => Sort.Bool) ++ // global input/output signals
            transducer.clocks.map(_ => Rationals.dom) // local clocks
        val locationPredicateMap = transducer.locations
            .filter(_ != transducer.initialLocation)
            .map(
            l => (l.label, MonoSortedPredicate(prefix + "Conf" + l, configurationSorts))
        ).toMap
        val globalSignals: Seq[ITerm] = globalSignalTerms.map(IConstant(_))
        
        // local clocks
        val clockTerms = transducer.clocks.map(clock =>
            Rationals.dom.newConstant(prefix + clock.label))
        val clockEnvironment = transducer.clocks.zip(clockTerms).toMap
        val initialClockEnvironment = transducer.clocks.map(_ -> C).toMap
        val clockArgs = clockTerms.map(IConstant(_))

        val invariantClauses = transducer.locations
        .filter(_ != transducer.initialLocation)
        .map { l =>
            val invArgs: Seq[ITerm] = Seq(IConstant(C)) ++ globalSignals ++ clockArgs
            val locationInvariant =
                encodeFormula(l.signalLabel.input, signalEnvironment) &
                encodeFormula(l.signalLabel.output, signalEnvironment) &
                encodeClockConstraint(l.invariant, clockEnvironment, C)
            (locationInvariant :- locationPredicateMap(l.label)(invArgs: _*))
        }
        val pb = ProgressBlock(invariantClauses)

        // Could not get signal system to work with a separate step predicate, i.e.
        // conf(..., s, ...) :- conf(..., s, ...), step(s, sp).
        def transitionClause(
            t: TimedTransducer.Transition,
            sourceConfiguration: Predicate
        ): (HornClauses.Clause, NoSync.type) = {
                val postClockArgs = transducer.clocks.map { clock =>
                    if (t.resetInstruction contains clock) IConstant(C) else IConstant(clockEnvironment(clock))
                }
                val preStepArgs: Seq[ITerm] =
                    Seq(IConstant(C)) ++ globalSignals ++ clockArgs
                val postStepArgs: Seq[ITerm] =
                    Seq(IConstant(C)) ++ globalSignals ++ postClockArgs
                val guard =
                    encodeFormula(t.signalLabel.input, signalEnvironment) &
                    encodeFormula(t.signalLabel.output, signalEnvironment) &
                    encodeClockConstraint(t.guard, clockEnvironment, C)
                (locationPredicateMap(t.target.label)(postStepArgs: _*)
                    :- (sourceConfiguration(preStepArgs: _*), guard), NoSync)
        }

        val firstStepTransitionClauses =
            transducer.transitions
                .filter(_.source == transducer.initialLocation)
                .map { t =>
                    val postStepArgs: Seq[ITerm] =
                        Seq(IConstant(C)) ++ globalSignals ++ transducer.clocks.map(_ => IConstant(C))
                    val guard =
                        encodeFormula(t.signalLabel.input, signalEnvironment) &
                        encodeFormula(t.signalLabel.output, signalEnvironment) &
                        encodeClockConstraint(t.guard, initialClockEnvironment, C)
                    (locationPredicateMap(t.target.label)(postStepArgs: _*) :- guard, NoSync)
                }

        val transitionClauses =
            transducer.transitions
            .filter(_.source != transducer.initialLocation)
            .map(t => transitionClause(t, locationPredicateMap(t.source.label)))

        val acceptSorts = // We need to add global clock and signal terms as args
            List(
                Rationals.dom // global clock
            ) ++
            globalSignalTerms.map(_ => Sort.Bool) :+ Sort.Integer // global input/output signals
        // The argument is the index of the acceptance set
        val acceptName = transducer.rank_id match {
            case Some(id) => prefix ++ "_accept_" ++ "rank_" ++ id.toString 
            case None => prefix ++ "_accept_NoRank"
        }
        val acceptPred = MonoSortedPredicate(acceptName, acceptSorts)
        /* For each acceptance set with index idx,
        acceptPred(idx) holds if the current transition or target location is 
        in the acceptance set. */ 
        val acceptanceCondition = if (transducer.acceptanceCondition.isEmpty) {
            //If empty accept condition, we treat every location and transition as accepting
            Seq((transducer.locations.filter(_ != transducer.initialLocation), 
                transducer.transitions.filter(_.source != transducer.initialLocation)))
        } else {
            transducer.acceptanceCondition
        }
        val acceptPreds = acceptanceCondition.flatMap{
            case (acc_loc, acc_trans) => 
            val loc_clauses = acc_loc.map{case l => 
                (Seq(locationPredicateMap(l.label)), transducer.rank_id)
            }
            val trans_clauses = acc_trans.map{ case t => 
                (Seq(locationPredicateMap(t.source.label),
                  locationPredicateMap(t.target.label)), transducer.rank_id)
            }
            (loc_clauses)// ++ trans_clauses) //FIXME: trans clauses gives later bug
        }.toMap
        
        EncodedTransducer(
            prefix + transducer.name,
            firstStepTransitionClauses ++ transitionClauses,
            pb,
            locationPredicateMap,
            invariantClauses,
            acceptPreds,
            globalSignalLabels,
            globalSignalTerms,
            clockTerms
        )
    }
    

    def encodeClockReset(reset: Boolean) : IFunApp = {
        if (reset) False else True
    }

    def encodeClockConstraint(
        clock_constraint: TimedTransducer.ClockConstraint,
        clockEnvironment: Map[TimedTransducer.Clock, ConstantTerm],
        global_clock: ITerm) : IFormula = {
            def encode(clock_constraint: TimedTransducer.ClockConstraint): IFormula =
                clock_constraint match {
                    case TimedTransducer.ClockConstraint.True => true
                    case TimedTransducer.ClockConstraint.Bound(clock, TimedTransducer.ClockConstraint.Lt, c) =>
                        lt(minus(global_clock, IConstant(clockEnvironment(clock))), toRat(c))
                    case TimedTransducer.ClockConstraint.Bound(clock, TimedTransducer.ClockConstraint.Leq, c) =>
                        leq(minus(global_clock, IConstant(clockEnvironment(clock))), toRat(c))
                    case TimedTransducer.ClockConstraint.Bound(clock, TimedTransducer.ClockConstraint.Gt, c) =>
                        gt(minus(global_clock, IConstant(clockEnvironment(clock))), toRat(c))
                    case TimedTransducer.ClockConstraint.Bound(clock, TimedTransducer.ClockConstraint.Geq, c) =>
                        geq(minus(global_clock, IConstant(clockEnvironment(clock))), toRat(c))
                    case TimedTransducer.ClockConstraint.Bound(clock, TimedTransducer.ClockConstraint.Eq, c) =>
                        (minus(global_clock, IConstant(clockEnvironment(clock))) === toRat(c))
                    case TimedTransducer.ClockConstraint.Conjunction(args) => and(args.map(encode))
                }
        encode(clock_constraint)
    }

    def encodeFormula[A <: TimedTransducer.Label](
        formula: Formula[A],
        environment: Map[String, ConstantTerm]) : IFormula = {
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
