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
                                 input_label_terms: Seq[ConstantTerm],
                                 output_labels_terms: Seq[ConstantTerm],
                                 clock_terms: Seq[ConstantTerm],
                                 new_clock_terms: Seq[ConstantTerm],
                                 resetFlags: Seq[ConstantTerm],
                                 inv_pred: Predicate,
                                 invariant_clauses: Seq[(HornClauses.Clause, NoSync.type)],
                                 step_pred: Predicate,
                                 step_clauses: Seq[(HornClauses.Clause, NoSync.type)])

    // global clock
    val C = Rationals.dom.newConstant("C")


    // Code waiting for transducerequation to be defined
    // Should return a set of Horn clauses
    def encodeTransducerEquation(teq : TimedTransducer.TimedTransducerEquation): Unit = {
        
        //Converts sequenctial composition to product, returns a list of all base transducers that should be composed woht product
        def seq_to_prod(teq: TimedTransducer.TimedTransducerEquation, proj_input: Boolean = false, proj_output: Boolean = false): 
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
                    seq_to_prod(t1, proj_input, proj_output) ++ seq_to_prod(t2, proj_input, proj_output)
                case TimedTransducer.Sequential(t1, t2) => 
                        seq_to_prod(t1, true, proj_output) ++
                        seq_to_prod(t2, proj_input, true)
            }
        }
        val transducers = seq_to_prod(teq)
        val horn_clauses = encodeTransducerProduct(transducers)
        horn_clauses
    }


    def encodeTransducerProduct(
        transducers: Seq[TimedTransducer.TimedTransducer]
    ): Unit = {

        val encoded_transducers = transducers.zipWithIndex.map {
            case (transducer, i) => encodeTransducer(transducer, s"T$i")
        }

        val loc_sorts = encoded_transducers.map(_.adt.sorts(0))
        // val new_ADT = new ADT(List("Loc"), 
        //     encoded_transducers.map(_.adt.sorts).flatMap(sl => 
        //         sl.map(ps => 
        //         (ps.name, ADT.CtorSignature(List(), ADT.ADTSort(0))))
        //     )
        // )
        // val loc_sorts = new_ADT.sorts
        
        // locs.map(l => (prefix + l.label, ADT.CtorSignature(List(), ADT.ADTSort(0))))



        
        val conf_disc_sort_args = 
            Seq(Rationals.dom) ++
            loc_sorts ++
            encoded_transducers.flatMap(_.input_label_terms.map(_ => Sort.Bool)) ++
            encoded_transducers.flatMap(_.output_labels_terms.map(_ => Sort.Bool)) ++
            encoded_transducers.flatMap(_.clock_terms.map(_ => Rationals.dom))
        val conf_disc = MonoSortedPredicate("Discrete Configuration", conf_disc_sort_args)
        val conf_time_sort_args = 
            Seq(Rationals.dom) ++
            loc_sorts ++
            Seq(Sort.Bool, Sort.Bool, Sort.Bool, Sort.Bool) ++
            Seq(Rationals.dom, Rationals.dom)
        val conf_time = MonoSortedPredicate("Timed Configuration", conf_time_sort_args)

        val signal_labels = 
            encoded_transducers.flatMap(_.input_label_terms: Seq[ITerm]) ++
            encoded_transducers.flatMap(_.output_labels_terms: Seq[ITerm])
        val conf_disc_args = 
            Seq(C: ITerm) ++
            encoded_transducers.map(_.initialLocation: ITerm) ++
            signal_labels ++
            encoded_transducers.flatMap(_.clock_terms: Seq[ITerm])
        val conf_time_args = 
            Seq(C: ITerm) ++
            encoded_transducers.map(_.initialLocation: ITerm) ++
            signal_labels ++
            encoded_transducers.flatMap(_.clock_terms: Seq[ITerm])
        val initial = conf_disc(conf_disc_args: _*)

        val tt =
            (conf_disc(conf_disc_args: _*) :- 
                conf_time(conf_time_args: _*),
                encoded_transducers.map(encode_invariant),
                NoSync)

        val subsets = (0 until transducers.length).foldLeft(Seq(Set.empty[Int])) {
            case (sets, i) => { sets ++ sets.map(_ + i)}
        }.drop(1)

        val transitions = subsets.map { subset =>
            // In subset => discrete transition,
            // Not in subset => time transition
            val conf_disc_args = 
                Seq(C: ITerm) ++
                (encoded_transducers.zipWithIndex.map {
                    case (ec, i) if subset(i) => ec.target
                    case (ec, i) => ec.src
                }: Seq[ITerm]) ++
                signal_labels ++
                (encoded_transducers.zipWithIndex.flatMap {
                    case (ec, i) if subset(i) => ec.new_clock_terms
                    case (ec, i) => ec.clock_terms
                }: Seq[ITerm]) 

            val head = conf_disc(conf_disc_args: _*)

            val conf_time_args = 
                Seq(C: ITerm) ++
                encoded_transducers.map(_.src: ITerm) ++
                signal_labels ++
                encoded_transducers.flatMap(_.clock_terms: Seq[ITerm])

            val actions = 
                encoded_transducers.zipWithIndex.map {
                    case (ec, i) if subset(i) => encode_step(ec)
                    case (ec, i) => encode_invariant(ec)
                }
            val resetClauses =
                encoded_transducers.zipWithIndex.filter {
                case (_, i) => subset(i) 
                }.map{
                    case(ec, _) =>
                        ec.resetFlags.zip(ec.clock_terms).zip(ec.new_clock_terms).map {
                            case ((cr, cp), c) =>
                                ((cr === True) ==> (cp === C)) & ((cr === False) ==> (cp === c))
                        }
                }
            val tt =
            (head :- 
                conf_time(conf_time_args: _*),
                actions,
                resetClauses,
                NoSync)
            tt
        }

        for (trans <- transitions) {
            println(trans)
        }

        transitions

        //TODO: Emit the clauses

        // Sequential composition:
        // If Q1 = P2 and P1 \cap Q2 = \emptyset, then
        // for each p in Q1 \cup Q2, in each label \alpha, replace \alpha with \exists q. \alpha[p/q].
        // val name = "Prod__" + transducers.map(_.name).mkString("_")
        // EncodedTransducer(
        //     name,
        //     new_ADT,
        //     funApps(transducer.initialLocation),
        //     s, sp,
        //     Seq(p), Seq(q),
        //     Seq(c1),
        //     Seq(c1p), Seq(c1r),
        //     inv, invariants,
        //     step, 
        //     transitions
        // )

        ???
    }


    
    def encode_step(et: EncodedTransducer): IAtom = {
        val pred_args: Seq[ConstantTerm] = 
            Seq(C) ++
            Seq(et.src) ++
            Seq(et.target) ++
            et.input_label_terms ++
            et.output_labels_terms ++
            et.clock_terms ++
            et.resetFlags
        et.step_pred(pred_args: _*)
    }

    def encode_invariant(et: EncodedTransducer): IAtom = {
        val pred_args: Seq[ConstantTerm] = 
            Seq(C) ++
            Seq(et.src) ++
            et.input_label_terms ++
            et.output_labels_terms ++
            et.clock_terms
        et.inv_pred(pred_args: _*)
    }

    def encodeTransducer(
        transducer: TimedTransducer.TimedTransducer,
        id: String
    ): EncodedTransducer = {
        val prefix = id + "@"
        val LocADT = createSortsFromStates(transducer.locations, prefix)
        val locSort = LocADT.sorts(0)
        val funApps = transducer.locations.zip(
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

        val a = 10

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
            l => (inv(funApps(l), p, q, C, c1) :- 
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
            t => (step(funApps(t.source), funApps(t.target), p, q, C, c1, encodeClockReset(t.resetInstruction.isEmpty)) :- 
                    (encodeFormula(t.signalLabel.input, signal_environment) &
                     encodeFormula(t.signalLabel.output, signal_environment) &
                     encodeClockConstraint(t.guard, c1, C)),
                     NoSync)
        )

        // TODO: implement global transitions
        EncodedTransducer(prefix + transducer.name,
                          LocADT,
                          funApps(transducer.initialLocation),
                          s, sp,
                          Seq(p), Seq(q),
                          Seq(c1),
                          Seq(c1p), Seq(c1r),
                          inv, invariants,
                          step, steps)
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
