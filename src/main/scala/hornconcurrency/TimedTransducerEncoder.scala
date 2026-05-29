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
                                 clauses: Seq[(HornClauses.Clause, NoSync.type)],
                                 progressBlock: ProgressBlock,
                                 configuration: Predicate,
                                 initialLocation: ITerm,
                                 locationTerm: ConstantTerm,
                                 invariantClauses: Seq[HornClauses.Clause],
                                 globalSignalLabels: Seq[String],
                                 globalSignalTerms: Seq[ConstantTerm],
                                 locationSort: Sort,
                                 clockTerms: Seq[ConstantTerm]
                                )

    // global clock
    val C = Rationals.dom.newConstant("C")

    def encodeTransducerEquation(teq : TimedTransducer.TimedTransducerEquation): 
        Seq[EncodedTransducer]= {
        
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
                globalSignalEnvironment)
        }
        encodedTransducers
    }

    /*  Each transducer is supposed to run in parallel using global signals to synchronize them.
        This method encodes a single local transducer, creating the following clauses:

        Initial transition:
            conf(C, p1,…,pn, s0, c) :- true

        Transitions:
            conf(C, p1,…,pn, s1, c) :- (conf(C, p1,…,pn, s0, c), (p1 == True & p2 == False))
            conf(C, p1,…,pn, s1, C) :- (conf(C, p1,…,pn, s1, c), (p1 == False & p2 == False))
            …

        Invariants (placed in a progress block)
        s1 => (p1 == True & p2 === True && C - c < 10) :- conf(C, p1,…,pn, s1, c)
        s2 => (p1 == False & p2 === False) :- conf(C, p1,…,pn, s1, c)
        ...

        Accept clauses:
            ???

        In this encoding, C is the global clock, and p1,...,pn are global signals.
        s0, s1 etc. are constants in a new location sort created for each transducer.
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
        val LocADT = createSortsFromStates(transducer.locations, prefix)
        val locSort = LocADT.sorts(0)
        val locMap = transducer.locations.map(_.label).zip(
            LocADT.constructors.map(IFunApp(_, List()))
        ).toMap
        val configuration = MonoSortedPredicate(prefix + "Conf",
            List(   
                Rationals.dom // global clock
            )
            ++ globalSignalTerms.map(_ => Sort.Bool) // global input/output signals
            ++ List(locSort) // location
            ++ transducer.clocks.map(_ => Rationals.dom) // local clocks
        )

        val s = locSort.newConstant(prefix + "s")
        val globalSignals: Seq[ITerm] = globalSignalTerms.map(IConstant(_))

        // local clocks
        val clockTerms = transducer.clocks.map(clock =>
            Rationals.dom.newConstant(prefix + clock.label))
        val clockEnvironment = transducer.clocks.zip(clockTerms).toMap
        val clockArgs = clockTerms.map(IConstant(_))

        // configuration(C, signals..., initialLocation, clocks...) :- true
        val initArgs: Seq[ITerm] =
            Seq(IConstant(C)) ++ globalSignals ++
            Seq(locMap(transducer.initialLocation.label)) ++
            transducer.clocks.map(_ => IConstant(C))
        val initialClause = (configuration(initArgs: _*) :- true, NoSync)

        val invariantClauses = transducer.locations.map { l =>
            val invArgs: Seq[ITerm] = Seq(IConstant(C)) ++ globalSignals ++ Seq(IConstant(s)) ++ clockArgs
            val inLocation = IConstant(s) === locMap(l.label)
            val locationInvariant =
                encodeFormula(l.signalLabel.input, signalEnvironment) &
                encodeFormula(l.signalLabel.output, signalEnvironment) &
                encodeClockConstraint(l.invariant, clockEnvironment, C)
            (inLocation ==> locationInvariant) :- configuration(invArgs: _*)
        }
        val pb = ProgressBlock(invariantClauses)

        // Could not get signal system to work with a separate step predicate, i.e.
        // conf(..., s, ...) :- conf(..., s, ...), step(s, sp).
        val transitionClauses =
            transducer.transitions.map { t =>
                val postClockArgs = transducer.clocks.map { clock =>
                    if (t.resetInstruction contains clock) IConstant(C) else IConstant(clockEnvironment(clock))
                }
                val preStepArgs: Seq[ITerm] =
                    Seq(IConstant(C)) ++ globalSignals ++ Seq(locMap(t.source.label)) ++ clockArgs
                val postStepArgs: Seq[ITerm] =
                    Seq(IConstant(C)) ++ globalSignals ++ Seq(locMap(t.target.label)) ++ postClockArgs
                val guard =
                    encodeFormula(t.signalLabel.input, signalEnvironment) &
                    encodeFormula(t.signalLabel.output, signalEnvironment) &
                    encodeClockConstraint(t.guard, clockEnvironment, C)
                (configuration(postStepArgs: _*) :- (configuration(preStepArgs: _*), guard), NoSync)
            }

        // The argument is the index of the acceptance set
        val acceptPred = MonoSortedPredicate(prefix + "Accept",List(Sort.Integer))
        /* For each acceptance set with index idx,
        acceptPred(idx) holds if the current transition or target location is 
        in the acceptance set. */ 
        val acceptClauses = Seq.empty[(HornClauses.Clause, NoSync.type)]
        
        val clauses = Seq(initialClause) ++ transitionClauses ++ acceptClauses
        EncodedTransducer(
            prefix + transducer.name,
            clauses,
            pb,
            configuration,
            locMap(transducer.initialLocation.label),
            s,
            invariantClauses,
            globalSignalLabels,
            globalSignalTerms,
            locSort,
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
                        (minus(global_clock, IConstant(clockEnvironment(clock))) < toRat(c))
                    case TimedTransducer.ClockConstraint.Bound(clock, TimedTransducer.ClockConstraint.Leq, c) =>
                        (minus(global_clock, IConstant(clockEnvironment(clock))) <= toRat(c))
                    case TimedTransducer.ClockConstraint.Bound(clock, TimedTransducer.ClockConstraint.Gt, c) =>
                        (minus(global_clock, IConstant(clockEnvironment(clock))) > toRat(c))
                    case TimedTransducer.ClockConstraint.Bound(clock, TimedTransducer.ClockConstraint.Geq, c) =>
                        (minus(global_clock, IConstant(clockEnvironment(clock))) >= toRat(c))
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
