/**
 * Copyright (c) 2011-2026 Philipp Ruemmer. All rights reserved.
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
import ap.types.MonoSortedPredicate
import ap.theories.ADT
import ap.theories.rationals.Rationals
import ap.util.{Seqs, Combinatorics}

import lazabs.horn.Util
import lazabs.horn.bottomup.HornClauses
import lazabs.horn.bottomup.HornPredAbs.predArgumentSorts
import lazabs.horn.abstractions.{VerificationHints, EmptyVerificationHints}
import lazabs.horn.preprocessor.HornPreprocessor

import scala.collection.mutable.{LinkedHashSet, HashSet => MHashSet,
                                 ArrayBuffer, HashMap => MHashMap}

object SignalSystem {
  import System._

/*
  val (signalSort, signalCtor, Seq(currentValue, lastContinuousValue)) =
    ADT.createRecordType("signal",
                         List(("currentValue",        Sort.Bool),
                              ("lastContinuousValue", Sort.Bool)))
*/
  case class ProgressBlock(invariants : Seq[HornClauses.Clause])

  /**
   * Create a timed system with signals.
   */
  def apply(_processes            : ProcessSet,
            _globalVarNum         : Int,
            _assertions           : Seq[HornClauses.Clause],
            _timeSpec             : RationalTime,
            _signals              : Set[Int],
            _progressBlocks       : Seq[Seq[ProgressBlock]],
            _globalVarAssumptions : Option[Seq[ITerm] => IFormula] = None,
            _hints                : VerificationHints = EmptyVerificationHints,
            _backgroundAxioms     : BackgroundAxioms = NoBackgroundAxioms)
                                  : SignalSystem =
    new {
      val processes = _processes
      val globalVarNum = _globalVarNum
      val globalVarAssumptions = _globalVarAssumptions
      val assertions = _assertions
      val hints = _hints
      val backgroundAxioms = _backgroundAxioms
      val timeSpec = _timeSpec
      val signals = _signals
      val progressBlocks = _progressBlocks
    } with SignalSystem

}

trait SignalSystem extends System {
  import System._
  import SignalSystem._

  /**
   * The global variable representing rational time.
   */
  def timeSpec : RationalTime

  /**
   * Global Boolean variables representing signals.
   */
  def signals : Set[Int]

  def progressBlocks : Seq[Seq[ProgressBlock]]

  assert(progressBlocks.size == processes.size)
  assert(signals.forall { ind => ind >= 0 && ind < globalVarNum })

}

// Not finished yet
class SignalEncoder(system : SignalSystem) {
  import system._
  import System._
  import Rationals.{dom => Rat}
  import IExpression._
  import HornClauses.Clause

  // We need to introduce copies of the signal variables as global variables
  val newGlobalVarNum = globalVarNum + signals.size

  val signalIndexesSorted =
    signals.toSeq.sorted
  val lastContinuousSignalValue =
    signalIndexesSorted.map(ind => Sort.Bool.newConstant(s"SignalCopy$ind"))

  // We also need local variables storing the entry time for each progress
  // block
  val progressEntryClocks =
    for (blocks <- progressBlocks) yield {
      for ((block, n) <- blocks.zipWithIndex) yield Rat.newConstant(s"E$n")
    }

  // Vector of functions converting state predicates to the extended predicates
  val toExtendedPred =
    (for ((preds, clocks) <- localPreds.iterator zip progressEntryClocks.iterator;
           extraSignalSorts = lastContinuousSignalValue.map(x => Sort.Bool);
           extraClockSorts = clocks.map(x => Rat);
           p <- preds.iterator) yield {
       val sorts = predArgumentSorts(p)
       val (sortPref, sortSuff) = sorts.splitAt(globalVarNum)
       val extSorts = sortPref ++ extraSignalSorts ++ sortSuff ++ extraClockSorts
       val newP = MonoSortedPredicate(p.name, extSorts)
       p -> newP
     }).toMap

  val extendedLocalPreds =
    localPreds.map(s => s.map(toExtendedPred))

  // For each local predicate (actually, only the ones inside progress blocks),
  // we need a copy to represent environment transitions
  val localPredCopies =
    extendedLocalPreds.map(s => s.map(
      p => MonoSortedPredicate(p.name + "_envCopy", predArgumentSorts(p))))

  val toPredCopy =
    (for ((preds1, preds2) <- extendedLocalPreds.iterator zip localPredCopies.iterator;
          (p1, p2) <- preds1.iterator zip preds2.iterator)
     yield (p1 -> p2)).toMap

  val envPreds =
    List(MonoSortedPredicate("Env0", globalVarSorts),
         MonoSortedPredicate("Env1", globalVarSorts),
         MonoSortedPredicate("Env2", globalVarSorts))

  val newLocalPreds =
    (extendedLocalPreds zip localPredCopies).map(p => p._1 ++ p._2) :+ envPreds

  val delayBarrier1 =
    new SimpleBarrier("DelayBarrier1", newLocalPreds.map(_.toSet))
  val delayBarrier2 =
    new SimpleBarrier("DelayBarrier2", newLocalPreds.map(_.toSet))

  val toExtendedAtom : IAtom => IAtom =
    (a : IAtom) =>
      toExtendedPred.get(a.pred) match {
        case Some(newP) => {
          val signalTerms = lastContinuousSignalValue.map(i(_))
          val clockTerms = progressEntryClocks(processIndex(a.pred)).map(i(_))
          val (argPref, argSuff) = a.args.splitAt(globalVarNum)
          IAtom(newP, argPref ++ signalTerms ++ argSuff ++ clockTerms)
        }
        case None =>
          a
      }

  val extendedBarriers = {
    val f = (p : IExpression.Predicate) => toExtendedPred.getOrElse(p, p)
    val m = for (p <- processes) yield f
    barriers.map(_.mapDomains(m))
  }

  val toExtendedBarrier =
    (barriers zip extendedBarriers).toMap

  val toExtendedSync =
    (s : Synchronisation) => s match {
      case BarrierSync(b) => BarrierSync(toExtendedBarrier(b))
      case s => s
    }

  val timeIndex = timeSpec.index

  val newLocalProcesses =
    for ((((clauses, r), progBlocks), entryClocks) <-
           processes.zip(progressBlocks).zip(progressEntryClocks)) yield {
      val blockInvClauses =
        for (block <- progBlocks) yield {
          (for (clause@Clause(_, Seq(atom), _) <- block.invariants.iterator)
           yield (atom.pred, clause)).toMap
        }
      val blockDomains =
        blockInvClauses.map(_.keySet)
      
      // Replace predicates in all clauses with the new predicates, add resets
      // for the progress entry clocks
      val extendedClauses =
        for ((Clause(head, body, constraint), sync) <- clauses) yield {
          val globalTime = head.args(timeIndex)
          val enterProgress =
            for (dom <- blockDomains) yield {
              dom.contains(head.pred) && !body.exists(a => dom.contains(a.pred))
            }
          val subst =
            (for ((c, true) <- entryClocks.iterator zip enterProgress.iterator)
             yield (c -> globalTime)).toMap
          val newHead =
            ConstantSubstVisitor(toExtendedAtom(head), subst).asInstanceOf[IAtom]
          (Clause(newHead, body.map(toExtendedAtom), constraint),
           toExtendedSync(sync))
        }

      // For each predicate in a progress block, add the two delay transitions
      val progressPreds = blockDomains.foldLeft(Set[Predicate]())(_ ++ _)
      val delayClauses =
        (for (pred <- progressPreds.toSeq.sortBy(_.name)) yield {
          val invClausesAndClocks =
            for ((clauseMapping, clock) <- blockInvClauses zip entryClocks;
                clause <- clauseMapping.get(pred).toSeq)
            yield (clause, clock)
          
          assert(!invClausesAndClocks.isEmpty)

          val Clause(_, Seq(baseAtom), _) = invClausesAndClocks.head._1
          // TODO: generalize
          assert(baseAtom.args.toSet.size == baseAtom.args.size &&
                  baseAtom.args.forall(_.isInstanceOf[IConstant]))

          val invariantsAndClocks =
            for ((Clause(_, Seq(atom), inv), clock) <- invClausesAndClocks) yield {
              // TODO: generalize
              assert(atom.args.toSet.size == atom.args.size &&
                      atom.args.forall(_.isInstanceOf[IConstant]))
              val subst =
                (for ((IConstant(c), t) <- atom.args zip baseAtom.args)
                  yield (c -> t)).toMap
              (~ConstantSubstVisitor(inv, subst), clock)
            }

          val extBaseAtom = toExtendedAtom(baseAtom)
          val extBaseAtomCopy = IAtom(toPredCopy(extBaseAtom.pred), extBaseAtom.args)

          val time = extBaseAtom.args(timeIndex)

          val guard1 =
            and(for ((inv, clock) <- invariantsAndClocks)
                yield ((time === clock) | inv))

          val signalSubst =
            (for ((ind, newS) <- signalIndexesSorted zip lastContinuousSignalValue;
                  IConstant(s) = extBaseAtom(ind))
            yield (s -> i(newS))).toMap

          val guard2 = // TODO
            ConstantSubstVisitor(and(invariantsAndClocks.map(_._1)), signalSubst)

          List(
            (Clause(extBaseAtomCopy, List(extBaseAtom), guard1),
            BarrierSync(delayBarrier1)),
            (Clause(extBaseAtom, List(extBaseAtomCopy), guard2),
            BarrierSync(delayBarrier2))
          )
        }).flatten
      (extendedClauses, r)
    }

  val newAssertions =
    for (Clause(head, body, constraint) <- assertions)
    yield Clause(toExtendedAtom(head), body.map(toExtendedAtom), constraint)

  val newGlobalVarAssumptions =
    for (a <- globalVarAssumptions) yield {
      (ts : Seq[ITerm]) => a(ts.take(globalVarNum))
    }

  val result = System(newLocalProcesses,
                      newGlobalVarNum,
                      newAssertions,
                      newGlobalVarAssumptions,
                      hints,  // TODO
                      backgroundAxioms)

}