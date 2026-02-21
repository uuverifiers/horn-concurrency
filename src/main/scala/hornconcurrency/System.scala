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
import ap.theories.rationals.Rationals
import ap.util.{Seqs, Combinatorics}

import lazabs.horn.Util
import lazabs.horn.bottomup.HornClauses
import lazabs.horn.bottomup.HornPredAbs.predArgumentSorts
import lazabs.horn.abstractions.{VerificationHints, EmptyVerificationHints}
import lazabs.horn.preprocessor.HornPreprocessor

import scala.collection.mutable.{LinkedHashSet, HashSet => MHashSet,
                                 ArrayBuffer, HashMap => MHashMap}

object System {

  abstract sealed class Replication
  case object Singleton extends Replication
  case object Infinite  extends Replication

  abstract sealed class TimeSpec
  case class  DiscreteTime(index : Int)                        extends TimeSpec
  case class  ContinuousTime(numIndex : Int, denomIndex : Int) extends TimeSpec
  case class  RationalTime(index : Int)                        extends TimeSpec

  type Process = Seq[(HornClauses.Clause, Synchronisation)]
  type ProcessSet = Seq[(Process, Replication)]

  def allPredicates(processes : ProcessSet) : Set[IExpression.Predicate] =
    (for ((proc, _) <- processes.iterator;
          (c, _) <- proc.iterator;
          p <- c.predicates.iterator)
     yield p).toSet


  //////////////////////////////////////////////////////////////////////////////

  abstract sealed class Synchronisation
  case object NoSync                         extends Synchronisation
  case class  Send(chan : CommChannel)       extends Synchronisation
  case class  Receive(chan : CommChannel)    extends Synchronisation
  case class  BarrierSync(barrier : Barrier) extends Synchronisation

  class CommChannel(name : String) {
    override def toString = name
  }

  //////////////////////////////////////////////////////////////////////////////

  object Barrier {
    def unapply(b : Barrier) = Some(b.domains)
  }

  abstract sealed class Barrier(val name : String,
                                val domains : Seq[Set[IExpression.Predicate]]) {
    override def toString = name
    def filterDomains(remainingPreds : Set[IExpression.Predicate]) : Barrier
  }

  class SimpleBarrier(_name : String,
                      _domains : Seq[Set[IExpression.Predicate]])
    extends Barrier(_name, _domains) {
    def filterDomains(remainingPreds : Set[IExpression.Predicate])
                    : SimpleBarrier =
      new SimpleBarrier(name, for (d <- domains) yield (d & remainingPreds))
  }

  /**
   * A family of barriers is specified like a simple barrier, but in
   * addition an equivalence relation has to be provided that describes
   * which processes can synchronise on the same barriers.
   */
  class BarrierFamily(_name : String,
                      _domains : Seq[Set[IExpression.Predicate]],
                      val equivalentProcesses :
                        (ITerm, ITerm, ITerm, ITerm) => IFormula)
    extends Barrier(_name, _domains) {
    def filterDomains(remainingPreds : Set[IExpression.Predicate])
                    : BarrierFamily =
      new BarrierFamily(name,
                        for (d <- domains) yield (d & remainingPreds),
                        equivalentProcesses)
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Specification of possible background axioms that can be used in the
   * transition or assertion clauses. Background predicates are not
   * allowed in time invariant clauses
   */
  sealed abstract class BackgroundAxioms {
    def predicates : Seq[IExpression.Predicate]
    def clauses : Seq[HornClauses.Clause]
  }

  case object NoBackgroundAxioms
              extends BackgroundAxioms {
    def predicates : Seq[IExpression.Predicate] = List()
    def clauses : Seq[HornClauses.Clause] = List()
  }

  case class  SomeBackgroundAxioms(predicates : Seq[IExpression.Predicate],
                                   clauses : Seq[HornClauses.Clause])
              extends BackgroundAxioms

  /**
   * Create an untimed system.
   */
  def apply(_processes            : ProcessSet,
            _globalVarNum         : Int,
            _assertions           : Seq[HornClauses.Clause],
            _globalVarAssumptions : Option[Seq[ITerm] => IFormula] = None,
            _hints                : VerificationHints = EmptyVerificationHints,
            _backgroundAxioms     : BackgroundAxioms = NoBackgroundAxioms)
                                  : System =
    new {
      val processes = _processes
      val globalVarNum = _globalVarNum
      val globalVarAssumptions = _globalVarAssumptions
      val assertions = _assertions
      val hints = _hints
      val backgroundAxioms = _backgroundAxioms
    } with System
}

/**
 * General trait for concurrent systems.
 */
trait System {
  import HornClauses.Clause
  import IExpression._
  import System._

  // Fields to be instantiated in an actual system. Note that the fields have
  // to be initialized before the constructor of the trait System is executed.
  def processes            : ProcessSet
  def globalVarNum         : Int
  def globalVarAssumptions : Option[Seq[ITerm] => IFormula]
  def assertions           : Seq[HornClauses.Clause]
  def hints                : VerificationHints
  def backgroundAxioms     : BackgroundAxioms

  val backgroundPreds = backgroundAxioms.predicates.toSet

  def isBackgroundAtom(a : IAtom) : Boolean = backgroundPreds contains a.pred

  for (c <- backgroundAxioms.clauses)
    assert(c.predicates subsetOf (backgroundPreds + HornClauses.FALSE))

  // Extractor to partition the body of a clause into the local process
  // predicates and the background predicates
  object ClauseBody {
    def unapply(body : List[IAtom]) : Option[(List[IAtom], List[IAtom])] =
      if (backgroundPreds.isEmpty)
        Some(body, List())
      else
        Some(body partition ((a) => !isBackgroundAtom(a)))
  }

  val localPreds = for ((process, _) <- processes) yield {
    val preds = new LinkedHashSet[Predicate]
    for ((c, _) <- process)
      for (p <- c.predicates)
        if (!(backgroundPreds contains p))
          preds += p
    preds.toSeq
  }

  val allLocalPreds =
    (for (preds <- localPreds.iterator; p <- preds.iterator) yield p).toSet

  assert(hints.predicateHints.keys forall (allLocalPreds ++ backgroundPreds))

  val globalVarSorts =
    predArgumentSorts(allLocalPreds.iterator.next) take globalVarNum

  val localPredsSet = for (preds <- localPreds) yield preds.toSet

  val processIndex =
    (for ((preds, i) <- localPreds.iterator.zipWithIndex;
          p <- preds.iterator)
      yield (p, i)).toMap

  // we assume that all processes use distinct sets of predicates
  {
    val allPreds = new MHashSet[Predicate]
    for (preds <- localPreds.iterator; p <- preds.iterator) {
      val b = allPreds add p
      assert(b, "Processes need to use distinct control predicates")
    }
  }

  val localInitClauses =
    for ((process, _) <- processes) yield
      (for ((c@Clause(_, body, _), NoSync) <- process.iterator;
            if body forall isBackgroundAtom)
        yield c).toList

  val localPredRanking =
    (for (preds <- localPreds.iterator; p <- preds.iterator)
      yield p).zipWithIndex.toMap

  val barriers = {
    val res = new LinkedHashSet[Barrier]
    for ((process, _) <- processes.iterator;
          (_, BarrierSync(b)) <- process.iterator)
      res += b
    res.toSeq
  }

  // barrier specifications have to be consistent with processes
  // in the system
  assert(barriers forall {
    case Barrier(doms) =>
      doms.size == processes.size &&
      ((0 until doms.size) forall { i => doms(i) subsetOf localPredsSet(i) })
  })

  // barrier synchronisation can only occur within the domain
  // of the barrier
  assert(processes forall { case (process, _) =>
          process forall {
            case (Clause(_, List(IAtom(pred, _)), _),
                  BarrierSync(Barrier(doms))) =>
              doms(processIndex(pred)) contains pred
            case _ => true
          }})

}

object TimedSystem {
  import System._

  /**
   * Create a timed system.
   */
  def apply(_processes            : ProcessSet,
            _globalVarNum         : Int,
            _assertions           : Seq[HornClauses.Clause],
            _timeSpec             : TimeSpec,
            _timeInvariants       : Seq[HornClauses.Clause] = List(),
            _globalVarAssumptions : Option[Seq[ITerm] => IFormula] = None,
            _hints                : VerificationHints = EmptyVerificationHints,
            _backgroundAxioms     : BackgroundAxioms = NoBackgroundAxioms)
                                  : TimedSystem =
    new {
      val processes = _processes
      val globalVarNum = _globalVarNum
      val globalVarAssumptions = _globalVarAssumptions
      val assertions = _assertions
      val hints = _hints
      val backgroundAxioms = _backgroundAxioms
      val timeSpec = _timeSpec
      val timeInvariants = _timeInvariants
    } with TimedSystem

}

trait TimedSystem extends System {
  import HornClauses.Clause
  import IExpression._
  import System._

  def timeSpec       : TimeSpec
  def timeInvariants : Seq[HornClauses.Clause]

  for (c <- timeInvariants)
    assert(Seqs.disjoint(c.predicates - HornClauses.FALSE, backgroundPreds))

}
