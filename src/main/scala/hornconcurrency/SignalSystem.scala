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
import ap.terfor.ConstantTerm

import lazabs.horn.Util
import lazabs.horn.bottomup.HornClauses
import lazabs.horn.bottomup.HornPredAbs.predArgumentSorts
import lazabs.horn.abstractions.{VerificationHints, EmptyVerificationHints}
import lazabs.horn.preprocessor.HornPreprocessor

import scala.collection.mutable.{LinkedHashSet, HashSet => MHashSet,
                                 ArrayBuffer, HashMap => MHashMap}
import lazabs.horn.global.HornClause
import hornconcurrency.System.NoBackgroundAxioms.predicates

object SignalSystem {
  import System._
  import HornClauses.Clause


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
            _accepts              : Seq[HornClauses.Clause] = Seq(),
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
      val accepts = _accepts
      
      
    } with SignalSystem

  import Rationals.{plus, minus, mul, zero, lessThan, lessThanOrEqual,
                    leq, lt, Fraction}

  object RatGtZero {
    def unapply(f : IFormula) : Option[ITerm] = f match {
      case IAtom(lessThan, Seq(t1, t2)) => Some(minus(t2, t1))
      case _                            => None
    }
  }

  object RatGeqZero {
    def unapply(f : IFormula) : Option[ITerm] = f match {
      case IAtom(lessThanOrEqual, Seq(t1, t2)) => Some(minus(t2, t1))
      case _                                   => None
    }
  }

  /**
   * Replace a rational <code>const</code> with
   * <code>newConst + epsilon</code> or <code>newConst - epsilon</code>.
   */
  class EpsilonSubstitutor(const       : ConstantTerm,
                           newConst    : ConstantTerm,
                           positiveEps : Boolean)
        extends CollectingVisitor[Unit, IExpression] {
    import IExpression._

    val ConstSum = Rationals.SymbolSum(i(const))

    def apply(f : IFormula) : IFormula =
      visit(f, ()).asInstanceOf[IFormula]

    override def preVisit(t : IExpression, arg : Unit) = t match {
      case RatGtZero(ConstSum(Const(num), Const(denom), rest)) => {
        assert(denom.signum > 0)
        val newTerm = plus(mul(Fraction(num, denom), i(newConst)), rest)
        if ((num.signum > 0) == positiveEps)
          // c + eps > 0  <=>  c >= 0
          ShortCutResult(leq(zero, newTerm))
        else
          // c - eps > 0  <=>  c > 0
          ShortCutResult(lt(zero, newTerm))
      }
      case RatGeqZero(ConstSum(Const(num), Const(denom), rest)) => {
        assert(denom.signum > 0)
        val newTerm = plus(mul(Fraction(num, denom), i(newConst)), rest)
        if ((num.signum > 0) == positiveEps)
          // c + eps >= 0  <=>  c >= 0
          ShortCutResult(leq(zero, newTerm))
        else
          // c - eps >= 0  <=>  c > 0
          ShortCutResult(lt(zero, newTerm))
      }
      case LeafFormula(t) if !ContainsSymbol.freeFromConstants(t, Set(const)) =>
        throw new Exception(
          "can only substitute with epsilon in the context of inequalities")
      case _ => {
        super.preVisit(t, arg)
      }
    }

    def postVisit(t : IExpression, arg : Unit, subres : Seq[IExpression]) =
      t update subres
  }

}

trait SignalSystem extends System {
  import System._
  import SignalSystem._
  import HornClauses.Clause


  def accepts : Seq[Clause]

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
  case class SignalSystemExtender(
        sorts: Seq[IExpression.Sort], 
        bodyTerms: Seq[ITerm],
        headTerms: Seq[ITerm],
        startIdx: Int = 0 //Where to insert terms
      ) {
        //Class for extending clauses in a Signal system with new global variables.
        def extendedProcessSet : ProcessSet = {
          processes.map{p =>
            val new_clauses = p._1.map{case (c, synch) =>(extendClause(c), synch)}
            (new_clauses, p._2)
          }
        }
        def extendedAssertions: Seq[Clause] = {
          assertions.map{extendClause}
        }
        def extendedProgressBlocks : Seq[Seq[ProgressBlock]] = {
          progressBlocks.map(_.map(pb => ProgressBlock(pb.invariants.map(extendClause))))
        } 
        def extendClause(c: Clause) : Clause = 
          c match {
            case Clause(head, body, constraint) => {
              val newHead = extendHeadAtom(head)
              val newBody = body.map(extendBodyAtom)
              Clause(newHead, newBody, constraint)
            }
          }
        def extendAtom(terms: Seq[ITerm])(atom: IAtom) : IAtom = {
          val old_sorts = predArgumentSorts(atom.pred)
          val old_args = atom.args
          val (sorts_pref, sorts_suff) = old_sorts.splitAt(startIdx)
          val (args_pref, args_suff) = old_args.splitAt(startIdx)

          IAtom(MonoSortedPredicate(
            atom.pred.name, 
            sorts_pref ++ sorts ++ sorts_suff), 
            args_pref ++ terms ++ args_suff 
          )
        }
        def extendedSignals = signals.map(startIdx +)
        def extendHeadAtom = extendAtom(headTerms)(_)
        def extendBodyAtom = extendAtom(bodyTerms)(_)


  }
  object SignalSystemExtender {
    // In case we want same body and head terms (I would expect this to be usual case)
    //StartIdx cannot have default argument here due to scala 2's weak type inference
    def apply(sorts: Seq[IExpression.Sort], terms: Seq[ITerm], startIdx: Int) =
      new SignalSystemExtender(sorts, terms, terms, startIdx)
  }
  //Combine this signal system with another signal system
  // Merges the global variables
  def combine(that: SignalSystem): SignalSystem = {
    //FIXME: may break if no progress blocks
    //or progress block without invariants
    val this_atom = this.progressBlocks.head.head.invariants.head.head
    val that_atom = that.progressBlocks.head.head.invariants.head.head
    
    val this_extender = SignalSystemExtender(
      predArgumentSorts(that_atom.pred), 
      that_atom.args,
      that_atom.args.size
    )
    val that_extender = that.SignalSystemExtender(
      predArgumentSorts(this_atom.pred), 
      this_atom.args,
      0
    )
    val new_globalVarAssumptions: Option[Seq[ITerm] => IFormula] = 
      (this.globalVarAssumptions, that.globalVarAssumptions) match {
        case (None, None) => None
        case (Some(this_a), None) => Some(ts => this_a(ts take this.globalVarNum))
        case (None, Some(that_a)) => Some(ts => that_a(ts takeRight that.globalVarNum))
        case (Some(this_a), Some(that_a)) => Some(
          ts => (this_a(ts take this.globalVarNum) &&& that_a(ts takeRight that.globalVarNum))
        )
      }
    val new_backgroundAxioms = SomeBackgroundAxioms(
      this.backgroundAxioms.predicates ++ that.backgroundAxioms.predicates,
      this.backgroundAxioms.clauses.map(this_extender.extendClause) ++ 
        that.backgroundAxioms.clauses.map(that_extender.extendClause)
    )
    SignalSystem(
      this_extender.extendedProcessSet ++ that_extender.extendedProcessSet,
      this.globalVarNum + that.globalVarNum,
      this_extender.extendedAssertions ++ that_extender.extendedAssertions,
      this.timeSpec,
      this.signals ++ that_extender.extendedSignals,
      this_extender.extendedProgressBlocks ++ that_extender.extendedProgressBlocks,
      this.accepts ++ that.accepts,
      new_globalVarAssumptions,
      this.hints ++ that.hints,
      new_backgroundAxioms
        //FIXME
        //FIXME
    )
      
  } 
  


  // Transform accept clauses to the ranking functions such that the system has no failing asserts
  // if the original system is empty (has no infinite runs with each accepting set being visited infinitely often)
  def transFormAcceptsToEmptiness(rankFuncs: Map[Int, ITerm]): SignalSystem = {
    //NOTE: This assumes all constant terms in the rank functions are already 
    // defined in the clauses as global vars. I.e., we expect that the signalsystem
    // should have been already merged with the SignalSystem of the program to verify.
    def isTrue(t: ITerm) : IFormula = t === ap.theories.ADT.BoolADT.True 
    def isFalse(t: ITerm): IFormula = t === ap.theories.ADT.BoolADT.False
    val new_globalVarNum = globalVarNum + rankFuncs.size
    val rankValues_sorts =
        List.fill(rankFuncs.size)(IExpression.Sort.Integer)
    val rankValues_bodyTerms = rankFuncs.map{case (k, _) => 
      IExpression.i(IExpression.Sort.Integer.newConstant(s"rank$k"))
    }.toSeq
    val rankValues_headTerms = rankFuncs.map{case (k, _) => 
      IExpression.i(IExpression.Sort.Integer.newConstant(s"newRank$k"))
    }.toSeq
    val rankValid_sorts = List.fill(rankFuncs.size)(IExpression.Sort.Bool)
    val rankValid_headTerms = rankFuncs.map{case (k, _) => 
      IExpression.i(IExpression.Sort.Bool.newConstant(s"newRank$k"))
    }.toSeq
    val rankValid_bodyTerms = rankFuncs.map{case (k, _) => 
      IExpression.i(IExpression.Sort.Bool.newConstant(s"newRank$k"))
    }.toSeq
    val rank_sorts = rankValues_sorts ++ rankValid_sorts
    val rank_headTerms = rankValues_headTerms ++ rankValid_headTerms
    val rank_bodyTerms = rankValues_bodyTerms ++ rankValid_bodyTerms

    
    def extendClauseWithRank(clause: Clause) = clause match {
      case Clause(head, body, constraint) => {
        val newHead = //extender.extendHeadAtom(head)
          IAtom(MonoSortedPredicate(head.pred.name, rank_sorts), rank_headTerms)
        val newBody = body.map( b => 
          IAtom(MonoSortedPredicate(b.pred.name, rank_sorts), rank_bodyTerms)
        )
        val zipped = rankValues_bodyTerms.zip(rankValues_headTerms).
                      zip(rankValid_bodyTerms).zip(rankValid_headTerms)
        val newConstraint = IExpression.and(zipped.map{
          case (((valb, valh), validb), validh) => 
          (isFalse(validb) ===> isFalse(validh)) & 
            (isTrue(validh) ===> (valh <= valb)) & constraint
        })
        Clause(newHead, newBody, newConstraint)
      }
    }
    val new_processSet = //extender.extendProcessSet(processes)
      processes.map{p =>
        val new_clauses = p._1.map{case (c, synch) => 
          (extendClauseWithRank(c), synch)
        }
        (new_clauses, p._2)
      }
    val new_progressBlocks = 
      progressBlocks.map(_.map(pb => 
        ProgressBlock(pb.invariants.map(extendClauseWithRank))))
    // val asserts = accepts.map{ case Clause(head, body, constraint) =>
    
    def extractRankID(s: String): Option[Int] = {
      val Pattern = """.*_rank(\d+)$""".r
      s match {
        case Pattern(numStr) =>
          // Safe conversion to Int
          scala.util.Try(numStr.toInt).toOption
        case _ => None
      }
    }

    val extender = SignalSystemExtender(rank_sorts, rank_bodyTerms, 0)
    val acceptAssertions = accepts.map{ 
      case Clause(head, body, constraint) => 
          val rankFunc = extractRankID(head.pred.name) match {
            case Some(rank) => rankFuncs.get(rank).get
            case None => ??? // FIXME: What happens if no rank function exists?
          } 
          val zipped = rankValues_bodyTerms.zip(rankValues_headTerms).
            zip(rankValid_bodyTerms).zip(rankValid_headTerms)
          val newConstraint = IExpression.and(zipped.map{
            case (((valb, valh), validb), validh) => 
            (isFalse(validb) ===> isFalse(validh)) & 
              (isTrue(validh) ===> (valh < valb)) & 
              IExpression.or(rankValid_headTerms.map(isTrue)) & 
              valh === rankFunc
              constraint
          })  
          val newBody = body.map(extender.extendBodyAtom)
          //Assert right-hand by setting lhs to FALSE 
          Clause(IAtom(HornClauses.FALSE, Seq()), newBody, newConstraint)
    }

    // assume assertions just carry along the rank terms
    val newAssertions = extender.extendedAssertions

    SignalSystem(
      new_processSet,
      new_globalVarNum,
      newAssertions ++ acceptAssertions,
      timeSpec,
      signals,
      new_progressBlocks,
      Seq(),
      globalVarAssumptions,
      hints,
      backgroundAxioms
    )
  }
}

// Not finished yet
class SignalEncoder(system : SignalSystem) {
  import system._
  import System._
  import SignalSystem._
  import Rationals.{dom => Rat}
  import IExpression._
  import HornClauses.Clause

  // We need to introduce copies of the signal variables as global variables
  val newGlobalVarNum = globalVarNum + signals.size
  val newGlobalVarSorts = globalVarSorts ++ (0 until signals.size).map(x => Rat)

  val signalIndexesSorted =
    signals.toSeq.sorted
  val lastContinuousSignalValue =
    signalIndexesSorted.map(ind => Sort.Bool.newConstant(s"sig$ind"))
  val lastContinuousSignalIndexesSorted =
    globalVarNum until newGlobalVarNum
  val allSignalIndexes =
    signalIndexesSorted ++ lastContinuousSignalIndexesSorted

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

  val progressInvariantClauses =
    for (progBlocks <- progressBlocks) yield
      for (block <- progBlocks) yield {
        (for (clause@Clause(_, Seq(atom), _) <- block.invariants.iterator)
         yield (atom.pred, clause)).toMap
      }
  val progressDomains =
    progressInvariantClauses.map(
      blocks => blocks.map(_.keySet).foldLeft(Set[Predicate]())(_ ++ _)
    )

  // For each local predicate inside a progress block,
  // we need a copy to represent environment transitions
  val toPredCopy =
    (for (preds <- progressDomains.iterator;
          p <- preds.iterator;
          extP = toExtendedPred(p);
          newP = MonoSortedPredicate(extP.name + "_delay",
                                     predArgumentSorts(extP) :+ Rat))
     yield (extP -> newP)).toMap

  val timeIndex = timeSpec.index

  val localTimeCopy =
    Rat.newConstant("LastC")

  val envPreds =
    List(MonoSortedPredicate("Env0", newGlobalVarSorts),
         MonoSortedPredicate("Env1", newGlobalVarSorts),
         MonoSortedPredicate("Env2", newGlobalVarSorts))

  val newLocalPreds =
    (for (preds <- extendedLocalPreds) yield {
      val copies = preds.collect(toPredCopy)
      preds ++ copies
    }) :+ envPreds

  val delayBarrier1 =
    new SimpleBarrier("DelayBarrier1", newLocalPreds.map(_.toSet))
  val delayBarrier2 =
    new SimpleBarrier("DelayBarrier2", newLocalPreds.map(_.toSet))

  val delayClauses = {
    val args =
      for ((s, n) <- newGlobalVarSorts.zipWithIndex) yield i(s.newConstant(s"a$n"))
    val time =
      args(timeIndex)
    val newTime =
      i(Rat.newConstant(s"b$timeIndex"))
    val updatedArgs =
      allSignalIndexes.foldLeft(args.updated(timeIndex, newTime)) {
        case (args, n) => args.updated(n, i(Sort.Bool.newConstant(s"b$n")))
      }
    List(
      (Clause(envPreds(0)(args : _*), List(), true),
       NoSync),
      (Clause(envPreds(1)(args : _*), List(envPreds(0)(args : _*)), true),
       BarrierSync(delayBarrier1)),
      (Clause(envPreds(2)(updatedArgs : _*),
         List(envPreds(1)(args : _*)),
         Rationals.gt(newTime, time)),
       NoSync),
      (Clause(envPreds(0)(args : _*), List(envPreds(2)(args : _*)), true),
       BarrierSync(delayBarrier2))
    )
  }

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

  val newLocalProcesses =
    for (((((clauses, r), progBlocks), entryClocks), blockInvClauses) <-
           processes.zip(progressBlocks)
                    .zip(progressEntryClocks)
                    .zip(progressInvariantClauses)) yield {
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
          val time = extBaseAtom.args(timeIndex)
          val IConstant(timeConst) = time

          val guard1 =
            and(for ((inv, clock) <- invariantsAndClocks)
                yield ((time === clock) | inv))

          val signalSubst =
            (for ((ind, newS) <- signalIndexesSorted zip lastContinuousSignalValue;
                  IConstant(s) = extBaseAtom(ind))
            yield (s -> i(newS))).toMap
          val guard2Conj =
            ConstantSubstVisitor(and(invariantsAndClocks.map(_._1)), signalSubst)

          val guard2Parts =
            LineariseVisitor(Transform2NNF(guard2Conj), IBinJunctor.And)
          val (timedGuard2Parts, untimedGuard2Parts) =
            guard2Parts.partition(f => SymbolCollector.constants(f)(timeConst))

          val clockSubst1 =
            new EpsilonSubstitutor(timeConst, localTimeCopy, true)
          val clockSubst2 =
            new EpsilonSubstitutor(timeConst, timeConst, false)

          val guard2 =
            clockSubst1(and(timedGuard2Parts)) &&&
            clockSubst2(and(timedGuard2Parts)) &&&
            and(untimedGuard2Parts)

          List(
            (Clause(IAtom(toPredCopy(extBaseAtom.pred),
                          extBaseAtom.args :+ time),
                    List(extBaseAtom),
                    guard1),
             BarrierSync(delayBarrier1)),
            (Clause(extBaseAtom,
                    List(IAtom(toPredCopy(extBaseAtom.pred),
                               extBaseAtom.args :+ i(localTimeCopy))),
                    guard2),
             BarrierSync(delayBarrier2))
          )
        }).flatten
      (extendedClauses ++ delayClauses, r)
    }

  val newAssertions =
    for (Clause(head, body, constraint) <- assertions)
    yield Clause(toExtendedAtom(head), body.map(toExtendedAtom), constraint)

  val newGlobalVarAssumptions =
    for (a <- globalVarAssumptions) yield {
      (ts : Seq[ITerm]) => a(ts.take(globalVarNum))
    }

  val result = System(newLocalProcesses :+ (delayClauses, Singleton),
                      newGlobalVarNum,
                      newAssertions,
                      newGlobalVarAssumptions,
                      hints,  // TODO
                      backgroundAxioms)

}
