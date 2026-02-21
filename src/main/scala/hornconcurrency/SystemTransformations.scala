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

object SystemTransformations {
  import HornClauses.Clause
  import IExpression._
  import System._
  import VerificationHints._
  import Combinatorics._

  /**
   * Create a finite instance of a parametric model,
   * by replacing infinite processes with a finite number of
   * singleton processes
   */
  def finitise(system          : System,
               instanceNumbers : Seq[Option[Range]]) : System = {
    import system._

    assert(instanceNumbers.size == processes.size &&
            ((instanceNumbers.iterator zip processes.iterator) forall {
              case (None, _)                => true
              case (Some(_), (_, Infinite)) => true
              case _                        => false
            }))

    val newPredicateHints =
      new MHashMap[IExpression.Predicate, Seq[VerifHintElement]]

    val predMappings =
      (for (((n, (process, _)), i) <-
              (instanceNumbers.iterator zip processes.iterator).zipWithIndex;
            j <- (n getOrElse (0 until 1)).iterator) yield {

          val mapping =
            (for (p <- localPreds(i).iterator) yield n match {
              case None =>
                p -> p
              case _ =>
                p -> MonoSortedPredicate(p.name + "_" + j,
                                          predArgumentSorts(p))
            }).toMap

          for ((a, b) <- mapping)
            (hints.predicateHints get a) match {
              case Some(preds) => newPredicateHints.put(b, preds)
              case None => // nothing
            }

          (mapping + (HornClauses.FALSE -> HornClauses.FALSE) ++
                    (for (p <- backgroundPreds) yield (p -> p)),
          i, for (_ <- n) yield j)
        }).toList

    def updateClause(clause : Clause,
                      mapping : Map[Predicate, Predicate],
                      id : Option[Int]) = {
      val Clause(head@IAtom(headP, headArgs), body, constraint) = clause
      val idConstraint : IFormula = id match {
        case None =>
          true
        case Some(id) =>
          (body ++ List(head)).head.args(globalVarNum) === id
      }
      Clause(IAtom(mapping(headP), headArgs),
              for (IAtom(p, a) <- body)
                yield IAtom(mapping(p), a),
              constraint &&& idConstraint)
    }

    val barrierMapping =
      (for (b <- barriers.iterator) yield {
          val newDomains =
            for ((m, i, _) <- predMappings) yield (b.domains(i) map m)
          b match {
            case b : SimpleBarrier =>
              b -> new SimpleBarrier(b.name, newDomains)
            case b : BarrierFamily =>
              b -> new BarrierFamily(b.name, newDomains,
                                    b.equivalentProcesses)
          }
        }).toMap

    val newProcesses = for ((mapping, i, j) <- predMappings) yield {
      val (oriProcess, t) = processes(i)

      val newProcess =
        for ((clause, sync) <- oriProcess) yield {
        val newSync = sync match {
          case BarrierSync(b) => BarrierSync(barrierMapping(b))
          case s              => s
        }
        (updateClause(clause, mapping, j), newSync)
      }

      (newProcess, if (instanceNumbers(i).isDefined) Singleton else t)
    }

    val newAssertions =
      (for (Clause(head, ClauseBody(processAtoms, backgroundAtoms),
                    constraint) <- assertions.iterator;
            allAtomsVec =
              for (IAtom(p, args) <- processAtoms) yield (
                  for ((m, _, _) <- predMappings;
                    if (m contains p)) yield IAtom(m(p), args));
            newBody <- cartesianProduct(allAtomsVec);
            if ((for (IAtom(p, _) <- newBody.iterator) yield p).toSet.size ==
                processAtoms.size))
        yield (Clause(head, newBody ++ backgroundAtoms, constraint))).toList

    system match {
      case system : TimedSystem => {
        import system.{timeInvariants, timeSpec}
        val newTimeInvs =
          (for ((mapping, i, j) <- predMappings.iterator;
                clause@Clause(_, Seq(IAtom(p, _)), _) <- timeInvariants.iterator;
               if (mapping contains p))
            yield updateClause(clause, mapping, j)).toList

        TimedSystem(newProcesses, globalVarNum, newAssertions,
                    timeSpec, newTimeInvs, globalVarAssumptions,
                    VerificationHints(newPredicateHints.toMap),
                    backgroundAxioms)
      }
      case system => {
        System(newProcesses, globalVarNum, newAssertions, globalVarAssumptions,
               VerificationHints(newPredicateHints.toMap),
               backgroundAxioms)
      }
    }
  }

  /**
   * Produce a smaller equi-safe system by merging transitions that only
   * concern local variables.
   */
  def mergeLocalTransitions(system           : System,
                            predicatesToKeep : Set[Predicate] = Set())
                          : System =
    mergeLocalTransitionsWithBackMapping(system, predicatesToKeep)._1

  /**
   * Produce a smaller equi-safe system by merging transitions that only
   * concern local variables. The second result component maps new clauses back
   * to (transition or assertion) clauses of the original system.
   */
  def mergeLocalTransitionsWithBackMapping(system           : System,
                                           predicatesToKeep : Set[Predicate] =
                                                              Set())
                                        : (System, Map[Clause, Seq[Clause]]) = {
    import system._

    val backMapping = new MHashMap[Clause, Seq[Clause]]

    val predsToKeep, predsWithTimeInvs = new MHashSet[Predicate]
    system match {
      case system : TimedSystem =>
        for (c <- system.timeInvariants) {
          predsToKeep ++= c.predicates
          predsWithTimeInvs ++= c.predicates
        }
      case _ =>
        // nothing
    }
    for (c <- assertions)
      predsToKeep ++= c.predicates

    // also keep initial states
    for (clauses <- localInitClauses.iterator; c <- clauses.iterator)
      predsToKeep ++= c.predicates

    // lastly keep all other requested preds
    predsToKeep ++= predicatesToKeep

    def isLocalClause(p : (Clause, Synchronisation)) = p match {
      case (clause@Clause(head@IAtom(_, headArgs),
                          ClauseBody(body@List(IAtom(_, bodyArgs)), _),
                          constraint), NoSync) =>
        Seqs.disjoint(predsWithTimeInvs, clause.predicates) && {
        val globalHeadArgs =
          (for (IConstant(c) <- headArgs take globalVarNum) yield c).toSet

        (globalHeadArgs.size == globalVarNum) &&
        (headArgs take globalVarNum) == (bodyArgs take globalVarNum) && {
          val occurringConstants = new MHashSet[ConstantTerm]
          val coll = new SymbolCollector(null, occurringConstants, null)
          coll.visitWithoutResult(constraint, 0)
          for (IAtom(_, args) <- (Iterator single head) ++ body.iterator)
            for (t <- args drop globalVarNum)
              coll.visitWithoutResult(t, 0)
          Seqs.disjoint(globalHeadArgs, occurringConstants)
        }
      }
      case _ => false
    }

    val newProcesses =
      (for (((clauses, repl), preds) <-
              processes.iterator zip localPreds.iterator) yield {
        val clauseBuffer = clauses.toBuffer

        // sort the predicates, to eliminate first predicates with high arity,
        // and then predicates with few incoming clauses
        val predsBuffer =
          ((for (pred <- preds.iterator;
                  if !(predsToKeep contains pred);
                  incoming =
                    for (p@(Clause(IAtom(`pred`, _), _, _), _) <- clauseBuffer)
                    yield p)
            yield (pred, incoming.size)).toVector
                                        .sortBy(t => (-t._1.arity, t._2))
                                        .map(_._1)).toBuffer


        val predIncomingMap = new MHashMap[Predicate, ArrayBuffer[(Clause, Synchronisation)]]
        val predOutgoingMap = new MHashMap[Predicate, ArrayBuffer[(Clause, Synchronisation)]]

        // todo: merge with above loop?
        for (pred <- preds.iterator) {
          predIncomingMap += ((pred, new ArrayBuffer[(Clause, Synchronisation)]))
          predOutgoingMap += ((pred, new ArrayBuffer[(Clause, Synchronisation)]))
          for (clause <- clauseBuffer) {
            clause match {
              case c@(Clause(IAtom(`pred`, _), _, _), _) =>
                predIncomingMap(pred) += c
              case c@(Clause(_, ClauseBody(List(IAtom(`pred`, _)), _), _), _) =>
                predOutgoingMap(pred) += c
              case _ =>
            }
          }
        }

        var changed = true
        while (changed) {
          changed = false

          val predsIt = predsBuffer.iterator
          while (!changed && predsIt.hasNext) {
            val pred = predsIt.next
            val incoming = predIncomingMap(pred)
            val outgoing = predOutgoingMap(pred)

            if (// avoid blow-up
                (incoming.size * outgoing.size <=
                    incoming.size + outgoing.size) &&
                (incoming forall {
                    case (c, _) => !(c.bodyPredicates contains pred) &&
                                  (!outgoing.isEmpty ||
                                    Seqs.disjoint(predsWithTimeInvs,
                                                  c.predicates))
                  }) &&
                (outgoing forall {
                    case (c, _) => c.head.pred != pred
                  })) {

              val newClauses =
                if (incoming forall (isLocalClause(_)))
                  for ((c1, _) <- incoming; (c2, s) <- outgoing;
                        newClause = merge(c2, c1);
                        if !newClause.hasUnsatConstraint)
                    yield {
                      val originalClauses : Seq[Clause] =
                        backMapping.getOrElse(c1, Seq(c1)) ++
                          backMapping.getOrElse(c2, Seq(c2))
                      backMapping.put(newClause, originalClauses)
                      (newClause, s)
                    }
                else if (!outgoing.isEmpty &&
                          (outgoing forall (isLocalClause(_))))
                  for ((c1, s) <- incoming; (c2, _) <- outgoing;
                        newClause = merge(c2, c1);
                        if !newClause.hasUnsatConstraint)
                    yield {
                      val originalClauses : Seq[Clause] =
                        backMapping.getOrElse(c1, Seq(c1)) ++
                          backMapping.getOrElse(c2, Seq(c2))
                      backMapping.put(newClause, originalClauses)
                      (newClause, s)
                    }
                else
                  null

              if (newClauses != null) {
                predsBuffer -= pred
                changed = true

                for (c@(Clause(IAtom(p1, _),
                               ClauseBody(List(IAtom(p2, _)), _), _), _) <-
                       incoming ++ outgoing) {
                  predIncomingMap(p1) -= c
                  predOutgoingMap(p2) -= c
                }

                for (c@(Clause(IAtom(p1, _),
                               ClauseBody(List(IAtom(p2, _)), _), _), _) <-
                       newClauses) {
                  predIncomingMap(p1) += c
                  predOutgoingMap(p2) += c
                }

              }
            }
          }
        }
        ((for ((_, clauses) <- predIncomingMap) yield
          clauses).flatten.toList, repl)
      }).toList

    val allPreds = allPredicates(newProcesses) + HornClauses.FALSE

    val newAssertions =
      assertions filter {
        clause => clause.predicates subsetOf (allPreds ++ backgroundPreds) }
    newAssertions.foreach(clause => backMapping.put(clause, Seq(clause)))

    // we need to remove deleted predicates also from the barriers
    val newBarriers = new MHashMap[Barrier, Barrier]

    def filterBarrier(b : Barrier) =
      newBarriers.getOrElseUpdate(b, b filterDomains allPreds)

    val newProcesses2 =
      for ((process, repl) <- newProcesses) yield {
        val newClauses =
          for ((clause, sync) <- process) yield sync match {
            case BarrierSync(b) => (clause, BarrierSync(filterBarrier(b)))
            case s              => (clause, s)
          }
        (newClauses, repl)
      }

    val newSystem =
      system match {
        case system : TimedSystem =>
          TimedSystem(newProcesses2,
                      globalVarNum,
                      newAssertions,
                      system.timeSpec,
                      system.timeInvariants,
                      globalVarAssumptions,
                      hints filterPredicates allPreds,
                      backgroundAxioms)
        case system =>
          System     (newProcesses2,
                      globalVarNum,
                      newAssertions,
                      globalVarAssumptions,
                      hints filterPredicates allPreds,
                      backgroundAxioms)
      }

    val mapping =
      backMapping.filter {
        case (newC, _) =>
          newSystem.processes.exists(p => p._1.exists(_._1 == newC)) ||
            newAssertions.contains(newC)
      }.toMap

    (newSystem, mapping)
  }

  /**
   * Given clauses p(...) :- ..., q(...), ... (clause1)
   * and q(...) :- body (clause2),
   * generate a clause p(...) :- ..., body, ... by inlining.
   */
  def merge(clause1 : HornClauses.Clause,
            clause2 : HornClauses.Clause) : HornClauses.Clause = {
    import clause1._
    import HornClauses.Clause
    import IExpression._
    if (body.size == 1) {
      clause1 mergeWith clause2
    } else {
      val Clause(IAtom(thatHeadPred, thatHeadArgs),
                  thatBody, thatConstraint) = clause2
      val (List(IAtom(_, thisBodyArgs)), thisBodyRem) =
        body partition (_.pred == thatHeadPred)

      if ((thisBodyArgs forall (_.isInstanceOf[IConstant])) &&
          (thisBodyArgs.toSet.size == thisBodyArgs.size) &&
          HornClauses.allTermsSimple(thatHeadArgs)) {
        // can directly inline

        val replacement =
          new MHashMap[ConstantTerm, ITerm]
        val definedConsts =
          (for (IConstant(c) <- thisBodyArgs.iterator) yield c).toSet
        for (c <- constants)
          if (!(definedConsts contains c))
            replacement.put(c, i(c.clone))

        for ((IConstant(c), t) <-
                thisBodyArgs.iterator zip thatHeadArgs.iterator)
          replacement.put(c, t)

        def replace(f : IFormula) =
          SimplifyingConstantSubstVisitor(f, replacement)

        Clause(replace(head).asInstanceOf[IAtom],
                (for (a <- thisBodyRem)
                  yield replace(a).asInstanceOf[IAtom]) ::: thatBody,
                replace(constraint) &&& thatConstraint)
      } else {
        val (Clause(newHead, newBody, newConstraint), _) =
          refresh
        val (List(IAtom(_, newBodyArgs)), newBodyRem) =
          newBody partition (_.pred == thatHeadPred)
        Clause(newHead, newBodyRem ::: thatBody,
                newConstraint &&& thatConstraint &&&
                (newBodyArgs === thatHeadArgs))
      }
    }
  }
}
