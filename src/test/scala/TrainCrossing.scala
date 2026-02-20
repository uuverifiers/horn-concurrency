/**
 * Copyright (c) 2011-2026 Philipp Ruemmer, Zafer Esen. All rights reserved.
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

import org.scalatest._

import ap.parser._
import ap.theories.rationals.Rationals
import ap.types.MonoSortedPredicate
import lazabs.horn.Util
import lazabs.horn.bottomup.{HornClauses, HornPredAbs}

class TrainCrossing extends FlatSpec {
  import HornClauses._
  import IExpression._
  import ParametricEncoder._
  import VerificationUtils._

  ap.util.Debug enableAllAssertions true

  "Train crossing example with ContinuousTime" should "be SOLVABLE" in {
    val train = for (i <- 0 to 4) yield (new Predicate("train" + i, 4 + 3))
    val gate  = for (i <- 0 to 5) yield (new Predicate("gate" + i, 4 + 3))

    val C = new ConstantTerm("C")
    val U = new ConstantTerm("U")
    val e = new ConstantTerm("e")
    val ticket = new ConstantTerm("ticket")
    val my_ticket = new ConstantTerm("my_ticket")
    val my_ticket2 = new ConstantTerm("my_ticket2")
    val next_waiting_ticket = new ConstantTerm("next_waiting_ticket")
    val next_available_ticket = new ConstantTerm("next_available_ticket")
    val x = new ConstantTerm("x")
    val x2 = new ConstantTerm("x2")
    val y = new ConstantTerm("y")
    val id = new ConstantTerm("id")
    val id2 = new ConstantTerm("id2")

    val go = new CommChannel("go")
    val appr = new CommChannel("appr")
    val leave = new CommChannel("leave")
    val stop = new CommChannel("stop")

    val gateProcess = List(

      (gate(1)(C, U, e, ticket, next_waiting_ticket, next_available_ticket, C) :- true,               NoSync),

      (gate(5)(C, U, e, ticket, next_available_ticket, next_available_ticket, y) :-
         gate(1)(C, U, e, ticket, next_waiting_ticket, next_available_ticket, y),                     NoSync),

      (gate(3)(C, U, e, next_waiting_ticket, next_waiting_ticket+1, next_available_ticket, y) :-
         (gate(5)(C, U, e, ticket, next_waiting_ticket, next_available_ticket, y),
          next_waiting_ticket < next_available_ticket),                                               NoSync),

      (gate(2)(C, U, e, ticket, next_waiting_ticket, next_available_ticket, y) :-
         (gate(5)(C, U, e, ticket, next_waiting_ticket, next_available_ticket, y),
          next_waiting_ticket === next_available_ticket),                                             NoSync),

      (gate(0)(C, U, e, ticket, next_waiting_ticket, next_available_ticket, y) :-
         gate(3)(C, U, e, ticket, next_waiting_ticket, next_available_ticket, y),                     Send(go)),

      (gate(0)(C, U, e, ticket, next_waiting_ticket, next_available_ticket+1, y) :-
         gate(2)(C, U, e, ticket, next_waiting_ticket, next_available_ticket, y),                     Receive(appr)),

      (gate(5)(C, U, e, ticket, next_waiting_ticket+1, next_available_ticket, y) :-
         gate(0)(C, U, e, ticket, next_waiting_ticket, next_available_ticket, y),                     Receive(leave)),

      (gate(4)(C, U, e, next_available_ticket, next_waiting_ticket, next_available_ticket+1, C) :-
         gate(0)(C, U, e, ticket, next_waiting_ticket, next_available_ticket, y),                     Receive(appr)),

      (gate(0)(C, U, e, ticket, next_waiting_ticket, next_available_ticket, y) :-
         gate(4)(C, U, e, ticket, next_waiting_ticket, next_available_ticket, y),                     Send(stop))

    )

    val trainProcess = List(

      (train(4)(C, U, e, ticket, id, my_ticket, C) :- true,                                           NoSync),

      (train(1)(C, U, id, ticket, id, my_ticket, C) :-
         train(4)(C, U, e, ticket, id, my_ticket, x),                                                 Send(appr)),

      (train(2)(C, U, e, ticket, id, ticket, C) :-
         (train(1)(C, U, e, ticket, id, my_ticket, x),
          C - x <= U*10, e === id),                                                                   Receive(stop)),

      (train(3)(C, U, e, ticket, id, my_ticket, C) :-
         (train(2)(C, U, e, ticket, id, my_ticket, x),
          my_ticket === ticket),                                                                      Receive(go)),

      (train(0)(C, U, e, ticket, id, my_ticket, C) :-
         (train(3)(C, U, e, ticket, id, my_ticket, x),
          C - x >= U*7),                                                                              NoSync),

      (train(0)(C, U, e, ticket, id, my_ticket, C) :-
         (train(1)(C, U, e, ticket, id, my_ticket, x),
          C - x >= U*10),                                                                             NoSync),

      (train(4)(C, U, id, ticket, id, my_ticket, C) :-
         (train(0)(C, U, e, ticket, id, my_ticket, x),
          C - x >= U*3),                                                                              Send(leave))

    )

    val timeInvs = List(
      (C - y <= U*5) :- gate(4)(C, U, e, ticket, next_waiting_ticket, next_available_ticket, y),
      (C - x <= U*20) :- train(1)(C, U, e, ticket, id, my_ticket, x),
      (C - x <= U*15) :- train(3)(C, U, e, ticket, id, my_ticket, x),
      (C - x <= U*5) :- train(0)(C, U, e, ticket, id, my_ticket, x)
    )

    val assertions =
      List(false :- (train(0)(C, U, e, ticket, id, my_ticket, x),
                     train(0)(C, U, e, ticket, id2, my_ticket2, x2)))

    val system =
      System(
        List((gateProcess, Singleton), (trainProcess, Infinite)),
        4, None,
        ContinuousTime(0, 1),
        timeInvs,
        assertions)

    val vl = runLoop(system)

/*  val enc =
    new ParametricEncoder(system, assertions, List(List(1, 2)))

 solve(enc) */
    assert(isSolvable(vl))
  }

  //////////////////////////////////////////////////////////////////////////////

  "Simplified train crossing example for FM submission" should "be SOLVABLE" in {
    ap.util.Debug enableAllAssertions true

    val train = for (i <- 0 to 4) yield (new Predicate("train" + i, 1 + 2))
    val gate  = for (i <- 0 to 5) yield (new Predicate("gate" + i, 1 + 2))

    val c = new ConstantTerm("c")
    val n = new ConstantTerm("n")
    val x = new ConstantTerm("x")
    val x1 = new ConstantTerm("x1")
    val x2 = new ConstantTerm("x2")
    val y = new ConstantTerm("y")
    val id  = new ConstantTerm("id")
    val id1 = new ConstantTerm("id1")
    val id2 = new ConstantTerm("id2")

    val go = new CommChannel("go")
    val appr = new CommChannel("appr")
    val leave = new CommChannel("leave")
    val stop = new CommChannel("stop")

    val gateProcess = List(

      (gate(0)(c, n, c) :-
         (true),                                                                                     NoSync),

      (gate(1)(c, 0, y) :-
         gate(0)(c, n, y),                                                                           NoSync),

      /*    (gate(2)(c, n, y) :-
       (gate(1)(c, n, y),
       !(n === 0)),                                                                                NoSync),

       (gate(3)(c, n, y) :-
       (gate(1)(c, n, y),
       (n === 0)),                                                                                 NoSync),
       */
      (gate(4)(c, n, y) :-
         (gate(1)(c, n, y), n =/= 0),                                                                         Send(go)),

      (gate(4)(c, n + 1, y) :-
         (gate(1)(c, n, y), n === 0),                                                                         Receive(appr)),

      (gate(1)(c, n - 1, y) :-
         (gate(4)(c, n, y)),                                                                         Receive(leave)),

      (gate(5)(c, n + 1, c) :-
         (gate(4)(c, n, y)),                                                                         Receive(appr)),

      (gate(4)(c, n, c) :-
         (gate(5)(c, n, y)),                                                                         Send(stop))

    )

    val trainProcess = List(

      (train(0)(c, id, c) :-
         true,                                                                                       NoSync),

      (train(2)(c, id, c) :-
         (train(0)(c, id, x)),                                                                       Send(appr)),

      (train(1)(c, id, c) :-
         (train(2)(c, id, x),
          c - x >= 10),                                                                              NoSync),

      (train(0)(c, id, c) :-
         (train(1)(c, id, x),
          c - x >= 3),                                                                               Send(leave)),

      (train(3)(c, id, c) :-
         (train(2)(c, id, x),
          c - x <= 10),                                                                              Receive(stop)),

      (train(4)(c, id, c) :-
         (train(3)(c, id, x)),                                                                       Receive(go)),

      (train(1)(c, id, c) :-
         (train(4)(c, id, x),
          c - x >= 7),                                                                                NoSync)

    )

    val timeInvs = List(
      (c - y <= 5)    :- gate(5)(c, n, y),
      (c - x <= 5)    :- train(1)(c, id, x),
      (c - x <= 20)   :- train(2)(c, id, x),
      (c - x <= 15)   :- train(4)(c, id, x)
    )

    val assertions =
      List(false :- (train(1)(c, id1, x1),
                     train(1)(c, id2, x2)))

    val system =
      System(
        List((gateProcess, Singleton), (trainProcess, Infinite)),
        1,
        None,
        DiscreteTime(0),
        timeInvs,
        assertions)

    // can we get deadlocks?
    //    List(false :- (train(1)(c, id1, x1),
    //                   gate(1)(c, n, y)))

    val vl = runLoop(system)
    assert(isSolvable(vl))
  }

  //////////////////////////////////////////////////////////////////////////////

  "Train crossing example with RationalTime" should "be SOLVABLE" in {
    val sorts = List(Rationals.dom, Sort.Integer, Sort.Integer,
                     Sort.Integer, Sort.Integer, Sort.Integer)
    val train = for (i <- 0 to 4) yield MonoSortedPredicate("train" + i, sorts)
    val gate  = for (i <- 0 to 5) yield MonoSortedPredicate("gate" + i, sorts)

    val C = Rationals.dom.newConstant("C")
    val e = new ConstantTerm("e")
    val ticket = new ConstantTerm("ticket")
    val my_ticket = new ConstantTerm("my_ticket")
    val my_ticket2 = new ConstantTerm("my_ticket2")
    val next_waiting_ticket = new ConstantTerm("next_waiting_ticket")
    val next_available_ticket = new ConstantTerm("next_available_ticket")
    val x = Rationals.dom.newConstant("x")
    val x2 = Rationals.dom.newConstant("x2")
    val y = Rationals.dom.newConstant("y")
    val id = new ConstantTerm("id")
    val id2 = new ConstantTerm("id2")

    val go = new CommChannel("go")
    val appr = new CommChannel("appr")
    val leave = new CommChannel("leave")
    val stop = new CommChannel("stop")

    import Rationals.{geq, leq, minus, int2ring => toRat}

    val gateProcess = List(

      (gate(1)(C, e, ticket, next_waiting_ticket, next_available_ticket, C) :- true,               NoSync),

      (gate(5)(C, e, ticket, next_available_ticket, next_available_ticket, y) :-
         gate(1)(C, e, ticket, next_waiting_ticket, next_available_ticket, y),                     NoSync),

      (gate(3)(C, e, next_waiting_ticket, next_waiting_ticket+1, next_available_ticket, y) :-
         (gate(5)(C, e, ticket, next_waiting_ticket, next_available_ticket, y),
          next_waiting_ticket < next_available_ticket),                                               NoSync),

      (gate(2)(C, e, ticket, next_waiting_ticket, next_available_ticket, y) :-
         (gate(5)(C, e, ticket, next_waiting_ticket, next_available_ticket, y),
          next_waiting_ticket === next_available_ticket),                                             NoSync),

      (gate(0)(C, e, ticket, next_waiting_ticket, next_available_ticket, y) :-
         gate(3)(C, e, ticket, next_waiting_ticket, next_available_ticket, y),                     Send(go)),

      (gate(0)(C, e, ticket, next_waiting_ticket, next_available_ticket+1, y) :-
         gate(2)(C, e, ticket, next_waiting_ticket, next_available_ticket, y),                     Receive(appr)),

      (gate(5)(C, e, ticket, next_waiting_ticket+1, next_available_ticket, y) :-
         gate(0)(C, e, ticket, next_waiting_ticket, next_available_ticket, y),                     Receive(leave)),

      (gate(4)(C, e, next_available_ticket, next_waiting_ticket, next_available_ticket+1, C) :-
         gate(0)(C, e, ticket, next_waiting_ticket, next_available_ticket, y),                     Receive(appr)),

      (gate(0)(C, e, ticket, next_waiting_ticket, next_available_ticket, y) :-
         gate(4)(C, e, ticket, next_waiting_ticket, next_available_ticket, y),                     Send(stop))

    )

    val trainProcess = List(

      (train(4)(C, e, ticket, id, my_ticket, C) :- true,                                           NoSync),

      (train(1)(C, id, ticket, id, my_ticket, C) :-
         train(4)(C, e, ticket, id, my_ticket, x),                                                 Send(appr)),

      (train(2)(C, e, ticket, id, ticket, C) :-
         (train(1)(C, e, ticket, id, my_ticket, x),
          leq(minus(C, x), toRat(10)), e === id),                                                  Receive(stop)),

      (train(3)(C, e, ticket, id, my_ticket, C) :-
         (train(2)(C, e, ticket, id, my_ticket, x),
          my_ticket === ticket),                                                                      Receive(go)),

      (train(0)(C, e, ticket, id, my_ticket, C) :-
         (train(3)(C, e, ticket, id, my_ticket, x),
          geq(minus(C, x), toRat(7))),                                                                NoSync),

      (train(0)(C, e, ticket, id, my_ticket, C) :-
         (train(1)(C, e, ticket, id, my_ticket, x),
          geq(minus(C, x), toRat(10))),                                                               NoSync),

      (train(4)(C, id, ticket, id, my_ticket, C) :-
         (train(0)(C, e, ticket, id, my_ticket, x),
          geq(minus(C, x), toRat(3))),                                                                Send(leave))

    )

    val timeInvs = List(
      leq(minus(C, y), toRat(5))  :- gate(4)(C, e, ticket, next_waiting_ticket, next_available_ticket, y),
      leq(minus(C, x), toRat(20)) :- train(1)(C, e, ticket, id, my_ticket, x),
      leq(minus(C, x), toRat(15)) :- train(3)(C, e, ticket, id, my_ticket, x),
      leq(minus(C, x), toRat(5))  :- train(0)(C, e, ticket, id, my_ticket, x)
    )

    val assertions =
      List(false :- (train(0)(C, e, ticket, id, my_ticket, x),
                     train(0)(C, e, ticket, id2, my_ticket2, x2)))

    val system =
      System(
        List((gateProcess, Singleton), (trainProcess, Infinite)),
        3, None,
        RationalTime(0),
        timeInvs,
        assertions)

    val vl = runLoop(system)

/*  val enc =
    new ParametricEncoder(system, assertions, List(List(1, 2)))

 solve(enc) */
    assert(isSolvable(vl))
  }
}