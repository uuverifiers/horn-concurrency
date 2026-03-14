/**
 * Copyright (c) 2026 Philipp Ruemmer, Zafer Esen. All rights reserved.
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
import ap.theories.ADT
import ap.types.MonoSortedPredicate
import lazabs.horn.Util
import lazabs.horn.bottomup.{HornClauses, HornPredAbs}

class SignalTests extends FlatSpec {
  import HornClauses._
  import IExpression._
  import System._
  import SignalSystem._
  import VerificationUtils._
  import Rationals.{geq, leq, gt, minus, int2ring => toRat}
  import ADT.BoolADT.{True, False}

  ap.util.Debug enableAllAssertions true

  val pSorts =
    List(Rationals.dom, Sort.Bool, Sort.Integer, Sort.Integer, Rationals.dom)
  val p = for (i <- 0 to 5) yield MonoSortedPredicate("p" + i, pSorts)

  val C = Rationals.dom.newConstant("C")
  val c = Rationals.dom.newConstant("c")
  val c_mon = Rationals.dom.newConstant("c_mon")
  val x = Sort.Integer.newConstant("x")
  val x1 = Sort.Integer.newConstant("x1")
  val y = Sort.Integer.newConstant("y")
  val s = Sort.Bool.newConstant("s")

/*
        c := 0,
        assume(p === (y >= 0)),
        loopWhile(true) (
          havoc(x),
          progress (c >= 0 && c <= 9 && (s === (y >= 0))) (
            y := x,
            ifthen(y < 0) (
              y := -y
            )
          ),
          assume(s === (y >= 0)),
          c := 0
        )
*/

  val pProc = List(
    (p(0)(C, s, x, y, c) :- true,
      NoSync),

    // entering loop, assume (s === (y >= 0)), reset(c)
    (p(1)(C, s, x, y, C) :- (p(0)(C, s, x, y, c), (s === True) <=> (y >= 0)),
      NoSync),
    // havoc(x)
    (p(2)(C, s, x1, y, c) :- p(1)(C, s, x, y, c),
      NoSync),

    // progress (c >= 0 && c <= 9 && (p === (y >= 0))
    (p(3)(C, s, x, y, c) :- p(2)(C, s, x, y, c),
      NoSync),
    // y := x
    (p(4)(C, s, x, x, c) :- p(3)(C, s, x, y, c),
      NoSync),
    // if y < 0 then y := -y
    (p(5)(C, s, x, -y, c) :- (p(4)(C, s, x, y, c), y < 0),
      NoSync),
    (p(5)(C, s, x, y, c) :- (p(4)(C, s, x, y, c), y >= 0),
      NoSync),
    // end of progress

    // assume (s === (y >= 0)), reset(c), return to loop head
    (p(1)(C, s, x, y, C) :- (p(5)(C, s, x, y, c), (s === True) <=> (y >= 0)),
      NoSync)
  )

  // progress invariants
  val pProgressBlock = ProgressBlock(
    for (n <- 3 to 5) yield
      ((geq(minus(C, c), toRat(0)) & leq(minus(C, c), toRat(9)) &
        ((s === True) <=> (y >= 0))) :- p(n)(C, s, x, y, c))
  )

/* 
        progress(true)(),
        c_mon := 0,
        progress(!s)(),
        assume(c_mon > 9) // or c_mon >= 9
        assert(false)
 */

  val monSorts = List(Rationals.dom, Sort.Bool, Rationals.dom)
  val mon = for (i <- 0 to 2) yield MonoSortedPredicate("monitor" + i, monSorts)

  def constructMonitor(delay : ITerm => IFormula) = {
    val monProc = List(
      // progress(true)
      (mon(0)(C, s, c_mon) :- true,
       NoSync),
      // end of progress

      // c_mon := 0, progress(!s)
      (mon(1)(C, s, C) :- mon(0)(C, s, c_mon),
       NoSync),
      // end of progress

      // assume(c_mon > 9)
      (mon(2)(C, s, C) :- (mon(1)(C, s, c_mon), delay(minus(C, c_mon))),
       NoSync)
      // assert(false)
    )

    // progress invariants
    val monProgressBlocks = List(
      // cannot use the :- notation here, because the first clause will be simplified
      // to true
      ProgressBlock(List(Clause(HornClauses.FALSE(), List(mon(0)(C, s, c_mon)), true))),
      ProgressBlock(List((s === False) :- mon(1)(C, s, c_mon)))
    )

    val assertions = List(
      false :- mon(2)(C, s, c_mon)
    )

    (monProc, monProgressBlocks, assertions)
  }

  "Correct system with signals" should "be SOLVABLE" in {
    val (monProc, monProgressBlocks, assertions) =
      constructMonitor(c_mon => gt(c_mon, toRat(9)))

    val system = SignalSystem(
      List((pProc, Singleton), (monProc, Singleton)),
      2,
      assertions,
      RationalTime(0),
      Set(1),
      List(List(pProgressBlock), monProgressBlocks)
    )

    val encoder = new SignalEncoder(system)

//    for ((p, _) <- encoder.result.processes; c <- p)
//    println(c)

    val vl = runLoop(encoder.result)
    assert(isSolvable(vl))
  }

  "Incorrect system with signals" should "NOT be SOLVABLE" in {
    val (monProc, monProgressBlocks, assertions) =
      constructMonitor(c_mon => geq(c_mon, toRat(9)))

    val system = SignalSystem(
      List((pProc, Singleton), (monProc, Singleton)),   // Processes
      2,                                                // Number of global variables
      assertions,                                       // Assertions
      RationalTime(0),                                  // Index of variable representing time
      Set(1),                                           // Indexes of signal variables
      List(List(pProgressBlock), monProgressBlocks)     // Progress invariants
    )

    val encoder = new SignalEncoder(system)

//    for ((p, _) <- encoder.result.processes; c <- p)
//    println(c)

    val vl = runLoop(encoder.result)
    assert(!isSolvable(vl))
  }

}