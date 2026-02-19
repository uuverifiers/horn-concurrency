/**
 * Copyright (c) 2026 Philipp Ruemmer. All rights reserved.
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
import lazabs.horn.Util
import lazabs.horn.bottomup.{HornClauses, HornPredAbs}

class InvRefinement extends FlatSpec {
  import HornClauses._
  import IExpression._
  import ParametricEncoder._
  import VerificationUtils._

  ap.util.Debug enableAllAssertions true

  val p = for (i <- 0 until 3) yield (new Predicate("p" + i, 2))
  val q = for (i <- 0 until 3) yield (new Predicate("q" + i, 2))
  val r = for (i <- 0 until 3) yield (new Predicate("r" + i, 2))

  val x = new ConstantTerm("x")
  val y = new ConstantTerm("y")

  val pProc = List(
    (p(0)(0, 0) :- true,
      NoSync),
    (p(0)(x + 1, y) :- p(0)(x, y),
      NoSync)
  )

  val qProc = List(
    (q(0)(0, 0) :- true,
      NoSync),
    (q(0)(x, y + 1) :- q(0)(x, y),
      NoSync)
  )

  val rProc = List(
    (r(0)(x, y) :- true,
      NoSync),
    (r(1)(x + 1, y + 1) :- r(0)(x, y),
      NoSync),
    (r(0)(x - 1, y - 1) :- r(1)(x, y),
      NoSync)
  )

  "System 1 with overlapping invariants" should "be solvable" in {
    val assertions = List(
      (x >= 0) :- p(0)(x, y),
      (y >= 0) :- p(0)(x, y)
    )

    val system =
      System(
        List((pProc, Singleton), (qProc, Singleton), (rProc, Singleton)),
        2,
        None,
        NoTime,
        List(),
        assertions)

    val vl =
      runLoop(system,
              initialInvariants = List(List(1, 0, 1), List(0, 1, 1)))
    assert(isSolvable(vl))
  }

  "System 2 with overlapping invariants" should "be not solvable" in {
    val assertions = List(
      (x >= y) :- p(0)(x, y)
    )

    val system =
      System(
        List((pProc, Singleton), (qProc, Singleton), (rProc, Singleton)),
        2,
        None,
        NoTime,
        List(),
        assertions)

    val vl =
      runLoop(system,
              initialInvariants = List(List(1, 0, 1), List(0, 1, 1)))
    assert(!isSolvable(vl))
  }
}