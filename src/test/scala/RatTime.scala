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

class RatTime extends FlatSpec {
  import HornClauses._
  import IExpression._
  import System._
  import VerificationUtils._
  import Rationals.{geq, leq, gt, minus, int2ring => toRat}

  ap.util.Debug enableAllAssertions true

  "System with rational time" should "be NOT SOLVABLE" in {
    val sorts = List(Rationals.dom, Rationals.dom)
    val p = for (i <- 0 to 1) yield MonoSortedPredicate("p" + i, sorts)

    val C = Rationals.dom.newConstant("C")
    val x = Rationals.dom.newConstant("x")

    val pProc = List(
      (p(0)(C, C) :- true,
       NoSync),
      (p(1)(C, x) :- (p(0)(C, x), gt(minus(C, x), toRat(5))),
       NoSync)
    )

    val assertions = List(
      false :- p(1)(C, x)
    )

    val system =
      TimedSystem(
        List((pProc, Singleton)),
        1,
        assertions,
        RationalTime(0),
        List())

    val vl = runLoop(system)

    assert(!isSolvable(vl))
  }
}