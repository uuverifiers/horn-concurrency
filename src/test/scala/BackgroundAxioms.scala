/**
 * Copyright (c) 2022-2026 Philipp Ruemmer. All rights reserved.
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
import lazabs.horn.bottomup.{HornClauses, HornPredAbs}

class BackgroundAxiomsTests extends FlatSpec {
  import HornClauses._
  import IExpression._
  import ParametricEncoder._
  import VerificationUtils._

  ap.util.Debug enableAllAssertions true

  "Background Axioms test 1" should "be SOLVABLE" in {

    val p = new Predicate("p", 1)
    val q = new Predicate("q", 1)
    val x = new ConstantTerm("x")

    val axioms = List(
      p(0)   :- true,
      p(x+1) :- p(x),
      false  :- (p(x), x < -10)
    )

    val qProc = List(
      (q(0)   :- true, NoSync),
      (q(x+1) :- q(x), NoSync)
    )

    val assertions =
      List((x >= -5) :- q(x))

    val system =
      System(List((qProc, Singleton)),
             0, None, NoTime, List(), assertions,
             backgroundAxioms = SomeBackgroundAxioms(List(p), axioms))

    val vl = runLoop(system)

    assert(isSolvable(vl))
  }
  
  "Background Axioms test 2" should "be NOT SOLVABLE" in {

    val p = new Predicate("p", 1)
    val q = new Predicate("q", 1)
    val x = new ConstantTerm("x")

    val axioms = List(
      p(0)   :- true,
      p(x+1) :- p(x),
      false  :- (p(x), x > 10)
    )

    val qProc = List(
      (q(0)   :- true, NoSync),
      (q(x+1) :- q(x), NoSync)
    )

    val assertions =
      List((x >= -5) :- q(x))

    val system =
      System(List((qProc, Singleton)),
             0, None, NoTime, List(), assertions,
             backgroundAxioms = SomeBackgroundAxioms(List(p), axioms))

    val vl = runLoop(system)

    assert(!isSolvable(vl))
  }
  
}
