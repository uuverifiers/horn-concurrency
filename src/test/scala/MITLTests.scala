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

import org.scalatest._

class MITLTests extends FlatSpec {
  import MITL._

  it should "translate conjunction correctly" in {
    val ap1 = AP("a")
    val ap2 = AP("b")

    val conj = Conjunction(ap1, ap2)
    val d = translateNF(conj)

    assert(d == Negation(Disjunction(Negation(AP("a")), Negation(AP("b")))))
  }

  it should "translate diamond correctly" in {
    val ap = AP("a")

    val d = Lozenge(LCRO(0, 1), ap)
    val translated = translateNF(d)

    assert(translated == U(LCRO(0, 1), True, AP("a")))
  }

    it should "translate past diamond correctly" in {
    val ap = AP("a")

    val d = PLozenge(LCRO(0, 1), ap)
    val translated = translateNF(d)

    assert(translated == S(LCRO(0, 1), True, AP("a")))
  }

    it should "translate box correctly" in {
    val ap = AP("a")

    val d = Box(LCRO(0, 1), ap)
    val translated = translateNF(d)

    assert(translated == Negation(U(LCRO(0, 1), True, Negation(AP("a")))))
  }

    it should "translate past box correctly" in {
    val ap = AP("a")

    val d = PBox(LCRO(0, 1), ap)
    val translated = translateNF(d)

    assert(translated == Negation(S(LCRO(0, 1), True, Negation(AP("a")))))
  }

}
