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
import ap.basetypes.HeapCollector

class MITLTests extends FlatSpec {
  import MITL._

  private val noRank: Option[Int] = None

  private def nfConjunction(left: MITL, right: MITL): MITL =
    Negation(Disjunction(Negation(left), Negation(right)))

  private def diamondOpenClosed0(right: Int, inner: MITL): MITL = {
    val open = Diamond(OpenOpen(0, right), inner, noRank)
    Disjunction(
      open,
      nfConjunction(
        U(OpenOpen(0, PosInfty), open, open, noRank),
        U(OpenOpen(0, PosInfty), Negation(inner), inner, noRank)))
  }

  private def diamondClosedOpen0(right: Int, inner: MITL): MITL =
    Disjunction(inner, Diamond(OpenOpen(0, right), inner, noRank))

  private def diamondClosedClosed0(right: Int, inner: MITL): MITL =
    Disjunction(inner, diamondOpenClosed0(right, inner))

  private def pDiamondOpenClosed0(right: Int, inner: MITL): MITL = {
    val open = PDiamond(OpenOpen(0, right), inner, noRank)
    Disjunction(
      open,
      nfConjunction(
        S(OpenOpen(0, PosInfty), open, open, noRank),
        S(OpenOpen(0, PosInfty), Negation(inner), inner, noRank)))
  }

  private def pDiamondClosedOpen0(right: Int, inner: MITL): MITL =
    Disjunction(inner, PDiamond(OpenOpen(0, right), inner, noRank))

  private def pDiamondClosedClosed0(right: Int, inner: MITL): MITL =
    Disjunction(inner, pDiamondOpenClosed0(right, inner))

  private def boxOpenOpen0(right: Int, inner: MITL): MITL =
    Negation(Diamond(OpenOpen(0, right), Negation(inner), noRank))

  private def boxOpenClosed0(right: Int, inner: MITL): MITL =
    Negation(diamondOpenClosed0(right, Negation(inner)))

  private def pBoxOpenOpen0(right: Int, inner: MITL): MITL =
    Negation(PDiamond(OpenOpen(0, right), Negation(inner), noRank))

  private def pBoxOpenClosed0(right: Int, inner: MITL): MITL =
    Negation(pDiamondOpenClosed0(right, Negation(inner)))

  private def nonStrictUntil(left: MITL, right: MITL): MITL =
    Disjunction(right, nfConjunction(left, U(OpenOpen(0, PosInfty), left, right, noRank)))

  private def nonStrictSince(left: MITL, right: MITL): MITL =
    Disjunction(right, nfConjunction(left, S(OpenOpen(0, PosInfty), left, right, noRank)))

  it should "translate conjunction correctly" in {
    val ap1 = AP("a")
    val ap2 = AP("b")

    val conj = Conjunction(ap1, ap2)
    val d = nf(conj)

    assert(d == Negation(Disjunction(Negation(AP("a")), Negation(AP("b")))))
  }

  it should "translate implication correctly" in {
    val ap1 = AP("a")
    val ap2 = AP("b")

    val conj = Implication(ap1, ap2)
    val d = nf(conj)

    assert(d == Disjunction(Negation(AP("a")), AP("b")))
  }
  
  it should "translate conjunction and implication correctly" in {
    val ap1 = AP("a")
    val ap2 = AP("b")

    val conj = Conjunction(ap1, Implication(ap1, ap2))
    val d = nf(conj)

    assert(d == Negation(Disjunction(Negation(ap1), Negation(Disjunction(Negation(ap1), ap2)))))
  }

  it should "translate diamond_[0,1) with normalized AP correctly" in {
    val ap = AP("a")

    val d = Diamond(ClosedOpen(0, 1), ap, None)
    val translated = nf(d)

    assert(translated == Disjunction(AP("a"), Diamond(OpenOpen(0, 1), ap, None)))
  }

  it should "translate diamond_(2,5) correctly" in {
    val ap = AP("a")

    val d = Diamond(OpenOpen(2, 5), ap, None)
    val translated = nf(d)

    assert(translated == Diamond(OpenOpen(0, 2), Negation(Diamond(OpenOpen(0, 2), Negation(Diamond(OpenOpen(0, 3), ap, None)), None)), None))
  }

  it should "translate diamond_(0,1] correctly" in {
    val ap = AP("a")

    val d = Diamond(OpenClosed(0, 1), ap, noRank)
    val translated = nf(d)

    assert(translated == diamondOpenClosed0(1, ap))
  }

  it should "translate diamond_(2,5] correctly" in {
    val ap = AP("a")

    val d = Diamond(OpenClosed(2, 5), ap, noRank)
    val translated = nf(d)

    val psi = diamondOpenClosed0(3, ap)
    val boxInner = Negation(diamondClosedOpen0(2, Negation(psi)))

    assert(translated == diamondOpenClosed0(2, boxInner))
  }

  it should "translate negated diamond with nested open diamond correctly" in {
    val ap = AP("a")

    val d = Negation(Diamond(ClosedOpen(0, 2), Negation(Diamond(OpenOpen(0, 3), ap, None)), None))
    val translated = nf(d)

    assert(translated ==
      Negation(
        Disjunction(
          Negation(Diamond(OpenOpen(0, 3), AP("a"), None)),
          Diamond(OpenOpen(0, 2), Negation(Diamond(OpenOpen(0, 3), AP("a"), None)), None)
        )
      ))
  }

  it should "translate open-closed diamond with nested closed-open diamond correctly" in {
    val ap = AP("a")

    val d = Diamond(OpenClosed(0, 2), Negation(Diamond(ClosedOpen(0, 2), ap, noRank)), noRank)
    val translated = nf(d)

    val inner = Negation(Disjunction(AP("a"), Diamond(OpenOpen(0, 2), AP("a"), noRank)))

    assert(translated == diamondOpenClosed0(2, inner))
  }

  it should "translate diamond_[0,1) correctly" in {
    val ap = AP("a")

    val d = Diamond(ClosedOpen(0, 1), ap, None)
    val translated = nf(d)

    assert(translated == Disjunction(AP("a"), Diamond(OpenOpen(0, 1), AP("a"), None)))
  }

  it should "translate diamond_[2,5) correctly" in {
    val ap = AP("a")

    val d = Diamond(ClosedOpen(2, 5), ap, noRank)
    val translated = nf(d)

    val psi = diamondClosedOpen0(3, ap)
    val boxInner = Negation(diamondOpenClosed0(2, Negation(psi)))

    assert(translated == diamondClosedOpen0(2, boxInner))
  }

  it should "translate diamond_[0,1] correctly" in {
    val ap = AP("a")

    val d = Diamond(ClosedClosed(0, 1), ap, noRank)
    val translated = nf(d)

    assert(translated == diamondClosedClosed0(1, ap))
  }

  it should "translate diamond_[2,5] correctly" in {
    val ap = AP("a")

    val d = Diamond(ClosedClosed(2, 5), ap, noRank)
    val translated = nf(d)

    val psi = diamondClosedClosed0(3, ap)
    val boxInner = Negation(diamondClosedClosed0(2, Negation(psi)))

    assert(translated == diamondClosedClosed0(2, boxInner))
  }

  it should "translate past diamond_(0,1] correctly" in {
    val ap = AP("a")

    val d = PDiamond(OpenClosed(0, 1), ap, noRank)
    val translated = nf(d)

    assert(translated == pDiamondOpenClosed0(1, ap))
  }

  it should "translate past diamond_(2,5) correctly" in {
    val ap = AP("a")

    val d = PDiamond(OpenOpen(2, 5), ap, noRank)
    val translated = nf(d)

    assert(translated == PDiamond(OpenOpen(0, 2), Negation(PDiamond(OpenOpen(0, 2), Negation(PDiamond(OpenOpen(0, 3), ap, noRank)), noRank)), noRank))
  }

  it should "translate past diamond_(2,5] correctly" in {
    val ap = AP("a")

    val d = PDiamond(OpenClosed(2, 5), ap, noRank)
    val translated = nf(d)

    val psi = pDiamondOpenClosed0(3, ap)
    val boxInner = Negation(pDiamondClosedOpen0(2, Negation(psi)))

    assert(translated == pDiamondOpenClosed0(2, boxInner))
  }

  it should "translate past diamond_[2,5) correctly" in {
    val ap = AP("a")

    val d = PDiamond(ClosedOpen(2, 5), ap, noRank)
    val translated = nf(d)

    val psi = pDiamondClosedOpen0(3, ap)
    val boxInner = Negation(pDiamondOpenClosed0(2, Negation(psi)))

    assert(translated == pDiamondClosedOpen0(2, boxInner))
  }

  it should "translate past diamond_[2,5] correctly" in {
    val ap = AP("a")

    val d = PDiamond(ClosedClosed(2, 5), ap, noRank)
    val translated = nf(d)
    val psi = pDiamondClosedClosed0(3, ap)
    val boxInner = Negation(pDiamondClosedClosed0(2, Negation(psi)))

    assert(translated == pDiamondClosedClosed0(2, boxInner))
  }

  it should "translate until_(0,1] correctly" in {
    val left = AP("a")
    val right = AP("b")

    val d = U(OpenClosed(0, 1), left, right, noRank)
    val translated = nf(d)

    assert(translated ==
      nfConjunction(
        U(OpenOpen(0, PosInfty), AP("a"), AP("b"), noRank),
        diamondOpenClosed0(1, AP("b"))))
  }

  it should "translate until_(2,5) correctly" in {
    val left = AP("a")
    val right = AP("b")

    val d = U(OpenOpen(2, 5), left, right, noRank)
    val translated = nf(d)
    val unbounded = boxOpenClosed0(2, nfConjunction(left, U(OpenOpen(0, PosInfty), left, right, noRank)))
    val eventual = Diamond(OpenOpen(0, 2), boxOpenOpen0(2, Diamond(OpenOpen(0, 3), right, noRank)), noRank)

    assert(translated == nfConjunction(unbounded, eventual))
  }

  it should "translate until_[2,infty) correctly" in {
    val left = AP("a")
    val right = AP("b")

    val d = U(ClosedOpen(2, PosInfty), left, right, noRank)
    val translated = nf(d)

    assert(translated ==
      nfConjunction(
        boxOpenOpen0(2, left),
        boxOpenClosed0(2, nonStrictUntil(left, right))))
  }

  it should "translate since_(0,1] correctly" in {
    val left = AP("a")
    val right = AP("b")

    val d = S(OpenClosed(0, 1), left, right, noRank)
    val translated = nf(d)

    assert(translated ==
      nfConjunction(
        S(OpenOpen(0, PosInfty), AP("a"), AP("b"), noRank),
        pDiamondOpenClosed0(1, AP("b"))))
  }

  it should "translate since_(2,5) correctly" in {
    val left = AP("a")
    val right = AP("b")

    val d = S(OpenOpen(2, 5), left, right, noRank)
    val translated = nf(d)
    val unbounded = pBoxOpenClosed0(2, nfConjunction(left, S(OpenOpen(0, PosInfty), left, right, noRank)))
    val eventual = PDiamond(OpenOpen(0, 2), pBoxOpenOpen0(2, PDiamond(OpenOpen(0, 3), right, noRank)), noRank)

    assert(translated == nfConjunction(unbounded, eventual))
  }

  it should "translate since_[2,infty) correctly" in {
    val left = AP("a")
    val right = AP("b")

    val d = S(ClosedOpen(2, PosInfty), left, right, noRank)
    val translated = nf(d)

    assert(translated ==
      nfConjunction(
        pBoxOpenOpen0(2, left),
        pBoxOpenClosed0(2, nonStrictSince(left, right))))
  }

    it should "translate past diamond correctly" in {
    val ap = AP("a")

    val d = PDiamond(ClosedOpen(0, 1), ap, None)
    val translated = nf(d)

    assert(translated == Disjunction(AP("a"), PDiamond(OpenOpen(0, 1), AP("a"), None)))
  }

    it should "translate box correctly" in {
    val ap = AP("a")

    val d = Box(ClosedOpen(0, 1), ap, None)
    val translated = nf(d)

    assert(translated == Negation(Disjunction(Negation(AP("a")), Diamond(OpenOpen(0, 1), Negation(AP("a")), None))))
  }

    it should "translate past box correctly" in {
    val ap = AP("a")

    val d = PBox(ClosedOpen(0, 1), ap, None)
    val translated = nf(d)

    assert(translated == Negation(Disjunction(Negation(AP("a")), PDiamond(OpenOpen(0, 1), Negation(AP("a")), None))))
  }

  it should "translate complex formulae correctly" in {
    val a = AP("a")
    val b = AP("b")

    val f = Implication(PBox(ClosedClosed(0, 100), a, noRank), b)
    val translated = nf(f)


    assert(translated == Disjunction(Negation(Negation(pDiamondClosedClosed0(100, Negation(AP("a"))))), AP("b")))
  }
}
