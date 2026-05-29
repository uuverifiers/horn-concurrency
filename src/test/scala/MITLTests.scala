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

  it should "translate diamond_(0,1) correctly" in {
    val ap = AP("a")

    val d = Diamond(ClosedOpen(0, 1), ap)
    val translated = nf(d)

    assert(translated == Disjunction(AP("a"), Diamond(OpenOpen(0, 1), AP("a"))))
  }

  it should "translate diamond_(2,5) correctly" in {
    val ap = AP("a")

    val d = Diamond(OpenOpen(2, 5), ap)
    val translated = nf(d)

    assert(translated == Diamond(OpenOpen(0, 2), Negation(Diamond(OpenOpen(0, 2), Negation(Diamond(OpenOpen(0, 3), ap))))))
  }

  // it should "translate diamond_(0,1] correctly" in {
  //   val ap = AP("a")

  //   val d = Diamond(OpenClosed(0, 1), ap)
  //   val translated = nf(d)

  //   assert(translated == 
  //     Disjunction(
  //       Diamond(OpenOpen(0, 1), AP("a")),
  //       Conjunction(
  //         U(OpenOpen(0, PosInfty), Diamond(OpenOpen(0, 1), AP("a")), Diamond(OpenOpen(0, 1), AP("a"))),
  //         U(OpenOpen(0, PosInfty), Negation(AP("a")), AP("a"))
  //       )
  //     )
  //   )
  // }

  // it should "translate diamond_(2,5] correctly" in {
  //   val ap = AP("a")

  //   val d = Diamond(OpenClosed(2, 5), ap)
  //   val translated = nf(d)

  //   val psi = Disjunction(
  //     Diamond(OpenOpen(0, 3), AP("a")),
  //     Conjunction(
  //       U(OpenOpen(0, PosInfty),
  //         Diamond(OpenOpen(0, 3), AP("a")),
  //         Diamond(OpenOpen(0, 3), AP("a"))
  //       ),
  //       U(OpenOpen(0, PosInfty),
  //         Negation(AP("a")),
  //         AP("a")
  //       )
  //     )
  //   )

  //   val boxInner = Negation(
  //     Disjunction(
  //       Negation(psi),
  //       Diamond(OpenOpen(0, 2), Negation(psi))
  //     )
  //   )

  //   val phi = Diamond(OpenOpen(0, 2), boxInner)

  //   assert(translated ==
  //     Disjunction(
  //       phi,
  //       Conjunction(
  //         U(OpenOpen(0, PosInfty), phi, phi),
  //         U(OpenOpen(0, PosInfty), Negation(boxInner), boxInner)
  //       )
  //     ))
  // }

  it should "translate subexpr correctly" in {
    val ap = AP("a")

    val d = Negation(Diamond(ClosedOpen(0, 2), Negation(Diamond(OpenOpen(0, 3), ap))))
    val translated = nf(d)

    assert(translated ==
      Negation(
        Disjunction(
          Negation(Diamond(OpenOpen(0, 3), AP("a"))),
          Diamond(OpenOpen(0, 2), Negation(Diamond(OpenOpen(0, 3), AP("a"))))
        )
      ))
  }

  // it should "translate subexpr2 correctly" in {
  //   val ap = AP("a")

  //   val d = Diamond(OpenClosed(0, 2), Negation(Diamond(ClosedOpen(0, 2), ap)))
  //   val translated = nf(d)

  //   val inner = Negation(Disjunction(AP("a"), Diamond(OpenOpen(0, 2), AP("a"))))

  //   assert(translated ==
  //     Disjunction(
  //       Diamond(OpenOpen(0, 2), inner),
  //       Conjunction(
  //         U(OpenOpen(0, PosInfty),
  //           Diamond(OpenOpen(0, 2), inner),
  //           Diamond(OpenOpen(0, 2), inner)
  //         ),
  //         U(OpenOpen(0, PosInfty),
  //           Negation(inner),
  //           inner
  //         )
  //       )
  //     ))
  // }

  it should "translate diamond_[0,1) correctly" in {
    val ap = AP("a")

    val d = Diamond(ClosedOpen(0, 1), ap)
    val translated = nf(d)

    assert(translated == Disjunction(AP("a"), Diamond(OpenOpen(0, 1), AP("a"))))
  }

  // it should "translate diamond_[2,5) correctly" in {
  //   val ap = AP("a")

  //   val d = Diamond(ClosedOpen(2, 5), ap)
  //   val translated = nf(d)

  //   val psi = Disjunction(AP("a"), Diamond(OpenOpen(0, 3), AP("a")))
  //   val boxInner = Negation(
  //     Disjunction(
  //       Diamond(OpenOpen(0, 2), Negation(psi)),
  //       Conjunction(
  //         U(OpenOpen(0, PosInfty),
  //           Diamond(OpenOpen(0, 2), Negation(psi)),
  //           Diamond(OpenOpen(0, 2), Negation(psi))
  //         ),
  //         U(OpenOpen(0, PosInfty),
  //           Negation(Negation(psi)),
  //           Negation(psi)
  //         )
  //       )
  //     )
  //   )

  //   assert(translated == Disjunction(boxInner, Diamond(OpenOpen(0, 2), boxInner)))
  // }

  // it should "translate diamond_[0,1] correctly" in {
  //   val ap = AP("a")

  //   val d = Diamond(ClosedClosed(0, 1), ap)
  //   val translated = nf(d)

  //   assert(translated ==
  //     Disjunction(
  //       AP("a"),
  //       Disjunction(
  //         Diamond(OpenOpen(0, 1), AP("a")),
  //         Conjunction(
  //           U(OpenOpen(0, PosInfty),
  //             Diamond(OpenOpen(0, 1), AP("a")),
  //             Diamond(OpenOpen(0, 1), AP("a"))
  //           ),
  //           U(OpenOpen(0, PosInfty),
  //             Negation(AP("a")),
  //             AP("a")
  //           )
  //         )
  //       )
  //     ))
  // }

  // it should "translate diamond_[2,5] correctly" in {
  //   val ap = AP("a")

  //   val d = Diamond(ClosedClosed(2, 5), ap)
  //   val translated = nf(d)

  //   val psi = Disjunction(
  //     AP("a"),
  //     Disjunction(
  //       Diamond(OpenOpen(0, 3), AP("a")),
  //       Conjunction(
  //         U(OpenOpen(0, PosInfty),
  //           Diamond(OpenOpen(0, 3), AP("a")),
  //           Diamond(OpenOpen(0, 3), AP("a"))
  //         ),
  //         U(OpenOpen(0, PosInfty),
  //           Negation(AP("a")),
  //           AP("a")
  //         )
  //       )
  //     )
  //   )

  //   val left = Negation(psi)
  //   val right = Disjunction(
  //     Diamond(OpenOpen(0, 2), Negation(psi)),
  //     Conjunction(
  //       U(OpenOpen(0, PosInfty),
  //         Diamond(OpenOpen(0, 2), Negation(psi)),
  //         Diamond(OpenOpen(0, 2), Negation(psi))
  //       ),
  //       U(OpenOpen(0, PosInfty),
  //         Negation(Negation(psi)),
  //         Negation(psi)
  //       )
  //     )
  //   )

  //   val boxInner = Negation(Disjunction(left, right))

  //   assert(translated ==
  //     Disjunction(
  //       boxInner,
  //       Disjunction(
  //         Diamond(OpenOpen(0, 2), boxInner),
  //         Conjunction(
  //           U(OpenOpen(0, PosInfty),
  //             Diamond(OpenOpen(0, 2), boxInner),
  //             Diamond(OpenOpen(0, 2), boxInner)
  //           ),
  //           U(OpenOpen(0, PosInfty),
  //             Negation(boxInner),
  //             boxInner
  //           )
  //         )
  //       )
  //     ))
  // }

  // it should "translate past diamond_(0,1] correctly" in {
  //   val ap = AP("a")

  //   val d = PDiamond(OpenClosed(0, 1), ap)
  //   val translated = nf(d)

  //   assert(translated ==
  //     Disjunction(
  //       PDiamond(OpenOpen(0, 1), AP("a")),
  //       Conjunction(
  //         S(OpenOpen(0, PosInfty), PDiamond(OpenOpen(0, 1), AP("a")), PDiamond(OpenOpen(0, 1), AP("a"))),
  //         S(OpenOpen(0, PosInfty), Negation(AP("a")), AP("a"))
  //       )
  //     )
  //   )
  // }

  // it should "translate past diamond_(2,5) correctly" in {
  //   val ap = AP("a")

  //   val d = PDiamond(OpenOpen(2, 5), ap)
  //   val translated = nf(d)

  //   assert(translated == PDiamond(OpenOpen(0, 2), Negation(PDiamond(OpenOpen(0, 2), Negation(PDiamond(OpenOpen(0, 3), ap))))))
  // }

  // it should "translate past diamond_(2,5] correctly" in {
  //   val ap = AP("a")

  //   val d = PDiamond(OpenClosed(2, 5), ap)
  //   val translated = nf(d)

  //   val psi = Disjunction(
  //     PDiamond(OpenOpen(0, 3), AP("a")),
  //     Conjunction(
  //       S(OpenOpen(0, PosInfty),
  //         PDiamond(OpenOpen(0, 3), AP("a")),
  //         PDiamond(OpenOpen(0, 3), AP("a"))
  //       ),
  //       S(OpenOpen(0, PosInfty),
  //         Negation(AP("a")),
  //         AP("a")
  //       )
  //     )
  //   )

  //   val boxInner = Negation(
  //     Disjunction(
  //       Negation(psi),
  //       PDiamond(OpenOpen(0, 2), Negation(psi))
  //     )
  //   )

  //   val phi = PDiamond(OpenOpen(0, 2), boxInner)

  //   assert(translated ==
  //     Disjunction(
  //       phi,
  //       Conjunction(
  //         S(OpenOpen(0, PosInfty), phi, phi),
  //         S(OpenOpen(0, PosInfty), Negation(boxInner), boxInner)
  //       )
  //     ))
  // }

  // it should "translate past diamond_[2,5) correctly" in {
  //   val ap = AP("a")

  //   val d = PDiamond(ClosedOpen(2, 5), ap)
  //   val translated = nf(d)

  //   val psi = Disjunction(AP("a"), PDiamond(OpenOpen(0, 3), AP("a")))
  //   val boxInner = Negation(
  //     Disjunction(
  //       PDiamond(OpenOpen(0, 2), Negation(psi)),
  //       Conjunction(
  //         S(OpenOpen(0, PosInfty),
  //           PDiamond(OpenOpen(0, 2), Negation(psi)),
  //           PDiamond(OpenOpen(0, 2), Negation(psi))
  //         ),
  //         S(OpenOpen(0, PosInfty),
  //           Negation(Negation(psi)),
  //           Negation(psi)
  //         )
  //       )
  //     )
  //   )

  //   assert(translated == Disjunction(boxInner, PDiamond(OpenOpen(0, 2), boxInner)))
  // }

  // it should "translate past diamond_[2,5] correctly" in {
  //   val ap = AP("a")

  //   val d = PDiamond(ClosedClosed(2, 5), ap)
  //   val translated = nf(d)

  //   val psi = Disjunction(
  //     AP("a"),
  //     Disjunction(
  //       PDiamond(OpenOpen(0, 3), AP("a")),
  //       Conjunction(
  //         S(OpenOpen(0, PosInfty),
  //           PDiamond(OpenOpen(0, 3), AP("a")),
  //           PDiamond(OpenOpen(0, 3), AP("a"))
  //         ),
  //         S(OpenOpen(0, PosInfty),
  //           Negation(AP("a")),
  //           AP("a")
  //         )
  //       )
  //     )
  //   )

  //   val left = Negation(psi)
  //   val right = Disjunction(
  //     PDiamond(OpenOpen(0, 2), Negation(psi)),
  //     Conjunction(
  //       S(OpenOpen(0, PosInfty),
  //         PDiamond(OpenOpen(0, 2), Negation(psi)),
  //         PDiamond(OpenOpen(0, 2), Negation(psi))
  //       ),
  //       S(OpenOpen(0, PosInfty),
  //         Negation(Negation(psi)),
  //         Negation(psi)
  //       )
  //     )
  //   )

  //   val boxInner = Negation(Disjunction(left, right))

  //   assert(translated ==
  //     Disjunction(
  //       boxInner,
  //       Disjunction(
  //         PDiamond(OpenOpen(0, 2), boxInner),
  //         Conjunction(
  //           S(OpenOpen(0, PosInfty),
  //             PDiamond(OpenOpen(0, 2), boxInner),
  //             PDiamond(OpenOpen(0, 2), boxInner)
  //           ),
  //           S(OpenOpen(0, PosInfty),
  //             Negation(boxInner),
  //             boxInner
  //           )
  //         )
  //       )
  //     ))
  // }

  // it should "translate until_(0,1] correctly" in {
  //   val left = AP("a")
  //   val right = AP("b")

  //   val d = U(OpenClosed(0, 1), left, right)
  //   val translated = nf(d)

  //   assert(translated ==
  //     Conjunction(
  //       U(OpenOpen(0, PosInfty), AP("a"), AP("b")),
  //       Disjunction(
  //         Diamond(OpenOpen(0, 1), AP("b")),
  //         Conjunction(
  //           U(OpenOpen(0, PosInfty), Diamond(OpenOpen(0, 1), AP("b")), Diamond(OpenOpen(0, 1), AP("b"))),
  //           U(OpenOpen(0, PosInfty), Negation(AP("b")), AP("b"))
  //         )
  //       )
  //     )
  //   )
  // }

  // it should "translate since_(0,1] correctly" in {
  //   val left = AP("a")
  //   val right = AP("b")

  //   val d = S(OpenClosed(0, 1), left, right)
  //   val translated = nf(d)

  //   assert(translated ==
  //     Conjunction(
  //       S(OpenOpen(0, PosInfty), AP("a"), AP("b")),
  //       Disjunction(
  //         PDiamond(OpenOpen(0, 1), AP("b")),
  //         Conjunction(
  //           S(OpenOpen(0, PosInfty), PDiamond(OpenOpen(0, 1), AP("b")), PDiamond(OpenOpen(0, 1), AP("b"))),
  //           S(OpenOpen(0, PosInfty), Negation(AP("b")), AP("b"))
  //         )
  //       )
  //     )
  //   )
  // }

    it should "translate past diamond correctly" in {
    val ap = AP("a")

    val d = PDiamond(ClosedOpen(0, 1), ap)
    val translated = nf(d)

    assert(translated == Disjunction(AP("a"), PDiamond(OpenOpen(0, 1), AP("a"))))
  }

    it should "translate box correctly" in {
    val ap = AP("a")

    val d = Box(ClosedOpen(0, 1), ap)
    val translated = nf(d)

    assert(translated == Negation(Disjunction(Negation(AP("a")), Diamond(OpenOpen(0, 1), Negation(AP("a"))))))
  }

    it should "translate past box correctly" in {
    val ap = AP("a")

    val d = PBox(ClosedOpen(0, 1), ap)
    val translated = nf(d)

    assert(translated == Negation(S(ClosedOpen(0, 1), True, Negation(AP("a")))))
  }

  // it should "translate complex formulae correctly" in {
  //   val a = AP("a")
  //   val b = AP("b")

  //   val f = Implication(PBox(ClosedClosed(0, 100), a), b)
  //   val translated = nf(f)

  //   assert(translated == Implication(Negation(S(ClosedClosed(0, 100), True, Negation(AP("a")))), AP("b")))

  // }
}
