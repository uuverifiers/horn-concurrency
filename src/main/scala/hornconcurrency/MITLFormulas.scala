/**
 * Copyright (c) 2026 Traton AB. All rights reserved.
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


sealed trait MITL {}

object MITL {
    final case class AP(label: String) extends MITL {
        override def toString : String = label
    }

    final case object True extends MITL {
        override def toString : String = "⊤"
    }
    final case object False extends MITL {
        override def toString : String = "⊥"
    }

    sealed trait EInt

    case class Finite(value: Int) extends EInt {
        override def toString : String = value.toString
    }

    implicit def intToFinite(x: Int): Finite =
        Finite(x)

    case object PosInfty extends EInt {
        override def toString : String = "∞"
    }
    case object NegInfty extends EInt {
        override def toString : String = "-∞"
    }

    sealed trait Interval {}

    final case class ClosedOpen(left: Int, right: EInt) extends Interval {
        override def toString : String = "[" + left.toString() + ", " + right.toString() + ")"
    }
    final case class OpenOpen(left: EInt, right: EInt) extends Interval {
        override def toString : String = "(" + left.toString() + ", " + right.toString() + ")"
    }
    final case class ClosedClosed(left: Int, right: Int) extends Interval {
        override def toString : String = "[" + left.toString() + ", " + right.toString() + "]"
    }
    final case class OpenClosed(left: EInt, right: Int) extends Interval {
        override def toString : String = "(" + left.toString() + ", " + right.toString() + "]"
    }

    final case class Negation(inner: MITL) extends MITL {
        override def toString : String = "¬(" + inner.toString() + ")"
    }
    final case class Disjunction(left: MITL, right: MITL) extends MITL {
        override def toString : String = "(" + left.toString() + " ∨ " + right.toString()  + ")"
    }
    final case class Conjunction(left: MITL, right: MITL) extends MITL {
        override def toString : String = "(" + left.toString() + " ∧ " + right.toString()  + ")"
    }
    final case class Implication(left: MITL, right: MITL) extends MITL {
        override def toString : String = "(" + left.toString() + " => " + right.toString()  + ")"
    }

    final case class U(interval: Interval, left: MITL, right: MITL, rankId: Option[Int]) extends MITL {
        override def toString : String = "(" + left.toString() + " U_" + interval + "(" + right.toString()  + ")"
    }
    final case class S(interval: Interval, left: MITL, right: MITL, rankId: Option[Int]) extends MITL {
        override def toString : String = "(" + left.toString() + " S_" + interval + "(" + right.toString()  + ")"
    }
    final case class Diamond(interval: Interval, inner: MITL, rankId: Option[Int]) extends MITL  {
        override def toString : String = "♦_" + interval.toString() + "(" + inner.toString() + ")"
    }
    final case class PDiamond(interval: Interval, inner: MITL, rankId: Option[Int]) extends MITL  {
        override def toString : String = "p♦_" + interval.toString() + "(" + inner.toString() + ")"
    }
    final case class Box(interval: Interval, inner: MITL, rankId: Option[Int]) extends MITL  {
        override def toString : String = "□_" + interval.toString() + "(" + inner.toString() + ")"
    }
    final case class PBox(interval: Interval, inner: MITL, rankId: Option[Int]) extends MITL  {
        override def toString : String = "⊟_" + interval.toString() + "(" + inner.toString() + ")"
    }

    // Probably want visitor instead.

    def nf(f: MITL): MITL = {
        f match {
            /* Bases cases */
            case True => True
            case False => False
            case AP(lit) => AP(lit)
            // case Negation(Negation(inner)) => nf(inner)
            case Negation(inner) => Negation(nf(inner))
            case Disjunction(left, right) => Disjunction(nf(left), nf(right))
            case Conjunction(left, right) => Negation(Disjunction(Negation(nf(left)), Negation(nf(right))))
            // case Conjunction(left, right) => Conjunction(nf(left), nf(right))
            case Implication(left, right) => Disjunction(Negation(nf(left)), nf(right))
            case U(OpenOpen(Finite(0), PosInfty), left, right, rank) =>
                val l = nf(left)
                val r = nf(right)
                U(OpenOpen(Finite(0), PosInfty), l, r, rank)
            case S(OpenOpen(Finite(0), PosInfty), left, right, rank) =>
                val l = nf(left)
                val r = nf(right)
                S(OpenOpen(Finite(0), PosInfty), l, r, rank)
            case Diamond(OpenOpen(Finite(0), Finite(b)), inner, rank) =>
                Diamond(OpenOpen(Finite(0), Finite(b)), nf(inner), rank)
            case PDiamond(OpenOpen(Finite(0), Finite(b)), inner, rank) =>
                PDiamond(OpenOpen(Finite(0), Finite(b)), nf(inner), rank)

            /* Inductive rewriting rules */
            
            case U(OpenOpen(Finite(c), PosInfty), left, right, rank) =>
                val res = Box(OpenClosed(0, c), Conjunction(left, U(OpenOpen(0, PosInfty), left, right, rank)), rank)
                nf(res)
            case U(OpenOpen(a, b), left, right, rank) =>
                val res = Conjunction(
                    U(OpenOpen(a, PosInfty), left, right, rank),
                    Diamond(OpenOpen(a,b), right, rank)
                )
                nf(res)
            case U(OpenClosed(a, b), left, right, rank) =>
                val res = Conjunction(
                    U(OpenOpen(a, PosInfty), left, right, rank),
                    Diamond(OpenClosed(a,b), right, rank)
                )
                nf(res)
            case U(ClosedOpen(c, PosInfty), left, right, rank) =>
                val res = Conjunction(
                    Box(OpenOpen(0, c), left, rank),
                    Box(OpenClosed(0, c), 
                        Disjunction(
                            right,
                            Conjunction(
                                left, 
                                U(OpenOpen(0, PosInfty), left, right, rank))), rank)
                )
                nf(res)
            case U(ClosedOpen(a, b), left, right, rank) =>
                val res = Conjunction(
                    U(ClosedOpen(a, PosInfty), left, right, rank),
                    Diamond(ClosedOpen(a,b), right, rank)
                )
                nf(res)
            case U(ClosedClosed(a, b), left, right, rank) =>
                val res = Conjunction(
                    U(ClosedOpen(a, PosInfty), left, right, rank),
                    Diamond(ClosedClosed(a,b), right, rank)
                )
                nf(res)
            case U(i, left, right, rank) => U(i, nf(left), nf(right), rank)
            case S(OpenOpen(Finite(c), PosInfty), left, right, rank) =>
                val l = nf(left)
                val r = nf(right)
                nf(PBox(OpenClosed(0, c), Conjunction(l, S(OpenOpen(0, PosInfty), l, r, rank)), rank))
            case S(OpenOpen(a, b), left, right, rank) =>
                val l = nf(left)
                val r = nf(right)
                val res = Conjunction(
                    S(OpenOpen(a, PosInfty), l, r, rank),
                    PDiamond(OpenOpen(a,b), r, rank)
                )
                nf(res)
            case S(OpenClosed(a, b), left, right, rank) =>
                val l = nf(left)
                val r = nf(right)
                val res = Conjunction(
                    S(OpenOpen(a, PosInfty), l, r, rank),
                    PDiamond(OpenClosed(a,b), r, rank)
                )
                nf(res)
            case S(ClosedOpen(c, PosInfty), left, right, rank) =>
                val l = nf(left)
                val r = nf(right)
                val res = Conjunction(
                    PBox(OpenOpen(0, c), l, rank),
                    PBox(OpenClosed(0, c), Disjunction(r, Conjunction(l, S(OpenOpen(0, PosInfty), l, r, rank))), rank)
                )
                nf(res)
            case S(ClosedOpen(a, b), left, right, rank) =>
                val l = nf(left)
                val r = nf(right)
                val res = Conjunction(
                    S(ClosedOpen(a, PosInfty), l, r, rank),
                    PDiamond(ClosedOpen(a,b), r, rank)
                )
                nf(res)
            case S(ClosedClosed(a, b), left, right, rank) =>
                val l = nf(left)
                val r = nf(right)
                val res = Conjunction(
                    S(ClosedOpen(a, PosInfty), l, r, rank),
                    PDiamond(ClosedClosed(a,b), r, rank)
                )
                nf(res)
            case S(i, left, right, rank) => S(i, nf(left), nf(right), rank)

            case Diamond(OpenClosed(Finite(0), a), inner, rank) =>
                val res = Disjunction(
                    Diamond(OpenOpen(0, a), inner, rank),
                    Conjunction(
                        U(OpenOpen(0, PosInfty), Diamond(OpenOpen(0, a), inner, rank), Diamond(OpenOpen(0, a), inner, rank), rank),
                        U(OpenOpen(0, PosInfty), Negation(inner), inner, rank)
                    ))
                nf(res)
            case Diamond(ClosedOpen(0, a), inner, rank) =>
                nf(Disjunction(inner, Diamond(OpenOpen(0, a), inner, rank)))
            case Diamond(ClosedClosed(0, a), inner, rank) => 
                nf(Disjunction(inner, Diamond(OpenClosed(0, a), inner, rank)))
            case Diamond(OpenOpen(Finite(a), Finite(b)), inner, rank) => 
                val c = math.min(a, b-a)
                val res = Diamond(OpenOpen(0, c), Box(OpenOpen(0, c), Diamond(OpenOpen(a-c, b-c), inner, rank), rank), rank)
                nf(res)
            case Diamond(OpenClosed(Finite(a), b), inner, rank) => 
                val c = math.min(a, b-a)
                val res = Diamond(OpenClosed(0, c), Box(ClosedOpen(0, c), Diamond(OpenClosed(a-c, b-c), inner, rank), rank), rank)
                nf(res)
            case Diamond(ClosedOpen(a, Finite(b)), inner, rank) if b-a > 0 => 
                val c = math.min(a, b-a)
                val res = Diamond(ClosedOpen(0, c), Box(OpenClosed(0, c), Diamond(ClosedOpen(a-c, b-c), inner, rank), rank), rank)
                nf(res)
            case Diamond(ClosedClosed(a, b), inner, rank) =>
                val c = math.min(a, b-a)
                val res = Diamond(ClosedClosed(0, c), Box(ClosedClosed(0, c), Diamond(ClosedClosed(a-c, b-c), inner, rank), rank), rank)
                nf(res)
            // case Diamond(interval, inner) => U(interval, True, nf(inner))
            
            case PDiamond(OpenClosed(Finite(0), a), inner, rank) =>
                val i = nf(inner)
                val res = Disjunction(
                    PDiamond(OpenOpen(0, a), i, rank),
                    Conjunction(
                        S(OpenOpen(0, PosInfty), PDiamond(OpenOpen(0, a), i, rank), PDiamond(OpenOpen(0, a), i, rank), rank),
                        S(OpenOpen(0, PosInfty), Negation(i), i, rank)
                    ))
                nf(res)
            case PDiamond(ClosedOpen(0, a), inner, rank) =>
                val i = nf(inner)
                Disjunction(i, PDiamond(OpenOpen(0, a), i, rank))
            case PDiamond(ClosedClosed(0, a), inner, rank) =>
                val i = nf(inner)
                nf(Disjunction(i, PDiamond(OpenClosed(0, a), i, rank)))
            case PDiamond(OpenOpen(Finite(a), Finite(b)), inner, rank) => 
                val c = math.min(a, b-a)
                val res = PDiamond(OpenOpen(0, c), PBox(OpenOpen(0, c), PDiamond(OpenOpen(a-c, b-c), inner, rank), rank), rank)
                nf(res)
            case PDiamond(OpenClosed(Finite(a), b), inner, rank) => 
                val c = math.min(a, b-a)
                val res = PDiamond(OpenClosed(0, c), PBox(ClosedOpen(0, c), PDiamond(OpenClosed(a-c, b-c), inner, rank), rank), rank)
                nf(res)
            case PDiamond(ClosedOpen(a, Finite(b)), inner, rank) => 
                val c = math.min(a, b-a)
                val res = PDiamond(ClosedOpen(0, c), PBox(OpenClosed(0, c), PDiamond(ClosedOpen(a-c, b-c), inner, rank), rank), rank)
                nf(res)
            case PDiamond(ClosedClosed(a, b), inner, rank) => 
                val c = math.min(a, b-a)
                val res = PDiamond(ClosedClosed(0, c), PBox(ClosedClosed(0, c), PDiamond(ClosedClosed(a-c, b-c), inner, rank), rank), rank)
                nf(res)
            case PDiamond(interval, inner, rank) => S(interval, True, nf(inner), rank)
            case Box(interval, inner, rank) => nf(Negation(Diamond(interval, Negation(inner), rank)))
            // case Box(interval, inner) => Negation(U(interval, True, Negation(nf(inner))))
            case PBox(interval, inner, rank) => nf(Negation(PDiamond(interval, Negation(inner), rank)))
            case Diamond(OpenOpen(a, b), inner, rank) => nf(U(OpenOpen(a, b), True, inner, rank))
        }
    }
}
