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

sealed trait MITL {
    // def propositions: Set[AP]

    // def &&(other: MITL) : MITL = {
    //     MITL.and(this, other)
    // }

    // def ||(other: MITL) : MITL = {
    //     MITL.or(this, other)
    // }
}

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

    sealed trait EInt {}

    case class ExtendedInt(value: Int) extends EInt {
        override def toString : String = value.toString
    }

    implicit def intToExtendedInt(x: Int): ExtendedInt =
        ExtendedInt(x)

    case class PosInfty() extends EInt {
        override def toString : String = "∞"

    }
    case class NegInfty() extends EInt {
        override def toString : String = "-∞"
    }

    sealed trait Interval {}

    final case class LCRO(left: Int, right: EInt) extends Interval {
        override def toString : String = "[" + left.toString() + ", " + right.toString() + ")"
    }
    final case class LORO(left: EInt, right: EInt) extends Interval {
        override def toString : String = "(" + left.toString() + ", " + right.toString() + ")"
    }
    final case class LCRC(left: Int, right: Int) extends Interval {
        override def toString : String = "[" + left.toString() + ", " + right.toString() + "]"
    }
    final case class LORC(left: EInt, right: Int) extends Interval {
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
    final case class U(interval: Interval, left: MITL, right: MITL) extends MITL {
        override def toString : String = "(" + left.toString() + " U_ " + interval + "(" + right.toString()  + ")"
    }
    final case class S(interval: Interval, left: MITL, right: MITL) extends MITL {
        override def toString : String = "(" + left.toString() + " S_" + interval + "(" + right.toString()  + ")"
    }
    final case class Lozenge(interval: Interval, inner: MITL) extends MITL  {
        override def toString : String = "♦_" + interval.toString() + "(" + inner.toString() + ")"
    }
    final case class PLozenge(interval: Interval, inner: MITL) extends MITL  {
        override def toString : String = "p♦_" + interval.toString() + "(" + inner.toString() + ")"
    }
    final case class Box(interval: Interval, inner: MITL) extends MITL  {
        override def toString : String = "□_" + interval.toString() + "(" + inner.toString() + ")"
    }
    final case class PBox(interval: Interval, inner: MITL) extends MITL  {
        override def toString : String = "⊟_" + interval.toString() + "(" + inner.toString() + ")"
    }

    // Probably want visitor instead.

    def translateNF(f: MITL): MITL = {
        f match {
            case True => True
            case False => False
            case AP(l) => AP(l)
            case Negation(Negation(i)) => translateNF(i)
            case Negation(i) => Negation(translateNF(i))
            case Disjunction(l, r) => Disjunction(translateNF(l), translateNF(r))
            case Conjunction(l, r) => Negation(Disjunction(Negation(translateNF(l)), Negation(translateNF(r))))
            case Implication(l, r) => Disjunction(Negation(translateNF(l)), translateNF(r))
            case U(i, l, r) => U(i, translateNF(l), translateNF(r))
            case S(i, l, r) => S(i, translateNF(l), translateNF(r))
            case Lozenge(interval, inner) => U(interval, True, translateNF(inner))
            case PLozenge(interval, inner) => S(interval, True, translateNF(inner))
            case Box(interval, inner) => Negation(U(interval, True, Negation(translateNF(inner))))
            case PBox(interval, inner) => Negation(S(interval, True, Negation(translateNF(inner))))
        }
    }
}