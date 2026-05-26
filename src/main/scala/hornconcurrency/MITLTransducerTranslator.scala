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
import hornconcurrency.MITL._
import hornconcurrency.TTTranslator.mitl_translation
import hornconcurrency.TimedTransducerEncoder.EncodedTransducer
import hornconcurrency.TimedTransducerEncoder.encodeTransducerEquation
import hornconcurrency.TimedTransducer.TimedTransducerEquation

object TTTranslator {
    def mitl_translation(formula: MITL): TimedTransducer.TimedTransducerEquation = {
        var nextVar: Int = 0

        def fresh(): Int = {
            nextVar = nextVar + 1
            nextVar
        }

        def unary(
            kind: TimedTransducer.BaseTransducerKind,
            inner: MITL,
            output: Int,
            bound: Int
        ): TimedTransducerEquation = {
            val input = fresh()
            val b = TimedTransducer.Base(TimedTransducer.baseTransducer(kind, input, output, bound))

            println(inner)

            inner match {
                case AP(_)  => b
                case _      => TimedTransducer.Sequential(translate(inner, input), b)
            }
        }

        def binary(
            kind: TimedTransducer.BaseTransducerKind,
            left: MITL,
            right: MITL,
            output: Int,
            bound: Int
        ): TimedTransducerEquation = {
            val leftInput = fresh()
            val rightInput = fresh()
            val b = TimedTransducer.Base(TimedTransducer.baseTransducer(kind, Seq(leftInput, rightInput), output, bound))

            val transducers = Seq(
                translateNonAtomic(left, leftInput),
                translateNonAtomic(right, rightInput)
            ).flatten

            transducers match {
                case Seq()  => b
                case Seq(single) => {
                    TimedTransducer.Sequential(single, b)
                }
                case Seq(l, r) => {
                    TimedTransducer.Sequential(TimedTransducer.Product(l, r), b)
                }
            }
        }

        def translateNonAtomic(formula: MITL, output: Int) : Option[TimedTransducer.TimedTransducerEquation] = {
            formula match {
                case AP(_) => None
                case _ => Some(translate(formula, output))
            }
        }

        def translate(formula: MITL, output: Int): TimedTransducer.TimedTransducerEquation = {
            formula match {
                case Negation(inner)                     => unary(TimedTransducer.BoolNot, inner, output, -1)
                case Diamond(ClosedClosed(0, a), inner)  => unary(TimedTransducer.Future, inner, output, a)
                case PDiamond(ClosedClosed(0, a), inner) => unary(TimedTransducer.Past, inner, output, a)
                case Disjunction(left, right)            => binary(TimedTransducer.BoolOr, left, right, output, -1)
                case U(ClosedClosed(0, a), left, right)  => binary(TimedTransducer.Until, left, right, output, a)
                case S(ClosedClosed(0, a), left, right)  => binary(TimedTransducer.Since, left, right, output, a)
                case _ => ???
            }
        }
        translate(formula, 0)
    }
}

object MainMITLTransducerTranslation extends App {

    val ap = AP("a")
    val formula = Diamond(ClosedClosed(0, 5), Diamond(ClosedClosed(0, 10), ap))

    val t = mitl_translation(formula)

    println(t)

    val e = encodeTransducerEquation(t)

    println(e)
}
