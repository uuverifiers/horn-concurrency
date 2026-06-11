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
import hornconcurrency.MITLTransducerTranslator.mitlTranslation
import hornconcurrency.TimedTransducerEncoder.EncodedTransducer
import hornconcurrency.TimedTransducerEncoder.encodeTransducerEquation
import hornconcurrency.TimedTransducer.TimedTransducerEquation

object MITLTransducerTranslator {
    def mitlTranslation(formula: MITL): TimedTransducer.TimedTransducerEquation = {
        var nextVar: Int = 0

        def fresh(): Int = {
            nextVar = nextVar + 1
            nextVar
        }

        def unary(
            kind: TimedTransducer.BaseTransducerKind,
            inner: MITL,
            output: Int,
            bound: Int,
            rank_id: Option[Int]
        ): TimedTransducerEquation = {
            def transducerFromInput(input: String) : TimedTransducer.Base = {
                TimedTransducer.Base(
                        TimedTransducer.baseTransducer(
                            kind,
                            TimedTransducer.InputLabel(input),
                            TimedTransducer.OutputLabel(output.toString()),
                            bound,
                            rank_id
                        )
                    )
            }
            inner match {
                case AP(label)  =>
                    transducerFromInput(label)
                case _      =>
                    val intermediateSignal = fresh()
                    val base = transducerFromInput(intermediateSignal.toString())
                    TimedTransducer.Sequential(translate(inner, intermediateSignal), base)
            }
        }

        def binary(
            kind: TimedTransducer.BaseTransducerKind,
            left: MITL,
            right: MITL,
            output: Int,
            bound: Int,
            rank_id: Option[Int]
        ): TimedTransducerEquation = {
            val (leftInput, leftTransducer) = InputFor(left)
            val (rightInput, rightTransducer) = InputFor(right)


            val transducers = Seq(
                leftTransducer,
                rightTransducer
            ).flatten

            val b = TimedTransducer.Base(
                TimedTransducer.baseTransducer(
                    kind,
                    Seq(TimedTransducer.InputLabel(leftInput), TimedTransducer.InputLabel(rightInput)),
                    TimedTransducer.OutputLabel(output.toString()),
                    bound,
                    rank_id
                )
            )
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

        def InputFor(formula: MITL) : (String, Option[TimedTransducer.TimedTransducerEquation]) = {
            formula match {
                case AP(label) => (label, None)
                case _ =>
                    val intermediateSignal = fresh()
                    (intermediateSignal.toString(), Some(translate(formula, intermediateSignal)))
            }
        }

        /*  Main idea: Given a temporal operator, e.g. F_{(0,a)}(p), generate a transducer T_F
            s.t. T_F has p as input and a fresh variable q as output.
        */
        def translate(formula: MITL, outputSignal: Int): TimedTransducer.TimedTransducerEquation = {
            formula match {
                case Negation(inner) => unary(TimedTransducer.BoolNot, inner, outputSignal, -1, None)
                case Diamond(OpenOpen(Finite(0), Finite(a)), inner, rank)  => 
                    unary(TimedTransducer.Future, inner, outputSignal, a, rank)
                case PDiamond(OpenOpen(Finite(0), Finite(a)), inner, rank) => 
                    unary(TimedTransducer.Past, inner, outputSignal, a, rank)
                case Disjunction(left, right) => 
                    binary(TimedTransducer.BoolOr, left, right, outputSignal, -1, None)
                case U(OpenOpen(Finite(0), PosInfty), left, right, rank)  => 
                    binary(TimedTransducer.Until, left, right, outputSignal, -1, rank)
                case S(OpenOpen(Finite(0), PosInfty), left, right, rank)  => 
                    binary(TimedTransducer.Since, left, right, outputSignal, -1, rank)
                case _ => ???
            }
        }
        translate(formula, 0)
    }
}