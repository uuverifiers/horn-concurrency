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

class TimedTransducerTests extends FlatSpec {
  import TimedTransducer._
  import TimedTransducer.ClockConstraint._

  it should "conjoin correctly" in {
    val c1 = Clock("c1")
    val c2 = Clock("c2")

    val b1 = Bound(c1, Geq, 2)
    val b2 = Bound(c1, Leq, 1)
    val b3 = Bound(c2, Leq, 3)
    val b4 = Bound(c2, Geq, 5)

    val conj = b1 && b2
    val conj2 = conj && b3
    val conj3 = conj2 && b4

    println(conj)
    println(conj2)
    println(conj3)

    assert(conj3 == Conjunction(Seq(b1, b2, b3, b4)))
  }

  // "TimedTransducer" should "expose the phase-1 syntax model" in {
  //   val x = Clock("x")
  //   val accept = InputLabel("accept")
  //   val done = OutputLabel("done")
  //   val idle = Location("idle")
  //   val busy = Location("busy", Bound(x, LessEqual, 10))

  //   val guard = and(Bound(x, GreaterEqual, 2), Bound(x, LessEqual, 5))
  //   val transducer =
  //     TimedTransducer(
  //       _locations = List(idle, busy),
  //       _initialLocation = idle,
  //       _transitions = List(
  //         Transition(
  //           source = idle,
  //           target = busy,
  //           label = TransitionLabel(Some(accept), Set(done)),
  //           guard = guard,
  //           resets = Set(x)
  //         )
  //       ),
  //       _clocks = List(x),
  //       _inputLabels = List(accept),
  //       _outputLabels = List(done)
  //     )

  //   assert(transducer.initialLocation == idle)
  //   assert(transducer.locationSet == Set(idle, busy))
  //   assert(busy.label == "busy")
  //   assert(transducer.clockSet == Set(x))
  //   assert(transducer.inputLabelSet == Set(accept))
  //   assert(transducer.outputLabelSet == Set(done))
  //   assert(transducer.transitions.head.guard.referencedClocks == Set(x))
  //   assert(transducer.transitions.head.label.input.contains(accept))
  //   assert(transducer.transitions.head.label.outputs == Set(done))
  //   assert(busy.invariant.referencedClocks == Set(x))
  //   assert(transducer.invariants(busy).referencedClocks == Set(x))
  // }

  // it should "reject transitions that target the initial location" in {
  //   val start = Location("start")
  //   val other = Location("other")

  //   val err = intercept[IllegalArgumentException] {
  //     TimedTransducer(
  //       _locations = List(start, other),
  //       _initialLocation = start,
  //       _transitions = List(
  //         Transition(source = other, target = start)
  //       ),
  //       _clocks = List()
  //     )
  //   }

  //   assert(err.getMessage contains "initial location")
  // }
}
