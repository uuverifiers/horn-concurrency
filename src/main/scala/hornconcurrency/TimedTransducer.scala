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

object TimedTransducer {

  final case class Clock(label : String) {
    override def toString : String = label
  }

  sealed trait Label {
    def label: String
  }

  final case class InputLabel(label : String) extends Label {
    override def toString : String = label
  }

  final case class OutputLabel(label : String) extends Label {
    override def toString : String = label
  }

  sealed trait Formula[+A <: Label]
  object Formula {
    case object True extends Formula[Nothing]
    case object False extends Formula[Nothing]
    final case class Atom[A <: Label](value: A) extends Formula[A]
    final case class Not[A <: Label](arg: Formula[A]) extends Formula[A]
    final case class And[A <: Label](args: Seq[Formula[A]]) extends Formula[A]
    final case class Or[A <: Label](args: Seq[Formula[A]]) extends Formula[A]
  }

  sealed trait ClockConstraint {
    def &&(other: ClockConstraint): ClockConstraint = ClockConstraint.and(this, other)
  }
  object ClockConstraint {
    final case object True extends ClockConstraint

    sealed trait Relation {
        def symbol: String
    }

    final case object Lt extends Relation {
        val symbol = "<"
    }

    final case object Leq extends Relation {
        val symbol = "<="
    }

    final case object Gt extends Relation {
        val symbol = ">"
    }

    final case object Geq extends Relation {
        val symbol = ">="
    }

    final case object Eq extends Relation {
        val symbol = "=="
    }

    final case class Bound(clock: Clock,
                           operator: Relation,
                           constant: Int) extends ClockConstraint {}

    final case class Conjunction(constraints: Seq[ClockConstraint]) extends ClockConstraint {}

    def and(c1: ClockConstraint, c2: ClockConstraint): ClockConstraint = {
        and(Seq(c1, c2))
    }

    def and(constraints: Seq[ClockConstraint]): ClockConstraint = {
        val s = constraints.flatMap({
            case True => Seq.empty
            case b: Bound => Seq(b)
            case Conjunction(s) => s 
        })

        s match {
            case Seq() => True
            case Seq(singleton) => singleton
            case conj => Conjunction(conj)
        }
    }
  }

  final case class SignalLabel(input : Formula[InputLabel],
                               output: Formula[OutputLabel]) {
  }

  final case class Location(label : String,
                            signalLabel: SignalLabel,
                            invariant: ClockConstraint = ClockConstraint.True) {
    override def toString : String = label
  }

  final case class Transition(source: Location,
                              target: Location,
                              signalLabel: SignalLabel,
                              guard: ClockConstraint,
                              resetInstruction: Seq[Clock]) {
  }

  case class TimedTransducer(name:String,
                             locations: Seq[Location],
                             initialLocation: Location,
                             clocks: Seq[Clock],
                             inputLabels: Seq[InputLabel],
                             outputLabels: Seq[OutputLabel],
                             transitions: Seq[Transition])

  sealed trait TimedTransducerEquation
  case class Base(t: TimedTransducer) extends TimedTransducerEquation
  case class Product(t1: TimedTransducerEquation, t2: TimedTransducerEquation)
    extends TimedTransducerEquation
  case class Sequential(t1: TimedTransducerEquation, t2: TimedTransducerEquation)
    extends TimedTransducerEquation
}

