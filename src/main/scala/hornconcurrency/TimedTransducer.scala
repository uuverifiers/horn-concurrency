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

  sealed trait BaseTransducerKind
  case object BoolNot extends BaseTransducerKind
  case object BoolOr extends BaseTransducerKind
  case object Future extends BaseTransducerKind
  case object Past extends BaseTransducerKind
  case object Until extends BaseTransducerKind
  case object Since extends BaseTransducerKind

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

  case class TimedTransducer(//TODO: breaks something?
                             name:String,
                             locations: Seq[Location],
                             initialLocation: Location,
                             clocks: Seq[Clock],
                             inputLabels: Seq[InputLabel],
                             outputLabels: Seq[OutputLabel],
                             transitions: Seq[Transition],
                             acceptanceCondition: Seq[(Seq[Location], Seq[Transition])] = Seq.empty,
                             rank_id: Option[Int]
                             )

  def location_to_acceptance_sets(l : Location, tt : TimedTransducer) : Seq[Int] = {
    tt.acceptanceCondition.zipWithIndex.collect {
      case ((locs, _), idx) if locs.contains(l) => idx
    }
  }
  def transition_to_acceptance_sets(t : Transition, tt : TimedTransducer) : Seq[Int] = {
    tt.acceptanceCondition.zipWithIndex.collect {
      case ((_, transitions), idx) if transitions.contains(t) => idx
    }
  }                           


  sealed trait TimedTransducerEquation
  case class Base(t: TimedTransducer) extends TimedTransducerEquation
  case class Product(t1: TimedTransducerEquation, t2: TimedTransducerEquation)
    extends TimedTransducerEquation
  case class Sequential(t1: TimedTransducerEquation, t2: TimedTransducerEquation)
    extends TimedTransducerEquation

  def baseTransducer(
                     kind: BaseTransducerKind,
                     input: InputLabel,
                     output: OutputLabel,
                     const: Int,
                     rank_id: Option[Int]): TimedTransducer =
    baseTransducer(kind, Seq(input), output, const, rank_id)

  def baseTransducer(
                     kind: BaseTransducerKind,
                     inputs: Seq[InputLabel],
                     output: OutputLabel,
                     const: Int,
                     rank_id: Option[Int]): TimedTransducer = {
    import ClockConstraint._
    import Formula._

    def inputName(i: Int): String = inputs(i).toString
    def inLabel(i: Int): InputLabel = InputLabel(inputName(i))
    val outputLabel = OutputLabel(output.toString)
    val c = Clock("c")
    val a = const

    val q = Atom(outputLabel)
    val notQ = Not(q)

    def u(s: String): Formula[InputLabel] = Atom(InputLabel(s))
    def notU(s: String): Formula[InputLabel] = Not(u(s))
    def andIn(args: Formula[InputLabel]*): Formula[InputLabel] = And(args)
    def orIn(args: Formula[InputLabel]*): Formula[InputLabel] = Or(args)
    def loc(label: String,
            input: Formula[InputLabel],
            output: Formula[OutputLabel],
            invariant: ClockConstraint = ClockConstraint.True): Location =
      Location(label, SignalLabel(input, output), invariant)
    def trans(source: Location,
              target: Location,
              input: Formula[InputLabel],
              output: Formula[OutputLabel],
              guard: ClockConstraint = ClockConstraint.True,
              reset: Boolean = false): Transition =
      Transition(source, target, SignalLabel(input, output), guard,
        if (reset) Seq(c) else Seq.empty)

    val si = loc("Si", Formula.True, Formula.True)

    // refactor later...
    kind match {
      case BoolNot =>
        val input = inputName(0)
        val inputLabel = InputLabel(input)
        val s0 = loc("S0", u(input), notQ)
        val s1 = loc("S1", notU(input), q)
        val locations = Seq(si, s0, s1)

        TimedTransducer(
          "NotTransducer_" + inputs.mkString("_") + "_" + output.toString,
          locations,
          si,
          Seq.empty,
          Seq(inputLabel),
          Seq(outputLabel),
          Seq(
            trans(si, s0, u(input), notQ),
            trans(si, s1, notU(input), q),
            trans(s0, s0, u(input), notQ),
            trans(s0, s1, notU(input), q),
            trans(s1, s0, u(input), notQ),
            trans(s1, s1, notU(input), q)
          ),
          Seq.empty,
          rank_id)

      case BoolOr =>
        val input1 = inputName(0)
        val inputLabel1 = InputLabel(input1)
        val input2 = inputName(1)
        val inputLabel2 = InputLabel(input2)
        val inputTrue = orIn(u(input1), u(input2))
        val inputFalse = andIn(notU(input1), notU(input2))
        val s0 = loc("S0", inputTrue, q)
        val s1 = loc("S1", inputFalse, notQ)
        val locations = Seq(si, s0, s1)

        TimedTransducer(
          "OrTransducer_" + inputs.mkString("_") + "_" + output.toString,
          locations,
          si,
          Seq.empty,
          Seq(inputLabel1, inputLabel2),
          Seq(outputLabel),
          Seq(
            trans(si, s0, inputTrue, q),
            trans(si, s1, inputFalse, notQ),
            trans(s0, s0, inputTrue, q),
            trans(s0, s1, inputFalse, notQ),
            trans(s1, s0, inputTrue, q),
            trans(s1, s1, inputFalse, notQ)
          ),
          Seq.empty,
          rank_id)

      case Future =>
        val input = inputName(0)
        val s0 = loc("S0", u(input), q)
        val s1 = loc("S1", notU(input), q, Bound(c, Lt, a))
        val s2 = loc("S2", notU(input), q, Bound(c, Lt, a))
        val s3 = loc("S3", notU(input), notQ)
        val locations = Seq(si, s0, s1, s2, s3)

        TimedTransducer(
          "FutureTransducer_" + inputs.mkString("_") + "_" + output.toString,
          locations,
          si,
          Seq(c),
          inputs.indices.map(inLabel),
          Seq(outputLabel),
          Seq(
            trans(si, s0, Formula.True, q),
            trans(si, s1, Formula.True, notQ, reset = true),
            trans(si, s2, Formula.True, q, reset = true),
            trans(si, s3, Formula.True, notQ),
            trans(s0, s0, notU(input), q),
            trans(s0, s1, Formula.True, notQ, reset = true),
            trans(s0, s2, Formula.True, q, reset = true),
            trans(s0, s3, Formula.True, notQ),
            trans(s1, s0, Formula.True, q, Bound(c, Eq, a)), 
            trans(s1, s1, u(input), notQ, Bound(c, Eq, a), reset = true),
            trans(s1, s2, u(input), q, Bound(c, Eq, a), reset = true),
            trans(s1, s3, u(input), notQ, Bound(c, Eq, a)),
            trans(s2, s0, Formula.True, notQ, Bound(c, Lt, a)),
            trans(s2, s1, u(input), notQ, Bound(c, Lt, a), reset = true),
            trans(s2, s2, u(input), q, Bound(c, Lt, a), reset = true),
            trans(s2, s3, u(input), notQ, Bound(c, Lt, a)),
            trans(s3, s1, notU(input), notQ, reset = true)          ),
          Seq.empty,
          rank_id)

      case Past =>
        val input = inputName(0)
        val s0 = loc("S0", u(input), q)
        val s1 = loc("S1", notU(input), q, Bound(c, Lt, a))
        val s2 = loc("S2", notU(input), notQ)
        val locations = Seq(si, s0, s1, s2)

        TimedTransducer(
          "PastTransducer_" + inputs.mkString("_") + "_" + output.toString,
          locations,
          si,
          Seq(c),
          inputs.indices.map(inLabel),
          Seq(outputLabel),
          Seq(
            trans(si, s0, Formula.True, notQ),
            trans(si, s1, u(input), notQ, reset = true),
            trans(si, s2, notU(input), notQ),
            trans(s0, s0, notU(input), q),
            trans(s0, s1, Formula.True, q, reset = true),
            trans(s0, s0, Formula.True, q, Bound(c, Lt, a)),
            trans(s1, s0, Formula.True, notQ, Bound(c, Eq, a)),
            trans(s1, s1, u(input), q, Bound(c, Lt, a), reset = true),
            trans(s1, s1, u(input), notQ, Bound(c, Eq, a), reset = true),
            trans(s1, s2, notU(input), notQ, Bound(c, Eq, a)),
            trans(s2, s0, Formula.True, notQ),
            trans(s2, s1, u(input), notQ)
          ),
          Seq.empty,
          rank_id)

      case Until =>
        val input1 = inputName(0)
        val input2 = inputName(1)
        val s0 = loc("S0", andIn(u(input1), u(input2)), q)
        val s1 = loc("S1", andIn(u(input1), notU(input2)), q)
        val s2 = loc("S2", notU(input1), notQ)
        val s3 = loc("S3", andIn(u(input1), notU(input2)), notQ)
        val locations = Seq(si, s0, s1, s2, s3) 
        TimedTransducer(
          "UntilTransducer_" + inputs.mkString("_") + "_" + output.toString,
          locations,
          si,
          Seq(c),
          inputs.indices.map(inLabel),
          Seq(outputLabel),
          Seq(
            trans(si, s0, Formula.True, q),
            trans(si, s1, Formula.True, q),
            trans(si, s2, Formula.True, notQ),
            trans(si, s3, Formula.True, notQ),
            trans(s0, s0, orIn(notU(input1), notU(input2)), q),
            trans(s0, s1, Formula.True, q),
            trans(s0, s2, Formula.True, notQ),
            trans(s0, s3, Formula.True, notQ),
            trans(s1, s0, orIn(u(input1), u(input2)), q),
            trans(s1, s1, u(input2), q),
            trans(s1, s2, u(input2), notQ),
            trans(s1, s3, u(input2), notQ),
            trans(s2, s0, Formula.True, q),
            trans(s2, s1, Formula.True, q),
            trans(s2, s2, u(input1), notQ),
            trans(s2, s3, Formula.True, notQ),
            trans(s3, s0, andIn(notU(input1), notU(input2)), q),
            trans(s3, s1, andIn(notU(input1), notU(input2)), q),
            trans(s3, s2, u(input2), notQ),
            trans(s3, s3, andIn(notU(input1), notU(input2)), notQ)
          ),
          Seq((Seq(s0, s2, s3), Seq.empty)),
          rank_id
          )

      case Since =>
        val input1 = inputName(0)
        val input2 = inputName(1)
        val s0 = loc("S0", andIn(u(input1), u(input2)), q)
        val s1 = loc("S1", andIn(u(input1), notU(input2)), q)
        val s2 = loc("S2", notU(input1), notQ)
        val s3 = loc("S3", andIn(u(input1), notU(input2)), notQ)
        val locations = Seq(si, s0, s1, s2, s3)

        TimedTransducer(
          "SinceTransducer_" + inputs.mkString("_") + "_" + output.toString,
          locations,
          si,
          Seq(c),
          inputs.indices.map(inLabel),
          Seq(outputLabel),
          Seq(
            trans(si, s0, Formula.True, q),
            trans(si, s1, u(input2), notQ),
            trans(si, s2, Formula.True, q),
            trans(si, s3, notU(input2), notQ),
            trans(s0, s0, orIn(notU(input1), notU(input2)), q),
            trans(s0, s1, orIn(u(input1), u(input2)), notQ),
            trans(s0, s2, Formula.True, q),
            trans(s0, s3, andIn(notU(input1), notU(input2)), notQ),
            trans(s1, s0, Formula.True, q),
            trans(s1, s1, u(input2), notQ),
            trans(s1, s2, Formula.True, q),
            trans(s1, s3, andIn(notU(input1), notU(input2)), notQ),
            trans(s2, s0, Formula.True, notQ),
            trans(s2, s1, u(input2), notQ),
            trans(s2, s2, u(input1), q),
            trans(s2, s3, notU(input2), notQ),
            trans(s3, s0, Formula.True, notQ),
            trans(s3, s1, notU(input2), notQ),
            trans(s3, s2, Formula.True, notQ),
            trans(s3, s3, andIn(notU(input1), notU(input2)), notQ)
          ),
          Seq.empty,
          rank_id)
    }
  }
}
