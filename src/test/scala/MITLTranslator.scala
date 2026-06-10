package hornconcurrency

import org.scalatest._
import ap.types.MonoSortedPredicate

class MITLTranslatorTests extends FlatSpec {
    import ap.parser._
    import ap.parser.IExpression._
    import ap.theories.ADT.BoolADT.{True, False}
    import ap.theories.rationals.Rationals
    import lazabs.horn.bottomup.HornClauses
    import HornClauses._
    import MITL._
    import MITLTransducerTranslator._
    import TimedTransducerEncoder._
    import SignalSystem._
    import System._
    import VerificationUtils._
    import Rationals.{geq, minus, int2ring => toRat}

    "MITL Once" should "prohibit runs where output is false for five time units after p" in {
        val formula = PDiamond(OpenOpen(0, 5), AP("p"))
        val encoded = encodeTransducerEquation(mitlTranslation(formula))

        val signalByLabel = encoded.head.globalSignalLabels.zip(encoded.head.globalSignalTerms).toMap
        val pSignal = signalByLabel("p")
        val qSignal = signalByLabel("0")

        val cMon = Rationals.dom.newConstant("c_mon")
        val monSorts = List(Rationals.dom) ++
            encoded.head.globalSignalTerms.map(_ => Sort.Bool) ++
            List(Rationals.dom)
        val monArgs = Seq(C) ++ encoded.head.globalSignalTerms ++ Seq(cMon)
        val resetMonArgs = Seq(C) ++ encoded.head.globalSignalTerms ++ Seq(C)
        val mon = for (i <- 0 to 2) yield MonoSortedPredicate("monitor" + i, monSorts)

        val monProc = List(
            // Wait until p becomes true, then reset the monitor clock.
            (mon(0)(monArgs: _*) :- true,
                NoSync),
            (mon(1)(resetMonArgs: _*) :-
                (mon(0)(monArgs: _*), pSignal === True),
                NoSync),

            (mon(2)(resetMonArgs: _*) :-
                (mon(1)(monArgs: _*), geq(minus(C, cMon), toRat(5))),
                NoSync)
        )

        val monProgressBlocks = List(
            ProgressBlock(List(Clause(HornClauses.FALSE(), List(mon(0)(monArgs: _*)), true))),
            ProgressBlock(List((qSignal === False) :- mon(1)(monArgs: _*)))
        )

        val assertion = false :- mon(2)(monArgs: _*)

        val globalVarNum = 1 + encoded.head.globalSignalTerms.size
        val system = SignalSystem(
            encoded.map(t => (t.clauses, System.Singleton)) :+ (monProc, System.Singleton),
            globalVarNum,
            Seq(assertion),
            RationalTime(0),
            (1 until globalVarNum).toSet,
            encoded.map(t => List(t.progressBlock)) :+ monProgressBlocks
        )

        val encoder = new SignalEncoder(system)
        val vl = runLoop(encoder.result)
        assert(isSolvable(vl))
    }
}
