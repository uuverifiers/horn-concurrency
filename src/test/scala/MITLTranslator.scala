package hornconcurrency

import org.scalatest.FlatSpec
import ap.types.MonoSortedPredicate

class MITLTranslatorTests extends FlatSpec {
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
    import Rationals.{geq, gt, lt, minus, int2ring => toRat}

    "MITL Future" should "prohibit runs where output is false for five time units after p" in {
        val formula = Diamond(OpenOpen(0, 5), AP("p"), None)
        val (encoded, _) = encodeTransducerEquation(mitlTranslation(formula))

        val signalByLabel = encoded.head.globalSignalLabels.zip(encoded.head.globalSignalTerms).toMap
        val pSignal = signalByLabel("p")
        val qSignal = signalByLabel("0")

        val cMon = Rationals.dom.newConstant("c_mon")
        val monSorts = List(Rationals.dom) ++
            encoded.head.globalSignalTerms.map(_ => Sort.Bool) ++
            List(Rationals.dom)
        val monArgs = Seq(C) ++ encoded.head.globalSignalTerms ++ Seq(cMon)
        val resetMonArgs = Seq(C) ++ encoded.head.globalSignalTerms ++ Seq(C)
        val mon = for (i <- 0 to 1) yield MonoSortedPredicate("monitor" + i, monSorts)

        val monProc = List(
            // Assume MITL formula is true
            (mon(0)(resetMonArgs: _*) :- (qSignal === True),
                NoSync),
            // Reach mon(1) after 5 units
            (mon(1)(resetMonArgs: _*) :-
                (mon(0)(monArgs: _*),
                    geq(minus(C, cMon), toRat(5))),
                NoSync)
        )

        val monProgressBlocks = List(
            // Allow time to progress as long as p is false
            ProgressBlock(List((pSignal === False) :- mon(0)(monArgs: _*))),
            ProgressBlock(List(Clause(HornClauses.FALSE(), List(mon(1)(monArgs: _*)), false)))
        )

        val assertion = false :- (mon(1)(monArgs: _*), (gt(minus(C, cMon), toRat(0))))

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

    "MITL Future" should "witness satisfaction when output is true and p occurs in the open interval" in {
        val formula = Diamond(OpenOpen(0, 5), AP("p"), None)
        val (encoded, _) = encodeTransducerEquation(mitlTranslation(formula))

        val signalByLabel = encoded.head.globalSignalLabels.zip(encoded.head.globalSignalTerms).toMap
        val pSignal = signalByLabel("p")
        val qSignal = signalByLabel("0")

        val cMon = Rationals.dom.newConstant("c_mon")
        val monSorts = List(Rationals.dom) ++
            encoded.head.globalSignalTerms.map(_ => Sort.Bool) ++
            List(Rationals.dom)
        val monArgs = Seq(C) ++ encoded.head.globalSignalTerms ++ Seq(cMon)
        val resetMonArgs = Seq(C) ++ encoded.head.globalSignalTerms ++ Seq(C)
        val mon = for (i <- 0 to 1) yield MonoSortedPredicate("satMonitor" + i, monSorts)

        val elapsed = minus(C, cMon)
        val monProc = List(
            (mon(0)(resetMonArgs: _*) :- (qSignal === True),
                NoSync),
            (mon(1)(monArgs: _*) :-
                (mon(0)(monArgs: _*),
                    pSignal === True,
                    gt(elapsed, toRat(0)),
                    lt(elapsed, toRat(5))),
                NoSync)
        )

        val monProgressBlocks = List(
            ProgressBlock(List(Clause(HornClauses.FALSE(), List(mon(0)(monArgs: _*)), false)))
        )

        val assertion = false :- mon(1)(monArgs: _*)

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
        assert(!isSolvable(vl))
    }
}
