package hornconcurrency

import org.scalatest._

class MITLTranslatorTests extends FlatSpec {
    import ap.parser._
    import ap.parser.IExpression._
    import ap.theories.ADT.BoolADT.{True}
    import ap.theories.rationals.Rationals
    import lazabs.horn.bottomup.HornClauses
    import HornClauses._
    import MITL._
    import MITLTransducerTranslator._
    import TimedTransducerEncoder._
    import SignalSystem._
    import System._
    import VerificationUtils._

    def signalSystem(
        encoded: Seq[EncodedTransducer],
        assertions: Seq[HornClauses.Clause],
        progressBlocks: Seq[Seq[ProgressBlock]]) = {
        val globalVarNum = 1 + encoded.head.globalSignalTerms.size
        SignalSystem(
            encoded.map(t => (t.clauses, System.Singleton)),
            globalVarNum,
            assertions,
            RationalTime(0),
            (1 until globalVarNum).toSet,
            progressBlocks
        )
    }

    def signalSystem(encoded: Seq[EncodedTransducer], assertions: Seq[HornClauses.Clause]): SignalSystem =
        signalSystem(encoded, assertions, encoded.map(t => List(t.progressBlock)))


    // "MITL nested future with SignalSystem" should "hold when the input signal is currently true in stable non-initial states" in {
    //     val formula = Diamond(ClosedClosed(0, 5), Diamond(ClosedClosed(0, 10), AP("p")))
    //     val encoded = encodeTransducerEquation(mitlTranslation(formula))

    //     val signalByLabel = encoded.head.globalSignalLabels.zip(encoded.head.globalSignalTerms).toMap
    //     val outputSignal = signalByLabel("0")
    //     val inputSignal = signalByLabel("2")

    //     // val assertion = false :- ???

    //     val system = signalSystem(encoded, Seq())

    //     val encoder = new SignalEncoder(system)
    //     val vl = runLoop(encoder.result)
    //     assert(isSolvable(vl))
    // }
}
