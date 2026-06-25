package hornconcurrency
import hornconcurrency.MITL._
import hornconcurrency.mitl.Absyn._

import ap.parser.IExpression
import ap.parser._
import ap.parser.IExpression._

import hornconcurrency.mitl.Yylex
import hornconcurrency.mitl.parser

import scala.collection.mutable.{Map => MMap}
case class MitlVar(name: String, sort: IExpression.Sort) {
  val term = sort match {
    case IExpression.Sort.Integer => IExpression.Sort.Integer.newConstant(name)
    case _ =>  ???
  }
}

case class MITLContext(
  mitls: Seq[MITL], 
  apMap: Map[String, Seq[ITerm] => IFormula], 
  ranks: Map[Int, Seq[ITerm] => ITerm]
)


object MITLContext {

  class MitlConverter(val varTerms: Seq[ITerm]) {
    //Converts from the parse tree to our own MITL ast
    // keeps a map apMap from variables to atomic propositions
    private var apMap: Map[String, Seq[ITerm] => IFormula] = Map()
    private var rankMap: Map[Int, Seq[ITerm] => ITerm] = Map()
    private var signal_var_id = 1
    private var mitlFormulas: Seq[MITL] = Seq()


    def toMitlContext() = MITLContext(mitlFormulas, apMap.toMap, rankMap.toMap)

    private def varToIndex: Map[String, Int] = 
      varTerms.zipWithIndex.map{case (vt, idx) => (vt.toString, idx)}.toMap


    def get_fresh_signal_var(varName: String = "q") = {
      val tmp = signal_var_id
      signal_var_id += 1
      varName + signal_var_id.toString      
    } 

    def parseMany(strs: Seq[String]) : MITLContext = {
      val parsedStrs: Seq[MitlDecl] = strs.map(s => parse(s))
      val parsedMitls: Seq[MFormula] = parsedStrs.collect{
        case mdecl: MitlFDecl => 
          mdecl.mitl_ match {case m: MitlSpec => m.mformula_}
      }
      val parsedRanks: (Seq[(Int, MExpr)]) = parsedStrs.collect{
        case rdecl: RankDecl =>  rdecl.ranking_ match {
            case r: RankFunc => (r.integer_, r.mexpr_)
        }
      }
      parsedRanks.foreach{ r => 
        val rank_expr = translateExpr(r._2)(_)
        rankMap = rankMap + ((r._1, rank_expr))
      }
      mitlFormulas = parsedMitls.map(translateFormula)
      toMitlContext()
    }
    

    def parse(input: String): MitlDecl = {
        import java.io.StringReader
        val reader = new StringReader(input)
        
        val lexer = new Yylex(reader)
        val parser = new parser(lexer, lexer.getSymbolFactory())

        val result = parser.pMitlDecl()   // entry point from BNFC
        result
    }

    def translateFormula(formula: MFormula): MITL = {
        formula match {
          case f: MFIff =>
            val left = translateFormula(f.mformula_1)
            val right = translateFormula(f.mformula_2)
            MITL.Conjunction(
              MITL.Implication(left, right),
              MITL.Implication(right, left))
          case f: MFBase => translateFormula(f.mformula_)
          case f: MFImpl =>
            val left = translateFormula(f.mformula_1)
            val right = translateFormula(f.mformula_2)
            MITL.Implication(left, right)
          case f: MFOr =>
            val left = translateFormula(f.mformula_1)
            val right = translateFormula(f.mformula_2)
            MITL.Disjunction(left, right)
          case f: MFUntil =>
            val rank = maybeTranslateRankId(f.optrank_)
            val interval = maybeTranslateInterval(f.optinterval_)
            val left = translateFormula(f.mformula_1)
            val right = translateFormula(f.mformula_2)
            MITL.U(interval, left, right, rank)
          case f: MFSince =>
            val rank = maybeTranslateRankId(f.optrank_)
            val interval = maybeTranslateInterval(f.optinterval_)
            val left = translateFormula(f.mformula_1)
            val right = translateFormula(f.mformula_2)
            MITL.S(interval, left, right, rank)
          case f: MFAnd =>
            val left = translateFormula(f.mformula_1)
            val right = translateFormula(f.mformula_2)
            MITL.Conjunction(left, right)
          case f: MFNot =>
            val formula = translateFormula(f.mformula_)
            MITL.Negation(formula)
          case f: MFEventually =>
            val rank = maybeTranslateRankId(f.optrank_)
            val interval = maybeTranslateInterval(f.optinterval_)
            val formula = translateFormula(f.mformula_)
            MITL.Diamond(interval, formula, rank)
          case f: MFGlobally =>
            val rank = maybeTranslateRankId(f.optrank_)
            val interval = maybeTranslateInterval(f.optinterval_)
            val formula = translateFormula(f.mformula_)
            MITL.Box(interval, formula, rank)
          case f: MFHistorically =>
            val rank = maybeTranslateRankId(f.optrank_)
            val interval = maybeTranslateInterval(f.optinterval_)
            val formula = translateFormula(f.mformula_)
            MITL.PBox(interval, formula, rank)
          case f: MFOnce =>
            val rank = maybeTranslateRankId(f.optrank_)
            val interval = maybeTranslateInterval(f.optinterval_)
            val formula = translateFormula(f.mformula_)
            MITL.PDiamond(interval, formula, rank)
          case f: UnOpBase => translateFormula(f.mformula_)
          case f: MFAtom => {
            val ap = translateAtom(f.matom_)(_)
            val signal_var = get_fresh_signal_var()
            apMap += ((signal_var, ap))
            MITL.AP(signal_var)
          }
          case f: FPar => translateFormula(f.mformula_)
        }
      }

      def maybeTranslateRankId(optRank: OptRank) : Option[Int] = {
        optRank match {
          case _: NoRank => None
          case r: WithRank => Some(r.integer_) 
        }
      }

      def maybeTranslateInterval(optInterval: OptInterval): MITL.Interval = {
        def translateInterval(interval: MInterval): MITL.Interval = {
          interval match {
            case i: RightOpenInterval =>
              val left =  translateIntBound(i.mitlbound_1)
              val right = translateBound(i.mitlbound_2)
              MITL.ClosedOpen(left, right)
            case i: OpenInterval =>
              val left =  translateBound(i.mitlbound_1)
              val right = translateBound(i.mitlbound_2)
              MITL.OpenOpen(left, right)
            case i: ClosedInterval =>
              val left =  translateIntBound(i.mitlbound_1)
              val right = translateIntBound(i.mitlbound_2)
              MITL.ClosedClosed(left, right)
            case i: LeftOpenInterval =>
              val left =  translateBound(i.mitlbound_1)
              val right = translateIntBound(i.mitlbound_2)
              MITL.OpenClosed(left, right)
          }
        }

        optInterval match {
          case _: NoInterval => MITL.ClosedOpen(0, MITL.PosInfty)
          case i: WithInterval => translateInterval(i.minterval_)
        }
      }

      def translateIntBound(bound: MitlBound): Int = {
        bound match {
          case b: MitlBoundInt => b.integer_
          case _ => ???
        }
      }

      def translateBound(bound: MitlBound): MITL.EInt = {
        bound match {
          case b: MitlBoundInt => translateIntBound(b)
          case b: MitlBoundInfty => MITL.PosInfty
        }
      }

      def translateExpr(expr: MExpr)(terms: Seq[ITerm]): ITerm = {
        expr match {
          case e: MEAdd => 
            translateExpr(e.mexpr_1)(terms) + translateExpr(e.mexpr_2)(terms)
          case e: MESub => translateExpr(e.mexpr_1)(terms) - translateExpr(e.mexpr_2)(terms)
          // multiplication with variables not allowed in presburger arithmetic
          case e: MEMul =>
            Console.err.println("Multiplication not supported for now.")
            i(Sort.Integer.newConstant("InvalidMul"))
          case e: MEDiv =>
            Console.err.println("Division not supported.")
            i(Sort.Integer.newConstant("InvalidDiv"))
          case e: MEVar =>
            terms(varToIndex(e.id_))
            // varTermsMap.getOrElse(e.id_, 
            //   i(Sort.Integer.newConstant(e.id_)) // TODO: Maybe should throw error instead?
            // )
          case e: MEInt => i(e.integer_)
          case e: MEParen => translateExpr(e.mexpr_)(terms)
        }
      }
      def translateAtom(atom: MAtom)(terms: Seq[ITerm]): IFormula = {
        atom match {
          case a: AtomRel =>
            println(a)
            val left = translateExpr(a.mexpr_1)(terms)
            val right = translateExpr(a.mexpr_2)(terms)


            a.mrelop_ match {
              case _: MRelLt => left < right
              case _: MRelLe => left <= right
              case _: MRelGt => left > right
              case _: MRelGe => left >= right
              case _: MRelEq => left === right
              case _: MRelNeq => left =/= right
            }
        }
      }
  }
  // def apply(str : String, varTerms: Seq[ITerm] = Seq.empty) = {
  //   //parses either a mitl or a ranking function
  //     apply(Seq(str), varTerms)
  // }
  
  def apply(strs : Seq[String], varTerms: Seq[ITerm] = Seq.empty) : MITLContext = {
    val mconv = new MitlConverter(varTerms)
    mconv.parseMany(strs)
    // strs.map{s => 
    //   parse(s) match {
    //     case _ => ???
    //   }
    // }
  }
}