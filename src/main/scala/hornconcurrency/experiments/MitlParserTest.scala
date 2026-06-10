package hornconcurrency

import java.io.StringReader

import hornconcurrency.mitl.Yylex
import hornconcurrency.mitl.parser
import hornconcurrency.mitl.Absyn._
import hornconcurrency.MITL
import ap.parser._
import ap.parser.IExpression._

object MitlParserTest extends App {

  def translate(ast: MitlDecl): MITL = {
    def translateFormula(formula: Formula): MITL = {
      formula match {
        case f: FIff =>
          val left = translateFormula(f.formula_1)
          val right = translateFormula(f.formula_2)
          MITL.Conjunction(
            MITL.Implication(left, right),
            MITL.Implication(right, left))
        case f: FBase => translateFormula(f.formula_)
        case f: FImpl =>
          val left = translateFormula(f.formula_1)
          val right = translateFormula(f.formula_2)
          MITL.Implication(left, right)
        case f: FOr =>
          val left = translateFormula(f.formula_1)
          val right = translateFormula(f.formula_2)
          MITL.Disjunction(left, right)
        case f: FUntil =>
          val interval = maybeTranslateInterval(f.optinterval_)
          val left = translateFormula(f.formula_1)
          val right = translateFormula(f.formula_2)
          MITL.U(interval, left, right)
        case f: FSince =>
          val interval = maybeTranslateInterval(f.optinterval_)
          val left = translateFormula(f.formula_1)
          val right = translateFormula(f.formula_2)
          MITL.S(interval, left, right)
        case f: FAnd =>
          val left = translateFormula(f.formula_1)
          val right = translateFormula(f.formula_2)
          MITL.Conjunction(left, right)
        case f: FNot =>
          val formula = translateFormula(f.formula_)
          MITL.Negation(formula)
        case f: FEventually =>
          val interval = maybeTranslateInterval(f.optinterval_)
          val formula = translateFormula(f.formula_)
          MITL.Diamond(interval, formula)
        case f: FGlobally =>
          val interval = maybeTranslateInterval(f.optinterval_)
          val formula = translateFormula(f.formula_)
          MITL.Box(interval, formula)
        case f: FHistorically =>
          val interval = maybeTranslateInterval(f.optinterval_)
          val formula = translateFormula(f.formula_)
          MITL.PBox(interval, formula)
        case f: FOnce =>
          val interval = maybeTranslateInterval(f.optinterval_)
          val formula = translateFormula(f.formula_)
          MITL.PDiamond(interval, formula)
        case f: UnOpBase => translateFormula(f.formula_)
        case f: FAtom => MITL.AP(translateAtom(f.atom_).toString())
        case f: FPar => translateFormula(f.formula_)
      }
    }

    def maybeTranslateInterval(optInterval: OptInterval): MITL.Interval = {
      def translateInterval(interval: Interval): MITL.Interval = {
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
        case i: WithInterval => translateInterval(i.interval_)
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

    def translateAtom(atom: Atom): IFormula = {
      def translateExpr(expr: Expr): ITerm = {
        expr match {
          case e: EAdd => translateExpr(e.expr_1) + translateExpr(e.expr_2)
          case e: ESub => translateExpr(e.expr_1) - translateExpr(e.expr_2)
          // multiplication with variables not allowed in presburger arithmetic
          case e: EMul =>
            Console.err.println("Multiplication not supported for now.")
            i(Sort.Integer.newConstant("InvalidMul"))
          case e: EDiv =>
            Console.err.println("Division not supported.")
            i(Sort.Integer.newConstant("InvalidDiv"))
          case e: EVar => i(Sort.Integer.newConstant(e.id_))
          case e: EInt => i(e.integer_)
          case e: EParen => translateExpr(e.expr_)
        }
      }

      atom match {
        case a: AtomRel =>
          println(a)
          val left = translateExpr(a.expr_1)
          val right = translateExpr(a.expr_2)


          a.relop_ match {
            case _: RelLt => left < right
            case _: RelLe => left <= right
            case _: RelGt => left > right
            case _: RelGe => left >= right
            case _: RelEq => left === right
            case _: RelNeq => left =/= right
          }
      }
    }

    ast match {
      case ranking: RankFunc => MITL.AP("Not Implemented")
      case formula: MitlFormula => translateFormula(formula.formula_)
      case _: MitlDecl => MITL.AP("Not Implemented")
    }
  }


  def parse(input: String): MitlDecl = {
    val reader = new StringReader(input)
    
    val lexer = new Yylex(reader)
    val parser = new parser(lexer, lexer.getSymbolFactory())

    val result = parser.pMitlDecl()   // entry point from BNFC
    result
  }


    val inputs =
Seq(
  """MITL_SPEC : F(2 < 3) ;""".stripMargin,
  """MITL_SPEC : G(5 >= 5) ;""".stripMargin,
  """MITL_SPEC : !(F(1 < 2)) ;""".stripMargin,
  """MITL_SPEC : F((1 + 2) < 4) ;""".stripMargin,
  """MITL_SPEC : G((10 - 3) > 2) ;""".stripMargin,
  """MITL_SPEC : F((2 * 3) == 6) ;""".stripMargin,
 
  // Boolean combinations
  """MITL_SPEC : F(1 < 2) && F(2 < 3) ;""".stripMargin,
  """MITL_SPEC : G(3 > 1) || F(4 <= 4) ;""".stripMargin,
  """MITL_SPEC : !(G(1 < 2) && F(3 > 4)) ;""".stripMargin,
  """MITL_SPEC : (F(1 < 2) ==> G(2 < 3)) ;""".stripMargin,
  """MITL_SPEC : (F(1 < 2) <=> F(2 < 3)) ;""".stripMargin,

  // Nested temporal operators
  """MITL_SPEC : F(G(1 < 2)) ;""".stripMargin,
  """MITL_SPEC : G(F(2 < 3)) ;""".stripMargin,
  """MITL_SPEC : F(G(F(1 < 2))) ;""".stripMargin,

  // Until / Since variants
  """MITL_SPEC : (F(1 < 2)) U (F(2 < 3)) ;""".stripMargin,
  """MITL_SPEC : (G(1 < 2)) S (F(3 > 1)) ;""".stripMargin,
  """MITL_SPEC : (F(1 < 2) U G(2 < 3)) && (G(3 > 4)) ;""".stripMargin,

  // Time-bounded operators
  """MITL_SPEC : F@(1,10)(2 < 5) ;""".stripMargin,
  """MITL_SPEC : G@[2,8](3 != 4) ;""".stripMargin,
  """MITL_SPEC : F@(0,5](1 < 2) ;""".stripMargin,
  """MITL_SPEC : G@(1,3)(2 <= 2) ;""".stripMargin,

  // Nested time bounds
  """MITL_SPEC : F@[0,5](G@[1,3](1 < 2)) ;""".stripMargin,
  """MITL_SPEC : G@[0,10)(F@[2,4](3 > 4)) ;""".stripMargin,
  """MITL_SPEC : F@(0,5](G@(1,4)(F@(0,2](1 < 2))) ;""".stripMargin,

  // Mixed arithmetic (“ranking-like” expressions)
  """MITL_SPEC : F((x + 1) < (y + 2)) ;""".stripMargin,
  """MITL_SPEC : G((rank1 - rank2) >= 0) ;""".stripMargin,
  """MITL_SPEC : F((score * 2) > (threshold + 1)) ;""".stripMargin,
  """MITL_SPEC : F((a * b) < (c - d)) ;""".stripMargin,

  // More complex composed formulas
  """MITL_SPEC : (F@[2,infty)(1 < 2) && G@[1,3](3 > 4)) ==> F(2 < 3) ;""".stripMargin,
  """MITL_SPEC : (F(1 < 2) || G(3 > 4)) U (F@[2,6](5 >= 3)) ;""".stripMargin,
  """MITL_SPEC : G@[0,infty)((F@[1,3](1 < 2)) ==> (G@[2,5](3 > 1))) ;""".stripMargin,

  // Deep nesting + intervals
  """MITL_SPEC : G@(0,5](F@[0,2](G@[1,3](1 < 2) U F(2 < 3)) && (G@[1,4](3 > 2))) ;""".stripMargin,
  // Simple ranked temporal operators
  """MITL_SPEC : {1}F(1 < 2) ;""".stripMargin,
  """MITL_SPEC : {2}G(3 > 4) ;""".stripMargin,

  // Ranked with intervals
  """MITL_SPEC : {1}F@[0,5](1 < 2) ;""".stripMargin,
  """MITL_SPEC : {2}G@[1,3](2 <= 2) ;""".stripMargin,
  """MITL_SPEC : {3}F@(0,5](3 > 1) ;""".stripMargin,

  // Ranked boolean combinations
  """MITL_SPEC : {1}F(1 < 2) && {2}G(3 > 4) ;""".stripMargin,
  """MITL_SPEC : {1}F(1 < 2) || {2}G(3 > 4) ;""".stripMargin,
  """MITL_SPEC : {1}F(1 < 2) ==> {2}G(3 > 4) ;""".stripMargin,
  """MITL_SPEC : {1}F(1 < 2) <=> {2}G(3 > 4) ;""".stripMargin,

  // Ranked Until / Since
  """MITL_SPEC : {1}F(1 < 2) U {2}G(3 > 4) ;""".stripMargin,
  """MITL_SPEC : {2}G(3 > 4) S {1}F(1 < 2) ;""".stripMargin,
  """MITL_SPEC : ({1}F(1 < 2)) U ({2}F(2 < 3)) ;""".stripMargin,

  // Mixed ranked + unranked
  """MITL_SPEC : {1}F(1 < 2) && G(2 < 3) ;""".stripMargin,
  """MITL_SPEC : F(1 < 2) || {2}G(3 > 4) ;""".stripMargin,

  // Nested ranked temporal operators
  """MITL_SPEC : {1}F({2}G(1 < 2)) ;""".stripMargin,
  """MITL_SPEC : {2}G({1}F(2 < 3)) ;""".stripMargin,
  """MITL_SPEC : {3}F({2}G({1}F(1 < 2))) ;""".stripMargin,

  // Ranked with arithmetic (ranking-style expressions inside predicates)
  """MITL_SPEC : {1}F((x + 1) < (y + 2)) ;""".stripMargin,
  """MITL_SPEC : {2}G((rank1 - rank2) >= 0) ;""".stripMargin,
  """MITL_SPEC : {3}F((score * 2) > threshold) ;""".stripMargin,

  // Ranked + intervals + nesting
  """MITL_SPEC : {1}F@(0,5]({2}G@[1,3](1 < 2)) ;""".stripMargin,
  """MITL_SPEC : {2}G@[0,4]({1}F@(1,2](2 < 3)) ;""".stripMargin,

  // Complex compositions
  """MITL_SPEC : ({1}F(1 < 2) && {2}G(2 < 3)) ==> {3}F(3 < 4) ;""".stripMargin,
  """MITL_SPEC : ({1}F(1 < 2) || {2}G(3 > 4)) U ({3}F(2 < 5)) ;""".stripMargin,

  // Deep nesting with multiple ranks
  """MITL_SPEC : {1}F({2}G({3}F(1 < 2) U {4}G(2 < 3))) ;""".stripMargin,
  """MITL_SPEC : {4}G({3}F({2}G({1}F(1 < 2)))) ;""".stripMargin,

  // Mixed ranked operators across Until
  """MITL_SPEC : ({1}F@[0,5](1 < 2)) U ({2}G@[1,4](3 > 4)) ;""".stripMargin,
  """MITL_SPEC : ({3}G@(0,5]({1}F(1 < 2))) S ({2}F@[0,3](2 < 3)) ;""".stripMargin
)

val ranking_inputs = Seq(
  """RANKING_FUNCTION 1: x + 1;""".stripMargin,
  """RANKING_FUNCTION 2: rank1 - rank2;""".stripMargin,
  """RANKING_FUNCTION 3: score * 2;""".stripMargin,
  """RANKING_FUNCTION 4: a * b + 42;""".stripMargin,
  """RANKING_FUNCTION 5: (1337 * y) - (z + 1) / 44;""".stripMargin 
)

    try {
      (inputs ++ ranking_inputs).foreach{case x =>
        println(s"Parsing input:\n$x\n")
        val ast = parse(x)

        val mitl_ast = translate(ast)
        println("Translated " + x + " into " + mitl_ast)

        println("✅ Parsing succeeded!")
        println("AST:")
        println(ast)

        // Optional: pretty print
        println("\nPretty print:")
        println(mitl.PrettyPrinter.print(ast))
      }
    } catch {
      case e: Throwable =>
        println("❌ Parsing failed:")
        e.printStackTrace()
    }
}
