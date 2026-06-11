package hornconcurrency

import java.io.StringReader

import hornconcurrency.mitl.Yylex
import hornconcurrency.mitl.parser
import hornconcurrency.mitl.Absyn._
import hornconcurrency.MITL
import ap.parser._
import ap.parser.IExpression._

import hornconcurrency.MITLContext._

object MitlParserTest extends App {

  


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
      val mc = MITLContext(inputs ++ ranking_inputs)
      println("mitl formulas:")
      mc.mitls.foreach(println)
      println("\nRanking functions")
      mc.ranks.foreach(println)
      println("\nMap signal vars to APs")
      mc.apMap.map{case (k,v) => println("signal_var: " + k + ", AP: "+ v)}
      // (inputs ++ ranking_inputs).foreach{case x =>
      //   println(s"Parsing input:\n$x\n")

      //   val mitl_ast = MitlContext(ast)
      //   println("Translated " + x + " into mitl-context:")
      //   println(mitl_ast)

      //   println("✅ Parsing succeeded!")
      //   println("AST:")
      //   println(ast)

      //   // Optional: pretty print
      //   println("\nPretty print:")
      //   println(mitl.PrettyPrinter.print(ast))
      // }
    } catch {
      case e: Throwable =>
        println("❌ Parsing failed:")
        e.printStackTrace()
    }
}
