package l
import syntax.universe._
import syntax.universe.vars._
import Statics._
import l.{ Dynamics => d }
import Problems._
import scala.language.implicitConversions
import pretty._
object Tests extends App {

  def test(expression: Expression, input: CodeType, expected: Either[(ValueType, Val), List[Problem]]) {
    val (found) = try {
      val foundtype = typecheck(Context(Map.empty, Map.empty), expression, evaluate(input))
      val foundvalue = d.evaluate(expression)
      Left(foundtype, foundvalue)
    } catch {
      case e: Throwable => Right(e)
    }
    val correct = (found, expected) match {
      case (Left((t1, v1)), Left((t2, v2))) => t1 == t2 && d.sameValue(v1, v2)
      case (Right(e: TypeException), Right(ps2)) if e.problems.sameElements(ps2) => true
      case _ =>
        found.right.foreach(_.printStackTrace)
        false
    }
    if (!correct) {
      println()
      println("!!! Test Case Failed !!!")
      println("Expression    = " + expression);
      println("Input         = " + input)
      println("Expected      = " + expected)
      println("Found         = " + found)
    } else {
      println(expression + " => " + found)
    }

  }
  def testGood(expression: Expression, expected: ValueType, value: Val, result: CodeType) {
    test(expression, result, Left(expected, value))
  }
  def testGood(expression: Expression, expected: ValueType, value: Val) {
    test(expression, expected, Left(expected, value))
  }
  def testBad(expression: Expression, result: CodeType, problems: Problem*) {
    test(expression, result, Right(problems.toList))
  }
  
  val x = newvar[Val]("x")
  var t = newvar[ValueType]("t")
  val h = newvar[Val]("h")
  val double = λ(x, nat, Fold(Z, h, S(S(h)), x))
  testBad(λ(x, x), ?, InferenceProblem(List(x.tag), true))
  testGood(λ(x, x), * -> *, λ(x, x))
  testGood(λ(x, nat, x), nat -> nat, λ(x, x))
  testGood(double(Num(3)), nat, Num(6), ?)
}