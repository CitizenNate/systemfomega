package l
import Syntax._
import Syntax.binding._
import Statics.typecheck
import Statics.Context
import Statics.valueToPartial
import Dynamics._
import Problems._
object Tests extends App{

  def test(expression: Expression, input: PartialType, expected: Either[(ValueType, Value), List[Problem]]) {
    val (found) = try {
      val foundtype = typecheck(Context(Map.empty, Map.empty, Map.empty), expression, input)
      val foundvalue = evaluate(expression)
      Left(foundtype, foundvalue)
    } catch {
      case e: Throwable => Right(e)
    }
    val correct = (found, expected) match {
      case (Left((t1, v1)), Left((t2, v2))) => t1 == t2 && sameValue(v1, v2)
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
    }else{
      println(expression +" => "+found)
    }

  }
  def testGood(expression: Expression, expected: ValueType, value: Value, result: PartialType = null) {
    val _result: PartialType = if (result == null) expected else result
    test(expression, _result, Left(expected, value))
  }
  def testBad(expression: Expression, result: PartialType, problems: Problem*) {
    test(expression, result, Right(problems.toList))
  }
  val x = newvar[Value]
  var t = newvar[CodeType]
  val h = newvar[Value]
  val nat = Nat
  val double = λ(nat, x, Fold(Zero, h, Succ(Succ(h)), x))
  testBad(λ(x, x), ?, InferenceProblem(List(x), true))
  testGood(λ(x, x), * -> *, λ(x, x))
  testGood(λ(nat, x, x), nat -> nat, λ(x, x))
  testGood(double(Num(3)), nat, Num(6))
}