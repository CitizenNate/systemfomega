package l
import Syntax._
import Syntax.binding._
object Dynamics {
  def evaluate(expr: Expression): Value = {
    expr match {
      case Triv => Triv
      case ApplyE(a, b) =>
        val LambdaE(_, x, body) = evaluate(a)
        evaluate(body.sub(x -> evaluate(b)))
      case ApplyET(a, b) =>
        val LambdaTE(_, _, body) = evaluate(a)
        evaluate(body)
      case Fold(base, hypo, step, num) =>
        val Num(n) = evaluate(num)
        var ret: Value = evaluate(base)
        for (i <- 0 until n) {
          ret = evaluate(step.sub(hypo -> ret))
        }
        ret
      case expr: LambdaE => expr
      case expr: LambdaTE => expr
      case num: Num => num
      case Zero => Num(0)
      case Succ(expr) =>
        val Num(n) = evaluate(expr)
        Num(n + 1)
      case _: VarE => ???
    }
  }
  def sameExpression(context: Map[Var[Value], Var[Value]], x: Expression, y: Expression): Boolean = {
    (x, y) match {
      case (Num(x), Num(y)) => x == y
      case (Triv, Triv) => true
      case (LambdaE(_, x1, b1), LambdaE(_, x2, b2)) =>
        sameExpression(context + (x1 -> x2), b1, b2)
      case (LambdaTE(_, _, b1), LambdaTE(_, _, b2)) =>
        sameExpression(context, b1, b2)
      case (ApplyE(x1, x2), ApplyE(y1, y2)) =>
        sameExpression(context, x1, y1) && sameExpression(context, x2, y2)
      case (VarE(x), VarE(y)) =>
        context(x) == y
      case (ApplyET(x, _), ApplyET(y, _)) =>
        sameExpression(context, x, y)
      case (Fold(x1, x2, x3, x4), Fold(y1, y2, y3, y4)) =>
        sameExpression(context, x1, y1) &&
          sameExpression(context + (x2 -> y2), x3, y3) &&
          sameExpression(context, x4, y4)
      case (Zero, Zero) => true
      case (Succ(x), Succ(y)) => sameExpression(context, x, y)
      case _ => false
    }
  }
  def sameValue(x: Value, y: Value): Boolean = {
    sameExpression(Map.empty, x, y)
  }
}