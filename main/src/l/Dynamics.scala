package l
import syntax.universe._
import syntax.universe.vars._

object Dynamics {
  def evaluate(expr: Expression): Val = {
    expr match {
      case Triv => Triv()
      case Apply(a, b) =>
        val Lambda(_, x, body) = evaluate(a)
        evaluate(body.sub(x -> evaluate(b)))
      case Apply(a, b) =>
        val Lambda(_, _, body) = evaluate(a)
        evaluate(body)
      case Fold(base, hypo, step, num) =>
        val Num(n) = evaluate(num)
        var ret: Val = evaluate(base)
        for (i <- 0 until n) {
          ret = evaluate(step.sub(hypo -> ret))
        }
        ret
      case Lambda(a, b, c) => Lambda(a, b, c)
      case PolyLambda(a, b, c) => PolyLambda(a,b,c)
      case Num(n) => Num(n)
      case Zero => Num(0)
      case Succ(expr) =>
        val Num(n) = evaluate(expr)
        Num(n + 1)
      case VarTerm(x) => ???
    }
  }
  def sameExpression(context: Map[Var[Val], Var[Val]], x: Expression, y: Expression): Boolean = {
    (x, y) match {
      case (Num(x), Num(y)) => x == y
      case (Triv, Triv) => true
      case (Lambda(_, x1, b1), Lambda(_, x2, b2)) =>
        sameExpression(context + (x1 -> x2), b1, b2)
      case (PolyLambda(_, _, b1), PolyLambda(_, _, b2)) =>
        sameExpression(context, b1, b2)
      case (Apply(x1, x2), Apply(y1, y2)) =>
        sameExpression(context, x1, y1) && sameExpression(context, x2, y2)
      case (VarTerm(x), VarTerm(y)) =>
        context(x) == y
      case (PolyApply(x, _), PolyApply(y, _)) =>
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
  def sameValue(x: Val, y: Val): Boolean = {
    sameExpression(Map.empty, x, y)
  }
}