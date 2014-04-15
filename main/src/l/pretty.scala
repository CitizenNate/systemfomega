package l
import syntax.universe._
import syntax.universe.vars._
import scala.language.implicitConversions

object pretty {
  implicit class CodeTypeHelper(x: CodeType) {
    def apply(y: CodeType) = Apply(x, y)
  }
  implicit class ExpressionHelper2(x: Expression) {
    def apply(y: Expression) = Apply(x, y)
  }

  implicit def pairToArrow1(x: (CodeType, CodeType)) = Arrow(x._1, x._2)
  implicit def pairToArrow2(x: (ExpressionType, ExpressionType)) = Arrow(x._1, x._2)
  implicit def pairToArrow3(x: (ValueType, ValueType)) = Arrow(x._1, x._2)
  implicit def valVarToVal(x: Var[Val]): Expression = VarTerm(x)

  def λt(variable: Var[ValueType], annot: Kind, body: CodeType): PartialType = Lambda(annot, variable, body)
  def λ(variable: Var[Val], annot: CodeType, body: Expression): Val = Lambda(annot, variable, body)
  
  def λ(variable: Var[Val], body: Expression): Val = Lambda(Unknown(), variable, body)
  def Λ(variable: Var[ValueType], annot: Kind, body: Expression): Val = PolyLambda(annot, variable, body)
  def ∀(variable: Var[ValueType], annot: Kind, body: CodeType): CodeType = Forall(annot, variable, body)

  val * : ValueType = Triv()
  val <> : Expression = Triv()
  val ? : PartialType = Unknown()
  val nat: ValueType = Nat()
  val Z: Expression = Zero()
  def S(pred: Expression): Expression = Succ(pred)
}