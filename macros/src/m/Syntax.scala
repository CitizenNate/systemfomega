package m
import scala.reflect._
import scala.reflect.runtime.universe._
import java.io.PrintWriter
import scala.reflect.runtime.universe
object SyntaxSpec extends SyntaxBuilder {
  object SORTS extends Enumeration {
    val Expression, Val, CodeType, ExpressionType, PartialType, ValueType, Kind = Value
  }
  val SORT = SORTS
  import SORT._

  def subtyping = List(
    Val <:< Expression,
    Kind <:< ValueType,
    ValueType <:< ExpressionType,
    ValueType <:< PartialType,
    ExpressionType <:< CodeType,
    PartialType <:< CodeType)

  def forCodeType(f: Sort => Decl) = List(f(CodeType))
  def forPartialType(f: Sort => Decl) = List(f(CodeType), f(PartialType))
  def forExpressionType(f: Sort => Decl) = List(f(CodeType), f(ExpressionType))
  def forValueType(f: Sort => Decl) = List(f(CodeType), f(ExpressionType), f(PartialType), f(ValueType))
  def forKind(f: Sort => Decl) = f(Kind) :: forValueType(f)

  def forExpression(f: Sort => Decl) = f(Expression) :: Nil
  def forValue(f: Sort => Decl) = f(Val) :: forExpression(f)

  def Arrow(t: Sort) = NodeDecl(Nil, List(Finally("in" -> t), Finally("out" -> t)), t, "Arrow")
  def Apply(t: Sort) = NodeDecl(Nil, List(Finally("fun" -> t), Finally("arg" -> t)), t, "Apply")
  def PolyApply = NodeDecl(Nil, List(Finally("fun" -> Expression), Finally("arg" -> ExpressionType)), Expression, "PolyApply")
  def Triv(t: Sort) = NodeDecl(Nil, List(), t, "Triv")

  def Lambda(
    annot: Sort,
    valueType: Sort,
    expressionType: Sort,
    parentType: Sort, name: String = "Lambda", producer: Boolean = true) =
    NodeDecl(Nil, List(
      Finally("annot" -> annot),
      Bind("x" -> valueType,
        Finally("body" -> expressionType))),
      parentType,
      name, producer)

  def Forall(t: Sort) = NodeDecl(Nil, List(Finally("annot" -> Kind), Bind("x" -> ValueType, Finally("body" -> t))), t, "Forall")

  def Unknown(t: Sort) = NodeDecl(Nil, List(), t, "Unknown")

  def Nat(t: Sort) = NodeDecl(Nil, List(), t, "Nat")

  val Fold = NodeDecl(Nil, List(
    Finally("base" -> Expression),
    Bind("hypo" -> Val, Finally("step" -> Expression)),
    Finally("on" -> Expression)), Expression, "Fold")

  def Zero(t: Sort) = NodeDecl(Nil, Nil, t, "Zero")
  def Num(t: Sort, t2: Sort, producer: Boolean) = NodeDecl(List("n" -> "Int"), Nil, t2, "Num", producer)
  def Succ(t: Sort) = NodeDecl(Nil, List(Finally("pred" -> t)), t, "Succ")

  def decls =
    List(Unknown(PartialType),
      VarDecl(Val, Val),
      VarDecl(Val, Expression, false),
      VarDecl(ValueType, ExpressionType, false),
      VarDecl(ValueType, ValueType),
      VarDecl(ValueType, CodeType, false),
      VarDecl(ValueType, PartialType, false),
      Lambda(CodeType, Val, Expression, Val),
      Lambda(CodeType, Val, Expression, Expression, producer = false),
      Lambda(Kind, ValueType, Expression, Val, "PolyLambda"),
      Lambda(Kind, ValueType, Expression, Expression, "PolyLambda", false),
      Lambda(Kind, ValueType, ExpressionType, ValueType),
      Lambda(Kind, ValueType, CodeType, PartialType),
      Lambda(Kind, ValueType, ExpressionType, ExpressionType, producer = false),
      Lambda(Kind, ValueType, CodeType, CodeType, producer = false),
      PolyApply,
      Unknown(PartialType),
      Nat(ValueType),
      Triv(Kind),
      Triv(Val),
      Num(Val, Expression, false),
      Num(Val, Val, true),
      Zero(Val),
      Fold) ::: (List(
        forValue(Succ),
        forValueType(Forall),
        forKind(Arrow),
        forExpression(Apply),
        forExpressionType(Apply)).flatten)
  this.print(new PrintWriter("../main/generated/g/Syntax.scala", "UTF-8"))
}




