package l

import scala.language.higherKinds
import scala.language.implicitConversions
/**
 * the syntax of this language, providing the following types:
 *
 * Expression
 * 		An expression or declaration inside the code.
 *
 * Value
 * 		An expression which has been completed evaluated.
 *
 * KindType
 * 		A type of a type.
 *
 * ValueType
 * 		A fully known and evaluated type.
 *
 * PartialType
 * 		A fully evaluated type.
 *
 * CodeType
 * 		A type. When a type occurs inside the code, it is of this general form.
 *
 * The types have the following subtyping structure:
 * 	   KindType is a subtype of ValueType, PartialType, and CodeType
 *     PartialType is a subtype of CodeType
 *
 * The critical detail here is the fact that ValueType is not a subtype of PartialType.
 * The reasoning is that such a subtyping would allow the following code to compile:
 *
 * val x = newvar[ValueType]
 * val xvar :ValueType = Var(x)
 * val value : ValueType = λ(*,x,*)
 * val partial : PartialType = value
 * val Lambda(_,y,_) = partial
 * //note that y is of type Var[PartialType]
 * val evil : ValueType = xvar.sub(y -> Unknown)
 *
 * note that evil is now the value Unknown, and is of type ValueType, which contradicts
 * the entire purpose of segregating ValueType and PartialType in the first place.
 *
 */
object Syntax {
  val binding: Binding = new StringBinding()
  import binding._

  //--------------------SORT DEFINITIONS--------------------------
  sealed trait KindSort

  sealed trait ValueTypeSort extends KindSort
  sealed trait PartialTypeSort extends KindSort
  sealed trait CodeTypeSort extends PartialTypeSort

  // types
  sealed abstract class TypeTerm[-T <: KindSort](override val toString: String) extends Product

  //fully qualified types
  type ValueType = TypeTerm[ValueTypeSort]

  //partially known types
  type PartialType = TypeTerm[PartialTypeSort]

  //unevaluated types
  type CodeType = TypeTerm[CodeTypeSort]

  // types of types
  type Kind = TypeTerm[KindSort]

  sealed abstract class Expression(override val toString: String) extends Product {
    def apply(x: Expression) = ApplyE(this, x)
  }
  sealed abstract class Value(toString: String) extends Expression(toString)

  //---------------------------- OBJECTS -------------------------------------
  case class Arrow[T <: KindSort](in: TypeTerm[T], out: TypeTerm[T]) extends TypeTerm[T](s"$in ⟶ $out")
  case object Nat extends TypeTerm[KindSort]("nat")

  case class ForallV(annot: Kind, v: Bind[ValueType], e: ValueType) extends ValueType(s"∀ $v : $annot . $e")
  case class ForallP(annot: Kind, v: Bind[PartialType], e: PartialType) extends PartialType(s"∀ $v : $annot . $e")

  case class LambdaV(annot: Kind, v: Bind[ValueType], e: ValueType) extends ValueType(s"λ $v : $annot . $e")
  case class LambdaP(annot: Kind, v: Bind[PartialType], e: PartialType) extends PartialType(s"λ $v : $annot . $e")
  case class LambdaE(annot: CodeType, v: Bind[Value], e: Expression) extends Value(s"(λ $v : $annot . $e)")
  case class LambdaTE(annot: Kind, v: Bind[PartialType], e: Expression) extends Value(s"Λ $v : $annot . $e")

  case class ApplyE(e1: Expression, e2: Expression) extends Expression(s"$e1 $e2")
  case class ApplyET(e1: Expression, t2: PartialType) extends Expression(s"$e1 $t2")
  case class ApplyC(t1: CodeType, t2: CodeType) extends CodeType(s"$t1 $t2")

  case class VarV(v: Var[ValueType]) extends ValueType(v.toString)
  case class VarP(v: Var[PartialType]) extends PartialType(v.toString)
  case class VarE(v: Var[Value]) extends Expression(v.toString)

  case object Unknown extends PartialType("?")
  case object Unit extends TypeTerm[KindSort]("*")
  case object Triv extends Value("()")
  case object Zero extends Expression("0")
  case class Succ(e: Expression) extends Expression(s"S $e")
  case class Num(n: Int) extends Value(n.toString)

  case class Fold(base: Expression, hypo: Bind[Value], step: Expression, num: Expression)
    extends Expression(s"(fold $base ($hypo => $step) $num)")

  type Gamma = Map[Var[Expression], ValueType]
  type Omega = Map[Var[PartialType], Kind]
  type Delta = Map[Var[PartialType], Var[ValueType]]
  //----------------------------- DECLARATION HELPERS ------------------------------
  val <> : Expression = Triv
  val * : ValueType = Unit
  val ? : PartialType = Unknown
  def λ(annot: PartialType, variable: Bind[Value], body: Expression) = LambdaE(annot, variable, body)
  def λ(variable: Bind[Value], body: Expression): Value = LambdaE(?, variable, body)
  def Λ(annot: Kind, variable: Bind[PartialType], body: Expression) = LambdaTE(annot, variable, body)
  def λ(annot: Kind, variable: Bind[PartialType], body: PartialType) = LambdaP(annot, variable, body)

  implicit def pairToArrow1[T <: KindSort](x: (TypeTerm[T], TypeTerm[T])): TypeTerm[T] = Arrow(x._1, x._2)
  implicit def varToExpr(v: Var[Value]): Expression = VarE(v)
  implicit def varToPartialType(v: Var[PartialType]): PartialType = VarP(v)
  implicit def varToValueType(v: Var[ValueType]): ValueType = VarV(v)
  
  
}