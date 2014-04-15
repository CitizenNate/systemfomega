package l
import syntax.universe._
import scala.language.implicitConversions
import scala.language.existentials
object Problems {
  sealed trait Problem

  //indicates that there is an actual type error in the code,
  // i.e. there is no way to give the expression a type
  case class TypeProblem(found: PartialType, require: PartialType) extends Problem

  //Indicates that the type inference is too weak to typecheck
  //the code, and that the user must add a type annotation to
  //one of several listed variables, or perform downward typechecking of
  //the given expression, instead of synthesis.
  case class InferenceProblem(vars: List[Tag], orCheck: Boolean) extends Problem

  //indicates that the code contains a variable that was never declared
  case class BindingProblem(variable: Tag) extends Problem

  //indicates that the kinds of the two types did not match
  case class KindProblem(found: Kind, require: Kind) extends Problem

  class TypeException(val problems: List[Problem], cause: TypeException) extends Exception(cause) {
    def amend(v: Tag, cont: Boolean): Nothing = {
      throw new TypeException(problems.map({
        case InferenceProblem(vs, true) =>
          InferenceProblem(v :: vs, cont)
        case x => x
      }), this)
    }
    def append(p: Problem): Nothing = {
      throw new TypeException(p :: problems, this)
    }
    override def toString = problems.toString
  }
  /**
   * execute x, and if there is a problem, amend all inferences failures
   */
  def amend[T](v: Tag, cont: Boolean)(x: => T): T = {
    try {
      x
    } catch {
      case e: TypeException => e.amend(v, cont)
    }
  }
  /**
   * execute x, and if there is a problem, include this problem as well
   */
  def append[T](p: Problem)(x: => T): T = {
    try {
      x
    } catch {
      case e: TypeException => e.append(p)
    }
  }

  implicit def throwHelper(x: Problem): TypeException = {
    new TypeException(List(x), null)
  }

  def inferenceProblem =
    throw new InferenceProblem(Nil, true)

  def inferenceProblem(binds: Tag) =
    throw InferenceProblem(List(binds), true)

  def typeProblem(found: PartialType, require: PartialType) =
    throw TypeProblem(found, require)

  def kindProblem(found: Kind, require: Kind) =
    throw KindProblem(found, require)

  def bindingProblem(v: Tag) =
    throw BindingProblem(v)

}