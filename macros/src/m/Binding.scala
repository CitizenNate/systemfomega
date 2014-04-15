package m
import scala.language.implicitConversions

import scala.language.higherKinds
/*import scala.language.experimental.macros
import scala.reflect.macros.Context
import scala.language.reflectiveCalls
import scala.annotation.StaticAnnotation

class Binding extends StaticAnnotation {
  def macroTransform(classes: Any): Any = macro Binding.buildNodesMacro
}
object Binding {

  trait Bind[B, T]
  trait Var[T]
  def buildNodesMacro(c: Context)(classes: c.Expr[Any]): c.Expr[Any] = {
    import c._
    import c.mirror.universe._

    val anyType = c.mirror.universe.typeTag[Any].tpe
    //val TypeApply(TypeRef(bindTypePrefix, bindTypeSymbol, _), _) = 

    sealed trait Decl

    case class Group(name: c.TypeName, parents: List[c.Tree]) extends Decl

    sealed trait Part
    case class Bind(bind: c.Tree, next: Part) extends Part
    case class Then(next: c.Tree) extends Part

    case class CaseClass(name: Name, parts: List[(TermName, Part)], extend: Tree) extends Decl
    case class CaseObject(name: Name, extend: c.Type) extends Decl
    def log(x: Any) = {
      c.info(classes.tree.pos, x.toString, false)
    }
    def logClass(x: Any) = {
      x match {
        case x: Product =>
          log(x.productPrefix + "(" + x.productIterator.toList.map(_.getClass) + ")")
        case x => log(x.getClass)
      }
    }
    val Block(List(ClassDef(_, traitSym, _, Template(_, _, x))), _) = classes.tree
    def localize(x: Type): Tree = {
      x match {
        case TypeRef(prefix, sym, params) =>

          val symPath: String = sym.fullName
          val traitPath: String = c.enclosingClass.symbol.fullName + "." + traitSym.encoded

          if (symPath.startsWith(traitPath)) {
            Ident(sym.name)
          } else {
            TypeTree(x)
          }
      }
    }
    def toPart(x: Type): Part = {
      x match {
        case TypeRef(prefix, sym, List(vartype, bodytype)) if (sym.fullName == "m.Binding.Bind") =>

          Bind(localize(vartype), toPart(bodytype))
        case _ =>
          Then(localize(x))

      }
    }

    val decls = for (elem <- x) yield {
      elem match {
        case TypeDef(_, x, _, y) =>

          val z = y.asInstanceOf[TypeTree].tpe match {
            case TypeBounds(_, RefinedType(y, _)) => y
            case TypeBounds(_, y) => List(y)
          }
          val w = z.filterNot(_ =:= anyType).map(localize(_))
          Group(x, w)

        case DefDef(_, x, _, List(y), z, _) =>
          val y2 = y.map {
            case ValDef(_, name, typeTree, _) =>
              (name, toPart(typeTree.tpe))
          }
          CaseClass(x, y2, localize(z.tpe))

        case DefDef(_, x, _, Nil, z, _) =>
          CaseObject(x, z.tpe)
      }
    }
    c.intr
  }
  def buildNodes(classes: Any): Any = macro buildNodesMacro
}*/
trait TagApi[Tag] {
  val tag: Tag
}
abstract class Viewer {
  trait TermApi[+A >: Bottom <: Top] {
    def sub[B >: Bottom <: Top](b: (Var[B], B)): A
  }
  type Var[T] <: TagApi[Tag]
  type Tag
  type Top <: TermApi[Top]
  type Bottom <: Top with TermApi[Bottom]
  type Term = Top
  def substitute[A >: Bottom <: Top, B >: Bottom <: Top](what: B, variable: Var[B], in: A): A
  val vars: Variable[Tag, Var]
}
abstract class AbstractViewer extends Viewer {
  sealed trait Leaf[+F <: Var[_]]
  case class FreeLeaf[+F <: Var[_]](x: F) extends Leaf[F]
  case class BoundLeaf[+F <: Var[_]](x: Int) extends Leaf[F]

  sealed trait View[T <: Top]
  case class NodeView[T <: Top](tag: (Any, List[(List[Tag], Top)]) => T, constant: Any, children: List[(List[Tag], Top)]) extends View[T]
  case class LeafView[T <: Top](x: Leaf[Var[T]]) extends View[T]

  protected def show[T >: Bottom <: Top](x: T): View[T]
  protected def hide[T >: Bottom <: Top](x: View[T]): T
  def bind[V >: Bottom <: Top, C >: Bottom <: Top](find: Var[V], x: C, replace: Int): C = {
    hide[C](show[C](x) match {
      case node @ NodeView(tag, constant, children) =>
        NodeView(tag, constant, children.map({
          case (tags, y) => (tags, bind(find, y, replace + tags.size))
        }))
      case LeafView(FreeLeaf(`find`)) => LeafView(BoundLeaf(replace))
      case v @ LeafView(FreeLeaf(_)) => v
      case LeafView(BoundLeaf(n)) => LeafView(BoundLeaf(n))
    })
  }
  def unbind[C >: Bottom <: Top](x: C, v: Var[_ >: Bottom <: Top]): C = {
    hide[C]((show[C](x) match {
      case NodeView(tag, constant, children) =>
        NodeView(tag, constant, children.map({
          case (Nil, y) => (Nil, unbind(y, v))
          case (tags, y) => (tags, y)
        }))
      case v @ LeafView(FreeLeaf(_)) => v
      case LeafView(BoundLeaf(0)) => LeafView(FreeLeaf(v))
      case LeafView(BoundLeaf(n)) => LeafView(BoundLeaf(n))
    }).asInstanceOf[View[C]])
  }
  def unbindMultiple[C >: Bottom <: Top](x: (List[Tag], C)): (List[Var[_ >: Bottom <: Top]], C) = {
    x match {
      case (Nil, child) => (Nil, child)
      case (tag :: tags, child) =>
        val v = vars.newvar[Bottom](tag)
        unbindMultiple((tags, child)) match {
          case (vs, child) => (v :: vs, unbind(child, v))
        }
    }
  }
  object Bind {

    def apply[C >: Bottom <: Top](vs: List[Var[_ >: Bottom <: Top]], child: C): (List[Tag], C) = {
      vs match {
        case Nil => (Nil, child)
        case v :: vs =>
          apply(vs, bind(v, child, 0)) match {
            case (tags, child) => (v.tag :: tags, child)
          }

      }
    }
    def unapply[C >: Bottom <: Top](x: (List[Tag], C)): Some[(List[Var[_ >: Bottom <: Top]], C)] = {
      Some(unbindMultiple(x))
    }
  }
  def substitute[A >: Bottom <: Top, B >: Bottom <: Top](what: B, variable: Var[B], in: A): A = {
    show(in) match {
      case NodeView(tag, constant, children) =>
        hide(NodeView(tag, constant, children.map({ case (n, in2) => (n, substitute(what, variable, in2)) })))
      case LeafView(FreeLeaf(`variable`)) => what.asInstanceOf[A]
      case LeafView(FreeLeaf(_)) => in
      case LeafView(BoundLeaf(_)) => in
    }
  }
}
trait Delay[T] {
  type lam[X] = T
}

trait Variable[Tag, Free[_]] {
  def newvar[X](origin: Tag): Free[X]
}
case class IntWrapper(tag: String, id: Int) extends TagApi[String] {
  override def toString = tag + "$" + encode(id)
  def encode(x: Int): String = {
    if (x == 0) {
      "a"
    } else encodeImpl(x)
  }
  def encodeImpl(x: Int): String = {
    if (x == 0) {
      return ""
    }
    val base = 26;
    val (div, rem) = (x / base, x % base)
    encodeImpl(div) + (rem + 'a').asInstanceOf[Char]
  }
}
class StringVariable extends Variable[String, ({ type lam[X] = IntWrapper })#lam] {
  var counter = 0
  def newvar[X](origin: String) = {
    counter += 1

    new IntWrapper(origin, counter)
  }
}