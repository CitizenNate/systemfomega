package l
import Util._
import Binding._
import scala.language.implicitConversions
import scala.language.higherKinds
/**
 * Binding provides access to ASTs through reflection. Mainly, this class provides access
 * to the substitution operation on ASTs: [a/x]b can be performed by b.sub( x -> a ). 
 */



object Binding {
  case class SyntaxMap[+A, +B](entries: List[(A, B)])
  implicit def syntaxToMap[A, B](map: SyntaxMap[A, B]): Map[A, B] = {
    map.entries.toMap
  }
  implicit def mapToSyntax[A, B](map: Map[A, B]): SyntaxMap[A, B] = {
    SyntaxMap(map.toList)
  }
  class Builder[+T](private val cls: Class[_], val fun: List[Any] => T) {
    override def equals(other: Any): Boolean = {
      other.getClass() == this.getClass() &&
        other.asInstanceOf[Builder[_]].cls == cls
    }
    def apply(x: List[Any]) = fun(x)
    def apply(x: Any) = fun(List(x))
  }
  def showProduct[T <: Product](t: T): (Builder[T], List[Any]) = {
    val builder = (args: List[Any]) => {
      val newArgs = try {
        val field = t.getClass.getField("$outer")
        field.setAccessible(true)
        val outer = field.get(t)
        outer :: args
      } catch {
        case e: NoSuchFieldException =>
          args
      }
      val constructor = t.getClass.getDeclaredConstructors()(0)
      constructor.setAccessible(true)
      constructor.newInstance(newArgs.map(_.asInstanceOf[Object]).toSeq: _*).asInstanceOf[T]
    }
    (new Builder(t.getClass, builder), t.productIterator.toList)
  }

}
abstract class Binding {
  type Bind[T] <: Var[T]
  type Var[+T]

  //def varToBind[T](x: Var[T]): Bind[T2] forSome { type T2 <: T }
  //def bindToVar[T](x: Bind[T]): Var[T2] forSome { type T2 >: T }

  def newvar[T]: Var[T] with Bind[T]

  def substituteImpl[T, T2](e1: T, x: Bind[_ >: T], e2: T2): T2
  def alpha[T](x: T, y: T): Boolean
  def normalizeImpl[T](x: T): T

  implicit class TermHelpers[T](val x: T) {
    def norm: T = normalizeImpl[T](x)
    def sub[T2](y: (Bind[_ >: T2], T2)) = substituteImpl[T2, T](y._2, y._1, x)
  }
}
abstract class AbstractBinding extends Binding {
  type Symbol

  type Bind[-T] = Symbol

  type Var[+T] = Symbol

  def minimumExcluded(x: Set[Symbol]): Symbol

  def getVar(x: Any): Option[Symbol]

  //def varToBind[T](x: Var[T]): Bind[T2] forSome { type T2 <: T } = x
  //def bindToVar[T](x: Bind[T]): Var[T2] forSome { type T2 >: T } = x

  sealed abstract class View[+T](id: Any)
  case class NodeView[+T](builder: Builder[T],
    base: List[Any],
    terms: List[(List[Symbol], Any)]) extends View[T](builder)

  case class VarView[+T](builder: Builder[T], v: Symbol) extends View[T](builder)

  def showt[T](t2: T): View[T] = {
    val t = t2.asInstanceOf[Product with T]
    val (builder, fields) = showProduct(t)
    if (t.productArity == 1) {
      val first = fields(0)
      getVar(first) match {
        case Some(v) =>
          return VarView[T](builder, v)
        case None => ()
      }
    }
    def tryCast(x: Any): Option[Product] = {
      (x, getVar(x)) match {
        case (y: Product, None) =>
          Some[Product](y)
        case _ => None
      }
    }
    val (uncastTerms, base) = split(fields, (tryCast _))
    val terms: List[(List[Symbol], Product)] = uncastTerms.map({ case ((vars: List[Symbol], term: Product)) => (vars, term) })
    return NodeView(builder, base, terms);
  }
  def hidet[T](t: View[T]): T = {
    t match {
      case VarView(builder, v) => builder(v)
      case NodeView(builder, base, terms) =>
        builder(terms.map({ case (vs, t) => vs :+ t }).flatten ++ base)
    }
  }
  def substituteExact[T, T2](e1: T, x: Symbol, e2: T2): T2 = {
    showt(e2) match {
      case NodeView(builder, base, terms) =>
        hidet(
          NodeView(
            builder,
            base,
            terms.map(term => term match {
              case (xs, t) =>
                (xs, substituteExact(e1, x, t))
            })))
      case VarView(builder, v) =>
        if (v == x) {
          //TODO is this safe?
          e1.asInstanceOf[T2]
        } else {
          hidet(VarView(builder, v))
        }
    }
  }
  def freshenBinds(fresh: Map[Symbol, Symbol], binds: (List[Symbol], Any)): (List[Symbol], Any) = {
    binds._1 match {
      case Nil => (Nil, freshen(fresh, binds._2))
      case x :: xs =>
        val y = newvar
        val ret = freshenBinds(fresh + (x -> y), (xs, binds._2))
        (y :: ret._1, ret._2)
    }
  }
  def freshen[T](fresh: Map[Symbol, Symbol], e1: T): T = {
    hidet(showt(e1) match {
      case NodeView(builder, base, terms) =>
        NodeView(builder, base, terms.map(freshenBinds(fresh, _)))
      case VarView(builder, v) =>
        VarView(builder, fresh.get(v).getOrElse(v))
    })
  }
  def substituteImpl[T, T2](e1: T, x: Symbol, e2: T2): T2 = {
    //TODO freshen only when necessary
    val e2f = freshen(Map.empty, e2)
    substituteExact(e1, x, e2f)
  }
  def isfree(x: Symbol, e: Any): Boolean = {
    showt(e) match {
      case NodeView(builder, base, terms) =>
        terms.exists({ case (xs, e2: Any) => !xs.contains(x) && isfree(x, e2) })
      case VarView(builder, v) => v == x
    }
  }
  def freevars(t: Any): List[Symbol] = {
    val ret = showt(t) match {
      case NodeView(_, _, ts) =>
        ts.map({
          case (xs, t) =>
            val before = freevars(t)
            val after = before.filterNot(xs.contains(_))
            after
        }).flatten
      case VarView(_, x) =>
        List(x)
    }
    ret
  }
  def alpha[T](x: T, y: T): Boolean = {
    alpha(Map.empty, x, y)

  }
  def alphaInner(context: Map[Symbol, Symbol], t1: (List[Symbol], Any), t2: (List[Symbol], Any)): Boolean = {
    (t1, t2) match {
      case ((Nil, t1), (Nil, t2)) =>
        alpha(context, t1, t2)
      case ((x :: xs, t1), (y :: ys, t2)) =>
        alphaInner(context + (x -> y), (xs, t1), (ys, t2))
    }
  }
  def alpha[T](context: Map[Symbol, Symbol], x: T, y: T): Boolean = {
    val ret = (showt(x), showt(y)) match {
      case (NodeView(c1, b1, t1), NodeView(c2, b2, t2)) =>
        val ret1 = c1 == c2
        val ret2 = b1 == b2
        val ret3 = t1.corresponds(t2)(alphaInner(context, _, _))
        val ret = ret1 && ret2 && ret3
        ret
      case (VarView(c1, x), VarView(c2, y)) =>
        c1 == c2 && (context.get(x) match {
          case None => ???
          case Some(y2) =>
            y == y2
        })
      case _ => false
    }
    ret
  }
  def normalizeImpl[T](term: T): T = {
    normalizeImpl(freevars(term).map(x => (x, x)).toMap, term)
  }
  def normalizeImpl[T](context: Map[Symbol, Symbol], term: T): T = {
    showt(term) match {
      case VarView(b, x) =>
        hidet(VarView[T](b, context(x)))
      case NodeView(builder, value, children) =>
        hidet(NodeView(
          builder,
          value,
          children.map(normalizeInner(context))))
    }
  }
  def normalizeInner[T](context: Map[Symbol, Symbol])(child: (List[Symbol], T)): (List[Symbol], T) = {
    child match {
      case (Nil, t) => (Nil, normalizeImpl(context, t))
      case (x :: xs, t) =>
        normalizeInnerVar(context, x, xs, t)
    }
  }
  def normalizeInnerVar[T](context: Map[Symbol, Symbol], x: Symbol, xs: List[Symbol], t: T): (List[Symbol], T) = {
    val y = minimumExcluded(context.values.toSet)
    val (ys, t2) = normalizeInner(context + (x -> y))(xs, t)
    (y :: ys, t2)
  }
}
case class IntWrapper(x: Int) {
  override def toString = encode(x)
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
class StringBinding extends AbstractBinding {

  type Symbol = IntWrapper
  var counter = 0
  def newvar[X] = {
    counter = counter + 1
    new IntWrapper(counter)
  }
  override def minimumExcluded(set: Set[Symbol]): IntWrapper = {
    for (i <- 0 until Int.MaxValue) {
      if (!set.contains(IntWrapper(i))) {
        return IntWrapper(i)
      }
    }
    ???
  }
  def getVar(x: Any) = {
    x match {
      case y @ IntWrapper(s) => Some(y)
      case _ => None
    }
  }

}