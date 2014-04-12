package l
import Syntax._
import Syntax.binding._
import Problems._
import scala.language.implicitConversions
object Statics extends App {
  /**
   * Under the interpretation of PartialTypes as sets,
   * returns the intersection of the arguments
   */
  def unify(found: PartialType, required: PartialType): PartialType = {
    (found, required) match {
      case (Unknown, _) =>
        required
      case (_, Unknown) =>
        found
      case (Unit, Unit) =>
        Unit
      case (Arrow(in1, out1), Arrow(in2, out2)) =>
        val in = unify(in1, in2)
        val out = unify(out1, out2)
        Arrow(in, out)
      case (Nat, Nat) =>
        Nat
      case _ =>
        typeProblem(found, required)
    }
  }

  /**
   * Attempts to "evaluate" the type by invoking all applications.
   */

  def evaluate(context: Map[Var[CodeType], Var[PartialType]], tpe: CodeType): PartialType = {
    tpe match {
      case Unknown => Unknown
      case Unit => Unit
      case Arrow(in, out) =>
        Arrow(evaluate(context, in), evaluate(context, out))
      case ApplyC(x, y) =>
        val fun = evaluate(context, x)
        val arg = evaluate(context, y)
        fun match {
          case LambdaP(_, v, body) =>
            evaluate(context, body.sub(v -> arg))
          case Unknown => inferenceProblem
          case _ => throw new RuntimeException("Stuck!");
        }
      case LambdaP(annot, v, body) =>
        LambdaP(annot, v, evaluate(context + (v -> v), body))
      case ForallP(kind, v, body) =>
        ForallP(kind, v, evaluate(context + (v -> v), body))
      case VarP(v) => VarP(context(v))
      case Nat => Nat
    }
  }

  /**
   * checked the given kind against an optional requirement.
   */
  def unify(found: Kind, required: Option[Kind]): Kind = {
    required.filter(_ == found).map(kindProblem(_, found))
    found
  }

  def kindcheck(context: Map[Var[PartialType], Kind], tpe: CodeType, result: Option[Kind]): Kind = {
    tpe match {
      case Unknown => result match {
        case Some(kind) => kind
        case None => inferenceProblem
      }
      case Unit =>
        unify(Unit, result)
      case Arrow(in, out) =>
        kindcheck(context, in, Some(Unit))
        kindcheck(context, out, Some(Unit))
        Unit
      case ApplyC(fun, arg) =>
        kindcheck(context, fun, None)
      case LambdaP(annot, v, body) =>
        Arrow(annot, kindcheck(context + (v -> annot), body, None))
      case ForallP(kind, v, body) =>
        Unit
      case VarP(v) =>
        unify(context.getOrElse(v, bindingProblem(v)), result)
      case Nat => Nat
    }
  }
  def normalize(omega: Omega, tpe: CodeType): PartialType = {
    kindcheck(omega, tpe, Some(Unit))
    evaluate(Map.empty, tpe)
  }
  def partialToValue(context: Map[Var[PartialType], Var[ValueType]], tpe: PartialType): ValueType = {
    tpe match {
      case Unknown => inferenceProblem
      case Arrow(a, b) =>
        Arrow(partialToValue(context, a), partialToValue(context, a))
      case LambdaP(k, v, t) =>
        val nv = newvar[ValueType]
        LambdaV(k, nv, partialToValue(context + (v -> nv), t))
      case ForallP(k, v, t) =>
        val nv = newvar[ValueType]
        ForallV(k, nv, partialToValue(context + (v -> nv), t))
      case Unit => Unit
      case VarP(v) => VarV(context(v))
      case Nat => Nat
    }
  }

  def valueToPartial(context: Map[Var[ValueType], Var[PartialType]], tpe: ValueType): PartialType = {
    tpe match {
      case Arrow(a, b) =>
        Arrow(valueToPartial(context, a), valueToPartial(context, a))
      case LambdaV(k, v, t) =>
        val nv = newvar[PartialType]
        LambdaP(k, nv, valueToPartial(context + (v -> nv), t))
      case ForallV(k, v, t) =>
        val nv = newvar[PartialType]
        ForallP(k, nv, valueToPartial(context + (v -> nv), t))
      case Unit => Unit
      case VarV(v) => VarP(context(v))
      case Nat => Nat
    }
  }

  implicit def valueToPartial(tpe: ValueType): PartialType = valueToPartial(Map.empty, tpe)

  def partialAsValue(tpe: PartialType) = partialToValue(Map.empty, tpe)

  def isValue(tpe: PartialType): Boolean = {
    try {
      partialAsValue(tpe)
      return true;
    } catch {
      case e: TypeException if e.problems == List(InferenceProblem(Nil, true)) =>
        true
    }
  }

  def normalizeToValue(omega: Omega, tpe: CodeType): ValueType = {
    partialAsValue(normalize(omega, tpe))
  }

  /**
   * returns whether a hint would be necessary to typecheck this expression
   */
  //TODO need to memoize for reasonable efficiency
  def needsHint(omega: Omega, e: Expression): Boolean = {
    e match {
      case LambdaE(annot, variable, body) =>
        isValue(normalize(omega, annot)) || needsHint(omega, body)
      case LambdaTE(annot, variable, body) =>
        needsHint(omega, body)
      case ApplyE(fun, arg) =>
        needsHint(omega, fun) && needsHint(omega, arg)
      case ApplyET(fun, arg) =>
        needsHint(omega, fun)
      case Triv =>
        false
      case VarE(v) =>
        false
      case Fold(base, hypo, step, num) =>
        ???
      case Zero =>
        false
      case Num(n) =>
        false
      case Succ(n) =>
        needsHint(omega, n)
    }
  }
  //  type Gamma = Map[Var[Expression], ValueType]

  case class Context(delta: Delta, omega: Omega, gamma: Gamma) {
    def addKind(x: Var[PartialType], nx: Var[ValueType], k: Kind) = {
      copy(delta = delta + (x -> nx), omega = omega + (x -> k))
    }
    def +(input: (Var[Expression], ValueType)): Context = copy(gamma = gamma + input)
  }

  //this is a weaker form of algorithm W where all variables are replaced by a wildcard.
  def typecheck(
    context: Context,
    e: Expression,
    result: PartialType): ValueType = e match {

    case LambdaE(annotExpr, variable, body) =>
      val annot = normalize(context.omega, annotExpr)
      val (input, output) = result match {
        case Unknown =>
          amend(variable, true) {
            (partialAsValue(annot), Unknown)
          }
        case Arrow(input, output) =>
          amend(variable, true) {
            (partialAsValue(unify(annot, input)), output)
          }
        case _ =>
          //this is an error case, but let's
          //give some extra info to the user
          val vartype = append(TypeProblem(Arrow(annot, Unknown), result)) {
            partialAsValue(annot)
          }
          val output = append(TypeProblem(Arrow(vartype, Unknown), result)) {
            typecheck(context + (variable -> vartype), body, Unknown)
          }
          typeProblem(Arrow(vartype, output), result)
      }
      Arrow(input, typecheck(context + (variable -> input), body, output))

    case ApplyE(fun, arg) =>
      if (needsHint(context.omega, fun)) {
        val Arrow(in, out) = typecheck(context, fun, Arrow(typecheck(context, arg, Unknown), result))
        out
      } else {
        val Arrow(in, out) = typecheck(context, fun, Arrow(Unknown, result))
        typecheck(context, arg, in)
        out
      }

    case Triv =>
      unify(Unit, result)
      Unit

    case VarE(x) =>
      val vartype = context.gamma.getOrElse(x, bindingProblem(x))
      unify(vartype, result)
      vartype

    case ApplyET(e, t) =>
      typecheck(context, e, ForallP(kindcheck(context.omega, t, None), newvar, result))

    case LambdaTE(k, x, e) =>
      val nx = newvar[ValueType]
      val newContext = context.addKind(x, nx, k)
      result match {
        case Unknown =>
          ForallV(k, nx, typecheck(newContext, e, Unknown))
        case ForallP(k2, x2, t) =>
          if (k != k2) {
            kindProblem(k, k2)
          }
          ForallV(k, nx, typecheck(newContext, e, t.sub(x2 -> VarP(x))))
        case _ =>
          val found = append(TypeProblem(ForallP(k, x, Unknown), result)) {
            ForallV(k, nx, typecheck(newContext, e, Unknown))
          }
          typeProblem(found, result)
      }

    case Zero =>
      unify(Nat, result)
      Nat

    case Succ(pred) =>
      typecheck(context, pred, unify(Nat, result))

    case Num(n) =>
      unify(Nat, result)
      Nat

    case Fold(base, hypo, step, num) =>
      typecheck(context, num, Nat)
      val predicate = typecheck(context, base, Unknown)
      typecheck(context + (hypo -> predicate), step, predicate)

  }

}