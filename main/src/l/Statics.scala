package l
import syntax.universe._
import syntax.universe.vars._
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
      case (Triv, Triv) =>
        Triv()
      case (Arrow(in1, out1), Arrow(in2, out2)) =>
        val in = unify(in1, in2)
        val out = unify(out1, out2)
        Arrow(in, out)
      case (Nat, Nat) =>
        Nat()

      case _ =>
        typeProblem(found, required)
    }
  }
  def unifyValue(found: ValueType, required: PartialType): ValueType = {
    (found, required) match {
      case (_, Unknown) =>
        found
      case (Triv, Triv) =>
        Triv()
      case (Arrow(in1, out1), Arrow(in2, out2)) =>
        val in = unifyValue(in1, in2)
        val out = unifyValue(out1, out2)
        Arrow(in, out)
      case (Nat, Nat) =>
        Nat()
      case _ =>
        typeProblem(found, required)
    }
  }

  def evaluateExpressionType(tpe: ExpressionType): ValueType = {
    partialAsValue(evaluate(tpe: CodeType))
  }
  /**
   * Attempts to "evaluate" the type by invoking all applications.
   */

  def evaluate(tpe: CodeType): PartialType = {
    tpe match {
      case Unknown => Unknown()
      case Triv => Triv()
      case Arrow(in, out) =>
        Arrow(evaluate(in), evaluate(out))
      case Apply(x, y) =>
        val fun = evaluate(x)
        val arg = partialAsValue(evaluate(y))

        fun match {
          case Lambda(_, v, body) =>
            evaluate(body.sub(v -> arg))
          case Unknown => inferenceProblem
          case _ => throw new RuntimeException("Stuck!");
        }
      case Lambda(annot, v, body) =>
        Lambda(annot, v, body)
      case Forall(kind, v, body) =>
        Forall(kind, v, evaluate(body))
      case VarTerm(v) =>
        val ret = VarTerm(v)
        ???
      case Nat => Nat()

    }
  }

  /**
   * checked the given kind against an optional requirement.
   */
  def unify(found: Kind, required: Option[Kind]): Kind = {
    required.filter(_ == found).map(kindProblem(_, found))
    found
  }

  def kindcheck(context: Map[Var[ValueType], Kind], tpe: CodeType, result: Option[Kind]): Kind = {
    tpe match {
      case Unknown => result match {
        case Some(kind) => kind
        case None => inferenceProblem
      }
      case Triv =>
        unify(Triv(), result)
      case Arrow(in, out) =>
        kindcheck(context, in, Some(Triv()))
        kindcheck(context, out, Some(Triv()))
        Triv()
      case Apply(fun, arg) =>
        kindcheck(context, fun, None)
      case Lambda(annot, v, body) =>
        Arrow(annot, kindcheck(context + (v -> annot), body, None))
      case Forall(kind, v, body) =>
        Triv()

      case VarTerm(v) =>
        unify(context.getOrElse(v, bindingProblem(v.tag)), result)
      case Nat => Triv()
    }
  }
  def normalize(omega: Map[Var[ValueType], Kind], tpe: CodeType): PartialType = {
    kindcheck(omega, tpe, Some(Triv()))
    evaluate(tpe)
  }
  def codeAsExpression(tpe: CodeType): ExpressionType = {
    tpe match {
      case Arrow(a, b) => Arrow(codeAsExpression(a), codeAsExpression(b))
      case Lambda(k, v, t) =>
        Lambda(k, v, codeAsExpression(t))
      case Unknown => inferenceProblem
      case Forall(k, v, t) =>
        Forall(k, v, codeAsExpression(t))
      case Triv => Triv()
      case VarTerm(v) => VarTerm(v)
      case Nat => Nat()
    }
  }
  def partialAsValue(tpe: PartialType): ValueType = {
    tpe match {
      case Arrow(a, b) => Arrow(partialAsValue(a), partialAsValue(b))
      case Lambda(k, v, t) =>
        Lambda(k, v, codeAsExpression(t))
      case Unknown => inferenceProblem
      case Forall(k, v, t) =>
        Forall(k, v, partialAsValue(t))
      case Triv => Triv()
      case VarTerm(v) => VarTerm(v)
      case Nat => Nat()
    }
  }

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
      case Lambda(annot, variable, body) =>
        isValue(normalize(omega, annot)) || needsHint(omega, body)
      case PolyLambda(annot, variable, body) =>
        needsHint(omega, body)
      case Apply(fun, arg) =>
        needsHint(omega, fun) && needsHint(omega, arg)
      case PolyApply(fun, arg) =>
        needsHint(omega, fun)
      case Triv =>
        false
      case VarTerm(v) =>
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
  type Gamma = Map[Var[Val], ValueType]
  type Omega = Map[Var[ValueType], Kind]

  case class Context(omega: Omega, gamma: Gamma) {
    def addKind(x: Var[ValueType], k: Kind) = {
      copy(omega = omega + (x -> k))
    }
    def addKind(x: (Var[ValueType], Kind)) {
      copy(omega = omega + x)
    }
    def +(input: (Var[Val], ValueType)): Context = copy(gamma = gamma + input)
  }

  //this is a weaker form of algorithm W where all variables are replaced by a wildcard.
  def typecheck(
    context: Context,
    e: Expression,
    result: PartialType): ValueType = e match {

    case Lambda(annotExpr, variable, body) =>
      val annot = normalize(context.omega, annotExpr)
      val (input, output) = result match {
        case Unknown =>
          amend(variable.tag, true) {
            (partialAsValue(annot), Unknown())
          }
        case Arrow(input, output) =>
          amend(variable.tag, true) {
            (partialAsValue(unify(annot, input)), output)
          }
        case _ =>
          //this is an error case, but let's
          //give some extra info to the user
          val vartype = append(TypeProblem(Arrow(annot, Unknown()), result)) {
            partialAsValue(annot)
          }
          val output = append(TypeProblem(Arrow(vartype, Unknown()), result)) {
            typecheck(context + (variable -> vartype), body, Unknown())
          }
          typeProblem(Arrow(vartype, output), result)
      }
      Arrow(input, typecheck(context + (variable -> input), body, output))

    case Apply(fun, arg) =>
      if (needsHint(context.omega, fun)) {
        val Arrow(in, out) = typecheck(context, fun, Arrow(typecheck(context, arg, Unknown()), result))
        out
      } else {
        val Arrow(in, out) = typecheck(context, fun, Arrow(Unknown(), result))
        typecheck(context, arg, in)
        out
      }

    case Triv =>
      unifyValue(Triv(), result)

    case VarTerm(x) =>
      val vartype = context.gamma.getOrElse(x, bindingProblem(x.tag))
      unifyValue(vartype, result)

    case PolyApply(expr, typeArg) =>
      val kindIn = kindcheck(context.omega, typeArg, None)
      val typeArgVal = evaluateExpressionType(typeArg)
      typecheck(context, expr, Unknown()) match {
        case Forall(kindRequired, variable, cls) =>
          unify(kindIn, Some(kindRequired))
          unifyValue(cls.sub(variable -> typeArgVal), result)
        case found => typeProblem(found, result)
      }

    case PolyLambda(k, x, e) =>
      val newContext = context.addKind(x, k)
      def found = Forall(k, x, typecheck(newContext, e, Unknown()))
      result match {
        case Unknown =>
          found
        case _ =>
          val problem = TypeProblem(Forall(k, x, Unknown()), result)
          typeProblem(append(problem)(found), result)
      }

    case Zero =>
      unifyValue(Nat(), result)

    case Succ(pred) =>
      typecheck(context, pred, unify(Nat(), result))

    case Num(n) =>
      unifyValue(Nat(), result)

    case Fold(base, hypo, step, num) =>
      typecheck(context, num, Nat())
      val predicate = typecheck(context, base, Unknown())
      typecheck(context + (hypo -> predicate), step, predicate)

  }

}