package m
import scala.reflect._
import scala.reflect.runtime.universe._
import java.io.PrintWriter
case class Sort(name: String)
abstract class SyntaxBuilder extends App {
  val SORT: Enumeration
  type Sort = SORT.Value

  implicit class SortHelpers(x: Sort) {
    def <:<(y: Sort) = (x, y)
  }
  def subtyping: List[(Sort, Sort)]

  sealed trait Part {
    def inargs: List[(String, String)]
    def outargs: List[String]
    def erasedArgs: List[(String, String)]
    def value: (String, String)
    def boundValue: String
    def makeApply: (List[String],String)
  }
  case class Bind(bind: (String, Sort), in: Part) extends Part {
    def inargs = (bind._1, "Var[_ >: " + bind._2.toString() + "]") :: in.inargs
    def outargs = "Var[" + bind._2.toString() + "]" :: in.outargs
    def erasedArgs = (bind._1, "Free") :: in.erasedArgs
    def value = in.value
    def boundValue = in.boundValue
    def makeApply = in.makeApply match { case (tags,name)=>(bind._1::tags,name)}
  }
  case class Finally(child: (String, Sort)) extends Part {
    def inargs = (child._1, child._2.toString()) :: Nil
    def outargs = child._2.toString() :: Nil
    def erasedArgs = (child._1, "Top") :: Nil
    def value = (child._1, "(List[Tag],Top)")
    def boundValue = child._1
    def makeApply = (Nil,child._1)
  }

  sealed trait Decl
  case class NodeDecl(constants: List[(String, String)], input: List[Part], output: Sort, name: String, producer: Boolean = true) extends Decl {
    val inargs = constants ::: input.map(_.inargs).flatten
    val outargs = constants.map(_._2) ::: input.map(_.outargs).flatten

    val erasedArgs = constants ::: input.map(_.erasedArgs).flatten
    val value = constants ::: input.map(_.value)
    val makeApply: List[String] = constants.map(_._1) ::: (input.map("Bind"+_.makeApply.toString))
    val erasure = (erasedArgs, makeApply)
  }
  case class VarDecl(site: Sort, inside: Sort, producer: Boolean = true) extends Decl

  def decls: List[Decl]

  def print(output: PrintWriter) {
    import output._
    val sorts = SORT.values.toList
    val extensions = subtyping.groupBy(_._1).mapValues(_.map(_._2)).withDefaultValue(Nil);
    val split = decls.map({ case x: NodeDecl => Left(x) case y: VarDecl => Right(y) })
    val (nodes, vardecls) = (split.map(_.left.toOption).flatten, split.map(_.right.toOption).flatten)

    val groups = nodes.groupBy(_.name).toMap
    def typeList(x: List[String]) = {
      x match {
        case Nil => "Option[Unit]"
        case xs => xs.mkString("Option[(", ",", ")]")
      }
    }
    def nameList(x: List[String]) = {
      x match {
        case Nil => ""
        case xs => xs.mkString("(", ",", ")")
      }
    }
    def groupExtractors(name: String, size: Int) = {
      (0 until size).map(name + "Extractor" + _).mkString(" with ")
    }
    def template(signature: Boolean) {

      if (signature) {

        println("abstract class SyntaxSignature extends AbstractViewer {")
        //println("type Var[T] = Free[T]")
        for (sort <- sorts) {
          val parents = extensions(sort)
          println("\ttype " + sort + " >: Bottom <: " + ("Top" :: s"TermApi[$sort]" :: parents).mkString("", " with ", ""))
        }
        for ((name, group) <- groups) {
          val obj = group.head.input.size == 0 && group.head.constants.size == 0
          /*if (group.head.input.size == 0) {
            
            println("\ttrait " + name + "Extractor{")
            println("\t\tself:" + selfType + " =>")
            println("\t\tdef unapply(x :" + selfType + "):Boolean")
            println("\t}")
            write("\tval " + name + " : " + name + "Extractor")
          } else {*/
          for ((node, index) <- group.zipWithIndex) {

            println("\ttrait " + name + "Extractor" + index + " {")
            if (!obj && node.producer) {
              println("\t\tdef apply" + node.inargs.map({ case (name, tpe) => name + ": " + tpe }).mkString("(", ",", ")") + " : " + node.output)
            }
            println("\t\tdef unapply(node:" + node.output + ") : " + typeList(node.outargs))
            println("\t}")
          }
          if (obj) {
            println("\ttrait " + name + "Producer {")
            val selfType = group.map(_.output).mkString(" with ")
            println("\t\tdef apply(): " + selfType)
            println("\t}")
          }
          write("\tval " + name + " : " + groupExtractors(name, group.size))
          if (obj) {
            write(" with " + name + "Producer")
          }
          println()
          if (obj) {
            //println("\timplicit def convert" + name + "(x:" + name + ".type)=x.apply()")
          }
        }
        if (vardecls.size > 0) {
          for ((VarDecl(site, inside, producer), index) <- vardecls.zipWithIndex) {
            println("\ttrait VarExtractor" + index + "{")
            if (producer) {
              println(s"\t\tdef apply(x:Var[$site]):$inside")
            }
            println(s"\t\tdef unapply(x:$inside):Option[Var[$site]]")
            println("\t}")
          }

          println("\tval VarTerm : " + groupExtractors("Var", vardecls.size))
        }
      } else {
        println(s"abstract class SyntaxStructure extends SyntaxSignature {")
        println("import vars._")
        println("\ttrait Top extends TermApi[Top] {")
        println("\t\tdef sub[B >: Bottom <: Top](b: (Var[B], B)): Top = {")
        println("\t\t\tsubstitute(b._2, b._1, this)")
        println("\t\t}")
        println("\t}")
        println("\ttype Free <: TagApi[Tag]")
        println("\ttype Var[X]=Free")
        println("\toverride type Bottom = Top")
        for (sort <- sorts) {
          println("\toverride type " + sort + " = Top")
        }
        for ((name, group) <- groups) {

          for ((value, valueGroup) <- group.groupBy(_.value)) {
            val obj = value.size == 0
            var valueName: String = null
            if (obj) {
              valueName = name
              println(s"\tcase object $name extends " + groupExtractors(name, group.size) + " with " + name + "Producer with Top {")
            } else {
              valueName = name + "Impl"
              println("\tcase class " + valueName + value.map({ case (name, tpe) => name + ": " + tpe }).mkString("(", ",", ")") + " extends Top{")
              println("\t\toverride def productPrefix:String = \"" + name + "\"")
              println("\t}")
              println("\tobject " + name + " extends " + groupExtractors(name, group.size) + " {")

            }
            for ((erasedArgs, erasedApply) <- valueGroup.map(_.erasure).distinct) {
              val names = nameList(erasedApply)
              val applyArgs = if (obj) {
                "()"
              } else {
                erasedArgs.map({ case (name, tpe) => name + ": " + tpe }).mkString("(", ",", ")")
              }
              println("\t\tdef apply" + applyArgs + " : Top = {")
              println("\t\t\t" + valueName + nameList(erasedApply))
              println("\t\t}");
              println("\t\tdef unapply(node:Top) : " + typeList(erasedArgs.map(_._2)) + " = {")
              println("\t\t\tnode match { case " + valueName + nameList(erasedApply) + "=>Some(" + nameList(erasedArgs.map(_._1)) + ") case _ => None }")
              println("\t\t}")
            }
            println("\t}")

          }

        }
        println("\tcase class VarTermImpl(v: Leaf[Free]) extends Top")
        println("\tcase object VarTerm extends " + groupExtractors("Var", vardecls.size) + " {")
        println("\t\tdef apply(x:Free) = VarTermImpl(FreeLeaf(x))")
        println("\t\tdef unapply(x:Top) = x match {")
        println("\t\t\tcase VarTermImpl(FreeLeaf(v))=>Some(v)")
        println("\t\t\tcase VarTermImpl(BoundLeaf(_))=> ???")
        println("\t\t\tcase _ => None")
        println("\t\t}")
        println("\t}")
        println("\tdef show[T >: Bottom <: Top](term: T):View[T] = term match {")
        for ((name, group) <- groups) {
          for (((value, valueGroup), valueIndex) <- group.groupBy(_.value).zipWithIndex) {
            val node = valueGroup.head
            val names = nameList(value.map(_._1))
            val implName = if (value.size > 0) name + "Impl" else name
            println(s"\t\tcase $implName$names =>")
            val constants = node.constants.map({ case (name, tpe) => name + ":" + tpe }).mkString("List(", ",", ")")
            val children = node.input.map(_.value).map(_._1).mkString("List(", ",", ")")
            val boundChildren = node.input.map(_.boundValue).mkString("List(", ",", ")")
            println(s"\t\t\tNodeView({case ($constants,$children) => $implName$names },$constants,$boundChildren)")
          }
        }
        println("\t\tcase VarTermImpl(v) => LeafView(v)")
        println("\t}")
        println("\tdef hide[T >: Bottom <: Top](view:View[T]):T = view match {")
        println("\t\tcase NodeView(tag,constant,children)=> tag(constant,children)")
        println("\t\tcase LeafView(v) => VarTermImpl(v)")
        println("\t}")
      }
      println("}")
      println()
    }

    println("// AUTOGENERATED CODE - DO NOT EDIT")
    println("package g")
    println("import m.Delay")
    println("import m.Viewer")
    println("import m.AbstractViewer")
    println("import m.Variable")
    println("import m.TagApi")
    println("import scala.language.higherKinds")
    println("import scala.language.implicitConversions")
    println("/** MATCH TEMPLATES")
    val supergraph = new Graph(extensions);
    val supertypes = sorts.map(x => x -> supergraph.reachable(x)).toMap;
    println(extensions)
    for (sort <- sorts) {
      println()
      println(sort + " match {")
      for ((name, group) <- nodes.filter(x => supertypes(x.output).contains(sort)).groupBy(_.name)) {
        val node = group.head
        println("\tcase " + node.name + nameList(node.inargs.map(_._1)) + " => ???")
      }
      println("}")
    }
    println("**/")
    template(true)
    template(false)
    close()
  }

}
class Graph[A](graph: Map[A, List[A]]) {
  def reachable(a: A): Set[A] = {
    bfs(Set(a))
  }
  def bfs(a: Set[A]): Set[A] = {

    val b = a.union(a.flatMap(graph))
    if (a == b) b else bfs(b)
  }
}