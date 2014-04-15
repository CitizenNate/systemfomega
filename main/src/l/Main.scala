package l
import syntax.universe._
import scala.language.higherKinds
object MainTest extends App {
  val t: PartialType = Triv()
  val x: PartialType = Arrow(Triv(), Triv())
  val res = x match {
    case Triv => Unknown()
    case Unknown => Triv()
    case Arrow(a, b) => (a, b)
  }
  println(res)
}
