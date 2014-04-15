package l

import g.SyntaxSignature
import g.SyntaxStructure
import m.IntWrapper
import m.StringVariable
import scala.language.higherKinds
import m.Variable
object syntax {
  private object Structure extends SyntaxStructure {
    type Free = IntWrapper
    type Tag = String
    val vars = new StringVariable()
  }
  val universe: SyntaxSignature{
    type Tag = String
  } = Structure
}