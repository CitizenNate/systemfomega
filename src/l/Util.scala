package l

object Util {
  def split[A, B](xs: List[A], check: A => Option[B]): (List[(List[A], B)], List[A]) = {
    xs match {
      case Nil => (Nil, Nil)
      case a :: ys => check(a) match {
        case Some(b) =>
          split(ys, check) match {
            case (list, hang) => ((Nil, b) :: list, hang)
          }
        case None =>
          split(ys, check) match {
            case (Nil, hang) => (Nil, a :: hang)
            case (((as, b) :: list), hang) => (((a :: as, b) :: list), hang)
          }
      }
    }
  }
}