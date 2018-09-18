import qq.droste._
import data.Attr
import data.list._

object Dyna {

  val natCoalg = Coalgebra[ListF[Int, ?], Int] {
    case 0 => NilF
    case n => ConsF(n, n-1)
  }

  val cvAlg = {

    def take(n: Int, xs: Attr[ListF[Int, ?], Int]): List[Int] =
      if (n <= 0) Nil else
        Attr.un[ListF[Int, ?], Int](xs) match {
          case (a, NilF) => List(a)
          case (a, ConsF(_, as)) => a :: take(n - 1, as)
        }

    CVAlgebra[ListF[Int, ?], Int] {
      case NilF => 1
      case ConsF(n, table) =>
        val xs = take(n, table)
        xs.zip(xs.reverse).map { case (a, b) => a * b }.sum
    }
  }

  val catalan = scheme.zoo.dyna[ListF[Int, ?], Int, Int](cvAlg, natCoalg)

  def main(args: Array[String]): Unit = {

    (0 to 10).foreach(i => println(catalan(i)))

  }
}
