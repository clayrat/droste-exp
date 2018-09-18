import cats.Functor
import cats.syntax.functor._

import qq.droste._
import data.list._

// TODO http://www.iis.sinica.edu.tw/~scm/pub/mds.pdf

object Zygo {

  // TODO add to Droste
  def zygo[F[_] : Functor, R, A, B](
    algebra: Algebra[F, A],
    ralgebra: RAlgebra[A, F, B]
  )(implicit project: Project[F, R]): R => B =
    kernel.hylo[F, R, (A, B)](
      fab => (algebra.run(fab.map(_._1)), ralgebra.run(fab)),
      project.coalgebra.run)
      .andThen(_._2)

  val zygoPseudoalgebra = RAlgebra[Boolean, ListF[Int, ?], Int] {
    case NilF => 0
    case ConsF(n, (b, x)) => if (b) n + x else n - x
  }

  val zygoAlgebra = Algebra[ListF[Int, ?], Boolean] {
    case NilF => false
    case ConsF(_, bool) => !bool
  }

  val plusMinus = zygo[ListF[Int, ?], List[Int], Boolean, Int](zygoAlgebra, zygoPseudoalgebra)

  def main(args: Array[String]): Unit = {

    println(plusMinus(List(1, 2, 3, 4, 5)))

  }

}
