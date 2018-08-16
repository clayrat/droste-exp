import cats.Order
import cats.syntax.order._
import cats.instances.int._
import qq.droste._
import data._
import list._

// after https://jtobin.io/sorting-slower-with-style

object Apo {

  // TODO added to droste.Basis after 0.4.0
  implicit def drosteBasisForListF[A]: Basis[ListF[A, ?], List[A]] =
    Basis.Default[ListF[A, ?], List[A]](ListF.toScalaListAlgebra, ListF.fromScalaListCoalgebra)

  def mapHead[A](f: A => A) =
    scheme.zoo.apo[ListF[A, ?], List[A], List[A]](
      RCoalgebra[List[A], ListF[A, ?], List[A]] {
        case Nil => NilF
        case h :: t => ConsF(f(h), Left(t))
      }
    )

  def cat[A](l: List[A], r: List[A]) =
    scheme.zoo.apo[ListF[A, ?], List[A], List[A]](
      RCoalgebra[List[A], ListF[A, ?], List[A]] {
        case Nil => r match {
          case Nil => NilF
          case h :: t => ConsF(h, Left(t))
        }
        case x :: Nil => ConsF(x, Left(r))
        case x :: t => ConsF(x, Right(t))
      }
    ).apply(l)

  def knockback[A: Order] =
    scheme.zoo.apo[ListF[A, ?], ListF[A, List[A]], List[A]](
      RCoalgebra[List[A], ListF[A, ?], ListF[A, List[A]]] {
        case NilF => NilF
        case ConsF(x, Nil) => ConsF(x, Left(Nil))
        case ConsF(x, h :: t) if x <= h => ConsF(x, Left(h :: t))
        case ConsF(x, h :: t) => ConsF(h, Right(ConsF(x, t)))
      }
    )

  def insertionSort[A: Order] =
    scheme.cata[ListF[A, ?], List[A], List[A]](Algebra[ListF[A, ?], List[A]](knockback[A]))

  def main(args: Array[String]): Unit = {

    println(mapHead[Int](_ + 1)(List(1, 2, 3)))

    println(cat(List(1, 2, 3), List(4, 5, 6)))

    println(insertionSort.apply(List(3, 1, 1, 2, 4, 3, 5, 1, 6, 2, 1)))

  }

}
