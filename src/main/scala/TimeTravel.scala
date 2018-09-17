import scala.language.higherKinds

import qq.droste._
import data._
import list._

// after https://jtobin.io/time-traveling-recursion

object TimeTravel {

  // TODO https://github.com/andyscott/droste/issues/59
  def oddIndices[A] = scheme.zoo.histo[ListF[A, ?], List[A], List[A]](
    CVAlgebra[ListF[A, ?], List[A]] {
      case NilF => Nil
      case ConsF(h, coa) => Attr.un[ListF[A, ?], List[A]](coa) match {
        case (_, NilF) => List(h)
        case (_, ConsF(_, coa2)) => h :: Attr.un[ListF[A, ?], List[A]](coa2)._1
      }
      //case ConsF(h, _ :< NilF) => List(h)
      //case ConsF(h, _ :< ConsF(_, t :< _)) => h :: t
    }
  )

  def evenIndices[A] = scheme.zoo.histo[ListF[A, ?], List[A], List[A]](
    CVAlgebra[ListF[A, ?], List[A]] {
      case NilF => Nil
      case ConsF(_, coa) => Attr.un[ListF[A, ?], List[A]](coa) match {
        case (_, NilF) => Nil
        case (_, ConsF(h, coa2)) => h :: Attr.un[ListF[A, ?], List[A]](coa2)._1
      }
      //case ConsF(_, _ :< NilF) => Nil
      //case ConsF(_, _ :< ConsF(h, t :< _)) => h :: t
    }
  )

  def oddIndicesF[A] = scheme.zoo.futu[ListF[A, ?], List[A], List[A]](
    CVCoalgebra[ListF[A, ?], List[A]] {
      case Nil => NilF
      case x :: Nil => ConsF(x, Coattr.pure[ListF[A, ?], List[A]](Nil))
      case x :: _ :: t => ConsF(x, Coattr.pure[ListF[A, ?], List[A]](t))
    }
  )

  def evenIndicesF[A] = scheme.zoo.futu[ListF[A, ?], List[A], List[A]](
    CVCoalgebra[ListF[A, ?], List[A]] {
      case Nil => NilF
      case _ :: Nil => NilF
      case _ :: h :: t => ConsF(h, Coattr.pure[ListF[A, ?], List[A]](t))
    }
  )

  def nilFr[A, B]: Coattr[ListF[A, ?], B] = Coattr.roll[ListF[A, ?], B](NilF)

  def consFr[A, B](a: A, b: B): Coattr[ListF[A, ?], B] = Coattr.roll[ListF[A, ?], B](ConsF(a, Coattr.pure[ListF[A, ?], B](b)))

  def twiddle[A] = scheme.zoo.futu[ListF[A, ?], List[A], List[A]](
    CVCoalgebra[ListF[A, ?], List[A]] {
      case Nil => NilF
      case x :: Nil => ConsF(x, nilFr)
      case x :: h :: t => ConsF(h, consFr(x, t))
    }
  )

  def main(args: Array[String]): Unit = {
    val l = List(1, 2, 3, 4, 5)
    println(oddIndices(l))
    println(evenIndices(l))
    println(oddIndicesF(l))
    println(evenIndicesF(l))

    println(twiddle((1 to 20).toList))

  }

}
