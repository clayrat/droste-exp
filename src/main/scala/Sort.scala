import qq.droste._
import qq.droste.data.list._
import ListF._
import cats.Functor

import scala.math.Ordering
import Ordering._

// following Augusteijn, "Sorting morphisms" (https://pdfs.semanticscholar.org/87b2/6d98d4c3e2f7983d0b79fba83c1f359abe25.pdf)

object Sort {

  // TODO add to droste.data.list?

  implicit def LFProjL[A] = new Project[ListF[A, ?], List[A]] {
    override def coalgebra: Coalgebra[ListF[A, ?], List[A]] = fromScalaListCoalgebra
  }

  implicit def LFEmbL[A] = new Embed[ListF[A, ?], List[A]] {
    override def algebra: Algebra[ListF[A, ?], List[A]] = toScalaListAlgebra
  }

  // 2.1 cata

  val prodAlg = Algebra[ListF[Int, ?], Int] {
    case NilF => 1
    case ConsF(h, t) => h * t
  }

  val prod = scheme.cata[ListF[Int, ?], List[Int], Int](prodAlg)

  // 2.2 ana

  val countCoalg = Coalgebra[ListF[Int, ?], Int] { n =>
    if (n == 0) NilF else ConsF(n, n-1)
  }

  val count = scheme.ana[ListF[Int, ?], Int, List[Int]](countCoalg)

  // 2.3 hylo

  val fac = scheme.hylo[ListF[Int, ?], Int, Int](prodAlg.run, countCoalg.run)

  // 2.4 insertion sort

  def insert[A: Ordering](x: A, l: List[A]): List[A] = {
    val ord = implicitly[Ordering[A]]
    l match {
      case Nil => List(x)
      case h::t => if (ord.lt(x,h)) x::h::t else h :: insert(x,t)
    }
  }

  def insertAlg[A: Ordering] = Algebra[ListF[A, ?], List[A]] {
    case NilF => Nil
    case ConsF(h, t) => insert(h, t)
  }

  def insertionSort[A: Ordering] = scheme.cata[ListF[A, ?], List[A], List[A]](insertAlg)

  // 2.5 selection sort

  def selectCoalg(extract: List[Int] => ListF[Int, List[Int]]) = Coalgebra[ListF[Int, ?], List[Int]] {
    case Nil => NilF
    case l@_::_ => extract(l)
  }

  // 2.5.1 straight

  def straightSelSort = {
    def selExtract(l : List[Int]): ListF[Int, List[Int]] = {
      def remove(x: Int, m: List[Int]): List[Int] = m match {
        case Nil => Nil
        case h::t if x == h => t
        case h::t => h :: remove(x,t)
      }
      val m = l.min
      ConsF(m, remove(m, l))
    }
    scheme.ana[ListF[Int, ?], List[Int], List[Int]](selectCoalg(selExtract))
  }

  // 2.5.2 bubble

  def bubbleSort = {
    def bubble(l : List[Int]): ListF[Int, List[Int]] = l match {
      case Nil => NilF // unreachable
      case h::Nil => ConsF(h, Nil)
      case h::t =>
        val ConsF(y,m) = bubble(t)
        if (h<y) ConsF(h, y::m) else ConsF(y, h::m)
    }
    scheme.ana[ListF[Int, ?], List[Int], List[Int]](selectCoalg(bubble))
  }

  def bubbleSort2 = {
    val bubbleAlg = Algebra[ListF[Int, ?], ListF[Int, List[Int]]] {
      case NilF => NilF // unreachable
      case ConsF(h, NilF) => ConsF(h, Nil)
      case ConsF(h, ConsF(i, t)) => if (h<i) ConsF(h, i::t) else ConsF(i, h::t)
    }
    scheme.ana[ListF[Int, ?], List[Int], List[Int]](selectCoalg(
      scheme.cata[ListF[Int, ?], List[Int], ListF[Int, List[Int]]](bubbleAlg)
    ))
  }

  // 3 leaf trees

  /*
  sealed trait LeafTree[A]
  case class Leaf[A](a: A) extends LeafTree[A]
  case class Split[A](l: LeafTree[A], r: LeafTree[A]) extends LeafTree[A]
*/

  sealed trait LeafTreeF[F, A]
  case class LeafF[F, A](a: A) extends LeafTreeF[F, A]
  case class SplitF[F, A](l: F, r: F) extends LeafTreeF[F, A]

  implicit def functor[A]: Functor[LeafTreeF[?, A]] = new Functor[LeafTreeF[?, A]] {
    override def map[B, C](fa: LeafTreeF[B, A])(f: B => C): LeafTreeF[C, A] = fa match {
      case SplitF(l, r) => SplitF(f(l), f(r))
      case LeafF(a)     => LeafF(a)
    }
  }

  def main(args: Array[String]): Unit = {

    println(prod(List(3,2,1)))

    println(count(3))

    println(fac(3))

    val unsorted = List(3,2,5,4,1)
    val intSort = insertionSort[Int]

    println(intSort(unsorted))
    println(straightSelSort(unsorted))
    println(bubbleSort(unsorted))
    println(bubbleSort2(unsorted))

  }


}
