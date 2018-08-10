import qq.droste._
import data._
import list._
import ListF._

import cats.Functor

import scala.math.Ordering

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

  // ex 1

  def revAlg[A] = Algebra[ListF[A, ?], List[A]] {
    case NilF => Nil
    case ConsF(h, t) => t :+ h
  }

  def revList[A] = scheme.cata[ListF[A, ?], List[A], List[A]](revAlg)

  // 2.2 ana

  val countCoalg = Coalgebra[ListF[Int, ?], Int] { n =>
    if (n == 0) NilF else ConsF(n, n-1)
  }

  val count = scheme.ana[ListF[Int, ?], Int, List[Int]](countCoalg)

  // TODO ex 2

  // 2.3 hylo

  val fac = scheme.hylo[ListF[Int, ?], Int, Int](prodAlg.run, countCoalg.run)

  // ex 3

  def repCoalg(x: Int) = Coalgebra[ListF[Int, ?], Int] { n =>
    if (n == 0) NilF else ConsF(x, n-1)
  }

  def pow(x: Int) = scheme.hylo[ListF[Int, ?], Int, Int](prodAlg.run, repCoalg(x).run)

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

  sealed trait LeafTreeF[F, A]
  case class LeafF[F, A](a: A) extends LeafTreeF[F, A]
  case class SplitF[F, A](l: F, r: F) extends LeafTreeF[F, A]

  type LeafTree[A] = Fix[LeafTreeF[?, A]]
  def leaf[A](a: A): LeafTree[A] = Fix[LeafTreeF[?, A]](LeafF(a))
  def split[A](l: LeafTree[A], r: LeafTree[A]): LeafTree[A] = Fix[LeafTreeF[?, A]](SplitF(l,r))

  implicit def LTFProjLT[A] = new Project[LeafTreeF[?, A], LeafTree[A]] {
    override def coalgebra = Fix.coalgebra[LeafTreeF[?, A]]
  }

  implicit def LTFEmbLT[A] = new Embed[LeafTreeF[?, A], LeafTree[A]] {
    override def algebra = Fix.algebra[LeafTreeF[?, A]]
  }

  implicit def ltFunctor[A]: Functor[LeafTreeF[?, A]] = new Functor[LeafTreeF[?, A]] {
    override def map[B, C](fa: LeafTreeF[B, A])(f: B => C): LeafTreeF[C, A] = fa match {
      case SplitF(l, r) => SplitF(f(l), f(r))
      case LeafF(a)     => LeafF(a)
    }
  }

  // 3.1 leaf-tree cata

  val treeSumAlg = Algebra[LeafTreeF[?, Int], Int] {
    case LeafF(a) => a
    case SplitF(l, r) => l + r
  }

  val treeSum = scheme.cata[LeafTreeF[?, Int], LeafTree[Int], Int](treeSumAlg)

  // 3.2 leaf-tree ana

  def fibTreeRec(n : Int): LeafTree[Int] = if (n<2) leaf(1) else split(fibTreeRec(n-1), fibTreeRec(n-2))

  val treeFibCoalg = Coalgebra[LeafTreeF[?, Int], Int] { n =>
    if (n<2) LeafF(1) else SplitF(n-1, n-2)
  }

  val fibTree = scheme.ana[LeafTreeF[?, Int], Int, LeafTree[Int]](treeFibCoalg)

  // 3.3 leaf-tree hylo

  val fib = scheme.hylo[LeafTreeF[?, Int], Int, Int](treeSumAlg.run, treeFibCoalg.run)

  // TODO ex 4

  // TODO ex 5

  // 3.4 merge sort

  val selectTreeCoalg = {
    val split = scheme.cata[ListF[Int, ?], List[Int], (List[Int], List[Int])](Algebra[ListF[Int, ?], (List[Int], List[Int])] {
      case NilF => (Nil, Nil)
      case ConsF(h, (l, r)) => (r, h::l)
    })
    Coalgebra[LeafTreeF[?, Int], List[Int]] {
      case Nil => LeafF(0) // unreachable
      case x::Nil => LeafF(x)
      case xs =>
        val (l, r) = split(xs)
        SplitF(l, r)
    }
  }

  val mergeAlg = {

    def merge(x: List[Int], y: List[Int]): List[Int] = (x,y) match {
      case (Nil, _) => y
      case (_, Nil) => x
      case (l::ls, r::rs) if l<r => l :: merge(ls, r::rs)
      case (l::ls, r::rs) => r :: merge(l::ls, rs)
    }

    Algebra[LeafTreeF[?, Int], List[Int]] {
      case LeafF(x) => List(x)
      case SplitF(l, r) => merge(l, r)
    }
  }

  def mergeSort(l : List[Int]) = l match {
    case Nil => Nil
    case xs =>
      val m = scheme.hylo[LeafTreeF[?, Int], List[Int], List[Int]](mergeAlg.run, selectTreeCoalg.run)
      m(xs)
  }

  // 4 binary trees

  def main(args: Array[String]): Unit = {

    println(prod(List(3,2,1)))
    println(revList(List(1,2,3,4)))

    println(count(3))
    println(fac(3))

    println(pow(2)(8))

    val unsorted = List(3,2,5,4,1)
    val intSort = insertionSort[Int]

    println(intSort(unsorted))
    println(straightSelSort(unsorted))
    println(bubbleSort(unsorted))
    println(bubbleSort2(unsorted))

    println(fibTreeRec(5))
    println(fibTree(5))

    println((0 to 10) map fib)

    println(mergeSort(unsorted))

  }


}
