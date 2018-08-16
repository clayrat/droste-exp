import qq.droste._
import data._
import list._
import Basis._

import cats.Functor

import scala.math.Ordering

// following Augusteijn, "Sorting morphisms" (https://pdfs.semanticscholar.org/87b2/6d98d4c3e2f7983d0b79fba83c1f359abe25.pdf)

object Sort {

  // TODO added to droste.Basis after 0.4.0
    implicit def drosteBasisForListF[A]: Basis[ListF[A, ?], List[A]] =
      Basis.Default[ListF[A, ?], List[A]](ListF.toScalaListAlgebra, ListF.fromScalaListCoalgebra)

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
    if (n == 0) NilF else ConsF(n, n - 1)
  }

  val count = scheme.ana[ListF[Int, ?], Int, List[Int]](countCoalg)

  // TODO ex 2

  // 2.3 hylo

  val fac = scheme.hylo[ListF[Int, ?], Int, Int](prodAlg, countCoalg)

  // ex 3

  def repCoalg(x: Int) = Coalgebra[ListF[Int, ?], Int] { n =>
    if (n == 0) NilF else ConsF(x, n - 1)
  }

  def pow(x: Int) = scheme.hylo[ListF[Int, ?], Int, Int](prodAlg, repCoalg(x))

  // 2.4 insertion sort

  def insert[A: Ordering](x: A, l: List[A]): List[A] = {
    val ord = implicitly[Ordering[A]]
    l match {
      case Nil => List(x)
      case h :: t => if (ord.lt(x, h)) x :: h :: t else h :: insert(x, t)
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
    case l@_ :: _ => extract(l)
  }

  def selectionSort(extract: List[Int] => ListF[Int, List[Int]]) =
    scheme.ana[ListF[Int, ?], List[Int], List[Int]](selectCoalg(extract))

  // 2.5.1 straight

  def selExtract(l: List[Int]): ListF[Int, List[Int]] = {
    def remove(x: Int, m: List[Int]): List[Int] = m match {
      case Nil => Nil
      case h :: t if x == h => t
      case h :: t => h :: remove(x, t)
    }

    val m = l.min
    ConsF(m, remove(m, l))
  }

  def straightSelSort = selectionSort(selExtract)

  // 2.5.2 bubble

  def bubble(l: List[Int]): ListF[Int, List[Int]] = l match {
    case Nil => NilF // unreachable
    case h :: Nil => ConsF(h, Nil)
    case h :: t =>
      val ConsF(y, m) = bubble(t)
      if (h < y) ConsF(h, y :: m) else ConsF(y, h :: m)
  }

  def bubbleSort = selectionSort(bubble)

  val bubbleAlg = Algebra[ListF[Int, ?], ListF[Int, List[Int]]] {
    case NilF => NilF // unreachable
    case ConsF(h, NilF) => ConsF(h, Nil)
    case ConsF(h, ConsF(i, t)) => if (h < i) ConsF(h, i :: t) else ConsF(i, h :: t)
  }

  def bubbleSort2 = selectionSort(
    scheme.cata[ListF[Int, ?], List[Int], ListF[Int, List[Int]]](bubbleAlg)
  )

  // 3 leaf trees

  sealed trait LeafTreeF[F, A]
  case class LeafF[F, A](a: A) extends LeafTreeF[F, A]
  case class SplitF[F, A](l: F, r: F) extends LeafTreeF[F, A]

  type LeafTree[A] = Fix[LeafTreeF[?, A]]
  def leaf[A](a: A): LeafTree[A] = Fix[LeafTreeF[?, A]](LeafF(a))
  def split[A](l: LeafTree[A], r: LeafTree[A]): LeafTree[A] = Fix[LeafTreeF[?, A]](SplitF(l, r))

  // not sure why is this needed
  implicit def drosteBasisForLeafTreeF[A]: Basis[LeafTreeF[?, A], LeafTree[A]] =
    drosteBasisForFix[LeafTreeF[?, A]]

  implicit def ltFunctor[A]: Functor[LeafTreeF[?, A]] = new Functor[LeafTreeF[?, A]] {
    override def map[B, C](fa: LeafTreeF[B, A])(f: B => C): LeafTreeF[C, A] = fa match {
      case SplitF(l, r) => SplitF(f(l), f(r))
      case LeafF(a) => LeafF(a)
    }
  }

  // 3.1 leaf-tree cata

  val treeSumAlg = Algebra[LeafTreeF[?, Int], Int] {
    case LeafF(a) => a
    case SplitF(l, r) => l + r
  }

  val treeSum = scheme.cata[LeafTreeF[?, Int], LeafTree[Int], Int](treeSumAlg)

  // 3.2 leaf-tree ana

  def fibTreeRec(n: Int): LeafTree[Int] = if (n < 2) leaf(1) else split[Int](fibTreeRec(n - 1), fibTreeRec(n - 2))

  val treeFibCoalg = Coalgebra[LeafTreeF[?, Int], Int] { n =>
    if (n < 2) LeafF(1) else SplitF(n - 1, n - 2)
  }

  val fibTree = scheme.ana[LeafTreeF[?, Int], Int, LeafTree[Int]](treeFibCoalg)

  // 3.3 leaf-tree hylo

  val fib = scheme.hylo[LeafTreeF[?, Int], Int, Int](treeSumAlg, treeFibCoalg)

  // TODO ex 4

  // TODO ex 5

  // 3.4 merge sort

  val selectTreeCoalg = {
    val split = scheme.cata[ListF[Int, ?], List[Int], (List[Int], List[Int])](Algebra[ListF[Int, ?], (List[Int], List[Int])] {
      case NilF => (Nil, Nil)
      case ConsF(h, (l, r)) => (r, h :: l)
    })
    Coalgebra[LeafTreeF[?, Int], List[Int]] {
      case Nil => LeafF(0) // unreachable
      case x :: Nil => LeafF(x)
      case xs =>
        val (l, r) = split(xs)
        SplitF(l, r)
    }
  }

  val mergeAlg = {

    def merge(x: List[Int], y: List[Int]): List[Int] = (x, y) match {
      case (Nil, _) => y
      case (_, Nil) => x
      case (l :: ls, r :: rs) if l < r => l :: merge(ls, r :: rs)
      case (l :: ls, r :: rs) => r :: merge(l :: ls, rs)
    }

    Algebra[LeafTreeF[?, Int], List[Int]] {
      case LeafF(x) => List(x)
      case SplitF(l, r) => merge(l, r)
    }
  }

  def mergeSort(l: List[Int]) = l match {
    case Nil => Nil
    case xs =>
      val m = scheme.hylo[LeafTreeF[?, Int], List[Int], List[Int]](mergeAlg, selectTreeCoalg)
      m(xs)
  }

  // 4 binary trees

  sealed trait BinTreeF[+F, +A]
  case object TipF extends BinTreeF[Nothing, Nothing]
  case class BranchF[F, A](x: A, l: F, r: F) extends BinTreeF[F, A]

  type BinTree[A] = Fix[BinTreeF[?, A]]
  def tip[A](a: A): BinTree[A] = Fix[BinTreeF[?, A]](TipF)
  def branch[A](x: A, l: BinTree[A], r: BinTree[A]): BinTree[A] = Fix[BinTreeF[?, A]](BranchF(x, l, r))

  implicit def btFunctor[A]: Functor[BinTreeF[?, A]] = new Functor[BinTreeF[?, A]] {
    override def map[B, C](fa: BinTreeF[B, A])(f: B => C): BinTreeF[C, A] = fa match {
      case BranchF(x, l, r) => BranchF(x, f(l), f(r))
      case TipF => TipF
    }
  }

  // not sure why is this needed again
  implicit def drosteBasisForBinTreeF[A]: Basis[BinTreeF[?, A], BinTree[A]] =
    drosteBasisForFix[BinTreeF[?, A]]

  // ex 6

  val btreeProdAlg = Algebra[BinTreeF[?, Int], Int] {
    case TipF => 1
    case BranchF(x, l, r) => x * l * r
  }

  val countBTreeCoalg = Coalgebra[BinTreeF[?, Int], (Int, Int)] {
    case (lo, hi) if lo < hi =>
      val mid = (lo + hi) / 2
      BranchF(mid, (lo, mid), (mid + 1, hi))
    case _ => TipF
  }

  def facBT(n: Int): Int = {
    val facRange = scheme.hylo[BinTreeF[?, Int], (Int, Int), Int](btreeProdAlg, countBTreeCoalg)
    facRange(1, n + 1)
  }

  // ex 7

  def replBTCoalg(x: Int) = Coalgebra[BinTreeF[?, Int], Int] { n =>
    if (n > 0) {
      val l = (n - 1) / 2
      val r = n - 1 - l
      BranchF(x, l, r)
    } else TipF
  }

  def powBT(x: Int) = scheme.hylo[BinTreeF[?, Int], Int, Int](btreeProdAlg, replBTCoalg(x))

  // TODO ex 8

  // 4.4 quicksort

  val btJoinAlg = Algebra[BinTreeF[?, Int], List[Int]] {
    case TipF => Nil
    case BranchF(x, l, r) => l ++ (x :: r)
  }

  val btSplitCoalg = Coalgebra[BinTreeF[?, Int], List[Int]] {
    case Nil => TipF
    case x :: l =>
      val (s, g) = l.partition(_ < x)
      BranchF(x, s, g)
  }

  val quicksort = scheme.hylo[BinTreeF[?, Int], List[Int], List[Int]](btJoinAlg, btSplitCoalg)

  // TODO ex 9

  // 4.5 heap sort

  def combine(lt: BinTree[Int], rt: BinTree[Int]): BinTree[Int] =
    (Fix.un[BinTreeF[?, Int]](lt), Fix.un[BinTreeF[?, Int]](rt)) match {
      case (t, TipF) => Fix.apply[BinTreeF[?, Int]](t)
      case (TipF, t) => Fix.apply[BinTreeF[?, Int]](t)
      case (BranchF(x, l, r), c@BranchF(y, _, _)) if x < y => branch[Int](x, l, combine(r, Fix.apply[BinTreeF[?, Int]](c)))
      case (b, BranchF(y, s, t)) => branch[Int](y, combine(Fix.apply[BinTreeF[?, Int]](b), s), t)
    }

  val extractCoalg = Coalgebra[ListF[Int, ?], BinTree[Int]] { bt =>
    Fix.un[BinTreeF[?, Int]](bt) match {
      case TipF => NilF
      case BranchF(x, l, r) => ConsF(x, combine(l, r))
    }
  }

  val heap2list = scheme.ana[ListF[Int, ?], BinTree[Int], List[Int]](extractCoalg)

  def bubble(h: Int, t: List[Int]): (Int, List[Int], List[Int]) = {
    val bubbleAlg = Algebra[ListF[Int, ?], (Int, List[Int], List[Int])] {
      case NilF => (h, Nil, Nil)
      case ConsF(x, (y, l, r)) => if (x < y) (x, y :: r, l) else (y, x :: r, l)
    }
    val bbl = scheme.cata[ListF[Int, ?], List[Int], (Int, List[Int], List[Int])](bubbleAlg)
    bbl(t)
  }

  val decomposeCoalg = Coalgebra[BinTreeF[?, Int], List[Int]] {
    case Nil => TipF
    case x :: xs =>
      val (a, b, c) = bubble(x, xs)
      BranchF(a, b, c)
  }

  val list2heap = scheme.ana[BinTreeF[?, Int], List[Int], BinTree[Int]](decomposeCoalg)

  val heapsort = list2heap andThen heap2list

  // 5.2 insert as paramorphism

  def combineRAlg(x: Int) = RAlgebra[List[Int], ListF[Int, ?], List[Int]] {
    case NilF => List(x)
    case ConsF(h, (l, _)) if x < h => x :: h :: l
    case ConsF(h, (_, rec)) => h :: rec
  }

  def insertP(x: Int) = scheme.zoo.para[ListF[Int, ?], List[Int], List[Int]](combineRAlg(x))

  def insertAlg2[A: Ordering] = Algebra[ListF[Int, ?], List[Int]] {
    case NilF => Nil
    case ConsF(h, t) => insertP(h)(t)
  }

  val insertionSort2 = scheme.cata[ListF[Int, ?], List[Int], List[Int]](insertAlg2)

  // 5.3 remove as paramorphism

  def selExtractP(l: List[Int]): ListF[Int, List[Int]] = {

    def removeRAlg(x: Int) = RAlgebra[List[Int], ListF[Int, ?], List[Int]] {
      case NilF => Nil
      case ConsF(h, (l, _)) if x == h => l
      case ConsF(h, (_, rec)) => h :: rec
    }

    def remove(x: Int) = scheme.zoo.para[ListF[Int, ?], List[Int], List[Int]](removeRAlg(x))

    val m = l.min
    ConsF(m, remove(m)(l))
  }

  def straightSelSort2 = selectionSort(selExtractP)

  def main(args: Array[String]): Unit = {

    val unsorted = List(3, 2, 5, 4, 1)

    println(prod(List(3, 2, 1)))

    println(revList(List(1, 2, 3, 4)))

    println(count(10))
    println(fac(10))

    println(pow(2)(8))

    val intSort = insertionSort[Int]

    println(intSort(unsorted))
    println(straightSelSort(unsorted))
    println(bubbleSort(unsorted))
    println(bubbleSort2(unsorted))

    println(fibTreeRec(5))
    println(fibTree(5))

    println((0 to 10) map fib)

    println(mergeSort(unsorted))

    println(facBT(10))
    println(powBT(2)(8))

    println(quicksort(unsorted))

    println(heapsort(unsorted))

    println(insertionSort2(unsorted))

    println(straightSelSort2(unsorted))

  }


}
