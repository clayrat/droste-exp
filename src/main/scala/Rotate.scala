import scala.language.higherKinds

import cats.Functor

import qq.droste._
import data._
import Basis._

// after https://jtobin.io/rotating-squares

object Rotate {

  sealed trait QuadTreeF[+A, +R]
  case class NodeF[A, R](ul: R, ur: R, lr: R, ll: R) extends QuadTreeF[A, R]
  case class LeafF[A, R](a: A) extends QuadTreeF[A, R]
  case object EmptyF extends QuadTreeF[Nothing, Nothing]

  implicit def qtFunctor[A]: Functor[QuadTreeF[A, ?]] = new Functor[QuadTreeF[A, ?]] {
    override def map[B, C](fa: QuadTreeF[A, B])(f: B => C): QuadTreeF[A, C] = fa match {
      case EmptyF => EmptyF
      case LeafF(a) => LeafF(a)
      case NodeF(ul, ur, lr, ll) => NodeF(f(ul), f(ur), f(lr), f(ll))
    }
  }

  type QuadTree[A] = Fix[QuadTreeF[A, ?]]

  def node[A](ul: QuadTree[A], ur: QuadTree[A], lr: QuadTree[A], ll: QuadTree[A]): QuadTree[A] =
    Fix[QuadTreeF[A, ?]](NodeF(ul, ur, lr, ll))

  def leaf[A](a: A): QuadTree[A] =
    Fix[QuadTreeF[A, ?]](LeafF(a))

  def empty[A]: QuadTree[A] =
    Fix[QuadTreeF[A, ?]](EmptyF)

  implicit def drosteBasisForQuadTreeF[A] =
    drosteBasisForFix[QuadTreeF[A, ?]]

  def toMatrix[A]: QuadTree[A] => List[List[A]] =
    scheme.cata[QuadTreeF[A, ?], QuadTree[A], List[List[A]]](
      Algebra[QuadTreeF[A, ?], List[List[A]]] {
        case NodeF(ul, ur, lr, ll) =>
          val u = ul.zip(ur).map { case (l, r) => l ++ r }
          val d = ll.zip(lr).map { case (l, r) => l ++ r }
          u ++ d
        case LeafF(a) => List(List(a))
        case EmptyF => Nil
      }
    )

  def printQT[A](f: A => Char, qtb: QuadTree[A]): Unit =
    toMatrix[A](qtb)
      .foreach(row => println(row.map(f).mkString))

  val tree: QuadTree[Boolean] = {
    val ul = node[Boolean](leaf(false), leaf(true), leaf(false), leaf(false))
    val ur = node[Boolean](leaf(false), leaf(false), leaf(false), leaf(true))
    val lr = node[Boolean](leaf(true), leaf(false), leaf(false), leaf(false))
    val ll = node[Boolean](leaf(true), leaf(true), leaf(false), leaf(false))
    node[Boolean](ul, ur, lr, ll)
  }

  def rotate[A] = scheme.cata[QuadTreeF[A, ?], QuadTree[A], QuadTree[A]](
    Algebra[QuadTreeF[A, ?], QuadTree[A]] {
      case NodeF(ul, ur, lr, ll) => node[A](ll, ul, ur, lr)
      case LeafF(a) => leaf(a)
      case EmptyF => empty[A]
    }
  )

  def builderCoalg[A] = Coalgebra[QuadTreeF[A, ?], List[A]] {
    case Nil => EmptyF
    case x::Nil => LeafF(x)
    case xs =>
      val (ab, cd) = xs.splitAt(xs.length / 2)
      val (a, b) = ab.splitAt(ab.length / 2)
      val (c, d) = cd.splitAt(cd.length / 2)
      NodeF(a, b, c, d)
  }

  def consumerAlg[A] = Algebra[QuadTreeF[A, ?], List[A]] {
    case EmptyF => Nil
    case LeafF(a) => List(a)
    case NodeF(ul, ur, lr, ll) => ll ++ ul ++ ur ++ lr
  }

  def rotateList[A] = scheme.hylo[QuadTreeF[A, ?], List[A], List[A]](consumerAlg, builderCoalg)

  def main(args: Array[String]): Unit = {

    val b2c: Boolean => Char = if (_) 'x' else '.'

    printQT[Boolean](b2c, tree)

    println

    printQT[Boolean](b2c, rotate[Boolean](tree))

    println

    println(rotateList(List(1,2,3,4)))

  }


}
