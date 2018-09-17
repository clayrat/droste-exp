import cats.{Functor, ~>}

import qq.droste._
import data.list._
import scheme.zoo._

import cats.Eval

// after https://jtobin.io/promorphisms-pre-post

object Pro {

  val smallSumAlg = Algebra[ListF[Int, ?], Int] {
    case ConsF(h, t) => if (h <= 10) h + t else 0
    case NilF => 0
  }

  val smallLenAlg = Algebra[ListF[Int, ?], Int] {
    case ConsF(h, t) => if (h <= 10) 1 + t else 0
    case NilF => 0
  }

  val smallSum = scheme.cata[ListF[Int, ?], List[Int], Int](smallSumAlg)

  val smallLen = scheme.cata[ListF[Int, ?], List[Int], Int](smallLenAlg)

  // decoupled

  val sumAlg = Algebra[ListF[Int, ?], Int] {
    case ConsF(h, t) => h + t
    case NilF => 0
  }

  val lenAlg = Algebra[ListF[Int, ?], Int] {
    case ConsF(_, t) => 1 + t
    case NilF => 0
  }

  val small: ListF[Int, ?] ~> ListF[Int, ?] =
    λ[ListF[Int, ?] ~> ListF[Int, ?]] {
      case NilF => NilF
      case t@ConsF(h, _) if h <= 10 => t
      case ConsF(_, _) => NilF
    }

  val smallSumP = prepro[ListF[Int, ?], List[Int], Int](small, sumAlg)
  val smallLenP = prepro[ListF[Int, ?], List[Int], Int](small, lenAlg)

  // diy lazy lists
  sealed trait StreamF[+A, +B]
  final case class PrependF[A, B](head: A, tail: Eval[B]) extends StreamF[A, B]
  case object EmptyF extends StreamF[Nothing, Nothing]

  implicit def streamFunctor[A]: Functor[StreamF[A, ?]] = new Functor[StreamF[A, ?]] {
    override def map[B, C](fa: StreamF[A, B])(f: B => C): StreamF[A, C] = fa match {
      case EmptyF => EmptyF
      case PrependF(h, t) => PrependF(h, t.map(f))
    }
  }

  implicit def streamFEmbed[A] = new Embed[StreamF[A, ?], Stream[A]]{
    override def algebra = Algebra[StreamF[A, ?], Stream[A]] {
    case PrependF(head, tail) => head #:: tail.value
    case EmptyF => Stream.empty[A]
  }}

  val streamCoalg = Coalgebra[StreamF[Int, ?], Int] {
    n => PrependF(n, Eval.later(n + 1))
  }

  val smallS: StreamF[Int, ?] ~> StreamF[Int, ?] =
    λ[StreamF[Int, ?] ~> StreamF[Int, ?]] {
      case EmptyF => EmptyF
      case t@PrependF(h, _) if h <= 10 => t
      case PrependF(_, _) => EmptyF
    }

  val smallStream = postpro[StreamF[Int, ?], Int, Stream[Int]](streamCoalg, smallS)

  def main(args: Array[String]): Unit = {

    val l = List(1, 5, 20)

    println(smallSum(l))
    println(smallLen(l))

    val hun = (1 to 100).toList

    println(smallSumP(hun))
    println(smallLenP(hun))

    println(smallStream(3).toList)
  }

}
