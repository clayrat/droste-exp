import cats.free.Yoneda
import cats.{Functor, ~>}

import qq.droste._
import qq.droste.data.list._

import cats.Eval

// after https://jtobin.io/promorphisms-pre-post

object Pro {

  // TODO added to droste.Basis after 0.4.0
  implicit def drosteBasisForListF[A]: Basis[ListF[A, ?], List[A]] =
    Basis.Default[ListF[A, ?], List[A]](ListF.toScalaListAlgebra, ListF.fromScalaListCoalgebra)

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

  // TODO add to droste
  def prepro[F[_] : Functor, R, B](
                                    natTrans: F ~> F,
                                    algebra: Algebra[F, B],
                                  )(implicit project: Project[F, R]): R => B =
    kernel.hylo[Yoneda[F, ?], R, B](
      yfb => algebra.run(yfb.mapK(natTrans).run),
      project.coalgebra.run.andThen(Yoneda.apply[F, R])
    )

  def postpro[F[_] : Functor, A, R](
                                     natTrans: F ~> F,
                                     coalgebra: Coalgebra[F, A],
                                   )(implicit embed: Embed[F, R]): A => R =
    kernel.hylo[Yoneda[F, ?], A, R](
      yfb => embed.algebra.run(yfb.run),
      coalgebra.run.andThen(fa => Yoneda.apply[F, A](fa).mapK(natTrans))
    )

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
  final case class PrependF[A, B](head: Eval[A], tail: Eval[B]) extends StreamF[A, B]
  case object EmptyF extends StreamF[Nothing, Nothing]

  implicit def streamFunctor[A]: Functor[StreamF[A, ?]] = new Functor[StreamF[A, ?]] {
    override def map[B, C](fa: StreamF[A, B])(f: B => C): StreamF[A, C] = fa match {
      case EmptyF => EmptyF
      case PrependF(h, t) => PrependF(h, t.map(f))
    }
  }

  implicit def streamFEmbed[A] = new Embed[StreamF[A, ?], Stream[A]]{
    override def algebra = Algebra[StreamF[A, ?], Stream[A]] {
    case PrependF(head, tail) => head.value #:: tail.value
    case EmptyF => Stream.empty[A]
  }}

  val streamCoalg = Coalgebra[StreamF[Int, ?], Int] {
    n => PrependF(Eval.now(n), Eval.now(n + 1))
  }

  val smallS: StreamF[Int, ?] ~> StreamF[Int, ?] =
    λ[StreamF[Int, ?] ~> StreamF[Int, ?]] {
      case EmptyF => EmptyF
      case t@PrependF(h, _) if h.value <= 10 => t
      case PrependF(_, _) => EmptyF
    }

  val smallStream = postpro[StreamF[Int, ?], Int, Stream[Int]](smallS, streamCoalg)

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
