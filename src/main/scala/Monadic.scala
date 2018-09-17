import scala.language.higherKinds

import cats.data.{Kleisli, ReaderT}
import cats.{Applicative, Monad, Traverse}
import cats.instances.either._
import cats.instances.list._
import cats.syntax.functor._

import qq.droste._
import data._
import list._

import util.DefaultTraverse

// after https://jtobin.io/monadic-recursion-schemes

object Monadic {

  def filterM[M[_], A](fm: A => M[Boolean])(implicit M: Monad[M]): List[A] => M[List[A]] =
    scheme.cataM[M, ListF[A, ?], List[A], List[A]](
      AlgebraM[M, ListF[A, ?], List[A]] {
        case NilF => M.pure(Nil)
        case ConsF(h, t) => fm(h).map(if (_) h :: t else t)
      }
    )

  def powerset[A](xs: List[A]): List[List[A]] =
    filterM[List,A](_ => List(true, false)).apply(xs)

  sealed trait ExprF[F]
  case class VarF[F](s: String) extends ExprF[F]
  case class LitF[F](i: Int) extends ExprF[F]
  case class AddF[F](l: F, r: F) extends ExprF[F]

  type Expr = Fix[ExprF[?]]
  def vr(s: String): Expr = Fix[ExprF](VarF(s))
  def lit(i: Int): Expr = Fix[ExprF](LitF(i))
  def add(l: Expr, r: Expr): Expr = Fix[ExprF](AddF(l, r))

  // TODO use derivation in 0.5
  implicit def exTraverse: Traverse[ExprF] = new DefaultTraverse[ExprF] {
    override def traverse[G[_], A, B](fa: ExprF[A])(f: A => G[B])(implicit G: Applicative[G]): G[ExprF[B]] = fa match {
      case VarF(v) => G.pure(VarF(v))
      case LitF(i) => G.pure(LitF(i))
      case AddF(l, r) => G.map2(f(l), f(r))(AddF.apply)
    }
  }

  val evalBad = scheme.cata[ExprF, Expr, Int](
    Algebra[ExprF, Int] {
      case VarF(_) => throw new Exception("free variable in expression")
      case LitF(j) => j
      case AddF(i, j) => i + j
    }
  )

  sealed trait Error
  case class FreeVar(v: String) extends Error

  val evalM = scheme.cataM[Either[Error, ?], ExprF, Expr, Int](
    AlgebraM[Either[Error, ?], ExprF, Int] {
      case VarF(v) => Left(FreeVar(v))
      case LitF(j) => Right(j)
      case AddF(i, j) => Right(i + j)
    }
  )

  // TODO why
  implicit val readEithMonad: cats.Monad[ReaderT[Either[Error, ?], Map[String, Int], ?]] =
    Kleisli.catsDataMonadForKleisli[Either[Error, ?], Map[String, Int]]

  val evalRM = scheme.cataM[ReaderT[Either[Error, ?], Map[String, Int], ?], ExprF, Expr, Int](
    AlgebraM[ReaderT[Either[Error, ?], Map[String, Int], ?], ExprF, Int] {
      case VarF(v) =>
        ReaderT.ask[Either[Error, ?], Map[String, Int]].flatMap(
          _.get(v)
            .fold(ReaderT.liftF[Either[Error, ?], Map[String, Int], Int](Left(FreeVar(v))))(ReaderT.pure[Either[Error, ?], Map[String, Int], Int])
        )

      case LitF(j) => ReaderT.pure[Either[Error, ?], Map[String, Int], Int](j)
      case AddF(i, j) => ReaderT.pure[Either[Error, ?], Map[String, Int], Int](i + j)
    }
  )

  def main(args: Array[String]): Unit = {

    println(powerset(List(1,2,3)))

    println(evalBad(add(lit(1), lit(2))))

    println(evalM(add(lit(1), vr("a"))))

    val open = add(vr("x"), vr("y"))

    val res = evalRM(open).run(Map("x" -> 1))
    println(res)

    val res2 = evalRM(open).run(Map("x" -> 1, "y" -> 2))
    println(res2)

  }

}
