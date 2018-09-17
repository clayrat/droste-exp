import scala.language.higherKinds
import scala.util.{Failure, Success, Try}

import cats.Functor
import cats.instances.either._
import cats.instances.tuple._

import qq.droste._
import data.list._
import syntax.compose._

// after https://blog.sumtypeofway.com/recursion-schemes-part-v/

object Elgot {

  sealed trait Token

  object Token {
    case class Lit(i: Int) extends Token
    case class Op(f: (Int, Int) => Int) extends Token
  }

  def parseToken(s: String): Token = s match {
    case "+" => Token.Op(_ + _)
    case "-" => Token.Op(_ - _)
    case "*" => Token.Op(_ * _)
    case "/" => Token.Op(_ / _)
    case num => Token.Lit(num.toInt)
  }

  val parseRPNCoalg = Coalgebra[ListF[Token, ?], String] { s =>
    if (s.isEmpty) NilF
    else {
      val (x, rest) = s.span(_ != ' ')
      val token = parseToken(x)
      val newSeed = rest.dropWhile(_ == ' ')
      ConsF(token, newSeed)
    }
  }

  type Stack = List[Int]

  val evalRPNAlg = Algebra[ListF[Token, ?], Stack => Stack] {
    case NilF => identity
    case ConsF(Token.Lit(i), cont) => stack => cont(i :: stack)
    case ConsF(Token.Op(fn), cont) => {
      case a :: b :: rest => cont(fn(b, a) :: rest)
      case stack => throw new Exception(s"too few args on stack: $stack")
    }
  }

  def rpn(s: String): Stack =
    scheme.hylo[ListF[Token, ?], String, Stack => Stack](evalRPNAlg, parseRPNCoalg)
      .apply(s)
      .apply(Nil)

  // TODO add to Droste?

  type ElgotCoalgebra[E[_], F[_], A] = GCoalgebra[(E ∘ F)#λ, A, A]
  type ElgotAlgebra[E[_], F[_], A] = GAlgebra[(E ∘ F)#λ, A, A]

  object ElgotCoalgebra extends scala.AnyRef {
    def apply[E[_], F[_], A](f: scala.Function1[A, E[F[A]]]): ElgotCoalgebra[E, F, A] = GCoalgebra[(E ∘ F)#λ, A, A](f)
  }

  object ElgotAlgebra extends scala.AnyRef {
    def apply[E[_], F[_], A](f: scala.Function1[E[F[A]], A]): ElgotAlgebra[E, F, A] = GAlgebra[(E ∘ F)#λ, A, A](f)
  }

  def elgot[F[_] : Functor, A, B](
                                   algebra: Algebra[F, B],
                                   coalgebra: ElgotCoalgebra[Either[B, ?], F, A]
                                 ): A => B =
    kernel.hyloC[Either[B, ?], F, A, B](
      _.fold(identity[B], algebra.apply),
      coalgebra.run)

  def coelgot[F[_] : Functor, A, B](
                                   algebra: ElgotAlgebra[(A, ?), F, B],
                                   coalgebra: Coalgebra[F, A]
                                 ): A => B =
    kernel.hyloC[(A, ?), F, A, B](
      algebra.run,
      a => (a, coalgebra(a)))

  sealed trait Result

  object Result {
    case class Success(s: Stack) extends Result
    case class ParseError(e: String) extends Result
    case class TooFewArguments(s: Stack) extends Result
  }

  type Cont = Result => Result

  def safeToken(s: String): Either[Cont, Token] = s match {
    case "+" => Right(Token.Op(_ + _))
    case "-" => Right(Token.Op(_ - _))
    case "*" => Right(Token.Op(_ * _))
    case "/" => Right(Token.Op(_ / _))
    case num => Try(num.toInt) match {
      case Success(i) => Right(Token.Lit(i))
      case Failure(e) => Left(_ => Result.ParseError(e.getMessage))
    }
  }

  val safeParseRPNCoalg = ElgotCoalgebra[Either[Cont, ?], ListF[Token, ?], String] { s =>
    if (s.isEmpty) Right(NilF)
    else {
      val (x, rest) = s.span(_ != ' ')
      val newSeed = rest.dropWhile(_ == ' ')
      safeToken(x).map(token => ConsF(token, newSeed))
    }
  }

  val safeEvalRPNAlg = Algebra[ListF[Token, ?], Cont] {
    case ConsF(Token.Lit(i), cont) => {
      case Result.Success(stack) => cont(Result.Success(i :: stack))
      case res => res
    }
    case ConsF(Token.Op(fn), cont) => {
      case Result.Success(a :: b :: rest) => cont(Result.Success(fn(b, a) :: rest))
      case Result.Success(st) => Result.TooFewArguments(st)
      case res => res
    }
    case _ => identity
  }

  def safeRpn(s: String): Result =
    elgot[ListF[Token, ?], String, Cont](safeEvalRPNAlg, safeParseRPNCoalg)
      .apply(s)
      .apply(Result.Success(Nil))

  def main(args: Array[String]): Unit = {

    println(rpn("15 7 1 1 + - / 3 * 2 1 1 + + -"))

    println(safeRpn("15 7 1 1 + - / 3 * 2 1 1 + + -"))

    println(safeRpn("1 +"))

    println(safeRpn("1 aa"))

  }

}
