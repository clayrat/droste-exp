import cats.Functor

import qq.droste._
import data._
import Basis._

// after https://jtobin.io/ad-via-recursion-schemes

object AD {

  sealed trait ExprF[+R]
  case object VarF extends ExprF[Nothing]
  case object ZeroF extends ExprF[Nothing]
  case object OneF extends ExprF[Nothing]
  case class NegateF[R](a: R) extends ExprF[R]
  case class SumF[R](a: R, b: R) extends ExprF[R]
  case class ProductF[R](a: R, b: R) extends ExprF[R]
  case class ExpF[R](a: R) extends ExprF[R]

  implicit def qtFunctor: Functor[ExprF] = new Functor[ExprF] {
    override def map[A, B](fa: ExprF[A])(f: A => B): ExprF[B] = fa match {
      case VarF => VarF
      case ZeroF => ZeroF
      case OneF => OneF
      case NegateF(a) => NegateF(f(a))
      case SumF(a, b) => SumF(f(a), f(b))
      case ProductF(a, b) => ProductF(f(a), f(b))
      case ExpF(a) => ExpF(f(a))
    }
  }

  type Expr = Fix[ExprF]
  val vr: Expr = Fix[ExprF](VarF)
  val zero: Expr = Fix[ExprF](ZeroF)
  val one: Expr = Fix[ExprF](OneF)
  def neg(x: Expr): Expr = Fix[ExprF](NegateF(x))
  def add(a: Expr, b: Expr): Expr = Fix[ExprF](SumF(a, b))
  def prod(a: Expr, b: Expr): Expr = Fix[ExprF](ProductF(a, b))
  def exp(x: Expr): Expr = Fix[ExprF](ExpF(x))

  def eval(x: Double): Expr => Double =
    scheme.cata(
      Algebra[ExprF, Double] {
        case VarF => x
        case ZeroF => 0
        case OneF => 1
        case NegateF(a) => -a
        case SumF(a, b) => a + b
        case ProductF(a, b) => a * b
        case ExpF(a) => Math.exp(a)
      }
    )

  val diff: Expr => Expr =
    scheme.zoo.para(
      RAlgebra[Expr, ExprF, Expr] {
        case VarF => one
        case ZeroF => zero
        case OneF => zero
        case NegateF((_, xd)) => neg(xd)
        case SumF((_, xd), (_, yd)) => add(xd, yd)
        case ProductF((x, xd), (y, yd)) => add(prod(x, yd), prod(xd, y))
        case ExpF((x, xd)) => prod(exp(x), xd)
      }
    )

  def ad(d: Double): Expr => (Double, Double) =
    scheme.cata(
      Algebra[ExprF, (Double, Double)] {
        case VarF => (d, 1)
        case ZeroF => (0, 0)
        case OneF => (1, 0)
        case NegateF((x, xd)) => (-x, -xd)
        case SumF((x, xd), (y, yd)) => (x + y, xd + yd)
        case ProductF((x, xd), (y, yd)) => (x * y, x * yd + xd * y)
        case ExpF((x, xd)) => (Math.exp(x), Math.exp(x) * xd)
      }
    )

  def fx(x : Expr): Expr =
    exp(add(x, neg(one)))

  def mkExpr(n: Int): Expr =
    List.fill(n)(fx _).foldLeft(vr)((e, f) => f(e))

  def main(args: Array[String]): Unit = {

    val input = List(0.0009, 1.0, 1.0001)

    val smallExpr = mkExpr(3)
    println(smallExpr)
    println(diff(smallExpr))
    println(input.map(i => eval(i)(smallExpr)))
    println(input.map(i => eval(i)(diff(smallExpr))))
    println(input.map(i => ad(i)(smallExpr)))

    val bigExpr = mkExpr(350)  // TODO larger values blow the stack
    println(input.map(i => eval(i)(diff(bigExpr))))
    println(input.map(i => ad(i)(bigExpr)))

  }

}
