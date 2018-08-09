import qq.droste._
import qq.droste.data._
import cats.implicits._

object Test {

  val natCoalgebra: Coalgebra[Option, BigDecimal] =
    Coalgebra(n => if (n > 0) Some(n - 1) else None)

  val fibAlgebra: CVAlgebra[Option, BigDecimal] = CVAlgebra {
    case Some(r1 :< Some(r2 :< _)) => r1 + r2
    case Some(_ :< None) => 1
    case None => 0
  }

  val fib: BigDecimal => BigDecimal =
    scheme.ghylo(
      fibAlgebra.gather(Gather.histo),
      natCoalgebra.scatter(Scatter.ana))

  val fibAlt: BigDecimal => BigDecimal =
    scheme.zoo.dyna(fibAlgebra, natCoalgebra)

  val fromNatAlgebra: Algebra[Option, BigDecimal] = Algebra {
    case Some(n) => n + 1
    case None => 0
  }

  // note: n is the fromNatAlgebra helper value from the previous level of recursion
  val sumSquaresAlgebra: RAlgebra[BigDecimal, Option, BigDecimal] = RAlgebra {
    case Some((n, value)) => value + (n + 1) * (n + 1)
    case None => 0
  }

  val sumSquares: BigDecimal => BigDecimal = scheme.ghylo(
    sumSquaresAlgebra.gather(Gather.zygo(fromNatAlgebra)),
    natCoalgebra.scatter(Scatter.ana))

  val fused: BigDecimal => (BigDecimal, BigDecimal) =
    scheme.ghylo(
      fibAlgebra.gather(Gather.histo) zip
        sumSquaresAlgebra.gather(Gather.zygo(fromNatAlgebra)),
      natCoalgebra.scatter(Scatter.ana))

}
