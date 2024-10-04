// #Sireum #Logika
//@Logika: --manual --background disabled

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._

//∀ x (P(x) ⋀ Q(x))    equivalent to     (∀ x P(x)) ⋀ (∀ x Q(x))

@pure def all2part1[T](P: T=>B @pure, Q: T=>B @pure): Unit = {
  Deduce(
    //@formatter: on

    (∀((x: T) => (P(x) & Q(x))))
      |-
    (∀((x: T) => P(x))) & (∀((x: T) => Q(x)))
    Proof(
      1 (∀((x: T) => (P(x) & Q(x)))) by Premise,
      //first prove ∀((x: T) => P(x)))
      2 Let ((random: T) => SubProof(
        3 (P(random) & Q(random)) by AllE[T](1),
        4 (P(random)) by AndE1(3)
        //goal: P(random) yay we did it
      )),
      5 (∀((x: T) => P(x))) by AllI[T](2),


      // second prove (∀((x: T) => Q(x)))

      12 Let ((random2: T) => SubProof(
        13 (P(random2) & Q(random2)) by AllE[T](1),
        14 (Q(random2)) by AndE2(13)
        //goal: Q(random2) yay we did it
      )),
      15 (∀((x: T) => Q(x))) by AllI[T](12),
      100 ((∀((x: T) => P(x))) & (∀((x: T) => Q(x)))) by AndI(5,15)//Conclusion

    )
    //@formatter: on
  )
}

@pure def all2part2[T](P: T=>B @pure, Q: T=>B @pure): Unit = {
  Deduce(
    //@formatter: off

    (
      ∀((x: T) => P(x))) & (∀((x: T) => Q(x))
    )
      |-
    (
      ∀((x: T) => (P(x) & Q(x)))
    )
    Proof(
      1 ((∀((x: T) => P(x))) & (∀((x: T) => Q(x)))) by Premise,
      2 Let ((a: T) => SubProof(
        3 (∀((x: T) => P(x))) by AndE1(1),
        4 (∀((x: T) => Q(x))) by AndE2(1),
        5 (P(a)) by AllE[T](3),
        6 (Q(a)) by AllE[T](4),
        7 ((P(a) & Q(a))) by AndI(5,6)
      )),

      8 (∀((x: T) => (P(x) & Q(x)))) by AllI[T](2)

    )
    //@formatter:on
  )
}