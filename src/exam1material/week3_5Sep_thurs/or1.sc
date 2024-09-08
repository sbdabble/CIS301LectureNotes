// #Sireum #Logika
//@Logika: --manual --background type

import org.sireum._

//Prove OR is commutative:
//p ∨ q ⊢ q ∨ p


@pure def or1(p: B, q: B): Unit = {
  Deduce(
    //@formatter: off

    (p | q) |- (q | p)
      Proof(

      1 ((p | q)) by Premise,
      2 SubProof2(
      3 (Assume(p)),
      4 (q|p) by OrI2(3)),
      5 SubProof3(
        5(q),
        (q| 0))
    )
    (q|p) by OrE()by OrI2(1, 3; 5




  )
    //@formatter:on
  )
}

can only prov ronbaalid w a  proof table