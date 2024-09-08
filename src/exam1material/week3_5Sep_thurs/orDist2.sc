// #Sireum #Logika
//@Logika: --manual --background type

import org.sireum._

//Second part proof of distributive law:
//p ∨ (q ∧ r)     is equivalent to
// (p ∨ q) ∧ (p ∨ r)


@pure def orDist2(p: B, q: B, r: B): Unit = {
  Deduce(
    //@formatter: off

     ((p | q) & (p | r)) |- (p | (q & r))
      Proof(

     Proof(
       1 ((p | q) & (p | r)) by Premise,
       2 (P | q) by AndE1
     )


    )
    //@formatter:on
  )
}