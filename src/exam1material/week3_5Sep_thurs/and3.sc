// #Sireum #Logika
//@Logika: --manual --background type

import org.sireum._

//Prove the sequent:
//p ∧ q ∧ r ⊢ q


@pure def and3(p: B, q: B, r: B): Unit = {
  Deduce(
    //@formatter: off

    (p & q & r) |- (q)
      Proof(
      1 ((p & q & r)) by Premise,
      2 (p & q) by AndE1(1), /// andE1 isolates the first side of the statement
      3 (q) by AndE2(2)
    )
    //@formatter:on
  )
}