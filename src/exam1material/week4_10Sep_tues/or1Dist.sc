// #Sireum #Logika
//@Logika: --manual --background type

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//First part proof of distributive law:
//p ∨ (q ∧ r)     is equivalent to
// (p ∨ q) ∧ (p ∨ r)


@pure def orDist1(p: B, q: B, r: B): Unit = {
  Deduce(
    //@formatter: off

    (p | (q & r)) |- ((p | q) & (p | r))
      Proof(

      //PROOF GOES HERE
      1 ( p | (q & r) ) by Premise,
      2 Subproof(
        3 Assume (p),
        4 (p | q) ORI1(3),
        5 (p or r) OrI1(3),
        6 ((p|q) & (p | r)) by AndI(4,5),

        //goal p or q
        // goal p or r
      ),
      7 Subproof(
        8 Assume (q & r),
        9 q by AndE1 (8),
        10 q by AndE1 (8),
      )
//goal ((p | q) & (p | r))
    )
    //@formatter:on
  )
}

// Subproofs must end with the same common end argument