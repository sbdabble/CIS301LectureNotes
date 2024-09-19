// #Sireum #Logika
//@Logika: --manual --background disabled

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def not5(p: B, q: B, r: B): Unit = {
  Deduce(
    //@formatter: off

    ( !(!p | !q) ) |- ( p & q )
      Proof(
      1 (  !(!p | !q) ) by Premise,
      // p LHS
      2 SubProof(
        3 Assume(!p),
        4 (!p | !q) by OrI1(3),
        5 (F) by NegE(4,1)
      )
      6 p by PbC(5)


      // q RHS
      // (p&q) by AndI
    )
    //@formatter:on
  )
}

/// Sequents and arguments
// proving theorems
