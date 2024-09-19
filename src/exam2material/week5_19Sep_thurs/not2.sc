// #Sireum #Logika
//@Logika: --manual --background disabled

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def not2(p: B, q: B, r: B): Unit = {
  Deduce(
    //@formatter: off

    ( !p & !q ) |- ( !(p | q)  )
      Proof(
        1 (  !p & !q ) by Premise,

        //subproof
          //assume p V q
      2 SubProof(
        3 Assume (p|q), // top level operator is the negation in the conclusion
        4 SubProof(
          5 Assume (p),
          6 (!p) by AndE1(1),
          7 (F) by NegE (5,6)
        ),
        8 SubProof(
          9 Assume(q),
          10 (!q) by AndE2(1),
          11 (F) by NegE(9,10)
        ),
        // Never two parenthesis together, contradiction gove OrE
        12 (F) by OrE(3,4,8)

      ),
      13 (!(p|q)) by NegI(2)

          //goal: F
    )
    //@formatter:on
  )
}