// #Sireum #Logika
//@Logika: --manual --background disabled

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def not4(p: B, q: B, r: B): Unit = {
  Deduce(
    //@formatter: off

      ( !q __>: !p )|- ( p __>: q )
      Proof(
      1 (  !q __>: !p ) by Premise,
        2 SubProof
          3 Assume (p), // goal LHS
        4 SubProof(
         5 (Assume(!p),
            (!p) by ImplyE(1,5)
        ),
        //Try pbc doesn't fit, going with costumed deceit
        4 (q) by Imply// foal RHS

        )
//final needs an implies introduction
    )
    //@formatter:on
  )
}