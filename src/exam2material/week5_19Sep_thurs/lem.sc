// #Sireum #Logika
//@Logika: --manual --background disabled
/// Law of Excluded Middle
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._
//FIXME Proof


@pure def lem(p: B): Unit = {
  Deduce(
    //@formatter: off

    |- ( p | !p )
      Proof(
          1 SubProof(
            2 Assume(p)
            ),

            /// no implies, no top statement, etc.

            3 SubProof(
              4 Assume (!(pvq)),
              5 ((pvq)) by PbC(2,4),
              ),




    //@formatter:on
  )
}