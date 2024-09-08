// #Sireum #Logika
//@Logika: --manual --background type

import org.sireum._

//Prove the sequent:
//p, q, r ⊢ r ∧ (q ∧ p)


@pure def and2(p: B, q: B, r: B): Unit = {
  Deduce(
    //@formatter: off

    (p, q, r) |- (r & (q & p))
      Proof(

      1 (p) by Premise,
      2 (q) by Premise,
      3 (r) by Premise,
      4 (q & p) by AndIntroduction(2,1), ///Introducing an AND operation intot eh proof
      5 ((r & (q & p)) by AndI(3,4))


    )Ï
    //@formatter:on
  )
}