// #Sireum #Logika
//@Logika: --manual --background disabled

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

import javax.swing.UIManager

//(c ∧ n) → t, h ∧ ¬s, h ∧ ¬(s ∨ c) → p ⊢ (n ∧ ¬t) → p


@pure def big1(c: B, n: B, t: B, h: B, s: B, p: B): Unit = {
  Deduce(
    //@formatter: off

    ( (c & n) __>: t, h & !s, h & !(s | c) __>: p ) |- ( n & !t __>: p )
      Proof(
        1 ( (c & n) __>: t ) by Premise,
        2 ( h & !s ) by Premise,
        3 ( h & !(s | c) __>: p ) by Premise,
      4 (h) by ANDE1(2SNAH)

    )
  )Assimw =Manager  //@formatter:on
  )
}

//Pre Conts, NegW

