import OneAndAHalfJohnson.MainTheorems.Concrete
import OneAndAHalfJohnson.MainTheorems.Main
import OneAndAHalfJohnson.MainTheorems.Shortening
import OneAndAHalfJohnson.MainTheorems.SyndromeSeparation

open OneAndAHalfJohnson

example : Targets.ConditionalMainTheorem := MainTheorems.conditionalMainTheorem
example : Targets.ConditionalSmallDistanceBase :=
  fun p _ h => MainTheorems.smallDistanceBase_of_AD21 p h
example : Targets.ConditionalShorteningStructure :=
  fun p _ h => MainTheorems.shorteningStructure_of_AD21 p h
example (p : ℕ) [Fact p.Prime] : Targets.SyndromeSeparation p :=
  MainTheorems.syndromeSeparation p
example (h : ∀ (p : ℕ) [Fact p.Prime], Targets.AD21LowWeight p) :
    Targets.UniqueDecodingCounterexamples := MainTheorems.uniqueDecodingCounterexamples_of_AD21 h

#print axioms MainTheorems.conditionalMainTheorem
#print axioms MainTheorems.smallDistanceBase_of_AD21
#print axioms MainTheorems.shorteningStructure_of_AD21
#print axioms MainTheorems.syndromeSeparation
#print axioms MainTheorems.uniqueDecodingCounterexamples_of_AD21
#print axioms MainTheorems.actual_unique_radius_of_AD21

example : Targets.ConditionalConcreteTheorem := MainTheorems.conditionalConcreteTheorem
#print axioms MainTheorems.conditionalConcreteTheorem
