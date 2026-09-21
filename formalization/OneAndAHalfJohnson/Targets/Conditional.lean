module

public import OneAndAHalfJohnson.Targets.Main
public import OneAndAHalfJohnson.Targets.Base
public import OneAndAHalfJohnson.Thresholds

/-!
# Authorized conditional scope — target propositions, not completed proofs

The initial project may assume only the explicit AD21 classification and Hamada
rank specialization. These propositions fix that boundary. All remaining
finite geometry, counting, randomness, numerical analysis, and asymptotics
must be proved. In particular, none of the construction contracts in `Base`
may be smuggled in as an additional external premise.
-/

@[expose] public section
namespace OneAndAHalfJohnson.Targets

/-- The main goal with precisely the characteristic-specific external classification. -/
def ConditionalMainTheorem : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], AD21LowWeight p →
    ∀ δ ρ η : ℝ, 0 < δ → δ < 1 → johnson δ < ρ → ρ < gamma δ → 0 < η →
      AsymptoticConclusion p δ ρ η

/-- The small-distance existence goal may rely on AD21, but not on extra
unproved geometric or syndrome-existence assumptions. -/
def ConditionalSmallDistanceBase : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], AD21LowWeight p → SmallDistanceBase p

/-- The shortening theorem is a deduction from the permitted classification. -/
def ConditionalShorteningStructure : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], AD21LowWeight p → ShorteningStructure p

/-- The concrete goal may additionally rely on the specialized Hamada rank formula. -/
def ConditionalConcreteTheorem : Prop :=
  AD21LowWeight 2 → HamadaBinaryRank → ConcreteTheorem

/-- The quantitative assertion of Corollary 1.2 follows from the main assertion.
This is a logical reduction; the main assertion is proved in `MainTheorems/Main.lean`. -/
theorem uniqueDecoding_of_main (hmain : MainTheorem) : UniqueDecodingCounterexamples := by
  intro p hp δ ρ η hδ0 hδhi hρlo hρhi hη
  have hs0 := Real.sqrt_nonneg (5 : ℝ)
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hδ1 : δ < 1 := by nlinarith
  exact hmain p hp δ ρ η hδ0 hδ1 hρlo (lt_min_iff.mp hρhi).1 hη

end OneAndAHalfJohnson.Targets
