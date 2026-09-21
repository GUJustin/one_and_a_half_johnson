module

public import OneAndAHalfJohnson.Basic

/-!
# Main theorem contracts

Theorem 1.1 (p. 3), restated as Theorem 3.1 (p. 7), and Theorem 4.1
(pp. 15–16) of [ePrint 2026/1894](https://eprint.iacr.org/2026/1894.pdf).

These are fully defined propositions, not theorem proofs or axioms.
The asymptotic contracts are proved in `MainTheorems/Main.lean`; the concrete
contract is proved in `MainTheorems/Concrete.lean`. The
asymptotic contract expands the paper's uniform O(1/s) into one constant M
chosen before s and N. A single code and single pair f,g are chosen before
all exceptional coefficients. Codes are explicitly nonzero, avoiding the
zero-code convention for minimum distance. The finite-field formulation is
invariant under choice of field model: it quantifies over every field of the
specified cardinality.
-/

@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson.Targets

/-- Full quantitative conclusion for fixed p, δ, ρ, η. All constants are
chosen before the growing exponent and the block length. -/
def AsymptoticConclusion (p : ℕ) (δ ρ η : ℝ) : Prop :=
  ∃ A c M : ℝ, 0 < A ∧ 0 < c ∧ 0 < M ∧
    ∃ D s₀ : ℕ, 1 ≤ D ∧ 1 ≤ s₀ ∧
      ∀ s : ℕ, s₀ ≤ s → ∀ N : ℕ,
        A * (s : ℝ) ^ D ≤ (N : ℝ) → N < p ^ s →
        ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F],
          Fintype.card F = p ^ s →
          ∃ (C : Submodule F (Fin N → F)) (f g : Fin N → F),
            C ≠ ⊥ ∧
            |relativeDistance C - δ| < η ∧
            |rate C - (1 - relativeDistance C)| ≤ M / (s : ℝ) ∧
            Far C f (gamma δ) ∧ Far C g (gamma δ) ∧
            c * Fintype.card F ≤ ((exceptional C f g ρ).card : ℝ)

/-- Main theorem contract, proved conditionally in `MainTheorems/Main.lean`. -/
def MainTheorem : Prop :=
  ∀ p : ℕ, p.Prime → ∀ δ ρ η : ℝ,
    0 < δ → δ < 1 → johnson δ < ρ → ρ < gamma δ → 0 < η →
    AsymptoticConclusion p δ ρ η

/-- Corollary 1.2 quantitative target, including all prime characteristics. -/
def UniqueDecodingCounterexamples : Prop :=
  ∀ p : ℕ, p.Prime → ∀ δ ρ η : ℝ,
    0 < δ → δ < 3 - Real.sqrt 5 →
    johnson δ < ρ → ρ < min (gamma δ) (δ / 2) → 0 < η →
    AsymptoticConclusion p δ ρ η

/-- Exact concrete existence target. Decimal bounds are exact real rationals;
the block length, alphabet size, and exceptional count are integers. -/
def ConcreteTheorem : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F],
    Fintype.card F = 2 ^ 128 →
    ∃ (C : Submodule F (Fin (2 ^ 36) → F)) (f g : Fin (2 ^ 36) → F),
      C ≠ ⊥ ∧
      4419 / 10000 < relativeDistance C ∧ relativeDistance C < 4511 / 10000 ∧
      5410875 / 10000000 < rate C ∧ rate C < 5502875 / 10000000 ∧
      Far C f (22945 / 100000) ∧ Far C g (22945 / 100000) ∧
      (1816 / 10000 : ℝ) < relativeDistance C / 2 ∧
      18049720589484545 ≤ (exceptional C f g (1816 / 10000)).card

end OneAndAHalfJohnson.Targets
