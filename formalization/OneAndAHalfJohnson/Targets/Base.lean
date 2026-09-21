module

public import OneAndAHalfJohnson.Targets.External
public import OneAndAHalfJohnson.ScalarExtension

/-!
# Base-construction contracts

Concrete target statements for Lemmas 3.2, 3.4, and 3.5 of ePrint 2026/1894.
Only the separate AD21 classification and Hamada rank premises are authorized
external assumptions. The propositions below are proved in the corresponding
`MainTheorems` modules; they are not additional external assumptions.
-/

@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson.Targets
open Geometry

/-- Number of points in the base coordinate space. -/
def baseLength (Q m : ℕ) : ℕ := (Q ^ m - 1) / (Q - 1)

/-- Number of points in a codimension-two subspace. -/
def incidenceWeight (Q m : ℕ) : ℕ := (Q ^ (m - 2) - 1) / (Q - 1)

/-- Lemma 3.2 (p. 7): one positive count constant and one dimension threshold
work uniformly over all subsequent dimensions and all field models. -/
def SmallDistanceBase (p : ℕ) : Prop :=
  ∀ a : ℕ, 1 ≤ a → 32 < p ^ a → p ^ a ≠ 49 → p ^ a ≠ 121 →
    ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, 4 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      ∀ (E : Type) [Field E] [Fintype E] [DecidableEq E],
        Fintype.card E = (p ^ a) ^ (2 * m) →
        ∃ (C : Submodule E (Fin (baseLength (p ^ a) m) → E))
          (f g : Fin (baseLength (p ^ a) m) → E),
          C ≠ ⊥ ∧
          (lowWeightCutoff (p ^ a) m : ℝ) / baseLength (p ^ a) m < relativeDistance C ∧
          relativeDistance C < 3 * (incidenceWeight (p ^ a) m : ℝ) / baseLength (p ^ a) m ∧
          Far C f (4 * (incidenceWeight (p ^ a) m : ℝ) / (3 * baseLength (p ^ a) m)) ∧
          Far C g (4 * (incidenceWeight (p ^ a) m : ℝ) / (3 * baseLength (p ^ a) m)) ∧
          c * Fintype.card E ≤ ((exceptional C f g
            ((incidenceWeight (p ^ a) m : ℝ) / baseLength (p ^ a) m)).card : ℝ)

/-- Lemma 3.4 (pp. 8–9): the same pair must contain the whole shortening,
not merely one separately chosen pair for each low-weight word. -/
def ShorteningStructure (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [CharP K p],
    ∀ a : ℕ, Fintype.card K = p ^ a →
    32 < Fintype.card K → Fintype.card K ≠ 49 → Fintype.card K ≠ 121 →
    ∃ m₀ : ℕ, 4 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      (∀ S : Finset (Point K m), S.card ≤ lowWeightCutoff (Fintype.card K) m →
        ∃ W W' : CodimTwo K m,
          incidenceSpan K (ZMod p) m ⊓ supportedCode (S : Set (Point K m)) ≤
            Submodule.span (ZMod p) {incidenceWord (ZMod p) W, incidenceWord (ZMod p) W'}) ∧
      (∀ S : Finset (Point K m), (S.card : ℝ) ≤ 4 *
          (incidenceWeight (Fintype.card K) m : ℝ) / 3 →
        ∃ W : CodimTwo K m,
          incidenceSpan K (ZMod p) m ⊓ supportedCode (S : Set (Point K m)) ≤
            Submodule.span (ZMod p) {incidenceWord (ZMod p) W}) ∧
      Code.dist (incidenceSpan K (ZMod p) m : Set (Point K m → ZMod p)) =
        incidenceWeight (Fintype.card K) m

/-- An actual incidence vector as an element of the extended ambient code. -/
def extendedIncidence {p : ℕ} [Fact p.Prime]
    {K E : Type} [Field K] [Field E] [Algebra (ZMod p) E]
    {m : ℕ} (W : CodimTwo K m) :
    extendCode (K := E) (incidenceSpan K (ZMod p) m) :=
  ⟨embedWord (incidenceWord (ZMod p) W),
    Submodule.subset_span ⟨_, incidenceWord_mem_span W, rfl⟩⟩

/-- Lemma 3.5 (pp. 10–11), with the needed `m ≥ 4` made explicit.
The syndrome map has the paper's domain: the actual extended ambient code. -/
def SyndromeSeparation (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [CharP K p],
    ∀ a : ℕ, Fintype.card K = p ^ a →
    32 < Fintype.card K → Fintype.card K ≠ 49 → Fintype.card K ≠ 121 →
    ∀ m : ℕ, 4 ≤ m →
      ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E],
        Fintype.card E = (Fintype.card K) ^ (2 * m) →
        ∃ ψ : extendCode (K := E) (incidenceSpan K (ZMod p) m) →ₗ[E] (E × E),
          (∀ W : CodimTwo K m, ψ (extendedIncidence W) ≠ 0) ∧
          ∀ W W' : CodimTwo K m, W ≠ W' →
            LinearIndependent E ![ψ (extendedIncidence W), ψ (extendedIncidence W')]

end OneAndAHalfJohnson.Targets
