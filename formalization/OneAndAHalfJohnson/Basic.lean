module

public import ArkLib.Data.CodingTheory.Basic.LinearCode
public import ArkLib.Data.CodingTheory.Basic.RelativeDistance
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Hamming semantics for the one-and-a-half Johnson counterexamples

The paper is ePrint 2026/1894, Section 2 (p. 6). Codes are actual linear
subspaces; closeness and strict farness quantify over actual codewords.
Multiplication by the block length avoids rounded radii. These predicates
have their usual relative-distance meaning for nonempty coordinate sets.
-/

@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson

variable {F I : Type*} [Field F] [DecidableEq F] [Fintype I]

/-- A codeword witnesses relative distance at most `ρ`. -/
def Close (C : Submodule F (I → F)) (v : I → F) (ρ : ℝ) : Prop :=
  ∃ c ∈ C, (hammingDist v c : ℝ) ≤ ρ * Fintype.card I

/-- Every codeword has relative distance strictly greater than `τ`. -/
def Far (C : Submodule F (I → F)) (v : I → F) (τ : ℝ) : Prop :=
  ∀ c ∈ C, τ * Fintype.card I < (hammingDist v c : ℝ)

/-- Distinct exceptional field coefficients, for one fixed pair of words. -/
def exceptional [Fintype F] (C : Submodule F (I → F)) (f g : I → F)
    (ρ : ℝ) : Finset F := by
  classical
  exact Finset.univ.filter (fun z => Close C (f + z • g) ρ)

/-- Relative minimum distance, using ArkLib's minimum Hamming distance. -/
def relativeDistance (C : Submodule F (I → F)) : ℝ :=
  (Code.dist (C : Set (I → F)) : ℝ) / Fintype.card I

/-- Dimension divided by block length. -/
def rate (C : Submodule F (I → F)) : ℝ :=
  (Module.finrank F C : ℝ) / Fintype.card I

/-- The one-and-a-half Johnson radius. -/
def johnson (δ : ℝ) : ℝ := 1 - (1 - δ) ^ (1 / 3 : ℝ)

/-- Defining-vector distance threshold from Theorem 1.1. -/
def gamma (δ : ℝ) : ℝ := 1 - (1 - δ) ^ (4 / 9 : ℝ)

/-- Ideal distance amplification by sampling `t` coordinates. -/
def amplify (t : ℕ) (u : ℝ) : ℝ := 1 - (1 - u) ^ t

/-- Enlarging a code preserves every closeness witness. -/
theorem Close.mono {C C' : Submodule F (I → F)} (hCC : C ≤ C')
    {v : I → F} {ρ : ℝ} (h : Close C v ρ) : Close C' v ρ := by
  obtain ⟨c, hc, hd⟩ := h
  exact ⟨c, hCC hc, hd⟩

/-- A strict farness bound excludes closeness at that same radius. -/
theorem Far.not_close {C : Submodule F (I → F)} {v : I → F} {ρ : ℝ}
    (h : Far C v ρ) : ¬ Close C v ρ := by
  rintro ⟨c, hc, hd⟩
  exact (not_le_of_gt (h c hc)) hd

/-- Membership spells out the codeword chosen after the challenge. -/
@[simp] theorem mem_exceptional [Fintype F] (C : Submodule F (I → F))
    (f g : I → F) (ρ : ℝ) (z : F) :
    z ∈ exceptional C f g ρ ↔ Close C (f + z • g) ρ := by
  classical
  simp [exceptional]

/-- Supercode completion cannot discard exceptional coefficients. -/
theorem exceptional_mono [Fintype F] {C C' : Submodule F (I → F)}
    (hCC : C ≤ C') (f g : I → F) (ρ : ℝ) :
    exceptional C f g ρ ⊆ exceptional C' f g ρ := by
  intro z hz
  exact (mem_exceptional _ _ _ _ _).mpr
    (((mem_exceptional _ _ _ _ _).mp hz).mono hCC)

end OneAndAHalfJohnson
