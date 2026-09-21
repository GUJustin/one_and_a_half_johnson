module

public import OneAndAHalfJohnson.Thresholds
public import OneAndAHalfJohnson.Syndrome

/-!
# Deterministic consequences of uniform weight amplification

The random construction in Section 3.2 (pp. 13–14) must produce a linear map
with a uniform weight estimate. This module derives the coset-distance
consequence from that estimate, including change from an extension alphabet
to a subfield alphabet. It does not assume or prove the existence of the
random map or its concentration event.
-/

@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson

variable {F E I J : Type*} [Field F] [Field E] [Algebra F E]
  [DecidableEq F] [DecidableEq E] [Fintype I] [Fintype J]

/-- Relative Hamming weight, with the zero-length convention inherited from division. -/
def relativeWeight {K X : Type*} [Zero K] [DecidableEq K] [Fintype X]
    (v : X → K) : ℝ := (hammingNorm v : ℝ) / Fintype.card X

/-- A relative Hamming weight never exceeds one. -/
theorem relativeWeight_le_one {K X : Type*} [Zero K] [DecidableEq K] [Fintype X]
    (v : X → K) : relativeWeight v ≤ 1 := by
  unfold relativeWeight
  exact div_le_one_of_le₀ (by exact_mod_cast (hammingNorm_le_card_fintype (x := v))) (Nat.cast_nonneg _)

/-- Uniform approximation to the ideal transform transfers source farness
through a linear map, even when the map reduces the alphabet to a subfield.
The strict target margin absorbs the approximation error. -/
theorem far_image_of_uniform_amplification
    (C D : Submodule E (I → E)) (hCD : C ≤ D)
    (A : (I → E) →ₗ[F] (J → F)) (f : I → E) (hf : f ∈ D)
    (t : ℕ) (α ε γ : ℝ)
    (hI : 0 < Fintype.card I) (hJ : 0 < Fintype.card J)
    (hfar : Far C f α)
    (happrox : ∀ v ∈ D, |relativeWeight (A v) - amplify t (relativeWeight v)| ≤ ε)
    (hmargin : γ + ε < amplify t α) :
    Far ((C.restrictScalars F).map A) (A f) γ := by
  intro y hy
  obtain ⟨c, hc, rfl⟩ := hy
  have hcC : c ∈ C := hc
  have hv : f - c ∈ D := D.sub_mem hf (hCD hcC)
  have hposI : (0 : ℝ) < Fintype.card I := by exact_mod_cast hI
  have hposJ : (0 : ℝ) < Fintype.card J := by exact_mod_cast hJ
  have hdist : hammingDist f c = hammingNorm (f - c) := by
    simpa only [sub_sub_cancel] using hammingDist_sub_eq_norm f (f - c)
  have hα : α ≤ relativeWeight (f - c) := by
    apply le_of_lt
    rw [relativeWeight, lt_div_iff₀ hposI]
    simpa only [hdist] using hfar c hcC
  have hmono := amplify_mono t hα (relativeWeight_le_one (f - c))
  have hlo := (abs_le.mp (happrox (f - c) hv)).1
  have hout : γ < relativeWeight (A (f - c)) := by linarith
  rw [relativeWeight, lt_div_iff₀ hposJ] at hout
  have houtdist : hammingNorm (A (f - c)) = hammingDist (A f) (A c) := by
    rw [map_sub]
    symm
    simpa only [sub_sub_cancel] using hammingDist_sub_eq_norm (A f) (A f - A c)
  simpa only [houtdist] using hout

/-- A source witness remains close after uniform weight amplification.
The challenge lies in the output field and acts on the input via its algebra structure. -/
theorem close_image_of_uniform_amplification
    (C D : Submodule E (I → E)) (hCD : C ≤ D)
    (A : (I → E) →ₗ[F] (J → F)) (f g : I → E)
    (hf : f ∈ D) (hg : g ∈ D) (z : F)
    (t : ℕ) (α ε γ : ℝ) (hα : α ≤ 1)
    (hJ : 0 < Fintype.card J)
    (hwitness : ∃ c ∈ C, relativeWeight (f + z • g - c) ≤ α)
    (happrox : ∀ v ∈ D, |relativeWeight (A v) - amplify t (relativeWeight v)| ≤ ε)
    (hmargin : amplify t α + ε ≤ γ) :
    Close ((C.restrictScalars F).map A) (A f + z • A g) γ := by
  obtain ⟨c, hc, hw⟩ := hwitness
  have hv : f + z • g - c ∈ D :=
    D.sub_mem (D.add_mem hf ((D.restrictScalars F).smul_mem z hg)) (hCD hc)
  have hmono := amplify_mono t hw hα
  have hhi := (abs_le.mp (happrox (f + z • g - c) hv)).2
  have hout : relativeWeight (A (f + z • g - c)) ≤ γ := by linarith
  have hposJ : (0 : ℝ) < Fintype.card J := by exact_mod_cast hJ
  rw [relativeWeight, div_le_iff₀ hposJ] at hout
  refine ⟨A c, ⟨c, hc, rfl⟩, ?_⟩
  have houtdist : hammingNorm (A (f + z • g - c)) =
      hammingDist (A f + z • A g) (A c) := by
    rw [map_sub, map_add, map_smul]
    symm
    simpa only [sub_sub_cancel] using
      hammingDist_sub_eq_norm (A f + z • A g) (A f + z • A g - A c)
  simpa only [houtdist] using hout

/-- A fixed set of distinct subfield challenges survives the amplification step. -/
theorem exceptional_count_image_of_uniform_amplification [Fintype F]
    (C D : Submodule E (I → E)) (hCD : C ≤ D)
    (A : (I → E) →ₗ[F] (J → F)) (f g : I → E)
    (hf : f ∈ D) (hg : g ∈ D) (T : Finset F)
    (t : ℕ) (α ε γ : ℝ) (hα : α ≤ 1)
    (hJ : 0 < Fintype.card J)
    (hwitness : ∀ z ∈ T, ∃ c ∈ C, relativeWeight (f + z • g - c) ≤ α)
    (happrox : ∀ v ∈ D, |relativeWeight (A v) - amplify t (relativeWeight v)| ≤ ε)
    (hmargin : amplify t α + ε ≤ γ) :
    T.card ≤ (exceptional ((C.restrictScalars F).map A) (A f) (A g) γ).card := by
  apply Finset.card_le_card
  intro z hz
  apply (mem_exceptional _ _ _ _ _).mpr
  exact close_image_of_uniform_amplification C D hCD A f g hf hg z
    t α ε γ hα hJ (hwitness z hz) happrox hmargin

/-- A positive amplified lower weight guarantees injectivity on the source code,
which must be established before discussing the image's minimum distance. -/
theorem injective_on_code_of_uniform_amplification
    (C D : Submodule E (I → E)) (hCD : C ≤ D)
    (A : (I → E) →ₗ[F] (J → F))
    (t : ℕ) (α ε : ℝ)
    (hweight : ∀ v ∈ C, v ≠ 0 → α ≤ relativeWeight v)
    (happrox : ∀ v ∈ D, |relativeWeight (A v) - amplify t (relativeWeight v)| ≤ ε)
    (hmargin : ε < amplify t α) :
    Set.InjOn A C := by
  intro x hx y hy hxy
  by_contra hne
  have hv := C.sub_mem hx hy
  have hn : x - y ≠ 0 := sub_ne_zero.mpr hne
  have hmono := amplify_mono t (hweight (x - y) hv hn) (relativeWeight_le_one (x - y))
  have hlo := (abs_le.mp (happrox (x - y) (hCD hv))).1
  have hz : A (x - y) = 0 := by simp [map_sub, hxy]
  rw [hz] at hlo
  have hw0 : relativeWeight (0 : J → F) = 0 := by simp [relativeWeight]
  rw [hw0] at hlo
  linarith

end OneAndAHalfJohnson
