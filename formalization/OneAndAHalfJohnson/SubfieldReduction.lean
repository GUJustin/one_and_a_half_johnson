module

public import OneAndAHalfJohnson.SubfieldLines

/-!
# Preserving a dense exceptional set while reducing the challenge field

A nonzero rescaling of the second defining word preserves its distance from
an extension-field linear code. Dense-line extraction then supplies distinct
base-field challenges and their actual closeness witnesses.
-/

@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson

/-- Multiplying a word by a nonzero field scalar preserves strict distance
from a linear code at the same relative threshold. -/
theorem Far.smul_nonzero {E I : Type*} [Field E] [DecidableEq E] [Fintype I]
    {C : Submodule E (I → E)} {g : I → E} {τ : ℝ}
    (hg : Far C g τ) (b : E) (hb : b ≠ 0) : Far C (b • g) τ := by
  intro c hc
  have hh := hg (b⁻¹ • c) (C.smul_mem _ hc)
  have hd : hammingDist (b • g) c = hammingDist g (b⁻¹ • c) := by
    have h := hammingDist_smul (k := b) (x := g) (y := b⁻¹ • c)
      (fun _ => IsSMulRegular.of_ne_zero hb)
    simpa only [smul_smul, mul_inv_cancel₀ hb, one_smul] using h
  simpa only [hd] using hh

/-- The converse completes the exact invariance under nonzero rescaling. -/
theorem far_smul_nonzero_iff {E I : Type*} [Field E] [DecidableEq E] [Fintype I]
    (C : Submodule E (I → E)) (g : I → E) (τ : ℝ) (b : E) (hb : b ≠ 0) :
    Far C (b • g) τ ↔ Far C g τ := by
  constructor
  · intro h
    have hh := h.smul_nonzero b⁻¹ (inv_ne_zero hb)
    simpa only [smul_smul, inv_mul_cancel₀ hb, one_smul] using hh
  · exact fun h => h.smul_nonzero b hb

/-- A word farther than `τ≥ρ` prevents zero from being an exceptional challenge. -/
theorem zero_not_mem_exceptional_of_far
    {E I : Type*} [Field E] [Fintype E] [DecidableEq E] [Fintype I]
    (C : Submodule E (I → E)) (f g : I → E) (ρ τ : ℝ)
    (hf : Far C f τ) (hρτ : ρ ≤ τ) : (0 : E) ∉ exceptional C f g ρ := by
  intro h
  have hclose := (mem_exceptional C f g ρ 0).mp h
  simp only [zero_smul, add_zero] at hclose
  obtain ⟨c,hc,hcclose⟩ := hclose
  have hscale := mul_le_mul_of_nonneg_right hρτ (Nat.cast_nonneg (Fintype.card I))
  exact (not_le_of_gt (hf c hc)) (hcclose.trans hscale)

/-- Reduce exceptional challenges from an extension field to a subfield while
retaining at least half the original density and preserving both defining-word
farness bounds. The subset counts actual distinct base-field coefficients. -/
theorem exists_subfield_exceptional_reduction
    {F E I : Type*} [Field F] [Field E] [Algebra F E]
    [Fintype F] [Fintype E] [Fintype I] [DecidableEq F] [DecidableEq E]
    (C : Submodule E (I → E)) (f g : I → E) (ρ τ c : ℝ)
    (hc : 0 < c) (hf : Far C f τ) (hg : Far C g τ) (hρτ : ρ ≤ τ)
    (hdensity : c * Fintype.card E ≤ ((exceptional C f g ρ).card : ℝ)) :
    ∃ b : E, b ≠ 0 ∧ ∃ T : Finset F,
      0 < c / 2 ∧ (c / 2) * Fintype.card F ≤ (T.card : ℝ) ∧
      Far C f τ ∧ Far C (b • g) τ ∧
      ∀ z ∈ T, Close C (f + algebraMap F E z • (b • g)) ρ := by
  classical
  let S := exceptional C f g ρ
  have hzero : (0 : E) ∉ S := zero_not_mem_exceptional_of_far C f g ρ τ hf hρτ
  obtain ⟨b,hb,hcount⟩ := exists_dense_subfield_line_coefficients (F := F) S hzero
  let T : Finset F := Finset.univ.filter (fun z => b * algebraMap F E z ∈ S)
  change S.card * (Fintype.card F - 1) ≤ (Fintype.card E - 1) * T.card at hcount
  have hF : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hE : 2 ≤ Fintype.card E := Fintype.one_lt_card
  have hcountR : (S.card : ℝ) * ((Fintype.card F : ℝ) - 1) ≤
      ((Fintype.card E : ℝ) - 1) * T.card := by
    have hf1 : 1 ≤ Fintype.card F := by omega
    have he1 : 1 ≤ Fintype.card E := by omega
    have hh : ((S.card * (Fintype.card F - 1) : ℕ) : ℝ) ≤
        ((Fintype.card E - 1) * T.card : ℕ) := by exact_mod_cast hcount
    simpa only [Nat.cast_mul, Nat.cast_sub hf1, Nat.cast_sub he1, Nat.cast_one] using hh
  have hqhalf : (Fintype.card F : ℝ) / 2 ≤ (Fintype.card F : ℝ) - 1 := by
    have hh : (2 : ℝ) ≤ Fintype.card F := by exact_mod_cast hF
    linarith
  have hEpos : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  have hT : (c / 2) * Fintype.card F ≤ (T.card : ℝ) := by
    apply (mul_le_mul_iff_left₀ hEpos).mp
    calc
      ((c / 2) * Fintype.card F) * Fintype.card E =
          (c * Fintype.card E) * ((Fintype.card F : ℝ) / 2) := by ring
      _ ≤ (S.card : ℝ) * ((Fintype.card F : ℝ) - 1) :=
        mul_le_mul hdensity hqhalf (by positivity) (Nat.cast_nonneg _)
      _ ≤ ((Fintype.card E : ℝ) - 1) * T.card := hcountR
      _ ≤ (Fintype.card E : ℝ) * T.card :=
        mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
      _ = (T.card : ℝ) * Fintype.card E := by ring
  refine ⟨b,hb,T, by positivity, hT, hf, hg.smul_nonzero b hb, ?_⟩
  intro z hz
  have hzS := (Finset.mem_filter.mp hz).2
  have hclose := (mem_exceptional C f g ρ (b * algebraMap F E z)).mp hzS
  simpa only [smul_smul, mul_comm b] using hclose

end OneAndAHalfJohnson
