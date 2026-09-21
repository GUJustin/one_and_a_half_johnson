module

public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic.FieldSimp

/-!
# Uniform Hoeffding concentration for a finite family of words

Bounded independent output coordinates concentrate simultaneously for every
word in a finite family. This is a generic probability theorem, not an
assumption that the paper's random sampler satisfies its hypotheses.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace OneAndAHalfJohnson

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Combining the two sub-Gaussian tails controls strict absolute deviations. -/
theorem measure_abs_gt_le_of_subgaussian {X : Ω → ℝ} {c : ℝ≥0}
    (hX : HasSubgaussianMGF X c μ) (ε : ℝ) (hε : 0 ≤ ε) :
    μ.real {ω | ε < |X ω|} ≤ 2 * Real.exp (-ε ^ 2 / (2 * c)) := by
  have hsub : {ω | ε < |X ω|} ⊆ {ω | ε ≤ X ω} ∪ {ω | ε ≤ (-X) ω} := by
    intro ω hω
    change ε < |X ω| at hω
    change ε ≤ X ω ∨ ε ≤ (-X) ω
    rcases lt_abs.mp hω with h | h
    · exact Or.inl h.le
    · exact Or.inr (by simp only [Pi.neg_apply]; linarith)
  calc
    μ.real {ω | ε < |X ω|} ≤ μ.real ({ω | ε ≤ X ω} ∪ {ω | ε ≤ (-X) ω}) :=
      measureReal_mono hsub
    _ ≤ μ.real {ω | ε ≤ X ω} + μ.real {ω | ε ≤ (-X) ω} := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-ε ^ 2 / (2 * c)) := by
      have h₁ := hX.measure_ge_le hε
      have h₂ := hX.neg.measure_ge_le hε
      linarith

/-- Averages of independent `[0,1]` random variables with common expectation
have failure probability at most `2 exp(-2 ε² N)`. -/
theorem measure_average_deviation_le
    {J : Type*} [Fintype J] [Nonempty J]
    (Y : J → Ω → ℝ) (p ε : ℝ)
    (hε : 0 ≤ ε)
    (hmeas : ∀ j, AEMeasurable (Y j) μ)
    (hbounded : ∀ j, ∀ᵐ ω ∂μ, Y j ω ∈ Set.Icc (0 : ℝ) 1)
    (hexpect : ∀ j, ∫ ω, Y j ω ∂μ = p)
    (hind : iIndepFun Y μ) :
    μ.real {ω | ε < |(∑ j, Y j ω) / Fintype.card J - p|} ≤
      2 * Real.exp (-2 * ε ^ 2 * Fintype.card J) := by
  classical
  let X : J → Ω → ℝ := fun j ω => Y j ω - p
  have hindX : iIndepFun X μ := hind.comp (fun _ x => x - p) (fun _ => by fun_prop)
  have hX (j : J) : HasSubgaussianMGF (X j) (1 / 4) μ := by
    have h := hasSubgaussianMGF_of_mem_Icc (hmeas j) (hbounded j)
    norm_num [X, hexpect j] at h ⊢
    exact h
  have hsum : HasSubgaussianMGF (fun ω => ∑ j, X j ω)
      (∑ _j : J, (1 / 4 : ℝ≥0)) μ :=
    HasSubgaussianMGF.sum_of_iIndepFun hindX (fun j _ => hX j)
  have hn : (0 : ℝ) < Fintype.card J := by exact_mod_cast Fintype.card_pos
  have htail := measure_abs_gt_le_of_subgaussian hsum (ε * Fintype.card J)
    (mul_nonneg hε hn.le)
  have heq (ω : Ω) :
      (∑ j, Y j ω) / Fintype.card J - p = (∑ j, X j ω) / Fintype.card J := by
    simp only [X, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have hsub : {ω | ε < |(∑ j, Y j ω) / Fintype.card J - p|} ⊆
      {ω | ε * Fintype.card J < |∑ j, X j ω|} := by
    intro ω hω
    change ε < |(∑ j, Y j ω) / Fintype.card J - p| at hω
    change ε * Fintype.card J < |∑ j, X j ω|
    rw [heq, abs_div, abs_of_pos hn] at hω
    exact (lt_div_iff₀ hn).mp hω
  apply (measureReal_mono hsub).trans
  convert htail using 1
  congr 2
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  push_cast
  field_simp
  ring

/-- Uniform concentration over a finite word family. The failure bound is
strictly below one, so one outcome satisfies every word estimate at once. -/
theorem exists_uniform_average_concentration
    {D J : Type*} [Fintype D] [Fintype J] [Nonempty J]
    (Y : D → J → Ω → ℝ) (p : D → ℝ) (ε : ℝ)
    (hε : 0 < ε)
    (hmeas : ∀ v j, AEMeasurable (Y v j) μ)
    (hbounded : ∀ v j, ∀ᵐ ω ∂μ, Y v j ω ∈ Set.Icc (0 : ℝ) 1)
    (hexpect : ∀ v j, ∫ ω, Y v j ω ∂μ = p v)
    (hind : ∀ v, iIndepFun (Y v) μ)
    (hfailure : 2 * (Fintype.card D : ℝ) *
      Real.exp (-2 * ε ^ 2 * Fintype.card J) < 1) :
    ∃ ω, ∀ v, |(∑ j, Y v j ω) / Fintype.card J - p v| ≤ ε := by
  classical
  let B : D → Set Ω := fun v => {ω | ε < |(∑ j, Y v j ω) / Fintype.card J - p v|}
  have hbound : μ.real (⋃ v, B v) ≤ 2 * (Fintype.card D : ℝ) *
      Real.exp (-2 * ε ^ 2 * Fintype.card J) := by
    calc
      μ.real (⋃ v, B v) ≤ ∑ v, μ.real (B v) := measureReal_iUnion_fintype_le B
      _ ≤ ∑ _v : D, 2 * Real.exp (-2 * ε ^ 2 * Fintype.card J) := by
        apply Finset.sum_le_sum
        intro v hv
        exact measure_average_deviation_le (Y v) (p v) ε hε.le
          (hmeas v) (hbounded v) (hexpect v) (hind v)
      _ = _ := by simp [mul_assoc, mul_comm]
  by_contra h
  push Not at h
  have hwhole : (⋃ v, B v) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro ω
    obtain ⟨v, hv⟩ := h ω
    exact Set.mem_iUnion.mpr ⟨v, hv⟩
  rw [hwhole] at hbound
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one] at hbound
  linarith

end OneAndAHalfJohnson
