module

public import OneAndAHalfJohnson.RandomSampling
public import OneAndAHalfJohnson.UniformConcentration
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Existence of the actual sampled amplification map

Independent uniform sampling rows are instantiated with their exact success
probability. The finite-family Hoeffding bound yields one actual linear map
with simultaneous weight control. No probabilistic premise is left to callers.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace OneAndAHalfJohnson

/-- Uniform independent draws from a finite nonempty row space concentrate
simultaneously for any finite family of bounded row statistics. -/
theorem exists_uniform_finite_samples
    {R D J : Type*} [Fintype R] [Nonempty R] [Fintype D] [Fintype J] [Nonempty J]
    (Z : D → R → ℝ) (hZ : ∀ v r, Z v r ∈ Set.Icc (0 : ℝ) 1)
    (ε : ℝ) (hε : 0 < ε)
    (hfailure : 2 * (Fintype.card D : ℝ) * Real.exp (-2 * ε ^ 2 * Fintype.card J) < 1) :
    ∃ ω : J → R, ∀ v,
      |(∑ j, Z v (ω j)) / Fintype.card J - (∑ r, Z v r) / Fintype.card R| ≤ ε := by
  classical
  let : MeasurableSpace R := ⊤
  let : MeasurableSingletonClass R := ⟨fun _ => trivial⟩
  let ν : Measure R := (PMF.uniformOfFintype R).toMeasure
  let μ : Measure (J → R) := Measure.pi (fun _ : J => ν)
  have hZm (v : D) : Measurable (Z v) := measurable_of_countable _
  have hexpect (v : D) (j : J) : ∫ ω, Z v (ω j) ∂μ = (∑ r, Z v r) / Fintype.card R := by
    have hp := measurePreserving_eval (fun _ : J => ν) j
    have hi := integral_map_of_stronglyMeasurable (μ := μ) hp.measurable (hZm v).stronglyMeasurable
    rw [hp.map_eq] at hi
    rw [← hi]
    simp only [ν, PMF.integral_eq_sum, PMF.uniformOfFintype_apply,
      ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
    rw [← Finset.mul_sum]
    exact (div_eq_inv_mul _ _).symm
  apply exists_uniform_average_concentration (μ := μ) (fun v j ω => Z v (ω j))
    (fun v => (∑ r, Z v r) / Fintype.card R) ε hε
  · intro v j
    exact ((hZm v).comp (measurable_pi_apply j)).aemeasurable
  · intro v j
    exact ae_of_all _ (fun ω => hZ v (ω j))
  · exact hexpect
  · intro v
    exact iIndepFun_pi (fun _ : J => (hZm v).aemeasurable)
  · exact hfailure

variable {F E I : Type*} [Field F] [Field E] [Algebra F E]
  [Fintype F] [Fintype E] [Fintype I] [Nonempty I]
  [DecidableEq F] [DecidableEq E]

/-- Normalize the exact row count into its actual success fraction. -/
theorem sampled_row_success_fraction (t : ℕ) (v : I → E) :
    ((Finset.univ.filter (fun r : SamplingRow F E I t =>
      r.2 (fun k => v (r.1 k)) ≠ 0)).card : ℝ) / Fintype.card (SamplingRow F E I t) =
      (1 - 1 / (Fintype.card F : ℝ)) * amplify t (relativeWeight v) := by
  classical
  let z := (Finset.univ.filter (fun i : I => v i = 0)).card
  have hz : z + hammingNorm v = Fintype.card I := by
    exact Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := fun i : I => v i = 0)
  have hzn : z ≤ Fintype.card I := by omega
  have hzp : z ^ t ≤ Fintype.card I ^ t := Nat.pow_le_pow_left hzn _
  have hq : 1 ≤ Fintype.card F := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt Fintype.card_pos)
  have hcount := sampled_row_nonzero_count (F := F) t v
  change Fintype.card F * _ = (Fintype.card I ^ t - z ^ t) * _ * _ at hcount
  have hc : (Fintype.card F : ℝ) *
      (Finset.univ.filter (fun r : SamplingRow F E I t => r.2 (fun k => v (r.1 k)) ≠ 0)).card =
      ((Fintype.card I : ℝ) ^ t - (z : ℝ) ^ t) *
        Fintype.card (Module.Dual F (Fin t → E)) * ((Fintype.card F : ℝ) - 1) := by
    exact_mod_cast hcount
  have hnR : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt Fintype.card_pos)
  have hqR : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt Fintype.card_pos)
  have hmR : (Fintype.card (Module.Dual F (Fin t → E)) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos (α := Module.Dual F (Fin t → E))))
  have hzero : 1 - relativeWeight v = (z : ℝ) / Fintype.card I := by
    have hzR : (z : ℝ) + hammingNorm v = Fintype.card I := by exact_mod_cast hz
    unfold relativeWeight
    field_simp
    linarith
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  unfold amplify
  rw [hzero, div_pow]
  push_cast
  field_simp
  nlinarith [hc]

/-- One actual sampled alphabet-reducing map gives the simultaneous weight
estimate for every word in a finite indexed family, under the explicit
Hoeffding union bound. All sampling and independence hypotheses are proved. -/
theorem exists_sampled_uniform_amplification
    {D J : Type*} [Fintype D] [Fintype J] [Nonempty J]
    (v : D → I → E) (t : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hfailure : 2 * (Fintype.card D : ℝ) * Real.exp (-2 * ε ^ 2 * Fintype.card J) < 1) :
    ∃ ω : J → SamplingRow F E I t, ∀ d,
      |relativeWeight (sampledLinearMap ω (v d)) -
        (1 - 1 / (Fintype.card F : ℝ)) * amplify t (relativeWeight (v d))| ≤ ε := by
  classical
  let Z : D → SamplingRow F E I t → ℝ := fun d r =>
    if r.2 (fun k => v d (r.1 k)) ≠ 0 then 1 else 0
  have hZ : ∀ d r, Z d r ∈ Set.Icc (0 : ℝ) 1 := by
    intro d r
    simp only [Z]
    split_ifs <;> constructor <;> norm_num
  have hmean (d : D) : (∑ r, Z d r) / Fintype.card (SamplingRow F E I t) =
      (1 - 1 / (Fintype.card F : ℝ)) * amplify t (relativeWeight (v d)) := by
    have he : (∑ r, Z d r) =
        ((Finset.univ.filter (fun r : SamplingRow F E I t =>
          r.2 (fun k => v d (r.1 k)) ≠ 0)).card : ℝ) := by
      simp only [Z, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [he]
    exact sampled_row_success_fraction t (v d)
  obtain ⟨ω, hω⟩ := exists_uniform_finite_samples Z hZ ε hε hfailure
  refine ⟨ω, ?_⟩
  intro d
  have he : (∑ j, Z d (ω j)) / Fintype.card J =
      relativeWeight (sampledLinearMap ω (v d)) := by
    change (∑ j, if (ω j).2 (fun k => v d ((ω j).1 k)) ≠ 0 then (1 : ℝ) else 0) /
        Fintype.card J =
      ((Finset.univ.filter (fun j => (ω j).2 (fun k => v d ((ω j).1 k)) ≠ 0)).card : ℝ) /
        Fintype.card J
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  simpa only [he, hmean] using hω d

/-- The uniform amplification conclusion as existence of an actual linear map,
ready for the deterministic image-distance lemmas. -/
theorem exists_linear_uniform_amplification
    {D J : Type*} [Fintype D] [Fintype J] [Nonempty J]
    (v : D → I → E) (t : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hfailure : 2 * (Fintype.card D : ℝ) * Real.exp (-2 * ε ^ 2 * Fintype.card J) < 1) :
    ∃ A : (I → E) →ₗ[F] (J → F), ∀ d,
      |relativeWeight (A (v d)) -
        (1 - 1 / (Fintype.card F : ℝ)) * amplify t (relativeWeight (v d))| ≤ ε := by
  obtain ⟨ω,hω⟩ := exists_sampled_uniform_amplification (F := F) (J := J) v t ε hε hfailure
  exact ⟨sampledLinearMap ω, hω⟩

end OneAndAHalfJohnson
