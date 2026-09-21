module
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Tactic.FieldSimp
/-! Relative-entropy Chernoff bounds for the concrete sampling argument. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace OneAndAHalfJohnson
/-- Binary relative entropy, with natural logarithms. -/
def bernoulliKL (a b : ℝ) : ℝ :=
  a * Real.log (a / b) + (1 - a) * Real.log ((1 - a) / (1 - b))
/-- The optimizing exponential tilt for a Bernoulli tail. -/
def bernoulliTilt (a b : ℝ) : ℝ := Real.log (a * (1 - b) / (b * (1 - a)))

/-- Substituting the optimal tilt gives the relative-entropy exponent. -/
theorem bernoulli_tilt_identity {a b : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hb0 : 0 < b) (hb1 : b < 1) (N : ℕ) :
    Real.exp (-bernoulliTilt a b * (a * N)) *
      (1 - b + b * Real.exp (bernoulliTilt a b)) ^ N =
        Real.exp (-(N : ℝ) * bernoulliKL a b) := by
  have ha : 0 < 1 - a := by linarith
  have hb : 0 < 1 - b := by linarith
  have hrat : 0 < a * (1 - b) / (b * (1 - a)) := by positivity
  have he : Real.exp (bernoulliTilt a b) = a * (1 - b) / (b * (1 - a)) :=
    Real.exp_log hrat
  have hbase : 1 - b + b * Real.exp (bernoulliTilt a b) = (1 - b) / (1 - a) := by
    rw [he]
    field_simp
    ring
  rw [hbase, ← Real.exp_log (div_pos hb ha), ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  unfold bernoulliTilt bernoulliKL
  rw [Real.log_div (ne_of_gt (mul_pos ha0 hb)) (ne_of_gt (mul_pos hb0 ha)),
    Real.log_mul (ne_of_gt ha0) (ne_of_gt hb),
    Real.log_mul (ne_of_gt hb0) (ne_of_gt ha),
    Real.log_div (ne_of_gt hb) (ne_of_gt ha),
    Real.log_div (ne_of_gt ha0) (ne_of_gt hb0),
    Real.log_div (ne_of_gt ha) (ne_of_gt hb)]
  ring

/-- The lower-tail optimizer has nonpositive tilt. -/
theorem bernoulliTilt_nonpos {a b : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hb0 : 0 < b) (hb1 : b < 1) (hab : a ≤ b) : bernoulliTilt a b ≤ 0 := by
  apply Real.log_nonpos
  · exact le_of_lt (div_pos (mul_pos ha0 (by linarith)) (mul_pos hb0 (by linarith)))
  · apply (div_le_one (mul_pos hb0 (by linarith))).mpr
    nlinarith

/-- The upper-tail optimizer has nonnegative tilt. -/
theorem bernoulliTilt_nonneg {a b : ℝ} (_ha0 : 0 < a) (ha1 : a < 1)
    (hb0 : 0 < b) (_hb1 : b < 1) (hab : b ≤ a) : 0 ≤ bernoulliTilt a b := by
  apply Real.log_nonneg
  apply (one_le_div (mul_pos hb0 (by linarith))).mpr
  nlinarith
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A zero-one variable has an integrable exponential at every real tilt. -/
theorem integrable_exp_mul_of_zero_one {X : Ω → ℝ} (t : ℝ)
    (hm : AEMeasurable X μ) (h01 : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) :
    Integrable (fun ω => Real.exp (t * X ω)) μ := by
  apply (integrable_const (Real.exp |t|)).mono' ((hm.const_mul t).exp.aestronglyMeasurable)
  filter_upwards [h01] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  rcases hω with h | h
  · simp [h]
  · simpa [h] using le_abs_self t

/-- The exact moment-generating function of any zero-one variable. -/
theorem mgf_of_zero_one {X : Ω → ℝ} {b : ℝ} (t : ℝ)
    (hm : AEMeasurable X μ) (h01 : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1)
    (hb : ∫ ω, X ω ∂μ = b) : mgf X μ t = 1 - b + b * Real.exp t := by
  have hInt : Integrable X μ := by
    apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    filter_upwards [h01] with ω hω
    rcases hω with h | h <;> simp [h]
  have he : (fun ω => Real.exp (t * X ω)) =ᵐ[μ]
      (fun ω => (1 : ℝ) + (Real.exp t - 1) * X ω) := by
    filter_upwards [h01] with ω hω
    rcases hω with h | h <;> simp [h]
  unfold mgf
  rw [integral_congr_ae he, integral_add (integrable_const _) (hInt.const_mul _),
    integral_const_mul, hb]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

/-- Independent zero-one trials have the exact binomial generating function. -/
theorem mgf_sum_zero_one {J : Type*} [Fintype J]
    (X : J → Ω → ℝ) (b t : ℝ)
    (hm : ∀ j, AEMeasurable (X j) μ)
    (h01 : ∀ j, ∀ᵐ ω ∂μ, X j ω = 0 ∨ X j ω = 1)
    (hb : ∀ j, ∫ ω, X j ω ∂μ = b) (hind : iIndepFun X μ) :
    mgf (fun ω => ∑ j, X j ω) μ t = (1 - b + b * Real.exp t) ^ Fintype.card J := by
  classical
  have hh := hind.mgf_sum₀ hm Finset.univ (t := t)
  have hfun : (∑ j, X j) = (fun ω => ∑ j, X j ω) := by ext ω; simp
  rw [hfun] at hh
  simpa only [mgf_of_zero_one t (hm _) (h01 _) (hb _),
    Finset.prod_const, Finset.card_univ] using hh

/-- Lower Chernoff tail for independent zero-one trials, in relative entropy form. -/
theorem bernoulli_sum_lower_tail {J : Type*} [Fintype J]
    (X : J → Ω → ℝ) {a b : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1) (hab : a ≤ b)
    (hm : ∀ j, Measurable (X j))
    (h01 : ∀ j, ∀ᵐ ω ∂μ, X j ω = 0 ∨ X j ω = 1)
    (hb : ∀ j, ∫ ω, X j ω ∂μ = b) (hind : iIndepFun X μ) :
    μ.real {ω | (∑ j, X j ω) ≤ a * Fintype.card J} ≤
      Real.exp (-(Fintype.card J : ℝ) * bernoulliKL a b) := by
  classical
  have hint : Integrable (fun ω => Real.exp (bernoulliTilt a b * ∑ j, X j ω)) μ := by
    simpa only [Finset.sum_apply] using hind.integrable_exp_mul_sum hm
      (s := Finset.univ) (fun j _ => integrable_exp_mul_of_zero_one _ (hm j).aemeasurable (h01 j))
  have hh := measure_le_le_exp_mul_mgf (X := fun ω => ∑ j, X j ω)
    (a * Fintype.card J) (bernoulliTilt_nonpos ha0 ha1 hb0 hb1 hab) hint
  rw [mgf_sum_zero_one X b _ (fun j => (hm j).aemeasurable) h01 hb hind,
    bernoulli_tilt_identity ha0 ha1 hb0 hb1] at hh
  exact hh

/-- Upper Chernoff tail for independent zero-one trials, in relative entropy form. -/
theorem bernoulli_sum_upper_tail {J : Type*} [Fintype J]
    (X : J → Ω → ℝ) {a b : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1) (hab : b ≤ a)
    (hm : ∀ j, Measurable (X j))
    (h01 : ∀ j, ∀ᵐ ω ∂μ, X j ω = 0 ∨ X j ω = 1)
    (hb : ∀ j, ∫ ω, X j ω ∂μ = b) (hind : iIndepFun X μ) :
    μ.real {ω | a * Fintype.card J ≤ ∑ j, X j ω} ≤
      Real.exp (-(Fintype.card J : ℝ) * bernoulliKL a b) := by
  classical
  have hint : Integrable (fun ω => Real.exp (bernoulliTilt a b * ∑ j, X j ω)) μ := by
    simpa only [Finset.sum_apply] using hind.integrable_exp_mul_sum hm
      (s := Finset.univ) (fun j _ => integrable_exp_mul_of_zero_one _ (hm j).aemeasurable (h01 j))
  have hh := measure_ge_le_exp_mul_mgf (X := fun ω => ∑ j, X j ω)
    (a * Fintype.card J) (bernoulliTilt_nonneg ha0 ha1 hb0 hb1 hab) hint
  rw [mgf_sum_zero_one X b _ (fun j => (hm j).aemeasurable) h01 hb hind,
    bernoulli_tilt_identity ha0 ha1 hb0 hb1] at hh
  exact hh

end OneAndAHalfJohnson
