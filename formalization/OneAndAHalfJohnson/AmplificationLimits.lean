module
public import OneAndAHalfJohnson.Thresholds
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecificLimits.Basic
/-! Analytic limits for choosing the fixed sampling repetition count. -/
@[expose] public section
noncomputable section
open Filter Topology
namespace OneAndAHalfJohnson
/-- Rounding the repetition count does not change the exponential amplification
limit. The input weight may vary, provided its first-order scale is fixed. -/
theorem tendsto_amplify_floor {u : ℝ → ℝ} {c L : ℝ} (hL : 0 ≤ L)
    (hu : Tendsto (fun x => x * u x) atTop (𝓝 c)) :
    Tendsto (fun x => amplify ⌊L * x⌋₊ (u x)) atTop (𝓝 (1 - Real.exp (-L * c))) := by
  have hlog : Tendsto (fun x => x * Real.log (1 - u x)) atTop (𝓝 (-c)) := by
    have hn : Tendsto (fun x => x * -u x) atTop (𝓝 (-c)) := by
      simpa only [mul_neg] using hu.neg
    simpa only [sub_eq_add_neg] using Real.tendsto_mul_log_one_add_of_tendsto hn
  have hprod := (tendsto_nat_floor_mul_div_atTop hL).mul hlog
  have hu0 : Tendsto u atTop (𝓝 0) := by
    have h := hu.div_atTop tendsto_id
    apply h.congr'
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
    dsimp
    exact mul_div_cancel_left₀ _ hx
  have hpos : ∀ᶠ x : ℝ in atTop, 0 < 1 - u x := by
    filter_upwards [hu0.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)] with x hx
    linarith
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hprod
  have heq : (fun x => Real.exp ((⌊L * x⌋₊ : ℝ) / x * (x * Real.log (1 - u x)))) =ᶠ[atTop]
      (fun x => (1 - u x) ^ ⌊L * x⌋₊) := by
    filter_upwards [hpos, eventually_ne_atTop (0 : ℝ)] with x hx hx0
    rw [div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_left₀ _ hx0]
    rw [Real.exp_nat_mul, Real.exp_log hx]
  have hp : Tendsto (fun x => (1 - u x) ^ ⌊L * x⌋₊) atTop (𝓝 (Real.exp (-L * c))) := by
    simpa only [mul_neg, neg_mul] using hexp.congr' heq
  exact tendsto_const_nhds.sub hp

/-- Slightly increase the target distance while retaining the exceptional-radius
slack. This supplies the strict defining-word inequality in the main theorem. -/
theorem exists_distance_overshoot {δ ρ η : ℝ} (hδ1 : δ < 1)
    (hρ : johnson δ < ρ) (hη : 0 < η) :
    ∃ δ' : ℝ, δ < δ' ∧ δ' < 1 ∧ δ' - δ < η ∧
      johnson δ' < ρ ∧ gamma δ < gamma δ' := by
  have hc : ContinuousAt johnson δ := by
    unfold johnson
    fun_prop (disch := positivity)
  have he : ∀ᶠ x in 𝓝 δ, johnson x < ρ := hc.tendsto.eventually (gt_mem_nhds hρ)
  have he1 : ∀ᶠ x in 𝓝 δ, x < 1 := gt_mem_nhds hδ1
  have heη : ∀ᶠ x in 𝓝 δ, x < δ + η := gt_mem_nhds (by linarith)
  have hl : ∀ᶠ x in 𝓝[>] δ, δ < x := self_mem_nhdsWithin
  have hall : ∀ᶠ x in 𝓝[>] δ, δ < x ∧ johnson x < ρ ∧ x < 1 ∧ x < δ + η :=
    hl.and
      ((he.and (he1.and heη)).filter_mono nhdsWithin_le_nhds)
  obtain ⟨δ', hleft, hj, hright, hdist⟩ := hall.exists
  refine ⟨δ', hleft, hright, by linarith, hj, ?_⟩
  unfold gamma
  have hh := Real.rpow_lt_rpow (by linarith : 0 ≤ 1 - δ')
    (by linarith : 1 - δ' < 1 - δ) (by norm_num : (0 : ℝ) < 4 / 9)
  linarith

/-- The basic inverse-scale input is covered by the rounded amplification limit. -/
theorem tendsto_amplify_floor_div (c L : ℝ) (hL : 0 ≤ L) :
    Tendsto (fun x : ℝ => amplify ⌊L * x⌋₊ (c / x)) atTop
      (𝓝 (1 - Real.exp (-L * c))) := by
  apply tendsto_amplify_floor hL
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
  exact (mul_div_cancel₀ c hx).symm

/-- A strict inequality at a positive endpoint persists at some smaller positive argument. -/
theorem exists_left_positive_of_continuousAt {f : ℝ → ℝ} {x y : ℝ}
    (hx : 0 < x) (hf : ContinuousAt f x) (hy : y < f x) :
    ∃ z : ℝ, 0 < z ∧ z < x ∧ y < f z := by
  have hl : ∀ᶠ z in 𝓝[<] x, z < x := self_mem_nhdsWithin
  have hpos : ∀ᶠ z in 𝓝 x, 0 < z := lt_mem_nhds hx
  have hv : ∀ᶠ z in 𝓝 x, y < f z := hf.tendsto.eventually (lt_mem_nhds hy)
  obtain ⟨z, hzx, hz0, hzv⟩ :=
    (hl.and ((hpos.and hv).filter_mono nhdsWithin_le_nhds)).exists
  exact ⟨z, hz0, hzx, hzv⟩

/-- The exponential scaling that targets a chosen distance. -/
def amplificationScale (δ : ℝ) : ℝ := -Real.log (1 - δ) / 3

/-- An interior target requires a positive repetition scale. -/
theorem amplificationScale_pos {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) :
    0 < amplificationScale δ := by
  unfold amplificationScale
  have hlog := Real.log_neg (by linarith : 0 < 1 - δ) (by linarith : 1 - δ < 1)
  linarith

/-- The three limiting radii agree with the paper's distance transforms. -/
theorem amplificationScale_endpoints {δ : ℝ} (h1 : δ < 1) :
    1 - Real.exp (-amplificationScale δ * 3) = δ ∧
    1 - Real.exp (-amplificationScale δ * 1) = johnson δ ∧
    1 - Real.exp (-amplificationScale δ * (4 / 3)) = gamma δ := by
  have hb : 0 < 1 - δ := by linarith
  unfold amplificationScale johnson gamma
  rw [Real.rpow_def_of_pos hb, Real.rpow_def_of_pos hb]
  constructor
  · have he : -(-Real.log (1 - δ) / 3) * 3 = Real.log (1 - δ) := by ring
    rw [he, Real.exp_log hb]
    ring
  · constructor <;> congr 2 <;> ring

end OneAndAHalfJohnson
