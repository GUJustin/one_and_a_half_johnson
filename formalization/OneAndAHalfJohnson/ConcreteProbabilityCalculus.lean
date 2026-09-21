module
public import OneAndAHalfJohnson.ConcreteDivergenceBounds
public import OneAndAHalfJohnson.WeightLayerBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
/-! Uniform concrete weight-layer Chernoff envelopes. -/
@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson.ConcreteAnalyticBounds

/-- Exact derivative of binary relative entropy in its probability argument. -/
theorem hasDerivAt_bernoulliKL {a p : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt (bernoulliKL a) ((p-a)/(p*(1-p))) p := by
  have h₁ := (((hasDerivAt_const p a).div (hasDerivAt_id p) (ne_of_gt hp0)).log
    (ne_of_gt (div_pos ha0 hp0))).const_mul a
  have h₂ := (((hasDerivAt_const p (1-a)).div
    ((hasDerivAt_const p 1).sub (hasDerivAt_id p)) (by dsimp; linarith)).log
      (ne_of_gt (div_pos (by linarith) (by dsimp; linarith)))).const_mul (1-a)
  convert h₁.add h₂ using 1
  · ext x; rfl
  · dsimp
    field_simp [ne_of_gt ha0, ne_of_gt hp0, show 1-a ≠ 0 by linarith, show 1-p ≠ 0 by linarith]
    ring

/-- Exact derivative of the concrete sampling probability. -/
theorem hasDerivAt_rowProbability (w : ℝ) :
    HasDerivAt rowProbability
      ((1-1/(2:ℝ)^128)*52500/68853957121*(1-w/68853957121)^52499) w := by
  have h := ((hasDerivAt_const w 1).sub
    (((hasDerivAt_const w 1).sub ((hasDerivAt_id w).div_const 68853957121)).pow 52500)).const_mul
      (1-1/(2:ℝ)^128)
  convert h using 1
  · rfl
  · dsimp
    generalize (1-w/68853957121)^52499 = z
    norm_num
    ring

/-- Survival and nonzero-output probabilities are monotone on the physical
weight interval. -/
theorem rowProbability_monotone : MonotoneOn rowProbability (Set.Icc 0 68853957121) := by
  intro x hx y hy hxy
  have hpow : (1-y/68853957121)^52500 ≤ (1-x/68853957121)^52500 := by
    apply pow_le_pow_left₀ (by linarith [hy.2])
    linarith
  unfold rowProbability
  generalize (1-x/68853957121)^52500 = X at *
  generalize (1-y/68853957121)^52500 = Y at *
  nlinarith

theorem rowProbability_mem_Ioo {w : ℝ} (hw0 : 0 < w) (hwn : w ≤ 68853957121) :
    0 < rowProbability w ∧ rowProbability w < 1 := by
  have hx0 : 0 ≤ 1-w/68853957121 := by linarith
  have hx1 : 1-w/68853957121 < 1 := by linarith
  have hpow0 : 0 ≤ (1-w/68853957121)^52500 := pow_nonneg hx0 _
  have hpow1 : (1-w/68853957121)^52500 < 1 := pow_lt_one₀ hx0 hx1 (by norm_num)
  unfold rowProbability
  generalize (1-w/68853957121)^52500 = X at *
  constructor <;> nlinarith

theorem bernoulliKL_mono {a p r : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hap : a ≤ p) (hpr : p ≤ r) (hr1 : r < 1) : bernoulliKL a p ≤ bernoulliKL a r := by
  have hd (x : ℝ) (hx : x ∈ Set.Icc p r) :=
    hasDerivAt_bernoulliKL ha0 ha1 (ha0.trans_le (hap.trans hx.1)) (hx.2.trans_lt hr1)
  have hm : MonotoneOn (bernoulliKL a) (Set.Icc p r) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
      (fun x hx => div_nonneg (sub_nonneg.mpr (hap.trans (interior_subset hx).1))
        (mul_nonneg (le_of_lt (ha0.trans_le (hap.trans (interior_subset hx).1)))
          (sub_nonneg.mpr ((interior_subset hx).2.trans hr1.le))))
  exact hm ⟨le_rfl, hpr⟩ ⟨hpr, le_rfl⟩ hpr

/-- The global dimension estimate handles all weights beyond the transition. -/
theorem global_alpha_exponent {w : ℝ} (hw : 12550000 ≤ w) (hwn : w ≤ 68853957121) :
    (3604584374:ℝ)*(128*Real.log 2) - 2^36*bernoulliKL (4419/10000) (rowProbability w) < -1000 := by
  have hp := rowProbability_monotone (by norm_num : (12550000:ℝ) ∈ Set.Icc 0 68853957121)
    ⟨by linarith, hwn⟩ hw
  have hKL := bernoulliKL_mono (by norm_num : (0:ℝ) < 4419/10000) (by norm_num)
    (by have h := probability_W.1; norm_num at h; linarith) hp
    (rowProbability_mem_Ioo (by linarith) hwn).2
  have hbase := divergence_alpha_W
  have hcount := count_global_upper
  norm_num at hKL hbase hcount ⊢
  linarith

theorem global_beta_exponent {w : ℝ} (hw : 12550000 ≤ w) (hwn : w ≤ 68853957121) :
    (3604584374:ℝ)*(128*Real.log 2) - 2^36*bernoulliKL (22945/100000) (rowProbability w) < -1000 := by
  have hp := rowProbability_monotone (by norm_num : (12550000:ℝ) ∈ Set.Icc 0 68853957121)
    ⟨by linarith, hwn⟩ hw
  have hKL := bernoulliKL_mono (by norm_num : (0:ℝ) < 22945/100000) (by norm_num)
    (by have h := probability_W.1; norm_num at h; linarith) hp
    (rowProbability_mem_Ioo (by linarith) hwn).2
  have hbase := divergence_beta_W
  have hcount := count_global_upper
  norm_num at hKL hbase hcount ⊢
  linarith

theorem bernoulliKL_antitone {a p r : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hp0 : 0 < p) (hpr : p ≤ r) (hra : r ≤ a) : bernoulliKL a r ≤ bernoulliKL a p := by
  have hd (x : ℝ) (hx : x ∈ Set.Icc p r) :=
    hasDerivAt_bernoulliKL ha0 ha1 (hp0.trans_le hx.1) (hx.2.trans_lt (hra.trans_lt ha1))
  have hm : AntitoneOn (bernoulliKL a) (Set.Icc p r) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
      (fun x hx => div_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr ((interior_subset hx).2.trans hra))
        (mul_nonneg (le_of_lt (hp0.trans_le (interior_subset hx).1))
          (sub_nonneg.mpr ((interior_subset hx).2.trans (hra.trans ha1.le)))))
  exact hm ⟨le_rfl, hpr⟩ ⟨hpr, le_rfl⟩ hpr

theorem short_word_upper_tail {w : ℝ} (hw0 : 0 < w) (hw : w ≤ 786433) :
    0 < rowProbability w ∧ rowProbability w < 4511/10000 ∧
      1565 < (2:ℝ)^36*bernoulliKL (4511/10000) (rowProbability w) := by
  have hp := rowProbability_monotone ⟨hw0.le, by linarith⟩
    (by norm_num : (786433:ℝ) ∈ Set.Icc 0 68853957121) hw
  have hp0 := (rowProbability_mem_Ioo hw0 (by linarith)).1
  have hr : rowProbability 786433 < 4511/10000 := by
    have hh := probability_d1.2
    norm_num at hh
    linarith
  refine ⟨hp0, hp.trans_lt hr, ?_⟩
  have hKL := bernoulliKL_antitone (by norm_num : (0:ℝ) < 4511/10000)
    (by norm_num) hp0 hp hr.le
  have hh := divergence_delta_d1
  norm_num at hKL hh ⊢
  linarith

theorem incidence_upper_tail :
    0 < rowProbability 262657 ∧ rowProbability 262657 < 1816/10000 ∧
      2702 < (2:ℝ)^36*bernoulliKL (1816/10000) (rowProbability 262657) := by
  refine ⟨(rowProbability_mem_Ioo (by norm_num) (by norm_num)).1, ?_, by convert divergence_tau_e using 1; norm_num⟩
  have h := probability_e.2
  norm_num at h
  linarith

end OneAndAHalfJohnson.ConcreteAnalyticBounds
