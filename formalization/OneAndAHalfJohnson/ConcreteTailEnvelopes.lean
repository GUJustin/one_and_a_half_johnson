module
public import OneAndAHalfJohnson.ConcreteLayerDerivative
@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson.ConcreteAnalyticBounds

/-- Algebraic identity exposing the finite-field correction in the derivative. -/
theorem slope_div_survival {w : ℝ} (hw0 : 0 < w) (hwn : w < 68853957121) :
    rowSlope w / (1-rowProbability w) =
      52500/(68853957121-w) *
        (((1-1/(2:ℝ)^128)*(1-w/68853957121)^52500) /
          (1/(2:ℝ)^128+(1-1/(2:ℝ)^128)*(1-w/68853957121)^52500)) := by
  have hp := rowProbability_mem_Ioo hw0 hwn.le
  have hne : 1-rowProbability w ≠ 0 := by linarith
  have hwne : (68853957121:ℝ)-w ≠ 0 := by linarith
  have hid : (1/(2:ℝ)^128+(1-1/(2:ℝ)^128)*(1-w/68853957121)^52500) =
      1-rowProbability w := by
    unfold rowProbability
    generalize (1-w/68853957121)^52500 = z
    ring
  rw [hid]
  rw [← mul_div_assoc]
  apply (div_left_inj' hne).mpr
  unfold rowSlope
  rw [show (1-w/68853957121)^52500 = (1-w/68853957121)^52499*(1-w/68853957121) from pow_succ _ _]
  generalize (1-w/68853957121)^52499 = z
  field_simp

/-- Pure algebra converting a relative derivative correction into a KL gain. -/
theorem divergence_gain_of_correction {N t d p a s c r : ℝ}
    (hN : 0 < N) (ht : 0 < t) (hd : 0 < d) (hp : 0 < p) (_hp1 : p < 1)
    (ha : a < p) (hc : c < r) (hs : s/(1-p) = t/d*r) :
    c*N*t/d*(1-a/p) < N*((p-a)/(p*(1-p)))*s := by
  have hfac : 0 < N*(t/d)*(1-a/p) := by
    apply mul_pos (mul_pos hN (div_pos ht hd))
    have := (div_lt_one hp).mpr ha
    linarith
  have hh := mul_lt_mul_of_pos_left hc hfac
  have hid : N*((p-a)/(p*(1-p)))*s = N*(t/d)*(1-a/p)*r := by
    calc
      _ = N*(1-a/p)*(s/(1-p)) := by field_simp
      _ = _ := by rw [hs]; ring
  rw [hid]
  convert hh using 1; ring

/-- The derivative gain exceeds the explicit rational envelope throughout
all three weight-layer intervals. -/
theorem divergence_slope_lower {a w : ℝ} (_ha0 : 0 ≤ a)
    (hap : a < rowProbability w) (hw0 : 0 < w) (hwW : w ≤ 12550000) :
    (999:ℝ)/1000 * 2^36 * 52500/(68853957121-w)*(1-a/rowProbability w) <
      2^36 * ((rowProbability w-a)/(rowProbability w*(1-rowProbability w))) * rowSlope w := by
  have hwn : w < 68853957121 := by linarith only [hwW]
  have hp := rowProbability_mem_Ioo hw0 hwn.le
  have hr : (697:ℝ)/10000000 ≤ (1-w/68853957121)^52500 := by
    apply survival_W_lower.le.trans
    apply pow_le_pow_left₀ (by norm_num)
    linarith only [hwW]
  exact divergence_gain_of_correction (by norm_num) (by norm_num) (by linarith only [hwn])
    hp.1 hp.2 hap (finite_field_correction_lower hr) (slope_div_survival hw0 hwn)

theorem layerExponent_antitone {a c l b T U : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hab : a < b)
    (hl0 : 0 < l) (hlW : l ≤ 12550000) (hpl : b ≤ rowProbability l)
    (hnum : T < (999:ℝ)/1000*2^36*52500/68853957121*(1-a/b))
    (hlog : Real.log (68853957121/l)+c < U) (hTU : U < T) :
    AntitoneOn (layerExponent a c) (Set.Icc l 12550000) := by
  have hd (w : ℝ) (hw : w ∈ Set.Icc l 12550000) :=
    hasDerivAt_layerExponent (c := c) ha0 ha1 (hl0.trans_le hw.1) (by linarith [hw.2])
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
    (fun w hw => (hd w hw).continuousAt.continuousWithinAt)
    (fun w hw => (hd w (interior_subset hw)).hasDerivWithinAt)
  intro w hw
  have hw := interior_subset hw
  have hw0 : 0 < w := hl0.trans_le hw.1
  have hp : b ≤ rowProbability w := hpl.trans (rowProbability_monotone
    ⟨hl0.le, by linarith⟩ ⟨hw0.le, by linarith [hw.2]⟩ hw.1)
  have hsmall := derivative_envelope_lower ha0.le hab hp hw0.le (by linarith [hw.2]) hnum
  have hlarge := divergence_slope_lower ha0.le (hab.trans_le hp) hw0 hw.2
  have hlogw : Real.log (68853957121/w) ≤ Real.log (68853957121/l) :=
    Real.log_le_log (div_pos (by norm_num) hw0)
      (div_le_div_of_nonneg_left (by norm_num) hl0 hw.1)
  linarith

theorem layer_alpha_exponent {w : ℝ} (hw : 784896 ≤ w) (hwW : w ≤ 12550000) :
    layerExponent (4419/10000) (128*Real.log 2) w < -1000 := by
  have hm := layerExponent_antitone (a := (4419:ℝ)/10000) (c := 128*Real.log 2)
    (l := 784896) (b := 45035/100000) (T := 982) (U := 101)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    probability_d0_lower.le (by norm_num) log_derivative_alpha_upper (by norm_num)
  have hh := hm (by norm_num : (784896:ℝ) ∈ Set.Icc 784896 12550000) ⟨hw,hwW⟩ hw
  have hcount := count_d0_upper
  have hKL := divergence_alpha_d0
  unfold layerExponent at hh ⊢
  norm_num at hh hcount hKL ⊢
  linarith

theorem layer_beta_exponent {w c : ℝ} (hw : 350210 ≤ w) (hwW : w ≤ 12550000)
    (hc0 : 0 ≤ c) (hc : c ≤ 128*Real.log 2) :
    layerExponent (22945/100000) c w < -1000 := by
  have hm := layerExponent_antitone (a := (22945:ℝ)/100000) (c := c)
    (l := 350210) (b := 2343/10000) (T := 1083) (U := 102)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    probability_wstar_lower.le (by norm_num)
    (by have h₁ := log_derivative_beta_upper; have h₂ := log_q_upper; linarith)
    (by norm_num)
  have hh := hm (by norm_num : (350210:ℝ) ∈ Set.Icc 350210 12550000) ⟨hw,hwW⟩ hw
  have hcount := count_wstar_upper
  have hKL := divergence_beta_wstar
  unfold layerExponent at hh ⊢
  norm_num at hh hcount hKL ⊢
  linarith

end OneAndAHalfJohnson.ConcreteAnalyticBounds
