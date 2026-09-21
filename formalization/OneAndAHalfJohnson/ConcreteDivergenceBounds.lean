module
public import OneAndAHalfJohnson.ConcreteAnalyticBounds
public import OneAndAHalfJohnson.ConcreteLogBounds
public import OneAndAHalfJohnson.BernoulliChernoff
/-! Certified relative-entropy and combinatorial-count inequalities for Theorem 4.1. -/
@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson.ConcreteAnalyticBounds
open ConcreteLogBounds

theorem divergence_lower {a p l u A B : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hl : 0 < l) (hu : u < 1)
    (hp : l ≤ p ∧ p ≤ u)
    (hA : A ≤ Real.log (a/u)) (hB : B ≤ Real.log ((1-a)/(1-l))) :
    a*A+(1-a)*B ≤ bernoulliKL a p := by
  have hp0 : 0 < p := hl.trans_le hp.1
  have hu0 : 0 < u := hp0.trans_le hp.2
  have hp1 : p < 1 := hp.2.trans_lt hu
  have hlog1 : A ≤ Real.log (a/p) := hA.trans (Real.log_le_log
    (div_pos ha0 hu0) (div_le_div_of_nonneg_left ha0.le hp0 hp.2))
  have hlog2 : B ≤ Real.log ((1-a)/(1-p)) := hB.trans (Real.log_le_log
    (div_pos (by linarith) (by linarith))
    (div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)))
  unfold bernoulliKL
  exact add_le_add (mul_le_mul_of_nonneg_left hlog1 ha0.le)
    (mul_le_mul_of_nonneg_left hlog2 (by linarith))

/-- The paper's strict Chernoff exponent at weight `784896`. -/
theorem divergence_alpha_d0 : 9922939 < (2:ℝ)^36 * bernoulliKL (4419 / 10000 : ℝ) (rowProbability 784896) := by
  have h := divergence_lower (a := (4419 / 10000 : ℝ)) (p := rowProbability 784896)
    (by norm_num) (by norm_num) (by norm_num : (0:ℝ) < (450350012396406367147831 / 1000000000000000000000000 : ℝ))
    (by norm_num : (450350012396406367176753 / 1000000000000000000000000 : ℝ) < (1:ℝ)) probability_d0
    (by convert alpha_d0_first using 1; norm_num)
    (by convert alpha_d0_second using 1; norm_num)
  norm_num at h ⊢
  linarith

/-- The paper's strict Chernoff exponent at weight `350210`. -/
theorem divergence_beta_wstar : 4620069 < (2:ℝ)^36 * bernoulliKL (4589 / 20000 : ℝ) (rowProbability 350210) := by
  have h := divergence_lower (a := (4589 / 20000 : ℝ)) (p := rowProbability 350210)
    (by norm_num) (by norm_num) (by norm_num : (0:ℝ) < (117174946902109905191969 / 500000000000000000000000 : ℝ))
    (by norm_num : (234349893804219810424201 / 1000000000000000000000000 : ℝ) < (1:ℝ)) probability_wstar
    (by convert beta_wstar_first using 1; norm_num)
    (by convert beta_wstar_second using 1; norm_num)
  norm_num at h ⊢
  linarith

/-- The paper's strict Chernoff exponent at weight `12550000`. -/
theorem divergence_alpha_W : 319867786434 < (2:ℝ)^36 * bernoulliKL (4419 / 10000 : ℝ) (rowProbability 12550000) := by
  have h := divergence_lower (a := (4419 / 10000 : ℝ)) (p := rowProbability 12550000)
    (by norm_num) (by norm_num) (by norm_num : (0:ℝ) < (499965105668533162799269 / 500000000000000000000000 : ℝ))
    (by norm_num : (999930211337066325598543 / 1000000000000000000000000 : ℝ) < (1:ℝ)) probability_W
    (by convert alpha_W_first using 1; norm_num)
    (by convert alpha_W_second using 1; norm_num)
  norm_num at h ⊢
  linarith

/-- The paper's strict Chernoff exponent at weight `12550000`. -/
theorem divergence_beta_W : 469738761478 < (2:ℝ)^36 * bernoulliKL (4589 / 20000 : ℝ) (rowProbability 12550000) := by
  have h := divergence_lower (a := (4589 / 20000 : ℝ)) (p := rowProbability 12550000)
    (by norm_num) (by norm_num) (by norm_num : (0:ℝ) < (499965105668533162799269 / 500000000000000000000000 : ℝ))
    (by norm_num : (999930211337066325598543 / 1000000000000000000000000 : ℝ) < (1:ℝ)) probability_W
    (by convert beta_W_first using 1; norm_num)
    (by convert beta_W_second using 1; norm_num)
  norm_num at h ⊢
  linarith

/-- The paper's strict Chernoff exponent at weight `262657`. -/
theorem divergence_tau_e : 2702 < (2:ℝ)^36 * bernoulliKL (227 / 1250 : ℝ) (rowProbability 262657) := by
  have h := divergence_lower (a := (227 / 1250 : ℝ)) (p := rowProbability 262657)
    (by norm_num) (by norm_num) (by norm_num : (0:ℝ) < (11343243794685505617233 / 62500000000000000000000 : ℝ))
    (by norm_num : (90745950357484044959313 / 500000000000000000000000 : ℝ) < (1:ℝ)) probability_e
    (by convert tau_e_first using 1; norm_num)
    (by convert tau_e_second using 1; norm_num)
  norm_num at h ⊢
  linarith

/-- The paper's strict Chernoff exponent at weight `786433`. -/
theorem divergence_delta_d1 : 1565 < (2:ℝ)^36 * bernoulliKL (4511 / 10000 : ℝ) (rowProbability 786433) := by
  have h := divergence_lower (a := (4511 / 10000 : ℝ)) (p := rowProbability 786433)
    (by norm_num) (by norm_num) (by norm_num : (0:ℝ) < (450993797588798758967679 / 1000000000000000000000000 : ℝ))
    (by norm_num : (112748449397199689749141 / 250000000000000000000000 : ℝ) < (1:ℝ)) probability_d1
    (by convert delta_d1_first using 1; norm_num)
    (by convert delta_d1_second using 1; norm_num)
  norm_num at h ⊢
  linarith

theorem count_d0_upper :
    (784896:ℝ) * (1 + Real.log (68853957121/784896)) + 128*Real.log 2 < 9718630 := by
  have h₁ := count_d0
  have h₂ := log_two
  norm_num at h₁ h₂
  linarith

theorem count_wstar_upper :
    (350210:ℝ) * (1 + Real.log (68853957121/350210)) < 4618908 := by
  have h := count_wstar
  norm_num at h
  linarith

theorem count_global_upper :
    (3604584374:ℝ) * (128*Real.log 2) < 319808959479 := by
  have h := log_two
  norm_num at h
  linarith

theorem log_q_upper : (128:ℝ)*Real.log 2 < 89 := by
  have h := log_two
  norm_num at h
  linarith

theorem survival_W_lower :
    (697:ℝ)/10000000 < (1-(12550000:ℝ)/68853957121)^52500 := by
  have h := probability_W.2
  unfold rowProbability at h
  generalize (1-(12550000:ℝ)/68853957121)^52500 = y at h ⊢
  norm_num at h
  linarith

/-- The finite-field correction loses less than one part in a thousand
throughout the weight range used in the union bound. -/
theorem finite_field_correction_lower {r : ℝ} (hr : (697:ℝ)/10000000 ≤ r) :
    (999:ℝ)/1000 < ((1-1/(2:ℝ)^128)*r) /
      (1/(2:ℝ)^128+(1-1/(2:ℝ)^128)*r) := by
  have hpos : 0 < (1/(2:ℝ)^128+(1-1/(2:ℝ)^128)*r) := by nlinarith
  apply (lt_div_iff₀ hpos).mpr
  nlinarith

theorem derivative_envelope_lower {a b T p w : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hp : b ≤ p)
    (hw0 : 0 ≤ w) (hwn : w < 68853957121)
    (hnum : T < (999:ℝ)/1000 * 2^36 * 52500 / 68853957121 * (1-a/b)) :
    T < (999:ℝ)/1000 * 2^36 * 52500 / (68853957121-w) * (1-a/p) := by
  have hb : 0 < b := ha.trans_lt hab
  have hp0 : 0 < p := hb.trans_le hp
  have hfac : 1-a/b ≤ 1-a/p := by
    have := div_le_div_of_nonneg_left ha hb hp
    linarith
  have hfac0 : 0 ≤ 1-a/b := by
    have := (div_lt_one hb).mpr hab
    linarith
  have hbase : (999:ℝ)/1000 * 2^36 * 52500 / 68853957121 ≤
      (999:ℝ)/1000 * 2^36 * 52500 / (68853957121-w) :=
    div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  exact hnum.trans_le (mul_le_mul hbase hfac hfac0 (by positivity))

theorem derivative_alpha_lower {p w : ℝ} (hp : (45035:ℝ)/100000 ≤ p)
    (hw0 : 0 ≤ w) (hwn : w < 68853957121) :
    982 < (999:ℝ)/1000 * 2^36 * 52500 / (68853957121-w) * (1-(4419/10000)/p) :=
  derivative_envelope_lower (by norm_num) (by norm_num) hp hw0 hwn (by norm_num)

theorem derivative_beta_first_lower {p w : ℝ} (hp : (2343:ℝ)/10000 ≤ p)
    (hw0 : 0 ≤ w) (hwn : w < 68853957121) :
    1083 < (999:ℝ)/1000 * 2^36 * 52500 / (68853957121-w) * (1-(22945/100000)/p) :=
  derivative_envelope_lower (by norm_num) (by norm_num) hp hw0 hwn (by norm_num)

theorem derivative_beta_second_lower {p w : ℝ} (hp : (45035:ℝ)/100000 ≤ p)
    (hw0 : 0 ≤ w) (hwn : w < 68853957121) :
    25675 < (999:ℝ)/1000 * 2^36 * 52500 / (68853957121-w) * (1-(22945/100000)/p) :=
  derivative_envelope_lower (by norm_num) (by norm_num) hp hw0 hwn (by norm_num)

theorem log_derivative_alpha_upper :
    Real.log ((68853957121:ℝ)/784896) + 128*Real.log 2 < 101 := by
  have h₁ := count_d0
  have h₂ := log_two
  norm_num at h₁ h₂
  linarith

theorem log_derivative_beta_upper :
    Real.log ((68853957121:ℝ)/350210) < 13 := by
  have h := count_wstar
  norm_num at h
  linarith

theorem log_exceptional_count_upper : Real.log (18049720589484545:ℝ) < 38 := by
  have h := Real.log_le_sub_one_of_pos
    (by norm_num : (0:ℝ) < 18049720589484545/(2:ℝ)^54)
  rw [Real.log_div (by norm_num) (by positivity), Real.log_pow] at h
  have h₂ := log_two
  norm_num at h h₂
  linarith

theorem probability_d0_lower : (45035:ℝ)/100000 < rowProbability 784896 := by
  have h := probability_d0.1
  norm_num at h
  linarith

theorem probability_wstar_lower : (2343:ℝ)/10000 < rowProbability 350210 := by
  have h := probability_wstar.1
  norm_num at h
  linarith

/-- A deliberately generous budget: even one failure term for each low-weight
layer and each exceptional witness remains below one when every exponent is
at most `-1000`. The preceding strict bounds have larger margins. -/
theorem coarse_failure_budget :
    ((3:ℝ)*68853957121+18049720589484545+4)*Real.exp (-1000) < 1 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 1000) 10
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  rw [Real.exp_neg, ← div_eq_mul_inv]
  apply (div_lt_one (Real.exp_pos 1000)).mpr
  linarith

end OneAndAHalfJohnson.ConcreteAnalyticBounds
