module
public import OneAndAHalfJohnson.ConcreteLayerDerivative
public import OneAndAHalfJohnson.WeightLayerBounds
/-! Conversion of the analytic layer exponent into the actual combinatorial
binomial and finite-field factors in the concrete union bound. -/
@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson.ConcreteAnalyticBounds

/-- Binomial support counts in the logarithmic form used by the derivative proof. -/
theorem concrete_choose_le_exp (w : ℕ) (hw : 0 < w) :
    ((68853957121:ℕ).choose w : ℝ) ≤
      Real.exp ((w:ℝ)*(1+Real.log (68853957121/w))) := by
  have hh := choose_le_exp_log_bound 68853957121 w (by omega) hw
  have hwR : (0:ℝ)<w := by exact_mod_cast hw
  have he : Real.exp 1 * (68853957121:ℝ) / w = Real.exp 1 * (68853957121/w) := by ring
  norm_num only [Nat.cast_ofNat] at hh
  rw [he, Real.log_mul (Real.exp_ne_zero _) (ne_of_gt (div_pos (by norm_num) hwR)),
    Real.log_exp] at hh
  exact hh

/-- The layer exponent with no field factor bounds the actual binomial tail. -/
theorem layer_tail_of_exponent_zero (a : ℝ) (w : ℕ) (hw : 0 < w)
    (h : layerExponent a 0 w ≤ -1000) :
    ((68853957121:ℕ).choose w : ℝ) *
      Real.exp (-(2:ℝ)^36*bernoulliKL a (rowProbability w)) ≤ Real.exp (-1000) := by
  apply (mul_le_mul_of_nonneg_right (concrete_choose_le_exp w hw) (Real.exp_nonneg _)).trans
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simpa only [layerExponent,mul_zero,add_zero,sub_eq_add_neg,neg_mul] using h

/-- Above the minimum code distance, the actual shortened Singleton field
factor has exactly the logarithm appearing in the analytic envelope. -/
theorem layer_tail_of_exponent (a : ℝ) (w : ℕ) (hw : 784896 ≤ w)
    (h : layerExponent a (128*Real.log 2) w ≤ -1000) :
    ((68853957121:ℕ).choose w : ℝ) * ((2:ℝ)^128)^(w-784895) *
      Real.exp (-(2:ℝ)^36*bernoulliKL a (rowProbability w)) ≤ Real.exp (-1000) := by
  have hpow : ((2:ℝ)^128)^(w-784895) =
      Real.exp (((w:ℝ)-784895)*(128*Real.log 2)) := by
    rw [← show ((w-784895:ℕ):ℝ) = (w:ℝ)-784895 by
      rw [Nat.cast_sub (by omega)]; norm_num]
    rw [Real.exp_nat_mul]
    congr 1
    have hh := Real.exp_nat_mul (Real.log 2) 128
    simpa only [Nat.cast_ofNat,Real.exp_log (by norm_num : (0:ℝ)<2)] using hh.symm
  apply (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (concrete_choose_le_exp w (by omega)) (by positivity))
    (Real.exp_nonneg _)).trans
  rw [hpow, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simpa only [layerExponent,sub_eq_add_neg,neg_mul] using h

end OneAndAHalfJohnson.ConcreteAnalyticBounds
