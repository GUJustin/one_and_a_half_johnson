module

public import OneAndAHalfJohnson.Amplification
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.FieldSimp

/-!
# Uniform polynomial block-length thresholds

A dimension bound polynomial in the field exponent implies a single polynomial
block-length threshold making the Hoeffding union bound strictly below one.
Constants are selected before the growing exponent and length. This module
also bounds the finite-field bias in the exact sampled mean.
-/

@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson

/-- An explicit coefficient for the required polynomial block length. -/
def amplificationSizeConstant (p R : ℕ) (B ε : ℝ) : ℝ :=
  ((R : ℝ) * B * Real.log p + 2) / (2 * ε ^ 2)

/-- Convert field cardinality and code dimension bounds into an exponential
bound with a uniform polynomial exponent. The dimension coefficient may be real. -/
theorem family_card_le_exp_of_dimension_bound
    (p R d s r k C : ℕ) (B : ℝ) (hp : 2 ≤ p)
    (hr : r ≤ R) (hk : (k : ℝ) ≤ B * (s : ℝ) ^ d)
    (hC : C ≤ (p ^ s) ^ (r * k)) :
    (C : ℝ) ≤ Real.exp ((R : ℝ) * B * Real.log p * (s : ℝ) ^ (d + 1)) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
  have hrR : (r : ℝ) ≤ R := by exact_mod_cast hr
  have hprod : (r : ℝ) * k ≤ (R : ℝ) * (B * (s : ℝ) ^ d) :=
    mul_le_mul hrR hk (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hprod
    (mul_nonneg (Nat.cast_nonneg s) hlog)
  have hexponent : (s : ℝ) * (r : ℝ) * k * Real.log p ≤
      (R : ℝ) * B * Real.log p * (s : ℝ) ^ (d + 1) := by
    rw [pow_succ]
    nlinarith [hmul]
  have hpow : (((p ^ s) ^ (r * k) : ℕ) : ℝ) =
      Real.exp ((s : ℝ) * (r : ℝ) * k * Real.log p) := by
    have he := Real.exp_nat_mul (Real.log (p : ℝ)) (s * (r * k))
    rw [Real.exp_log hpR] at he
    simpa only [Nat.cast_pow, Nat.cast_mul, pow_mul, mul_assoc] using he.symm
  calc
    (C : ℝ) ≤ ((p ^ s) ^ (r * k) : ℕ) := by exact_mod_cast hC
    _ = _ := hpow
    _ ≤ _ := Real.exp_le_exp.mpr hexponent

/-- The explicit polynomial threshold forces the complete finite-family
Hoeffding failure bound below one, uniformly over field exponents and lengths. -/
theorem hoeffding_union_lt_one_of_polynomial_length
    (p R d : ℕ) (B ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε)
    (s r k C N : ℕ) (hs : 1 ≤ s) (hr : r ≤ R)
    (hk : (k : ℝ) ≤ B * (s : ℝ) ^ d) (hC : C ≤ (p ^ s) ^ (r * k))
    (hN : amplificationSizeConstant p R B ε * (s : ℝ) ^ (d + 1) ≤ N) :
    2 * (C : ℝ) * Real.exp (-2 * ε ^ 2 * N) < 1 := by
  have hcard := family_card_le_exp_of_dimension_bound p R d s r k C B hp hr hk hC
  have hden : 0 < 2 * ε ^ 2 := by positivity
  have hscale : ((R : ℝ) * B * Real.log p + 2) * (s : ℝ) ^ (d + 1) ≤
      2 * ε ^ 2 * N := by
    have hh := mul_le_mul_of_nonneg_left hN hden.le
    unfold amplificationSizeConstant at hh
    field_simp at hh
    nlinarith [hh]
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hspow : (1 : ℝ) ≤ (s : ℝ) ^ (d + 1) := one_le_pow₀ hsR
  have hexponent : (R : ℝ) * B * Real.log p * (s : ℝ) ^ (d + 1) +
      (-2 * ε ^ 2 * N) ≤ -2 := by nlinarith [hscale]
  have he : (2 : ℝ) < Real.exp 2 := by
    have hh := Real.add_one_lt_exp (show (2 : ℝ) ≠ 0 by norm_num)
    linarith
  have hlast : 2 * Real.exp (-2) < 1 := by
    rw [Real.exp_neg]
    exact (mul_inv_lt_iff₀ (Real.exp_pos 2)).mpr (by simpa using he)
  calc
    2 * (C : ℝ) * Real.exp (-2 * ε ^ 2 * N) ≤
        2 * Real.exp ((R : ℝ) * B * Real.log p * (s : ℝ) ^ (d + 1)) *
          Real.exp (-2 * ε ^ 2 * N) := by gcongr
    _ = 2 * Real.exp ((R : ℝ) * B * Real.log p * (s : ℝ) ^ (d + 1) +
        (-2 * ε ^ 2 * N)) := by rw [mul_assoc, ← Real.exp_add]
    _ ≤ 2 * Real.exp (-2) := by gcongr
    _ < 1 := hlast

/-- Positivity of the chosen block-length coefficient. -/
theorem amplificationSizeConstant_pos (p R : ℕ) (B ε : ℝ)
    (hp : 2 ≤ p) (hB : 0 ≤ B) (hε : 0 < ε) :
    0 < amplificationSizeConstant p R B ε := by
  have hl : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
  unfold amplificationSizeConstant
  apply div_pos
  · have hh := mul_nonneg (mul_nonneg (Nat.cast_nonneg R) hB) hl
    linarith
  · positivity

/-- The coefficient is chosen before every field exponent, dimension and block
length; this is the uniform quantifier order required by Theorem 3.1. -/
theorem exists_polynomial_hoeffding_threshold
    (p R d : ℕ) (B ε : ℝ) (hp : 2 ≤ p) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ s r k C N : ℕ,
      1 ≤ s → r ≤ R → (k : ℝ) ≤ B * (s : ℝ) ^ d →
      C ≤ (p ^ s) ^ (r * k) → A * (s : ℝ) ^ (d + 1) ≤ N →
      2 * (C : ℝ) * Real.exp (-2 * ε ^ 2 * N) < 1 := by
  refine ⟨amplificationSizeConstant p R B ε,
    amplificationSizeConstant_pos p R B ε hp hB hε, ?_⟩
  exact fun s r k C N hs hr hk hC hN =>
    hoeffding_union_lt_one_of_polynomial_length p R d B ε hp hε s r k C N hs hr hk hC hN

/-- The ideal amplification transform maps the unit interval into itself. -/
theorem amplify_mem_Icc (t : ℕ) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    amplify t u ∈ Set.Icc (0 : ℝ) 1 := by
  have hb0 : 0 ≤ 1 - u := by linarith [hu.2]
  have hb1 : 1 - u ≤ 1 := by linarith [hu.1]
  have hp0 := pow_nonneg hb0 t
  have hp1 := pow_le_one₀ hb0 hb1 (n := t)
  unfold amplify
  constructor <;> linarith

/-- Absorb the exact finite-field success factor into an additive `1/q` error. -/
theorem amplification_error_le_add_inv
    (t : ℕ) (q u w ε : ℝ) (hq : 0 < q) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (happrox : |w - (1 - 1 / q) * amplify t u| ≤ ε) :
    |w - amplify t u| ≤ ε + 1 / q := by
  have hΦ := amplify_mem_Icc t hu
  have hbias : |(1 - 1 / q) * amplify t u - amplify t u| ≤ 1 / q := by
    have he : (1 - 1 / q) * amplify t u - amplify t u = -(amplify t u) / q := by ring
    rw [he, abs_div, abs_neg, abs_of_nonneg hΦ.1, abs_of_pos hq]
    exact div_le_div_of_nonneg_right hΦ.2 hq.le
  calc
    |w - amplify t u| =
        |(w - (1 - 1 / q) * amplify t u) + ((1 - 1 / q) * amplify t u - amplify t u)| := by
      congr 1
      ring
    _ ≤ |w - (1 - 1 / q) * amplify t u| +
        |(1 - 1 / q) * amplify t u - amplify t u| := abs_add_le _ _
    _ ≤ ε + 1 / q := add_le_add happrox hbias

end OneAndAHalfJohnson
