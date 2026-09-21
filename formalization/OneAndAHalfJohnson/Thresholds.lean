module

public import OneAndAHalfJohnson.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Radius comparisons

Elementary real inequalities used in the introduction (p. 2) and amplification
argument (pp. 12–14) of ePrint 2026/1894.
-/

@[expose] public section
namespace OneAndAHalfJohnson

/-- The defining-vector threshold strictly exceeds the exceptional threshold. -/
theorem johnson_lt_gamma {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) :
    johnson δ < gamma δ := by
  have h := Real.rpow_lt_rpow_of_exponent_gt
    (show 0 < 1 - δ by linarith) (show 1 - δ < 1 by linarith)
    (show (1 / 3 : ℝ) < 4 / 9 by norm_num)
  unfold johnson gamma
  linarith

/-- The defining-vector threshold remains below the target code distance. -/
theorem gamma_lt_distance {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) :
    gamma δ < δ := by
  have h := Real.self_lt_rpow_of_lt_one
    (show 0 < 1 - δ by linarith) (show 1 - δ < 1 by linarith)
    (show (4 / 9 : ℝ) < 1 by norm_num)
  unfold gamma
  linarith

/-- Sampling preserves zero weight under the ideal distance transform. -/
theorem amplify_zero (t : ℕ) : amplify t 0 = 0 := by simp [amplify]

/-- More nonzero coordinates increase the ideal amplified weight. -/
theorem amplify_mono (t : ℕ) {u v : ℝ} (huv : u ≤ v) (hv : v ≤ 1) :
    amplify t u ≤ amplify t v := by
  unfold amplify
  have h : (1 - v) ^ t ≤ (1 - u) ^ t :=
    pow_le_pow_left₀ (by linarith) (by linarith) t
  linarith

/-- Exactly the distance range where the one-and-a-half Johnson radius
lies below the unique-decoding radius (Corollary 1.2, p. 3). -/
theorem johnson_lt_half_iff {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) :
    johnson δ < δ / 2 ↔ δ < 3 - Real.sqrt 5 := by
  have hs0 := Real.sqrt_nonneg (5 : ℝ)
  have hs : (Real.sqrt (5 : ℝ)) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs2 : 2 < Real.sqrt (5 : ℝ) := by nlinarith
  have hbase : 0 ≤ 1 - δ := by linarith
  have hc0 : 0 ≤ (1 - δ) ^ (1 / 3 : ℝ) := Real.rpow_nonneg hbase _
  have hc : ((1 - δ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = 1 - δ := by
    rw [← Real.rpow_mul_natCast hbase]
    norm_num
  have hequiv : johnson δ < δ / 2 ↔ (1 - δ / 2) ^ (3 : ℕ) < 1 - δ := by
    unfold johnson
    constructor
    · intro h
      have hp := pow_lt_pow_left₀ (show 1 - δ / 2 < (1 - δ) ^ (1 / 3 : ℝ) by linarith)
        (show 0 ≤ 1 - δ / 2 by linarith) (by decide : (3 : ℕ) ≠ 0)
      simpa only [hc] using hp
    · intro h
      by_contra hn
      have hp := pow_le_pow_left₀ hc0
        (show (1 - δ) ^ (1 / 3 : ℝ) ≤ 1 - δ / 2 by linarith) 3
      rw [hc] at hp
      linarith
  rw [hequiv]
  constructor
  · intro h
    have hquad : 0 < δ ^ 2 - 6 * δ + 4 := by
      nlinarith
    nlinarith
  · intro h
    have hquad : 0 < δ ^ 2 - 6 * δ + 4 := by
      nlinarith [sq_nonneg (3 - δ - Real.sqrt 5)]
    nlinarith [mul_pos h0 hquad]

/-- The exceptional radius in Theorem 4.1 exceeds the Johnson radius even
at the upper endpoint of the code-distance interval. -/
theorem concrete_johnson_upper : johnson (4511 / 10000) < 1816 / 10000 := by
  have hbase : (0 : ℝ) ≤ 1 - 4511 / 10000 := by norm_num
  have hc0 : 0 ≤ (1 - (4511 / 10000 : ℝ)) ^ (1 / 3 : ℝ) :=
    Real.rpow_nonneg hbase _
  have hc : ((1 - (4511 / 10000 : ℝ)) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) =
      1 - 4511 / 10000 := by
    rw [← Real.rpow_mul_natCast hbase]
    norm_num
  unfold johnson
  by_contra h
  have hp := pow_le_pow_left₀ hc0
    (show (1 - (4511 / 10000 : ℝ)) ^ (1 / 3 : ℝ) ≤ 1 - 1816 / 10000 by linarith) 3
  rw [hc] at hp
  norm_num at hp

/-- Increasing the target distance increases the one-and-a-half Johnson radius. -/
theorem johnson_mono {δ δ' : ℝ} (h : δ ≤ δ') (h' : δ' ≤ 1) :
    johnson δ ≤ johnson δ' := by
  have hh := Real.rpow_le_rpow (by linarith : 0 ≤ 1 - δ')
    (by linarith : 1 - δ' ≤ 1 - δ) (by norm_num : (0 : ℝ) ≤ 1 / 3)
  unfold johnson
  linarith

end OneAndAHalfJohnson
