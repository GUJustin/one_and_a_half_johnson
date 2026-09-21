module

public import OneAndAHalfJohnson.SubspacePolynomialShape
public import OneAndAHalfJohnson.SubspacePolynomialSeparable
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Algebra.BigOperators.Field

/-!
# Power sums over finite vector subspaces

Moment identities for the actual subspace root product used in Lemma 3.5.
The constant derivative and low moments follow from Q-power support and
Lagrange interpolation at the elements of the subspace.
-/

@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson.SubspacePolynomial
open Polynomial

variable {K E : Type*} [Field K] [Fintype K] [Field E] [Algebra K E] [Fintype E]

local instance (W : Submodule K E) : Fintype W := Fintype.ofFinite W
local instance (W : Submodule K E) : DecidableEq W := Classical.decEq W

omit [Fintype E] in
/-- The geometry field cardinality is zero in every extension field. -/
theorem geometry_card_cast_eq_zero : (Fintype.card K : E) = 0 := by
  have h := congrArg (algebraMap K E) (Nat.cast_card_eq_zero K)
  simpa only [map_natCast, map_zero] using h

/-- Every nonlinear term of the subspace polynomial has zero derivative. -/
theorem rootProduct_derivative (W : Submodule K E) :
    (rootProduct W).derivative = C ((rootProduct W).coeff 1) := by
  ext n
  rw [coeff_derivative, coeff_C]
  by_cases hn : n = 0
  · simp [hn]
  · simp only [ite_eq_right hn]
    by_cases hc : (rootProduct W).coeff (n + 1) = 0
    · simp [hc]
    · obtain ⟨j, hj, he⟩ := rootProduct_qPowerSupport W (n + 1) hc
      have hj0 : j ≠ 0 := by intro h; simp [h] at he; omega
      have hcast : ((n + 1 : ℕ) : E) = 0 := by
        rw [he, Nat.cast_pow, geometry_card_cast_eq_zero (K := K), zero_pow hj0]
      simpa only [Nat.cast_add, Nat.cast_one, mul_zero] using congrArg
        (fun z : E => (rootProduct W).coeff (n + 1) * z) hcast

/-- The Lagrange denominator at every element is the same nonzero coefficient. -/
theorem rootProduct_lagrange_denominator (W : Submodule K E) (w : W) :
    (∏ z ∈ (Finset.univ : Finset W).erase w, ((w : E) - z)) =
      (rootProduct W).coeff 1 := by
  classical
  have h := Lagrange.eval_nodal_derivative_eval_node_eq
    (s := (Finset.univ : Finset W)) (v := fun z : W => (z : E)) (Finset.mem_univ w)
  have he : Lagrange.nodal Finset.univ (fun z : W => (z : E)) = rootProduct W := by
    simp only [Lagrange.nodal, rootProduct]
    congr 1
    ext x
    simp
  rw [he, rootProduct_derivative, eval_C, Lagrange.eval_nodal] at h
  exact h.symm

/-- Summation of a polynomial of degree below the subspace cardinality extracts
its coefficient at one less than that cardinality, scaled by the linear term. -/
theorem sum_eval_eq_linear_coeff_mul (W : Submodule K E) (P : Polynomial E)
    (hP : P.degree < (Fintype.card W : WithBot ℕ)) :
    (∑ w : W, P.eval (w : E)) =
      (rootProduct W).coeff 1 * P.coeff (Fintype.card W - 1) := by
  classical
  have h := Lagrange.coeff_eq_sum
    (s := (Finset.univ : Finset W)) (v := fun w : W => (w : E))
    Subtype.val_injective.injOn (P := P) (by simpa using hP)
  simp only [Finset.card_univ, rootProduct_lagrange_denominator, ← Finset.sum_div] at h
  have he := (eq_div_iff (rootProduct_coeff_one_ne_zero W)).mp h
  simpa [mul_comm] using he.symm

/-- The moment functional on powers of the extension-field coordinate. -/
def moment (W : Submodule K E) (t : ℕ) : E := ∑ w : W, (w : E) ^ t

/-- All moments below cardinality minus one vanish; that last moment is the
nonzero linear coefficient of the subspace polynomial. -/
theorem moment_lt_card (W : Submodule K E) (t : ℕ) (ht : t < Fintype.card W) :
    moment W t = if t = Fintype.card W - 1 then (rootProduct W).coeff 1 else 0 := by
  have h := sum_eval_eq_linear_coeff_mul W (X ^ t) (by simpa using ht)
  simpa only [moment, eval_pow, eval_X, coeff_X_pow, mul_ite, mul_one, mul_zero,
    eq_comm] using h

/-- Every higher moment satisfies the recurrence given by the monic root
polynomial. This is an identity over the actual finite subspace. -/
theorem moment_recurrence (W : Submodule K E) (t : ℕ) :
    moment W (t + Fintype.card W) +
      ∑ i ∈ Finset.range (Fintype.card W), (rootProduct W).coeff i * moment W (t + i) = 0 := by
  classical
  have hd : (rootProduct W).natDegree = Fintype.card W := by
    rw [rootProduct_natDegree]
    exact (Module.card_eq_pow_finrank (K := K) (V := W)).symm
  have hpoly := (rootProduct_monic W).as_sum
  rw [hd] at hpoly
  have hw (w : W) : (w : E) ^ (t + Fintype.card W) +
      ∑ i ∈ Finset.range (Fintype.card W), (rootProduct W).coeff i * (w : E) ^ (t + i) = 0 := by
    have hz := (rootProduct_eval_eq_zero W (w : E)).mpr w.property
    rw [hpoly] at hz
    simp only [eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C] at hz
    have hh := congrArg (fun z : E => (w : E) ^ t * z) hz
    simpa [mul_add, Finset.mul_sum, pow_add, mul_assoc, mul_left_comm] using hh
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun w _ => hw w)
  simpa only [Finset.sum_add_distrib, Finset.sum_const_zero, ← Finset.mul_sum,
    moment, Finset.sum_comm] using hsum

/-- A gap below the leading term forces a corresponding gap in the moments. -/
theorem moment_middle_eq_zero (W : Submodule K E) (A t : ℕ)
    (ht : Fintype.card W ≤ t) (hsmall : t + A < 2 * Fintype.card W - 1)
    (htail : ∀ i, i < Fintype.card W → (rootProduct W).coeff i ≠ 0 → i ≤ A) :
    moment W t = 0 := by
  have hrec := moment_recurrence W (t - Fintype.card W)
  have hs : (∑ i ∈ Finset.range (Fintype.card W),
      (rootProduct W).coeff i * moment W (t - Fintype.card W + i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hc : (rootProduct W).coeff i = 0
    · simp [hc]
    · have hiA := htail i (Finset.mem_range.mp hi) hc
      have hu : t - Fintype.card W + i < Fintype.card W := by omega
      have hu' : t - Fintype.card W + i ≠ Fintype.card W - 1 := by omega
      rw [moment_lt_card W _ hu, ite_eq_right hu', mul_zero]
  rw [hs, add_zero, Nat.sub_add_cancel ht] at hrec
  exact hrec

/-- The next relevant moments extract individual lower coefficients whenever
the root polynomial has a sufficiently large gap below its leading term. -/
theorem moment_high_eq_neg_coeff (W : Submodule K E) (A b : ℕ)
    (hb : 1 ≤ b) (hbA : b ≤ A) (hAn : A < Fintype.card W)
    (hgap : 2 * A < Fintype.card W + b)
    (htail : ∀ i, i < Fintype.card W → (rootProduct W).coeff i ≠ 0 → i ≤ A) :
    moment W (2 * Fintype.card W - b - 1) =
      -(rootProduct W).coeff 1 * (rootProduct W).coeff b := by
  have hrec := moment_recurrence W (Fintype.card W - b - 1)
  have hbN : b < Fintype.card W := lt_of_le_of_lt hbA hAn
  have he : Fintype.card W - b - 1 + Fintype.card W =
      2 * Fintype.card W - b - 1 := by omega
  rw [he] at hrec
  have hs : (∑ i ∈ Finset.range (Fintype.card W), (rootProduct W).coeff i *
      moment W (Fintype.card W - b - 1 + i)) =
      (rootProduct W).coeff b * (rootProduct W).coeff 1 := by
    rw [Finset.sum_eq_single b]
    · have he' : Fintype.card W - b - 1 + b = Fintype.card W - 1 := by omega
      rw [he', moment_lt_card W _ (by omega), ite_eq_left rfl]
    · intro i hi hib
      by_cases hc : (rootProduct W).coeff i = 0
      · simp [hc]
      · have hiA := htail i (Finset.mem_range.mp hi) hc
        by_cases hil : i < b
        · have hu : Fintype.card W - b - 1 + i < Fintype.card W := by omega
          have hu' : Fintype.card W - b - 1 + i ≠ Fintype.card W - 1 := by omega
          rw [moment_lt_card W _ hu, ite_eq_right hu', mul_zero]
        · have hu : Fintype.card W ≤ Fintype.card W - b - 1 + i := by omega
          rw [moment_middle_eq_zero W A _ hu (by omega) htail, mul_zero]
    · intro h
      exact (h (Finset.mem_range.mpr hbN)).elim
  rw [hs] at hrec
  have hz := eq_neg_of_add_eq_zero_left hrec
  simpa [neg_mul, mul_comm] using hz

/-- Q-power support bounds every coefficient strictly below the leading term
by the immediately preceding Q-power. -/
theorem rootProduct_tail_bound (W : Submodule K E) (hr : 1 ≤ Module.finrank K W)
    (i : ℕ) (hi : i < Fintype.card W) (hc : (rootProduct W).coeff i ≠ 0) :
    i ≤ Fintype.card K ^ (Module.finrank K W - 1) := by
  obtain ⟨j, hj, rfl⟩ := rootProduct_qPowerSupport W i hc
  have hn : Fintype.card W = Fintype.card K ^ Module.finrank K W :=
    Module.card_eq_pow_finrank (K := K) (V := W)
  have hj' : j < Module.finrank K W := by
    rw [hn] at hi
    by_contra h
    exact (not_lt_of_ge (Nat.pow_le_pow_right Fintype.card_pos (Nat.le_of_not_gt h))) hi
  exact Nat.pow_le_pow_right Fintype.card_pos (by omega)

/-- The first distinguished power sum is the linear coefficient. -/
theorem moment_card_sub_one (W : Submodule K E) :
    moment W (Fintype.card W - 1) = (rootProduct W).coeff 1 := by
  rw [moment_lt_card W _ (Nat.sub_lt Fintype.card_pos (by omega)), ite_eq_left rfl]

/-- The coefficient-extracting power sums used for both non-leading syndrome
coordinates; valid for every lower Q-power when the field order exceeds two. -/
theorem moment_two_card_sub_qpow_sub_one (W : Submodule K E)
    (hQ : 2 < Fintype.card K) (j : ℕ) (hj : j < Module.finrank K W) :
    moment W (2 * Fintype.card W - Fintype.card K ^ j - 1) =
      -(rootProduct W).coeff 1 * (rootProduct W).coeff (Fintype.card K ^ j) := by
  have hr : 1 ≤ Module.finrank K W := by omega
  have hn : Fintype.card W = Fintype.card K ^ Module.finrank K W :=
    Module.card_eq_pow_finrank (K := K) (V := W)
  have hn' : Fintype.card W = Fintype.card K *
      Fintype.card K ^ (Module.finrank K W - 1) := by
    rw [hn, ← pow_succ']
    congr 1
    omega
  apply moment_high_eq_neg_coeff W (Fintype.card K ^ (Module.finrank K W - 1))
      (Fintype.card K ^ j)
  · exact Nat.one_le_pow _ _ (by omega)
  · exact Nat.pow_le_pow_right Fintype.card_pos (by omega)
  · rw [hn]
    exact Nat.pow_lt_pow_right (by omega) (by omega)
  · have hpos : 0 < Fintype.card K ^ (Module.finrank K W - 1) := Nat.pow_pos Fintype.card_pos
    have hmul := Nat.mul_lt_mul_of_pos_right hQ hpos
    rw [← hn'] at hmul
    omega
  · exact rootProduct_tail_bound W hr

/-- The three concrete finite power sums displayed in Lemma 3.5 (p. 10).
The ambient subspace has dimension `m-2`; all coefficients refer to its actual
root-product polynomial. No moment identity is assumed. -/
theorem rootProduct_distinguished_moments (W : Submodule K E) (m : ℕ)
    (hm : 4 ≤ m) (hW : Module.finrank K W + 2 = m) (hQ : 2 < Fintype.card K) :
    (∑ w : W, (w : E) ^ (Fintype.card K ^ (m - 2) - 1)) =
        (rootProduct W).coeff 1 ∧
    (∑ w : W, (w : E) ^ (2 * Fintype.card K ^ (m - 2) -
        Fintype.card K ^ (m - 3) - 1)) =
        -(rootProduct W).coeff 1 * (rootProduct W).coeff (Fintype.card K ^ (m - 3)) ∧
    (∑ w : W, (w : E) ^ (2 * Fintype.card K ^ (m - 2) -
        Fintype.card K ^ (m - 4) - 1)) =
        -(rootProduct W).coeff 1 * (rootProduct W).coeff (Fintype.card K ^ (m - 4)) := by
  have hr : Module.finrank K W = m - 2 := by omega
  have hn : Fintype.card W = Fintype.card K ^ (m - 2) := by
    rw [Module.card_eq_pow_finrank (K := K) (V := W), hr]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [moment, hn] using moment_card_sub_one W
  · simpa only [moment, hn] using
      moment_two_card_sub_qpow_sub_one W hQ (m - 3) (by omega)
  · simpa only [moment, hn] using
      moment_two_card_sub_qpow_sub_one W hQ (m - 4) (by omega)

end OneAndAHalfJohnson.SubspacePolynomial
