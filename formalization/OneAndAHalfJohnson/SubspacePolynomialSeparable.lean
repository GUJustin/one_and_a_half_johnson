module

public import OneAndAHalfJohnson.SubspacePolynomial
public import Mathlib.FieldTheory.Separable

/-!
# The nonzero linear coefficient of the actual subspace polynomial

The normalization in Lemma 3.5 (pp. 10–11) divides by this coefficient.
Its nonvanishing follows from distinct roots, independently of the outstanding
Q-power-support theorem.
-/

@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson.SubspacePolynomial

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Fintype E]

/-- All roots of the actual root product are distinct. -/
theorem rootProduct_separable (W : Submodule K E) : (rootProduct W).Separable := by
  classical
  exact Polynomial.separable_prod_X_sub_C_iff.mpr Subtype.val_injective

/-- The zero constant term expresses that a linear subspace contains zero. -/
theorem rootProduct_coeff_zero (W : Submodule K E) : (rootProduct W).coeff 0 = 0 := by
  simpa only [Polynomial.coeff_zero_eq_eval_zero] using
    (rootProduct_eval_eq_zero W 0).mpr W.zero_mem

/-- The linear coefficient used to normalize the syndrome is nonzero. -/
theorem rootProduct_coeff_one_ne_zero (W : Submodule K E) :
    (rootProduct W).coeff 1 ≠ 0 := by
  have hz := (rootProduct_eval_eq_zero W 0).mpr W.zero_mem
  have h := (rootProduct_separable W).eval₂_derivative_ne_zero (RingHom.id E)
    (x := (0 : E)) (by simpa only [Polynomial.eval₂_id] using hz)
  simpa only [Polynomial.eval₂_id, ← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_derivative, zero_add, Nat.cast_zero, Nat.cast_one, mul_one] using h

end OneAndAHalfJohnson.SubspacePolynomial
