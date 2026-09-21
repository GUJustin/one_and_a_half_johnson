module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic

/-! Rational certificates for exponential and logarithm bounds.
All numerical premises are rational arithmetic, checked by the Lean kernel. -/
@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson.NumericLogCertificates

theorem exp_interval {x L U : ℝ} (n : ℕ) (hn : 0 < n) (hx : |x| ≤ 1)
    (hL : L ≤ (∑ i ∈ Finset.range n, x^i / i.factorial) -
      |x|^n*((n+1)/(n.factorial*n)))
    (hU : (∑ i ∈ Finset.range n, x^i / i.factorial) +
      |x|^n*((n+1)/(n.factorial*n)) ≤ U) : L ≤ Real.exp x ∧ Real.exp x ≤ U := by
  have h := Real.exp_bound hx hn
  have hh := abs_le.mp h
  push_cast at hL hU hh
  constructor <;> linarith

theorem exp_double_interval {x l u L U : ℝ}
    (hx : l ≤ Real.exp x ∧ Real.exp x ≤ u) (hl : 0 ≤ l)
    (hL : L ≤ l*l) (hU : u*u ≤ U) : L ≤ Real.exp (2*x) ∧ Real.exp (2*x) ≤ U := by
  rw [two_mul, Real.exp_add]
  have he := (Real.exp_pos x).le
  exact ⟨hL.trans (mul_le_mul hx.1 hx.1 hl he),
    (mul_le_mul hx.2 hx.2 he (he.trans hx.2)).trans hU⟩

end OneAndAHalfJohnson.NumericLogCertificates
