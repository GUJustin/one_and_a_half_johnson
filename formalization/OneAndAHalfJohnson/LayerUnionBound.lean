module
public import OneAndAHalfJohnson.Basic
/-! Summing finite word-family tail bounds by exact Hamming weight layers. -/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace OneAndAHalfJohnson
variable {F I : Type*} [Field F] [DecidableEq F] [Fintype I]

/-- Exact regrouping of a finite word family by Hamming weight. -/
theorem sum_by_weight_layers (A : Finset (I → F)) (P : ℕ → ℝ) :
    ∑ v ∈ A, P (hammingNorm v) =
      ∑ w ∈ Finset.range (Fintype.card I + 1),
        ((A.filter (fun v => hammingNorm v = w)).card : ℝ) * P w := by
  classical
  have hm : ∀ v ∈ A, hammingNorm v ∈ Finset.range (Fintype.card I + 1) := by
    intro v hv
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hammingNorm_le_card_fintype)
  rw [← Finset.sum_fiberwise_of_maps_to hm]
  apply Finset.sum_congr rfl
  intro w hw
  have he : ∑ v ∈ A.filter (fun v => hammingNorm v = w), P (hammingNorm v) =
      ∑ _v ∈ A.filter (fun v => hammingNorm v = w), P w := by
    apply Finset.sum_congr rfl
    intro v hv
    rw [(Finset.mem_filter.mp hv).2]
  rw [he, Finset.sum_const, nsmul_eq_mul]

/-- One uniform budget per layer gives a finite-family union bound. -/
theorem sum_le_of_weight_layer_bounds (A : Finset (I → F)) (P : ℕ → ℝ) (ε : ℝ)
    (hP : ∀ w ≤ Fintype.card I,
      ((A.filter (fun v => hammingNorm v = w)).card : ℝ) * P w ≤ ε) :
    (∑ v ∈ A, P (hammingNorm v)) ≤ ((Fintype.card I : ℝ) + 1) * ε := by
  rw [sum_by_weight_layers]
  calc
    _ ≤ ∑ _w ∈ Finset.range (Fintype.card I + 1), ε := by
      apply Finset.sum_le_sum
      intro w hw
      exact hP w (Nat.le_of_lt_succ (Finset.mem_range.mp hw))
    _ = _ := by simp
end OneAndAHalfJohnson
