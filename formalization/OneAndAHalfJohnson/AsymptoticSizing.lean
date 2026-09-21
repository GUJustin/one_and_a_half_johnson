module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

/-! # One uniform threshold for field size and polynomial output length -/
@[expose] public section
noncomputable section
open Filter Topology
namespace OneAndAHalfJohnson

/-- Choose all size constants before the growing exponent and block length. -/
theorem exists_final_size_threshold (p a d : ℕ) (hp : 2 ≤ p) (ha : 1 ≤ a)
    (ξ H : ℝ) (hξ : 0 < ξ) (_hH : 0 < H) :
    ∃ A : ℝ, 0 < A ∧ ∃ s₀ : ℕ, 1 ≤ s₀ ∧ ∀ s : ℕ, s₀ ≤ s → ∀ N : ℕ,
      A * (s : ℝ) ^ (d + 1) ≤ N →
      4 * (2 * a) ≤ s ∧ s ≤ N ∧ H * (s : ℝ) ^ (d + 1) ≤ N ∧
        1 / (p ^ s : ℝ) < ξ := by
  have hpow : Tendsto (fun s : ℕ => (p : ℝ) ^ s) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast hp)
  have hinv : Tendsto (fun s : ℕ => 1 / (p ^ s : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hpow
  obtain ⟨s₁,hs₁⟩ := eventually_atTop.mp (hinv.eventually_lt_const hξ)
  refine ⟨max 1 H, lt_of_lt_of_le zero_lt_one (le_max_left _ _), max s₁ (4 * (2 * a)), ?_, ?_⟩
  · have h := le_max_right s₁ (4 * (2 * a)); omega
  · intro s hs N hN
    have hslarge : 4 * (2 * a) ≤ s := (le_max_right _ _).trans hs
    have hspos : 1 ≤ s := by omega
    have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hspos
    have hspow : (s : ℝ) ≤ (s : ℝ) ^ (d + 1) := by
      rw [pow_succ]
      nlinarith [one_le_pow₀ hsR (n := d)]
    have hN' : (s : ℝ) ^ (d + 1) ≤ N := le_trans
      (by nlinarith [le_max_left (1 : ℝ) H, pow_nonneg (show (0 : ℝ) ≤ (s : ℝ) from Nat.cast_nonneg s) (d+1)]) hN
    refine ⟨hslarge, ?_, ?_, hs₁ s ((le_max_left _ _).trans hs)⟩
    · exact_mod_cast hspow.trans hN'
    · exact (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)).trans hN

end OneAndAHalfJohnson
