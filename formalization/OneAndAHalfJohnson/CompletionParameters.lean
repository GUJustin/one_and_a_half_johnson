module

public import OneAndAHalfJohnson.CodeCompletion
public import Mathlib.Tactic.FieldSimp

/-!
# Quantitative parameters for distance-preserving completion

The greedy completion condition follows from `q^h ≥ 4·2^N` whenever the
forbidden coset radius is below the code distance. This covers the paper's
factor-eight asymptotic choice and factor-four concrete choice.

For the asymptotic rate claim this module uses the faithful alternative integer
choice `h = (N+3)/s + 1`. It proves the required power threshold and the uniform
rate error `6/s` whenever the alphabet has size `p^s`, `p≥2`, and `N≥s≥1`.
No real logarithm, upper bound on block length, or external theorem is needed
for this completion step. Constructing the input code and obtaining its initial
distance/coset separation remain obligations of the base and amplification steps.
-/

@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson

/-- A power bound on the requested Singleton defect implies the forbidden-set
cardinality criterion. This even allows the coset radius `b = d-1`. -/
theorem completion_cardinality_of_defect_power
    (q N d b K h : ℕ) (hq : 0 < q) (hbd : b < d)
    (hbalance : K + (d - 1) + h = N)
    (hpower : 4 * 2 ^ N ≤ q ^ h) :
    (2 ^ N * q ^ (d - 1) + 2 ^ (N + 1) * q ^ b) * q ^ K < q ^ N := by
  have hb : b ≤ d - 1 := by omega
  have hqpow : q ^ b ≤ q ^ (d - 1) := Nat.pow_le_pow_right hq hb
  have hc : 3 * 2 ^ N < q ^ h := by
    have hp : 0 < (2 : ℕ) ^ N := Nat.pow_pos (by decide)
    omega
  calc
    (2 ^ N * q ^ (d - 1) + 2 ^ (N + 1) * q ^ b) * q ^ K ≤
        (3 * 2 ^ N) * q ^ (K + (d - 1)) := by
      calc
        _ ≤ (2 ^ N * q ^ (d - 1) + 2 ^ (N + 1) * q ^ (d - 1)) * q ^ K :=
          Nat.mul_le_mul_right _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ hqpow) _)
        _ = _ := by rw [pow_add q K (d - 1), pow_succ]; ring
    _ < q ^ h * q ^ (K + (d - 1)) :=
      Nat.mul_lt_mul_of_pos_right hc (Nat.pow_pos hq)
    _ = q ^ N := by rw [← pow_add]; congr 1; omega

/-- Singleton defect with subtraction performed after adding the unit term. -/
def singletonDefect {F I : Type*} [Field F] [DecidableEq F] [Fintype I]
    (C : Submodule F (I → F)) : ℕ :=
  Fintype.card I + 1 - (Module.finrank F C + Code.dist (C : Set (I → F)))

/-- The Singleton inequality supplies the exact natural-number defect identity. -/
theorem singletonDefect_balance {F I : Type*} [Field F] [DecidableEq F] [Fintype I]
    (C : Submodule F (I → F)) :
    Module.finrank F C + Code.dist (C : Set (I → F)) + singletonDefect C =
      Fintype.card I + 1 := by
  have hs := LinearCode.singleton_bound_linear C
  change Module.finrank F C ≤ Fintype.card I - Code.dist (C : Set (I → F)) + 1 at hs
  have hd := Code.dist_le_card (C : Set (I → F))
  unfold singletonDefect
  omega

/-- Every nonzero code whose two words are farther than `b` can be enlarged
while keeping those properties and obtaining defect at most `h`, provided
`b` is below its minimum distance and `q^h ≥ 4·2^N`. -/
theorem exists_completion_defect_eq_min
    {F I : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype I] [DecidableEq I]
    (C₀ : Submodule F (I → F)) (f g : I → F) (b h : ℕ)
    (hne : ∃ c ∈ C₀, c ≠ 0)
    (hf : ∀ c ∈ C₀, b < hammingDist f c)
    (hg : ∀ c ∈ C₀, b < hammingDist g c)
    (hbd : b < Code.dist (C₀ : Set (I → F)))
    (hpower : 4 * 2 ^ Fintype.card I ≤ Fintype.card F ^ h) :
    ∃ C : Submodule F (I → F), C₀ ≤ C ∧
      Code.dist (C : Set (I → F)) = Code.dist (C₀ : Set (I → F)) ∧
      (∀ c ∈ C, b < hammingDist f c) ∧
      (∀ c ∈ C, b < hammingDist g c) ∧
      singletonDefect C = min (singletonDefect C₀) h := by
  by_cases hsmall : singletonDefect C₀ ≤ h
  · exact ⟨C₀, le_rfl, rfl, hf, hg, (min_eq_left hsmall).symm⟩
  let d := Code.dist (C₀ : Set (I → F))
  let K := Fintype.card I + 1 - (d + h)
  have hbalance₀ := singletonDefect_balance C₀
  have hK : Module.finrank F C₀ ≤ K := by dsimp [K, d]; omega
  have hbalance : K + (d - 1) + h = Fintype.card I := by dsimp [K, d]; omega
  have hsize := completion_cardinality_of_defect_power (Fintype.card F)
    (Fintype.card I) d b K h Fintype.card_pos hbd hbalance hpower
  obtain ⟨C, hC, hdim, hdist, hfC, hgC⟩ := exists_code_completion C₀ f g b K hne hf hg hK hsize
  refine ⟨C, hC, hdist, hfC, hgC, ?_⟩
  rw [min_eq_right (show h ≤ singletonDefect C₀ by omega)]
  unfold singletonDefect
  rw [hdim, hdist]
  change Fintype.card I + 1 - (K + d) = h
  omega

/-- The defect-upper-bound form, including the already-small-defect branch. -/
theorem exists_completion_defect_le
    {F I : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype I] [DecidableEq I]
    (C₀ : Submodule F (I → F)) (f g : I → F) (b h : ℕ)
    (hne : ∃ c ∈ C₀, c ≠ 0)
    (hf : ∀ c ∈ C₀, b < hammingDist f c)
    (hg : ∀ c ∈ C₀, b < hammingDist g c)
    (hbd : b < Code.dist (C₀ : Set (I → F)))
    (hpower : 4 * 2 ^ Fintype.card I ≤ Fintype.card F ^ h) :
    ∃ C : Submodule F (I → F), C₀ ≤ C ∧
      Code.dist (C : Set (I → F)) = Code.dist (C₀ : Set (I → F)) ∧
      (∀ c ∈ C, b < hammingDist f c) ∧
      (∀ c ∈ C, b < hammingDist g c) ∧ singletonDefect C ≤ h := by
  obtain ⟨C,hC,hd,hfC,hgC,he⟩ :=
    exists_completion_defect_eq_min C₀ f g b h hne hf hg hbd hpower
  exact ⟨C,hC,hd,hfC,hgC,he.le.trans (min_le_right _ _)⟩

/-- Exact rate identity in terms of the actual Singleton defect. -/
theorem rate_eq_one_sub_distance_add_defect
    {F I : Type*} [Field F] [DecidableEq F] [Fintype I]
    (C : Submodule F (I → F)) (hN : 0 < Fintype.card I) :
    rate C = 1 - relativeDistance C +
      (1 - (singletonDefect C : ℝ)) / Fintype.card I := by
  have hbalance : (Module.finrank F C : ℝ) + Code.dist (C : Set (I → F)) +
      singletonDefect C = (Fintype.card I : ℝ) + 1 := by
    exact_mod_cast singletonDefect_balance C
  have hn : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  unfold rate relativeDistance
  field_simp
  nlinarith

/-- A bounded Singleton defect gives a uniform quantitative rate error. -/
theorem rate_error_le_of_defect_le
    {F I : Type*} [Field F] [DecidableEq F] [Fintype I]
    (C : Submodule F (I → F)) (hN : 0 < Fintype.card I) (h : ℕ)
    (hdef : singletonDefect C ≤ h) :
    |rate C - (1 - relativeDistance C)| ≤ ((h : ℝ) + 1) / Fintype.card I := by
  have hnr : (0 : ℝ) < Fintype.card I := by exact_mod_cast hN
  have hd : (singletonDefect C : ℝ) ≤ h := by exact_mod_cast hdef
  have hd0 : (0 : ℝ) ≤ singletonDefect C := Nat.cast_nonneg _
  have ha : |1 - (singletonDefect C : ℝ)| ≤ (h : ℝ) + 1 := by
    apply abs_le.mpr
    constructor <;> linarith
  rw [rate_eq_one_sub_distance_add_defect C hN]
  simp only [add_sub_cancel_left, abs_div, abs_of_pos hnr]
  exact div_le_div_of_nonneg_right ha hnr.le

/-- A symbolic exponent comparison supplies the factor-four threshold for a
power-of-two alphabet, avoiding evaluation of the field-sized powers. -/
theorem completion_defect_power_of_exponent_bound (n a h : ℕ)
    (hexponent : n + 2 ≤ a * h) :
    4 * (2 : ℕ) ^ n ≤ (2 ^ a) ^ h := by
  have he : 4 * (2 : ℕ) ^ n = 2 ^ (n + 2) := by
    rw [pow_add, show (2 : ℕ) ^ 2 = 4 by norm_num, Nat.mul_comm]
  rw [he, ← pow_mul]
  exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hexponent

/-- The concrete defect exponent exceeds the exact required exponent. -/
theorem concrete_completion_exponent : (2 : ℕ) ^ 36 + 2 ≤ 128 * 536870913 := by
  norm_num

/-- The concrete parameters satisfy the factor-four defect-power condition.
The symbolic helper prevents reduction of enormous field-sized powers. -/
theorem concrete_completion_defect_power :
    4 * (2 : ℕ) ^ (2 ^ 36) ≤ (2 ^ 128) ^ 536870913 :=
  completion_defect_power_of_exponent_bound (2 ^ 36) 128 536870913
    concrete_completion_exponent

/-- An integer-only choice of completion defect with a uniform `O(1/s)` rate
cost for length at least `s`. No real logarithm or ceiling is required. -/
def asymptoticCompletionDefect (N s : ℕ) : ℕ := (N + 3) / s + 1

/-- The quotient-and-remainder identity gives a strict exponent margin. -/
theorem asymptoticCompletionDefect_exponent (N s : ℕ) (hs : 0 < s) :
    N + 3 < s * asymptoticCompletionDefect N s := by
  have hm := Nat.mod_lt (N + 3) hs
  have he := Nat.mod_add_div (N + 3) s
  unfold asymptoticCompletionDefect
  nlinarith

/-- Over every alphabet `p^s` with `p≥2`, the integer defect choice covers
factor eight times the binary support count. -/
theorem asymptoticCompletionDefect_power (p N s : ℕ) (hp : 2 ≤ p) (hs : 0 < s) :
    8 * (2 : ℕ) ^ N ≤ (p ^ s) ^ asymptoticCompletionDefect N s := by
  have he : 8 * (2 : ℕ) ^ N = 2 ^ (N + 3) := by
    rw [pow_add, show (2 : ℕ) ^ 3 = 8 by norm_num, Nat.mul_comm]
  rw [he, ← pow_mul]
  exact (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
    (asymptoticCompletionDefect_exponent N s hs).le).trans
    (Nat.pow_le_pow_left hp _)

/-- The rate-error cost of the integer defect choice is uniformly at most
`6/s` for every length `N≥s≥1`. -/
theorem asymptoticCompletionDefect_rate_bound (N s : ℕ) (hs : 0 < s) (hNs : s ≤ N) :
    ((asymptoticCompletionDefect N s : ℝ) + 1) / N ≤ 6 / (s : ℝ) := by
  have hnat : (asymptoticCompletionDefect N s + 1) * s ≤ 6 * N := by
    have he := Nat.mod_add_div (N + 3) s
    unfold asymptoticCompletionDefect
    calc
      ((N + 3) / s + 1 + 1) * s = s * ((N + 3) / s) + 2 * s := by ring
      _ ≤ N + 3 + 2 * s := Nat.add_le_add_right (by omega) _
      _ ≤ 6 * N := by omega
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hNR : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le hs hNs)
  apply (div_le_div_iff₀ hNR hsR).mpr
  exact_mod_cast hnat

/-- Complete any nonzero code over a field of cardinality `p^s` while retaining
its distance and both word-separation bounds, at uniform rate error `6/s`.
This theorem proves the main paper's completion step independently of its base
construction and amplification. Its initial-code hypotheses still must be
supplied by those constructions. -/
theorem exists_completion_rate_error_le_six_div
    {F I : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype I] [DecidableEq I]
    (C₀ : Submodule F (I → F)) (f g : I → F) (b p s : ℕ)
    (hp : 2 ≤ p) (hs : 0 < s) (hcard : Fintype.card F = p ^ s)
    (hNs : s ≤ Fintype.card I)
    (hne : ∃ c ∈ C₀, c ≠ 0)
    (hf : ∀ c ∈ C₀, b < hammingDist f c)
    (hg : ∀ c ∈ C₀, b < hammingDist g c)
    (hbd : b < Code.dist (C₀ : Set (I → F))) :
    ∃ C : Submodule F (I → F), C₀ ≤ C ∧
      Code.dist (C : Set (I → F)) = Code.dist (C₀ : Set (I → F)) ∧
      (∀ c ∈ C, b < hammingDist f c) ∧
      (∀ c ∈ C, b < hammingDist g c) ∧
      |rate C - (1 - relativeDistance C)| ≤ 6 / (s : ℝ) := by
  let h := asymptoticCompletionDefect (Fintype.card I) s
  have hpower : 4 * 2 ^ Fintype.card I ≤ Fintype.card F ^ h := by
    rw [hcard]
    exact (Nat.mul_le_mul_right _ (by decide : 4 ≤ (8 : ℕ))).trans
      (asymptoticCompletionDefect_power p (Fintype.card I) s hp hs)
  obtain ⟨C,hC,hd,hfC,hgC,hdef⟩ :=
    exists_completion_defect_le C₀ f g b h hne hf hg hbd hpower
  refine ⟨C,hC,hd,hfC,hgC, ?_⟩
  exact (rate_error_le_of_defect_le C (lt_of_lt_of_le hs hNs) h hdef).trans
    (asymptoticCompletionDefect_rate_bound (Fintype.card I) s hs hNs)

end OneAndAHalfJohnson
