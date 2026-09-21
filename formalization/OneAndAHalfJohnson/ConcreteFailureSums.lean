module
public import OneAndAHalfJohnson.WeightLayerBounds
public import OneAndAHalfJohnson.LayerUnionBound
public import OneAndAHalfJohnson.ConcreteTailEnvelopes
public import OneAndAHalfJohnson.ConcreteLayerCounting
/-! Finite-family failure budgets, combining exact support layers with the
concrete analytic envelopes. No probabilistic independence is assumed here:
these are deterministic sums of the individual Chernoff bounds. -/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace OneAndAHalfJohnson
variable {F I : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype I] [DecidableEq I]

/-- Split a finite separated family into empty, support-counted, and globally
counted weight layers. This is the combinatorial interface for numeric tails. -/
theorem family_tail_sum_le (A : Finset (I → F)) (P : ℕ → ℝ)
    (d r W M : ℕ) (ε : ℝ) (hd : 0 < d) (hε : 0 ≤ ε)
    (hP : ∀ w, 0 ≤ P w)
    (hmin : ∀ v ∈ A, r ≤ hammingNorm v)
    (hsep : ∀ v ∈ A, ∀ u ∈ A, v ≠ u → d ≤ hammingDist v u)
    (hcard : A.card ≤ M)
    (hlayer : ∀ w, r ≤ w → w < W → w ≤ Fintype.card I →
      ((Fintype.card I).choose w : ℝ) *
        (Fintype.card F : ℝ)^(w-(d-1)) * P w ≤ ε)
    (hglobal : ∀ w, W ≤ w → w ≤ Fintype.card I → (M : ℝ) * P w ≤ ε) :
    ∑ v ∈ A, P (hammingNorm v) ≤ ((Fintype.card I : ℝ)+1)*ε := by
  apply sum_le_of_weight_layer_bounds
  intro w hwn
  by_cases hwr : w < r
  · have he : A.filter (fun v => hammingNorm v = w) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      obtain ⟨hvA,hvw⟩ := Finset.mem_filter.mp hv
      have hh := hmin v hvA
      omega
    simpa [he] using hε
  by_cases hwW : w < W
  · have hc := weight_layer_card_le A d w hd hsep
    have hcR : ((A.filter (fun v => hammingNorm v = w)).card : ℝ) ≤
        ((Fintype.card I).choose w : ℝ) * (Fintype.card F : ℝ)^(w-(d-1)) := by
      exact_mod_cast hc
    exact (mul_le_mul_of_nonneg_right hcR (hP w)).trans (hlayer w (by omega) hwW hwn)
  · have hc : (A.filter (fun v => hammingNorm v = w)).card ≤ M :=
      (Finset.card_filter_le _ _).trans hcard
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (hP w)).trans
      (hglobal w (by omega) hwn)

/-- Nonzero codewords as an actual finite word family. -/
def nonzeroCodeWords (C : Submodule F (I → F)) : Finset (I → F) := by
  classical
  exact Finset.univ.filter (fun v => v ∈ C ∧ v ≠ 0)

/-- Nonzero words have weight at least the code distance. -/
theorem nonzeroCodeWords_min (C : Submodule F (I → F))
    (v : I → F) (hv : v ∈ nonzeroCodeWords C) :
    Code.dist (C : Set (I → F)) ≤ hammingNorm v := by
  classical
  have hh : v ∈ C ∧ v ≠ 0 := (Finset.mem_filter.mp hv).2
  apply Nat.sInf_le
  refine ⟨v,hh.1,0,C.zero_mem,hh.2,?_⟩
  simp

/-- Nonzero codewords form a subset of the zero affine coset. -/
theorem nonzeroCodeWords_subset (C : Submodule F (I → F)) :
    nonzeroCodeWords C ⊆ affineCodeWords C 0 := by
  classical
  intro v hv
  have hh : v ∈ C ∧ v ≠ 0 := (Finset.mem_filter.mp hv).2
  simpa [affineCodeWords] using hh.1


/-- An exponential identity for the logarithm of a finite-field cardinality. -/
theorem field_power_as_exp (r k : ℕ) :
    ((2:ℝ)^r)^k = Real.exp ((k:ℝ)*((r:ℝ)*Real.log 2)) := by
  rw [Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<2)]

/-- Convert a logarithmic tail envelope without evaluating a giant integer. -/
theorem global_tail_of_exponent {a : ℝ}
    (h : (3604584374:ℝ)*(128*Real.log 2) - (2:ℝ)^36*a ≤ -1000) :
    ((2:ℝ)^128)^3604584374 * Real.exp (-(2:ℝ)^36*a) ≤ Real.exp (-1000) := by
  rw [field_power_as_exp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simpa only [Nat.cast_ofNat, sub_eq_add_neg, neg_mul] using h

/-- Source distance bounds are exactly minimum-weight bounds in its affine coset. -/
theorem affineCodeWords_min_of_source (C : Submodule F (I → F)) (f : I → F)
    (r : ℕ) (hr : ∀ c ∈ C, r ≤ hammingDist f c) :
    ∀ v ∈ affineCodeWords C f, r ≤ hammingNorm v := by
  classical
  intro v hv
  have hvC : v-f ∈ C := (Finset.mem_filter.mp hv).2
  have hc : f-v ∈ C := by simpa only [neg_sub] using C.neg_mem hvC
  have hh := hr (f-v) hc
  have he : hammingDist f (f-v) = hammingNorm v := by
    unfold hammingDist hammingNorm
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply]
    constructor
    · intro h hz
      apply h
      simp [hz]
    · intro h he
      apply h
      have hh := congrArg (fun x => f i - x) he
      simpa using hh.symm
  rwa [he] at hh

/-- Transfer concrete scalar tail envelopes to any separated family of the
advertised dimension and minimum weight. Numeric inputs are isolated here so
that the code and affine-coset applications share the same counting proof. -/
theorem concrete_family_failure_sum
    (A : Finset (I → F)) (a : ℝ) (r : ℕ)
    (hF : Fintype.card F = 2^128) (hI : Fintype.card I = 68853957121)
    (hmin : ∀ v ∈ A, r ≤ hammingNorm v)
    (hsep : ∀ v ∈ A, ∀ u ∈ A, v ≠ u → 784896 ≤ hammingDist v u)
    (hcard : A.card ≤ Fintype.card F ^ 3604584374)
    (hlayer : ∀ w : ℕ, r ≤ w → w < 12550000 →
      ((68853957121:ℕ).choose w : ℝ) * ((2:ℝ)^128)^(w-784895) *
        Real.exp (-(2:ℝ)^36 * bernoulliKL a (ConcreteAnalyticBounds.rowProbability w)) ≤
          Real.exp (-1000))
    (hglobal : ∀ w : ℕ, 12550000 ≤ w → w ≤ 68853957121 →
      (3604584374:ℝ)*(128*Real.log 2) - (2:ℝ)^36 *
        bernoulliKL a (ConcreteAnalyticBounds.rowProbability w) ≤ -1000) :
    ∑ v ∈ A, Real.exp (-(2:ℝ)^36 *
      bernoulliKL a (ConcreteAnalyticBounds.rowProbability (hammingNorm v))) ≤
        (68853957121+1:ℝ)*Real.exp (-1000) := by
  have hh := family_tail_sum_le A
    (fun w => Real.exp (-(2:ℝ)^36 * bernoulliKL a (ConcreteAnalyticBounds.rowProbability w)))
    784896 r 12550000 (Fintype.card F ^ 3604584374) (Real.exp (-1000))
    (by omega) (Real.exp_nonneg _) (fun _ => Real.exp_nonneg _) hmin hsep hcard
  rw [hI] at hh
  apply hh
  · intro w hwr hwW _
    simpa only [hF, Nat.cast_pow, Nat.cast_ofNat] using hlayer w hwr hwW
  · intro w hwW hwn
    have ht := global_tail_of_exponent (hglobal w hwW hwn)
    simpa only [hF, Nat.cast_pow, Nat.cast_ofNat] using ht

/-- Total lower-tail failure budget for every actual nonzero concrete codeword. -/
theorem concrete_nonzero_failure_sum (C : Submodule F (I → F))
    (hF : Fintype.card F = 2^128) (hI : Fintype.card I = 68853957121)
    (hk : Module.finrank F C = 3604584374)
    (hd : 784896 ≤ Code.dist (C : Set (I → F))) :
    ∑ v ∈ nonzeroCodeWords C, Real.exp (-(2:ℝ)^36 * bernoulliKL (4419/10000)
      (ConcreteAnalyticBounds.rowProbability (hammingNorm v))) ≤
        (68853957121+1:ℝ)*Real.exp (-1000) := by
  apply concrete_family_failure_sum _ _ 784896 hF hI
  · intro v hv
    exact hd.trans (nonzeroCodeWords_min C v hv)
  · intro v hv u hu hne
    exact hd.trans (affineCodeWords_separated C 0 v (nonzeroCodeWords_subset C hv)
      u (nonzeroCodeWords_subset C hu) hne)
  · have hh := Finset.card_le_card (nonzeroCodeWords_subset C)
    rwa [affineCodeWords_card, hk] at hh
  · intro w hw hwW
    exact ConcreteAnalyticBounds.layer_tail_of_exponent _ w hw
      (ConcreteAnalyticBounds.layer_alpha_exponent (by exact_mod_cast hw)
        (by exact_mod_cast hwW.le)).le
  · intro w hw hwn
    exact (ConcreteAnalyticBounds.global_alpha_exponent
      (by exact_mod_cast hw) (by exact_mod_cast hwn)).le

/-- Total lower-tail failure budget for every word in an actual source coset. -/
theorem concrete_affine_failure_sum (C : Submodule F (I → F)) (f : I → F)
    (hF : Fintype.card F = 2^128) (hI : Fintype.card I = 68853957121)
    (hk : Module.finrank F C = 3604584374)
    (hd : 784896 ≤ Code.dist (C : Set (I → F)))
    (hf : ∀ c ∈ C, 350210 ≤ hammingDist f c) :
    ∑ v ∈ affineCodeWords C f, Real.exp (-(2:ℝ)^36 * bernoulliKL (22945/100000)
      (ConcreteAnalyticBounds.rowProbability (hammingNorm v))) ≤
        (68853957121+1:ℝ)*Real.exp (-1000) := by
  apply concrete_family_failure_sum _ _ 350210 hF hI
  · exact affineCodeWords_min_of_source C f 350210 hf
  · intro v hv u hu hne
    exact hd.trans (affineCodeWords_separated C f v hv u hu hne)
  · rw [affineCodeWords_card, hk]
  · intro w hw hwW
    by_cases hw0 : w < 784896
    · rw [show w-784895=0 by omega, pow_zero, mul_one]
      exact ConcreteAnalyticBounds.layer_tail_of_exponent_zero _ w (by omega)
        (ConcreteAnalyticBounds.layer_beta_exponent (by exact_mod_cast hw)
          (by exact_mod_cast hwW.le) le_rfl (by positivity)).le
    · exact ConcreteAnalyticBounds.layer_tail_of_exponent _ w (by omega)
        (ConcreteAnalyticBounds.layer_beta_exponent (by exact_mod_cast hw)
          (by exact_mod_cast hwW.le) (by positivity) le_rfl).le
  · intro w hw hwn
    exact (ConcreteAnalyticBounds.global_beta_exponent
      (by exact_mod_cast hw) (by exact_mod_cast hwn)).le

end OneAndAHalfJohnson
