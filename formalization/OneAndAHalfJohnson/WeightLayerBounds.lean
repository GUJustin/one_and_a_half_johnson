module
public import OneAndAHalfJohnson.Basic
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.FieldTheory.Finiteness
/-! Combinatorial bounds for the concrete weight-layer union argument. -/
@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson
/-- The elementary exponential upper bound on a binomial coefficient. -/
theorem choose_le_exp_log_bound (n w : ℕ) (hn : 0 < n) (hw : 0 < w) :
    (n.choose w : ℝ) ≤ Real.exp ((w : ℝ) * Real.log (Real.exp 1 * n / w)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hpow : (0 : ℝ) < (w : ℝ) ^ w := pow_pos hwR _
  have hfac := Real.pow_div_factorial_le_exp (w : ℝ) hwR.le w
  have hc := Nat.choose_le_pow_div (α := ℝ) w n
  have hmul := mul_le_mul_of_nonneg_left hfac (pow_nonneg (div_nonneg hnR.le hwR.le) w)
  have hidentity : ((n : ℝ) / w) ^ w * ((w : ℝ) ^ w / w.factorial) =
      (n : ℝ) ^ w / w.factorial := by
    rw [div_pow]
    field_simp
  rw [hidentity] at hmul
  apply hc.trans
  convert hmul using 1
  rw [Real.log_div (ne_of_gt (mul_pos (Real.exp_pos _) hnR)) (ne_of_gt hwR),
    Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt hnR), Real.log_exp,
    mul_sub, mul_add, mul_one, Real.exp_sub, Real.exp_add,
    Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log hnR, Real.exp_log hwR, div_pow]
  ring
variable {F I : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype I] [DecidableEq I]

/-- A family supported on S with pairwise distance at least d is determined by
any |S|−(d−1) surviving coordinates. This includes empty and singleton families. -/
theorem supported_family_card_le (A : Finset (I → F)) (S : Finset I) (d : ℕ)
    (hd : 0 < d) (hsupp : ∀ v ∈ A, ∀ i ∉ S, v i = 0)
    (hsep : ∀ v ∈ A, ∀ w ∈ A, v ≠ w → d ≤ hammingDist v w) :
    A.card ≤ Fintype.card F ^ (S.card - (d - 1)) := by
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq (Nat.sub_le S.card (d - 1))
  let r : A → T → F := fun v i => v.val i.val
  have hinj : Function.Injective r := by
    intro v w hr
    apply Subtype.ext
    by_contra hne
    have hdist := hsep v.val v.property w.val w.property hne
    have hsub : Finset.univ.filter (fun i => v.val i ≠ w.val i) ⊆ S \ T := by
      intro i hi
      have hvw : v.val i ≠ w.val i := (Finset.mem_filter.mp hi).2
      apply Finset.mem_sdiff.mpr
      constructor
      · by_contra hiS
        exact hvw ((hsupp _ v.property i hiS).trans (hsupp _ w.property i hiS).symm)
      · intro hiT
        exact hvw (congrFun hr ⟨i,hiT⟩)
    have hbound : hammingDist v.val w.val ≤ (S \ T).card := Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset hTS, hTcard] at hbound
    omega
  have hc := Fintype.card_le_of_injective r hinj
  simpa only [Fintype.card_coe, Fintype.card_fun, hTcard] using hc

/-- Covering a weight layer by its exact supports gives the shortened Singleton
bound on the number of words in that layer. -/
theorem weight_layer_card_le (A : Finset (I → F)) (d w : ℕ) (hd : 0 < d)
    (hsep : ∀ v ∈ A, ∀ u ∈ A, v ≠ u → d ≤ hammingDist v u) :
    (A.filter (fun v => hammingNorm v = w)).card ≤
      (Fintype.card I).choose w * Fintype.card F ^ (w - (d - 1)) := by
  classical
  let B (S : Finset I) := A.filter (fun v => ∀ i ∉ S, v i = 0)
  have hcover : A.filter (fun v => hammingNorm v = w) ⊆
      (Finset.univ.powersetCard w).biUnion B := by
    intro v hv
    obtain ⟨hvA,hvw⟩ := Finset.mem_filter.mp hv
    let S : Finset I := Finset.univ.filter (fun i => v i ≠ 0)
    apply Finset.mem_biUnion.mpr
    refine ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hvw⟩, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨hvA, ?_⟩
    intro i hi
    simpa [S] using hi
  have hb (S : Finset I) (hS : S ∈ Finset.univ.powersetCard w) :
      (B S).card ≤ Fintype.card F ^ (w - (d - 1)) := by
    have hc := (Finset.mem_powersetCard.mp hS).2
    rw [← hc]
    exact supported_family_card_le (B S) S d hd
      (fun v hv => (Finset.mem_filter.mp hv).2)
      (fun v hv u hu => hsep v (Finset.mem_filter.mp hv).1 u (Finset.mem_filter.mp hu).1)
  calc
    _ ≤ ((Finset.univ.powersetCard w).biUnion B).card := Finset.card_le_card hcover
    _ ≤ ∑ S ∈ Finset.univ.powersetCard w, (B S).card := Finset.card_biUnion_le
    _ ≤ ∑ _S ∈ Finset.univ.powersetCard w, Fintype.card F ^ (w - (d - 1)) :=
      Finset.sum_le_sum hb
    _ = _ := by simp

/-- The actual affine translate of a linear code, represented as a finite set. -/
def affineCodeWords (C : Submodule F (I → F)) (f : I → F) : Finset (I → F) := by
  classical
  exact Finset.univ.filter (fun v => v - f ∈ C)

omit [DecidableEq F] in
/-- Translation preserves the exact size of a linear code. -/
theorem affineCodeWords_card (C : Submodule F (I → F)) (f : I → F) :
    (affineCodeWords C f).card = Fintype.card F ^ Module.finrank F C := by
  classical
  let e : C ≃ ↥(affineCodeWords C f) :=
    { toFun := fun c => ⟨c.val + f, by simp [affineCodeWords]⟩
      invFun := fun v => ⟨v.val - f, by simpa [affineCodeWords] using v.property⟩
      left_inv := fun c => by ext; simp
      right_inv := fun v => by ext; simp }
  rw [← Fintype.card_coe, ← Fintype.card_congr e]
  exact Module.card_eq_pow_finrank

/-- Two distinct words of the same affine coset have at least the code distance. -/
theorem affineCodeWords_separated (C : Submodule F (I → F)) (f : I → F)
    (v : I → F) (hv : v ∈ affineCodeWords C f)
    (u : I → F) (hu : u ∈ affineCodeWords C f) (hne : v ≠ u) :
    Code.dist (C : Set (I → F)) ≤ hammingDist v u := by
  classical
  have hvC : v - f ∈ C := (Finset.mem_filter.mp hv).2
  have huC : u - f ∈ C := (Finset.mem_filter.mp hu).2
  have hne' : v - f ≠ u - f := fun he => hne (sub_left_injective he)
  have hh : Code.dist (C : Set (I → F)) ≤ hammingDist (v - f) (u - f) :=
    Nat.sInf_le ⟨v-f,hvC,u-f,huC,hne',le_rfl⟩
  have he : hammingDist (v-f) (u-f) = hammingDist v u := by
    unfold hammingDist
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply]
    exact not_congr ⟨fun h => sub_left_injective h, fun h => congrArg (fun x => x - f i) h⟩
  rwa [he] at hh

/-- The weight-layer bound for an actual affine code coset. -/
theorem affineCodeWords_layer_card_le (C : Submodule F (I → F)) (f : I → F)
    (d w : ℕ) (hd : 0 < d) (hC : d ≤ Code.dist (C : Set (I → F))) :
    ((affineCodeWords C f).filter (fun v => hammingNorm v = w)).card ≤
      (Fintype.card I).choose w * Fintype.card F ^ (w - (d - 1)) :=
  weight_layer_card_le _ d w hd
    (fun v hv u hu hne => hC.trans (affineCodeWords_separated C f v hv u hu hne))

end OneAndAHalfJohnson
