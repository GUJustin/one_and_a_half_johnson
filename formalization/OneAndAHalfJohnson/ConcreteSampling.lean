module
public import OneAndAHalfJohnson.RefinedRandomAmplification
public import OneAndAHalfJohnson.ConcreteProbabilityCalculus
public import OneAndAHalfJohnson.ConcreteFailureSums
/-! The actual concrete sampling map (Section 4, pp. 17–19).
The lower families comprise all nonzero codewords and both entire affine cosets.
The upper family includes every exceptional witness and a nonzero short codeword.
Exact mean identities and the summed KL bounds select one map for all families. -/
/-! Concrete finite-family sampling on actual words, with the certified
relative-entropy failure budget of Section 4. -/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace OneAndAHalfJohnson
open ConcreteAnalyticBounds

/-- The concrete finite row experiment has exactly the certified mean. -/
theorem sampledMean_concrete {F I : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype I] (hF : Fintype.card F = 2^128) (hI : Fintype.card I = 68853957121)
    (v : I → F) : sampledMean (F:=F) 52500 v = rowProbability (hammingNorm v) := by
  simp only [sampledMean,relativeWeight,amplify,rowProbability,hF,hI,Nat.cast_pow,Nat.cast_ofNat]

/-- Exact finite-family sampling from the three lower-tail budgets and the
certified upper-tail witness bounds. -/
theorem exists_concrete_sampling_map
    {F I J W : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype I] [DecidableEq I] [Fintype J] [Fintype W]
    (C : Submodule F (I → F)) (f g h₀ : I → F) (v : W → I → F)
    (hF : Fintype.card F = 2^128) (hI : Fintype.card I = 68853957121)
    (hJ : Fintype.card J = 2^36) (hW : Fintype.card W = 18049720589484545)
    (hd : 784896 ≤ Code.dist (C : Set (I → F)))
    (hfmin : ∀ x ∈ affineCodeWords C f, 350210 ≤ hammingNorm x)
    (hgmin : ∀ x ∈ affineCodeWords C g, 350210 ≤ hammingNorm x)
    (hh₀ : h₀ ≠ 0) (hh₀weight : hammingNorm h₀ ≤ 786433)
    (hv : ∀ w, hammingNorm (v w) = 262657)
    (hs0 : (∑ x ∈ nonzeroCodeWords C, Real.exp (-(2:ℝ)^36*
      bernoulliKL (4419/10000) (rowProbability (hammingNorm x)))) ≤
      (68853957121+1)*Real.exp (-1000))
    (hsf : (∑ x ∈ affineCodeWords C f, Real.exp (-(2:ℝ)^36*
      bernoulliKL (22945/100000) (rowProbability (hammingNorm x)))) ≤
      (68853957121+1)*Real.exp (-1000))
    (hsg : (∑ x ∈ affineCodeWords C g, Real.exp (-(2:ℝ)^36*
      bernoulliKL (22945/100000) (rowProbability (hammingNorm x)))) ≤
      (68853957121+1)*Real.exp (-1000)) :
    ∃ A : (I → F) →ₗ[F] (J → F),
      (∀ c ∈ C, c ≠ 0 → 4419/10000 < relativeWeight (A c)) ∧
      (∀ c ∈ C, 22945/100000 < relativeWeight (A (f-c))) ∧
      (∀ c ∈ C, 22945/100000 < relativeWeight (A (g-c))) ∧
      relativeWeight (A h₀) < 4511/10000 ∧
      (∀ w, relativeWeight (A (v w)) < 1816/10000) := by
  classical
  let : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  let : Nonempty J := Fintype.card_pos_iff.mp (by rw [hJ]; positivity)
  let L := (↥(nonzeroCodeWords C)) ⊕ ((↥(affineCodeWords C f)) ⊕ (↥(affineCodeWords C g)))
  let vl : L → I → F := Sum.elim Subtype.val (Sum.elim Subtype.val Subtype.val)
  let al : L → ℝ := Sum.elim (fun _ => 4419/10000) (fun _ => 22945/100000)
  let vu : Option W → I → F := fun w => w.elim h₀ v
  let au : Option W → ℝ := fun w => w.elim (4511/10000) (fun _ => 1816/10000)
  have hnorm (x : I → F) : (hammingNorm x:ℝ) ≤ 68853957121 := by
    have hh := hammingNorm_le_card_fintype (x:=x)
    rw [hI] at hh
    exact_mod_cast hh
  have hlcode (x : I → F) (hx : x ∈ nonzeroCodeWords C) :
      0 < sampledMean (F:=F) 52500 x ∧ sampledMean (F:=F) 52500 x < 1 ∧
      4419/10000 ≤ sampledMean (F:=F) 52500 x := by
    rw [sampledMean_concrete hF hI]
    have hw : (784896:ℝ) ≤ hammingNorm x := by exact_mod_cast hd.trans (nonzeroCodeWords_min C x hx)
    have hp := rowProbability_monotone (by norm_num : (784896:ℝ) ∈ Set.Icc 0 68853957121)
      ⟨by linarith,hnorm x⟩ hw
    have hi := rowProbability_mem_Ioo (by linarith : (0:ℝ)<hammingNorm x) (hnorm x)
    exact ⟨hi.1,hi.2,by linarith [probability_d0_lower]⟩
  have hlaffine (x : I → F) (hx : 350210 ≤ hammingNorm x) :
      0 < sampledMean (F:=F) 52500 x ∧ sampledMean (F:=F) 52500 x < 1 ∧
      22945/100000 ≤ sampledMean (F:=F) 52500 x := by
    rw [sampledMean_concrete hF hI]
    have hw : (350210:ℝ) ≤ hammingNorm x := by exact_mod_cast hx
    have hp := rowProbability_monotone (by norm_num : (350210:ℝ) ∈ Set.Icc 0 68853957121)
      ⟨by linarith,hnorm x⟩ hw
    have hi := rowProbability_mem_Ioo (by linarith : (0:ℝ)<hammingNorm x) (hnorm x)
    exact ⟨hi.1,hi.2,by linarith [probability_wstar_lower]⟩
  have hL (x : L) : 0 < al x ∧ al x < 1 ∧ 0 < sampledMean (F:=F) 52500 (vl x) ∧
      sampledMean (F:=F) 52500 (vl x) < 1 ∧ al x ≤ sampledMean (F:=F) 52500 (vl x) := by
    rcases x with x | x
    · exact ⟨by norm_num [al],by norm_num [al],hlcode x x.property⟩
    · rcases x with x | x
      · exact ⟨by norm_num [al],by norm_num [al],hlaffine x (hfmin x x.property)⟩
      · exact ⟨by norm_num [al],by norm_num [al],hlaffine x (hgmin x x.property)⟩
  have hh₀pos : (0:ℝ) < hammingNorm h₀ := by
    exact_mod_cast (Nat.pos_of_ne_zero (fun he => hh₀ (hammingNorm_eq_zero.mp he)))
  have hupper0 := short_word_upper_tail hh₀pos (by exact_mod_cast hh₀weight)
  have hupperv := incidence_upper_tail
  have hU (w : Option W) : 0 < au w ∧ au w < 1 ∧ 0 < sampledMean (F:=F) 52500 (vu w) ∧
      sampledMean (F:=F) 52500 (vu w) < 1 ∧ sampledMean (F:=F) 52500 (vu w) ≤ au w := by
    cases w with
    | none =>
      simp only [au,vu,Option.elim_none,sampledMean_concrete hF hI]
      exact ⟨by norm_num,by norm_num,hupper0.1,by linarith [hupper0.2.1],hupper0.2.1.le⟩
    | some w =>
      simp only [au,vu,Option.elim_some,sampledMean_concrete hF hI,hv,Nat.cast_ofNat]
      exact ⟨by norm_num,by norm_num,hupperv.1,by linarith [hupperv.2.1],hupperv.2.1.le⟩
  have hsumL : (∑ x : L, Real.exp (-(Fintype.card J:ℝ)*bernoulliKL (al x)
      (sampledMean (F:=F) 52500 (vl x)))) ≤ 3*(68853957121+1)*Real.exp (-1000) := by
    rw [← Finset.sum_coe_sort] at hs0 hsf hsg
    simp only [L,Fintype.sum_sum_type,al,vl,Sum.elim_inl,Sum.elim_inr,
      sampledMean_concrete hF hI,hJ,Nat.cast_pow,Nat.cast_ofNat]
    linarith
  have hsumU : (∑ w : Option W, Real.exp (-(Fintype.card J:ℝ)*bernoulliKL (au w)
      (sampledMean (F:=F) 52500 (vu w)))) ≤ (18049720589484545+1)*Real.exp (-1000) := by
    have hpoint (w : Option W) : Real.exp (-(Fintype.card J:ℝ)*bernoulliKL (au w)
        (sampledMean (F:=F) 52500 (vu w))) ≤ Real.exp (-1000) := by
      apply Real.exp_le_exp.mpr
      cases w with
      | none =>
        simp only [au,vu,Option.elim_none,sampledMean_concrete hF hI,hJ,Nat.cast_pow,Nat.cast_ofNat]
        linarith [hupper0.2.2]
      | some w =>
        simp only [au,vu,Option.elim_some,sampledMean_concrete hF hI,hv,hJ,Nat.cast_pow,Nat.cast_ofNat]
        linarith [hupperv.2.2]
    have hh := Finset.sum_le_sum (s:=Finset.univ) (fun w _ => hpoint w)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_option,hW,nsmul_eq_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using hh
  have hfailure : (∑ x : L, Real.exp (-(Fintype.card J:ℝ)*bernoulliKL (al x)
      (sampledMean (F:=F) 52500 (vl x)))) +
      (∑ w : Option W, Real.exp (-(Fintype.card J:ℝ)*bernoulliKL (au w)
      (sampledMean (F:=F) 52500 (vu w)))) < 1 := by
    linarith [coarse_failure_budget]
  obtain ⟨A,hAL,hAU⟩ := exists_linear_refined_amplification vl vu 52500 al au hL hU hfailure
  refine ⟨A,?_,?_,?_,hAU none,fun w => hAU (some w)⟩
  · intro c hc hcn
    exact hAL (Sum.inl ⟨c,by simp [nonzeroCodeWords,hc,hcn]⟩)
  · intro c hc
    apply hAL (Sum.inr (Sum.inl ⟨f-c,?_⟩))
    simp only [affineCodeWords,Finset.mem_filter,Finset.mem_univ,true_and]
    simpa only [sub_sub_cancel_left] using C.neg_mem hc
  · intro c hc
    apply hAL (Sum.inr (Sum.inr ⟨g-c,?_⟩))
    simp only [affineCodeWords,Finset.mem_filter,Finset.mem_univ,true_and]
    simpa only [sub_sub_cancel_left] using C.neg_mem hc

end OneAndAHalfJohnson
