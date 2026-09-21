module
public import OneAndAHalfJohnson.AmplificationLimits
/-! Fixed amplification parameters, chosen before the growing field exponent. -/
@[expose] public section
noncomputable section
open Filter Topology
namespace OneAndAHalfJohnson

/-- Choose a fixed geometry field size and repetition count with strict margins
at all four weight envelopes. The constants do not depend on the final field
exponent or output block length. -/
theorem exists_amplification_parameters (p : ℕ) (hp : 2 ≤ p)
    {δ ρ η : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hρ : johnson δ < ρ) (hη : 0 < η) :
    ∃ a t : ℕ, ∃ ξ : ℝ, 1 ≤ a ∧ 1 ≤ t ∧ 0 < ξ ∧ 121 < p ^ a ∧
      amplify t (1 / (p ^ a : ℝ) ^ 2) + 3 * ξ < ρ ∧
      gamma δ + 3 * ξ < amplify t ((4 / 3 - 2 / (p ^ a : ℝ) ^ 2) / (p ^ a : ℝ) ^ 2) ∧
      δ + 3 * ξ < amplify t ((3 - 7 / (p ^ a : ℝ)) / (p ^ a : ℝ) ^ 2) ∧
      amplify t (3 / (p ^ a : ℝ) ^ 2) + 3 * ξ < δ + η := by
  obtain ⟨δ', hδδ', hδ'1, hη', hρ', hγ'⟩ := exists_distance_overshoot hδ1 hρ hη
  have hδ'0 : 0 < δ' := lt_trans hδ0 hδδ'
  let L := amplificationScale δ'
  have hL : 0 < L := amplificationScale_pos hδ'0 hδ'1
  obtain ⟨h3, h1, hfour⟩ := amplificationScale_endpoints hδ'1
  change 1 - Real.exp (-L * 3) = δ' at h3
  change 1 - Real.exp (-L * 1) = johnson δ' at h1
  change 1 - Real.exp (-L * (4 / 3)) = gamma δ' at hfour
  have hccont (x : ℝ) : ContinuousAt (fun c : ℝ => 1 - Real.exp (-L * c)) x := by fun_prop
  obtain ⟨c, hc0, hc3, hcδ⟩ := exists_left_positive_of_continuousAt
    (by norm_num : (0 : ℝ) < 3) (hccont 3) (h3.symm ▸ hδδ')
  obtain ⟨d, hd0, hd4, hdγ⟩ := exists_left_positive_of_continuousAt
    (by norm_num : (0 : ℝ) < 4 / 3) (hccont (4 / 3)) (hfour.symm ▸ hγ')
  let Q : ℕ → ℝ := fun a => (p : ℝ) ^ a
  have hQ : Tendsto Q atTop atTop := tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast hp)
  have hQ2 : Tendsto (fun a => Q a ^ 2) atTop atTop := (tendsto_pow_atTop (n := 2) (by decide)).comp hQ
  have hlim (v : ℝ) := (tendsto_amplify_floor_div v L hL.le).comp hQ2
  have he1 : ∀ᶠ a in atTop, amplify ⌊L * Q a ^ 2⌋₊ (1 / Q a ^ 2) < ρ :=
    (hlim 1).eventually (gt_mem_nhds (h1.symm ▸ hρ'))
  have he3 : ∀ᶠ a in atTop, amplify ⌊L * Q a ^ 2⌋₊ (3 / Q a ^ 2) < δ + η :=
    (hlim 3).eventually (gt_mem_nhds (by rw [h3]; linarith))
  have hec : ∀ᶠ a in atTop, δ < amplify ⌊L * Q a ^ 2⌋₊ (c / Q a ^ 2) :=
    (hlim c).eventually (lt_mem_nhds hcδ)
  have hed : ∀ᶠ a in atTop, gamma δ < amplify ⌊L * Q a ^ 2⌋₊ (d / Q a ^ 2) :=
    (hlim d).eventually (lt_mem_nhds hdγ)
  have hclim : Tendsto (fun a => 3 - 7 / Q a) atTop (𝓝 (3 : ℝ)) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop hQ)
  have hdlim : Tendsto (fun a => 4 / 3 - 2 / Q a ^ 2) atTop (𝓝 (4 / 3 : ℝ)) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop hQ2)
  have hec' := hclim.eventually (lt_mem_nhds hc3)
  have hed' := hdlim.eventually (lt_mem_nhds hd4)
  obtain ⟨a, ha, hqa, h1a, h3a, hca, hda, hcqa, hdqa⟩ :=
    ((eventually_ge_atTop 1).and ((hQ.eventually_gt_atTop 121).and
      (he1.and (he3.and (hec.and (hed.and (hec'.and hed'))))))).exists
  have hq0 : 0 < Q a := by linarith
  have hq2 : 0 < Q a ^ 2 := sq_pos_of_pos hq0
  have hq2big : 4 < Q a ^ 2 := by nlinarith
  let t := ⌊L * Q a ^ 2⌋₊
  have hlow : δ < amplify t ((3 - 7 / Q a) / Q a ^ 2) := by
    apply lt_of_lt_of_le hca (amplify_mono t (div_le_div_of_nonneg_right hcqa.le hq2.le) ?_)
    apply (div_le_one hq2).mpr
    have : 0 < 7 / Q a := div_pos (by norm_num) hq0
    linarith
  have hfar : gamma δ < amplify t ((4 / 3 - 2 / Q a ^ 2) / Q a ^ 2) := by
    apply lt_of_lt_of_le hda (amplify_mono t (div_le_div_of_nonneg_right hdqa.le hq2.le) ?_)
    apply (div_le_one hq2).mpr
    have : 0 < 2 / Q a ^ 2 := div_pos (by norm_num) hq2
    linarith
  have ht : 1 ≤ t := by
    by_contra hn
    have ht0 : t = 0 := by omega
    simp [ht0, amplify] at hlow
    linarith
  let gap := min (ρ - amplify t (1 / Q a ^ 2))
    (min (amplify t ((4 / 3 - 2 / Q a ^ 2) / Q a ^ 2) - gamma δ)
      (min (amplify t ((3 - 7 / Q a) / Q a ^ 2) - δ)
        (δ + η - amplify t (3 / Q a ^ 2))))
  have hgap : 0 < gap := by dsimp [gap, t]; positivity
  have hg1 : gap ≤ ρ - amplify t (1 / Q a ^ 2) := min_le_left _ _
  have htail : gap ≤ min (amplify t ((4 / 3 - 2 / Q a ^ 2) / Q a ^ 2) - gamma δ)
      (min (amplify t ((3 - 7 / Q a) / Q a ^ 2) - δ)
        (δ + η - amplify t (3 / Q a ^ 2))) := min_le_right _ _
  have hg2 := htail.trans (min_le_left _ _)
  have htail' := htail.trans (min_le_right _ _)
  have hg3 := htail'.trans (min_le_left _ _)
  have hg4 := htail'.trans (min_le_right _ _)
  refine ⟨a, t, gap / 4, ha, ht, by positivity, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [Q] at hqa
    exact_mod_cast hqa
  · change amplify t (1 / Q a ^ 2) + 3 * (gap / 4) < ρ
    linarith
  · change gamma δ + 3 * (gap / 4) < amplify t ((4 / 3 - 2 / Q a ^ 2) / Q a ^ 2)
    linarith
  · change δ + 3 * (gap / 4) < amplify t ((3 - 7 / Q a) / Q a ^ 2)
    linarith
  · change amplify t (3 / Q a ^ 2) + 3 * (gap / 4) < δ + η
    linarith
end OneAndAHalfJohnson
