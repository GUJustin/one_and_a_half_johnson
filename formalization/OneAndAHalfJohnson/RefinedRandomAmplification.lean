module

public import OneAndAHalfJohnson.RandomAmplification
public import OneAndAHalfJohnson.BernoulliChernoff

/-! Actual linear sampling with simultaneous, word-dependent relative-entropy
tail bounds. Lower and upper families may have different thresholds and means. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace OneAndAHalfJohnson

/-- Strict simultaneous Bernoulli bounds follow from a finite sum of closed-tail
probability bounds below one. -/
theorem exists_bernoulli_family_bounds
    {Ω L U J : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [Fintype L] [Fintype U] [Fintype J] [Nonempty J]
    (XL : L → J → Ω → ℝ) (XU : U → J → Ω → ℝ)
    (aL bL : L → ℝ) (aU bU : U → ℝ)
    (hL : ∀ v, 0 < aL v ∧ aL v < 1 ∧ 0 < bL v ∧ bL v < 1 ∧ aL v ≤ bL v)
    (hU : ∀ v, 0 < aU v ∧ aU v < 1 ∧ 0 < bU v ∧ bU v < 1 ∧ bU v ≤ aU v)
    (hmL : ∀ v j, Measurable (XL v j)) (hmU : ∀ v j, Measurable (XU v j))
    (h01L : ∀ v j, ∀ᵐ ω ∂μ, XL v j ω = 0 ∨ XL v j ω = 1)
    (h01U : ∀ v j, ∀ᵐ ω ∂μ, XU v j ω = 0 ∨ XU v j ω = 1)
    (hbL : ∀ v j, ∫ ω, XL v j ω ∂μ = bL v)
    (hbU : ∀ v j, ∫ ω, XU v j ω ∂μ = bU v)
    (hindL : ∀ v, iIndepFun (XL v) μ) (hindU : ∀ v, iIndepFun (XU v) μ)
    (hfailure : (∑ v, Real.exp (-(Fintype.card J:ℝ)*bernoulliKL (aL v) (bL v))) +
      (∑ v, Real.exp (-(Fintype.card J:ℝ)*bernoulliKL (aU v) (bU v))) < 1) :
    ∃ ω, (∀ v, aL v < (∑ j, XL v j ω)/Fintype.card J) ∧
      (∀ v, (∑ j, XU v j ω)/Fintype.card J < aU v) := by
  classical
  let BL : L → Set Ω := fun v => {ω | (∑ j, XL v j ω) ≤ aL v*Fintype.card J}
  let BU : U → Set Ω := fun v => {ω | aU v*Fintype.card J ≤ ∑ j, XU v j ω}
  have hl : μ.real (⋃ v, BL v) ≤ ∑ v, Real.exp (-(Fintype.card J:ℝ)*bernoulliKL (aL v) (bL v)) := by
    apply (measureReal_iUnion_fintype_le BL).trans
    apply Finset.sum_le_sum
    intro v _
    obtain ⟨ha0,ha1,hb0,hb1,hab⟩ := hL v
    exact bernoulli_sum_lower_tail (XL v) ha0 ha1 hb0 hb1 hab (hmL v) (h01L v) (hbL v) (hindL v)
  have hu : μ.real (⋃ v, BU v) ≤ ∑ v, Real.exp (-(Fintype.card J:ℝ)*bernoulliKL (aU v) (bU v)) := by
    apply (measureReal_iUnion_fintype_le BU).trans
    apply Finset.sum_le_sum
    intro v _
    obtain ⟨ha0,ha1,hb0,hb1,hab⟩ := hU v
    exact bernoulli_sum_upper_tail (XU v) ha0 ha1 hb0 hb1 hab (hmU v) (h01U v) (hbU v) (hindU v)
  have hbad : μ.real ((⋃ v, BL v) ∪ (⋃ v, BU v)) < 1 :=
    ((measureReal_union_le _ _).trans (add_le_add hl hu)).trans_lt hfailure
  have hn : (0:ℝ) < Fintype.card J := by exact_mod_cast Fintype.card_pos
  by_contra hh
  have hwhole : ((⋃ v, BL v) ∪ (⋃ v, BU v)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro ω
    by_contra hω
    apply hh
    refine ⟨ω,?_,?_⟩
    · intro v
      apply (lt_div_iff₀ hn).mpr
      by_contra hv
      exact hω (Or.inl (Set.mem_iUnion.mpr ⟨v,le_of_not_gt hv⟩))
    · intro v
      apply (div_lt_iff₀ hn).mpr
      by_contra hv
      exact hω (Or.inr (Set.mem_iUnion.mpr ⟨v,le_of_not_gt hv⟩))
  simp only [hwhole,measureReal_def,measure_univ,ENNReal.toReal_one,lt_self_iff_false] at hbad

/-- Instantiate all probability hypotheses with independent uniform samples of
an actual finite row space. -/
theorem exists_finite_sample_family_bounds
    {R L U J : Type*} [Fintype R] [Nonempty R] [Fintype L] [Fintype U]
    [Fintype J] [Nonempty J]
    (ZL : L → R → ℝ) (ZU : U → R → ℝ) (aL : L → ℝ) (aU : U → ℝ)
    (h01L : ∀ v r, ZL v r = 0 ∨ ZL v r = 1)
    (h01U : ∀ v r, ZU v r = 0 ∨ ZU v r = 1)
    (hL : ∀ v, 0 < aL v ∧ aL v < 1 ∧ 0 < (∑ r, ZL v r)/Fintype.card R ∧
      (∑ r, ZL v r)/Fintype.card R < 1 ∧ aL v ≤ (∑ r, ZL v r)/Fintype.card R)
    (hU : ∀ v, 0 < aU v ∧ aU v < 1 ∧ 0 < (∑ r, ZU v r)/Fintype.card R ∧
      (∑ r, ZU v r)/Fintype.card R < 1 ∧ (∑ r, ZU v r)/Fintype.card R ≤ aU v)
    (hfailure : (∑ v, Real.exp (-(Fintype.card J:ℝ)*bernoulliKL (aL v)
      ((∑ r, ZL v r)/Fintype.card R))) +
      (∑ v, Real.exp (-(Fintype.card J:ℝ)*bernoulliKL (aU v)
      ((∑ r, ZU v r)/Fintype.card R))) < 1) :
    ∃ ω : J → R, (∀ v, aL v < (∑ j, ZL v (ω j))/Fintype.card J) ∧
      (∀ v, (∑ j, ZU v (ω j))/Fintype.card J < aU v) := by
  classical
  let : MeasurableSpace R := ⊤
  let : MeasurableSingletonClass R := ⟨fun _ => trivial⟩
  let ν : Measure R := (PMF.uniformOfFintype R).toMeasure
  let μ : Measure (J → R) := Measure.pi (fun _ : J => ν)
  have hm (Z : R → ℝ) : Measurable Z := measurable_of_countable _
  have hexpect (Z : R → ℝ) (j : J) : ∫ ω, Z (ω j) ∂μ = (∑ r, Z r)/Fintype.card R := by
    have hp := measurePreserving_eval (fun _ : J => ν) j
    have hi := integral_map_of_stronglyMeasurable (μ := μ) hp.measurable (hm Z).stronglyMeasurable
    rw [hp.map_eq] at hi
    rw [← hi]
    simp only [ν,PMF.integral_eq_sum,PMF.uniformOfFintype_apply,
      ENNReal.toReal_inv,ENNReal.toReal_natCast,smul_eq_mul]
    rw [← Finset.mul_sum]
    exact (div_eq_inv_mul _ _).symm
  apply exists_bernoulli_family_bounds μ (fun v j ω => ZL v (ω j))
    (fun v j ω => ZU v (ω j)) aL (fun v => (∑ r, ZL v r)/Fintype.card R)
    aU (fun v => (∑ r, ZU v r)/Fintype.card R) hL hU
  · exact fun v j => (hm _).comp (measurable_pi_apply j)
  · exact fun v j => (hm _).comp (measurable_pi_apply j)
  · exact fun v j => ae_of_all _ (fun ω => h01L v (ω j))
  · exact fun v j => ae_of_all _ (fun ω => h01U v (ω j))
  · exact fun v j => hexpect _ j
  · exact fun v j => hexpect _ j
  · exact fun v => iIndepFun_pi (fun _ : J => (hm (ZL v)).aemeasurable)
  · exact fun v => iIndepFun_pi (fun _ : J => (hm (ZU v)).aemeasurable)
  · exact hfailure

/-- The exact sampled mean for a source word. -/
def sampledMean {F E I : Type*} [Fintype F] [Zero E] [DecidableEq E] [Fintype I]
    (t : ℕ) (v : I → E) : ℝ :=
  (1-1/(Fintype.card F:ℝ))*amplify t (relativeWeight v)

/-- A genuine alphabet-reducing linear map simultaneously satisfies arbitrary
finite lower and upper families whenever their exact Chernoff tail sum is below
one. All row sampling, independence and mean identification are internal. -/
theorem exists_linear_refined_amplification
    {F E I J L U : Type*} [Field F] [Field E] [Algebra F E]
    [Fintype F] [Fintype E] [DecidableEq F] [DecidableEq E]
    [Fintype I] [Nonempty I] [Fintype J] [Nonempty J] [Fintype L] [Fintype U]
    (vL : L → I → E) (vU : U → I → E) (t : ℕ) (aL : L → ℝ) (aU : U → ℝ)
    (hL : ∀ v, 0 < aL v ∧ aL v < 1 ∧ 0 < sampledMean (F:=F) t (vL v) ∧
      sampledMean (F:=F) t (vL v) < 1 ∧ aL v ≤ sampledMean (F:=F) t (vL v))
    (hU : ∀ v, 0 < aU v ∧ aU v < 1 ∧ 0 < sampledMean (F:=F) t (vU v) ∧
      sampledMean (F:=F) t (vU v) < 1 ∧ sampledMean (F:=F) t (vU v) ≤ aU v)
    (hfailure : (∑ v, Real.exp (-(Fintype.card J:ℝ)*
      bernoulliKL (aL v) (sampledMean (F:=F) t (vL v)))) +
      (∑ v, Real.exp (-(Fintype.card J:ℝ)*
      bernoulliKL (aU v) (sampledMean (F:=F) t (vU v)))) < 1) :
    ∃ A : (I → E) →ₗ[F] (J → F),
      (∀ v, aL v < relativeWeight (A (vL v))) ∧
      (∀ v, relativeWeight (A (vU v)) < aU v) := by
  classical
  let Z : (I → E) → SamplingRow F E I t → ℝ := fun v r =>
    if r.2 (fun k => v (r.1 k)) ≠ 0 then 1 else 0
  have h01 (v : I → E) (r : SamplingRow F E I t) : Z v r = 0 ∨ Z v r = 1 := by
    dsimp [Z]
    split_ifs <;> simp
  have hmean (v : I → E) : (∑ r, Z v r)/Fintype.card (SamplingRow F E I t) =
      sampledMean (F:=F) t v := by
    have he : (∑ r, Z v r) =
        ((Finset.univ.filter (fun r : SamplingRow F E I t =>
          r.2 (fun k => v (r.1 k)) ≠ 0)).card : ℝ) := by
      simp only [Z,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    rw [he]
    exact sampled_row_success_fraction t v
  obtain ⟨ω,hωL,hωU⟩ := exists_finite_sample_family_bounds (J:=J)
    (fun v => Z (vL v)) (fun v => Z (vU v)) aL aU
    (fun v => h01 (vL v)) (fun v => h01 (vU v))
    (by simpa only [hmean] using hL) (by simpa only [hmean] using hU)
    (by simpa only [hmean] using hfailure)
  have he (v : I → E) : (∑ j, Z v (ω j))/Fintype.card J =
      relativeWeight (sampledLinearMap ω v) := by
    change (∑ j, if (ω j).2 (fun k => v ((ω j).1 k)) ≠ 0 then (1:ℝ) else 0)/
        Fintype.card J =
      ((Finset.univ.filter (fun j => (ω j).2 (fun k => v ((ω j).1 k)) ≠ 0)).card:ℝ)/
        Fintype.card J
    simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  exact ⟨sampledLinearMap ω, by simpa only [he] using hωL, by simpa only [he] using hωU⟩

end OneAndAHalfJohnson
