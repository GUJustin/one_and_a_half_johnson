module

public import OneAndAHalfJohnson.Amplification
public import OneAndAHalfJohnson.CodeDistance
public import OneAndAHalfJohnson.CompletionParameters

/-!
# Assembling genuine code parameters after uniform amplification

Minimum-distance estimates use actual minimum-weight witnesses in nonzero
codes. Positivity of the amplified lower bound proves injectivity before
passing to image minimum distance. All code and word hypotheses are ordinary
inputs to this reusable deterministic step, not external paper assumptions.
-/

@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson

/-- A nonzero linear code has an actual word attaining its minimum weight. -/
theorem exists_minimum_weight_word
    {F I : Type*} [Field F] [DecidableEq F] [Fintype I]
    (C : Submodule F (I → F)) (hne : ∃ c ∈ C, c ≠ 0) :
    ∃ c ∈ C, c ≠ 0 ∧ hammingNorm c = Code.dist (C : Set (I → F)) := by
  have hs : {d : ℕ | ∃ c ∈ C, c ≠ 0 ∧ hammingNorm c ≤ d}.Nonempty := by
    obtain ⟨c,hc,hn⟩ := hne
    exact ⟨hammingNorm c,c,hc,hn,le_rfl⟩
  have hw := csInf_mem hs
  rw [← LinearCode.disFromHammingNorm, ← LinearCode.dist_eq_dist_from_HammingNorm] at hw
  obtain ⟨c,hc,hn,hupper⟩ := hw
  have hlower := code_distance_le_of_nonzero_word C (hammingNorm c) ⟨c,hc,hn,le_rfl⟩
  exact ⟨c,hc,hn,Nat.le_antisymm hupper hlower⟩

/-- Every nonzero codeword has relative weight at least the actual relative
minimum distance. -/
theorem relativeDistance_le_relativeWeight
    {F I : Type*} [Field F] [DecidableEq F] [Fintype I]
    (C : Submodule F (I → F)) {v : I → F} (hv : v ∈ C) (hn : v ≠ 0) :
    relativeDistance C ≤ relativeWeight v := by
  have h := code_distance_le_of_nonzero_word C (hammingNorm v) ⟨v,hv,hn,le_rfl⟩
  unfold relativeDistance relativeWeight
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast h

/-- Uniform ideal-weight approximation controls actual image minimum distance.
The strict positive margin also guarantees that the image code is nonzero. -/
theorem image_distance_of_uniform_amplification
    {F E I J : Type*} [Field F] [Field E] [Algebra F E]
    [DecidableEq F] [DecidableEq E] [Fintype I] [Fintype J]
    (C D : Submodule E (I → E)) (hCD : C ≤ D)
    (A : (I → E) →ₗ[F] (J → F)) (t : ℕ) (ε : ℝ)
    (hne : ∃ c ∈ C, c ≠ 0)
    (happrox : ∀ v ∈ D, |relativeWeight (A v) - amplify t (relativeWeight v)| ≤ ε)
    (hpositive : ε < amplify t (relativeDistance C)) :
    ((C.restrictScalars F).map A) ≠ ⊥ ∧
      |relativeDistance ((C.restrictScalars F).map A) - amplify t (relativeDistance C)| ≤ ε := by
  let C' := (C.restrictScalars F).map A
  have hinj : Set.InjOn A C := injective_on_code_of_uniform_amplification C D hCD A t
    (relativeDistance C) ε (fun v hv hn => relativeDistance_le_relativeWeight C hv hn)
    happrox hpositive
  have hAnz (c : I → E) (hc : c ∈ C) (hn : c ≠ 0) : A c ≠ 0 := by
    intro hz
    apply hn
    exact hinj hc C.zero_mem (by simpa only [map_zero] using hz)
  have hne' : ∃ y ∈ C', y ≠ 0 := by
    obtain ⟨c,hc,hn⟩ := hne
    exact ⟨A c, ⟨c,hc,rfl⟩, hAnz c hc hn⟩
  have hC' : C' ≠ ⊥ := by
    intro h
    obtain ⟨y,hy,hn⟩ := hne'
    exact hn (by simpa only [h, Submodule.mem_bot] using hy)
  refine ⟨hC', abs_le.mpr ⟨?_, ?_⟩⟩
  · obtain ⟨y,hy,hyn,hywt⟩ := exists_minimum_weight_word C' hne'
    obtain ⟨c,hc,hcy⟩ := hy
    have hcn : c ≠ 0 := by intro hh; subst c; exact hyn (hcy ▸ map_zero A)
    have hlo := (abs_le.mp (happrox c (hCD hc))).1
    have hmono := amplify_mono t (relativeDistance_le_relativeWeight C hc hcn)
      (relativeWeight_le_one c)
    have hrel : relativeWeight (A c) = relativeDistance C' := by
      unfold relativeWeight relativeDistance
      rw [hcy, hywt]
    rw [hrel] at hlo
    linarith
  · obtain ⟨c,hc,hcn,hcwt⟩ := exists_minimum_weight_word C hne
    have hrel : relativeWeight c = relativeDistance C := by
      unfold relativeWeight relativeDistance
      rw [hcwt]
    have hupp := (abs_le.mp (happrox c (hCD hc))).2
    rw [hrel] at hupp
    have him := relativeDistance_le_relativeWeight C' (v := A c) ⟨c,hc,rfl⟩ (hAnz c hc hcn)
    linarith

/-- Lower and upper bounds on the source code's actual relative distance
transfer through the ideal transform with additive error. -/
theorem image_distance_bounds_of_uniform_amplification
    {F E I J : Type*} [Field F] [Field E] [Algebra F E]
    [DecidableEq F] [DecidableEq E] [Fintype I] [Fintype J]
    (C D : Submodule E (I → E)) (hCD : C ≤ D)
    (A : (I → E) →ₗ[F] (J → F)) (t : ℕ) (ε α β : ℝ)
    (hne : ∃ c ∈ C, c ≠ 0)
    (hlo : α ≤ relativeDistance C) (hhi : relativeDistance C ≤ β) (hβ : β ≤ 1)
    (happrox : ∀ v ∈ D, |relativeWeight (A v) - amplify t (relativeWeight v)| ≤ ε)
    (hpositive : ε < amplify t α) :
    let C' := (C.restrictScalars F).map A
    C' ≠ ⊥ ∧ amplify t α - ε ≤ relativeDistance C' ∧
      relativeDistance C' ≤ amplify t β + ε := by
  have hd1 : relativeDistance C ≤ 1 := by
    obtain ⟨c,hc,hn⟩ := hne
    exact (relativeDistance_le_relativeWeight C hc hn).trans (relativeWeight_le_one c)
  have hmlo := amplify_mono t hlo hd1
  have hmhi := amplify_mono t hhi hβ
  obtain ⟨hn,hd⟩ := image_distance_of_uniform_amplification C D hCD A t ε hne happrox
    (hpositive.trans_le hmlo)
  have hh := abs_le.mp hd
  exact ⟨hn, by linarith [hh.1], by linarith [hh.2]⟩

/-- Closeness supplies a genuine relative-weight difference witness at positive
block length. -/
theorem Close.exists_relativeWeight_difference
    {E I : Type*} [Field E] [DecidableEq E] [Fintype I]
    {C : Submodule E (I → E)} {v : I → E} {ρ : ℝ}
    (h : Close C v ρ) (hI : 0 < Fintype.card I) :
    ∃ c ∈ C, relativeWeight (v - c) ≤ ρ := by
  obtain ⟨c,hc,hd⟩ := h
  refine ⟨c,hc, ?_⟩
  have hn : (0 : ℝ) < Fintype.card I := by exact_mod_cast hI
  have he : hammingDist v c = hammingNorm (v - c) := by
    simpa only [sub_sub_cancel] using hammingDist_sub_eq_norm v (v - c)
  rw [relativeWeight, div_le_iff₀ hn]
  simpa only [he] using hd

/-- Full deterministic image assembly: one fixed map and one fixed pair of
words retain genuine code-distance bounds, strict farness, and a fixed finite
set of distinct exceptional challenges. -/
theorem amplified_image_parameters
    {F E I J : Type*} [Field F] [Field E] [Algebra F E]
    [Fintype F] [DecidableEq F] [DecidableEq E] [Fintype I] [Fintype J]
    (C D : Submodule E (I → E)) (hCD : C ≤ D)
    (A : (I → E) →ₗ[F] (J → F)) (f g : I → E) (hfD : f ∈ D) (hgD : g ∈ D)
    (t : ℕ) (ε α ρ₀ γ ρ : ℝ) (T : Finset F)
    (hI : 0 < Fintype.card I) (hJ : 0 < Fintype.card J)
    (hne : ∃ c ∈ C, c ≠ 0)
    (happrox : ∀ v ∈ D, |relativeWeight (A v) - amplify t (relativeWeight v)| ≤ ε)
    (hpositive : ε < amplify t (relativeDistance C))
    (hf : Far C f α) (hg : Far C g α)
    (hfar_margin : γ + ε < amplify t α)
    (hρ₀ : ρ₀ ≤ 1) (hclose_margin : amplify t ρ₀ + ε ≤ ρ)
    (hT : ∀ z ∈ T, Close C (f + z • g) ρ₀) :
    let C' := (C.restrictScalars F).map A
    C' ≠ ⊥ ∧
      amplify t (relativeDistance C) - ε ≤ relativeDistance C' ∧
      relativeDistance C' ≤ amplify t (relativeDistance C) + ε ∧
      Far C' (A f) γ ∧ Far C' (A g) γ ∧
      T.card ≤ (exceptional C' (A f) (A g) ρ).card := by
  obtain ⟨hne',hd⟩ := image_distance_of_uniform_amplification C D hCD A t ε hne happrox hpositive
  have hd' := abs_le.mp hd
  refine ⟨hne', by linarith [hd'.1], by linarith [hd'.2], ?_, ?_, ?_⟩
  · exact far_image_of_uniform_amplification C D hCD A f hfD t α ε γ hI hJ hf happrox hfar_margin
  · exact far_image_of_uniform_amplification C D hCD A g hgD t α ε γ hI hJ hg happrox hfar_margin
  · apply exceptional_count_image_of_uniform_amplification C D hCD A f g hfD hgD T
      t ρ₀ ε ρ hρ₀ hJ _ happrox hclose_margin
    exact fun z hz => (hT z hz).exists_relativeWeight_difference hI

/-- Convert a positive relative-distance margin into near-MDS completion,
using the exact floor of `γN`. Farness and all exceptional coefficients survive;
there is no rounding loss in the defining-word threshold. -/
theorem exists_relative_nearMDS_completion
    {F I : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype I] [DecidableEq I]
    (C₀ : Submodule F (I → F)) (f g : I → F) (γ ρ : ℝ) (p s : ℕ)
    (hp : 2 ≤ p) (hs : 0 < s) (hcard : Fintype.card F = p ^ s)
    (hNs : s ≤ Fintype.card I) (hne : ∃ c ∈ C₀, c ≠ 0)
    (hγ : 0 ≤ γ) (hdistance : γ < relativeDistance C₀)
    (hf : Far C₀ f γ) (hg : Far C₀ g γ) :
    ∃ C : Submodule F (I → F), C₀ ≤ C ∧ C ≠ ⊥ ∧
      relativeDistance C = relativeDistance C₀ ∧
      Far C f γ ∧ Far C g γ ∧
      (exceptional C₀ f g ρ).card ≤ (exceptional C f g ρ).card ∧
      |rate C - (1 - relativeDistance C)| ≤ 6 / (s : ℝ) := by
  let b := ⌊γ * Fintype.card I⌋₊
  have hn : (0 : ℝ) < Fintype.card I := by exact_mod_cast (lt_of_lt_of_le hs hNs)
  have hγN : 0 ≤ γ * (Fintype.card I : ℝ) := mul_nonneg hγ hn.le
  have hfabs : ∀ c ∈ C₀, b < hammingDist f c := by
    intro c hc
    exact (Nat.floor_lt hγN).mpr (hf c hc)
  have hgabs : ∀ c ∈ C₀, b < hammingDist g c := by
    intro c hc
    exact (Nat.floor_lt hγN).mpr (hg c hc)
  have hbd : b < Code.dist (C₀ : Set (I → F)) := by
    apply (Nat.floor_lt hγN).mpr
    exact (lt_div_iff₀ hn).mp hdistance
  obtain ⟨C,hC,hd,hfC,hgC,hrate⟩ :=
    exists_completion_rate_error_le_six_div C₀ f g b p s hp hs hcard hNs hne hfabs hgabs hbd
  have hCne : C ≠ ⊥ := by
    intro h
    obtain ⟨c,hc,hcn⟩ := hne
    exact hcn (by simpa only [h, Submodule.mem_bot] using hC hc)
  refine ⟨C,hC,hCne, ?_, ?_, ?_, ?_, hrate⟩
  · unfold relativeDistance
    rw [hd]
  · intro c hc
    exact Nat.lt_of_floor_lt (hfC c hc)
  · intro c hc
    exact Nat.lt_of_floor_lt (hgC c hc)
  · exact Finset.card_le_card (exceptional_mono hC f g ρ)

end OneAndAHalfJohnson
