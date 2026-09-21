module

public import OneAndAHalfJohnson.ConcreteCompletion
public import OneAndAHalfJohnson.ConcreteBase

/-! Deterministic assembly of the concrete sampled code and its completion. -/
@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson

/-- Actual per-word sampling inequalities imply all concrete code parameters.
This lemma is an intermediate deterministic deduction; the sampler supplying
its inequalities is constructed separately by the finite-family KL bound. -/
theorem concrete_code_of_sampled_bounds
    {F I J W : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype I] [Fintype J] [DecidableEq J] [Fintype W]
    (C : Submodule F (I → F)) (f g h₀ : I → F) (z : W → F) (v : W → I → F)
    (A : (I → F) →ₗ[F] (J → F))
    (hF : Fintype.card F = 2^128) (hJ : Fintype.card J = 2^36)
    (hdim : Module.finrank F C ≤ 3604584374)
    (hh₀ : h₀ ∈ C) (hh₀ne : h₀ ≠ 0)
    (hz : Function.Injective z) (hv : ∀ w, f+z w • g-v w ∈ C)
    (hlower : ∀ c ∈ C, c ≠ 0 → 4419/10000 < relativeWeight (A c))
    (hf : ∀ c ∈ C, 22945/100000 < relativeWeight (A (f-c)))
    (hg : ∀ c ∈ C, 22945/100000 < relativeWeight (A (g-c)))
    (hupper : relativeWeight (A h₀) < 4511/10000)
    (hvupper : ∀ w, relativeWeight (A (v w)) < 1816/10000) :
    ∃ C₁ : Submodule F (J → F), C₁ ≠ ⊥ ∧
      4419/10000 < relativeDistance C₁ ∧ relativeDistance C₁ < 4511/10000 ∧
      5410875/10000000 < rate C₁ ∧ rate C₁ < 5502875/10000000 ∧
      Far C₁ (A f) (22945/100000) ∧ Far C₁ (A g) (22945/100000) ∧
      (1816/10000:ℝ) < relativeDistance C₁/2 ∧
      Fintype.card W ≤ (exceptional C₁ (A f) (A g) (1816/10000)).card := by
  classical
  let C₀ := C.map A
  have hJn : (0:ℝ) < Fintype.card J := by rw [hJ]; positivity
  have hAnonzero {c : I → F} (hc : c ∈ C) (hcn : c ≠ 0) : A c ≠ 0 := by
    intro he
    have hh := hlower c hc hcn
    rw [he] at hh
    norm_num [relativeWeight] at hh
  have hword : ∃ w ∈ C₀, w ≠ 0 := ⟨A h₀,Submodule.mem_map.mpr ⟨h₀,hh₀,rfl⟩,hAnonzero hh₀ hh₀ne⟩
  have hC₀ : C₀ ≠ ⊥ := by
    intro he
    obtain ⟨w,hw,hwn⟩ := hword
    exact hwn (by simpa only [he,Submodule.mem_bot] using hw)
  have hd₀lo : 4419/10000 < relativeDistance C₀ := by
    obtain ⟨w,hw,hwn,hweight⟩ := exists_minimum_weight_word C₀ hword
    obtain ⟨c,hc,rfl⟩ := hw
    have hcne : c ≠ 0 := by intro he; apply hwn; simp [he]
    have hh := hlower c hc hcne
    simpa only [relativeWeight,hweight,relativeDistance] using hh
  have hd₀hi : relativeDistance C₀ < 4511/10000 :=
    (relativeDistance_le_relativeWeight C₀ (Submodule.mem_map.mpr ⟨h₀,hh₀,rfl⟩)
      (hAnonzero hh₀ hh₀ne)).trans_lt hupper
  have far_image (x : I → F)
      (hx : ∀ c ∈ C, 22945/100000 < relativeWeight (A (x-c))) :
      Far C₀ (A x) (22945/100000) := by
    intro y hy
    obtain ⟨c,hc,rfl⟩ := hy
    have hh := (lt_div_iff₀ hJn).mp (hx c hc)
    have he : hammingDist (A x) (A c) = hammingNorm (A (x-c)) := by
      rw [map_sub]
      simpa only [sub_sub_cancel] using hammingDist_sub_eq_norm (A x) (A x-A c)
    simpa only [he] using hh
  have hcount₀ : Fintype.card W ≤ (exceptional C₀ (A f) (A g) (1816/10000)).card := by
    have hsub : Finset.univ.image z ⊆ exceptional C₀ (A f) (A g) (1816/10000) := by
      intro u hu
      obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hu
      apply (mem_exceptional C₀ (A f) (A g) _ _).mpr
      refine ⟨A (f+z w • g-v w),Submodule.mem_map.mpr ⟨_,hv w,rfl⟩,?_⟩
      have he : hammingDist (A f+z w • A g) (A (f+z w • g-v w)) = hammingNorm (A (v w)) := by
        rw [map_sub,map_add,map_smul]
        exact hammingDist_sub_eq_norm _ _
      rw [he]
      exact ((div_lt_iff₀ hJn).mp (hvupper w)).le
    have hcard : (Finset.univ.image z).card = Fintype.card W := by
      rw [Finset.card_image_of_injective _ hz,Finset.card_univ]
    rw [← hcard]
    exact Finset.card_le_card hsub
  have hdim₀ : Module.finrank F C₀ ≤ 3604584374 := (Submodule.finrank_map_le A C).trans hdim
  obtain ⟨C₁,_,hC₁,hd,hf₁,hg₁,hcount,_,hrlo,hrhi⟩ := exists_concrete_completion
    C₀ (A f) (A g) (1816/10000) hF hJ hC₀ hdim₀ hd₀lo hd₀hi (far_image f hf) (far_image g hg)
  refine ⟨C₁,hC₁,by rwa [hd],by rwa [hd],hrlo,hrhi,hf₁,hg₁,?_,hcount₀.trans hcount⟩
  rw [hd]
  linarith

/-- The concluding comparisons on p. 20 refer to the actual code distance:
the exceptional radius beats Johnson, is more than .03935 below unique
decoding, and has more than 2^18 times the block length many challenges. -/
theorem concrete_code_consequences
    {F J : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype J]
    (C : Submodule F (J → F)) (f g : J → F)
    (hJ : Fintype.card J = 2^36)
    (hlo : 4419/10000 < relativeDistance C) (hhi : relativeDistance C < 4511/10000)
    (hcount : 18049720589484545 ≤ (exceptional C f g (1816/10000)).card) :
    johnson (relativeDistance C) < 1816/10000 ∧
      3935/100000 < relativeDistance C/2-1816/10000 ∧
      2^18*Fintype.card J < (exceptional C f g (1816/10000)).card := by
  refine ⟨(johnson_mono hhi.le (by norm_num)).trans_lt concrete_johnson_upper,?_,?_⟩
  · linarith
  · rw [hJ]
    exact lt_of_lt_of_le (by norm_num) hcount

end OneAndAHalfJohnson
