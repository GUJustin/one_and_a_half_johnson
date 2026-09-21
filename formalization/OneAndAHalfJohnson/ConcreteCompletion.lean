module

public import OneAndAHalfJohnson.AmplificationAssembly

/-! Exact supercode completion for the concrete parameters of Theorem 4.1.
The initial dimension need only be bounded above by the actual ambient rank. -/
@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson

/-- The concrete code can be completed with the exact rate identity asserted
in the paper, while preserving distance, strict source farness and every
exceptional challenge. -/
theorem exists_concrete_completion
    {F I : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype I] [DecidableEq I]
    (C₀ : Submodule F (I → F)) (f g : I → F) (ρ : ℝ)
    (hF : Fintype.card F = 2^128) (hI : Fintype.card I = 2^36)
    (hne : C₀ ≠ ⊥) (hdim : Module.finrank F C₀ ≤ 3604584374)
    (hlo : 4419/10000 < relativeDistance C₀) (hhi : relativeDistance C₀ < 4511/10000)
    (hf : Far C₀ f (22945/100000)) (hg : Far C₀ g (22945/100000)) :
    ∃ C : Submodule F (I → F), C₀ ≤ C ∧ C ≠ ⊥ ∧
      relativeDistance C = relativeDistance C₀ ∧
      Far C f (22945/100000) ∧ Far C g (22945/100000) ∧
      (exceptional C₀ f g ρ).card ≤ (exceptional C f g ρ).card ∧
      rate C = 1-relativeDistance C-1/128 ∧
      5410875/10000000 < rate C ∧ rate C < 5502875/10000000 := by
  classical
  have hn : 0 < Fintype.card I := by rw [hI]; positivity
  have hnR : (0:ℝ) < Fintype.card I := by exact_mod_cast hn
  have hword : ∃ v ∈ C₀, v ≠ 0 := by
    by_contra hh
    push Not at hh
    apply hne
    exact le_antisymm (fun v hv => by simpa using hh v hv) bot_le
  let b : ℕ := ⌊(22945/100000:ℝ)*Fintype.card I⌋₊
  have hbpos : 0 ≤ (22945/100000:ℝ)*Fintype.card I := by positivity
  have hfabs : ∀ c ∈ C₀, b < hammingDist f c := by
    intro c hc
    exact (Nat.floor_lt hbpos).mpr (hf c hc)
  have hgabs : ∀ c ∈ C₀, b < hammingDist g c := by
    intro c hc
    exact (Nat.floor_lt hbpos).mpr (hg c hc)
  have hbd : b < Code.dist (C₀ : Set (I → F)) := by
    apply (Nat.floor_lt hbpos).mpr
    apply (lt_div_iff₀ hnR).mp
    change (22945/100000:ℝ) < relativeDistance C₀
    linarith
  have hpower : 4*2^Fintype.card I ≤ Fintype.card F^536870913 := by
    rw [hI,hF]
    exact concrete_completion_defect_power
  have hdef : 536870913 ≤ singletonDefect C₀ := by
    have hbalance : (Module.finrank F C₀:ℝ) + Code.dist (C₀ : Set (I → F)) +
        singletonDefect C₀ = (Fintype.card I:ℝ)+1 := by exact_mod_cast singletonDefect_balance C₀
    have hdimR : (Module.finrank F C₀:ℝ) ≤ 3604584374 := by exact_mod_cast hdim
    have hd : (Code.dist (C₀ : Set (I → F)):ℝ) < (4511/10000:ℝ)*Fintype.card I :=
      (div_lt_iff₀ hnR).mp hhi
    rw [hI] at hd hbalance
    norm_num at hd hbalance
    have hh : (536870913:ℝ) ≤ singletonDefect C₀ := by linarith
    exact_mod_cast hh
  obtain ⟨C,hC,hd,hfC,hgC,hdefC⟩ := exists_completion_defect_eq_min
    C₀ f g b 536870913 hword hfabs hgabs hbd hpower
  have hCne : C ≠ ⊥ := by
    intro hh
    apply hne
    exact le_antisymm (by simpa only [hh] using hC) bot_le
  have hdist : relativeDistance C = relativeDistance C₀ := by unfold relativeDistance; rw [hd]
  have hrate : rate C = 1-relativeDistance C-1/128 := by
    rw [rate_eq_one_sub_distance_add_defect C hn,hdefC,min_eq_right hdef,hI]
    norm_num
    ring
  refine ⟨C,hC,hCne,hdist,?_,?_,Finset.card_le_card (exceptional_mono hC f g ρ),hrate,?_,?_⟩
  · exact fun c hc => Nat.lt_of_floor_lt (hfC c hc)
  · exact fun c hc => Nat.lt_of_floor_lt (hgC c hc)
  · rw [hrate,hdist]
    linarith
  · rw [hrate,hdist]
    linarith

end OneAndAHalfJohnson
