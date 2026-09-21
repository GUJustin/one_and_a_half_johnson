module

public import OneAndAHalfJohnson.AsymptoticConstruction
public import OneAndAHalfJohnson.AmplificationParameters
public import OneAndAHalfJohnson.AsymptoticSizing
public import OneAndAHalfJohnson.Targets.Conditional

/-! # Theorems 1.1 and 3.1, conditional only on AD21
All constants are fixed before the field exponent, block length and field model.
-/
@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson.MainTheorems
open Targets

/-- Complete fixed-characteristic asymptotic conclusion of Theorems 1.1 and 3.1
(pp. 3 and 12–15). -/
theorem asymptoticConclusion_of_AD21 (p : ℕ) [Fact p.Prime]
    (hAD : AD21LowWeight p) (δ ρ η : ℝ)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hρ : johnson δ < ρ) (hη : 0 < η) :
    AsymptoticConclusion p δ ρ η := by
  obtain ⟨a,t,ξ,ha,_,hξ,hQ,hclose,hfar,hlower,hupper⟩ :=
    exists_amplification_parameters p (Fact.out : p.Prime).two_le hδ hδ1 hρ hη
  let d := 2*(p^a-1)
  let H := amplificationSizeConstant p (2*a) (2^d) ξ
  have hH : 0 < H := amplificationSizeConstant_pos p (2*a) (2^d) ξ
    (Fact.out : p.Prime).two_le (by positivity) hξ
  obtain ⟨A,hA,s₀,hs₀,hsize⟩ := exists_final_size_threshold p a d
    (Fact.out : p.Prime).two_le ha ξ H hξ hH
  have hpR : (0:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  refine ⟨A,1/(8*(p^a:ℝ)^4),6,hA,by positivity,by norm_num,d+1,s₀,by omega,hs₀,?_⟩
  intro s hs N hN _ F _ _ _ hF
  obtain ⟨hlarge,hNs,hN',hsmall⟩ := hsize s hs N hN
  have hspos : 0 < s := by omega
  have hγ : 0 ≤ gamma δ := by
    have hh := Real.rpow_le_one (show 0 ≤ 1-δ by linarith)
      (show 1-δ ≤ 1 by linarith) (show (0:ℝ) ≤ 4/9 by norm_num)
    unfold gamma
    linarith
  exact asymptotic_code_at_size p hAD a t ha ξ δ ρ η hξ hδ hδ1 hγ hQ
    hclose hfar hlower hupper s N hspos hlarge hNs hsmall hN' F hF

/-- Full all-characteristic main result (Theorems 1.1 and 3.1). -/
theorem mainTheorem_of_AD21
    (hAD : ∀ (p : ℕ) [Fact p.Prime], AD21LowWeight p) : MainTheorem := by
  intro p hp δ ρ η hδ hδ1 hρ _ hη
  let : Fact p.Prime := ⟨hp⟩
  exact asymptoticConclusion_of_AD21 p (hAD p) δ ρ η hδ hδ1 hρ hη

/-- The characteristic-specific conditional main contract, with exactly AD21
as its external premise. -/
theorem conditionalMainTheorem : ConditionalMainTheorem := by
  intro p _ hAD δ ρ η hδ hδ1 hρ _ hη
  exact asymptoticConclusion_of_AD21 p hAD δ ρ η hδ hδ1 hρ hη

/-- Corollary 1.2 (p. 3), with the same sole external classification premise. -/
theorem uniqueDecodingCounterexamples_of_AD21
    (hAD : ∀ (p : ℕ) [Fact p.Prime], AD21LowWeight p) : UniqueDecodingCounterexamples :=
  uniqueDecoding_of_main (mainTheorem_of_AD21 hAD)

/-- Stronger actual-code formulation: the exceptional radius is strictly below
half the constructed code's own relative distance, not merely half the target
limit. The tolerance is reduced before any growing size parameters are chosen. -/
theorem actual_unique_radius_of_AD21 (p : ℕ) [Fact p.Prime]
    (hAD : AD21LowWeight p) (δ ρ η : ℝ)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hρ : johnson δ < ρ)
    (hhalf : ρ < δ/2) (hη : 0 < η) :
    ∃ A c M : ℝ, 0 < A ∧ 0 < c ∧ 0 < M ∧
      ∃ D s₀ : ℕ, 1 ≤ D ∧ 1 ≤ s₀ ∧
        ∀ s : ℕ, s₀ ≤ s → ∀ N : ℕ,
          A * (s:ℝ)^D ≤ (N:ℝ) → N < p^s →
          ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F],
            Fintype.card F = p^s →
            ∃ (C : Submodule F (Fin N → F)) (f g : Fin N → F),
              C ≠ ⊥ ∧ |relativeDistance C-δ| < η ∧
              |rate C-(1-relativeDistance C)| ≤ M/(s:ℝ) ∧
              Far C f (gamma δ) ∧ Far C g (gamma δ) ∧
              c*Fintype.card F ≤ (exceptional C f g ρ).card ∧
              ρ < relativeDistance C/2 := by
  let η' := min η ((δ-2*ρ)/2)
  have hη' : 0 < η' := lt_min hη (by linarith)
  obtain ⟨A,c,M,hA,hc,hM,D,s₀,hD,hs₀,hcodes⟩ :=
    asymptoticConclusion_of_AD21 p hAD δ ρ η' hδ hδ1 hρ hη'
  refine ⟨A,c,M,hA,hc,hM,D,s₀,hD,hs₀,?_⟩
  intro s hs N hN hNq F _ _ _ hF
  obtain ⟨C,f,g,hC,hd,hr,hf,hg,hcount⟩ := hcodes s hs N hN hNq F hF
  refine ⟨C,f,g,hC,hd.trans_le (min_le_left _ _),hr,hf,hg,hcount,?_⟩
  have hh := (abs_lt.mp hd).1
  have hh' : η' ≤ (δ-2*ρ)/2 := min_le_right _ _
  linarith

end OneAndAHalfJohnson.MainTheorems
