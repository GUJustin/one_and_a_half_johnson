module

public import OneAndAHalfJohnson.Basic

/-!
# The syndrome-to-counterexample argument

This formalizes the concluding algebraic argument of Lemma 3.2 of ePrint
2026/1894. The geometric construction of the ambient code, the syndrome map,
and its low-weight exclusions are explicit hypotheses, not existence claims.
-/

@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson

variable {F I : Type*} [Field F] [Fintype I] [DecidableEq F]

/-- Distance to a translate is the weight of the translating vector. -/
theorem hammingDist_sub_eq_norm (v u : I → F) :
    hammingDist v (v - u) = hammingNorm u := by
  rw [hammingDist_comm, hammingDist_eq_hammingNorm]
  congr 1
  abel

/-- A low-weight word with the same syndrome supplies a nearby codeword. -/
theorem close_of_equal_syndrome (D : Submodule F (I → F))
    (ψ : (I → F) →ₗ[F] (F × F)) {v u : I → F} {ρ : ℝ}
    (hv : v ∈ D) (hu : u ∈ D) (hs : ψ v = ψ u)
    (hw : (hammingNorm u : ℝ) ≤ ρ * Fintype.card I) :
    Close (D ⊓ LinearMap.ker ψ) v ρ := by
  refine ⟨v - u, ⟨D.sub_mem hv hu, ?_⟩, ?_⟩
  · change ψ (v - u) = 0
    simp [map_sub, hs]
  · simpa only [hammingDist_sub_eq_norm] using hw

/-- Normalized incidence syndromes produce exceptional coefficients. -/
theorem close_of_normalized_syndrome (D : Submodule F (I → F))
    (ψ : (I → F) →ₗ[F] (F × F)) {f g u : I → F} {z : F} {ρ : ℝ}
    (hf : f ∈ D) (hg : g ∈ D) (hu : u ∈ D)
    (hsf : ψ f = (1, 0)) (hsg : ψ g = (0, 1))
    (hsu : ψ u = (1, z))
    (hw : (hammingNorm u : ℝ) ≤ ρ * Fintype.card I) :
    Close (D ⊓ LinearMap.ker ψ) (f + z • g) ρ := by
  apply close_of_equal_syndrome D ψ (D.add_mem hf (D.smul_mem z hg)) hu ?_ hw
  simp [map_add, map_smul, hsf, hsg, hsu, Prod.smul_mk]

/-- Injectively indexed normalized syndromes give a cardinality lower bound. -/
theorem card_exceptional_ge_of_syndromes [Fintype F]
    {J : Type*} [Fintype J] (D : Submodule F (I → F))
    (ψ : (I → F) →ₗ[F] (F × F)) {f g : I → F} {ρ : ℝ}
    (hf : f ∈ D) (hg : g ∈ D)
    (hsf : ψ f = (1, 0)) (hsg : ψ g = (0, 1))
    (z : J → F) (hz : Function.Injective z) (u : J → I → F)
    (hu : ∀ j, u j ∈ D) (hsu : ∀ j, ψ (u j) = (1, z j))
    (hw : ∀ j, (hammingNorm (u j) : ℝ) ≤ ρ * Fintype.card I) :
    Fintype.card J ≤ (exceptional (D ⊓ LinearMap.ker ψ) f g ρ).card := by
  classical
  have hsub : Finset.univ.image z ⊆ exceptional (D ⊓ LinearMap.ker ψ) f g ρ := by
    intro a ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
    apply (mem_exceptional _ _ _ _ _).mpr
    exact close_of_normalized_syndrome D ψ hf hg (hu j) hsf hsg (hsu j) (hw j)
  simpa only [Finset.card_image_of_injective _ hz, Finset.card_univ]
    using Finset.card_le_card hsub

/-- Excluding a syndrome among low-weight ambient words proves strict farness. -/
theorem far_of_syndrome_exclusion (D : Submodule F (I → F))
    (ψ : (I → F) →ₗ[F] (F × F)) {v : I → F} {τ : ℝ}
    (hv : v ∈ D)
    (hexclude : ∀ u ∈ D, (hammingNorm u : ℝ) ≤ τ * Fintype.card I →
      ψ u ≠ ψ v) :
    Far (D ⊓ LinearMap.ker ψ) v τ := by
  intro c hc
  by_contra h
  have hw : (hammingNorm (v - c) : ℝ) ≤ τ * Fintype.card I := by
    have heq : hammingDist v c = hammingNorm (v - c) := by
      simpa only [sub_sub_cancel] using hammingDist_sub_eq_norm v (v - c)
    simpa only [heq] using le_of_not_gt h
  apply hexclude (v - c) (D.sub_mem hv hc.1) hw
  have hcψ : ψ c = 0 := hc.2
  simp [map_sub, hcψ]

end OneAndAHalfJohnson
