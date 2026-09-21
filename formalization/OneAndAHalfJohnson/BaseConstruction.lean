module

public import OneAndAHalfJohnson.SyndromeDirections
public import OneAndAHalfJohnson.CodeDistance
public import OneAndAHalfJohnson.KernelWitness
public import OneAndAHalfJohnson.MainTheorems.Shortening

/-!
# Assembly of the small-distance base code

Supporting algebra for Lemma 3.2: small-word exclusion, unused syndrome
slopes, source farness, and exceptional coefficients. Geometric classification
and syndrome construction are supplied by their proved modules.
-/

@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson.BaseConstruction

variable {F I J : Type*} [Field F] [Fintype I] [DecidableEq F]

omit [Fintype I] [DecidableEq F] in
/-- Pairwise independent nonzero images exclude every nonzero vector in any
one- or two-row span from the kernel. -/
theorem pair_span_kernel_exclusion (u : J → I → F)
    (ψ : (I → F) →ₗ[F] (F × F))
    (hn : ∀ j, ψ (u j) ≠ 0)
    (hind : ∀ i j, i ≠ j → LinearIndependent F ![ψ (u i), ψ (u j)])
    (i j : J) (v : I → F) (hv : v ∈ Submodule.span F {u i, u j})
    (hv0 : v ≠ 0) : ψ v ≠ 0 := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hv
  intro h
  simp only [map_add, map_smul] at h
  by_cases hij : i = j
  · subst j
    rw [← add_smul] at h
    have hab : a + b = 0 := (smul_eq_zero.mp h).resolve_right (hn i)
    exact hv0 (by rw [← add_smul, hab, zero_smul])
  · obtain ⟨ha, hb⟩ := (LinearIndependent.pair_iff.mp (hind i j hij)) a b h
    exact hv0 (by simp [ha, hb])

omit [Fintype I] [DecidableEq F] in
/-- Two independent row images make the syndrome map surjective on the ambient code. -/
theorem surjective_restriction_of_pair (D : Submodule F (I → F))
    (ψ : (I → F) →ₗ[F] (F × F)) (u v : I → F) (hu : u ∈ D) (hv : v ∈ D)
    (hind : LinearIndependent F ![ψ u, ψ v]) :
    Function.Surjective (ψ.comp D.subtype) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  have hs := hind.span_eq_top_of_card_eq_finrank' (by simp)
  rw [← hs]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact ⟨⟨u, hu⟩, rfl⟩
  · exact ⟨⟨v, hv⟩, rfl⟩

omit [Field F] in
/-- Fewer row directions than field elements leave an unused affine slope. -/
theorem exists_unused_slope [Fintype F] [Fintype J]
    (z : J → F) (hcard : Fintype.card J < Fintype.card F) :
    ∃ c : F, c ∉ Set.range z := by
  by_contra h
  have hs : Function.Surjective z := by
    intro c
    by_contra hc
    exact h ⟨c, hc⟩
  exact (not_le_of_gt hcard) (Fintype.card_le_of_surjective z hs)

omit [Fintype I] [DecidableEq F] in
/-- A nonvertical row span cannot contain the vertical source syndrome. -/
theorem singleton_syndrome_ne_vertical (ψ : (I → F) →ₗ[F] (F × F))
    (u v : I → F) (hu : (ψ u).1 ≠ 0) (hv : v ∈ Submodule.span F {u}) :
    ψ v ≠ (0, 1) := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
  intro he
  have h1 : a * (ψ u).1 = 0 := by simpa using congrArg Prod.fst he
  have ha := (mul_eq_zero.mp h1).resolve_right hu
  have hs := congrArg Prod.snd he
  simp [ha] at hs

omit [Fintype I] [DecidableEq F] in
/-- An unused affine slope cannot occur in a single row span. -/
theorem singleton_syndrome_ne_affine (ψ : (I → F) →ₗ[F] (F × F))
    (u v : I → F) (c : F) (hu : (ψ u).1 ≠ 0)
    (hc : (ψ u).2 / (ψ u).1 ≠ c) (hv : v ∈ Submodule.span F {u}) :
    ψ v ≠ (1, c) := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
  intro he
  have h1 : a * (ψ u).1 = 1 := by simpa using congrArg Prod.fst he
  have h2 : a * (ψ u).2 = c := by simpa using congrArg Prod.snd he
  apply hc
  apply (div_eq_iff hu).mpr
  calc
    (ψ u).2 = (a * (ψ u).1) * (ψ u).2 := by rw [h1, one_mul]
    _ = (a * (ψ u).2) * (ψ u).1 := by ring
    _ = c * (ψ u).1 := by rw [h2]

/-- A horizontal source at any unused slope and a vertical source produce one
exceptional coefficient for every independent incidence direction. -/
theorem card_exceptional_ge_of_offset_slopes [Fintype F] [Fintype J]
    (D : Submodule F (I → F)) (ψ : (I → F) →ₗ[F] (F × F))
    (u : J → I → F) (hu : ∀ j, u j ∈ D)
    (hfirst : ∀ j, (ψ (u j)).1 ≠ 0)
    (hind : ∀ i j, i ≠ j → LinearIndependent F ![ψ (u i), ψ (u j)])
    (c : F) (f g : I → F) (hf : f ∈ D) (hg : g ∈ D)
    (hsf : ψ f = (1, c)) (hsg : ψ g = (0, 1)) (ρ : ℝ)
    (hw : ∀ j, (hammingNorm (u j) : ℝ) ≤ ρ * Fintype.card I) :
    Fintype.card J ≤ (exceptional (D ⊓ LinearMap.ker ψ) f g ρ).card := by
  classical
  let a : J → F := fun j => (ψ (u j)).1
  let b : J → F := fun j => (ψ (u j)).2
  let z : J → F := fun j => b j / a j - c
  have hi : Function.Injective (fun j => b j / a j) :=
    slopes_injective_of_pairwise_independent a b hfirst (by simpa [a, b] using hind)
  have hz : Function.Injective z := by
    intro i j he
    apply hi
    have hh := congrArg (fun x : F => x + c) he
    simpa [z] using hh
  have hsub : Finset.univ.image z ⊆ exceptional (D ⊓ LinearMap.ker ψ) f g ρ := by
    intro x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    apply (mem_exceptional _ _ _ _ _).mpr
    have hs : ψ ((a j)⁻¹ • u j) = (1, b j / a j) :=
      syndrome_normalize ψ (u j) (a j) (b j) (hfirst j) rfl
    apply close_of_equal_syndrome D ψ (D.add_mem hf (D.smul_mem _ hg))
      (D.smul_mem _ (hu j))
    · rw [map_add, map_smul, hsf, hsg, hs]
      ext <;> simp [z]
    · rw [hammingNorm_smul_nonzero _ (inv_ne_zero (hfirst j))]
      exact hw j
  simpa only [Finset.card_image_of_injective _ hz, Finset.card_univ] using
    Finset.card_le_card hsub

/-- The common-pair shortening theorem controls every small word after scalar
extension. -/
theorem extended_small_word_pair
    (p : ℕ) [Fact p.Prime] (hAD : Targets.AD21LowWeight p)
    (K : Type) [Field K] [Fintype K] [CharP K p]
    (a : ℕ) (hcard : Fintype.card K = p ^ a)
    (hQ : 32 < Fintype.card K) (h49 : Fintype.card K ≠ 49) (h121 : Fintype.card K ≠ 121)
    (m : ℕ) (hm : 4 ≤ m)
    (E : Type) [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
    (v : Geometry.Point K m → E)
    (hv : v ∈ extendCode (K := E) (Geometry.incidenceSpan K (ZMod p) m))
    (hw : hammingNorm v ≤ Targets.lowWeightCutoff (Fintype.card K) m) :
    ∃ W T : Geometry.CodimTwo K m,
      v ∈ Submodule.span E {Geometry.incidenceWord E W, Geometry.incidenceWord E T} := by
  classical
  let S : Finset (Geometry.Point K m) := Finset.univ.filter (fun i => v i ≠ 0)
  have hS : S.card = hammingNorm v := rfl
  obtain ⟨W, T, hWT⟩ := shortening_contained_in_two_incidence_rows
    p hAD K a hcard hQ h49 h121 m hm S (by simpa only [hS] using hw)
  have hsupport : v ∈ supportedCode (S : Set _) := by
    intro i hi
    simpa [S] using hi
  have ht := shortened_extendCode_le_pair (K := E) _ _ _ _ hWT ⟨hv, hsupport⟩
  exact ⟨W, T, by simpa only [Geometry.embed_incidenceWord] using ht⟩

/-- The smaller shortening threshold gives a single incidence row after
extension of scalars. -/
theorem extended_small_word_singleton
    (p : ℕ) [Fact p.Prime] (hAD : Targets.AD21LowWeight p)
    (K : Type) [Field K] [Fintype K] [CharP K p]
    (a : ℕ) (hcard : Fintype.card K = p ^ a)
    (hQ : 32 < Fintype.card K) (h49 : Fintype.card K ≠ 49) (h121 : Fintype.card K ≠ 121)
    (m : ℕ) (hm : 4 ≤ m)
    (E : Type) [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
    (v : Geometry.Point K m → E)
    (hv : v ∈ extendCode (K := E) (Geometry.incidenceSpan K (ZMod p) m))
    (hw : (hammingNorm v : ℝ) ≤ 4 * (Targets.incidenceWeight (Fintype.card K) m : ℝ) / 3) :
    ∃ W : Geometry.CodimTwo K m, v ∈ Submodule.span E {Geometry.incidenceWord E W} := by
  classical
  let S : Finset (Geometry.Point K m) := Finset.univ.filter (fun i => v i ≠ 0)
  have hS : S.card = hammingNorm v := rfl
  obtain ⟨W, hW⟩ := shortening_contained_in_one_incidence_row
    p hAD K a hcard hQ h49 h121 m hm S (by simpa only [hS] using hw)
  have hsupport : v ∈ supportedCode (S : Set _) := by
    intro i hi
    simpa [S] using hi
  have ht := shortened_extendCode_le_singleton (K := E) _ _ _ hW ⟨hv, hsupport⟩
  exact ⟨W, by simpa only [Geometry.embed_incidenceWord] using ht⟩

end OneAndAHalfJohnson.BaseConstruction
