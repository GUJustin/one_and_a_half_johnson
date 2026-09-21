module

public import OneAndAHalfJohnson.Syndrome

/-!
# Normalizing syndrome directions

The normalization step at the end of Lemma 3.2: nonzero first coordinates
allow rescaling incidence words to syndromes `(1, z)` without changing their
weight. Pairwise independent syndromes give distinct coefficients `z`.
-/

@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson

variable {F I : Type*} [Field F] [Fintype I] [DecidableEq F]

/-- Nonzero rescaling leaves Hamming weight unchanged. -/
theorem hammingNorm_smul_nonzero (a : F) (ha : a ≠ 0) (u : I → F) :
    hammingNorm (a • u) = hammingNorm u := by
  apply hammingNorm_smul
  intro i
  exact IsSMulRegular.of_ne_zero ha

omit [Fintype I] [DecidableEq F] in
/-- Normalize a syndrome with nonzero first coordinate. -/
theorem syndrome_normalize (ψ : (I → F) →ₗ[F] (F × F)) (u : I → F)
    (a b : F) (ha : a ≠ 0) (hs : ψ u = (a, b)) :
    ψ (a⁻¹ • u) = (1, b / a) := by
  simp [map_smul, hs, Prod.smul_mk, ha, div_eq_mul_inv, mul_comm]

/-- Distinct slopes of nonvertical syndrome directions give many exceptions. -/
theorem card_exceptional_ge_of_syndrome_slopes [Fintype F]
    {J : Type*} [Fintype J] (D : Submodule F (I → F))
    (ψ : (I → F) →ₗ[F] (F × F)) {f g : I → F} {ρ : ℝ}
    (hf : f ∈ D) (hg : g ∈ D)
    (hsf : ψ f = (1, 0)) (hsg : ψ g = (0, 1))
    (a b : J → F) (ha : ∀ j, a j ≠ 0)
    (hslopes : Function.Injective (fun j => b j / a j))
    (u : J → I → F) (hu : ∀ j, u j ∈ D)
    (hsu : ∀ j, ψ (u j) = (a j, b j))
    (hw : ∀ j, (hammingNorm (u j) : ℝ) ≤ ρ * Fintype.card I) :
    Fintype.card J ≤ (exceptional (D ⊓ LinearMap.ker ψ) f g ρ).card := by
  apply card_exceptional_ge_of_syndromes D ψ hf hg hsf hsg
    (fun j => b j / a j) hslopes (fun j => (a j)⁻¹ • u j)
  · intro j; exact D.smul_mem _ (hu j)
  · intro j; exact syndrome_normalize ψ (u j) (a j) (b j) (ha j) (hsu j)
  · intro j
    rw [hammingNorm_smul_nonzero _ (inv_ne_zero (ha j))]
    exact hw j

omit [DecidableEq F] in
/-- Independent pairs of two-dimensional vectors with nonzero first coordinates
have distinct slopes. -/
theorem slopes_injective_of_pairwise_independent {J : Type*}
    (a b : J → F) (ha : ∀ j, a j ≠ 0)
    (hind : ∀ i j, i ≠ j → LinearIndependent F ![(a i, b i), (a j, b j)]) :
    Function.Injective (fun j => b j / a j) := by
  intro i j hij
  by_contra hne
  have hi := (linearIndependent_fin2.mp (hind i j hne)).2 (a i / a j)
  apply hi
  change (a i / a j) • (a j, b j) = (a i, b i)
  apply Prod.ext
  · simp [div_eq_mul_inv, ha j, mul_assoc]
  · change (a i / a j) * b j = b i
    have hcross := (div_eq_div_iff (ha i) (ha j)).mp hij
    rw [div_mul_eq_mul_div]
    apply (div_eq_iff (ha j)).mpr
    simpa only [mul_comm] using hcross.symm

/-- Pairwise independent incidence syndromes yield the exceptional-set count. -/
theorem card_exceptional_ge_of_independent_syndromes [Fintype F]
    {J : Type*} [Fintype J] (D : Submodule F (I → F))
    (ψ : (I → F) →ₗ[F] (F × F)) {f g : I → F} {ρ : ℝ}
    (hf : f ∈ D) (hg : g ∈ D)
    (hsf : ψ f = (1, 0)) (hsg : ψ g = (0, 1))
    (a b : J → F) (ha : ∀ j, a j ≠ 0)
    (hind : ∀ i j, i ≠ j → LinearIndependent F ![(a i, b i), (a j, b j)])
    (u : J → I → F) (hu : ∀ j, u j ∈ D)
    (hsu : ∀ j, ψ (u j) = (a j, b j))
    (hw : ∀ j, (hammingNorm (u j) : ℝ) ≤ ρ * Fintype.card I) :
    Fintype.card J ≤ (exceptional (D ⊓ LinearMap.ker ψ) f g ρ).card := by
  exact card_exceptional_ge_of_syndrome_slopes D ψ hf hg hsf hsg a b ha
    (slopes_injective_of_pairwise_independent a b ha hind) u hu hsu hw

end OneAndAHalfJohnson
