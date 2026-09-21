module

public import OneAndAHalfJohnson.GeometryTriple
public import OneAndAHalfJohnson.GeometryIndependence
public import OneAndAHalfJohnson.CodeDistance
public import OneAndAHalfJohnson.ScalarExtension

/-!
# Small nonzero syndrome-kernel witnesses

Three independent incidence rows have a nontrivial dependence after mapping
to a two-dimensional syndrome space. The dependence remains nonzero in the
ambient code and is supported on the explicitly counted three-row union.
-/

@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson
open scoped Classical

/-- Three independent supported rows produce a nonzero word in every
 two-coordinate syndrome kernel, with no larger support. -/
theorem exists_kernel_word_of_three_independent
    {E I : Type*} [Field E] [Fintype I] [DecidableEq E]
    (D : Submodule E (I → E)) (ψ : (I → E) →ₗ[E] (E × E))
    (u : Fin 3 → I → E) (hli : LinearIndependent E u) (hu : ∀ j, u j ∈ D)
    (S : Finset I) (hsupp : ∀ j i, i ∉ S → u j i = 0) :
    ∃ v ∈ D ⊓ LinearMap.ker ψ, v ≠ 0 ∧ hammingNorm v ≤ S.card := by
  classical
  let L := ψ.comp (Finsupp.linearCombination E u)
  have hker : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
    simp only [Module.finrank_prod, Module.finrank_self, Module.finrank_finsupp_self,
      Fintype.card_fin]
    omega)
  obtain ⟨c,hc,hcne⟩ := (LinearMap.ker L).ne_bot_iff.mp hker
  refine ⟨Finsupp.linearCombination E u c, ⟨?_,hc⟩, ?_, ?_⟩
  · rw [Finsupp.linearCombination_apply]
    exact D.sum_mem (fun j hj => D.smul_mem _ (hu j))
  · intro heq
    apply hcne
    apply (linearIndependent_iff_injective_finsuppLinearCombination.mp hli)
    simpa only [map_zero] using heq
  · apply Finset.card_le_card
    intro i hi
    by_contra hiS
    have hi' : Finsupp.linearCombination E u c i ≠ 0 := (Finset.mem_filter.mp hi).2
    apply hi'
    simp [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply, hsupp _ _ hiS]

namespace Geometry

/-- The concrete three-row geometry supplies a nonzero kernel word with the
paper's explicit support upper bound, for every two-coordinate syndrome map. -/
theorem exists_small_incidence_kernel_word
    {K E : Type*} [Field K] [Finite K] [Field E] [DecidableEq E]
    {m : ℕ} (hm : 4 ≤ m) (hQ : 32 < Nat.card K)
    (D : Submodule E (Point K m → E))
    (hD : ∀ i : Fin 3, incidenceWord E (tripleSpace K hm i) ∈ D)
    (ψ : (Point K m → E) →ₗ[E] (E × E)) :
    ∃ v ∈ D ⊓ LinearMap.ker ψ, v ≠ 0 ∧ hammingNorm v ≤
      3 * Nat.card K ^ (m - 3) + (Nat.card K ^ (m - 4) - 1) / (Nat.card K - 1) := by
  classical
  let S := triplePoints K hm 0 ∪ triplePoints K hm 1 ∪ triplePoints K hm 2
  obtain ⟨v,hv,hn,hw⟩ := exists_kernel_word_of_three_independent D ψ
    (fun i => incidenceWord E (tripleSpace K hm i))
    (incidence_rows_independent_of_card_le_eight hQ hm (tripleSpace K hm)
      (tripleSpace_injective K hm) (by decide)) hD S (by
        intro j P hP
        have hnot : ¬ Incident (tripleSpace K hm j).val P := by
          intro h
          apply hP
          have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
          rcases hj with rfl | rfl | rfl <;> simp [S, triplePoints, h]
        simp [incidenceWord, hnot])
  refine ⟨v,hv,hn,?_⟩
  simpa only [S, triplePoints_union_card K hm hQ] using hw

/-- Nontriviality and the explicit upper distance bound of the incidence
syndrome kernel follow without any hypothesis on the syndrome map. -/
theorem incidence_kernel_distance_le
    {K E : Type*} [Field K] [Finite K] [Field E] [DecidableEq E]
    {m : ℕ} (hm : 4 ≤ m) (hQ : 32 < Nat.card K)
    (ψ : (Point K m → E) →ₗ[E] (E × E)) :
    Code.dist (incidenceSpan K E m ⊓ LinearMap.ker ψ : Set (Point K m → E)) ≤
      3 * Nat.card K ^ (m - 3) + (Nat.card K ^ (m - 4) - 1) / (Nat.card K - 1) := by
  exact code_distance_le_of_nonzero_word _ _
    (exists_small_incidence_kernel_word hm hQ (incidenceSpan K E m)
      (fun i => incidenceWord_mem_span _) ψ)

/-- Actual nonzero kernel witness and exact support budget for `Q=512,m=5`. -/
theorem exists_incidence_kernel_word_512_five
    {K E : Type*} [Field K] [Finite K] [Field E] [DecidableEq E]
    (hK : Nat.card K = 512) (ψ : (Point K 5 → E) →ₗ[E] (E × E)) :
    ∃ v ∈ incidenceSpan K E 5 ⊓ LinearMap.ker ψ, v ≠ 0 ∧ hammingNorm v ≤ 786433 := by
  obtain ⟨v,hv,hn,hw⟩ := exists_small_incidence_kernel_word (K := K) (m := 5)
    (by omega) (by omega) (incidenceSpan K E 5) (fun i => incidenceWord_mem_span _) ψ
  refine ⟨v,hv,hn,?_⟩
  norm_num [hK] at hw
  exact hw

/-- Extending coefficients preserves the actual zero-one incidence word. -/
theorem embed_incidenceWord {K k E : Type*} [Field K] [Field k] [Field E] [Algebra k E]
    {m : ℕ} (W : CodimTwo K m) :
    embedWord (K := E) (incidenceWord k W) = incidenceWord E W := by
  classical
  funext P
  simp [embedWord, incidenceWord, apply_ite]

/-- Each incidence row is in the scalar extension of the base incidence code. -/
theorem incidenceWord_mem_extendCode {K k E : Type*} [Field K] [Field k] [Field E]
    [Algebra k E] {m : ℕ} (W : CodimTwo K m) :
    incidenceWord E W ∈ extendCode (K := E) (incidenceSpan K k m) := by
  rw [← embed_incidenceWord (k := k) W]
  exact Submodule.subset_span ⟨incidenceWord k W, incidenceWord_mem_span W, rfl⟩

/-- The upper-bound witness lies in the actual extended incidence code used
in Lemma 3.2, without an additional nontriviality assumption. -/
theorem exists_small_extended_incidence_kernel_word
    {K k E : Type*} [Field K] [Finite K] [Field k] [Field E] [DecidableEq E]
    [Algebra k E] {m : ℕ} (hm : 4 ≤ m) (hQ : 32 < Nat.card K)
    (ψ : (Point K m → E) →ₗ[E] (E × E)) :
    ∃ v ∈ extendCode (K := E) (incidenceSpan K k m) ⊓ LinearMap.ker ψ,
      v ≠ 0 ∧ hammingNorm v ≤
        3 * Nat.card K ^ (m - 3) + (Nat.card K ^ (m - 4) - 1) / (Nat.card K - 1) := by
  exact exists_small_incidence_kernel_word hm hQ _
    (fun i => incidenceWord_mem_extendCode (k := k) (tripleSpace K hm i)) ψ

/-- Strict upper distance bound below three row weights for the actual
scalar-extended kernel code. -/
theorem extended_incidence_kernel_distance_lt_three_weight
    {K k E : Type*} [Field K] [Finite K] [Field k] [Field E] [DecidableEq E]
    [Algebra k E] {m : ℕ} (hm : 4 ≤ m) (hQ : 32 < Nat.card K)
    (ψ : (Point K m → E) →ₗ[E] (E × E)) :
    Code.dist (extendCode (K := E) (incidenceSpan K k m) ⊓ LinearMap.ker ψ :
      Set (Point K m → E)) < 3 * ((Nat.card K ^ (m - 2) - 1) / (Nat.card K - 1)) := by
  have hle := code_distance_le_of_nonzero_word _ _
    (exists_small_extended_incidence_kernel_word (k := k) hm hQ ψ)
  have hlt := triplePoints_union_card_lt_three_weight K hm hQ
  rw [triplePoints_union_card K hm hQ] at hlt
  exact lt_of_le_of_lt hle hlt

end Geometry
end OneAndAHalfJohnson
