module

public import OneAndAHalfJohnson.SubspacePolynomial
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Q-linearized shape of actual subspace root products

The proof constructs a nonzero Q-linearized polynomial annihilating a basis by
linear dimension counting, extends annihilation to the whole subspace using
finite-field Frobenius linearity, and identifies the resulting polynomial with
a scalar multiple of the actual root product.
-/

@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson.SubspacePolynomial

open Polynomial

/-- A coefficient vector defines a polynomial with explicitly Q-power support. -/
def qPolynomial {E : Type*} [Field E] (Q d : ℕ) (c : Fin (d + 1) → E) : Polynomial E :=
  ∑ i, monomial (Q ^ i.val) (c i)

/-- Extraction of the coefficient vector, because the Q-power exponents are distinct. -/
theorem qPolynomial_coeff {E : Type*} [Field E] (Q d : ℕ) (hQ : 1 < Q)
    (c : Fin (d + 1) → E) (j : Fin (d + 1)) :
    (qPolynomial Q d c).coeff (Q ^ j.val) = c j := by
  classical
  simp only [qPolynomial, finsetSum_coeff, coeff_monomial]
  have he (i : Fin (d + 1)) : Q ^ i.val = Q ^ j.val ↔ i = j := by
    rw [Nat.pow_right_inj hQ, Fin.val_inj]
  simp_rw [he]
  simp

/-- The polynomial coefficient vector is faithfully represented. -/
theorem qPolynomial_ne_zero {E : Type*} [Field E] (Q d : ℕ) (hQ : 1 < Q)
    (c : Fin (d + 1) → E) (hc : c ≠ 0) : qPolynomial Q d c ≠ 0 := by
  intro h
  apply hc
  funext j
  have hj := qPolynomial_coeff Q d hQ c j
  simpa [h] using hj.symm

/-- The displayed monomial sum has Q-power support through the specified level. -/
theorem qPolynomial_support {E : Type*} [Field E] (Q d : ℕ)
    (c : Fin (d + 1) → E) : QPowerSupport Q d (qPolynomial Q d c) := by
  classical
  intro n hn
  have he : ∃ j : Fin (d + 1), (monomial (Q ^ j.val) (c j)).coeff n ≠ 0 := by
    by_contra h
    push Not at h
    exact hn (by simp [qPolynomial, h])
  obtain ⟨j, hj⟩ := he
  refine ⟨j.val, by omega, ?_⟩
  by_contra h
  exact hj (by simp [coeff_monomial, Ne.symm h])

/-- Support bounds give the expected degree bound. -/
theorem qPolynomial_natDegree_le {E : Type*} [Field E] (Q d : ℕ) (hQ : 0 < Q)
    (c : Fin (d + 1) → E) : (qPolynomial Q d c).natDegree ≤ Q ^ d := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  by_contra h
  obtain ⟨j, hj, rfl⟩ := qPolynomial_support Q d c n h
  exact (not_lt_of_ge (Nat.pow_le_pow_right hQ hj)) hn

variable {K E : Type*} [Field K] [Fintype K] [Field E] [Algebra K E]

/-- Evaluation of a Q-linearized polynomial as a K-linear map. -/
def qEvaluation (d : ℕ) (c : Fin (d + 1) → E) : E →ₗ[K] E :=
  ∑ i, c i • ((FiniteField.frobeniusAlgHom K E) ^ i.val).toLinearMap

/-- Frobenius iteration identifies linear-map evaluation with polynomial evaluation. -/
theorem qEvaluation_apply (d : ℕ) (c : Fin (d + 1) → E) (x : E) :
    qEvaluation (K := K) d c x = (qPolynomial (Fintype.card K) d c).eval x := by
  simp only [qEvaluation, LinearMap.sum_apply, LinearMap.smul_apply,
    AlgHom.toLinearMap_apply, smul_eq_mul, qPolynomial, eval_finsetSum, eval_monomial]
  congr 1
  funext i
  rw [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate]

/-- Evaluation at an ordered list is linear in the polynomial coefficients. -/
def basisEvaluation (d : ℕ) (b : Fin d → E) :
    (Fin (d + 1) → E) →ₗ[E] (Fin d → E) where
  toFun c j := ∑ i, c i * b j ^ (Fintype.card K ^ i.val)
  map_add' c c' := by
    ext j
    simp [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    ext j
    simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

omit [Field K] [Algebra K E] in
/-- There are more polynomial coefficients than prescribed root constraints. -/
theorem exists_nonzero_annihilator_coefficients (d : ℕ) (b : Fin d → E) :
    ∃ c : Fin (d + 1) → E, c ≠ 0 ∧ basisEvaluation (K := K) d b c = 0 := by
  have hn : ¬ Function.Injective (basisEvaluation (K := K) d b) := by
    intro hi
    have hd := LinearMap.finrank_le_finrank_of_injective hi
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hd
    omega
  obtain ⟨c, c', he, hne⟩ := Function.not_injective_iff.mp hn
  refine ⟨c - c', sub_ne_zero.mpr hne, ?_⟩
  rw [map_sub, he, sub_self]

/-- The actual root product of a finite K-subspace has Q-power support.
No subspace-polynomial shape assumption is needed: the proof uses Frobenius
linearity, dimension counting, and divisibility by the distinct root factors. -/
theorem rootProduct_qPowerSupport [Fintype E] (W : Submodule K E) :
    QPowerSupport (Fintype.card K) (Module.finrank K W) (rootProduct W) := by
  classical
  let d := Module.finrank K W
  let b : Fin d → E := fun j => (Module.finBasis K W j : E)
  obtain ⟨c, hc, hvanish⟩ := exists_nonzero_annihilator_coefficients (K := K) d b
  let P := qPolynomial (Fintype.card K) d c
  have hP : P ≠ 0 := qPolynomial_ne_zero _ _ Fintype.one_lt_card c hc
  have hlin : (qEvaluation (K := K) d c).comp W.subtype = 0 := by
    apply (Module.finBasis K W).ext
    intro j
    rw [LinearMap.comp_apply, qEvaluation_apply]
    have hj := congrFun hvanish j
    simpa [basisEvaluation, qPolynomial, eval_finsetSum, eval_monomial, b] using hj
  have hroot : ∀ x ∈ W, P.eval x = 0 := by
    intro x hx
    have hh := congrArg (fun f : W →ₗ[K] E => f ⟨x, hx⟩) hlin
    simpa [LinearMap.comp_apply, qEvaluation_apply, P] using hh
  have hdvd : rootProduct W ∣ P := by
    unfold rootProduct
    apply Finset.prod_dvd_of_coprime
    · intro a ha b hb hab
      exact pairwise_coprime_X_sub_C (s := fun x : W => (x : E)) Subtype.val_injective hab
    · intro x hx
      exact dvd_iff_isRoot.mpr (hroot x x.property)
  have hdeg : P.natDegree ≤ (rootProduct W).natDegree := by
    rw [rootProduct_natDegree]
    exact qPolynomial_natDegree_le _ _ Fintype.card_pos c
  have he : P = C P.leadingCoeff * rootProduct W :=
    eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (rootProduct_monic W) hdvd hdeg
  intro n hn
  apply qPolynomial_support (Fintype.card K) d c n
  change P.coeff n ≠ 0
  rw [he, coeff_C_mul]
  exact mul_ne_zero (leadingCoeff_ne_zero.mpr hP) hn

/-- At level two, the three displayed coefficients determine the entire
Q-linearized polynomial. -/
theorem qPowerSupport_two_ext {F : Type*} [Field F] (Q : ℕ)
    (P R : Polynomial F) (hP : QPowerSupport Q 2 P) (hR : QPowerSupport Q 2 R)
    (h₀ : P.coeff (Q ^ 2) = R.coeff (Q ^ 2))
    (h₁ : P.coeff Q = R.coeff Q) (h₂ : P.coeff 1 = R.coeff 1) : P = R := by
  ext n
  by_contra hne
  have hs : ∃ j ≤ 2, n = Q ^ j := by
    by_cases hp : P.coeff n = 0
    · apply hR n
      intro hr
      exact hne (hp.trans hr.symm)
    · exact hP n hp
  obtain ⟨j, hj, rfl⟩ := hs
  have he : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases he with rfl | rfl | rfl
  · exact hne (by simpa using h₂)
  · exact hne (by simpa using h₁)
  · exact hne h₀

/-- The top two lower coefficients of actual codimension-two subspace
polynomials determine the subspace in every ambient dimension at least four.
This discharges the coefficient-uniqueness argument of Lemma 3.5 without any
polynomial-shape premise. -/
theorem rootProduct_top_two_determine_subspace [Fintype E]
    (m : ℕ) (hm : 4 ≤ m) (hdim : Module.finrank K E = m)
    (W T : Submodule K E)
    (hW : Module.finrank K W + 2 = m) (hT : Module.finrank K T + 2 = m)
    (h₁ : (rootProduct W).coeff (Fintype.card K ^ (m - 3)) =
      (rootProduct T).coeff (Fintype.card K ^ (m - 3)))
    (h₂ : (rootProduct W).coeff (Fintype.card K ^ (m - 4)) =
      (rootProduct T).coeff (Fintype.card K ^ (m - 4))) : W = T := by
  have hdW : Module.finrank K W = m - 2 := by omega
  have hdT : Module.finrank K T = m - 2 := by omega
  have hsW := rootProduct_qPowerSupport W
  have hsT := rootProduct_qPowerSupport T
  rw [hdW] at hsW
  rw [hdT] at hsT
  by_cases hm5 : 5 ≤ m
  · exact subspace_eq_of_top_two_coefficients m hm5 hdim W T hW hT hsW hsT h₁ h₂
  · have hm4 : m = 4 := by omega
    rw [hm4] at hsW hsT hdW hdT h₁ h₂
    apply rootProduct_injective
    apply qPowerSupport_two_ext (Fintype.card K) _ _ hsW hsT
    · have hdW' : (rootProduct W).natDegree = Fintype.card K ^ 2 := by
        simpa [hdW] using rootProduct_natDegree W
      have hdT' : (rootProduct T).natDegree = Fintype.card K ^ 2 := by
        simpa [hdT] using rootProduct_natDegree T
      have hW1 := (rootProduct_monic W).coeff_natDegree
      have hT1 := (rootProduct_monic T).coeff_natDegree
      rw [hdW'] at hW1
      rw [hdT'] at hT1
      exact hW1.trans hT1.symm
    · simpa using h₁
    · simpa using h₂

end OneAndAHalfJohnson.SubspacePolynomial
