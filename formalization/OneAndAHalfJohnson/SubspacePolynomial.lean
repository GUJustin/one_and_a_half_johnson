module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Root-product polynomials for finite vector subspaces

Concrete polynomial semantics for Lemma 3.5 of ePrint 2026/1894. The field `K`
is the geometry field and `E` is an extension field containing the subspaces.
The root product, its roots, monicity, degree, and injectivity are verified.
The coefficient-cancellation result is conditional on explicit Q-power support;
the general support theorem is proved in `SubspacePolynomialShape`.
No external classification or polynomial-shape axiom is introduced here.
-/

@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson.SubspacePolynomial

open Polynomial

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Fintype E]

/-- The actual product of `X-w` over all elements of a finite subspace. -/
def rootProduct (W : Submodule K E) : Polynomial E := by
  classical
  exact ∏ w : W, (X - C (w : E))

/-- The subspace root product is monic. -/
theorem rootProduct_monic (W : Submodule K E) : (rootProduct W).Monic := by
  classical
  exact monic_prod_X_sub_C (fun w : W => (w : E)) Finset.univ

/-- The roots of the product are exactly the elements of the subspace. -/
theorem rootProduct_eval_eq_zero (W : Submodule K E) (x : E) :
    (rootProduct W).eval x = 0 ↔ x ∈ W := by
  classical
  simp only [rootProduct, eval_prod, eval_sub, eval_X, eval_C,
    Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, sub_eq_zero]
  exact ⟨fun ⟨w, h⟩ => h ▸ w.property, fun h => ⟨⟨x, h⟩, rfl⟩⟩

/-- The root product has degree equal to the cardinality of the subspace. -/
theorem rootProduct_natDegree [Fintype K] (W : Submodule K E) :
    (rootProduct W).natDegree = Fintype.card K ^ Module.finrank K W := by
  classical
  rw [rootProduct, natDegree_finsetProd_X_sub_C_eq_card]
  simpa using Module.card_eq_pow_finrank (K := K) (V := W)

/-- Equality of root products determines the original subspace. -/
theorem rootProduct_injective : Function.Injective (rootProduct (K := K) (E := E)) := by
  intro W T h
  ext x
  rw [← rootProduct_eval_eq_zero W x, ← rootProduct_eval_eq_zero T x, h]

/-- A polynomial has Q-linearized support through level `d` if all its nonzero
coefficients occur at exponents `Q^j` with `j ≤ d`. This is a concrete property,
not a bundled assertion of the root-product shape theorem. -/
def QPowerSupport {F : Type*} [Field F] (Q d : ℕ) (P : Polynomial F) : Prop :=
  ∀ i, P.coeff i ≠ 0 → ∃ j ≤ d, i = Q ^ j

/-- Cancelling the top three possible coefficients in two Q-linearized
polynomials drops the degree to the next possible Q-power. For monic subspace
polynomials the leading coefficients agree automatically, leaving the two
coefficients singled out by Lemma 3.5. -/
theorem natDegree_sub_le_of_top_coefficients
    {F : Type*} [Field F] (Q d : ℕ) (hQ : 0 < Q) (hd : 3 ≤ d)
    (P R : Polynomial F) (hP : QPowerSupport Q d P) (hR : QPowerSupport Q d R)
    (h₀ : P.coeff (Q ^ d) = R.coeff (Q ^ d))
    (h₁ : P.coeff (Q ^ (d - 1)) = R.coeff (Q ^ (d - 1)))
    (h₂ : P.coeff (Q ^ (d - 2)) = R.coeff (Q ^ (d - 2))) :
    (P - R).natDegree ≤ Q ^ (d - 3) := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro i hi
  rw [coeff_sub, sub_eq_zero]
  by_contra hne
  have hs : ∃ j ≤ d, i = Q ^ j := by
    by_cases hp : P.coeff i = 0
    · apply hR i
      intro hr
      exact hne (hp.trans hr.symm)
    · exact hP i hp
  obtain ⟨j, hj, rfl⟩ := hs
  have hj' : d - 3 < j := by
    by_contra h
    exact (not_lt_of_ge (Nat.pow_le_pow_right hQ (Nat.le_of_not_gt h))) hi
  have he : j = d ∨ j = d - 1 ∨ j = d - 2 := by omega
  rcases he with rfl | rfl | rfl
  · exact hne h₀
  · exact hne h₁
  · exact hne h₂

/-- For ambient dimension at least five, the top two lower coefficients
identify a codimension-two subspace, provided its actual root product has the
Q-linearized support property. The intersection cardinality and root-count
argument are proved here; `SubspacePolynomialShape.rootProduct_qPowerSupport` supplies Q-linearized support. -/
theorem subspace_eq_of_top_two_coefficients [Fintype K]
    (m : ℕ) (hm : 5 ≤ m) (hdim : Module.finrank K E = m)
    (W T : Submodule K E)
    (hW : Module.finrank K W + 2 = m) (hT : Module.finrank K T + 2 = m)
    (hsW : QPowerSupport (Fintype.card K) (m - 2) (rootProduct W))
    (hsT : QPowerSupport (Fintype.card K) (m - 2) (rootProduct T))
    (h₁ : (rootProduct W).coeff (Fintype.card K ^ (m - 3)) =
      (rootProduct T).coeff (Fintype.card K ^ (m - 3)))
    (h₂ : (rootProduct W).coeff (Fintype.card K ^ (m - 4)) =
      (rootProduct T).coeff (Fintype.card K ^ (m - 4))) : W = T := by
  classical
  have hQ : 1 < Fintype.card K := Fintype.one_lt_card
  have hdW : (rootProduct W).natDegree = Fintype.card K ^ (m - 2) := by
    rw [rootProduct_natDegree]
    congr 1
    omega
  have hdT : (rootProduct T).natDegree = Fintype.card K ^ (m - 2) := by
    rw [rootProduct_natDegree]
    congr 1
    omega
  have h₀ : (rootProduct W).coeff (Fintype.card K ^ (m - 2)) =
      (rootProduct T).coeff (Fintype.card K ^ (m - 2)) := by
    have hW1 := (rootProduct_monic W).coeff_natDegree
    have hT1 := (rootProduct_monic T).coeff_natDegree
    rw [hdW] at hW1
    rw [hdT] at hT1
    exact hW1.trans hT1.symm
  have hd := natDegree_sub_le_of_top_coefficients (Fintype.card K) (m - 2)
    (by omega) (by omega) (rootProduct W) (rootProduct T) hsW hsT h₀
    (by simpa [Nat.sub_sub] using h₁) (by simpa [Nat.sub_sub] using h₂)
  have hdimInf : m - 4 ≤ Module.finrank K ↥(W ⊓ T) := by
    have he := Submodule.finrank_sup_add_finrank_inf_eq W T
    have hb : Module.finrank K ↥(W ⊔ T) ≤ m := by
      simpa [hdim] using (W ⊔ T).finrank_le
    omega
  have hcard : (rootProduct W - rootProduct T).natDegree < Fintype.card ↥(W ⊓ T) := by
    rw [Module.card_eq_pow_finrank (K := K)]
    apply lt_of_le_of_lt hd
    apply Nat.pow_lt_pow_right hQ
    omega
  have hz : rootProduct W - rootProduct T = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      (rootProduct W - rootProduct T) (f := fun x : ↥(W ⊓ T) => (x : E))
      Subtype.val_injective (fun x => by
        rw [eval_sub, (rootProduct_eval_eq_zero W x).mpr x.property.1,
          (rootProduct_eval_eq_zero T x).mpr x.property.2, sub_self]) hcard
  exact rootProduct_injective (sub_eq_zero.mp hz)

end OneAndAHalfJohnson.SubspacePolynomial
