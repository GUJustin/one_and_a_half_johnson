module

public import OneAndAHalfJohnson.Geometry
public import OneAndAHalfJohnson.ScalarExtension
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Algebra.ZMod

/-!
# A polynomial bound on incidence-code dimension

For fixed geometry-field order Q, incidence rows are polynomial functions of
projective representatives of degree at most 2(Q-1). We bound their span using
products of the constant function and the m coordinate functions, obtaining
(m+1)^(2(Q-1)). This coarse bound suffices for the asymptotic rate argument;
it does not assert the sharper prime-field degree bound quoted in the paper.
-/

@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson.Geometry
open scoped Classical Pointwise

/-- A codimension-two subspace is the common zero set of two linear functionals. -/
theorem exists_two_functionals_kernel {K : Type*} [Field K] {m : ℕ} (W : CodimTwo K m) :
    ∃ l₀ l₁ : (Fin m → K) →ₗ[K] K,
      ∀ x, x ∈ W.val ↔ l₀ x = 0 ∧ l₁ x = 0 := by
  have hdim : Module.finrank K ((Fin m → K) ⧸ W.val) = 2 := by
    have h := Submodule.finrank_quotient_add_finrank W.val
    have hW := W.property
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    omega
  let e : ((Fin m → K) ⧸ W.val) ≃ₗ[K] (Fin 2 → K) :=
    LinearEquiv.ofFinrankEq _ _ (by simp [hdim, Module.finrank_fintype_fun_eq_card])
  let f : (Fin m → K) →ₗ[K] (Fin 2 → K) := e.toLinearMap.comp W.val.mkQ
  refine ⟨(LinearMap.proj 0).comp f, (LinearMap.proj 1).comp f, ?_⟩
  intro x
  have hx : x ∈ W.val ↔ f x = 0 := by
    simp [f]
  rw [hx]
  change f x = 0 ↔ f x 0 = 0 ∧ f x 1 = 0
  constructor
  · intro h; simp [h]
  · rintro ⟨h0,h1⟩
    funext i
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl
    · exact h0
    · exact h1

/-- Constant and coordinate functions evaluated at the selected projective representatives. -/
def affineCoordinate {K : Type*} [Field K] {m : ℕ} : Option (Fin m) → Point K m → K
  | none => 1
  | some i => fun P => P.rep i

/-- The finite family of affine coordinate functions. -/
def affineCoordinates (K : Type*) [Field K] (m : ℕ) : Finset (Point K m → K) :=
  Finset.univ.image affineCoordinate

/-- The linear span of constants and coordinate evaluations. -/
def affineCoordinateSpan (K : Type*) [Field K] (m : ℕ) : Submodule K (Point K m → K) :=
  Submodule.span K (affineCoordinates K m : Set (Point K m → K))

/-- The affine coordinate generator set has at most m+1 elements. -/
theorem affineCoordinates_card_le (K : Type*) [Field K] (m : ℕ) :
    (affineCoordinates K m).card ≤ m + 1 := by
  simpa [affineCoordinates] using
    (Finset.card_image_le (s := (Finset.univ : Finset (Option (Fin m))))
      (f := affineCoordinate (K := K)))

/-- The constant function belongs to the affine coordinate span. -/
theorem one_mem_affineCoordinateSpan (K : Type*) [Field K] (m : ℕ) :
    (1 : Point K m → K) ∈ affineCoordinateSpan K m := by
  apply Submodule.subset_span
  exact Finset.mem_image.mpr ⟨none, Finset.mem_univ _, rfl⟩

/-- Any linear functional evaluated on projective representatives lies in that span. -/
theorem linearFunctional_mem_affineCoordinateSpan {K : Type*} [Field K] {m : ℕ}
    (l : (Fin m → K) →ₗ[K] K) :
    (fun P : Point K m => l P.rep) ∈ affineCoordinateSpan K m := by
  have he : (fun P : Point K m => l P.rep) =
      ∑ i : Fin m, (l (fun j => if i = j then 1 else 0)) • affineCoordinate (some i) := by
    funext P
    rw [LinearMap.pi_apply_eq_sum_univ l P.rep]
    simp [affineCoordinate, mul_comm]
  rw [he]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  exact Submodule.subset_span (Finset.mem_image.mpr ⟨some i, Finset.mem_univ _, rfl⟩)

/-- Powers of the affine-coordinate span have polynomially bounded dimension. -/
theorem finrank_affineCoordinateSpan_pow_le (K : Type*) [Field K] [Finite K] (m d : ℕ) :
    Module.finrank K ((affineCoordinateSpan K m) ^ d : Submodule K (Point K m → K)) ≤ (m + 1) ^ d := by
  rw [affineCoordinateSpan, Submodule.span_pow, ← Finset.coe_pow]
  exact (finrank_span_finset_le_card _).trans
    (Finset.card_pow_le.trans (Nat.pow_le_pow_left (affineCoordinates_card_le K m) d))

/-- A finite-field zero test is a polynomial of degree Q-1. -/
theorem finiteField_zero_indicator {K : Type*} [Field K] [Fintype K] (x : K) :
    1 - x ^ (Fintype.card K - 1) = if x = 0 then 1 else 0 := by
  by_cases hx : x = 0
  · simp [hx, Nat.sub_ne_zero_of_lt Fintype.one_lt_card]
  · simp [hx, FiniteField.pow_card_sub_one_eq_one x hx]

/-- The actual incidence row is a product of two polynomial zero tests. -/
theorem incidenceWord_eq_two_zero_tests {K : Type*} [Field K] [Fintype K]
    {m : ℕ} (W : CodimTwo K m) :
    ∃ l₀ l₁ : (Fin m → K) →ₗ[K] K,
      incidenceWord K W =
        (1 - (fun P : Point K m => l₀ P.rep) ^ (Fintype.card K - 1)) *
        (1 - (fun P : Point K m => l₁ P.rep) ^ (Fintype.card K - 1)) := by
  obtain ⟨l₀,l₁,hker⟩ := exists_two_functionals_kernel W
  refine ⟨l₀,l₁,?_⟩
  funext P
  have hP : Incident W.val P ↔ l₀ P.rep = 0 ∧ l₁ P.rep = 0 :=
    (incident_iff_rep_mem W.val P).trans (hker P.rep)
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.one_apply, Pi.pow_apply, finiteField_zero_indicator]
  by_cases h0 : l₀ P.rep = 0 <;> by_cases h1 : l₁ P.rep = 0 <;>
    simp [incidenceWord, hP, h0, h1]

/-- Every incidence row has degree at most 2(Q-1) in the affine coordinates. -/
theorem incidenceWord_mem_affineCoordinateSpan_pow {K : Type*} [Field K] [Fintype K]
    {m : ℕ} (W : CodimTwo K m) :
    incidenceWord K W ∈ (affineCoordinateSpan K m) ^ (2 * (Fintype.card K - 1)) := by
  obtain ⟨l₀,l₁,heq⟩ := incidenceWord_eq_two_zero_tests W
  let L := affineCoordinateSpan K m
  have h1 : (1 : Point K m → K) ∈ L ^ (Fintype.card K - 1) := by
    simpa only [one_pow] using L.pow_mem_pow (one_mem_affineCoordinateSpan K m) (Fintype.card K - 1)
  have h0 := L.pow_mem_pow (linearFunctional_mem_affineCoordinateSpan l₀) (Fintype.card K - 1)
  have h2 := L.pow_mem_pow (linearFunctional_mem_affineCoordinateSpan l₁) (Fintype.card K - 1)
  rw [heq, two_mul, pow_add]
  exact Submodule.mul_mem_mul ((L ^ _).sub_mem h1 h0) ((L ^ _).sub_mem h1 h2)

/-- A genuine polynomial-in-dimension rank bound for the geometry-field code. -/
theorem incidenceSpan_finrank_le_polynomial (K : Type*) [Field K] [Fintype K] (m : ℕ) :
    Module.finrank K (incidenceSpan K K m) ≤ (m + 1) ^ (2 * (Fintype.card K - 1)) := by
  have hle : incidenceSpan K K m ≤
      (affineCoordinateSpan K m) ^ (2 * (Fintype.card K - 1)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨W,rfl⟩
    exact incidenceWord_mem_affineCoordinateSpan_pow W
  exact (Submodule.finrank_mono hle).trans (finrank_affineCoordinateSpan_pow_le K m _)

/-- Extending coefficients of the incidence code gives its incidence span
over the larger coefficient field, since every entry is zero or one. -/
theorem extendCode_incidenceSpan {K k E : Type*} [Field K] [Field k] [Field E]
    [Algebra k E] (m : ℕ) :
    extendCode (K := E) (incidenceSpan K k m) = incidenceSpan K E m := by
  rw [incidenceSpan, extendCode_span]
  have he : embedWord (K := E) '' Set.range (incidenceWord k : CodimTwo K m → Point K m → k) =
      Set.range (incidenceWord E : CodimTwo K m → Point K m → E) := by
    rw [← Set.range_comp]
    congr 1
    funext W P
    simp [embedWord, incidenceWord]
  rw [he]
  rfl

/-- The same polynomial bound holds for a base coefficient field embedded in
the geometry field; scalar extension preserves its dimension. -/
theorem incidenceSpan_base_finrank_le_polynomial
    (K k : Type*) [Field K] [Fintype K] [Field k] [Algebra k K] (m : ℕ) :
    Module.finrank k (incidenceSpan K k m) ≤ (m + 1) ^ (2 * (Fintype.card K - 1)) := by
  rw [← finrank_extendCode (K := K) (incidenceSpan K k m), extendCode_incidenceSpan]
  exact incidenceSpan_finrank_le_polynomial K m

/-- A scalar-extended base incidence code retains the polynomial dimension bound. -/
theorem extended_incidenceSpan_finrank_le_polynomial
    (K k E : Type*) [Field K] [Fintype K] [Field k] [Field E]
    [Algebra k K] [Algebra k E] (m : ℕ) :
    Module.finrank E (extendCode (K := E) (incidenceSpan K k m)) ≤
      (m + 1) ^ (2 * (Fintype.card K - 1)) := by
  rw [finrank_extendCode]
  exact incidenceSpan_base_finrank_le_polynomial K k m

/-- The prime-field incidence code in the paper satisfies the coarse polynomial bound. -/
theorem prime_incidenceSpan_finrank_le_polynomial
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [Fintype K] [CharP K p] (m : ℕ) :
    Module.finrank (ZMod p) (incidenceSpan K (ZMod p) m) ≤
      (m + 1) ^ (2 * (Fintype.card K - 1)) := by
  let : Algebra (ZMod p) K := ZMod.algebra K p
  exact incidenceSpan_base_finrank_le_polynomial K (ZMod p) m

end OneAndAHalfJohnson.Geometry
