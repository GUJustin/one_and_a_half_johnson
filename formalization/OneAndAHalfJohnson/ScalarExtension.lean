module

public import OneAndAHalfJohnson.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

/-!
# Scalar extension commutes with coordinate shortening

The scalar-extension step used in Section 3.1 of ePrint 2026/1894 is proved
for any finite-dimensional field extension and any coordinate set.

The proof first projects an extended word along arbitrary base-field linear
functionals. Span induction keeps every resulting coefficient word in the
base code. A finite field basis then reconstructs the original word, while
each coefficient word inherits its coordinate support. No finite-coordinate
or finite-field assumption is needed.
-/

@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson

variable {k K I : Type*} [Field k] [Field K] [Algebra k K]

/-- Embed a word by applying the field inclusion to each coordinate. -/
def embedWord (u : I → k) : I → K := fun i => algebraMap k K (u i)

/-- Extension of scalars expressed as the span of embedded words. -/
def extendCode (U : Submodule k (I → k)) : Submodule K (I → K) :=
  Submodule.span K (embedWord '' (U : Set (I → k)))

/-- Words supported on the indicated coordinates. -/
def supportedCode (S : Set I) : Submodule k (I → k) where
  carrier := {u | ∀ i, i ∉ S → u i = 0}
  zero_mem' := by simp
  add_mem' := by intro u v hu hv i hi; simp [hu i hi, hv i hi]
  smul_mem' := by intro a u hu i hi; simp [hu i hi]

/-- Every linear coefficient projection of an extended word belongs to the base code. -/
theorem coefficient_mem_base (U : Submodule k (I → k)) {v : I → K}
    (hv : v ∈ extendCode (K := K) U) :
    ∀ φ : K →ₗ[k] k, (fun i => φ (v i)) ∈ U := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨u, hu, rfl⟩ := hv
    intro φ
    have h : (fun i => φ (embedWord (K := K) u i)) = φ 1 • u := by
      funext i
      change φ (algebraMap k K (u i)) = φ 1 * u i
      have he : algebraMap k K (u i) = u i • (1 : K) := by simp [Algebra.smul_def]
      rw [he, map_smul]
      simp [mul_comm]
    rw [h]
    exact U.smul_mem _ hu
  | zero =>
    intro φ
    convert U.zero_mem using 1
    funext i
    exact map_zero φ
  | add x y hx hy ihx ihy =>
    intro φ
    convert U.add_mem (ihx φ) (ihy φ) using 1
    funext i
    exact map_add φ (x i) (y i)
  | smul a x hx ih =>
    intro φ
    exact ih (φ.comp (LinearMap.mul k K a))

/-- Extension of scalars commutes with shortening to a coordinate set. -/
theorem extendCode_inf_supported [FiniteDimensional k K]
    (U : Submodule k (I → k)) (S : Set I) :
    extendCode (K := K) (U ⊓ supportedCode S) =
      extendCode (K := K) U ⊓ supportedCode S := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨u, hu, rfl⟩
    constructor
    · exact Submodule.subset_span ⟨u, hu.1, rfl⟩
    · intro i hi
      change algebraMap k K (u i) = 0
      rw [hu.2 i hi, map_zero]
  · intro v hv
    let b := Module.finBasis k K
    have hcoeff (j) : (fun i => b.coord j (v i)) ∈ U ⊓ supportedCode S := by
      constructor
      · exact coefficient_mem_base U hv.1 (b.coord j)
      · intro i hi
        change b.coord j (v i) = 0
        rw [hv.2 i hi, map_zero]
    have hsum : v = ∑ j, b j • embedWord (K := K) (fun i => b.coord j (v i)) := by
      funext i
      simp only [Finset.sum_apply, Pi.smul_apply, embedWord, smul_eq_mul]
      simpa only [Module.Basis.coord_apply, Algebra.smul_def, mul_comm] using (b.sum_repr (v i)).symm
    rw [hsum]
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨_, hcoeff j, rfl⟩

/-- Scalar extension preserves the dimension of a finite-length code. -/
theorem finrank_extendCode [Fintype I] (U : Submodule k (I → k)) :
    Module.finrank K (extendCode (K := K) U) = Module.finrank k U := by
  classical
  let b := Module.finBasis k U
  let w := fun j => embedWord (K := K) (b j : I → k)
  have hli : LinearIndependent K w := by
    apply linearIndependent_algebraMap_comp_iff.mpr
    exact b.linearIndependent.map' U.subtype U.ker_subtype
  have hspan : Submodule.span K (Set.range w) = extendCode (K := K) U := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact Submodule.subset_span ⟨b j, (b j).property, rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨u, hu, rfl⟩
      have he : embedWord (K := K) u =
          ∑ j, algebraMap k K (b.repr ⟨u, hu⟩ j) • w j := by
        funext i
        have hh := congrArg (fun x : U => (x : I → k) i) (b.sum_repr ⟨u, hu⟩)
        simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul] at hh
        change algebraMap k K (u i) = _
        rw [← hh, map_sum]
        simp [w, embedWord, map_mul, Algebra.smul_def]
      rw [he]
      apply Submodule.sum_mem
      intro j hj
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  rw [← hspan, finrank_span_eq_card hli]
  simp

/-- Enlarging a base code enlarges its extension. -/
theorem extendCode_mono {U V : Submodule k (I → k)} (h : U ≤ V) :
    extendCode (K := K) U ≤ extendCode (K := K) V := by
  apply Submodule.span_mono
  exact Set.image_mono h

/-- Extending the span of generators equals the span of their embeddings. -/
theorem extendCode_span (s : Set (I → k)) :
    extendCode (K := K) (Submodule.span k s) =
      Submodule.span K (embedWord '' s) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨u, hu, rfl⟩
    induction hu using Submodule.span_induction with
    | mem u hu => exact Submodule.subset_span ⟨u, hu, rfl⟩
    | zero =>
      have h : embedWord (K := K) (0 : I → k) = 0 := by ext; simp [embedWord]
      rw [h]
      exact Submodule.zero_mem _
    | add x y hx hy ihx ihy =>
      have h : embedWord (K := K) (x + y) = embedWord x + embedWord y := by
        ext; simp [embedWord]
      rw [h]
      exact Submodule.add_mem _ ihx ihy
    | smul a x hx ih =>
      have h : embedWord (K := K) (a • x) = algebraMap k K a • embedWord x := by
        ext; simp [embedWord]
      rw [h]
      exact Submodule.smul_mem _ _ ih
  · apply Submodule.span_mono
    exact Set.image_mono Submodule.subset_span

/-- A generator bound for a shortened base code transfers to its scalar extension. -/
theorem shortened_extendCode_le_span [FiniteDimensional k K]
    (U : Submodule k (I → k)) (S : Set I) (s : Set (I → k))
    (h : U ⊓ supportedCode S ≤ Submodule.span k s) :
    extendCode (K := K) U ⊓ supportedCode S ≤
      Submodule.span K (embedWord '' s) := by
  rw [← extendCode_inf_supported, ← extendCode_span]
  exact extendCode_mono h

/-- The single-generator shortening bound survives scalar extension. -/
theorem shortened_extendCode_le_singleton [FiniteDimensional k K]
    (U : Submodule k (I → k)) (S : Set I) (u : I → k)
    (h : U ⊓ supportedCode S ≤ Submodule.span k {u}) :
    extendCode (K := K) U ⊓ supportedCode S ≤
      Submodule.span K {embedWord u} := by
  simpa only [Set.image_singleton] using shortened_extendCode_le_span U S {u} h

/-- The two-generator shortening bound survives scalar extension. -/
theorem shortened_extendCode_le_pair [FiniteDimensional k K]
    (U : Submodule k (I → k)) (S : Set I) (u v : I → k)
    (h : U ⊓ supportedCode S ≤ Submodule.span k {u, v}) :
    extendCode (K := K) U ⊓ supportedCode S ≤
      Submodule.span K {embedWord u, embedWord v} := by
  simpa only [Set.image_insert_eq, Set.image_singleton] using
    shortened_extendCode_le_span U S {u, v} h

end OneAndAHalfJohnson
