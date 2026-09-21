module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.GroupTheory.Index
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Tactic.Linarith

/-!
# Exact finite counts for a random linear functional

The probability calculation in Section 3.2 (p. 13) uses that a uniformly
chosen linear functional sends a fixed nonzero vector uniformly into the
base field. This module states the count without divisions or measure choices.
-/

@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson

variable {F V : Type*} [Field F] [Fintype F] [DecidableEq F]
  [AddCommGroup V] [Module F V] [Fintype (Module.Dual F V)]

omit [Fintype F] [DecidableEq F] [Fintype (Module.Dual F V)] in
/-- Evaluation at a nonzero vector is a surjection from the dual to the field. -/
theorem dual_evaluation_surjective {x : V} (hx : x ≠ 0) :
    Function.Surjective (fun φ : Module.Dual F V => φ x) := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one F hx
  intro a
  exact ⟨a • φ, by simp [hφ]⟩

omit [Fintype F] in
/-- Each field value has the same number of linear-functional preimages. -/
theorem dual_evaluation_fibers {x : V} (hx : x ≠ 0) (a b : F) :
    (Finset.univ.filter (fun φ : Module.Dual F V => φ x = a)).card =
      (Finset.univ.filter (fun φ : Module.Dual F V => φ x = b)).card := by
  let e := ((Module.Dual.eval F V) x).toAddMonoidHom
  exact AddMonoidHom.card_fiber_eq_of_mem_range e
    (dual_evaluation_surjective hx a) (dual_evaluation_surjective hx b)

/-- Fraction-free uniformity: the zero fiber has exactly one q-th of all
linear functionals. -/
theorem dual_evaluation_zero_count {x : V} (hx : x ≠ 0) :
    Fintype.card (Module.Dual F V) = Fintype.card F *
      (Finset.univ.filter (fun φ : Module.Dual F V => φ x = 0)).card := by
  classical
  calc
    Fintype.card (Module.Dual F V) =
        ∑ a : F, (Finset.univ.filter (fun φ : Module.Dual F V => φ x = a)).card := by
      simpa using (Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset (Module.Dual F V))) (t := Finset.univ)
        (f := fun φ => φ x) (by intro φ hφ; exact Finset.mem_univ _))
    _ = Fintype.card F *
        (Finset.univ.filter (fun φ : Module.Dual F V => φ x = 0)).card := by
      simp_rw [dual_evaluation_fibers (F := F) hx _ 0]
      simp

/-- The fraction of linear functionals nonzero on a fixed nonzero vector is
`(q-1)/q`, stated as an exact integer identity. -/
theorem dual_evaluation_nonzero_count {x : V} (hx : x ≠ 0) :
    Fintype.card F * (Finset.univ.filter
      (fun φ : Module.Dual F V => φ x ≠ 0)).card =
      Fintype.card (Module.Dual F V) * (Fintype.card F - 1) := by
  classical
  have hz := dual_evaluation_zero_count (F := F) hx
  have hs := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Module.Dual F V))) (p := fun φ => φ x = 0)
  simp only [Finset.card_univ] at hs
  have hq : Fintype.card F - 1 + 1 = Fintype.card F :=
    Nat.sub_add_cancel (by have := Fintype.card_pos (α := F); omega)
  nlinarith

end OneAndAHalfJohnson
