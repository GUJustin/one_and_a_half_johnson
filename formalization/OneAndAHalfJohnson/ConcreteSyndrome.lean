module
public import OneAndAHalfJohnson.FiniteSyndrome
public import OneAndAHalfJohnson.GeometryIndependence
public import OneAndAHalfJohnson.GeometryCardinality
public import OneAndAHalfJohnson.ScalarExtension
public import OneAndAHalfJohnson.ConcreteArithmetic
public import OneAndAHalfJohnson.Targets.External
/-! Deterministic two-check construction for the paper's concrete geometry.
The exact number of incidence rows has square smaller than `2^128`, so the
finite hyperplane argument applies over the actual advertised coefficient field. -/
@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson
open Geometry

/-- The `PG(4,512)` incidence rows admit a separating ambient syndrome over
any field of cardinality `2^128`, with every first coordinate nonzero. -/
theorem exists_concrete_separating_syndrome
    (K E : Type*) [Field K] [Fintype K] [Field E] [Fintype E]
    (hK : Fintype.card K = 512) (hE : Fintype.card E = 2^128) :
    ∃ ψ : (Point K 5 → E) →ₗ[E] (E × E),
      (∀ W : CodimTwo K 5, (ψ (incidenceWord E W)).1 ≠ 0) ∧
      ∀ W T : CodimTwo K 5, W ≠ T →
        LinearIndependent E ![ψ (incidenceWord E W), ψ (incidenceWord E T)] := by
  classical
  let : Fintype (CodimTwo K 5) := Fintype.ofFinite _
  have : Finite (Module.Dual E (Point K 5 → E)) :=
    Finite.of_injective (fun f => (f : (Point K 5 → E) → E)) DFunLike.coe_injective
  let : Fintype (Module.Dual E (Point K 5 → E)) := Fintype.ofFinite _
  have hq : Nat.card K = 512 := by simpa only [Nat.card_eq_fintype_card] using hK
  apply exists_finite_separating_syndrome (incidenceWord E)
  · intro W hz
    have hw := incidence_weight (k := E) W
    rw [hz] at hw
    norm_num [hq, hK] at hw
  · intro W T hWT
    have hi : Function.Injective (![W,T] : Fin 2 → CodimTwo K 5) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    convert incidence_rows_independent_of_card_le_eight (k := E)
      (by omega : 32 < Nat.card K) (by omega : 4 ≤ 5) ![W,T] hi (by decide) using 1
    ext i
    fin_cases i <;> rfl
  · rw [← Nat.card_eq_fintype_card, codimTwo_card_512_five K hK, hE]
    norm_num

/-- Rank-nullity for a two-check map restricted to an ambient linear code. -/
theorem finrank_inter_ker_of_surjective {F V : Type*} [Field F]
    [AddCommGroup V] [Module F V] (D : Submodule F V) [FiniteDimensional F D]
    (ψ : V →ₗ[F] (F × F)) (hψ : Function.Surjective (ψ.comp D.subtype)) :
    Module.finrank F (D ⊓ LinearMap.ker ψ : Submodule F V) + 2 =
      Module.finrank F D := by
  let e : LinearMap.ker (ψ.comp D.subtype) ≃ₗ[F]
      (D ⊓ LinearMap.ker ψ : Submodule F V) :=
    { toFun := fun x => ⟨x.val.val, x.val.property, x.property⟩
      invFun := fun x => ⟨⟨x.val, x.property.1⟩, x.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have h := (ψ.comp D.subtype).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hψ, finrank_top, e.finrank_eq] at h
  simpa [Module.finrank_prod, add_comm] using h

/-- Hamada's permitted external rank formula and surjectivity of the two checks
 give the actual concrete kernel dimension, rather than assuming it. -/
theorem concrete_kernel_finrank_of_Hamada
    (hH : Targets.HamadaBinaryRank) (K E : Type) [Field K] [Fintype K]
    [CharP K 2] [Field E] [Algebra (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
    (hK : Fintype.card K = 512)
    (ψ : (Point K 5 → E) →ₗ[E] (E × E))
    (hψ : Function.Surjective (ψ.comp
      (extendCode (K := E) (incidenceSpan K (ZMod 2) 5)).subtype)) :
    Module.finrank E
      (extendCode (K := E) (incidenceSpan K (ZMod 2) 5) ⊓ LinearMap.ker ψ :
        Submodule E (Point K 5 → E)) = 3604584374 := by
  have h := finrank_inter_ker_of_surjective
    (extendCode (K := E) (incidenceSpan K (ZMod 2) 5)) ψ hψ
  rw [finrank_extendCode, hH K hK, ConcreteArithmetic.hamada_matrix_trace] at h
  omega

end OneAndAHalfJohnson
