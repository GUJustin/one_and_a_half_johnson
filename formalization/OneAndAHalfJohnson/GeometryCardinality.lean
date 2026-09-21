module

public import OneAndAHalfJohnson.Geometry
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Counting codimension-two subspaces

Ordered independent pairs can be counted either directly or by their spanned
two-dimensional subspace. Dual annihilators identify the latter subspaces with
the codimension-two geometry indexing the paper's incidence vectors.
-/

@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson.Geometry

/-- Two-dimensional subspaces of a vector space. -/
abbrev TwoSubspace (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :=
  {W : Submodule K V // Module.finrank K W = 2}

/-- Ordered independent pairs in a vector space. -/
abbrev TwoFrame (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :=
  {v : Fin 2 → V // LinearIndependent K v}

/-- An independent pair in a two-dimensional subspace spans that subspace
when viewed in the ambient vector space. -/
theorem frame_span_eq {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (W : TwoSubspace K V) (v : TwoFrame K W.val) :
    Submodule.span K (Set.range (fun i => (v.val i : V))) = W.val := by
  have : FiniteDimensional K W.val := Module.finite_of_finrank_pos (by rw [W.property]; omega)
  have hli : LinearIndependent K (fun i => (v.val i : V)) := by
    convert v.property.map' W.val.subtype W.val.ker_subtype using 1
    funext i
    rfl
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact (v.val i).property
  · rw [finrank_span_eq_card hli, Fintype.card_fin, W.property]

/-- Forget the chosen two-dimensional subspace and keep its independent pair. -/
def frameInSubspaceToFrame {K V : Type*} [Field K] [AddCommGroup V] [Module K V] :
    (Σ W : TwoSubspace K V, TwoFrame K W.val) → TwoFrame K V :=
  fun x => ⟨fun i => (x.2.val i : V), x.2.property.map' x.1.val.subtype x.1.val.ker_subtype⟩

/-- Every independent pair belongs to its unique spanned two-dimensional subspace. -/
theorem frameInSubspaceToFrame_bijective {K V : Type*}
    [Field K] [AddCommGroup V] [Module K V] :
    Function.Bijective (frameInSubspaceToFrame (K := K) (V := V)) := by
  constructor
  · intro x y heq
    have hv : (fun i => (x.2.val i : V)) = (fun i => (y.2.val i : V)) := congrArg Subtype.val heq
    have hW : x.1 = y.1 := by
      apply Subtype.ext
      rw [← frame_span_eq x.1 x.2, ← frame_span_eq y.1 y.2, hv]
    cases x with
    | mk W v =>
      cases y with
      | mk T w =>
        dsimp at hW
        subst T
        congr 1
        apply Subtype.ext
        funext i
        exact Subtype.ext (congrFun hv i)
  · intro v
    let W : TwoSubspace K V := ⟨Submodule.span K (Set.range v.val), by
      rw [finrank_span_eq_card v.property, Fintype.card_fin]⟩
    let w : Fin 2 → W.val := fun i => ⟨v.val i, Submodule.subset_span ⟨i,rfl⟩⟩
    have hw : LinearIndependent K w := by
      apply LinearIndependent.of_comp W.val.subtype
      exact v.property
    exact ⟨⟨W,⟨w,hw⟩⟩, rfl⟩

/-- Number of ordered independent pairs over a finite field. -/
theorem twoFrame_card {K V : Type*} [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [Finite V] (hV : 2 ≤ Module.finrank K V) :
    Nat.card (TwoFrame K V) =
      (Fintype.card K ^ Module.finrank K V - 1) *
      (Fintype.card K ^ Module.finrank K V - Fintype.card K) := by
  rw [card_linearIndependent hV]
  simp [Fin.prod_univ_two]

/-- Counting independent pairs by their unique two-dimensional span. -/
theorem twoSubspace_card_mul {K V : Type*} [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [Finite V] (hV : 2 ≤ Module.finrank K V) :
    Nat.card (TwoSubspace K V) *
      ((Fintype.card K ^ 2 - 1) * (Fintype.card K ^ 2 - Fintype.card K)) =
      (Fintype.card K ^ Module.finrank K V - 1) *
        (Fintype.card K ^ Module.finrank K V - Fintype.card K) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  have : Finite (Submodule K V) := Finite.of_injective (fun W : Submodule K V => (W : Set V)) SetLike.coe_injective
  let : Fintype (TwoSubspace K V) := Fintype.ofFinite _
  have heq := Nat.card_congr (Equiv.ofBijective
    (frameInSubspaceToFrame (K := K) (V := V)) frameInSubspaceToFrame_bijective)
  rw [Nat.card_sigma, twoFrame_card hV] at heq
  have hlocal (W : TwoSubspace K V) : Nat.card (TwoFrame K W.val) =
      (Fintype.card K ^ 2 - 1) * (Fintype.card K ^ 2 - Fintype.card K) := by
    rw [twoFrame_card (by rw [W.property]), W.property]
  simpa only [hlocal, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Nat.card_eq_fintype_card] using heq

/-- Taking the dual annihilator identifies codimension-two subspaces with
 two-dimensional subspaces of the dual vector space. -/
def codimTwoEquivDualTwo (K : Type*) [Field K] (m : ℕ) :
    CodimTwo K m ≃ TwoSubspace K (Module.Dual K (Fin m → K)) where
  toFun W := ⟨W.val.dualAnnihilator, by
    have h := Subspace.finrank_add_finrank_dualAnnihilator_eq W.val
    have hW := W.property
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    omega⟩
  invFun W := ⟨W.val.dualCoannihilator, by
    have h := Subspace.finrank_add_finrank_dualCoannihilator_eq W.val
    have hW := W.property
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    omega⟩
  left_inv W := Subtype.ext Subspace.dualAnnihilator_dualCoannihilator_eq
  right_inv W := Subtype.ext Subspace.dualCoannihilator_dualAnnihilator_eq

/-- Exact Grassmannian cardinality with its denominator cleared. -/
theorem codimTwo_card_mul (K : Type*) [Field K] [Fintype K]
    (m : ℕ) (hm : 2 ≤ m) :
    Nat.card (CodimTwo K m) *
      ((Fintype.card K ^ 2 - 1) * (Fintype.card K ^ 2 - Fintype.card K)) =
      (Fintype.card K ^ m - 1) * (Fintype.card K ^ m - Fintype.card K) := by
  have : Finite (Module.Dual K (Fin m → K)) :=
    Finite.of_injective (fun f : Module.Dual K (Fin m → K) => (f : (Fin m → K) → K)) DFunLike.coe_injective
  rw [Nat.card_congr (codimTwoEquivDualTwo K m)]
  simpa only [Subspace.dual_finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
    twoSubspace_card_mul (K := K) (V := Module.Dual K (Fin m → K))
      (by simpa only [Subspace.dual_finrank_eq, Module.finrank_fintype_fun_eq_card,
        Fintype.card_fin] using hm)

/-- The usual quotient formula for the number of codimension-two subspaces. -/
theorem codimTwo_card (K : Type*) [Field K] [Fintype K]
    (m : ℕ) (hm : 2 ≤ m) :
    Nat.card (CodimTwo K m) =
      ((Fintype.card K ^ m - 1) * (Fintype.card K ^ m - Fintype.card K)) /
        ((Fintype.card K ^ 2 - 1) * (Fintype.card K ^ 2 - Fintype.card K)) := by
  have hQ : 1 < Fintype.card K := Fintype.one_lt_card
  have hQ2 : Fintype.card K < Fintype.card K ^ 2 := by nlinarith
  have hden : 0 < (Fintype.card K ^ 2 - 1) *
      (Fintype.card K ^ 2 - Fintype.card K) := Nat.mul_pos (by omega) (by omega)
  rw [← codimTwo_card_mul K m hm, Nat.mul_div_cancel _ hden]

/-- The actual number of incidence rows in the paper's `PG(4,512)` specialization. -/
theorem codimTwo_card_512_five (K : Type*) [Field K] [Fintype K]
    (hK : Fintype.card K = 512) :
    Nat.card (CodimTwo K 5) = 18049720589484545 := by
  rw [codimTwo_card K 5 (by omega), hK]
  norm_num

end OneAndAHalfJohnson.Geometry
