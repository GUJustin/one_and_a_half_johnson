module

public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.InformationTheory.Hamming
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Concrete projective incidence coordinates

Semantics for Section 3.1 of ePrint 2026/1894: coordinates are projective points
(one-dimensional subspaces) of `K^m`, and rows are incidence vectors of
codimension-two subspaces. The geometry field `K` and coefficient field `k` are
separate. Taking `k = ZMod p` gives the paper's prime-field incidence code;
the definitions also allow scalar extensions without changing the point set.

Mathlib's `Projectivization` supplies the point type and point-count theorem.
Its ring-theoretic Grassmannian parametrizes locally free quotients, so here the
finite-dimensional Grassmannian is the direct subtype of submodules satisfying
`finrank + 2 = m`. This avoids truncated subtraction at small dimensions.
The paper uses `m ≥ 4`; definitions and elementary semantics need no such bound.
No classification or syndrome-existence result is asserted in this module.
-/

@[expose] public section
noncomputable section

namespace OneAndAHalfJohnson.Geometry

/-- Projective points of the vector space `K^m`. -/
abbrev Point (K : Type*) [Field K] (m : ℕ) :=
  Projectivization K (Fin m → K)

/-- Finite projective coordinates over a finite geometry field. -/
noncomputable instance pointFintype (K : Type*) [Field K] [Finite K] (m : ℕ) :
    Fintype (Point K m) := Fintype.ofFinite _

/-- Codimension-two vector subspaces, parametrized without truncated subtraction. -/
abbrev CodimTwo (K : Type*) [Field K] (m : ℕ) :=
  {W : Submodule K (Fin m → K) // Module.finrank K W + 2 = m}

variable {K k : Type*} [Field K] [Field k] {m : ℕ}

/-- A projective point lies in a vector subspace when its associated line does. -/
def Incident (W : Submodule K (Fin m → K)) (P : Point K m) : Prop :=
  P.submodule ≤ W

/-- Incidence can be checked using any chosen nonzero representative. -/
theorem incident_iff_rep_mem (W : Submodule K (Fin m → K)) (P : Point K m) :
    Incident W P ↔ P.rep ∈ W := by
  rw [Incident, Projectivization.submodule_eq, Submodule.span_singleton_le_iff_mem]

/-- Incidence of a projective point constructed from a nonzero vector. -/
theorem incident_mk_iff (W : Submodule K (Fin m → K))
    (v : Fin m → K) (hv : v ≠ 0) :
    Incident W (Projectivization.mk K v hv) ↔ v ∈ W := by
  rw [Incident, Projectivization.submodule_mk, Submodule.span_singleton_le_iff_mem]

/-- The `k`-valued incidence vector of a codimension-two subspace. -/
def incidenceWord (k : Type*) [Field k] (W : CodimTwo K m) : Point K m → k := by
  classical
  exact fun P => if Incident W.val P then 1 else 0

/-- Membership gives the unit entry of an incidence vector. -/
theorem incidenceWord_eq_one (W : CodimTwo K m) (P : Point K m) :
    incidenceWord k W P = 1 ↔ Incident W.val P := by
  classical
  simp [incidenceWord]

/-- Support of an incidence vector is precisely its projective point set. -/
theorem incidenceWord_ne_zero (W : CodimTwo K m) (P : Point K m) :
    incidenceWord k W P ≠ 0 ↔ Incident W.val P := by
  classical
  simp [incidenceWord]

/-- Set-level support identity, independent of any enumeration of the points. -/
theorem support_incidenceWord (W : CodimTwo K m) :
    Function.support (incidenceWord k W) = {P | Incident W.val P} := by
  ext P
  exact incidenceWord_ne_zero W P

/-- The ambient incidence code is the coefficient-field span of all rows. -/
def incidenceSpan (K k : Type*) [Field K] [Field k] (m : ℕ) :
    Submodule k (Point K m → k) :=
  Submodule.span k (Set.range (incidenceWord k : CodimTwo K m → Point K m → k))

/-- Each geometric incidence row belongs to the ambient incidence code. -/
theorem incidenceWord_mem_span (W : CodimTwo K m) :
    incidenceWord k W ∈ incidenceSpan K k m :=
  Submodule.subset_span ⟨W, rfl⟩

/-- The exact number of coordinates over a finite geometry field. -/
theorem point_card [Finite K] :
    Nat.card (Point K m) = (Nat.card K ^ m - 1) / (Nat.card K - 1) := by
  rw [Projectivization.card'', Nat.card_fun]
  simp

/-- The same coordinate count as a geometric sum. -/
theorem point_card_sum [Finite K] :
    Nat.card (Point K m) = ∑ i ∈ Finset.range m, Nat.card K ^ i := by
  apply Projectivization.card_of_finrank
  simp [Module.finrank_fintype_fun_eq_card]

/-- Projective points of a submodule identify exactly with incident ambient points. -/
def incidentEquiv (W : Submodule K (Fin m → K)) :
    Projectivization K W ≃ {P : Point K m // Incident W P} := by
  let f : Projectivization K W → {P : Point K m // Incident W P} := fun P =>
    ⟨Projectivization.map W.subtype W.subtype_injective P, by
      induction P using Projectivization.ind with
      | h v hv =>
        rw [Projectivization.map_mk, incident_mk_iff]
        exact v.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro P Q he
    exact Projectivization.map_injective W.subtype W.subtype_injective
      (congrArg Subtype.val he)
  · intro P
    have hr : P.val.rep ∈ W := (incident_iff_rep_mem W P.val).mp P.property
    let v : W := ⟨P.val.rep, hr⟩
    have hv : v ≠ 0 := fun h => P.val.rep_nonzero (congrArg Subtype.val h)
    refine ⟨Projectivization.mk K v hv, ?_⟩
    apply Subtype.ext
    exact Projectivization.mk_rep P.val

/-- Number of incident points in an arbitrary finite-dimensional subspace. -/
theorem incident_card [Finite K] (W : Submodule K (Fin m → K)) :
    Nat.card {P : Point K m // Incident W P} =
      (Nat.card K ^ Module.finrank K W - 1) / (Nat.card K - 1) := by
  rw [← Nat.card_congr (incidentEquiv W), Projectivization.card'']
  let e : W ≃ₗ[K] (Fin (Module.finrank K W) → K) :=
    LinearEquiv.ofFinrankEq _ _ (by simp [Module.finrank_fintype_fun_eq_card])
  rw [Nat.card_congr e.toEquiv, Nat.card_fun]
  simp

/-- Incidence of two subspaces is incidence of their intersection. -/
theorem incident_inf_iff (W T : Submodule K (Fin m → K)) (P : Point K m) :
    Incident (W ⊓ T) P ↔ Incident W P ∧ Incident T P :=
  le_inf_iff

/-- Exact number of coordinates shared by two incidence rows. -/
theorem overlap_card [Finite K] (W T : CodimTwo K m) :
    Nat.card {P : Point K m // Incident W.val P ∧ Incident T.val P} =
      (Nat.card K ^ Module.finrank K ↥(W.val ⊓ T.val) - 1) / (Nat.card K - 1) := by
  simpa only [incident_inf_iff] using incident_card (W.val ⊓ T.val)

/-- The incidence weight is the projective point count in dimension `m-2`.
The dimension equation defining `CodimTwo` already entails `2 ≤ m`. -/
theorem incidence_weight [Finite K] [DecidableEq k] (W : CodimTwo K m) :
    hammingNorm (incidenceWord k W) =
      (Nat.card K ^ (m - 2) - 1) / (Nat.card K - 1) := by
  classical
  have hw : Module.finrank K W.val = m - 2 := by omega
  have he : hammingNorm (incidenceWord k W) =
      Nat.card {P : Point K m // Incident W.val P} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp only [hammingNorm, incidenceWord_ne_zero]
  rw [he, incident_card, hw]

/-- Distinct codimension-two subspaces meet in dimension at most `m-3`. -/
theorem intersection_finrank_le (W T : CodimTwo K m) (hne : W ≠ T) :
    Module.finrank K ↥(W.val ⊓ T.val) ≤ m - 3 := by
  have hd : Module.finrank K W.val = Module.finrank K T.val := by
    have := W.property
    have := T.property
    omega
  have hnle : ¬ W.val ≤ T.val := by
    intro h
    exact hne (Subtype.ext (Submodule.eq_of_le_of_finrank_eq h hd))
  have hlt : W.val ⊓ T.val < W.val := by
    apply lt_of_le_of_ne inf_le_left
    intro h
    exact hnle (h ▸ inf_le_right)
  have hdim := Submodule.finrank_lt_finrank_of_lt hlt
  have := W.property
  omega

/-- The shared projective coordinates of distinct incidence rows satisfy the
usual codimension-three point-count bound. -/
theorem overlap_card_le [Finite K] (W T : CodimTwo K m) (hne : W ≠ T) :
    Nat.card {P : Point K m // Incident W.val P ∧ Incident T.val P} ≤
      (Nat.card K ^ (m - 3) - 1) / (Nat.card K - 1) := by
  rw [overlap_card]
  apply Nat.div_le_div_right
  apply Nat.sub_le_sub_right
  exact Nat.pow_le_pow_right (lt_trans Nat.zero_lt_one Finite.one_lt_card)
    (intersection_finrank_le W T hne)

end OneAndAHalfJohnson.Geometry
