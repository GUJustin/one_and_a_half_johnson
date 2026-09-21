module

public import OneAndAHalfJohnson.Geometry
public import OneAndAHalfJohnson.Shortening
public import OneAndAHalfJohnson.GeometryShorteningBounds

/-!
# Three coordinate incidence subspaces

The subspaces with zero coordinates `{0,1}`, `{0,2}`, and `{0,3}` lie in the
same coordinate hyperplane. Their pair and triple intersections give the
explicit small-support kernel witness used in Lemma 3.2 and Theorem 4.1.
-/

@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson.Geometry
open scoped Classical

/-- Coordinate vectors vanishing on the specified finite set. -/
def coordinateKernel (K : Type*) [Field K] {m : ℕ} (A : Finset (Fin m)) :
    Submodule K (Fin m → K) := Pi.spanSubset K (A : Set (Fin m))ᶜ

/-- Membership is vanishing at every excluded coordinate. -/
theorem mem_coordinateKernel (K : Type*) [Field K] {m : ℕ}
    (A : Finset (Fin m)) (v : Fin m → K) :
    v ∈ coordinateKernel K A ↔ ∀ i ∈ A, v i = 0 := by
  simp [coordinateKernel, Pi.mem_spanSubset_iff]

/-- Number of free coordinates in a coordinate kernel. -/
theorem finrank_coordinateKernel (K : Type*) [Field K] {m : ℕ} (A : Finset (Fin m)) :
    Module.finrank K (coordinateKernel K A) = m - A.card := by
  rw [coordinateKernel, Pi.dim_spanSubset]
  rw [Set.ncard_compl (A : Set (Fin m))]
  simp

/-- Intersecting coordinate kernels combines their excluded coordinates. -/
theorem coordinateKernel_inf (K : Type*) [Field K] {m : ℕ} (A B : Finset (Fin m)) :
    coordinateKernel K A ⊓ coordinateKernel K B = coordinateKernel K (A ∪ B) := by
  ext v
  simp only [Submodule.mem_inf, mem_coordinateKernel, Finset.mem_union]
  constructor
  · rintro ⟨hA,hB⟩ i (hi | hi)
    · exact hA i hi
    · exact hB i hi
  · intro h
    exact ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi)⟩

/-- The first-four-coordinate pattern defining each member of the triple. -/
def tripleMask (i : Fin 3) : Finset (Fin 4) := {0, i.succ}

/-- Embed the excluded-coordinate pattern into ambient dimension `m ≥ 4`. -/
def tripleExcluded {m : ℕ} (hm : 4 ≤ m) (i : Fin 3) : Finset (Fin m) :=
  (tripleMask i).map ⟨Fin.castLE hm, Fin.castLE_injective hm⟩

/-- Each triple member excludes exactly two coordinates. -/
theorem tripleExcluded_card {m : ℕ} (hm : 4 ≤ m) (i : Fin 3) :
    (tripleExcluded hm i).card = 2 := by
  rw [tripleExcluded, Finset.card_map]
  simp [tripleMask, Ne.symm (Fin.succ_ne_zero i)]

/-- Two different members jointly exclude three coordinates. -/
theorem tripleExcluded_union_card {m : ℕ} (hm : 4 ≤ m) (i j : Fin 3) (hij : i ≠ j) :
    (tripleExcluded hm i ∪ tripleExcluded hm j).card = 3 := by
  rw [tripleExcluded, tripleExcluded, ← Finset.map_union, Finset.card_map]
  fin_cases i <;> fin_cases j <;> simp_all [tripleMask]

/-- All three members jointly exclude four coordinates. -/
theorem tripleExcluded_union_three_card {m : ℕ} (hm : 4 ≤ m) :
    (tripleExcluded hm 0 ∪ tripleExcluded hm 1 ∪ tripleExcluded hm 2).card = 4 := by
  simp only [tripleExcluded, ← Finset.map_union, Finset.card_map]
  decide

/-- Three concrete codimension-two subspaces. -/
def tripleSpace (K : Type*) [Field K] {m : ℕ} (hm : 4 ≤ m) (i : Fin 3) : CodimTwo K m :=
  ⟨coordinateKernel K (tripleExcluded hm i), by
    rw [finrank_coordinateKernel, tripleExcluded_card]
    omega⟩

/-- All three subspaces lie in the same coordinate hyperplane. -/
theorem tripleSpace_le_common_hyperplane (K : Type*) [Field K] {m : ℕ}
    (hm : 4 ≤ m) (i : Fin 3) :
    (tripleSpace K hm i).val ≤ coordinateKernel K {Fin.castLE hm 0} := by
  intro v hv
  change v ∈ coordinateKernel K (tripleExcluded hm i) at hv
  rw [mem_coordinateKernel] at hv ⊢
  intro j hj
  have hj0 : j = Fin.castLE hm 0 := Finset.mem_singleton.mp hj
  subst j
  apply hv
  exact Finset.mem_map.mpr ⟨0, by simp [tripleMask], rfl⟩

/-- The common containing coordinate subspace is a hyperplane. -/
theorem triple_common_hyperplane_finrank (K : Type*) [Field K] {m : ℕ} (hm : 4 ≤ m) :
    Module.finrank K (coordinateKernel K {Fin.castLE hm 0}) = m - 1 := by
  rw [finrank_coordinateKernel, Finset.card_singleton]

/-- Exact dimension of each pair intersection. -/
theorem tripleSpace_pair_finrank (K : Type*) [Field K] {m : ℕ}
    (hm : 4 ≤ m) (i j : Fin 3) (hij : i ≠ j) :
    Module.finrank K ((tripleSpace K hm i).val ⊓ (tripleSpace K hm j).val : Submodule K (Fin m → K)) = m - 3 := by
  rw [tripleSpace, tripleSpace, coordinateKernel_inf, finrank_coordinateKernel,
    tripleExcluded_union_card hm i j hij]

/-- Exact dimension of the triple intersection. -/
theorem tripleSpace_triple_finrank (K : Type*) [Field K] {m : ℕ} (hm : 4 ≤ m) :
    Module.finrank K ((tripleSpace K hm 0).val ⊓ (tripleSpace K hm 1).val ⊓
      (tripleSpace K hm 2).val : Submodule K (Fin m → K)) = m - 4 := by
  change Module.finrank K (coordinateKernel K (tripleExcluded hm 0) ⊓
    coordinateKernel K (tripleExcluded hm 1) ⊓ coordinateKernel K (tripleExcluded hm 2) :
    Submodule K (Fin m → K)) = m - 4
  rw [coordinateKernel_inf, coordinateKernel_inf, finrank_coordinateKernel,
    tripleExcluded_union_three_card]

/-- These three subspaces are distinct. -/
theorem tripleSpace_injective (K : Type*) [Field K] {m : ℕ} (hm : 4 ≤ m) :
    Function.Injective (tripleSpace K hm) := by
  intro i j heq
  by_contra hij
  have h := tripleSpace_pair_finrank K hm i j hij
  rw [heq, inf_idem] at h
  have hh := (tripleSpace K hm j).property
  omega

/-- Projective coordinates occupied by one of the three incidence rows. -/
def triplePoints (K : Type*) [Field K] [Finite K] {m : ℕ}
    (hm : 4 ≤ m) (i : Fin 3) : Finset (Point K m) := by
  classical
  exact Finset.univ.filter (Incident (tripleSpace K hm i).val)

/-- Weight of each triple row. -/
theorem triplePoints_card (K : Type*) [Field K] [Finite K] {m : ℕ}
    (hm : 4 ≤ m) (i : Fin 3) :
    (triplePoints K hm i).card = (Nat.card K ^ (m - 2) - 1) / (Nat.card K - 1) := by
  classical
  simpa only [triplePoints, hammingNorm, incidenceWord_ne_zero] using
    incidence_weight (k := K) (tripleSpace K hm i)

/-- Pairwise overlap of the three coordinate incidence rows. -/
theorem triplePoints_pair_card (K : Type*) [Field K] [Finite K] {m : ℕ}
    (hm : 4 ≤ m) (i j : Fin 3) (hij : i ≠ j) :
    (triplePoints K hm i ∩ triplePoints K hm j).card =
      (Nat.card K ^ (m - 3) - 1) / (Nat.card K - 1) := by
  classical
  have h := overlap_card (tripleSpace K hm i) (tripleSpace K hm j)
  rw [tripleSpace_pair_finrank K hm i j hij, Nat.card_eq_fintype_card,
    Fintype.card_subtype] at h
  convert h using 2
  ext P
  simp [triplePoints]

/-- Triple overlap of the coordinate incidence rows. -/
theorem triplePoints_triple_card (K : Type*) [Field K] [Finite K] {m : ℕ} (hm : 4 ≤ m) :
    (triplePoints K hm 0 ∩ triplePoints K hm 1 ∩ triplePoints K hm 2).card =
      (Nat.card K ^ (m - 4) - 1) / (Nat.card K - 1) := by
  classical
  have h := incident_card ((tripleSpace K hm 0).val ⊓ (tripleSpace K hm 1).val ⊓
    (tripleSpace K hm 2).val)
  rw [tripleSpace_triple_finrank K hm, Nat.card_eq_fintype_card,
    Fintype.card_subtype] at h
  convert h using 2
  ext P
  simp [triplePoints, incident_inf_iff, and_assoc]

/-- Exact union size with inclusion–exclusion written without natural subtraction. -/
theorem triplePoints_union_card_identity (K : Type*) [Field K] [Finite K]
    {m : ℕ} (hm : 4 ≤ m) :
    (triplePoints K hm 0 ∪ triplePoints K hm 1 ∪ triplePoints K hm 2).card +
      3 * ((Nat.card K ^ (m - 3) - 1) / (Nat.card K - 1)) =
      3 * ((Nat.card K ^ (m - 2) - 1) / (Nat.card K - 1)) +
        (Nat.card K ^ (m - 4) - 1) / (Nat.card K - 1) := by
  classical
  let A := triplePoints K hm 0
  let B := triplePoints K hm 1
  let C := triplePoints K hm 2
  have h1 := three_sets_card_identity A B C
  have h2 := Finset.card_sdiff_add_card_eq_card
    (show A ∩ B ∩ C ⊆ A ∪ B ∪ C by intro P hP; simp_all)
  have hA := triplePoints_card K hm 0
  have hB := triplePoints_card K hm 1
  have hC := triplePoints_card K hm 2
  have hAB := triplePoints_pair_card K hm 0 1 (by decide)
  have hAC := triplePoints_pair_card K hm 0 2 (by decide)
  have hBC := triplePoints_pair_card K hm 1 2 (by decide)
  have hABC := triplePoints_triple_card K hm
  change (A ∪ B ∪ C).card + _ = _
  change A.card = _ at hA
  change B.card = _ at hB
  change C.card = _ at hC
  change (A ∩ B).card = _ at hAB
  change (A ∩ C).card = _ at hAC
  change (B ∩ C).card = _ at hBC
  change (A ∩ B ∩ C).card = _ at hABC
  omega

/-- Convenient closed form for the three-row union used in the paper. -/
theorem triplePoints_union_card (K : Type*) [Field K] [Finite K]
    {m : ℕ} (hm : 4 ≤ m) (hQ : 32 < Nat.card K) :
    (triplePoints K hm 0 ∪ triplePoints K hm 1 ∪ triplePoints K hm 2).card =
      3 * Nat.card K ^ (m - 3) + (Nat.card K ^ (m - 4) - 1) / (Nat.card K - 1) := by
  have h := triplePoints_union_card_identity K hm
  have he := (incidence_arithmetic _ _ hQ hm).1
  omega

/-- The explicit union is strictly smaller than three incidence weights. -/
theorem triplePoints_union_card_lt_three_weight (K : Type*) [Field K] [Finite K]
    {m : ℕ} (hm : 4 ≤ m) (hQ : 32 < Nat.card K) :
    (triplePoints K hm 0 ∪ triplePoints K hm 1 ∪ triplePoints K hm 2).card <
      3 * ((Nat.card K ^ (m - 2) - 1) / (Nat.card K - 1)) := by
  have h := triplePoints_union_card_identity K hm
  have hc : (Nat.card K ^ (m - 4) - 1) / (Nat.card K - 1) ≤
      (Nat.card K ^ (m - 3) - 1) / (Nat.card K - 1) := by
    apply Nat.div_le_div_right
    apply Nat.sub_le_sub_right
    exact Nat.pow_le_pow_right (by omega) (by omega)
  obtain ⟨he,hB,hab,hb⟩ := incidence_arithmetic _ _ hQ hm
  have hBpos : 0 < (Nat.card K ^ (m - 3) - 1) / (Nat.card K - 1) := by
    by_contra hn
    have hz : (Nat.card K ^ (m - 3) - 1) / (Nat.card K - 1) = 0 := by omega
    rw [hz, zero_mul] at hB
    have ha : Nat.card K ^ (m - 3) ≤ 1 := by omega
    nlinarith
  omega

/-- The concrete triple has exactly the support budget used in Theorem 4.1. -/
theorem triplePoints_union_card_512_five (K : Type*) [Field K] [Finite K]
    (hK : Nat.card K = 512) :
    (triplePoints K (m := 5) (by omega) 0 ∪ triplePoints K (m := 5) (by omega) 1 ∪
      triplePoints K (m := 5) (by omega) 2).card = 786433 := by
  rw [triplePoints_union_card K (by omega) (by omega), hK]
  norm_num

end OneAndAHalfJohnson.Geometry
