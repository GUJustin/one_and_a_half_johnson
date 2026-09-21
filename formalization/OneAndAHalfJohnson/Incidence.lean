module

public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Private coordinates and incidence independence

Generic support-isolation ingredients for the proof of Lemma 3.4 of ePrint
2026/1894. These results do not construct projective subspaces or prove their
intersection bounds. In particular, no numbered result of the paper is claimed
complete here.
-/

@[expose] public section

namespace OneAndAHalfJohnson

/-- A family of coordinate vectors is independent if each vector has a nonzero
coordinate at which every other vector vanishes. No finiteness of the family
or coordinate space is necessary. -/
theorem linearIndependent_of_private_coordinates
    {F I J : Type*} [Field F] (u : J → I → F)
    (h : ∀ j, ∃ i, u j i ≠ 0 ∧ ∀ k, k ≠ j → u k i = 0) :
    LinearIndependent F u := by
  classical
  rw [linearIndependent_iff']
  intro s c hc j hj
  obtain ⟨i, hji, hi⟩ := h j
  have he := congrFun hc i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at he
  rw [Finset.sum_eq_single j] at he
  · exact (mul_eq_zero.mp he).resolve_right hji
  · intro k hk hkj
    simp [hi k hkj]
  · exact fun hj' => (hj' hj).elim

/-- If the total overlap with the other sets is smaller than one set, that set
has a point belonging to none of the others. The strict comparison is essential. -/
theorem exists_private_point_of_overlap_sum_lt
    {I J : Type*} [DecidableEq I] [DecidableEq J] [Fintype J]
    (S : J → Finset I) (j : J)
    (h : ∑ k ∈ Finset.univ.erase j, (S j ∩ S k).card < (S j).card) :
    ∃ i ∈ S j, ∀ k, k ≠ j → i ∉ S k := by
  have hc : ((Finset.univ.erase j).biUnion (fun k => S j ∩ S k)).card <
      (S j).card := lt_of_le_of_lt Finset.card_biUnion_le h
  obtain ⟨i, hij, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  refine ⟨i, hij, ?_⟩
  intro k hkj hik
  apply hi
  exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ k⟩,
    Finset.mem_inter.mpr ⟨hij, hik⟩⟩

/-- Incidence vectors are independent under the strict sum-of-overlaps bound.
Finite-geometry applications must separately prove the stated bound. -/
theorem incidence_linearIndependent_of_overlap_sum_lt
    {F I J : Type*} [Field F] [DecidableEq I] [DecidableEq J] [Fintype J]
    (S : J → Finset I)
    (h : ∀ j, ∑ k ∈ Finset.univ.erase j, (S j ∩ S k).card < (S j).card) :
    LinearIndependent F (fun j i => if i ∈ S j then (1 : F) else 0) := by
  apply linearIndependent_of_private_coordinates
  intro j
  obtain ⟨i, hi, hk⟩ := exists_private_point_of_overlap_sum_lt S j (h j)
  refine ⟨i, by simp [hi], ?_⟩
  intro k hkj
  simp [hk k hkj]

end OneAndAHalfJohnson
