module

public import OneAndAHalfJohnson.Geometry
public import OneAndAHalfJohnson.Incidence

/-!
# Independence of small geometric incidence families

The support-isolation argument used in Lemma 3.4 of ePrint 2026/1894:
over a geometry field of order greater than 32, any family of at most eight
distinct codimension-two incidence rows is independent over every coefficient
field. This proves that ingredient, not the full shortening classification.
-/

@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson.Geometry

/-- Seven possible overlaps occupy fewer coordinates than a full incidence row. -/
theorem seven_overlap_lt_weight (Q m : ℕ) (hQ : 32 < Q) (hm : 4 ≤ m) :
    7 * ((Q ^ (m - 3) - 1) / (Q - 1)) < (Q ^ (m - 2) - 1) / (Q - 1) := by
  have hQ' : 1 < Q := by omega
  rw [← Nat.geomSum_eq hQ', ← Nat.geomSum_eq hQ']
  have he : m - 2 = (m - 3) + 1 := by omega
  rw [he, geom_sum_succ]
  have h : 7 * (∑ i ∈ Finset.range (m - 3), Q ^ i) ≤
      Q * (∑ i ∈ Finset.range (m - 3), Q ^ i) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- At most eight distinct codimension-two incidence rows are linearly
independent over an arbitrary coefficient field. -/
theorem incidence_rows_independent_of_card_le_eight
    {K k J : Type*} [Field K] [Finite K] [Field k] [Fintype J]
    {m : ℕ} (hQ : 32 < Nat.card K) (hm : 4 ≤ m)
    (W : J → CodimTwo K m) (hW : Function.Injective W) (hJ : Fintype.card J ≤ 8) :
    LinearIndependent k (fun j => incidenceWord k (W j)) := by
  classical
  let S : J → Finset (Point K m) := fun j => Finset.univ.filter (Incident (W j).val)
  have hS (j : J) : (S j).card =
      (Nat.card K ^ (m - 2) - 1) / (Nat.card K - 1) := by
    have hd : Module.finrank K (W j).val = m - 2 := by have := (W j).property; omega
    rw [← hd, ← incident_card (W j).val, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hST (j l : J) (hne : l ≠ j) : (S j ∩ S l).card ≤
      (Nat.card K ^ (m - 3) - 1) / (Nat.card K - 1) := by
    have he : (S j ∩ S l).card =
        Nat.card {P : Point K m // Incident (W j).val P ∧ Incident (W l).val P} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      congr 1
      ext P
      simp [S]
    rw [he]
    exact overlap_card_le (W j) (W l) (fun h => hne (hW h).symm)
  have hsum (j : J) : ∑ l ∈ Finset.univ.erase j, (S j ∩ S l).card < (S j).card := by
    calc
      _ ≤ ∑ _l ∈ Finset.univ.erase j,
          (Nat.card K ^ (m - 3) - 1) / (Nat.card K - 1) :=
        Finset.sum_le_sum (fun l hl => hST j l (Finset.mem_erase.mp hl).1)
      _ ≤ 7 * ((Nat.card K ^ (m - 3) - 1) / (Nat.card K - 1)) := by
        simp only [Finset.sum_const, smul_eq_mul]
        apply Nat.mul_le_mul_right
        simp only [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ]
        omega
      _ < (S j).card := by rw [hS]; exact seven_overlap_lt_weight _ _ hQ hm
  change LinearIndependent k (fun j i => if Incident (W j).val i then (1 : k) else 0)
  simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using
    (incidence_linearIndependent_of_overlap_sum_lt (F := k) S hsum)

/-- Distinct geometric subspaces have distinct incidence vectors, over every
coefficient field. This does not require the cardinality restrictions above. -/
theorem incidenceWord_injective {K k : Type*} [Field K] [Field k] {m : ℕ} :
    Function.Injective (incidenceWord k : CodimTwo K m → Point K m → k) := by
  intro W T h
  apply Subtype.ext
  ext v
  by_cases hv : v = 0
  · simp [hv]
  · rw [← incident_mk_iff W.val v hv, ← incident_mk_iff T.val v hv]
    rw [← incidenceWord_eq_one (k := k) W, ← incidenceWord_eq_one (k := k) T, h]

end OneAndAHalfJohnson.Geometry
