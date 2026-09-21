module

public import OneAndAHalfJohnson.Geometry
public import OneAndAHalfJohnson.Targets.External
public import Mathlib.Tactic.Linarith

/-!
# Quantitative geometry bounds for shortening

Exact integer inequalities and nonemptiness of the codimension-two
Grassmannian used when assembling Lemma 3.4. No classification is assumed here.
-/

@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson.Geometry

/-- Codimension-two subspaces exist in every ambient dimension at least two. -/
theorem codimTwo_nonempty (K : Type*) [Field K] (m : ℕ) (hm : 2 ≤ m) :
    Nonempty (CodimTwo K m) := by
  let f : Fin (m - 2) → Fin m := Fin.castLE (Nat.sub_le m 2)
  have hf : Function.Injective f := Fin.castLE_injective _
  let v : Fin (m - 2) → (Fin m → K) := fun i => Pi.basisFun K (Fin m) (f i)
  have hv : LinearIndependent K v := (Pi.basisFun K (Fin m)).linearIndependent.comp f hf
  refine ⟨⟨Submodule.span K (Set.range v), ?_⟩⟩
  rw [finrank_span_eq_card hv, Fintype.card_fin]
  omega

/-- Arithmetic identities for an incidence weight and its codimension-three
intersection bound. -/
theorem incidence_arithmetic (Q m : ℕ) (hQ : 32 < Q) (hm : 4 ≤ m) :
    let e := (Q ^ (m - 2) - 1) / (Q - 1)
    let B := (Q ^ (m - 3) - 1) / (Q - 1)
    let a := Q ^ (m - 3)
    let b := Q ^ (m - 4)
    e = B + a ∧ B * (Q - 1) = a - 1 ∧ a = Q * b ∧ 1 ≤ b := by
  dsimp
  have hQ' : 1 < Q := by omega
  have h1 : m - 2 = (m - 3) + 1 := by omega
  have h2 : m - 3 = (m - 4) + 1 := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Nat.geomSum_eq hQ', ← Nat.geomSum_eq hQ', h1, geom_sum_succ']
    omega
  · rw [← Nat.geomSum_eq hQ']
    exact geom_sum_mul_of_one_le (by omega) _
  · rw [h2, pow_succ']
  · exact Nat.one_le_pow _ _ (by omega)

/-- A shortening at the AD21 cutoff cannot support two genuinely overlapping
pairs of incidence rows. -/
theorem cutoff_add_three_overlap_lt_three_weight (Q m : ℕ) (hQ : 32 < Q) (hm : 4 ≤ m) :
    Targets.lowWeightCutoff Q m + 3 * ((Q ^ (m - 3) - 1) / (Q - 1)) <
      3 * ((Q ^ (m - 2) - 1) / (Q - 1)) := by
  obtain ⟨he, hB, hab, hb⟩ := incidence_arithmetic Q m hQ hm
  unfold Targets.lowWeightCutoff
  have ha : 0 < Q ^ (m - 3) := Nat.pow_pos (by omega)
  omega

/-- Clearing denominators in the strict `4e/3 < 2(e-B)` bound. -/
theorem four_weight_lt_six_difference (Q m : ℕ) (hQ : 32 < Q) (hm : 4 ≤ m) :
    4 * ((Q ^ (m - 2) - 1) / (Q - 1)) <
      6 * (((Q ^ (m - 2) - 1) / (Q - 1)) - ((Q ^ (m - 3) - 1) / (Q - 1))) := by
  obtain ⟨he, hB, hab, hb⟩ := incidence_arithmetic Q m hQ hm
  have hQ1 : Q - 1 ≥ 32 := by omega
  have ha : 1 ≤ Q ^ (m - 3) := Nat.one_le_pow _ _ (by omega)
  have hmul := Nat.mul_le_mul_left ((Q ^ (m - 3) - 1) / (Q - 1)) hQ1
  rw [hB] at hmul
  omega

/-- The one-row shortening threshold lies within the AD21 classification cutoff. -/
theorem four_weight_le_three_cutoff (Q m : ℕ) (hQ : 32 < Q) (hm : 4 ≤ m) :
    4 * ((Q ^ (m - 2) - 1) / (Q - 1)) ≤ 3 * Targets.lowWeightCutoff Q m := by
  obtain ⟨he, hB, hab, hb⟩ := incidence_arithmetic Q m hQ hm
  unfold Targets.lowWeightCutoff
  have hQ1 : Q - 1 ≥ 32 := by omega
  have hmul := Nat.mul_le_mul_left ((Q ^ (m - 3) - 1) / (Q - 1)) hQ1
  have hmul2 := Nat.mul_le_mul_right (Q ^ (m - 4)) (show 33 ≤ Q by omega)
  have hsub : 3 * Q ^ (m - 4) + 1 ≤ 3 * Q ^ (m - 3) := by nlinarith
  omega

end OneAndAHalfJohnson.Geometry
