module

public import OneAndAHalfJohnson.GeometryCardinality

/-!
# Uniform incidence-count bounds

The exact Grassmannian cardinality supplies both an unused syndrome slope
and a positive fraction of all syndrome-field coefficients in Lemma 3.2.
-/

@[expose] public section
namespace OneAndAHalfJohnson.Geometry

/-- The incidence count is strictly below the syndrome-field cardinality. -/
theorem codimTwo_card_lt_syndrome_card (K : Type*) [Field K] [Fintype K]
    (m : ℕ) (hm : 4 ≤ m) : Nat.card (CodimTwo K m) < Fintype.card K ^ (2 * m) := by
  let Q := Fintype.card K
  let X := Q ^ m
  let D := (Q ^ 2 - 1) * (Q ^ 2 - Q)
  have hQ : 1 < Q := Fintype.one_lt_card
  have hX : 0 < X := Nat.pow_pos (by omega)
  have hQ2 : Q < Q ^ 2 := by nlinarith
  have hD : 1 ≤ D := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hp := codimTwo_card_mul K m (by omega)
  change Nat.card (CodimTwo K m) * D = (X - 1) * (X - Q) at hp
  have hb : Nat.card (CodimTwo K m) ≤ Nat.card (CodimTwo K m) * D := by
    simpa using Nat.mul_le_mul_left (Nat.card (CodimTwo K m)) hD
  have hnum : (X - 1) * (X - Q) < X * X := by
    calc
      _ ≤ (X - 1) * X := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ < X * X := Nat.mul_lt_mul_of_pos_right (Nat.sub_lt hX (by omega)) hX
  have he : Fintype.card K ^ (2 * m) = X * X := by
    change Q ^ (2 * m) = Q ^ m * Q ^ m
    rw [two_mul, pow_add]
  rw [he]
  exact lt_of_le_of_lt (hb.trans_eq hp) hnum

/-- A coarse uniform lower bound on the incidence count, with denominator
cleared. This holds already for dimension four. -/
theorem syndrome_card_le_four_mul_count_mul_qpow (K : Type*) [Field K] [Fintype K]
    (m : ℕ) (hm : 4 ≤ m) :
    Fintype.card K ^ (2 * m) ≤ 4 * Nat.card (CodimTwo K m) * Fintype.card K ^ 4 := by
  let Q := Fintype.card K
  let X := Q ^ m
  let D := (Q ^ 2 - 1) * (Q ^ 2 - Q)
  have hQ : 1 < Q := Fintype.one_lt_card
  have hX2 : Q ^ 2 ≤ X := Nat.pow_le_pow_right (by omega) (by omega)
  have hX : 2 * Q ≤ X := by nlinarith
  have h1 : X ≤ 2 * (X - 1) := by omega
  have h2 : X ≤ 2 * (X - Q) := by omega
  have hn := Nat.mul_le_mul h1 h2
  have hD : D ≤ Q ^ 4 := by
    calc
      _ ≤ Q ^ 2 * Q ^ 2 := Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
      _ = Q ^ 4 := by ring
  have hp := codimTwo_card_mul K m (by omega)
  change Nat.card (CodimTwo K m) * D = (X - 1) * (X - Q) at hp
  have hbound := Nat.mul_le_mul_left (4 * Nat.card (CodimTwo K m)) hD
  have he : Fintype.card K ^ (2 * m) = X * X := by
    change Q ^ (2 * m) = Q ^ m * Q ^ m
    rw [two_mul, pow_add]
  rw [he]
  nlinarith

/-- The incidence population is at least `1/(4Q^4)` times the syndrome field. -/
theorem codimTwo_card_fraction (K : Type*) [Field K] [Fintype K]
    (m : ℕ) (hm : 4 ≤ m) :
    (1 / (4 * (Fintype.card K : ℝ) ^ 4)) * (Fintype.card K : ℝ) ^ (2 * m) ≤
      (Nat.card (CodimTwo K m) : ℝ) := by
  have h := syndrome_card_le_four_mul_count_mul_qpow K m hm
  have hcast : (Fintype.card K : ℝ) ^ (2 * m) ≤
      4 * (Nat.card (CodimTwo K m) : ℝ) * (Fintype.card K : ℝ) ^ 4 := by exact_mod_cast h
  have hKpos : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hpos : (0 : ℝ) < 4 * (Fintype.card K : ℝ) ^ 4 := by positivity
  rw [one_div, inv_mul_eq_div]
  apply (div_le_iff₀ hpos).mpr
  nlinarith [hcast]

end OneAndAHalfJohnson.Geometry
