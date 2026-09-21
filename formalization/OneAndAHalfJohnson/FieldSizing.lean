module

public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Tactic.Ring

/-!
# Compatible extension sizes for every field exponent

The gcd choice in Section 3.2 (p. 13) makes `Q^(2m) = q^r` for every
positive exponent `s`, while bounding `r` by the fixed constant `2a`.
These are integer identities; existence of the corresponding field embeddings
is a separate finite-field obligation.
-/

@[expose] public section
namespace OneAndAHalfJohnson

/-- Exact exponent identity in the gcd-based field-size choice. -/
theorem gcd_extension_exponents (a s : ℕ) (hs : 0 < s) :
    a * (2 * (s / Nat.gcd s (2 * a))) = s * (2 * a / Nat.gcd s (2 * a)) := by
  have hd : 0 < Nat.gcd s (2 * a) := Nat.gcd_pos_of_pos_left _ hs
  have hds := Nat.mul_div_cancel' (Nat.gcd_dvd_left s (2 * a))
  have hda := Nat.mul_div_cancel' (Nat.gcd_dvd_right s (2 * a))
  apply Nat.eq_of_mul_eq_mul_left hd
  calc
    Nat.gcd s (2 * a) * (a * (2 * (s / Nat.gcd s (2 * a)))) =
        (2 * a) * (Nat.gcd s (2 * a) * (s / Nat.gcd s (2 * a))) := by ring
    _ = (2 * a) * s := by rw [hds]
    _ = s * (Nat.gcd s (2 * a) * (2 * a / Nat.gcd s (2 * a))) := by rw [hda]; ring
    _ = Nat.gcd s (2 * a) * (s * (2 * a / Nat.gcd s (2 * a))) := by ring

/-- The base construction's alphabet is an extension of the desired alphabet
with the stated numerical size. -/
theorem gcd_extension_field_size (p a s : ℕ) (hs : 0 < s) :
    (p ^ a) ^ (2 * (s / Nat.gcd s (2 * a))) =
      (p ^ s) ^ (2 * a / Nat.gcd s (2 * a)) := by
  rw [← pow_mul, ← pow_mul, gcd_extension_exponents a s hs]

/-- The extension degree is bounded independently of the growing exponent. -/
theorem gcd_extension_degree_le (a s : ℕ) :
    2 * a / Nat.gcd s (2 * a) ≤ 2 * a := Nat.div_le_self _ _

/-- A uniform lower bound on s suffices for any required base dimension. -/
theorem gcd_base_dimension_ge (a s m₀ : ℕ) (ha : 0 < a) (hs : 0 < s)
    (hlarge : m₀ * (2 * a) ≤ s) :
    m₀ ≤ s / Nat.gcd s (2 * a) := by
  apply (Nat.le_div_iff_mul_le (Nat.gcd_pos_of_pos_left _ hs)).mpr
  exact (Nat.mul_le_mul_left _ (Nat.gcd_le_right s (by omega : 0 < 2 * a))).trans hlarge

end OneAndAHalfJohnson
