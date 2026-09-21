module

public import OneAndAHalfJohnson.FieldSizing
public import OneAndAHalfJohnson.IncidenceRankBound
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Actual field extensions and polynomial ambient sizes

For every output field F of order p^s, the gcd choice produces a concrete
extension of bounded degree r≤2a and cardinality (p^a)^(2m), where
m=s/gcd(s,2a). The actual extended incidence code has dimension polynomial in s
and the corresponding cardinality bound needed for uniform amplification.
-/

@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson

/-- The gcd-selected extension degree is positive. -/
theorem gcd_extension_degree_pos (a s : ℕ) (ha : 0 < a) (hs : 0 < s) :
    0 < 2 * a / Nat.gcd s (2 * a) := by
  apply Nat.div_pos
  · exact Nat.gcd_le_right s (by omega)
  · exact Nat.gcd_pos_of_pos_left _ hs

/-- The actual finite extension realizing the gcd-based field-size choice. -/
def SizedExtension (F : Type) [Field F] [Fintype F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (a s : ℕ) (ha : 0 < a) (hs : 0 < s) : Type :=
  let : NeZero (2 * a / Nat.gcd s (2 * a)) := ⟨(gcd_extension_degree_pos a s ha hs).ne'⟩
  FiniteField.Extension F p (2 * a / Nat.gcd s (2 * a))
  deriving Field, Finite, Algebra (ZMod p)

/-- The constructed field carries its actual algebra structure over F. -/
instance sizedExtensionAlgebra (F : Type) [Field F] [Fintype F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (a s : ℕ) (ha : 0 < a) (hs : 0 < s) : Algebra F (SizedExtension F p a s ha hs) := by
  let : NeZero (2 * a / Nat.gcd s (2 * a)) := ⟨(gcd_extension_degree_pos a s ha hs).ne'⟩
  exact inferInstanceAs (Algebra F (FiniteField.Extension F p (2 * a / Nat.gcd s (2 * a))))

/-- The constructed algebra is finite-dimensional over F. -/
instance sizedExtensionFiniteDimensional (F : Type) [Field F] [Fintype F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (a s : ℕ) (ha : 0 < a) (hs : 0 < s) : FiniteDimensional F (SizedExtension F p a s ha hs) :=
  Module.Finite.of_finite

/-- Degree of the constructed extension over the chosen output field. -/
theorem sizedExtension_finrank (F : Type) [Field F] [Fintype F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (a s : ℕ) (ha : 0 < a) (hs : 0 < s) :
    Module.finrank F (SizedExtension F p a s ha hs) = 2 * a / Nat.gcd s (2 * a) := by
  let : NeZero (2 * a / Nat.gcd s (2 * a)) := ⟨(gcd_extension_degree_pos a s ha hs).ne'⟩
  exact FiniteField.finrank_extension F p _

/-- Exact compatible cardinality of the constructed extension. -/
theorem sizedExtension_card (F : Type) [Field F] [Fintype F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (a s : ℕ) (ha : 0 < a) (hs : 0 < s) (hF : Fintype.card F = p ^ s) :
    Nat.card (SizedExtension F p a s ha hs) =
      (p ^ a) ^ (2 * (s / Nat.gcd s (2 * a))) := by
  let : NeZero (2 * a / Nat.gcd s (2 * a)) := ⟨(gcd_extension_degree_pos a s ha hs).ne'⟩
  rw [SizedExtension, FiniteField.natCard_extension, Nat.card_eq_fintype_card, hF]
  exact (gcd_extension_field_size p a s hs).symm

/-- The same extension has the expected output-field-power cardinality. -/
theorem sizedExtension_card_output_power (F : Type) [Field F] [Fintype F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (a s : ℕ) (ha : 0 < a) (hs : 0 < s) (hF : Fintype.card F = p ^ s) :
    Nat.card (SizedExtension F p a s ha hs) =
      (p ^ s) ^ (2 * a / Nat.gcd s (2 * a)) := by
  rw [sizedExtension_card F p a s ha hs hF, gcd_extension_field_size p a s hs]

/-- An instance-ready existential version, accepting only the output field's
cardinality rather than an additional characteristic premise. -/
theorem exists_sized_field_tower (F : Type) [Field F] [Fintype F]
    (p : ℕ) [Fact p.Prime] (a s : ℕ) (ha : 0 < a) (hs : 0 < s)
    (hF : Fintype.card F = p ^ s) :
    ∃ (E : Type) (_ : Field E) (_ : Fintype E) (_ : Algebra F E) (_ : Algebra (ZMod p) E),
      Module.finrank F E = 2 * a / Nat.gcd s (2 * a) ∧
      Fintype.card E = (p ^ a) ^ (2 * (s / Nat.gcd s (2 * a))) ∧
      Fintype.card E = (p ^ s) ^ (2 * a / Nat.gcd s (2 * a)) := by
  let : CharP F p := charP_of_card_eq_prime_pow hF
  let E := SizedExtension F p a s ha hs
  let : Fintype E := Fintype.ofFinite E
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · exact sizedExtension_finrank F p a s ha hs
  · simpa only [Nat.card_eq_fintype_card] using sizedExtension_card F p a s ha hs hF
  · simpa only [Nat.card_eq_fintype_card] using sizedExtension_card_output_power F p a s ha hs hF

/-- The extension degree is bounded by a constant chosen before s and F. -/
theorem sizedExtension_finrank_le (F : Type) [Field F] [Fintype F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (a s : ℕ) (ha : 0 < a) (hs : 0 < s) :
    Module.finrank F (SizedExtension F p a s ha hs) ≤ 2 * a := by
  rw [sizedExtension_finrank]
  exact gcd_extension_degree_le a s

/-- Replace the base dimension m≤s by a uniform polynomial in the field exponent. -/
theorem polynomial_dimension_bound_in_exponent (m s d : ℕ) (hs : 0 < s) (hm : m ≤ s) :
    (m + 1) ^ d ≤ 2 ^ d * s ^ d := by
  rw [← mul_pow]
  exact Nat.pow_le_pow_left (by omega) d

/-- The actual scalar-extended prime incidence code has a uniform polynomial
bound in s, including the gcd-selected base dimension. -/
theorem extended_incidence_dimension_bound_in_exponent
    (p : ℕ) [Fact p.Prime] (K E : Type*) [Field K] [Fintype K] [CharP K p]
    [Field E] [Algebra (ZMod p) E] (m s : ℕ) (hs : 0 < s) (hm : m ≤ s) :
    Module.finrank E (extendCode (K := E) (Geometry.incidenceSpan K (ZMod p) m)) ≤
      2 ^ (2 * (Fintype.card K - 1)) * s ^ (2 * (Fintype.card K - 1)) := by
  rw [finrank_extendCode]
  exact (Geometry.prime_incidenceSpan_finrank_le_polynomial p K m).trans
    (polynomial_dimension_bound_in_exponent m s _ hs hm)

/-- Cardinality bound for the actual ambient incidence code, ready to use as
the finite family in the simultaneous amplification estimate. -/
theorem extended_incidence_card_bound_in_exponent
    (p : ℕ) [Fact p.Prime] (K E : Type*) [Field K] [Fintype K] [CharP K p]
    [Field E] [Fintype E] [Algebra (ZMod p) E]
    (m s r : ℕ) (hs : 0 < s) (hm : m ≤ s) (hE : Fintype.card E = (p ^ s) ^ r) :
    Nat.card (extendCode (K := E) (Geometry.incidenceSpan K (ZMod p) m)) ≤
      (p ^ s) ^ (r * (2 ^ (2 * (Fintype.card K - 1)) * s ^ (2 * (Fintype.card K - 1)))) := by
  rw [Module.natCard_eq_pow_finrank (K := E), Nat.card_eq_fintype_card, hE, ← pow_mul]
  apply Nat.pow_le_pow_right
  · exact Nat.pow_pos (Fact.out : p.Prime).pos
  · exact Nat.mul_le_mul_left r
      (extended_incidence_dimension_bound_in_exponent p K E m s hs hm)

end OneAndAHalfJohnson
