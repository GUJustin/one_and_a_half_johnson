module

public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Rat.Floor
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Exact arithmetic for Theorem 4.1

These are kernel-checked arithmetic components of ePrint 2026/1894,
Theorem 4.1 (pp. 15–20). They do not establish the incidence construction,
Hamada's rank formula, concentration bounds, or existence of the claimed code.
All decimal constants are represented by exact rational numbers.
-/

@[expose] public section

namespace OneAndAHalfJohnson.ConcreteArithmetic

/-- Number of projective points for the specialization `Q = 512`, `m = 5`. -/
theorem raw_length : ((512 : ℕ) ^ 5 - 1) / 511 = 68853957121 := by norm_num

/-- Weight of a codimension-two incidence vector in the specialization. -/
theorem incidence_weight : ((512 : ℕ) ^ 3 - 1) / 511 = 262657 := by norm_num

/-- The lower cutoff and upper three-incidence weight used in the paper. -/
theorem distance_cutoffs :
    3 * (512 : ℕ) ^ 2 - 3 * 512 - 1 = 784895 ∧
    784895 + 1 = (784896 : ℕ) ∧ 3 * (512 : ℕ) ^ 2 + 1 = 786433 := by norm_num

/-- Exact evaluation of the Gaussian-binomial expression; its combinatorial
interpretation requires a separate finite-geometry theorem. -/
theorem incidence_count :
    (((512 : ℕ) ^ 5 - 1) * (512 ^ 4 - 1)) /
      ((512 ^ 2 - 1) * (512 - 1)) = 18049720589484545 := by norm_num

/-- The exceptional count exceeds `2^18` times the final block length. -/
theorem exceptional_count_gap :
    (18049720589484545 : ℕ) > 2 ^ 54 ∧
    (2 : ℕ) ^ 54 = 2 ^ 18 * 2 ^ 36 := by norm_num

/-- Two syndrome directions can be left unused at the level of cardinalities. -/
theorem unused_directions_cardinality :
    (18049720589484545 : ℕ) < 2 ^ 128 - 1 := by norm_num

/-- Exact rational verification of the pairwise-syndrome union-bound estimate.
The probability formula and applicability of the union bound are separate. -/
theorem syndrome_union_bound :
    ((18049720589484545 : ℚ) * (18049720589484545 - 1) / 2) *
        ((2 ^ 128 : ℚ)⁻¹ + (2 ^ 128 : ℚ)⁻¹ ^ 2 - (2 ^ 128 : ℚ)⁻¹ ^ 3) <
      48 / 100000000 := by norm_num

/-- Integrality turns the strict `4e/3` bound into the stated cutoff. -/
theorem integral_coset_cutoff (w : ℕ) (hw : (4 : ℚ) * 262657 / 3 < w) :
    350210 ≤ w := by
  have h : (350209 : ℚ) < w := by linarith
  exact_mod_cast h

/-- The completion defect is the ceiling of `(N + 2) / 128`. -/
theorem completion_defect :
    ⌈(((2 : ℚ) ^ 36 + 2) / 128)⌉ = (536870913 : ℤ) ∧
    (536870913 : ℚ) = (2 : ℚ) ^ 36 / 128 + 1 := by norm_num

/-- The shortening exponent at the transition is below the proposed dimension. -/
theorem shortening_transition :
    (12550000 : ℕ) - 784896 + 1 = 11765105 ∧
    (11765105 : ℕ) < 3604584374 := by norm_num

/-- The initial dimension and upper distance bound leave enough completion room. -/
theorem completion_room :
    (5489 / 10000 : ℚ) * 2 ^ 36 - 3604584374 > 536870913 := by norm_num

/-- Exact rate identity from `K = N - d + 1 - h` and `h = N/128 + 1`. -/
theorem completion_rate_identity (d : ℚ) :
    ((2 ^ 36 - d + 1 - 536870913) / 2 ^ 36 : ℚ) =
      1 - d / 2 ^ 36 - 1 / 128 := by ring_nf

/-- Conditional arithmetic implication from the distance interval to the rate
interval. No code with those parameters is asserted here. -/
theorem rate_interval (δ : ℚ)
    (hlo : 4419 / 10000 < δ) (hhi : δ < 4511 / 10000) :
    5410875 / 10000000 < 1 - δ - 1 / 128 ∧
    1 - δ - 1 / 128 < 5502875 / 10000000 := by constructor <;> linarith

/-- The exceptional radius lies strictly below half the claimed minimum distance,
with the claimed additive gap. -/
theorem radius_gap (δ : ℚ) (hδ : 4419 / 10000 < δ) :
    1816 / 10000 < δ / 2 ∧ 3935 / 100000 < δ / 2 - 1816 / 10000 := by
  constructor <;> linarith

/-- The strict separation needed in the supercode coset estimate. -/
theorem coset_completion_separation :
    ((4419 / 10000 - 22945 / 100000) * 2 ^ 36 - 1 : ℚ) >
      (212 / 1000) * 2 ^ 36 := by norm_num

/-- Exact matrix arithmetic in the Hamada-formula specialization. This statement
only evaluates the matrix trace; it does not identify any incidence rank. -/
theorem hamada_matrix_trace :
    Matrix.trace ((!![5, 10; 1, 10] : Matrix (Fin 2) (Fin 2) ℕ) ^ 9) =
      3604584375 := by
  norm_num [pow_succ, Matrix.mul_fin_two, Matrix.trace_fin_two]

end OneAndAHalfJohnson.ConcreteArithmetic
