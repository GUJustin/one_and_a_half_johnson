module

public import OneAndAHalfJohnson.Geometry
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.InformationTheory.Hamming
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Permitted external premises: AD21 and Hamada

These concrete propositions name the two external inputs the user explicitly
allows as assumptions in the initial conditional formalization. They are not
axioms, admitted proofs, or assertions that the paper's other results hold.
Future conditional theorems must take these propositions as explicit arguments.

`AD21LowWeight` is precisely the two-incidence-row classification used as
Theorem 3.3 (p. 8) of ePrint 2026/1894. It applies to the prime-field incidence
span, not its extension-field span and not a common containing pair for an
entire shortening; those stronger conclusions still require proof.
`HamadaBinaryRank` is the PG(4, 512) rank-formula specialization used on p. 17.
The arithmetic evaluation of its matrix trace is proved separately.
-/

@[expose] public section
noncomputable section

namespace OneAndAHalfJohnson.Targets

open Geometry

/-- The exact cutoff used for Theorem 3.3. Applications require `4 ≤ m` and
`32 < Q`, so the natural-number subtraction equals the integer expression. -/
def lowWeightCutoff (Q m : ℕ) : ℕ :=
  3 * Q ^ (m - 3) - 3 * Q ^ (m - 4) - 1

/-- Permitted external AD21 classification, stated over the actual incidence
code with prime coefficient field. Zero coefficients and equal subspaces allow
representations using fewer than two rows. -/
def AD21LowWeight (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [CharP K p],
    ∀ a : ℕ, Fintype.card K = p ^ a →
    32 < Fintype.card K → Fintype.card K ≠ 49 → Fintype.card K ≠ 121 →
    ∀ m : ℕ, 4 ≤ m →
    ∀ v : Point K m → ZMod p,
      v ∈ incidenceSpan K (ZMod p) m →
      hammingNorm v ≤ lowWeightCutoff (Fintype.card K) m →
      ∃ (W W' : CodimTwo K m) (a b : ZMod p),
        v = a • incidenceWord (ZMod p) W + b • incidenceWord (ZMod p) W'

/-- Permitted external Hamada rank formula specialized to the actual binary
incidence span of codimension-two subspaces of a five-dimensional space over
a field of order 512. This does not assume a rank for any constructed kernel. -/
def HamadaBinaryRank : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [CharP K 2],
    Fintype.card K = 512 →
    Module.finrank (ZMod 2) (incidenceSpan K (ZMod 2) 5) =
      1 + Matrix.trace ((!![5, 10; 1, 10] : Matrix (Fin 2) (Fin 2) ℕ) ^ 9)

end OneAndAHalfJohnson.Targets
