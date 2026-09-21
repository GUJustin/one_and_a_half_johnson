module
public import OneAndAHalfJohnson.RandomFunctional
public import OneAndAHalfJohnson.SyndromeDirections
public import Mathlib.Tactic.LinearCombination
/-! A finite union of hyperplanes constructs separating syndrome maps whenever
the coefficient field is sufficiently large. This replaces the random two-check
existence argument for the concrete construction. -/
@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson
variable {F V J : Type*} [Field F] [Fintype F] [DecidableEq F]
  [AddCommGroup V] [Module F V] [Fintype (Module.Dual F V)] [Fintype J]

/-- Fewer than q nonzero vectors admit a linear functional nonzero on all of them. -/
theorem exists_functional_nonzero_on_family (u : J → V) (hu : ∀ j, u j ≠ 0)
    (hcard : Fintype.card J < Fintype.card F) :
    ∃ φ : Module.Dual F V, ∀ j, φ (u j) ≠ 0 := by
  classical
  let bad (j : J) := Finset.univ.filter (fun φ : Module.Dual F V => φ (u j) = 0)
  let B := Finset.univ.biUnion bad
  have hB : Fintype.card F * B.card ≤ Fintype.card J * Fintype.card (Module.Dual F V) := by
    calc
      _ ≤ Fintype.card F * ∑ j, (bad j).card :=
        Nat.mul_le_mul_left _ (Finset.card_biUnion_le)
      _ = ∑ j : J, Fintype.card F * (bad j).card := Finset.mul_sum _ _ _
      _ = _ := by
        simp_rw [show ∀ j, Fintype.card F * (bad j).card = Fintype.card (Module.Dual F V) from
          fun j => (dual_evaluation_zero_count (hu j)).symm]
        simp
  have hsmall : B.card < Fintype.card (Module.Dual F V) := by
    have hpos := Fintype.card_pos (α := Module.Dual F V)
    have hstrict := Nat.mul_lt_mul_of_pos_right hcard hpos
    nlinarith
  have hex : ∃ φ : Module.Dual F V, φ ∉ B := by
    by_contra h
    have heq : B = Finset.univ := Finset.eq_univ_iff_forall.mpr (by simpa using h)
    simp [heq] at hsmall
  obtain ⟨φ, hφ⟩ := hex
  refine ⟨φ, ?_⟩
  intro j hj
  apply hφ
  exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, by simp [bad, hj]⟩
omit [Fintype F] [DecidableEq F] in
/-- Nonvertical two-dimensional vectors with distinct slopes are independent. -/
theorem independent_pairs_of_distinct_slopes (a b c d : F) (ha : a ≠ 0) (hc : c ≠ 0)
    (hslope : b / a ≠ d / c) : LinearIndependent F ![(a,b),(c,d)] := by
  rw [linearIndependent_fin2]
  constructor
  · intro hz
    exact hc (congrArg Prod.fst hz)
  · intro r heq
    have h1 : r * c = a := congrArg Prod.fst heq
    have h2 : r * d = b := congrArg Prod.snd heq
    apply hslope
    apply (div_eq_div_iff ha hc).mpr
    linear_combination -c * h2 + d * h1

/-- A field larger than the square of the family size admits two linear checks
with nonzero first coordinates and pairwise independent syndrome directions.
The first check normalizes the rows; the second separates all normalized differences. -/
theorem exists_finite_separating_syndrome (u : J → V) (hu : ∀ j, u j ≠ 0)
    (hind : ∀ i j, i ≠ j → LinearIndependent F ![u i,u j])
    (hcard : Fintype.card J ^ 2 < Fintype.card F) :
    ∃ ψ : V →ₗ[F] (F × F), (∀ j, (ψ (u j)).1 ≠ 0) ∧
      ∀ i j, i ≠ j → LinearIndependent F ![ψ (u i),ψ (u j)] := by
  classical
  have hJ : Fintype.card J < Fintype.card F := by
    by_cases hzero : Fintype.card J = 0
    · rw [hzero]; exact Fintype.card_pos
    · have hp : 1 ≤ Fintype.card J := by omega
      nlinarith
  obtain ⟨φ,hφ⟩ := exists_functional_nonzero_on_family u hu hJ
  let v : J → V := fun j => (φ (u j))⁻¹ • u j
  have hinj : Function.Injective v := by
    intro i j heq
    by_contra hij
    have hz : (φ (u i))⁻¹ • u i + (-(φ (u j))⁻¹) • u j = 0 := by
      simpa only [neg_smul, ← sub_eq_add_neg] using sub_eq_zero.mpr heq
    have hh := (LinearIndependent.pair_iff.mp (hind i j hij)) _ _ hz
    exact (inv_ne_zero (hφ i)) hh.1
  let T := {ij : J × J // ij.1 ≠ ij.2}
  have hT : Fintype.card T < Fintype.card F := by
    have hle : Fintype.card T ≤ Fintype.card (J × J) := Fintype.card_subtype_le _
    simp only [Fintype.card_prod] at hle
    nlinarith
  obtain ⟨χ,hχ⟩ := exists_functional_nonzero_on_family
    (fun ij : T => v ij.val.1 - v ij.val.2)
    (fun ij => sub_ne_zero.mpr (fun he => ij.property (hinj he))) hT
  refine ⟨φ.prod χ, hφ, ?_⟩
  intro i j hij
  change LinearIndependent F ![(φ (u i),χ (u i)),(φ (u j),χ (u j))]
  apply independent_pairs_of_distinct_slopes _ _ _ _ (hφ i) (hφ j)
  apply sub_ne_zero.mp
  have hh := hχ ⟨(i,j),hij⟩
  simpa only [v, map_sub, map_smul, smul_eq_mul, div_eq_mul_inv, mul_comm] using hh

end OneAndAHalfJohnson
