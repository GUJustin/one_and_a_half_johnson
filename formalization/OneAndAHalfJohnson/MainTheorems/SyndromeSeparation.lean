module

public import OneAndAHalfJohnson.SyndromeConstruction
public import Mathlib.FieldTheory.Finite.Extension

/-!
# Main theorem: separating syndrome map (Lemma 3.5)

This proves `Targets.SyndromeSeparation`, corresponding to Lemma 3.5 on
pp. 10–11 of ePrint 2026/1894. Every codimension-two incidence vector in the
actual scalar-extended incidence code has a nonzero syndrome, and every two
distinct such vectors have linearly independent syndromes.

The proof constructs the intermediate field of order Q^m, embeds it into the
specified syndrome field of order Q^(2m), and chooses a scalar outside that
intermediate field. The explicit moment map and all subspace-polynomial facts
are proved in supporting modules. Neither AD21 nor Hamada is assumed here. The reusable ambient theorem also
proves that every first syndrome coordinate is nonzero, and needs only `Q > 2`;
the original paper-facing statement is a restriction of this stronger result.
-/

@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson.MainTheorems

/-- Construct a whole-ambient syndrome map whose incidence syndromes have
nonzero first coordinates and pairwise independent directions. This strengthened
form of Lemma 3.5 is reusable by the kernel and source-word constructions. -/
theorem exists_ambient_syndrome_first_nonzero (p : ℕ) [Fact p.Prime]
    (K : Type) [Field K] [Fintype K] [CharP K p]
    (a : ℕ) (hK : Fintype.card K = p ^ a) (hQ : 2 < Fintype.card K)
    (m : ℕ) (hm : 4 ≤ m) (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E]
    (hE : Fintype.card E = Fintype.card K ^ (2 * m)) :
    ∃ ψ : (Geometry.Point K m → E) →ₗ[E] (E × E),
      (∀ W : Geometry.CodimTwo K m, (ψ (Geometry.incidenceWord E W)).1 ≠ 0) ∧
      ∀ W T : Geometry.CodimTwo K m, W ≠ T →
        LinearIndependent E ![ψ (Geometry.incidenceWord E W), ψ (Geometry.incidenceWord E T)] := by
  classical

  -- Stage 1: construct the intermediate extension of dimension m.
  let : NeZero m := ⟨by omega⟩
  let : Algebra (ZMod p) K := ZMod.algebra K p
  let V := FiniteField.Extension K p m
  let : Fintype V := Fintype.ofFinite V
  have hdimK : Module.finrank (ZMod p) K = a := by
    apply Nat.pow_right_injective (Fact.out : p.Prime).two_le
    exact (FiniteField.pow_finrank_eq_card p K).trans hK
  have hdimE : Module.finrank (ZMod p) E = a * (2 * m) := by
    apply Nat.pow_right_injective (Fact.out : p.Prime).two_le
    change p ^ Module.finrank (ZMod p) E = p ^ (a * (2 * m))
    rw [FiniteField.pow_finrank_eq_card p E, hE, hK]
    simp only [pow_mul]
  have hdimV : Module.finrank (ZMod p) V = a * m := by
    rw [FiniteField.finrank_zmod_extension, hdimK]
  have hdiv : Module.finrank (ZMod p) V ∣ Module.finrank (ZMod p) E := by
    rw [hdimV, hdimE]
    exact ⟨2, by ring⟩
  obtain ⟨f⟩ := FiniteField.nonempty_algHom_of_finrank_dvd
    (F := ZMod p) (K := V) (L := E) hdiv
  let : Algebra V E := f.toAlgebra

  -- Stage 2: choose coordinates and a scalar outside the intermediate field.
  have hdim : Module.finrank K V = m := FiniteField.finrank_extension K p m
  let Φ : (Fin m → K) ≃ₗ[K] V := LinearEquiv.ofFinrankEq _ _ (by
    rw [hdim, Module.finrank_fintype_fun_eq_card, Fintype.card_fin])
  have hcardV : Fintype.card V = Fintype.card K ^ m := by
    simpa only [Nat.card_eq_fintype_card] using FiniteField.natCard_extension K p m
  have hsmall : Fintype.card V < Fintype.card E := by
    rw [hcardV, hE]
    exact Nat.pow_lt_pow_right Fintype.one_lt_card (by omega)
  have hns : ¬ Function.Surjective (algebraMap V E) := by
    intro hs
    exact (not_le_of_gt hsmall) (Fintype.card_le_of_surjective (algebraMap V E) hs)
  have hex : ∃ β : E, β ∉ Set.range (algebraMap V E) := by
    by_contra h
    apply hns
    intro y
    have hy : y ∈ Set.range (algebraMap V E) := by
      by_contra hn
      exact h ⟨y, hn⟩
    exact hy
  obtain ⟨β, hβ⟩ := hex

  -- Stage 3: retain the whole-ambient map and its stronger first-coordinate property.
  refine ⟨SyndromeConstruction.syndromeMap Φ β, ?_, ?_⟩
  · exact SyndromeConstruction.syndromeMap_incidence_fst_ne_zero Φ β hm hQ
  · exact SyndromeConstruction.syndromeMap_incidence_pair_independent Φ β hβ hm hQ

/-- Full finite-field statement of Lemma 3.5, obtained by restricting the
strengthened ambient construction to the actual scalar-extended incidence code. -/
theorem syndromeSeparation (p : ℕ) [Fact p.Prime] : Targets.SyndromeSeparation p := by
  classical
  intro K _ _ _ a hK hQ _ _ m hm E _ _ _ hE
  obtain ⟨ψ,hfirst,hpair⟩ := exists_ambient_syndrome_first_nonzero p K a hK (by omega) m hm E hE
  let D := extendCode (K := E) (Geometry.incidenceSpan K (ZMod p) m)
  let ψD := ψ.comp D.subtype
  have he (W : Geometry.CodimTwo K m) : ψD (Targets.extendedIncidence W) =
      ψ (Geometry.incidenceWord E W) := by
    change ψ (embedWord (Geometry.incidenceWord (ZMod p) W)) = _
    congr 1
    funext P
    simp [embedWord, Geometry.incidenceWord]
  refine ⟨ψD, ?_, ?_⟩
  · intro W hzero
    rw [he] at hzero
    exact hfirst W (congrArg Prod.fst hzero)
  · intro W T hWT
    rw [he, he]
    exact hpair W T hWT

end OneAndAHalfJohnson.MainTheorems
