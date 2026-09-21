module

public import OneAndAHalfJohnson.BaseConstruction
public import OneAndAHalfJohnson.BaseCardinality
public import OneAndAHalfJohnson.MainTheorems.SyndromeSeparation
public import OneAndAHalfJohnson.CoordinateTransport
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Main theorem: the small-distance base construction (Lemma 3.2)

The geometric code is assembled from the proved shortening classification,
separating syndrome construction, and a concrete three-incidence kernel word.
Only the explicitly permitted AD21 low-weight classification is an assumption.
-/

@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson.MainTheorems
open Geometry Targets BaseConstruction

/-- The complete geometric base code before reindexing its projective
coordinates by a consecutive finite index set. -/
theorem point_base_of_AD21
    (p : ℕ) [Fact p.Prime] (hAD : AD21LowWeight p)
    (K : Type) [Field K] [Fintype K] [CharP K p]
    (a : ℕ) (hK : Fintype.card K = p ^ a)
    (hQ : 32 < Fintype.card K) (h49 : Fintype.card K ≠ 49) (h121 : Fintype.card K ≠ 121)
    (m : ℕ) (hm : 4 ≤ m)
    (E : Type) [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
    (hE : Fintype.card E = Fintype.card K ^ (2 * m)) :
    ∃ (C : Submodule E (Point K m → E)) (f g : Point K m → E),
      C ≤ extendCode (K := E) (incidenceSpan K (ZMod p) m) ∧
      f ∈ extendCode (K := E) (incidenceSpan K (ZMod p) m) ∧
      g ∈ extendCode (K := E) (incidenceSpan K (ZMod p) m) ∧
      C ≠ ⊥ ∧
      lowWeightCutoff (Fintype.card K) m < Code.dist (C : Set (Point K m → E)) ∧
      Code.dist (C : Set (Point K m → E)) < 3 * incidenceWeight (Fintype.card K) m ∧
      Far C f (4 * (incidenceWeight (Fintype.card K) m : ℝ) /
        (3 * Fintype.card (Point K m))) ∧
      Far C g (4 * (incidenceWeight (Fintype.card K) m : ℝ) /
        (3 * Fintype.card (Point K m))) ∧
      Nat.card (CodimTwo K m) ≤
        (exceptional C f g ((incidenceWeight (Fintype.card K) m : ℝ) /
          Fintype.card (Point K m))).card := by
  classical
  let : Fintype (CodimTwo K m) := Fintype.ofFinite _
  let D := extendCode (K := E) (incidenceSpan K (ZMod p) m)
  let u := incidenceWord E (K := K) (m := m)
  have hu (W : CodimTwo K m) : u W ∈ D := incidenceWord_mem_extendCode (k := ZMod p) W
  obtain ⟨ψ, hfirst, hind⟩ := exists_ambient_syndrome_first_nonzero p K a hK (by omega) m hm E hE
  have hn (W : CodimTwo K m) : ψ (u W) ≠ 0 := by
    intro hz
    apply hfirst W
    exact congrArg Prod.fst hz
  have hpair : tripleSpace K hm 0 ≠ tripleSpace K hm 1 := by
    intro h
    have hh := tripleSpace_injective K hm h
    norm_num at hh
  have hsurj := surjective_restriction_of_pair D ψ
    (u (tripleSpace K hm 0)) (u (tripleSpace K hm 1))
    (hu _) (hu _) (hind _ _ hpair)
  let z : CodimTwo K m → E := fun W => (ψ (u W)).2 / (ψ (u W)).1
  have hcount : Fintype.card (CodimTwo K m) < Fintype.card E := by
    rw [hE, ← Nat.card_eq_fintype_card]
    exact codimTwo_card_lt_syndrome_card K m hm
  obtain ⟨c, hc⟩ := exists_unused_slope z hcount
  obtain ⟨f, hf⟩ := hsurj (1, c)
  obtain ⟨g, hg⟩ := hsurj (0, 1)
  let C := D ⊓ LinearMap.ker ψ
  have hQnat : 32 < Nat.card K := by simpa only [Nat.card_eq_fintype_card] using hQ
  obtain ⟨w, hwC, hw0, _⟩ := exists_small_extended_incidence_kernel_word
    (k := ZMod p) hm hQnat ψ
  have hC : C ≠ ⊥ := by
    intro h
    have hw : w ∈ C := hwC
    rw [h] at hw
    exact hw0 hw
  have hdist : lowWeightCutoff (Fintype.card K) m < Code.dist (C : Set (Point K m → E)) := by
    apply syndrome_kernel_distance_gt D ψ _ ⟨w, hwC, hw0⟩
    intro v hv hv0 hvwt
    obtain ⟨W, T, hspan⟩ := extended_small_word_pair
      p hAD K a hK hQ h49 h121 m hm E v hv hvwt
    exact pair_span_kernel_exclusion u ψ hn hind W T v hspan hv0
  have hdistUpper : Code.dist (C : Set (Point K m → E)) < 3 * incidenceWeight (Fintype.card K) m := by
    simpa only [C, D, Submodule.coe_inf, Set.inf_eq_inter, incidenceWeight, Nat.card_eq_fintype_card] using
      extended_incidence_kernel_distance_lt_three_weight (k := ZMod p) hm hQnat ψ
  have hpoint : Nonempty (Point K m) := by
    refine ⟨Projectivization.mk K (fun _ : Fin m => (1 : K)) ?_⟩
    intro h
    have hh := congrFun h (⟨0, by omega⟩ : Fin m)
    exact one_ne_zero hh
  let : Nonempty (Point K m) := hpoint
  have hN : (0 : ℝ) < Fintype.card (Point K m) := by exact_mod_cast Fintype.card_pos
  have hτ : (4 * (incidenceWeight (Fintype.card K) m : ℝ) /
      (3 * Fintype.card (Point K m))) * Fintype.card (Point K m) =
        4 * (incidenceWeight (Fintype.card K) m : ℝ) / 3 := by field_simp
  have hfarf : Far C f (4 * (incidenceWeight (Fintype.card K) m : ℝ) /
      (3 * Fintype.card (Point K m))) := by
    apply far_of_syndrome_exclusion D ψ f.property
    intro v hv hwt
    rw [hτ] at hwt
    obtain ⟨W, hspan⟩ := extended_small_word_singleton p hAD K a hK hQ h49 h121 m hm E v hv hwt
    rw [show ψ (f : Point K m → E) = (1, c) from hf]
    apply singleton_syndrome_ne_affine ψ (u W) v c (hfirst W) _ hspan
    intro he
    exact hc ⟨W, he⟩
  have hfarg : Far C g (4 * (incidenceWeight (Fintype.card K) m : ℝ) /
      (3 * Fintype.card (Point K m))) := by
    apply far_of_syndrome_exclusion D ψ g.property
    intro v hv hwt
    rw [hτ] at hwt
    obtain ⟨W, hspan⟩ := extended_small_word_singleton p hAD K a hK hQ h49 h121 m hm E v hv hwt
    rw [show ψ (g : Point K m → E) = (0, 1) from hg]
    exact singleton_syndrome_ne_vertical ψ (u W) v (hfirst W) hspan
  refine ⟨C, f, g, inf_le_left, f.property, g.property, hC, hdist, hdistUpper, hfarf, hfarg, ?_⟩
  rw [Nat.card_eq_fintype_card]
  apply card_exceptional_ge_of_offset_slopes D ψ u hu hfirst hind c f g f.property g.property hf hg
  intro W
  have hnorm : hammingNorm (u W) = incidenceWeight (Fintype.card K) m := by
    simpa only [u, incidenceWeight, Nat.card_eq_fintype_card] using incidence_weight (k := E) W
  rw [hnorm, div_mul_cancel₀ _ (ne_of_gt hN)]

/-- Full Lemma 3.2, conditional only on AD21. The construction works uniformly
for `m ≥ 4`, and one may take the explicit count constant `c_Q = 1/(4Q^4)`.
The conclusion quantifies over every syndrome-field model of the required size. -/
theorem smallDistanceBase_of_AD21 (p : ℕ) [Fact p.Prime]
    (hAD : AD21LowWeight p) : SmallDistanceBase p := by
  classical
  intro a ha hQ h49 h121
  let c : ℝ := 1 / (4 * ((p ^ a : ℕ) : ℝ) ^ 4)
  have hQpos : (0 : ℝ) < (p ^ a : ℕ) := by exact_mod_cast (by omega : 0 < p ^ a)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, 4, le_rfl, ?_⟩
  intro m hm E _ _ _ hE

  -- Stage 1: select the geometry field and identify the syndrome characteristic.
  let : NeZero a := ⟨by omega⟩
  let K := GaloisField p a
  let : Fintype K := Fintype.ofFinite K
  have hK : Fintype.card K = p ^ a := by
    simpa only [Nat.card_eq_fintype_card] using GaloisField.card p (n := a) (by omega)
  let : CharP E p := charP_of_card_eq_prime_pow
    (show Fintype.card E = p ^ (a * (2 * m)) by rw [hE]; simp only [pow_mul])
  let : Algebra (ZMod p) E := ZMod.algebra E p
  have hEK : Fintype.card E = Fintype.card K ^ (2 * m) := by rw [hK]; exact hE

  -- Stage 2: assemble the geometric code with all distance and source guarantees.
  obtain ⟨C, f, g, _, _, _, hC, hlo, hhi, hf, hg, hcount⟩ := point_base_of_AD21
    p hAD K a hK (by rwa [hK]) (by rwa [hK]) (by rwa [hK]) m hm E hEK
  have hpoints : Fintype.card (Point K m) = baseLength (p ^ a) m := by
    simpa only [Nat.card_eq_fintype_card, hK, baseLength] using (point_card (K := K) (m := m))
  have hNnat : 0 < Fintype.card (Point K m) :=
    lt_of_lt_of_le (lt_of_le_of_lt (Nat.zero_le _) hlo) (Code.dist_le_card (C : Set (Point K m → E)))
  have hN : (0 : ℝ) < Fintype.card (Point K m) := by exact_mod_cast hNnat
  have hfrac : c * (Fintype.card E : ℝ) ≤ (Nat.card (CodimTwo K m) : ℝ) := by
    have hh := codimTwo_card_fraction K m hm
    simpa only [hEK, hK, Nat.cast_pow, c] using hh

  -- Stage 3: relabel coordinates and preserve every quantitative condition.
  let e : Point K m ≃ Fin (baseLength (p ^ a) m) := Fintype.equivFinOfCardEq hpoints
  refine ⟨reindexCode e C, reindexWord e f, reindexWord e g, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hz
    apply hC
    change C.map (reindexWord e).toLinearMap = ⊥ at hz
    exact Submodule.map_eq_bot_iff.mp hz
  · rw [reindexCode_relativeDistance, relativeDistance, ← hpoints, ← hK]
    apply (div_lt_div_iff_of_pos_right hN).mpr
    exact_mod_cast hlo
  · rw [reindexCode_relativeDistance, relativeDistance, ← hpoints, ← hK]
    apply (div_lt_div_iff_of_pos_right hN).mpr
    exact_mod_cast hhi
  · rw [reindexCode_far, ← hpoints, ← hK]
    exact hf
  · rw [reindexCode_far, ← hpoints, ← hK]
    exact hg
  · rw [reindexCode_exceptional, ← hpoints, ← hK]
    exact hfrac.trans (by exact_mod_cast hcount)

end OneAndAHalfJohnson.MainTheorems
