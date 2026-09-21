module
public import OneAndAHalfJohnson.ConcreteSyndrome
public import OneAndAHalfJohnson.BaseConstruction
/-! Concrete geometric base for Section 4. All words live on the actual points
of PG(4,512). The only external inputs are AD21 and Hamada; syndrome existence,
source separation, kernel witnesses, and all numerical bounds are proved. -/
@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson
open Geometry Targets BaseConstruction

/-- Concrete base data, including each exceptional coefficient and its actual
weight-262657 witness. The ambient code is explicitly the scalar extension of
the binary incidence span. -/
theorem concrete_base_of_AD21_Hamada
    (hAD : AD21LowWeight 2) (hH : HamadaBinaryRank)
    (K E : Type) [Field K] [Fintype K] [CharP K 2]
    [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod 2) E]
    (hK : Fintype.card K = 512) (hE : Fintype.card E = 2^128) :
    let D := extendCode (K := E) (incidenceSpan K (ZMod 2) 5)
    ∃ (C : Submodule E (Point K 5 → E)) (f g h₀ : Point K 5 → E)
      (z : CodimTwo K 5 → E) (v : CodimTwo K 5 → Point K 5 → E),
      C ≤ D ∧ f ∈ D ∧ g ∈ D ∧ C ≠ ⊥ ∧
      Module.finrank E C = 3604584374 ∧
      784896 ≤ Code.dist (C : Set (Point K 5 → E)) ∧
      h₀ ∈ C ∧ h₀ ≠ 0 ∧ hammingNorm h₀ ≤ 786433 ∧
      (∀ c ∈ C, 350210 ≤ hammingDist f c) ∧
      (∀ c ∈ C, 350210 ≤ hammingDist g c) ∧
      Function.Injective z ∧
      (∀ W, v W ∈ D ∧ hammingNorm (v W) = 262657 ∧ f + z W • g - v W ∈ C) := by
  classical
  let : Fintype (CodimTwo K 5) := Fintype.ofFinite _
  let D := extendCode (K := E) (incidenceSpan K (ZMod 2) 5)
  let u := incidenceWord E (K := K) (m := 5)
  have hu (W : CodimTwo K 5) : u W ∈ D := incidenceWord_mem_extendCode (k := ZMod 2) W
  obtain ⟨ψ, hfirst, hind⟩ := exists_concrete_separating_syndrome K E hK hE
  have hn (W : CodimTwo K 5) : ψ (u W) ≠ 0 := by
    intro hz
    exact hfirst W (congrArg Prod.fst hz)
  have hpair : tripleSpace K (by omega : 4 ≤ 5) 0 ≠ tripleSpace K (by omega : 4 ≤ 5) 1 := by
    intro he
    have hh := tripleSpace_injective K (by omega : 4 ≤ 5) he
    norm_num at hh
  have hsurj := surjective_restriction_of_pair D ψ
    (u (tripleSpace K (by omega : 4 ≤ 5) 0)) (u (tripleSpace K (by omega : 4 ≤ 5) 1))
    (hu _) (hu _) (hind _ _ hpair)
  let slope : CodimTwo K 5 → E := fun W => (ψ (u W)).2 / (ψ (u W)).1
  have hcount : Fintype.card (CodimTwo K 5) < Fintype.card E := by
    rw [← Nat.card_eq_fintype_card, codimTwo_card_512_five K hK, hE]
    norm_num
  obtain ⟨b, hb⟩ := exists_unused_slope slope hcount
  obtain ⟨f, hf⟩ := hsurj (1,b)
  obtain ⟨g, hg⟩ := hsurj (0,1)
  let C := D ⊓ LinearMap.ker ψ
  have hq : Nat.card K = 512 := by simpa only [Nat.card_eq_fintype_card] using hK
  obtain ⟨w, hw, hw0, hweight⟩ := exists_small_extended_incidence_kernel_word
    (k := ZMod 2) (by omega : 4 ≤ 5) (by omega : 32 < Nat.card K) ψ
  have hC : C ≠ ⊥ := by
    intro he
    have hh : w ∈ C := hw
    rw [he] at hh
    exact hw0 hh
  have hdim : Module.finrank E C = 3604584374 :=
    concrete_kernel_finrank_of_Hamada hH K E hK ψ hsurj
  have hd : lowWeightCutoff (Fintype.card K) 5 < Code.dist (C : Set (Point K 5 → E)) := by
    apply syndrome_kernel_distance_gt D ψ _ ⟨w, hw, hw0⟩
    intro v hv hv0 hvwt
    obtain ⟨W,T,hspan⟩ := extended_small_word_pair 2 hAD K 9
      (by norm_num [hK]) (by omega) (by omega) (by omega) 5 (by omega) E v hv hvwt
    exact pair_span_kernel_exclusion u ψ hn hind W T v hspan hv0
  have hsource (x : D) (hx : ψ x = (1,b) ∨ ψ x = (0,1)) :
      ∀ c ∈ C, 350210 ≤ hammingDist (x : Point K 5 → E) c := by
    intro c hc
    by_contra hdist
    have hnwt : hammingNorm ((x : Point K 5 → E) - c) ≤ 350209 := by
      have he := hammingDist_sub_eq_norm (x : Point K 5 → E) ((x : Point K 5 → E) - c)
      simp only [sub_sub_cancel] at he
      omega
    have hwt : (hammingNorm ((x : Point K 5 → E) - c) : ℝ) ≤
        4 * (incidenceWeight (Fintype.card K) 5 : ℝ) / 3 := by
      norm_num [incidenceWeight, hK]
      have hh : (hammingNorm ((x : Point K 5 → E) - c) : ℝ) ≤ 350209 := by exact_mod_cast hnwt
      linarith
    obtain ⟨W,hspan⟩ := extended_small_word_singleton 2 hAD K 9
      (by norm_num [hK]) (by omega) (by omega) (by omega) 5 (by omega) E
      ((x : Point K 5 → E)-c) (D.sub_mem x.property hc.1) hwt
    have he : ψ ((x : Point K 5 → E)-c) = ψ x := by
      rw [map_sub, show ψ c = 0 from hc.2, sub_zero]
    rcases hx with hx | hx
    · apply singleton_syndrome_ne_affine ψ (u W) _ b (hfirst W) _ hspan (he.trans hx)
      intro hh
      exact hb ⟨W,hh⟩
    · exact singleton_syndrome_ne_vertical ψ (u W) _ (hfirst W) hspan (he.trans hx)
  let z : CodimTwo K 5 → E := fun W => slope W - b
  let v : CodimTwo K 5 → Point K 5 → E := fun W => (ψ (u W)).1⁻¹ • u W
  have hi : Function.Injective slope := slopes_injective_of_pairwise_independent
    (fun W => (ψ (u W)).1) (fun W => (ψ (u W)).2) hfirst (by simpa using hind)
  have hz : Function.Injective z := by
    intro W T he
    apply hi
    exact sub_left_injective he
  refine ⟨C,f,g,w,z,v,inf_le_left,f.property,g.property,hC,hdim,?_,hw,hw0,?_,
    hsource f (Or.inl hf),hsource g (Or.inr hg),hz,?_⟩
  · norm_num [lowWeightCutoff, hK] at hd
    omega
  · norm_num [hq, hK] at hweight
    exact hweight
  · intro W
    have hv : v W ∈ D := D.smul_mem _ (hu W)
    refine ⟨hv, ?_, D.sub_mem (D.add_mem f.property (D.smul_mem _ g.property)) hv, ?_⟩
    · rw [hammingNorm_smul_nonzero _ (inv_ne_zero (hfirst W))]
      simpa [u, hq, hK] using incidence_weight (k := E) W
    · change ψ ((f : Point K 5 → E) + z W • (g : Point K 5 → E) - v W) = 0
      have hvψ := syndrome_normalize ψ (u W) _ _ (hfirst W) rfl
      rw [map_sub, map_add, map_smul, show ψ (f : Point K 5 → E) = (1,b) from hf,
        show ψ (g : Point K 5 → E) = (0,1) from hg, hvψ]
      ext <;> simp [z, slope, u]

end OneAndAHalfJohnson
