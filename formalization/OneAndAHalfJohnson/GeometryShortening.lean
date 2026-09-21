module

public import OneAndAHalfJohnson.Shortening
public import OneAndAHalfJohnson.GeometryIndependence
public import OneAndAHalfJohnson.GeometryShorteningBounds
public import OneAndAHalfJohnson.Targets.Base
public import OneAndAHalfJohnson.CodeDistance

/-!
# Lemma 3.4, conditional only on the authorized AD21 classification

The proof uses independence of at most six geometric incidence rows to make
small coefficient representations unique. Maximal support among the sparse
representations reduces a common-pair claim to the case of two overlapping
pairs. Their coordinate supports cover the union of three incidence rows
outside the triple overlap; the projective counting bounds exclude that case.
This argument works in characteristic two as well as in odd characteristic.

At the smaller threshold a genuine pair is excluded by its symmetric-difference
support. The resulting common singleton also gives the exact minimum distance.
All three conclusions hold already at dimension four.
-/

@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson
open Geometry Targets

/-- Any chosen member of a two-element finite set can be listed first. -/
theorem pair_eq_of_mem {J : Type*} [DecidableEq J] (T : Finset J)
    (hT : T.card = 2) (i : J) (hi : i ∈ T) : ∃ j, i ≠ j ∧ T = {i,j} := by
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hT
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · exact ⟨b, hab, rfl⟩
  · exact ⟨a, Ne.symm hab, by ext; simp [or_comm]⟩

/-- Six-row local independence in the set-indexed form needed by sparse uniqueness. -/
theorem geometric_six_rows_independent {K k : Type*} [Field K] [Finite K] [Field k]
    {m : ℕ} (hQ : 32 < Nat.card K) (hm : 4 ≤ m)
    (T : Finset (CodimTwo K m)) (hT : T.card ≤ 6) :
    LinearIndepOn k (incidenceWord k) (T : Set (CodimTwo K m)) := by
  classical
  exact incidence_rows_independent_of_card_le_eight hQ hm
    (fun j : T => j.val) (fun _ _ h => Subtype.ext h) (by simpa using (show T.card ≤ 8 by omega))

/-- Three-row-overlap obstruction for the actual finite projective incidence words. -/
theorem geometric_overlapping_pairs_impossible {K k : Type*}
    [Field K] [Fintype K] [Field k] {m : ℕ} [DecidableEq (CodimTwo K m)]
    (hQ : 32 < Fintype.card K) (hm : 4 ≤ m)
    (S : Finset (Point K m)) (hS : S.card ≤ lowWeightCutoff (Fintype.card K) m)
    (x y : CodimTwo K m →₀ k) (hx : x.support.card = 2) (hy : y.support.card = 2)
    (hu : (x.support ∪ y.support).card = 3)
    (hxS : Finsupp.linearCombination k (incidenceWord k) x ∈ supportedCode (S : Set _))
    (hyS : Finsupp.linearCombination k (incidenceWord k) y ∈ supportedCode (S : Set _)) : False := by
  classical
  have hi : (x.support ∩ y.support).Nonempty := by
    rw [← Finset.card_pos]
    have h := Finset.card_union_add_card_inter x.support y.support
    omega
  obtain ⟨i, hi⟩ := hi
  obtain ⟨hix, hiy⟩ := Finset.mem_inter.mp hi
  obtain ⟨j, hij, hxset⟩ := pair_eq_of_mem x.support hx i hix
  obtain ⟨l, hil, hyset⟩ := pair_eq_of_mem y.support hy i hiy
  have hjl : j ≠ l := by
    intro he; subst l
    rw [hxset, hyset, Finset.union_self, Finset.card_pair hij] at hu
    omega
  let A : CodimTwo K m → Finset (Point K m) := fun W => Finset.univ.filter (Incident W.val)
  have hAc (W : CodimTwo K m) : (A W).card =
      (Fintype.card K ^ (m - 2) - 1) / (Fintype.card K - 1) := by
    have h := incidence_weight (k := k) W
    classical
    simpa only [hammingNorm, incidenceWord_ne_zero, Nat.card_eq_fintype_card] using h
  have hAB (W T : CodimTwo K m) (hne : W ≠ T) :
      (A W ∩ A T).card ≤ (Fintype.card K ^ (m - 3) - 1) / (Fintype.card K - 1) := by
    have he : (A W ∩ A T).card =
        Nat.card {P : Point K m // Incident W.val P ∧ Incident T.val P} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      congr 1
      ext P
      simp [A]
    rw [he]
    simpa only [Nat.card_eq_fintype_card] using overlap_card_le W T hne
  have hxeq : Finsupp.linearCombination k (incidenceWord k) x =
      x i • incidenceWord k i + x j • incidenceWord k j := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum, hxset, Finset.sum_pair hij]
  have hyeq : Finsupp.linearCombination k (incidenceWord k) y =
      y i • incidenceWord k i + y l • incidenceWord k l := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum, hyset, Finset.sum_pair hil]
  apply overlapping_pairs_impossible (A i) (A j) (A l) S (x i) (x j) (y i) (y l)
    (Finsupp.mem_support_iff.mp hix)
    (Finsupp.mem_support_iff.mp (by rw [hxset]; simp))
    (Finsupp.mem_support_iff.mp hiy)
    (Finsupp.mem_support_iff.mp (by rw [hyset]; simp))
  · intro P hP
    have h := hxS P hP
    rw [hxeq] at h
    simpa [A, incidenceWord] using h
  · intro P hP
    have h := hyS P hP
    rw [hyeq] at h
    simpa [A, incidenceWord] using h
  · exact hAc i
  · exact hAc j
  · exact hAc l
  · exact hAB i j hij
  · exact hAB i l hil
  · exact hAB j l hjl
  · exact lt_of_le_of_lt (Nat.add_le_add_right hS _)
      (cutoff_add_three_overlap_lt_three_weight _ _ hQ hm)

/-- AD21 supplies a two-sparse coefficient representation of each word in a
shortening at the classification cutoff. -/
theorem shortening_word_sparse (p : ℕ) [Fact p.Prime] (hAD : AD21LowWeight p)
    (K : Type) [Field K] [Fintype K] [CharP K p]
    (a : ℕ) (hcard : Fintype.card K = p ^ a)
    (hQ : 32 < Fintype.card K) (h49 : Fintype.card K ≠ 49) (h121 : Fintype.card K ≠ 121)
    (m : ℕ) (hm : 4 ≤ m) (S : Finset (Point K m))
    (hS : S.card ≤ lowWeightCutoff (Fintype.card K) m)
    (v : Point K m → ZMod p)
    (hv : v ∈ incidenceSpan K (ZMod p) m ⊓ supportedCode (S : Set _)) :
    ∃ z : CodimTwo K m →₀ ZMod p, z.support.card ≤ 2 ∧
      Finsupp.linearCombination (ZMod p) (incidenceWord (ZMod p)) z = v := by
  classical
  have hwt : hammingNorm v ≤ S.card := by
    apply Finset.card_le_card
    intro i hi
    have hi' : v i ≠ 0 := (Finset.mem_filter.mp hi).2
    by_contra hn
    exact hi' (hv.2 i hn)
  obtain ⟨W,T,c,d,hrep⟩ := hAD K a hcard hQ h49 h121 m hm v hv.1 (hwt.trans hS)
  refine ⟨Finsupp.single W c + Finsupp.single T d, ?_, ?_⟩
  · have hsub : (Finsupp.single W c + Finsupp.single T d).support ⊆ {W,T} := by
      intro j hj
      have hj' := Finsupp.support_add hj
      rcases Finset.mem_union.mp hj' with hj' | hj'
      · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp (Finsupp.support_single_subset hj')))
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Finset.mem_singleton.mp (Finsupp.support_single_subset hj'))))
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · simpa only [map_add, Finsupp.linearCombination_single] using hrep.symm

/-- Lemma 3.4, two-incidence conclusion, with the explicit threshold `m ≥ 4`.
Only the external AD21 classification is assumed. The same pair contains every
word of the shortening. -/
theorem shortening_contained_in_two_incidence_rows
    (p : ℕ) [Fact p.Prime] (hAD : AD21LowWeight p)
    (K : Type) [Field K] [Fintype K] [CharP K p]
    (a : ℕ) (hcard : Fintype.card K = p ^ a)
    (hQ : 32 < Fintype.card K) (h49 : Fintype.card K ≠ 49) (h121 : Fintype.card K ≠ 121)
    (m : ℕ) (hm : 4 ≤ m) (S : Finset (Point K m))
    (hS : S.card ≤ lowWeightCutoff (Fintype.card K) m) :
    ∃ W T : CodimTwo K m,
      incidenceSpan K (ZMod p) m ⊓ supportedCode (S : Set _) ≤
        Submodule.span (ZMod p) {incidenceWord (ZMod p) W, incidenceWord (ZMod p) T} := by
  classical
  let : Fintype (CodimTwo K m) := Fintype.ofFinite _
  let : Nonempty (CodimTwo K m) := codimTwo_nonempty K m (by omega)
  obtain ⟨T, hT, hspan⟩ := exists_common_sparse_support (incidenceWord (ZMod p))
    (incidenceSpan K (ZMod p) m ⊓ supportedCode (S : Set _))
    (geometric_six_rows_independent (by simpa only [Nat.card_eq_fintype_card] using hQ) hm)
    (shortening_word_sparse p hAD K a hcard hQ h49 h121 m hm S hS)
    (fun x y hx hy hu hxS hyS =>
      geometric_overlapping_pairs_impossible hQ hm S hS x y hx hy hu hxS.2 hyS.2)
  by_cases hT2 : T.card = 2
  · obtain ⟨W,W',hne,hTeq⟩ := Finset.card_eq_two.mp hT2
    refine ⟨W,W', ?_⟩
    simpa only [hTeq, Finset.coe_pair, Set.image_pair] using hspan
  · have hT1 : T.card ≤ 1 := by omega
    obtain ⟨W,hW⟩ := Finset.card_le_one_iff_subset_singleton.mp hT1
    refine ⟨W,W, hspan.trans (Submodule.span_mono ?_)⟩
    rintro _ ⟨j,hj,rfl⟩
    have hjW : j = W := Finset.mem_singleton.mp (hW hj)
    simp [hjW]

/-- A genuine pair of incidence rows needs more than `4e/3` coordinates. -/
theorem geometric_pair_impossible {K k : Type*}
    [Field K] [Fintype K] [Field k] {m : ℕ}
    (hQ : 32 < Fintype.card K) (hm : 4 ≤ m)
    (S : Finset (Point K m))
    (hS : 3 * S.card ≤ 4 * ((Fintype.card K ^ (m - 2) - 1) / (Fintype.card K - 1)))
    (x : CodimTwo K m →₀ k) (hx : x.support.card = 2)
    (hxS : Finsupp.linearCombination k (incidenceWord k) x ∈ supportedCode (S : Set _)) : False := by
  classical
  obtain ⟨i,j,hij,hxset⟩ := Finset.card_eq_two.mp hx
  let A : CodimTwo K m → Finset (Point K m) := fun W => Finset.univ.filter (Incident W.val)
  have hAc (W : CodimTwo K m) : (A W).card =
      (Fintype.card K ^ (m - 2) - 1) / (Fintype.card K - 1) := by
    simpa only [hammingNorm, incidenceWord_ne_zero, Nat.card_eq_fintype_card] using
      incidence_weight (k := k) W
  have hAB : (A i ∩ A j).card ≤
      (Fintype.card K ^ (m - 3) - 1) / (Fintype.card K - 1) := by
    have he : (A i ∩ A j).card =
        Nat.card {P : Point K m // Incident i.val P ∧ Incident j.val P} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      congr 1
      ext P
      simp [A]
    rw [he]
    simpa only [Nat.card_eq_fintype_card] using overlap_card_le i j hij
  have hxeq : Finsupp.linearCombination k (incidenceWord k) x =
      x i • incidenceWord k i + x j • incidenceWord k j := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum, hxset, Finset.sum_pair hij]
  have hh := two_sets_card_bound (A i) (A j) S (x i) (x j)
    (Finsupp.mem_support_iff.mp (by rw [hxset]; simp))
    (Finsupp.mem_support_iff.mp (by rw [hxset]; simp))
    (fun P hP => by
      have h := hxS P hP
      rw [hxeq] at h
      simpa [A, incidenceWord] using h)
  rw [hAc, hAc] at hh
  have hstrict := four_weight_lt_six_difference _ _ hQ hm
  omega

/-- Every word in the smaller shortening has a one-row representation. -/
theorem shortening_word_single (p : ℕ) [Fact p.Prime] (hAD : AD21LowWeight p)
    (K : Type) [Field K] [Fintype K] [CharP K p]
    (a : ℕ) (hcard : Fintype.card K = p ^ a)
    (hQ : 32 < Fintype.card K) (h49 : Fintype.card K ≠ 49) (h121 : Fintype.card K ≠ 121)
    (m : ℕ) (hm : 4 ≤ m) (S : Finset (Point K m))
    (hS : 3 * S.card ≤ 4 * ((Fintype.card K ^ (m - 2) - 1) / (Fintype.card K - 1)))
    (v : Point K m → ZMod p)
    (hv : v ∈ incidenceSpan K (ZMod p) m ⊓ supportedCode (S : Set _)) :
    ∃ z : CodimTwo K m →₀ ZMod p, z.support.card ≤ 1 ∧
      Finsupp.linearCombination (ZMod p) (incidenceWord (ZMod p)) z = v := by
  have hcut : S.card ≤ lowWeightCutoff (Fintype.card K) m := by
    have h := four_weight_le_three_cutoff _ _ hQ hm
    omega
  obtain ⟨z,hz,heq⟩ := shortening_word_sparse p hAD K a hcard hQ h49 h121 m hm S hcut v hv
  refine ⟨z, ?_, heq⟩
  by_contra hn
  have hz2 : z.support.card = 2 := by omega
  exact geometric_pair_impossible hQ hm S hS z hz2 (heq ▸ hv.2)

/-- Lemma 3.4, one-incidence conclusion, at every `m ≥ 4`. -/
theorem shortening_contained_in_one_incidence_row
    (p : ℕ) [Fact p.Prime] (hAD : AD21LowWeight p)
    (K : Type) [Field K] [Fintype K] [CharP K p]
    (a : ℕ) (hcard : Fintype.card K = p ^ a)
    (hQ : 32 < Fintype.card K) (h49 : Fintype.card K ≠ 49) (h121 : Fintype.card K ≠ 121)
    (m : ℕ) (hm : 4 ≤ m) (S : Finset (Point K m))
    (hS : (S.card : ℝ) ≤ 4 * (incidenceWeight (Fintype.card K) m : ℝ) / 3) :
    ∃ W : CodimTwo K m,
      incidenceSpan K (ZMod p) m ⊓ supportedCode (S : Set _) ≤
        Submodule.span (ZMod p) {incidenceWord (ZMod p) W} := by
  classical
  let : Fintype (CodimTwo K m) := Fintype.ofFinite _
  let : Nonempty (CodimTwo K m) := codimTwo_nonempty K m (by omega)
  have hSnat : 3 * S.card ≤ 4 * ((Fintype.card K ^ (m - 2) - 1) / (Fintype.card K - 1)) := by
    have hh : (3 : ℝ) * S.card ≤ 4 * incidenceWeight (Fintype.card K) m := by linarith
    exact_mod_cast hh
  apply exists_common_single_support (incidenceWord (ZMod p))
    (incidenceSpan K (ZMod p) m ⊓ supportedCode (S : Set _))
  · intro T hT
    exact geometric_six_rows_independent
      (by simpa only [Nat.card_eq_fintype_card] using hQ) hm T (by omega)
  · exact shortening_word_single p hAD K a hcard hQ h49 h121 m hm S hSnat

/-- Lemma 3.4, exact distance of the prime-field incidence span. -/
theorem incidence_span_distance
    (p : ℕ) [Fact p.Prime] (hAD : AD21LowWeight p)
    (K : Type) [Field K] [Fintype K] [CharP K p]
    (a : ℕ) (hcard : Fintype.card K = p ^ a)
    (hQ : 32 < Fintype.card K) (h49 : Fintype.card K ≠ 49) (h121 : Fintype.card K ≠ 121)
    (m : ℕ) (hm : 4 ≤ m) :
    Code.dist (incidenceSpan K (ZMod p) m : Set (Point K m → ZMod p)) =
      incidenceWeight (Fintype.card K) m := by
  classical
  let e := incidenceWeight (Fintype.card K) m
  have hepos : 0 < e := by
    have ha := Nat.pow_pos (show 0 < Fintype.card K by omega) (n := m - 3)
    have hh := (incidence_arithmetic _ _ hQ hm).1
    change 0 < (Fintype.card K ^ (m - 2) - 1) / (Fintype.card K - 1)
    rw [hh]
    exact Nat.add_pos_right _ ha
  obtain ⟨W⟩ := codimTwo_nonempty K m (by omega)
  have hWweight : hammingNorm (incidenceWord (ZMod p) W) = e := by
    simpa only [Nat.card_eq_fintype_card, e, incidenceWeight] using incidence_weight (k := ZMod p) W
  have hWne : incidenceWord (ZMod p) W ≠ 0 := by
    intro h
    rw [h, hammingNorm_zero] at hWweight
    omega
  have hnonzero : ∃ v ∈ incidenceSpan K (ZMod p) m, v ≠ 0 :=
    ⟨incidenceWord (ZMod p) W, incidenceWord_mem_span W, hWne⟩
  apply le_antisymm
  · exact code_distance_le_of_nonzero_word _ e
      ⟨incidenceWord (ZMod p) W, incidenceWord_mem_span W, hWne, hWweight.le⟩
  · have hdist := code_distance_gt_of_nonzero_weights (incidenceSpan K (ZMod p) m)
      (e - 1) hnonzero ?_
    · change e ≤ _
      omega
    · intro v hv hvne
      by_contra hbad
      have hsmall : hammingNorm v < e := by omega
      let S : Finset (Point K m) := Finset.univ.filter (fun P => v P ≠ 0)
      have hScard : S.card = hammingNorm v := rfl
      have hvS : v ∈ supportedCode (S : Set _) := by
        intro P hP
        by_contra hn
        exact hP (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩)
      have hSreal : (S.card : ℝ) ≤ 4 * (incidenceWeight (Fintype.card K) m : ℝ) / 3 := by
        have hle : S.card ≤ incidenceWeight (Fintype.card K) m := by omega
        have hle' : (S.card : ℝ) ≤ (incidenceWeight (Fintype.card K) m : ℝ) := by exact_mod_cast hle
        have hnonneg : (0 : ℝ) ≤ incidenceWeight (Fintype.card K) m := Nat.cast_nonneg _
        linarith
      obtain ⟨T,hT⟩ := shortening_contained_in_one_incidence_row
        p hAD K a hcard hQ h49 h121 m hm S hSreal
      obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (hT ⟨hv,hvS⟩)
      have hcne : c ≠ 0 := by intro h; subst c; simp only [zero_smul] at hc; exact hvne hc.symm
      have hvweight : hammingNorm v = e := by
        rw [← hc, hammingNorm_smul (fun _ => IsSMulRegular.of_ne_zero hcne)]
        simpa only [Nat.card_eq_fintype_card, e, incidenceWeight] using incidence_weight (k := ZMod p) T
      omega

end OneAndAHalfJohnson
