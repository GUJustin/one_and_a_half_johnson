module

public import OneAndAHalfJohnson.Basic

/-!
# Support bounds for sparse incidence combinations

These finite-set lemmas isolate the overlapping-pair obstruction in the
shortening argument of Lemma 3.4. They hold in arbitrary characteristic,
including characteristic two where coefficients at a shared row may cancel.
-/

@[expose] public section
namespace OneAndAHalfJohnson

/-- Three set sizes equal the size of their union outside the triple overlap
plus the three pair-overlap sizes. -/
theorem three_sets_card_identity {I : Type*} [DecidableEq I] (A B C : Finset I) :
    A.card + B.card + C.card =
      ((A ∪ B ∪ C) \ (A ∩ B ∩ C)).card +
        (A ∩ B).card + (A ∩ C).card + (B ∩ C).card := by
  have h1 := Finset.card_union_add_card_inter A B
  have h2 := Finset.card_union_add_card_inter (A ∪ B) C
  have h3 := Finset.card_union_add_card_inter (A ∩ C) (B ∩ C)
  have h4 := Finset.card_sdiff_add_card_eq_card
    (show A ∩ B ∩ C ⊆ A ∪ B ∪ C by intro x hx; simp_all)
  have hu : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := by ext; simp only [Finset.mem_inter, Finset.mem_union]; tauto
  have hi : (A ∩ C) ∩ (B ∩ C) = A ∩ B ∩ C := by ext; simp only [Finset.mem_inter]; tauto
  rw [hu] at h2
  rw [hi] at h3
  omega

/-- Two overlapping pair combinations with all coefficients nonzero cover
all coordinates of the three rows except possibly their triple intersection. -/
theorem three_sets_sdiff_subset_of_overlapping_pairs
    {F I : Type*} [Field F] [DecidableEq I] (A B C S : Finset I)
    (a b c d : F) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hv : ∀ i, i ∉ S → a * (if i ∈ A then 1 else 0) +
      b * (if i ∈ B then 1 else 0) = 0)
    (hw : ∀ i, i ∉ S → c * (if i ∈ A then 1 else 0) +
      d * (if i ∈ C then 1 else 0) = 0) :
    (A ∪ B ∪ C) \ (A ∩ B ∩ C) ⊆ S := by
  intro i hi
  by_contra hiS
  have hv' := hv i hiS
  have hw' := hw i hiS
  by_cases hA : i ∈ A <;> by_cases hB : i ∈ B <;> by_cases hC : i ∈ C <;>
    simp_all

/-- The support containing two genuinely overlapping pair combinations has
a lower bound independent of coefficient cancellations. -/
theorem overlapping_pairs_card_bound
    {F I : Type*} [Field F] [DecidableEq I] (A B C S : Finset I)
    (a b c d : F) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hv : ∀ i, i ∉ S → a * (if i ∈ A then 1 else 0) +
      b * (if i ∈ B then 1 else 0) = 0)
    (hw : ∀ i, i ∉ S → c * (if i ∈ A then 1 else 0) +
      d * (if i ∈ C then 1 else 0) = 0) :
    A.card + B.card + C.card ≤ S.card +
      (A ∩ B).card + (A ∩ C).card + (B ∩ C).card := by
  have h := Finset.card_le_card
    (three_sets_sdiff_subset_of_overlapping_pairs A B C S a b c d ha hb hc hd hv hw)
  rw [three_sets_card_identity A B C]
  omega

/-- Uniform incidence weights and overlap bounds rule out overlapping pair
combinations on a coordinate set smaller than three weights minus overlaps. -/
theorem overlapping_pairs_impossible
    {F I : Type*} [Field F] [DecidableEq I] (A B C S : Finset I)
    (a b c d : F) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hv : ∀ i, i ∉ S → a * (if i ∈ A then 1 else 0) +
      b * (if i ∈ B then 1 else 0) = 0)
    (hw : ∀ i, i ∉ S → c * (if i ∈ A then 1 else 0) +
      d * (if i ∈ C then 1 else 0) = 0)
    {e Bnd : ℕ} (hA : A.card = e) (hB : B.card = e) (hC : C.card = e)
    (hAB : (A ∩ B).card ≤ Bnd) (hAC : (A ∩ C).card ≤ Bnd)
    (hBC : (B ∩ C).card ≤ Bnd) (hS : S.card + 3 * Bnd < 3 * e) : False := by
  have h := overlapping_pairs_card_bound A B C S a b c d ha hb hc hd hv hw
  omega

/-- Independence on small row sets makes small coefficient representations
unique, even if the entire incidence family is linearly dependent. -/
theorem sparse_representation_unique
    {F J V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (u : J → V) {r s : ℕ}
    (hind : ∀ T : Finset J, T.card ≤ r + s → LinearIndepOn F u (T : Set J))
    (x y : J →₀ F) (hx : x.support.card ≤ r) (hy : y.support.card ≤ s)
    (heq : Finsupp.linearCombination F u x = Finsupp.linearCombination F u y) :
    x = y := by
  classical
  have hcard : (x.support ∪ y.support).card ≤ r + s :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add hx hy)
  apply (linearIndepOn_iffₛ.mp (hind _ hcard)) x ?_ y ?_ heq
  · rw [Finsupp.mem_supported]
    intro j hj
    exact Finset.mem_union_left _ hj
  · rw [Finsupp.mem_supported]
    intro j hj
    exact Finset.mem_union_right _ hj

/-- A combination genuinely using three or four rows cannot be represented
using at most two, under independence of every six-row subfamily. -/
theorem three_or_four_rows_not_two
    {F J V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (u : J → V)
    (hind : ∀ T : Finset J, T.card ≤ 6 → LinearIndepOn F u (T : Set J))
    (x y : J →₀ F) (hxlo : 3 ≤ x.support.card) (hxhi : x.support.card ≤ 4)
    (hy : y.support.card ≤ 2) :
    Finsupp.linearCombination F u x ≠ Finsupp.linearCombination F u y := by
  intro heq
  have hxy := sparse_representation_unique u (r := 4) (s := 2) hind x y hxhi hy heq
  rw [hxy] at hxlo
  omega

/-- In a subspace whose words all have two-row representations, a genuine
pair representation cannot be disjoint from any nonzero sparse representation.
The sum would otherwise genuinely use three or four rows. -/
theorem sparse_pair_must_overlap
    {F J V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (u : J → V) (U : Submodule F V)
    (hind : ∀ T : Finset J, T.card ≤ 6 → LinearIndepOn F u (T : Set J))
    (hsparse : ∀ v ∈ U, ∃ z : J →₀ F, z.support.card ≤ 2 ∧
      Finsupp.linearCombination F u z = v)
    (x y : J →₀ F) (hx : x.support.card = 2)
    (hylo : 1 ≤ y.support.card) (hyhi : y.support.card ≤ 2)
    (hxU : Finsupp.linearCombination F u x ∈ U)
    (hyU : Finsupp.linearCombination F u y ∈ U) :
    ¬ Disjoint x.support y.support := by
  classical
  intro hd
  obtain ⟨z, hz, heq⟩ := hsparse _ (U.add_mem hxU hyU)
  have hcard : (x + y).support.card = 2 + y.support.card := by
    rw [Finsupp.support_add_eq hd, Finset.card_union_of_disjoint hd, hx]
  apply three_or_four_rows_not_two u hind (x + y) z (by omega) (by omega) hz
  simpa only [map_add] using heq.symm

/-- In a finite two-sparse subspace, exclusion of genuinely overlapping pairs
forces a single common support of size at most two for all words. -/
theorem exists_common_sparse_support
    {F J V : Type*} [Field F] [Fintype F] [Fintype J] [DecidableEq J]
    [AddCommGroup V] [Module F V]
    (u : J → V) (U : Submodule F V)
    (hind : ∀ T : Finset J, T.card ≤ 6 → LinearIndepOn F u (T : Set J))
    (hsparse : ∀ v ∈ U, ∃ z : J →₀ F, z.support.card ≤ 2 ∧
      Finsupp.linearCombination F u z = v)
    (hoverlap : ∀ x y : J →₀ F, x.support.card = 2 → y.support.card = 2 →
      (x.support ∪ y.support).card = 3 →
      Finsupp.linearCombination F u x ∈ U →
      Finsupp.linearCombination F u y ∈ U → False) :
    ∃ T : Finset J, T.card ≤ 2 ∧ U ≤ Submodule.span F (u '' (T : Set J)) := by
  classical
  let A : Finset (J →₀ F) := Finset.univ.filter (fun x => x.support.card ≤ 2 ∧
    Finsupp.linearCombination F u x ∈ U)
  have hA : A.Nonempty := ⟨0, by simp [A]⟩
  obtain ⟨x, hxA, hmax⟩ := A.exists_max_image (fun x => x.support.card) hA
  have hx : x.support.card ≤ 2 ∧ Finsupp.linearCombination F u x ∈ U := by
    simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and] using hxA
  refine ⟨x.support, hx.1, ?_⟩
  intro v hv
  obtain ⟨y, hy, rfl⟩ := hsparse v hv
  have hyA : y ∈ A := by simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hy, hv⟩
  have hymax : y.support.card ≤ x.support.card := hmax y hyA
  have hsub : y.support ⊆ x.support := by
    by_contra hnot
    have hypos : 0 < y.support.card := Finset.card_pos.mpr (by
      obtain ⟨j, hj, _⟩ := Finset.not_subset.mp hnot
      exact ⟨j, hj⟩)
    by_cases hd : Disjoint x.support y.support
    · obtain ⟨z, hz, heq⟩ := hsparse _ (U.add_mem hx.2 hv)
      have hsum : (x + y).support.card = x.support.card + y.support.card := by
        rw [Finsupp.support_add_eq hd, Finset.card_union_of_disjoint hd]
      have hxy : x + y = z := sparse_representation_unique u (r := 4) (s := 2) hind
        (x + y) z (by omega) hz (by simpa only [map_add] using heq.symm)
      have hzA : z ∈ A := by
        simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hz, heq ▸ U.add_mem hx.2 hv⟩
      have hzmax := hmax z hzA
      rw [← hxy] at hzmax
      omega
    · have hinter : 0 < (x.support ∩ y.support).card := by
        rw [Finset.card_pos]
        obtain ⟨j, hjx, hjy⟩ := Finset.not_disjoint_iff.mp hd
        exact ⟨j, Finset.mem_inter.mpr ⟨hjx, hjy⟩⟩
      have hunion : x.support.card < (x.support ∪ y.support).card := by
        apply Finset.card_lt_card
        exact Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left, by
          intro he; apply hnot; rw [he]; exact Finset.subset_union_right⟩
      have hcard := Finset.card_union_add_card_inter x.support y.support
      have hx2 : x.support.card = 2 := by omega
      have hy2 : y.support.card = 2 := by omega
      have hu3 : (x.support ∪ y.support).card = 3 := by omega
      exact hoverlap x y hx2 hy2 hu3 hx.2 hv
  rw [Finsupp.linearCombination_apply]
  apply Submodule.sum_mem
  intro j hj
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hsub hj, rfl⟩)

/-- A nonzero pair combination covers the symmetric difference of its rows. -/
theorem two_sets_card_bound
    {F I : Type*} [Field F] [DecidableEq I] (A B S : Finset I)
    (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hv : ∀ i, i ∉ S → a * (if i ∈ A then 1 else 0) +
      b * (if i ∈ B then 1 else 0) = 0) :
    A.card + B.card ≤ S.card + 2 * (A ∩ B).card := by
  have hsub : (A ∪ B) \ (A ∩ B) ⊆ S := by
    intro i hi
    by_contra hiS
    have h := hv i hiS
    by_cases hiA : i ∈ A <;> by_cases hiB : i ∈ B <;> simp_all
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_add_card_inter A B
  have h3 := Finset.card_sdiff_add_card_eq_card
    (show A ∩ B ⊆ A ∪ B by intro i hi; simp_all)
  omega

/-- A finite subspace all of whose words use at most one row has a fixed
one-row support when every three-row family is independent. -/
theorem exists_common_single_support
    {F J V : Type*} [Field F] [Fintype F] [Fintype J] [Nonempty J] [DecidableEq J]
    [AddCommGroup V] [Module F V]
    (u : J → V) (U : Submodule F V)
    (hind : ∀ T : Finset J, T.card ≤ 3 → LinearIndepOn F u (T : Set J))
    (hsparse : ∀ v ∈ U, ∃ z : J →₀ F, z.support.card ≤ 1 ∧
      Finsupp.linearCombination F u z = v) :
    ∃ j : J, U ≤ Submodule.span F {u j} := by
  classical
  let A : Finset (J →₀ F) := Finset.univ.filter (fun x => x.support.card ≤ 1 ∧
    Finsupp.linearCombination F u x ∈ U)
  have hA : A.Nonempty := ⟨0, by simp [A]⟩
  obtain ⟨x, hxA, hmax⟩ := A.exists_max_image (fun x => x.support.card) hA
  have hx : x.support.card ≤ 1 ∧ Finsupp.linearCombination F u x ∈ U := by
    simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and] using hxA
  obtain ⟨j,hj⟩ := Finset.card_le_one_iff_subset_singleton.mp hx.1
  refine ⟨j, ?_⟩
  intro v hv
  obtain ⟨y, hy, rfl⟩ := hsparse v hv
  have hsub : y.support ⊆ x.support := by
    by_contra hnot
    obtain ⟨l, hly, hlx⟩ := Finset.not_subset.mp hnot
    have hypos := Finset.card_pos.mpr ⟨l,hly⟩
    have hd : Disjoint x.support y.support := by
      apply Finset.disjoint_left.mpr
      intro z hzx hzy
      have hzl := Finset.card_le_one.mp hy z hzy l hly
      exact hlx (hzl ▸ hzx)
    obtain ⟨z, hz, heq⟩ := hsparse _ (U.add_mem hx.2 hv)
    have hsum : (x + y).support.card = x.support.card + y.support.card := by
      rw [Finsupp.support_add_eq hd, Finset.card_union_of_disjoint hd]
    have hxy : x + y = z := sparse_representation_unique u (r := 2) (s := 1) hind
      (x + y) z (by omega) hz (by simpa only [map_add] using heq.symm)
    have hzA : z ∈ A := by
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hz, heq ▸ U.add_mem hx.2 hv⟩
    have hzmax := hmax z hzA
    rw [← hxy] at hzmax
    omega
  rw [Finsupp.linearCombination_apply]
  apply Submodule.sum_mem
  intro l hl
  have hlj : l = j := Finset.mem_singleton.mp (hj (hsub hl))
  exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [hlj]))

end OneAndAHalfJohnson
