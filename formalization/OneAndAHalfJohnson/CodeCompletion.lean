module

public import OneAndAHalfJohnson.Supercode
public import OneAndAHalfJohnson.CodeDistance
public import ArkLib.Data.CodingTheory.HammingBallVolume
public import Mathlib.Data.Nat.Choose.Sum

/-! # Hamming-ball bounds and deterministic distance-preserving completion

These results instantiate greedy forbidden-set avoidance with low-weight words
and two Hamming balls. They require no random-supercode existence premise.
-/

@[expose] public section
noncomputable section
namespace OneAndAHalfJohnson

/-- The elementary bound obtained by summing shells and bounding each alphabet
factor by `q^r`. The radius may exceed the block length. -/
theorem card_hamming_ball_le {F I : Type*} [Fintype F] [Nonempty F] [DecidableEq F]
    [Fintype I] [DecidableEq I] (y : I → F) (r : ℕ) :
    (Finset.univ.filter (fun x => hammingDist y x ≤ r)).card ≤
      2 ^ Fintype.card I * Fintype.card F ^ r := by
  classical
  let n := Fintype.card I
  let R := min r n
  have hpartition :
      (Finset.univ.filter (fun x => hammingDist y x ≤ r)).card =
        ∑ i ∈ Finset.range (R + 1),
          (Finset.univ.filter (fun x : I → F => hammingDist y x = i)).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range,
        Finset.mem_univ, true_and]
      constructor
      · intro h
        refine ⟨hammingDist y x, ?_, rfl⟩
        have hn := hammingDist_le_card_fintype (x := y) (y := x)
        dsimp [R, n]
        omega
      · rintro ⟨i, hi, h⟩
        dsimp [R] at hi
        omega
    · intro a ha b hb hab
      simp only [Finset.disjoint_filter, Finset.mem_univ, true_implies]
      intro x hxa hxb
      exact hab (hxa.symm.trans hxb)
  rw [hpartition]
  calc
    _ ≤ ∑ i ∈ Finset.range (R + 1), Nat.choose n i * Fintype.card F ^ r := by
      apply Finset.sum_le_sum
      intro i hi
      rw [CodingTheory.card_filter_hammingDist_eq]
      apply Nat.mul_le_mul_left
      calc
        (Fintype.card F - 1) ^ i ≤ Fintype.card F ^ i := Nat.pow_le_pow_left (Nat.sub_le _ _) _
        _ ≤ Fintype.card F ^ r := Nat.pow_le_pow_right Fintype.card_pos (by
          have := Finset.mem_range.mp hi
          dsimp [R] at this
          omega)
    _ ≤ ∑ i ∈ Finset.range (n + 1), Nat.choose n i * Fintype.card F ^ r := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · apply Finset.range_mono
        dsimp [R]
        omega
      · intros; exact Nat.zero_le _
    _ = 2 ^ n * Fintype.card F ^ r := by
      rw [← Finset.sum_mul, Nat.sum_range_choose]

/-- Complete a code to a prescribed dimension while retaining its minimum
weight and the strict absolute distance of two defining words. The numerical
hypothesis is the crude forbidden-set bound from the paper. -/
theorem exists_code_completion_of_weight_bounds
    {F I : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype I] [DecidableEq I]
    (C₀ : Submodule F (I → F)) (f g : I → F) (d b K : ℕ)
    (hd : 0 < d)
    (hmin : ∀ c ∈ C₀, c ≠ 0 → d ≤ hammingNorm c)
    (hwitness : ∃ c ∈ C₀, c ≠ 0 ∧ hammingNorm c ≤ d)
    (hf : ∀ c ∈ C₀, b < hammingDist f c)
    (hg : ∀ c ∈ C₀, b < hammingDist g c)
    (hK : Module.finrank F C₀ ≤ K)
    (hsize : (2 ^ Fintype.card I * Fintype.card F ^ (d - 1) +
      2 ^ (Fintype.card I + 1) * Fintype.card F ^ b) * Fintype.card F ^ K <
        Fintype.card F ^ Fintype.card I) :
    ∃ C : Submodule F (I → F), C₀ ≤ C ∧ Module.finrank F C = K ∧
      Code.dist (C : Set (I → F)) = d ∧
      (∀ c ∈ C, b < hammingDist f c) ∧ (∀ c ∈ C, b < hammingDist g c) := by
  classical
  let L : Finset (I → F) := Finset.univ.filter (fun v => v ≠ 0 ∧ hammingNorm v ≤ d - 1)
  let Bf : Finset (I → F) := Finset.univ.filter (fun v => hammingDist f v ≤ b)
  let Bg : Finset (I → F) := Finset.univ.filter (fun v => hammingDist g v ≤ b)
  let B := L ∪ Bf ∪ Bg
  have hL : L.card ≤ 2 ^ Fintype.card I * Fintype.card F ^ (d - 1) := by
    apply le_trans (Finset.card_le_card (t := Finset.univ.filter
      (fun v => hammingDist (0 : I → F) v ≤ d - 1)) ?_)
      (card_hamming_ball_le (0 : I → F) (d - 1))
    intro v hv
    have hv' := (Finset.mem_filter.mp hv).2.2
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, hammingDist_zero_left] using hv'
  have hBcard : B.card ≤ 2 ^ Fintype.card I * Fintype.card F ^ (d - 1) +
      2 ^ (Fintype.card I + 1) * Fintype.card F ^ b := by
    calc
      B.card ≤ L.card + Bf.card + Bg.card :=
        le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (Finset.card_union_le _ _) _)
      _ ≤ 2 ^ Fintype.card I * Fintype.card F ^ (d - 1) +
          2 ^ Fintype.card I * Fintype.card F ^ b +
          2 ^ Fintype.card I * Fintype.card F ^ b :=
        Nat.add_le_add (Nat.add_le_add hL (card_hamming_ball_le f b))
          (card_hamming_ball_le g b)
      _ = _ := by ring
  have hB : B.Nonempty := by
    refine ⟨f, Finset.mem_union_left _ (Finset.mem_union_right _ ?_)⟩
    simp [Bf]
  have havoid : ∀ v ∈ B, v ∉ C₀ := by
    intro v hv hc
    rcases Finset.mem_union.mp hv with hv | hv
    · rcases Finset.mem_union.mp hv with hv | hv
      · have hh := (Finset.mem_filter.mp hv).2
        have hl := hmin v hc hh.1
        omega
      · exact (Nat.not_le_of_gt (hf v hc)) (Finset.mem_filter.mp hv).2
    · exact (Nat.not_le_of_gt (hg v hc)) (Finset.mem_filter.mp hv).2
  have hsize' : B.card * Fintype.card F ^ K < Fintype.card (I → F) := by
    rw [Fintype.card_fun]
    exact lt_of_le_of_lt (Nat.mul_le_mul_right _ hBcard) hsize
  obtain ⟨C, hC, hdim, hCB⟩ := exists_avoiding_supercode C₀ B hB havoid K hK hsize'
  have hnonzero : ∃ c ∈ C, c ≠ 0 := by
    obtain ⟨c, hc, hn, _⟩ := hwitness
    exact ⟨c, hC hc, hn⟩
  have hlow : d - 1 < Code.dist (C : Set (I → F)) := by
    apply code_distance_gt_of_nonzero_weights C (d - 1) hnonzero
    intro c hc hn
    by_contra hw
    apply hCB c (Finset.mem_union_left _ (Finset.mem_union_left _ ?_)) hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn, Nat.le_of_not_gt hw⟩
  have hupp : Code.dist (C : Set (I → F)) ≤ d := by
    apply code_distance_le_of_nonzero_word C d
    obtain ⟨c, hc, hn, hw⟩ := hwitness
    exact ⟨c, hC hc, hn, hw⟩
  refine ⟨C, hC, hdim, by omega, ?_, ?_⟩
  · intro c hc
    by_contra hh
    apply hCB c (Finset.mem_union_left _ (Finset.mem_union_right _ ?_)) hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.le_of_not_gt hh⟩
  · intro c hc
    by_contra hh
    apply hCB c (Finset.mem_union_right _ ?_) hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.le_of_not_gt hh⟩

/-- Distance-preserving completion stated using the actual minimum distance of
an existing nonzero code. Both defining words remain farther than `b`. -/
theorem exists_code_completion
    {F I : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype I] [DecidableEq I]
    (C₀ : Submodule F (I → F)) (f g : I → F) (b K : ℕ)
    (hne : ∃ c ∈ C₀, c ≠ 0)
    (hf : ∀ c ∈ C₀, b < hammingDist f c)
    (hg : ∀ c ∈ C₀, b < hammingDist g c)
    (hK : Module.finrank F C₀ ≤ K)
    (hsize : (2 ^ Fintype.card I *
        Fintype.card F ^ (Code.dist (C₀ : Set (I → F)) - 1) +
      2 ^ (Fintype.card I + 1) * Fintype.card F ^ b) * Fintype.card F ^ K <
        Fintype.card F ^ Fintype.card I) :
    ∃ C : Submodule F (I → F), C₀ ≤ C ∧ Module.finrank F C = K ∧
      Code.dist (C : Set (I → F)) = Code.dist (C₀ : Set (I → F)) ∧
      (∀ c ∈ C, b < hammingDist f c) ∧ (∀ c ∈ C, b < hammingDist g c) := by
  have hd : 0 < Code.dist (C₀ : Set (I → F)) :=
    code_distance_gt_of_nonzero_weights C₀ 0 hne (fun c hc hn => hammingNorm_pos_iff.mpr hn)
  have hmin : ∀ c ∈ C₀, c ≠ 0 → Code.dist (C₀ : Set (I → F)) ≤ hammingNorm c := by
    intro c hc hn
    exact code_distance_le_of_nonzero_word C₀ _ ⟨c, hc, hn, le_rfl⟩
  have hwitness : ∃ c ∈ C₀, c ≠ 0 ∧ hammingNorm c ≤ Code.dist (C₀ : Set (I → F)) := by
    rw [show Code.dist (C₀ : Set (I → F)) = LinearCode.disFromHammingNorm C₀ from
      LinearCode.dist_eq_dist_from_HammingNorm C₀, LinearCode.disFromHammingNorm]
    have hs : {d : ℕ | ∃ c ∈ C₀, c ≠ 0 ∧ hammingNorm c ≤ d}.Nonempty := by
      obtain ⟨c, hc, hn⟩ := hne
      exact ⟨hammingNorm c, c, hc, hn, le_rfl⟩
    exact csInf_mem hs
  exact exists_code_completion_of_weight_bounds C₀ f g _ b K hd hmin hwitness hf hg hK hsize

end OneAndAHalfJohnson
