module

public import OneAndAHalfJohnson.Basic

/-!
# Minimum-distance assembly from small-word exclusion

Generic assembly lemmas for the syndrome-kernel construction in Section 3 of
 ePrint 2026/1894. These results use actual Hamming weight and actual linear
codes. The geometry classifying small words and constructing the syndrome map
are separate obligations; no paper existence theorem is proved here.
-/

@[expose] public section

namespace OneAndAHalfJohnson

variable {F I : Type*} [Field F] [DecidableEq F] [Fintype I]

/-- A nonzero code has distance above `L` if every nonzero word has weight above
`L`. The nonzero hypothesis is needed because ArkLib assigns distance zero to
the zero code. -/
theorem code_distance_gt_of_nonzero_weights
    (C : Submodule F (I → F)) (L : ℕ)
    (hne : ∃ c ∈ C, c ≠ 0)
    (hweight : ∀ c ∈ C, c ≠ 0 → L < hammingNorm c) :
    L < Code.dist (C : Set (I → F)) := by
  rw [show Code.dist (C : Set (I → F)) = LinearCode.disFromHammingNorm C from
    LinearCode.dist_eq_dist_from_HammingNorm C, LinearCode.disFromHammingNorm]
  have hs : {d : ℕ | ∃ c ∈ C, c ≠ 0 ∧ hammingNorm c ≤ d}.Nonempty := by
    obtain ⟨c, hc, hn⟩ := hne
    exact ⟨hammingNorm c, c, hc, hn, le_rfl⟩
  obtain ⟨c, hc, hn, hw⟩ := csInf_mem hs
  exact lt_of_lt_of_le (hweight c hc hn) hw

/-- One nonzero word supplies an upper bound on the code's minimum distance. -/
theorem code_distance_le_of_nonzero_word
    (C : Submodule F (I → F)) (U : ℕ)
    (h : ∃ c ∈ C, c ≠ 0 ∧ hammingNorm c ≤ U) :
    Code.dist (C : Set (I → F)) ≤ U := by
  rw [show Code.dist (C : Set (I → F)) = LinearCode.disFromHammingNorm C from
    LinearCode.dist_eq_dist_from_HammingNorm C, LinearCode.disFromHammingNorm]
  exact csInf_le' h

/-- Excluding small nonzero vectors from the syndrome kernel gives the strict
minimum-distance bound for a nonzero intersection code. -/
theorem syndrome_kernel_distance_gt
    {V : Type*} [AddCommGroup V] [Module F V]
    (D : Submodule F (I → F)) (ψ : (I → F) →ₗ[F] V) (L : ℕ)
    (hne : ∃ c ∈ D ⊓ LinearMap.ker ψ, c ≠ 0)
    (hexclude : ∀ c ∈ D, c ≠ 0 → hammingNorm c ≤ L → ψ c ≠ 0) :
    L < Code.dist (D ⊓ LinearMap.ker ψ : Set (I → F)) := by
  apply code_distance_gt_of_nonzero_weights _ L hne
  intro c hc hn
  by_contra h
  exact hexclude c hc.1 hn (Nat.le_of_not_gt h) hc.2

/-- A small-word classification by two-generator spans, and injectivity of the
syndrome map on those spans, exclude every small nonzero word from its kernel.
The selected generators and the geometry proving this classification remain
explicit hypotheses. -/
theorem syndrome_nonzero_of_pair_span_classification
    {V : Type*} [AddCommGroup V] [Module F V]
    (D : Submodule F (I → F)) (ψ : (I → F) →ₗ[F] V) (L : ℕ)
    (hclass : ∀ c ∈ D, c ≠ 0 → hammingNorm c ≤ L →
      ∃ a b : I → F, c ∈ Submodule.span F ({a, b} : Set (I → F)) ∧
        Set.InjOn ψ (Submodule.span F ({a, b} : Set (I → F)))) :
    ∀ c ∈ D, c ≠ 0 → hammingNorm c ≤ L → ψ c ≠ 0 := by
  intro c hc hn hw hψ
  obtain ⟨a, b, hab, hinj⟩ := hclass c hc hn hw
  exact hn (hinj hab (Submodule.zero_mem _) (by simpa using hψ))

/-- Combined distance assembly for a pair-span classification. Nontriviality of
the resulting kernel is required independently of its small-word exclusion. -/
theorem syndrome_kernel_distance_gt_of_pair_span_classification
    {V : Type*} [AddCommGroup V] [Module F V]
    (D : Submodule F (I → F)) (ψ : (I → F) →ₗ[F] V) (L : ℕ)
    (hne : ∃ c ∈ D ⊓ LinearMap.ker ψ, c ≠ 0)
    (hclass : ∀ c ∈ D, c ≠ 0 → hammingNorm c ≤ L →
      ∃ a b : I → F, c ∈ Submodule.span F ({a, b} : Set (I → F)) ∧
        Set.InjOn ψ (Submodule.span F ({a, b} : Set (I → F)))) :
    L < Code.dist (D ⊓ LinearMap.ker ψ : Set (I → F)) :=
  syndrome_kernel_distance_gt D ψ L hne
    (syndrome_nonzero_of_pair_span_classification D ψ L hclass)

end OneAndAHalfJohnson
