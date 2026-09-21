module

public import OneAndAHalfJohnson.GeometryShortening

/-!
# Lemma 3.4: structure and distance of shortened incidence codes

Paper: ePrint 2026/1894, PDF pp. 8–9. This module proves the entire
`Targets.ShorteningStructure` contract, conditionally only on the explicitly
authorized `Targets.AD21LowWeight` classification (Theorem 3.3). Hamada's rank
formula and the paper's other existence statements are not premises.

For a geometry field of order `Q = p^a > 32`, with `Q ≠ 49, 121`, write
`e = (Q^(m-2)-1)/(Q-1)` and `L = 3*Q^(m-3)-3*Q^(m-4)-1`. The result says:

* Every shortening on at most `L` coordinates lies in one fixed span of two
  codimension-two incidence rows.
* Every shortening on at most `4e/3` coordinates lies in one fixed incidence-row
  span.
* The prime-field incidence code has minimum Hamming distance exactly `e`.

The same selected pair or singleton contains every word in its shortening.
The proof gives the explicit dimension threshold `m₀ = 4`, so it covers the
paper's concrete `Q = 512`, `m = 5` application as well as its asymptotic use.

The supporting proofs are in `GeometryShortening`. Local independence makes
small row representations unique. Maximal coefficient support reduces the
common-pair assertion to overlapping pairs, whose coordinate support exceeds
the cutoff. Symmetric-difference counting excludes a genuine pair at `4e/3`;
the resulting singleton statement yields the exact distance. These arguments
include characteristic two without assuming away coefficient cancellation.
-/

@[expose] public section
namespace OneAndAHalfJohnson.MainTheorems
open Targets

/-- Full Lemma 3.4, conditional only on AD21, with the verified threshold `m₀ = 4`. -/

theorem shorteningStructure_of_AD21 (p : ℕ) [Fact p.Prime]
    (hAD : AD21LowWeight p) : ShorteningStructure p := by
  intro K _ _ _ a hcard hQ h49 h121
  refine ⟨4, le_rfl, ?_⟩
  intro m hm
  exact ⟨shortening_contained_in_two_incidence_rows p hAD K a hcard hQ h49 h121 m hm,
    shortening_contained_in_one_incidence_row p hAD K a hcard hQ h49 h121 m hm,
    incidence_span_distance p hAD K a hcard hQ h49 h121 m hm⟩

end OneAndAHalfJohnson.MainTheorems
