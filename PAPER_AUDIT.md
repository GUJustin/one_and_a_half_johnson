# Paper inventory and proof audit

Source: Kominers, Thaler, Zheng, *The One-and-a-Half Johnson Bound Is Tight for Proximity Gaps of General Linear Codes*, August 2026, [ePrint 2026/1894](https://eprint.iacr.org/2026/1894). Page references below are the printed PDF page numbers, not extraction line numbers. Audit performed 2026-09-21 against the downloaded public paper. The initial inventory below is retained for traceability. Final coverage is in RESULTS.md; alternative proof routes are documented in PROOF_NOTES.md.

## Numbered results

| Result | Pages | Statement and dependencies |
|---|---|---|
| Theorem 1.1 | 3 | Main all-distance counterexample, for every sufficiently large field exponent and every admissible block length; near-MDS rate. Same mathematical statement as Theorem 3.1. |
| Corollary 1.2 | 3 | Counterexamples below unique decoding for `0 < δ < 3 - √5`. Depends on Theorem 1.1 and the elementary radius comparison. |
| Theorem 3.1 | 7; proof 12–15 | Restated main theorem. Depends on Lemma 3.2, parameter selection, subfield-line extraction, random amplification, dimension counting, and random supercode completion. |
| Lemma 3.2 | 7; proof 11–12 | Small-distance base counterexample. Depends on Theorem 3.3, Lemmas 3.4–3.5, scalar-extension shortening, and projective-subspace counts. |
| Theorem 3.3 | 8 | Low-weight ambient words use at most two incidence vectors. Invokes external Adriaensen–Denaux Theorem 5.9 and its field-size/cutoff definitions. |
| Lemma 3.4 | 8–9 | Shortenings supported on at most `L_m` points lie in a two-incidence span; those supported on at most `4e_m/3` points lie in a one-incidence span; ambient minimum distance is `e_m`. Depends on 3.3, intersection counting, and sparse-subspace classification. |
| Lemma 3.5 | 10–11 | Explicit two-check syndrome map with nonzero, pairwise independent incidence syndromes. Depends on subspace polynomials, power sums, and the quadratic extension. |
| Theorem 4.1 | 15–16; proof 16–20 | Concrete field `2^128`, length `2^36`, distance/rate intervals, word distances, and exceptional coefficient count. Depends on 3.3–3.4, random syndrome separation, Hamada rank, refined concentration, and supercode completion. |

## Substantial unnumbered proof obligations

1. **Radius algebra (pp. 2–3, 20):** `J₃/₂(δ) < Γ(δ) < δ`; characterization of `J₃/₂(δ) < δ/2`; the concrete radius and slack comparisons.
2. **Finite geometry (pp. 7–9, 11):** counts of points and codimension-two subspaces, intersection bounds, and `|Gr(m−2,m)|/Q^(2m) → 1/((Q²−1)(Q²−Q))`.
3. **Incidence independence (p. 8):** any collection of at most eight distinct incidence vectors is independent, using private support coordinates.
4. **Sparse coefficient spaces (pp. 8–9):** a three-dimensional coefficient space contains a vector with at least three nonzero coordinates; classify two-dimensional spaces all of whose vectors have weight at most two, including the binary triangle exception.
5. **Support estimates (p. 9):** exclude the binary triangle; bound weights of two-incidence combinations and their union supports.
6. **Scalar extension (used pp. 11–14):** extension commutes with shortening, preserves dimension, and transfers incidence containment to extension-field words.
7. **Subspace polynomials (pp. 10–11):** linearized shape, nonzero linear coefficient, determination by the top two lower coefficients, and three stated power-sum identities.
8. **Three-incidence kernel word (p. 11):** construct subspaces with the stipulated pairwise/triple intersections; obtain a nonzero kernel word with weight at most `3Q^(m−3)+(Q^(m−4)−1)/(Q−1)`.
9. **Syndrome witnesses (pp. 11–12):** surjectivity, two unused directions, defining words far from the kernel, and an injection from incidence vectors to exceptional coefficients.
10. **Amplification parameter selection (p. 12):** choose `Q,t,ξ,m₀` satisfying all strict radius and distance inequalities uniformly for `m ≥ m₀`.
11. **Field compatibility (p. 13):** the gcd construction works for every sufficiently large exponent `s`; averaging on subfield lines retains at least `c_Q q/2` exceptional coefficients; rescaling preserves distance.
12. **Random amplification (pp. 13–14):** success probability `(1−1/q)Φ_t(u)`, independent output coordinates, and simultaneous concentration over the ambient code.
13. **Dimension and threshold (pp. 13–14):** polynomial indicator representation, `k_m ≤ binomial(am+2a(p−1),2a(p−1))`, and uniform polynomial block-length threshold `A s^D`.
14. **Image-code properties (p. 14):** injectivity on the base code, minimum-distance approximation, coset separation, and exceptional-witness persistence.
15. **Supercode completion (p. 15):** random-supercode membership probability, Hamming-ball bounds, simultaneous preservation of minimum distance and coset separation, and uniform Singleton-defect/rate bound.
16. **Concrete base parameters (p. 16):** exact integers, random-syndrome dependence probability `q⁻¹+q⁻²−q⁻³`, and the numerical union bound.
17. **Hamada specialization (p. 17):** incidence rank is `1 + trace([[5,10],[1,10]]^9) = 3,604,584,376`; hence kernel dimension is `3,604,584,374`.
18. **Weight-layer counts (pp. 17–18):** shortening Singleton bounds and corresponding affine-coset support bounds.
19. **Refined tails (pp. 17–19):** binomial relative-entropy Chernoff bounds, derivative formulas, all numerical inequalities, and a total failure probability strictly below one.
20. **Concrete completion (p. 20):** exact completion dimension and defect, rate identity, exceptional-count/block-length ratio, and stated unique-decoding slack.

Background claims about other code families in the introduction are contextual citations, not new results proved in this paper. Tables and overview approximations should be checked as explanatory material, while the numbered statements above define the principal formalization targets.

## Gaps and quantifiers to resolve

- **Missing displayed identity (p. 11):** the proof says “By this identity” and “By the displayed identity” without displaying the needed scalar-extension/shortening identity. Explicitly prove `(span_Fq U)[S] = span_Fq(U[S])`, with the embeddings spelled out. This is a repairable exposition gap, not a detected counterexample.
- **Dimension hypothesis (pp. 10–11):** Lemma 3.5 needs `m ≥ 4` explicitly to make its coefficient/exponent references meaningful. All “sufficiently large” dimensions need quantified thresholds.
- **Strict amplification margins (p. 12):** convergence exactly to the target `δ` gives equality at `Γ(δ)`, not the required strict defining-word separation. One proof route chooses a slightly larger intermediate target distance within the allowed `η` error, then controls rounding and finite-`Q,m` errors. Parameter existence is a substantive analytic lemma.
- **Injectivity before minimum distance (p. 14):** uniform weight approximation must first show every nonzero base-code word has positive image weight. Choose `ξ` small enough relative to the positive amplified distance before equating image minimum distance with a minimum over original nonzero words.
- **Uniform big-O (p. 15):** state an explicit constant uniform over admissible `N`. The ceiling contributes `1/N`; control this with the polynomial lower bound. The upper bound `N < q` alone does not prove `h/N = O(1/s)`.
- **Concrete probability accounting (pp. 18–19):** replace “negligible probability” by explicit finite sums bounded by less than one. Transcendental decimal comparisons need certified estimates, not floating-point evidence alone.
- **External mathematics (pp. 8, 17):** AD21 classification and Hamada rank are substantial imported results. Explicit hypothesis interfaces are honest intermediate deliverables; they do not constitute unconditional verification. Neither should be silently replaced by an axiom and reported as proved.

No clear mathematical contradiction was found in this audit. The numerical inequalities were inventoried, not independently certified here.

## Pinned dependency search evidence

Read-only local searches were performed under `formalization/.lake/packages`, with no network use. `git rev-parse HEAD` agrees with `lake-manifest.json`:

| Library | Pinned revision | Search tree |
|---|---|---|
| mathlib | `5ed2965256430c3649e86755f9576b54eca72435` | `.lake/packages/mathlib/Mathlib` (8,529 Lean files) |
| ArkLib | `fa14552d40e793f2ea26e65c440306aae0c08a26` | `.lake/packages/Arklib/ArkLib` (503 Lean files) |

From the `formalization` directory, the broad content search was:

```sh
rg -n -i 'Adriaensen|Denaux|Hamada|small.weight.codewords|projective.geometric.code|incidence.matrix|grassmannian' .lake/packages/mathlib/Mathlib .lake/packages/Arklib/ArkLib
```

It found no Adriaensen/Denaux classification or Hamada rank result. `Hamada` only matched the unrelated author surname Hamadani. Other hits were generic Grassmannian definitions, simple-graph incidence matrices, and an incidence-matrix interpretation in set-family VC theory.

A focused follow-up searched:

```sh
rg -n -i 'hamada|adriaensen|denaux|rank.formula|small.weight|projective.geomet|projective.code' .lake/packages/Arklib/ArkLib/Data/CodingTheory .lake/packages/mathlib/Mathlib/LinearAlgebra .lake/packages/mathlib/Mathlib/InformationTheory .lake/packages/mathlib/Mathlib/Combinatorics
```

This likewise located no relevant classification or rank formula. A filename search for `code|hamming|grassmann|projectiv|inciden|finitegeometry` identified nearby APIs. The following sources were read to disambiguate promising hits:

- `Mathlib/LinearAlgebra/Projectivization/Cardinality.lean`: useful generic projective-point cardinality results, including `Projectivization.card` and `Projectivization.card'`; not incidence-code rank or low-weight classification.
- `ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds/Powers/Incidence.lean`: incidence estimates for a univariate-powers MCA bound, referencing Bafna–Choudhary–Guruswami–Mardia; not the projective incidence construction in this paper.

Conclusion: neither external theorem was located in these pinned sources. This is bounded source-search evidence, not a proof that an equivalent result cannot exist under unexpected terminology. Existing projectivization, Hamming, linear-code, and extension-code infrastructure remains useful.

## First implementation priorities

1. Hamming-code definitions and scalar-extension shortening.
2. A generic syndrome-counterexample theorem separating finite geometry from coding consequences.
3. Random-supercode completion and exact concrete integer arithmetic.
4. Incidence-support lemmas, amplification, and explicit parameter quantifiers.
5. Full AD21 and Hamada dependency work, with conditional interfaces clearly distinguished from completed unconditional results throughout.

## Final disposition

All eight numbered statements are covered: seven have theorem proofs (including the repeated main theorem), and Theorem 3.3 is the accepted AD21 hypothesis. Hamada is the only other external premise.

The supporting obligations are discharged to the extent needed for those exact conclusions. We do not claim a transcription of every displayed intermediate formula: the Grassmannian limit is replaced by a uniform density bound; sparse-space classification by a direct common-span argument; the sharper binomial rank estimate by a sufficient polynomial bound; random-supercode membership by deterministic greedy completion; and random-syndrome dependence probabilities by deterministic hyperplane avoidance. See PROOF_NOTES.md for the precise replacements. The remaining geometric, field, amplification, finite-family concentration, and concrete arithmetic requirements are proved in the library.
