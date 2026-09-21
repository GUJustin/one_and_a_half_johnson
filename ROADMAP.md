# Conditional paper formalization roadmap

## Accepted scope and completion criterion

The user accepts an initial formalization conditional **only on the external Adriaensen–Denaux low-weight classification and Hamada incidence-rank formula**. Everything else needed for all numbered results of ePrint 2026/1894 must be proved. All work remains local in this project; this plan prescribes no remote repository, publication, or deadline.

The permitted premises are concrete propositions in `formalization/OneAndAHalfJohnson/Targets/External.lean`:

- `AD21LowWeight p`: classification of low-weight words of the actual prime-field incidence span into at most two incidence rows, with the field-cardinality and dimension restrictions used in Theorem 3.3. This is not classification over an extension field and does not assume a common pair for an entire shortening.
- `HamadaBinaryRank`: the actual binary incidence-span rank at geometry field size 512 and dimension 5 equals one plus the specified matrix trace. This does not assume a kernel dimension or any probabilistic construction.

These are definitions of propositions, not axioms. Final theorems must take them as explicit hypotheses. For a fixed characteristic, the asymptotic result needs `AD21LowWeight p` only. The all-characteristic main theorem may take `∀ p, ∀ hp : Fact p.Prime, @AD21LowWeight p hp`. The concrete result needs `AD21LowWeight 2` and `HamadaBinaryRank`. Standard Lean logical axioms are distinct from these mathematical premises and must be reported by axiom checks.

**Completed conditional scope:** all numbered results are accounted for in [RESULTS.md](RESULTS.md), including Theorem 4.1. AD21 (Theorem 3.3) and Hamada remain explicit external hypotheses.

The development ledger below is historical. Its pending labels describe earlier stages and are superseded by RESULTS.md and the final validation receipts.

## Existing local coverage

| Module | Available mathematical content | Boundary |
|---|---|---|
| `Basic` | Actual linear codes, Hamming closeness/farness, exceptional coefficient sets, rate/distance/radius definitions, enlargement monotonicity | No code existence |
| `ScalarExtension` | Shortening commutation, dimension preservation, span and singleton/pair containment transfer | No base incidence classification |
| `Incidence` | Private-coordinate independence and overlap-sum criterion for incidence words | Generic support lemmas; actual geometry supplied separately |
| `GeometryIndependence` | Actual families of at most eight distinct geometric incidence rows are independent; incidence map is injective | Full shortening classification remains pending |
| `CodeDistance` | Strict lower/upper minimum-distance assembly and conditional syndrome-kernel exclusion | Nonzero kernel and small-word classification still needed |
| `Syndrome` | Genuine closeness witnesses, farness from low-weight exclusion, injective coefficient counting | Assumes the map, words, and exclusions |
| `SyndromeDirections` | Nonzero scaling preserves weight; syndrome normalization; independent nonvertical directions give injective slopes and exceptional counts | Missing map construction, unused directions, change of basis, and defining-word existence |
| `Thresholds` | `J₃/₂ < Γ < δ`, monotonicity of amplification, exact unique-decoding cutoff, concrete Johnson endpoint bound | No asymptotic parameter selection |
| `ConcreteArithmetic` | Exact integer/rational parameter checks, matrix trace, rate/radius arithmetic | No geometric rank identification or transcendental tail certification |
| `Geometry` | Actual projective points/subspaces and incidence spans; point/incident counts; exact row weight; intersection dimension and overlap bounds | No Grassmannian count or subspace-polynomial machinery |
| `SubfieldLines` | Exact dense-translate and nonzero subfield-line extraction inequalities, including counts in the base field itself | Constant-density and code-rescaling assembly remain |
| `Amplification` | Deterministic farness, closeness, count preservation, and code injectivity from a uniform weight estimate; supports alphabet reduction by restricting scalars | No random-map existence, concentration, or parameter choice |
| `Targets/Main`, `Targets/Base`, `Targets/External` | Explicit final/base contracts and the two permitted external propositions | Definitions only; base contracts are not additional permitted assumptions |
| `Shortening`, `GeometryShorteningBounds`, `GeometryShortening`, `MainTheorems/Shortening` | Complete common-pair/common-singleton shortening and exact ambient distance; full Lemma 3.4 from AD21 with threshold 4 | Explicit AD21 premise only; independently source-reviewed |
| `Supercode` | Exact-dimension enlargement avoiding a finite forbidden set by a deterministic greedy proof | Requires the explicit numerical size bound; independently inspected by root integrator |
| `CodeCompletion` | Crude Hamming-ball count and actual distance/two-word-distance preserving completion from an explicit numerical size bound | Individually kernel-checked; separate source review and paper defect/rate arithmetic remain |

`REVIEW.md` records independent source review for the core auxiliary modules. The Geometry/External and SyndromeDirections authors report their interfaces and local compilation; final centralized build and review evidence should be recorded separately, rather than inferred from this roadmap.

Coverage update: independent source review now also covers the latest Geometry, GeometryIndependence, SubfieldLines, SyndromeDirections, base/external contracts, and deterministic Amplification. Gate 1's point/incident counts, pairwise intersection bounds, and up-to-eight independence are available; Gate 3's combinatorial line extraction and deterministic image implications are available. The gates below specify the full end-state obligations; these completed ingredients should be reused, not reimplemented. Independent review does not substitute for the centralized final build.

## Priority dependency graph

An arrow means the right-hand node requires the left-hand node. Parallel branches may be developed independently, but downstream acceptance requires all incoming obligations.

```text
G1 Actual finite geometry counts/intersections ─┬─> G2 Incidence/sparse-shortening proof
AD21LowWeight ────────────────────────────────┘           |
ScalarExtension ────────────────────────────────────────┤
                                                       v
                                              Lemma 3.4 + extension transfer

G1 ─> P1 Subspace polynomials/power sums ─> P2 Explicit syndrome map (Lemma 3.5)
G1 ─> S1 Projective syndrome directions/unused axes/surjectivity
Lemma 3.4 + Lemma 3.5 + S1 + three-row kernel witness ─> Lemma 3.2

G1 ─> D1 Polynomial indicator dimension bound
Lemma 3.2 + F1 Field compatibility/subfield-line averaging ─┐
D1 + A1 Uniform random amplification + A2 Parameter choice ├─> A3 Pre-completion code
                                                        ┘
R1 Random-supercode preservation + A3 ─> Theorem 3.1 ─> Theorem 1.1
Theorem 1.1 + Thresholds + tolerance choice ─> Corollary 1.2

G1 + Lemma 3.4 + S1 + S2 Random syndrome map ─> C1 Concrete base code
HamadaBinaryRank + ScalarExtension + trace arithmetic ─> C2 Concrete dimension
C1 + C2 + C3 Weight-layer counts + C4 Certified tails ─> C5 Concrete amplified code
C5 + R1 + ConcreteArithmetic + Thresholds ─> Theorem 4.1
```

The concrete branch does **not** require Lemma 3.5: the paper uses a random syndrome map because the explicit map's field does not embed in the concrete field. Reusing the wrong branch would change the theorem's field size.

## Execution stages and acceptance gates

### Gate 1 — Finite geometry and Lemma 3.4

1. Prove finiteness and counts for points lying inside subspaces; identify incidence weights as `(Q^(m−2)−1)/(Q−1)`.
2. Prove distinct codimension-two subspaces intersect in dimension at most `m−3`, and derive support-overlap bounds. Prove the Grassmannian count and its asymptotic density, with all denominator positivity hypotheses.
3. Apply the generic private-coordinate theorem to collections of at most eight distinct incidence rows.
4. Prove the sparse linear-space classification used on pp. 8–9, including the binary triangle exception; rule that exception out by the actual union-support estimate.
5. Derive common two-row shortening containment from `AD21LowWeight`, then one-row containment and exact ambient minimum distance. Supply an explicit dimension threshold, not an extra “shortening classification” assumption.
6. Apply the existing scalar-extension transfer theorems to the actual incidence span. Prove embedded incidence words agree with incidence words over the larger coefficient field.

**Accept when:** a named Lemma 3.4 theorem, conditional only on AD21 and the paper's parameter hypotheses, states both shortening conclusions and the actual minimum-distance identity. No new external classification, intersection, or independence assumptions remain in that theorem.

For the concrete branch, additionally ensure this theorem applies at `Q=512,m=5`. The eventual-only `ShorteningStructure` contract permits an unspecified threshold greater than 5, so it alone is insufficient. Prove an explicit threshold covering that instance or a separately certified finite specialization. Alternative internal support arguments are allowed, but their hypotheses must be discharged rather than added to the external boundary.

**Gate 1 shortening acceptance update:** the named full theorem now exists, with explicit threshold 4, and has passed independent source review. The concrete-dimension applicability caveat is resolved. The separate Grassmannian-count/asymptotic-density work listed in this stage remains pending for later base-code existence.

### Gate 2 — Explicit parity checks and small-distance base code

1. Construct the finite field extension tower and identify the geometry vector space with the field of order `Q^m`.
2. Develop the needed subspace-polynomial facts: linearization, nonzero linear coefficient, top-two-coefficient uniqueness, and the three power-sum identities. These are internal proof obligations, not permitted additional external premises.
3. Define the explicit linear map using projective representatives; prove representative independence, nonzero syndromes, and pairwise independent directions. State `m ≥ 4` explicitly.
4. Complete the syndrome-direction infrastructure: count `q+1` directions, obtain two unused directions, choose a codomain basis, prove surjectivity, and select actual defining words. Resolve the whole-word-space versus subspace-domain map interface by a proved extension or equivalent restricted formulation.
5. Construct the three geometric rows with specified pairwise/triple intersections and their nonzero kernel combination. Use it both for nontriviality and the strict upper distance bound.
6. Assemble Lemma 3.2 using the existing distance, scalar-extension, normalization, and exceptional-count lemmas. Give explicit witnesses to “sufficiently large” and a positive uniform `c_Q`.

**Accept when:** Lemma 3.5 is proved without AD21 or Hamada; Lemma 3.2 is proved with AD21 only. Neither theorem may assume the required syndrome map or the final witness words as inputs.

### Gate 3 — General amplification and all-exponent quantifiers

1. Prove the gcd-based compatibility `Q^(2m) = (p^s)^r`, uniform boundedness of `r`, and growth of `m` for every sufficiently large `s`.
2. Partition nonzero extension-field elements into subfield lines and prove the exceptional-line averaging bound; prove nonzero rescaling preserves distance to a linear code.
3. Prove the polynomial indicator representation and degree/dimension bound for the actual incidence span.
4. Define the random coordinate samples and random linear functionals, prove the exact output success probability and independence, and establish the uniform concentration event by a finite union bound.
5. Prove a dedicated parameter-selection theorem with strict margins. Choose a slightly larger intermediate target distance to ensure strict `Γ(δ)` separation, then control integer locality rounding, finite `Q,m` errors, and `ξ`.
6. Obtain constants `A,D,s₀` uniformly before `s,N`; prove injectivity on the base code before using image minimum distance; transport all coset and exceptional witnesses.

**Accept when:** a pre-completion code exists for every exponent and block length in the main contract, with actual distance error and strict word-separation bounds, conditional only on AD21. No unproved concentration lemma, asymptotic estimate, or parameter-selection proposition is added to the external boundary.

### Gate 4 — Near-MDS completion and asymptotic results

Implementation update: `Supercode` and `CodeCompletion` use a deterministic greedy alternative to random-supercode counting. The cardinality bound `(2^n q^(d−1) + 2^(n+1) q^b) q^K < q^n` suffices for exact dimension, preserved minimum distance, and preserved word separation. This is an allowed replacement of the probabilistic proof, not an extra external premise. The remaining completion work is to derive this numerical condition from the paper's chosen defect and to finish uniform rate arithmetic. Random-supercode membership probabilities need not be proved if the deterministic route establishes every required conclusion.

1. Count superspaces or equivalently use quotient spaces to prove the exact membership probability for a uniformly chosen supercode of a specified dimension.
2. Prove the Hamming-ball count and simultaneous distance/coset-preservation estimate; handle the already-small-defect branch.
3. Prove the uniform defect bound, including the ceiling term `1/N`, using the block-length lower bound.
4. Assemble a theorem proving `AsymptoticConclusion p δ ρ η`; then the all-prime `MainTheorem`. Reuse the same proof for the duplicate numbering 1.1/3.1 rather than introducing a divergent contract.
5. Prove Corollary 1.2 from the main theorem and exact cutoff comparison. For the prose consequence about the actual code's unique-decoding radius, choose tolerance smaller than the positive gap between target `δ/2` and `ρ`.

**Accept when:** named conditional proofs of Theorems 1.1/3.1 and Corollary 1.2 use AD21 only, preserve the full quantifier order in `Targets/Main.lean`, and establish the claimed actual-code consequence.

### Gate 5 — Concrete example

1. Prove the random two-check map's pairwise dependence probability and union bound for the actual incidence family. Apply the existing exact rational probability comparison.
2. Build the concrete base code, defining vectors, `B` distinct exceptions, and nonzero low-weight codeword using geometry and AD21. Do not substitute the asymptotic explicit syndrome field.
3. Apply `HamadaBinaryRank`, existing matrix arithmetic, scalar-extension dimension preservation, and rank-nullity to obtain the concrete kernel dimension.
4. Prove shortening Singleton bounds and affine-coset support-layer counts. Prove the relative-entropy binomial tail theorem and derivative estimates used in the paper.
5. Certify every concrete real/logarithmic inequality by kernel-checkable bounds; sum the finite failure probabilities explicitly to a value below one. Numerical experimentation may guide bounds but is not acceptance evidence.
6. Apply the generic supercode completion theorem with the concrete defect; finish the exact rate interval, exceptional count, Johnson comparison, unique-decoding slack, and count-to-length ratio.

**Accept when:** a named theorem proves `ConcreteTheorem` from AD21 at characteristic two and Hamada only. It must produce an actual linear code and fixed words at the stated field size and block length, not merely verify arithmetic conditional on their existence.

## Numbered-result ledger at completion

| Paper item | Required final evidence | Permitted external inputs |
|---|---|---|
| Theorem 1.1 | Proof of `MainTheorem` with full uniform constants | AD21 in each prime characteristic |
| Corollary 1.2 | Proof of `UniqueDecodingCounterexamples` and actual unique-radius consequence | AD21 via main theorem |
| Theorem 3.1 | Same main theorem proof, explicit paper cross-reference | AD21 |
| Lemma 3.2 | Actual small-distance base-code existence and all three bounds | AD21 |
| Theorem 3.3 | Explicit accepted external premise and correctly instantiated wrapper | AD21 itself |
| Lemma 3.4 | Two-/one-incidence shortening and ambient minimum distance | AD21 |
| Lemma 3.5 | Constructed explicit parity map with both direction properties | None |
| Theorem 4.1 | Proof of exact `ConcreteTheorem` plus stated quantitative consequences | AD21 at two; Hamada |

## Final local acceptance checks

- Run the full default `lake build` from `formalization`; import every intended public module through the library root. Rebuild after the last proof edit.
- Add a local checks module with `#check` for each numbered-result proof and `#print axioms` for those proofs and substantive auxiliary roots. Record the resulting accepted standard logical axioms; reject `sorryAx` and custom result axioms. Explicit AD21/Hamada theorem arguments are permitted premises, not hidden axioms.
- Scan local proof sources for `sorry`, `admit`, custom `axiom`, trust-bypass attributes, and unsafe/native-decision shortcuts; inspect any matches rather than treating prose mentions as failures.
- Independently review final theorem types against the PDF: all exponent/block-length quantifiers, prime characteristics, constants chosen before growth variables, strict inequalities, actual code minimum distance/rate, fixed defining words, and distinct exceptional coefficients.
- Verify every final nonlogical hypothesis is either a paper parameter restriction or one of the two accepted external premises. Intermediate conditional assembly lemmas must not leak additional assumptions into final statements.
- Keep the paper-to-declaration ledger current. Distinguish definitions, verified auxiliary results, accepted external inputs, and proved numbered results. Update `REVIEW.md` to supersede its current “all numbered results pending” statement only when the corresponding final proofs exist and pass checks.
- Deliver only local artifacts and accurate remaining-work status. A successful auxiliary-module build is not completion of this accepted scope.

## Integration checkpoint

Further completed supporting modules: exact Grassmannian cardinality; triple-incidence kernel witness; actual subspace-polynomial shape and moments; polynomial incidence-rank bound; uniform sampled-map existence; polynomial Hoeffding threshold; subfield reduction; compatible finite-field towers; strict amplification parameter selection; actual image-distance and near-MDS completion assembly. The coarse rank bound `(m+1)^(2(Q−1))` is sufficient for the main polynomial-length statement but does not claim the paper's sharper exponent.

These are individually compiled ingredients. The centralized all-declaration receipt must be refreshed after the ongoing main/concrete proof edits before treating it as current.

## Main theorem completion

`MainTheorems.conditionalMainTheorem` proves the exact characteristic-specific contract; `mainTheorem_of_AD21` proves the full all-prime contract; `uniqueDecodingCounterexamples_of_AD21` proves Corollary 1.2. `actual_unique_radius_of_AD21` additionally proves the exceptional radius is below half the constructed code's actual distance. Constants are chosen before all growing parameters; rate error uses `M=6`. The final construction actually produces distance above the target δ and below δ+η, using the analytically justified overshoot.

The root integrator independently inspected the at-size assembly and final wrappers. Individual compilation and axiom checks pass; see `validation/main-theorem-receipt.md`. The remaining numbered theorem is 4.1. Its concrete base, exact rank, sharper Chernoff inequalities, numerical certificates, and exact-rate completion are available, while weight-layer probability aggregation and final assembly are ongoing.
