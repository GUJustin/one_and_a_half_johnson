# Independent source review

**Latest coverage update:** the final section below records a completed conditional proof of full Lemma 3.4. Earlier statements that all numbered results were pending are historical snapshots and are superseded for that lemma. Theorem 3.3 remains the accepted AD21 external premise. Other numbered existence results remain pending.

Reviewed on 2026-09-21: `formalization/OneAndAHalfJohnson/Basic.lean`, `Syndrome.lean`, and `ConcreteArithmetic.lean`, against the public paper extraction `/tmp/eprint-2026-1894.txt`. The final arithmetic source inspected uses `module`, public imports, and `@[expose] public section`, and includes `hamada_matrix_trace`. This review changed no proof files and ran no builds or shared Lean processes. Compilation reports belong to the implementing agents; this is an independent mathematical/source review.

## Verdict

The inspected declarations are faithful **conditional support lemmas and exact arithmetic checks**. No mathematical defect was found in their current conclusions. They do not prove Lemma 3.2, either main theorem, or Theorem 4.1. Their source documentation accurately states that limitation. Full paper completion remains pending; see `PAPER_AUDIT.md` for the missing obligations.

## Mathematical review

| Component | Finding | Status |
|---|---|---|
| `Close`, `Far` | Quantify over actual codewords and multiply thresholds by the actual coordinate cardinality. For a nonempty coordinate set these express the paper's closeness and strict farness (p. 6). There is no rounded radius or proxy count. | Pass; eventual bridge to a minimum-distance-to-code API remains useful. |
| `exceptional` | Filters actual distinct field coefficients for the fixed words `f,g` and actual closeness witnesses. Matches `Z_ρ` on p. 6. | Pass. |
| `relativeDistance` | Uses ArkLib's `Code.dist`; inspected `Basic/Distance.lean` and `Basic/LinearCode.lean`. The latter proves equality with minimum nonzero Hamming weight. ArkLib returns zero for the zero code, whereas the paper's written minimum over nonzero words does not define that case. | Pending integration condition: establish a nonzero code when connecting paper statements. No current theorem misuses this definition. |
| Empty coordinate sets | The basic API permits them. Then closeness is automatic and strict farness is impossible, unlike ordinary division-based relative distance conventions. The module header explicitly limits its relative-distance interpretation to nonempty coordinates. | Resolved by accurate documentation; future main statements must enforce positive block length. |
| `rate`, `johnson`, `gamma`, `amplify` | Dimension/cardinality and real exponents match pp. 2, 6, 12. Real exponent notation has the intended real type. | Pass; radius comparison lemmas remain pending. |
| Monotonicity and exclusion lemmas | Code enlargement preserves witnesses and exceptional coefficients; strict farness excludes closeness. | Pass. |
| `hammingDist_sub_eq_norm` | Correct translation identity, including subtraction orientation via symmetry. | Pass. |
| `close_of_equal_syndrome` | Constructs the actual codeword `v-u` in `D ∩ ker ψ`; closeness follows from the actual weight of `u`. | Pass; faithfully captures p. 11–12 algebra. |
| `close_of_normalized_syndrome` | Uses the concrete normalized syndromes `(1,0)`, `(0,1)`, `(1,z)` to give a genuine exceptional witness. | Pass. |
| `card_exceptional_ge_of_syndromes` | Requires an explicit injection of the indexing type into the field and supplies witnesses for every coefficient in its image. Does not replace cardinality by an unrelated measure. | Pass; incidence directions and their injection must still be constructed. |
| `far_of_syndrome_exclusion` | Correctly derives farness from low-weight syndrome exclusion, using `v-c` and membership in `D`. | Pass; geometric low-weight exclusion remains an explicit hypothesis. |
| Syndrome map domain | The paper defines `ψ : D → F²`, while these lemmas assume `ψ : (I → F) →ₗ[F] F²`. A linear map on a subspace extends over a field, so this is a sound conditional formulation, but application needs an extension theorem or a subspace-domain variant. | Pending integration bridge; not a logical defect in present theorems. |
| Concrete integer/rational evaluations | Constants agree with pp. 16–20: raw length, incidence weight/count, cutoffs, syndrome union-bound numerical value, completion defect, transition exponent, completion room, rate interval, and radius gap. Decimal targets are exact rational fractions. | Pass as arithmetic-only statements. |
| `integral_coset_cutoff` | Correctly turns `4·262657/3 < w`, for natural `w`, into `350210 ≤ w`. | Pass. |
| `completion_rate_identity` | A rational algebraic identity. It does not assert that the displayed numerator is an actual code dimension or prove natural-subtraction side conditions. | Pass with explicitly conditional scope. |
| `hamada_matrix_trace` | Evaluates the trace as `3,604,584,375`; the paper then adds one for ambient incidence rank and subtracts two for the kernel. It does not claim to prove Hamada's rank theorem. | Pass with accurate scope. |

## Trust review

The reviewed local source files contain no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, or `trustCompiler` occurrences. Proof bodies use ordinary kernel-checkable reasoning and arithmetic tactics (`norm_num`, `linarith`, `ring_nf`, `simp`, finite-set cardinality, and linear-map identities). `noncomputable`, classical decidability, and public module exposure are not trust bypasses.

This source scan does **not** certify the transitive axiom closure of imported declarations. A final centralized build and `#print axioms` checks should confirm that each exported theorem depends only on the project's accepted standard logical axioms, with no `sorryAx` or custom external-result axioms. No shared build was run by this reviewer, as requested.

## Remaining completion boundaries

- No incidence-code construction, AD21 classification, scalar-extension shortening theorem, or explicit syndrome construction has been discharged by the reviewed modules.
- No amplification concentration, parameter-limit theorem, or random-supercode existence theorem has been discharged.
- The concrete arithmetic does not certify Hamada's geometric rank formula, binomial tail bounds, logarithm/relative-entropy inequalities, or the existence of the concrete code.
- No claim that all paper results are formalized is warranted by these modules. The present support lemmas can be reported as completed only with their stated hypotheses and arithmetic scope.

No blocking source defect was found. Pending items above are explicit mathematical integration and completeness obligations, rather than requests to weaken or remove valid current results.

## Additional review: scalar extension, thresholds, and theorem contracts

Independently reviewed `ScalarExtension.lean`, `Thresholds.lean`, and `Targets/Main.lean` after their implementation. No build was run by this reviewer. The integrator reports that the scalar-extension proof compiled and its axioms were checked; those reports are distinct from this source review.

### Scalar extension

`extendCode_inf_supported` proves exactly the missing scalar-extension/shortening identity identified on p. 11 of the paper, for an arbitrary coordinate set and a finite-dimensional extension of fields. Its definitions model the actual span of coordinatewise embedded base-code words and actual coordinate support.

The argument is mathematically sound: span induction shows that every base-field linear coefficient projection of an extended word lies in the base code. In the scalar multiplication case, composing the coefficient functional with multiplication by the extension-field scalar is the required base-field linear operation. A finite basis of the extension reconstructs the word as a finite sum of its embedded coefficient words. Zero coordinates remain zero under all coefficient projections, so those words belong to the shortening. The reverse inclusion follows from embedded generators and closure of the support subspace.

**Status: resolved.** The earlier review item saying no scalar-extension shortening theorem had been discharged is superseded for this identity. This proves neither preservation of code dimension nor the other incidence and amplification obligations. There is no requirement that the coordinate set be finite, and the finite-dimensional field-extension hypothesis is appropriate for the paper. No mathematical defect or trust bypass was found.

### Threshold lemmas

- `johnson_lt_gamma` and `gamma_lt_distance` correctly compare powers of a base strictly between zero and one, proving the two inequalities stated on p. 2.
- `amplify_zero` is correct for every natural locality, including zero. Its comment mentions endpoints, but the declaration proves only the zero endpoint; this is a minor documentation imprecision, not a mathematical issue.
- `amplify_mono` is sound with the stated hypotheses `u ≤ v ≤ 1`: both complementary bases are nonnegative. A lower bound on `u` is unnecessary for this algebraic monotonicity statement.

**Status: pass.** The unique-decoding cutoff characterization involving `3 − √5`, the positive strict amplification margins, and uniform parameter selection remain pending.

### Full main and concrete contracts

The target declarations are definitions of propositions, explicitly labeled **NOT PROVED**, and are neither axioms nor proofs. Their quantifiers preserve the important content of the paper:

- `A,c,M,D,s₀` are chosen before both exponent and block length, so the exceptional density and rate-error bound are uniform over all admissible `s,N`.
- Every sufficiently large exponent and every block length `A s^D ≤ N < p^s` is included; there is no subsequence weakening.
- The existential code and fixed pair `f,g` precede the exceptional coefficient count.
- Relative-distance approximation, strict defining-word farness, and a positive constant exceptional density have the correct inequalities.
- The absolute rate-error bound `M/s` is a faithful explicit version of the paper's uniform big-O term. Taking `M>0` instead of merely nonnegative does not weaken or obstruct the intended theorem.
- Nonzero codes are explicitly required. Positivity of block length follows from `A>0`, `s≥s₀≥1`, and the lower bound, resolving the zero-code and zero-length concerns for these main targets.
- Quantifying over every finite field model of the given cardinality is a mathematically equivalent field-isomorphism-invariant formulation. A future construction in one model needs the standard transport step to prove this version.
- The concrete target has exactly the stated block length, field cardinality, distance/rate intervals, strict word-distance bound, exceptional radius, and integer exceptional-count lower bound. The explicit unique-decoding-radius inequality is also faithful.
- `UniqueDecodingCounterexamples` records the corollary's quantitative conclusion with the correct target-distance and radius hypotheses. The additional prose consequence that a constructed code fails *inside its actual unique-decoding radius* still requires choosing a sufficiently small distance tolerance and relating target `δ` to actual `relativeDistance C`; that consequence is not separately proved by this definition.

**Status: pass as unproved contracts.** The presence of these definitions must not be counted as theorem completion. Their scope addresses the principal asymptotic and concrete statements; the intermediate incidence-construction results are still governed by the remaining inventory in `PAPER_AUDIT.md`.

The added sources contain no local `sorry`, `admit`, `native_decide`, `unsafe`, `implemented_by`, or `trustCompiler`. The only `axiom` text found by the source scan in this additional scope is the target header explicitly saying the definitions are not axioms. No new blocking issue was found.

## Final additional review: dimension, incidence, minimum distance, and cutoff

Reviewed the latest `ScalarExtension.lean`, `Incidence.lean`, `CodeDistance.lean`, and complete `Thresholds.lean`, including `johnson_lt_half_iff` and `concrete_johnson_upper`. No builds were run. `Targets/Main.lean` is unchanged from the preceding review.

| Added result group | Mathematical assessment | Status |
|---|---|---|
| `finrank_extendCode` | A base-code basis remains independent after coordinatewise field embedding, and its embedded vectors span the extension. Finite coordinates ensure a finite-dimensional base code; the extension field itself need not have finite degree for this result. The statement proves the actual dimension identity needed on p. 14. | Pass; dimension-preservation obligation resolved. |
| `extendCode_mono`, `extendCode_span` | Correct functoriality and generator-span identities for the specified coordinatewise extension. No geometric assumptions are hidden in the notation. | Pass. |
| `shortened_extendCode_le_span`, singleton/pair specializations | Correctly combine shortening commutation with span transfer. These give precisely the base-field-to-extension-field containment implication needed when applying Lemma 3.4 on p. 11. The base containment remains an explicit hypothesis. | Pass; transfer implication resolved, incidence classification still pending. |
| `linearIndependent_of_private_coordinates` | Isolating one nonzero coordinate for each family member proves independence by evaluating any finite linear relation at that coordinate. Correct for arbitrary index and coordinate types over a field. | Pass. |
| `exists_private_point_of_overlap_sum_lt` | The union of overlaps has cardinality at most the sum of overlap cardinalities. A strict deficit against the chosen set supplies a private point. The strict inequality is retained in the statement. | Pass. |
| `incidence_linearIndependent_of_overlap_sum_lt` | Correct assembly of the preceding arguments for actual zero/one incidence words. It does not assume or claim finite-projective intersection formulas. | Pass; generic independence ingredient of p. 8, not the specialized eight-vector result. |
| `code_distance_gt_of_nonzero_weights` | Correctly uses a nonempty set of attainable upper bounds on nonzero word weights to identify the natural infimum and transfer a strict lower bound. Explicit nonzero-code witness avoids ArkLib's zero-code distance convention. | Pass. |
| `code_distance_le_of_nonzero_word` | An actual nonzero codeword provides an actual minimum-distance upper bound. | Pass. |
| `syndrome_kernel_distance_gt` | Actual ambient-word exclusion from the kernel gives the strict distance bound, with independent nontriviality hypothesis. | Pass. |
| Pair-span classification assembly | The hypothesis explicitly supplies two generators, membership in their span, and injectivity of the syndrome map on that span. Injectivity compares the word to zero, proving exclusion. This is a valid generic assembly lemma; it does not prove the geometric classification or derive injectivity from independent incidence syndromes. | Pass with conditional scope. |
| `johnson_lt_half_iff` | Correct exact characterization on `0 < δ < 1`. The proof cubes nonnegative quantities, uses the real cube-root identity, and reduces to the quadratic cutoff `δ < 3 − √5`. | Pass; the earlier pending elementary cutoff obligation is resolved. |
| `concrete_johnson_upper` | Certifies the precise real inequality at `δ = 4511/10000` through rational cubing, not floating-point approximation. This is the endpoint comparison from p. 20. Monotonicity/application to the constructed code remains part of later assembly. | Pass. |

The `amplify_zero` comment now correctly describes only zero weight, resolving the earlier minor documentation observation. The latest four reviewed modules have no occurrences of `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, or `trustCompiler` in their source. Final compilation and transitive axiom checks remain the integrator's responsibility.

### Final coverage distinction

The auxiliary results are substantive: scalar extension commutes with shortening and preserves dimension; containment transfers across scalar extension; private-support incidence families are independent; actual minimum-distance and syndrome implications are established; both symbolic and concrete Johnson-radius comparisons are certified; exact concrete arithmetic and exceptional-syndrome assembly have been checked.

**Every numbered paper result remains unproved in full:** Theorem 1.1, Corollary 1.2, Theorem 3.1, Lemma 3.2, Theorem 3.3, Lemma 3.4, Lemma 3.5, and Theorem 4.1. In particular, the elementary cutoff comparison alone is not Corollary 1.2, scalar-transfer and private-support lemmas alone are not Lemma 3.4, and generic syndrome assembly alone is not Lemma 3.2. The external AD21 and Hamada results, specialized incidence geometry, syndrome construction, concentration/existence arguments, parameter quantifiers, and near-MDS completion remain essential outstanding work.

No blocking mathematical or source-level trust issue was found in this final review scope.

## Subsequent review: actual geometry, dense lines, and deterministic amplification

Reviewed the complete current sources of `SubfieldLines`, `SyndromeDirections`, `Geometry`, `GeometryIndependence`, `Targets/External`, `Targets/Base`, and `Amplification`. No builds or proof edits were performed by this reviewer. Amplification was still being compiled by the integrator at review time; the following judgments concern mathematical source fidelity, not an independent compilation claim.

### Results reviewed

- **Dense subfield lines:** `exists_dense_translate` is a valid finite-group averaging argument, even if the indexed family has repetitions. Its specialization to field units uses genuine distinct nonzero base-field scalars. `exists_dense_subfield_line_coefficients` transfers the exact count to a subset of the base field, correctly excludes zero, and retains a nonzero multiplier. This proves the combinatorial extraction inequality on p. 13 without assuming a line partition. Conversion to the paper's real constant-density bound and preservation of source distance under rescaling still need assembly.
- **Syndrome directions:** normalization by the inverse first coordinate has the correct slope `b/a`; nonzero scaling preserves weight; equality of slopes contradicts independent syndrome pairs. The exceptional-set theorem counts actual distinct coefficients and uses actual nearby codewords. It does not provide unused directions, a change of basis, surjectivity, or the original words/maps.
- **Actual projective geometry:** `Point`, `CodimTwo`, and `Incident` faithfully represent one-dimensional points and codimension-two vector subspaces. `incidentEquiv` identifies the actual incident set with projectivization of the subspace. Point and incident counts, incidence weight, intersection dimension bounds, and overlap bounds are sound and use the geometry field's cardinality independently of the coefficient field.
- **Small-family independence:** `incidence_rows_independent_of_card_le_eight` specializes the generic private-support argument to the actual geometric rows, with `Q>32`, `m≥4`, distinct subspaces, and arbitrary coefficient field. The seven-overlap bound is strict as required. `incidenceWord_injective` correctly recovers subspace membership using all nonzero projective representatives. This resolves the specific “up to eight incidence rows are independent” ingredient on p. 8, not the remainder of Lemma 3.4.
- **Deterministic alphabet-reducing amplification:** the map is genuinely linear over the output field, and the source code is explicitly restricted to that field before taking its image. Farness is proved for every actual image codeword. Closeness uses actual source witnesses with output-field challenges, and the count theorem preserves a fixed finite set of distinct challenges. All required positive-length divisions have explicit hypotheses. The injectivity theorem correctly uses positivity of the amplified lower weight on nonzero differences before minimum-distance assembly. These statements establish deterministic implications from a uniform weight estimate, not the random map's existence or concentration.

### External-premise and base-contract audit

`AD21LowWeight` and `HamadaBinaryRank` are faithfully narrow propositions over the actual incidence span. They assume neither common shortening pairs nor extension-field classification, constructed-kernel rank, random maps, or code existence. They remain the **only two permitted external mathematical inputs** for the accepted conditional scope. Their declarations are definitions, not axioms. An all-characteristic theorem should quantify the AD21 premise over prime characteristics; a fixed-characteristic theorem should not require unrelated instances.

`SmallDistanceBase` has one positive density constant and one dimension threshold chosen before all later dimensions and finite-field models. Its strict code-distance and defining-word bounds and nonstrict exceptional count agree with Lemma 3.2. It is parameterized by `p`; a proof identifying it with the paper must require that `p` is prime, as the intended theorem wrapper does.

`ShorteningStructure` correctly requires a common pair for each whole shortening, not a separately chosen pair for each word. It includes the one-row containment and exact minimum distance. **Integration caveat:** its eventual threshold is not bounded by 5. Proving this contract alone cannot justify its use at the concrete `Q=512,m=5` parameters. Supply a sufficiently strong explicit threshold or prove that finite specialization separately.

`SyndromeSeparation` correctly uses the actual extended ambient code as the domain and requires both nonzero syndromes and pairwise independence. Its field-model invariance and missing explicit embedding of the geometry field require finite-field transport during its eventual construction, but do not invalidate the statement. The previously identified restricted-domain versus whole-word-space assembly bridge remains pending.

All three base contracts are labeled unproved and do not enlarge the accepted external assumption boundary. No full shortening theorem is claimed: an independent alternative support-lemma route under development is still an internal proof task, not an additional assumption or completed target.

### Status and trust

No blocking mathematical defect was found. Source scans of this review scope found no proof admission or trust-bypass construct; `axiom` occurs only in explanatory text denying that the external propositions are axioms. Full builds and transitive axiom checks remain centralized with the integrator.

The geometry weights/intersections, specialized small-family independence, dense-line extraction, and deterministic amplification implications are substantive additions. All numbered paper results still lack completed final conditional proofs; the classification input itself is accepted externally. Grassmannian counts, shortening structure, explicit syndrome construction, uniform random amplification, quantitative parameter choice, supercode existence, and the concrete probability analysis remain major obligations.

## Completed conditional Lemma 3.4: independent review

Reviewed `Shortening.lean`, `GeometryShorteningBounds.lean`, `GeometryShortening.lean`, and `MainTheorems/Shortening.lean` after the author reported compilation and an axiom check. No build was run by this reviewer for this review. The theorem

`OneAndAHalfJohnson.MainTheorems.shorteningStructure_of_AD21`

proves the complete `Targets.ShorteningStructure p` contract from `AD21LowWeight p` alone. It explicitly chooses `m₀ = 4`. This resolves both the common-shortening obligation and the previously flagged applicability issue at `Q=512,m=5`.

The proof is faithful to the paper's conclusions while using an alternative internal argument. Local six-row independence gives uniqueness of sparse coefficient representations. A maximal sparse support contains all others: disjoint additional support contradicts maximality via the sum; a genuinely overlapping pair would force the coordinate support to include the union of three incidence rows outside their triple intersection. The exact counting bound excludes that possibility at the AD21 cutoff. This handles characteristic two and possible coefficient cancellation without assuming it away.

At the smaller threshold, the symmetric difference of two distinct rows is too large for a genuine two-row combination. Sparse uniqueness then yields one common row for the entire shortening. The exact ambient distance follows by exhibiting an incidence word of weight `e` and excluding nonzero words below `e` using that common-singleton result. Codimension-two subspace nonemptiness, positive incidence weight, the numerical cutoff comparison, and the actual Hamming-distance infimum are all discharged internally.

**Verdict: full Lemma 3.4 is conditionally proved under exactly the accepted AD21 premise.** The contract is not simply assumed, and Hamada or any other unproved paper conclusion is not an input. No blocking mathematical issue was found in the inspected proof chain. The author reports the final theorem's axiom closure as `propext`, `Classical.choice`, and `Quot.sound`; centralized checks should retain that evidence.

The classification used as Theorem 3.3 is still an accepted external input, not an internal proof. Lemma 3.2, Lemma 3.5, Theorems 1.1/3.1 and 4.1, and Corollary 1.2 remain unproved in full.

## Authored completion modules awaiting separate review

This review agent subsequently authored `Supercode.lean` and `CodeCompletion.lean`; the following is an implementation record, **not an independent review of its own proofs**. The root integrator independently inspected the greedy supercode argument and reported no issue. `CodeCompletion.lean` still requires separate source review.

- `Supercode` proves finite-forbidden-set avoidance while enlarging to an exact prescribed dimension, under `|B| q^K < q^(dim V)`, by a greedy union-of-spans argument.
- `CodeCompletion` proves the crude Hamming-ball bound `2^n q^r`, forms the actual forbidden low-weight and two centered-ball sets, and constructs a supercode preserving actual minimum distance and both strict absolute word-distance bounds under the explicit numerical size condition.
- Both modules were individually kernel-checked by their author with axiom output containing only `propext`, `Classical.choice`, and `Quot.sound` for their exported theorem roots. This does not complete the paper's rate/defect arithmetic or any numbered existence theorem.

## Subsequent independent reviews and completed base results

The syndrome agent independently reviewed the original full Lemma 3.5 chain: polynomial shape and top-coefficient uniqueness, all required moments, projective-line partition, and compatible finite-field tower. No mathematical defect or additional premise was found. The integrator read the strengthened first-coordinate theorem and its restriction wrapper; the stronger result retains the actual ambient linear map.

The integrator inspected `MainTheorems/BaseConstruction.lean` and `IncidenceRankBound.lean`. The base construction uses actual unused affine syndrome slope, nonzero first coordinates, and the proved triple-incidence kernel word. It returns membership of both source words and the code in the actual scalar-extended incidence code. Its public wrapper proves the complete Lemma 3.2 contract under AD21 only. The polynomial rank argument uses actual projective representatives, two quotient-coordinate functionals, finite-field zero tests, and span powers; coefficient extension preserves rank. No hidden rank assumption was found.

The syndrome agent independently source-reviewed `AmplificationLimits`, `AmplificationParameters`, `RandomAmplification`, `AmplificationSize`, and `SubfieldReduction`, reporting no blocking issue. The overshoot makes the Γ margin strict; all amplification constants precede growing parameters; the sample space is an actual product of uniform finite row distributions; subfield extraction counts distinct coefficients and preserves farness by nonzero scaling. These supporting results are not alone completion of the main existence theorem.

The integrator also inspected the probability and completion proof bodies. Individual compilation and axiom reports are positive; final centralized receipts remain required after assembly.

## Main theorem and actual-radius corollary: integrator review

The root integrator read all of `AsymptoticConstruction.lean` and `MainTheorems/Main.lean`, including the final reduced-tolerance corollary. No mathematical issue was found. The actual code, two source words, and exception set are chosen before challenges; field models are arbitrary; all constants are fixed before s and N. The point-base theorem supplies membership in the actual incidence span, whose proved polynomial rank controls the union bound. The actual sampled linear map is injective on the code before minimum-distance transfer. Completion preserves exact distance and strict Γ-farness, with rate error≤6/s. No external input beyond AD21 is used.

The stronger corollary chooses `min η ((δ−2ρ)/2)` before all growth variables and derives `ρ < relativeDistance C/2`; it is not merely a comparison with the target limit δ. These files compile warning-free and their six audited roots have only the standard logical axioms, as recorded in `validation/main-theorem-receipt.md`.

The integrator also read the finite-syndrome hyperplane proof and concrete rank-nullity specialization. The alternative deterministic construction uses `B²<q` and pairwise independence of actual incidence rows; the Hamada premise applies to the actual binary incidence code and is transferred by proved scalar-extension dimension preservation. No extra rank premise is introduced.

## Final integration review

The root integrator reviewed ConcreteFailureSums and ConcreteLayerCounting against the actual finite nonzero-codeword and affine-coset families. The low-weight empty layers, shortened Singleton counts, global dimension counts, and natural-number subtraction boundary agree with the sampler's failure sums. The final wrappers have no remaining analytic assumptions.

ConcreteTailEnvelopes was reviewed for the exact finite-field sampling correction, derivative signs, interval endpoints, and the beta transition below minimum code distance. Its uniform beta envelope handles both zero and positive field-count exponents. The final concrete assembly was reviewed against the complete ConcreteTheorem contract; it uses only AD21 and Hamada. Independent agent reviews cover the Chernoff/sampler and construction/completion interfaces.

These completed results supersede pending status notes in earlier review entries. Final machine validation is recorded in validation/axioms.json, validation/dependencies.json, and validation/lean.log.

Final central validation passed: all 72 modules built, all 485 explicitly named declarations use only the allowed standard axioms, and all 20 dependency revisions match their pins without tracked changes. The checker accepted a proved control and rejected both a sorryAx control and missing output.
