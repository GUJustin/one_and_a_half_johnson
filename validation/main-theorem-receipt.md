# Main theorem validation receipt

Theorems 1.1 and 3.1 and Corollary 1.2 are now proved conditional only on the characteristic-specific AD21 classification. The only input mathematical premise is `Targets.AD21LowWeight p`; Hamada is not needed for these asymptotic results.

`MainTheorems.conditionalMainTheorem` has the exact `Targets.ConditionalMainTheorem` type. `mainTheorem_of_AD21` and `uniqueDecodingCounterexamples_of_AD21` have exact `Targets.MainTheorem` and `Targets.UniqueDecodingCounterexamples` conclusions. `actual_unique_radius_of_AD21` additionally guarantees the exceptional radius is below half the constructed code’s own distance.

The construction chooses fixed a,t,ξ before s,N, then uses degree D=2(p^a−1)+1, density c=1/(8(p^a)^4), and rate coefficient M=6. The actual field tower, geometric base code, subfield extraction, random linear map, simultaneous Hoeffding concentration, genuine minimum-distance bounds, and near-MDS supercode are assembled. No sampler or code-existence hypotheses remain at the public main theorem boundary. The proof actually works without using N<p^s, while retaining this premise in the requested exact contract.

Validation: both sources compiled with the pinned `lake env lean`, producing local oleans. `/tmp/one_half_main_audit.lean` typechecked exact-contract examples and printed axioms for all six public construction/main/corollary declarations. Every root reports only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or custom axioms.

Root agent independently reviewed the at-size construction and main wrapper before compilation and found no mathematical issue. The later actual-radius corollary is a direct tolerance reduction and remains available for final independent review.

Source SHA-256:

- `formalization/OneAndAHalfJohnson/AsymptoticConstruction.lean`: `a42f6fd38ff6d3d4e230e390f92d59238b809ed6c18ff7f30410916a1a07ff97`
- `formalization/OneAndAHalfJohnson/MainTheorems/Main.lean`: `374bba1d71f3da2d6137cc35cb184ff29a5e587b7f60d3b4d66c36764844b709`
