# Concrete theorem validation receipt

Theorem 4.1 is fully proved by `MainTheorems.concreteTheorem_of_AD21_Hamada`, with exact target type `AD21LowWeight 2 → HamadaBinaryRank → ConcreteTheorem`. `MainTheorems.conditionalConcreteTheorem` has exactly `Targets.ConditionalConcreteTheorem`.

The result quantifies over every field model of order 2^128 and constructs a nonzero code of length 2^36 with all exact distance, rate, defining-word farness, unique-decoding-radius and exceptional-count inequalities in the target. The proof uses actual PG(4,512) coordinates, actual incidence-span rank, separating syndromes, complete support-layer Chernoff sums for the nonzero code and both affine cosets, actual independent uniform row sampling, and exact-defect supercode completion. No sampler-existence, numeric, or construction premises remain beyond AD21 and Hamada.

The helper `concrete_code_consequences` proves the p. 20 comparisons for the actual output code: Johnson threshold below .1816, unique-decoding gap greater than .03935, and more than 2^18 times the block length many exceptional challenges.

All listed sources compile warning-free with the pinned Lean toolchain. `/tmp/one_half_concrete_final_audit.lean` checked both exact-contract examples and audited the full concrete theorem, conditional contract, actual-code consequences, sampling, deterministic construction, completion, and derivative helper. Every root reports only `propext`, `Classical.choice`, and `Quot.sound`. No custom axioms or `sorryAx` occur. Root and syndrome agents independently reviewed the concrete sampling and assembly sources and reported no mathematical issues.

Source SHA-256:

- `formalization/OneAndAHalfJohnson/ConcreteCompletion.lean`: `42a3f42490a79afbc5c1e566b8d8a5a7bdadd47e24911cd0f6080be08c818b9a`
- `formalization/OneAndAHalfJohnson/ConcreteConstruction.lean`: `1050664108657bc65c82f07def7839847f332f8516aa65b54fa4bea5475b2420`
- `formalization/OneAndAHalfJohnson/ConcreteSampling.lean`: `8ce44d18515a6874b94603a177d28d77cf89815e96f1432cdfd028074595cb77`
- `formalization/OneAndAHalfJohnson/ConcreteLayerDerivative.lean`: `c8abe19ec44ace33ab1c888451e1513a1b86c6c86813e96cb8251e1ba90f5290`
- `formalization/OneAndAHalfJohnson/RefinedRandomAmplification.lean`: `61c98296bf75e93a6f67b476a4565351114cb94834bba861789b9e36e3904d45`
- `formalization/OneAndAHalfJohnson/MainTheorems/Concrete.lean`: `78ab2bbdd698948e9461e3cc69e2d660aad958efd4d0e3310145f49f77eb9db5`
