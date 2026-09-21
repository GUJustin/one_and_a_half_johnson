# Paper-to-Lean result map

The paper is [ePrint 2026/1894](https://eprint.iacr.org/2026/1894). The source snapshot and hash are in `paper/`. The accepted external propositions are defined in [Targets/External.lean](formalization/OneAndAHalfJohnson/Targets/External.lean).

| Paper result | Lean declaration | External inputs |
|---|---|---|
| Theorems 1.1 and 3.1 | `MainTheorems.mainTheorem_of_AD21`, `conditionalMainTheorem` | AD21 |
| Corollary 1.2 | `MainTheorems.uniqueDecodingCounterexamples_of_AD21` | AD21 |
| Actual-code unique-radius strengthening | `MainTheorems.actual_unique_radius_of_AD21` | AD21 |
| Lemma 3.2 | `MainTheorems.smallDistanceBase_of_AD21` | AD21 |
| Theorem 3.3 | `Targets.AD21LowWeight` — accepted external input | AD21 itself |
| Lemma 3.4 | `MainTheorems.shorteningStructure_of_AD21` | AD21 |
| Lemma 3.5 | `MainTheorems.syndromeSeparation` | None |
| Theorem 4.1 | `MainTheorems.concreteTheorem_of_AD21_Hamada`, `conditionalConcreteTheorem` | AD21 and Hamada |

All declaration names above have prefix `OneAndAHalfJohnson.`. Complete statement contracts are in `Targets/`; their definitions alone are not theorem proofs. [Checks/CompletedResults.lean](formalization/Checks/CompletedResults.lean) checks completed proofs against those contracts.

[PROOF_NOTES.md](PROOF_NOTES.md) explains the alternative internal proof routes. [REVIEW.md](REVIEW.md) records source reviews; `validation/` contains build, axiom, and pinned-dependency receipts. The all-declaration receipt should be regenerated after any proof edit.
