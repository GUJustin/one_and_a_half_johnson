# Proof routes and assumption boundary

The final statements use actual finite fields, linear subspaces, Hamming distances, dimensions, and finite sets of distinct exceptional coefficients. AD21 and the specialized Hamada formula are explicit theorem arguments. They are not Lean axioms, and no other existence statement is left as an external premise.

Several internal arguments differ from the paper while proving the same numbered conclusions:

- Scalar extension is proved to commute with shortening, making explicit the identity invoked in the paper's base-code proof.
- Common sparse supports are proved using incidence independence and support counting, without separately classifying the binary triangle exception.
- Subspace-polynomial shape is proved by linear algebra and root divisibility. Syndrome coordinates sum powers over each projective line, avoiding a choice-dependent representative normalization.
- The base construction works for every `m ≥ 4`, with exceptional density at least `1/(4Q⁴)`.
- The main amplification uses a slight overshoot of the requested distance to obtain the strict source-distance margin above Γ(δ).
- The asymptotic dimension argument uses the coarser sufficient bound `(m+1)^(2(Q−1))`. It does not claim the paper's sharper prime-field binomial rank bound. The main theorem permits a constant polynomial exponent, so its quantitative conclusion is preserved.
- Supercodes are constructed by deterministic finite-set avoidance. The asymptotic completion uses an integer defect bound giving rate error at most `6/s`.
- The concrete syndrome is selected by two finite hyperplane-avoidance arguments using `B² < q`, rather than by computing the paper's exact random-map dependence probability.
- Concrete real-number estimates use rational interval certificates: outward-rounded repeated squaring for the exact sampling powers, and a proved Taylor remainder bound plus doubling for exponentials and logarithms. All numerical certificates are checked by Lean; floating-point calculations are not trusted.

The project formalizes the paper's numbered conclusions under the agreed inputs. Alternative internal proofs replace some intermediate estimates; this is not a claim that every displayed calculation in the original proof has been reproduced verbatim.
