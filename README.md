# decision-quotient-bounds

Machine-checked relations between logit perturbations, KL divergence and argmax / top-k decisions,
in Lean 4 with Mathlib.

A decision taken from logits (argmax, top-k set, routing to experts) depends only on pairwise
contrasts, and it is blind to a common shift of all logits. A KL divergence between the softmax
distributions is a different quantity. This repository proves the exact identity behind KL bounds,
proves that a small KL does **not** protect a decision, and proves the exact contrast conditions that
do protect it. It also shows that correlated perturbations, whose rows share a common component, are
certified with strictly less information than bounds on every row.

Every theorem is checked by the Lean kernel, with no `sorry`, and uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`. Labels: **[L]** new theorem or construction proved in Lean; **[L-known]** Lean formalization of a known result; **refuted** counterexample proved in Lean; **open** precise statement not resolved here.

## Contents

| Module | Statement | Status |
|--------|-----------|--------|
| `SoftmaxKL` | `KL(softmax z ‖ softmax(z + δ)) = log E_p[e^δ] − E_p[δ]` with `p = softmax z` | [L-known] |
| | gauge invariance: `softmax(z + c·1) = softmax z`, and `δ ↦ δ + c·1` leaves the KL unchanged | [L-known] |
| | Hoeffding's lemma for finite distributions: `log E_p[e^δ] − E_p[δ] ≤ (b − a)²/8` for `δ ∈ [a, b]` | [L-known] |
| | `KL(softmax z ‖ softmax(z + δ)) ≤ (max δ − min δ)²/8` | [L-known] |
| | claim "a small enough KL preserves the top-1 class": for every `η > 0` a two-class shift with `KL < η` changes the top class | **refuted** |
| `PairwiseContrast` | `i` stays the strict argmax iff `δ_j − δ_i < z_i − z_j` for all `j ≠ i` | [L-known] |
| | robust form over a set `Δ` of shifts: `z_i − z_j > δ_j − δ_i` for every `δ ∈ Δ` | [L-known] |
| | top-k sets: the same condition for every member / non-member pair | [L-known] |
| | margin `> 2ρ` suffices when `‖δ‖∞ ≤ ρ`; margin exactly `2ρ` does not | [L-known] |
| | contrasts are invariant under `δ ↦ δ + c·1` | [L-known] |
| `CommonModeCancellation` | for rows `e_j = c + r_j`: `(e_j − e_i)·x = (r_j − r_i)·x` | [L-known] |
| | residual contrasts certify the decision for every common component `c` | [L] |
| | per-row certificates can need a margin `2M` (any `M`) where the residual certificate needs `0` | [L] |

Open questions:

- **open**: the minimum number of bits needed to certify a top-k decision under structured
  perturbations (low-rank or sign-constrained rows), beyond the common-mode case proved here.
- **open**: sharp joint conditions on KL and margin that imply preservation of the whole sampling
  distribution, rather than only of the argmax.

## Reproduce

```bash
lake exe cache get
lake build
scripts/audit.sh     # #print axioms for every theorem; fails on sorry, warnings or extra axioms
```

Pinned toolchain: `leanprover/lean4:v4.33.1`, Mathlib `v4.33.1`
(commit `0df444a360eaa60ab8c11dca51a86af692955474`). The Hoeffding step uses Mathlib's
`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`.

## License

MIT
