# Obligation hypergraphs

Status labels: **[L-known]** formalized here, mathematically known or elementary;
**[L]** formalized here, statement new in this form; **refuted** the claim is false and the
counterexample is formalized; **open** not proved.

## Statement

Fix a context `x : ι → V`, a finite family `A` of admissible interventions (full assignments) and a
consequence `f`. An intervention `a` is *adversarial* if `f a ≠ f x`; its *support* is the set of
coordinates where it differs from `x`. A coordinate set `R` *protects* `f` if every admissible
intervention whose support avoids `R` keeps `f`.

**Theorem.** `R` protects `f` if and only if `R` meets every inclusion-minimal adversarial support.

No monotonicity of `f` is assumed: a larger intervention may be harmless again, and only the
antichain of minimal adversarial supports matters.

## Motivation

Decide which coordinates must be held fixed so that no admissible intervention can change a
consequence, and know that nothing smaller works. The admissible family `A` can encode constraints
(budgets, forbidden combinations, physically reachable states), which the unconstrained setting
does not allow.

## Proof

Necessity: a minimal adversarial support disjoint from `R` is the support of an admissible
adversarial intervention that leaves `R` untouched. Sufficiency: every adversarial support contains
a minimal one, by strong induction on cardinality, and a set meeting the minimal one meets the
larger one.

## Background

Hitting-set duality between conflicts and diagnoses (R. Reiter, *A theory of diagnosis from first
principles*, 1987) and between abductive and contrastive explanations of classifiers (A. Ignatiev,
N. Narodytska, N. Asher, J. Marques-Silva, *From contrastive to abductive explanations and back
again*, 2020). The version here allows an arbitrary finite admissible family. With costs, optimal
protections are exactly minimum-weight transversals; minimum hitting set is NP-hard in general
(classical, not formalized here).

## Formalization

`DecisionQuotient/ObligationHypergraph.lean`

| Status | Statement | Lean name |
|--------|-----------|-----------|
| [L-known] | protection iff every adversarial support is hit | `protects_iff_hits_bad` |
| [L-known] | every adversarial support contains a minimal one | `exists_minimal_sub` |
| [L-known] | protection iff every *minimal* adversarial support is hit | `protects_iff_hits_minimal` |
| [L-known] | optimal protections under any cost are the optimal weighted transversals | `optimal_protection_iff` |
| [L-known] | several consequences: protected iff the union of their minimal families is hit | `protects_all_iff` |
| **refuted** | "keeping every coordinate whose individual change alters `f` suffices" | `marginal_insufficient` |
| [L-known] | the counterexample-guided loop returns only protections | `cegis_sound` |
| [L-known] | counterexample supports are new; termination within `|𝓜| + 1` oracle calls | `cex_new`, `cegis_terminates`, `cegis_terminates_of_exact` |
| [L-known] | minimum-weight proposals return a minimum-weight protection | `cegis_optimal` |
| [L] | threshold: every protection has at least `n - k + 1` coordinates; a known family missing a `k`-set has a non-protecting transversal of size `n - k` | `threshold_protects_card`, `threshold_gap`, `threshold_no_early_stop` |
| [L] | threshold: minimum-cardinality proposals need more than `C(n, k)` oracle calls, with any exact oracle | `threshold_rounds`, `threshold_rounds_from_empty` |

## Discovery by counterexamples

The minimal family is usually unknown. The loop `cegis` proposes a transversal `R` of the supports
known so far and asks an exact counterexample oracle for an admissible adversarial intervention
whose support avoids `R`. It stops when there is none.

* **Soundness.** The returned set protects `f`.
* **Termination.** Each counterexample support is new, because it avoids `R` and `R` hits every
  known support. If all counterexample supports lie in a finite family `𝓜`, the loop stops within
  `|𝓜| + 1` oracle calls: `|adversarial supports| + 1` for any exact oracle, `|minimal supports| + 1`
  for an oracle that returns minimal counterexamples. No intervention is enumerated.
* **Optimality.** If each proposal is a minimum-weight transversal of the known supports, the
  returned protection has minimum weight among all protections.
* **Lower bound.** For the threshold consequence "at least `k` of `n` Boolean coordinates switched
  on", minimum-cardinality proposals need more than `C(n, k)` oracle calls, whatever the exact
  oracle. A known family that misses one `k`-set `S` has the transversal `Sᶜ` of size `n - k`, while
  every protection has at least `n - k + 1` elements, so the loop cannot stop before all `C(n, k)`
  minimal supports are known. For `k = ⌊n/2⌋` this is exponential in `n`. An oracle that returns
  supports of size exactly `k` meets the matching upper bound `C(n, k) + 1` (`cegis_terminates` with
  `𝓜` the `k`-sets).

The cost of certifying an *optimal* protection is governed by the size of the minimal family, not
by the number of interventions, and it can be exponential. Finding *some* protection is free
(propose every coordinate). Value queries alone are weaker still: locating one hidden word among
`2^L` with membership queries needs `2^L` queries (`hankel-hidden-word`, `QueryLowerBound`).

The loop is the implicit hitting set scheme (E. Moreno-Centeno, R. M. Karp, *The implicit hitting
set approach to solve combinatorial optimization problems with an application to multigenome
alignment*, 2013); soundness, termination and optimality are formalized here. The threshold lower
bound is elementary; we did not find it stated in this form.

## Counterexample

`marginal_insufficient`: `f = AND` over a set `H` of at least two Boolean coordinates, from the
all-false context, every assignment admissible. No single change alters `f`, so the marginal set is
empty, yet the empty set does not protect `f`, and any single coordinate of `H` does.

## Limitations

* Finite admissible family and fixed context. The theorem says when a set is sufficient; it does
  not compute the minimal supports.
* The loop assumes an exact counterexample oracle and a transversal solver (minimum hitting set
  is NP-hard in general). Approximate oracles and approximate solvers are not covered.
* The lower bound is for minimum-cardinality proposals on threshold consequences. A general lower
  bound for every counterexample-guided learner that certifies optimality is **open** here.
* Nothing is claimed for continuous intervention sets or for probabilistic protection.

## Verification

`scripts/audit.sh` compiles every module with `#print axioms` of each theorem appended, and fails on
`sorry`, on warnings, or on axioms outside `propext`, `Classical.choice` and `Quot.sound`. Pinned
toolchain: Lean `v4.33.1`, Mathlib `v4.33.1`.
