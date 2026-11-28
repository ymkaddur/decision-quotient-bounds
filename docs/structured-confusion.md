# Finite receiver contracts and structured probes

## Common messages

A receiver observes a side value and a common message. Each state specifies a set of acceptable
answers. A decoder exists exactly when the acceptable sets have a common point on every fiber
of the pair (side, message). The forward witness is the decoder value. In reverse, choose one
point in each intersection. Total decoders also choose an output on unreachable pairs.

For exact demands, the fibers must contain a single demand value. This is proper coloring of
the confusion graph. The theorem alphabet_budget_iff_chromatic uses Mathlib's
SimpleGraph.chromaticNumber and establishes the equivalence for every finite alphabet budget.
A fixed binary budget of b bits gives an alphabet of size 2^b. The statement concerns a single
simultaneous message. Interactive, stochastic and variable-length models have their own constraints.

For scalar closed intervals, choose the largest lower endpoint in each nonempty fiber and compare
it with every upper endpoint. A scan needs one extremum pair per receiver fiber and one pass over
the states. The pairwise test inside a fiber may inspect quadratically many pairs. This is a
verification bound for a given code. The theorem pairwise_vector_contract_fails gives three
radius-one disks, centered at (0, 0), (2, 0) and (1, 3/2), with pairwise intersections and an empty
triple intersection. For a family with an independently established finite intersection bound k,
bounded_obstructions reduces feasibility to witnesses with at most k states. A linear encoder
collapses such a set to one message precisely when its difference span lies in the kernel.

A surjective summary preserves the feasible budgets when all receiver contracts factor through
it. A weaker premise also suffices. Keep one representative per summary with acceptable answers
contained in those of every state in the same class, simultaneously for all receivers. The side
values must factor through the summary. Restrict a concrete code to the representatives and lift
a summary code by composition. Both actions preserve the alphabet budget. If a transition commutes
with a summary, summary_after_schedule carries this equality through every fixed finite action schedule.

With complementary sides and additive encoder alphabets, transmit the sum of the two component
encoders. Each receiver subtracts the term computed from its own side. Decoders may vary with
their side values. Over a finite field, an arbitrary linear encoder on a direct sum restricts
to encoders on both axes. The largest of the two minimum ranks is therefore necessary. It is
sufficient by the sum construction after padding the smaller alphabet. The additive encoders
must depend on their respective axes. Arbitrary codes for individual side fibers require
additional compatibility, as the five-cycle control demonstrates.

## Intervention probes

Let the deviation at a mask S be the sum of its subset coefficients c(T), and suppose the
coefficients vanish outside a given finite candidate family. On any region closed under taking
subsets, the values on the candidate masks determine whether every deviation vanishes. Prove
this by increasing cardinality. Each coefficient is either zero by hypothesis or equal to its
probe after all proper subset coefficients vanish. Conversely, if all coefficients in the
region vanish, each allowed deviation is a sum of zeros.

This applies to masks disjoint from a protected set. For a degree bound d, it suffices to test
the disjoint masks of size at most d. More generally, candidates within a known bag family
of size at most w yield at most the sum of 2^w over the bags. The expense of finding and
certifying the candidate family is separate. A monomial on a single mask of size greater than
d vanishes on every tested mask of size at most d and is nonzero on its own mask.

For arbitrary coefficients over the binary field, the m allowed coefficients in the region
are m independent bits. In the deterministic exact membership-only model, a zero transcript
with fewer than m queries leaves a nonzero solution of the homogeneous evaluation equations.
Its smallest nonzero coefficient has a nonzero probe. Querying the m candidate masks achieves
the bound. This argument concerns a fixed protected region and a promised coefficient family.
The Lean theorems formalize the triangular implication and the false-promise witness.

## Verification and references

Run lake build, scripts/audit.sh, and python scripts/confusion_checks.py after restoring the
pinned dependencies. The Python controls use exact fractions and exhaustive small binary
families. The proof admits all finite state sets, including singleton and empty sets.

- Witsenhausen's chromatic formulation is the exact-demand antecedent.
  [IEEE Transactions on Information Theory](https://doi.org/10.1109/TIT.1976.1055607)
- For multiple receivers and coding transformations, see the original index-coding formulation.
  [Bar-Yossef et al.](https://webee.technion.ac.il/people/zivby/papers/indexing/indexing.full.pdf)
- Boolean subset transforms and bounded-degree function classes are classical.
  [Abbe, Shpilka and Ye](https://arxiv.org/abs/2002.03317)

The receiver-specific obstruction sizes, dominant-representative reduction and candidate-mask
checks specify which transformations preserve the tested contract. Finding a small family
with adequate coverage for a new application is a separate discovery problem.
