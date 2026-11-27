import Mathlib

/-!
# Obligation hypergraphs: exact sufficiency of protected coordinate sets

Fix a context `x : ι → V`, a finite family `A` of admissible interventions (full assignments
`a : ι → V`), and a consequence `f`. An intervention is **adversarial** if it changes the
consequence, `f a ≠ f x`. Its **support** is the set of coordinates it modifies. A set `R` of
coordinates **protects** `f` if every admissible intervention that leaves `R` untouched keeps the
consequence.

* `protects_iff_hits_bad`: `R` protects `f` iff `R` meets the support of every adversarial
  intervention;
* `exists_minimal_sub`, `protects_iff_hits_minimal`: iff `R` meets every *inclusion-minimal*
  adversarial support (a hypergraph transversal). No monotonicity of `f` is assumed: a larger
  intervention may be harmless again, and the criterion only involves the minimal antichain;
* `optimal_protection_iff`: hence optimal protections under any cost are exactly the optimal
  transversals (weighted hitting set);
* `protects_all_iff`: several consequences are protected iff the union of their minimal families
  is hit;
* `marginal_insufficient` (**refutation**): keeping every coordinate whose individual change alters
  `f` is not enough. For `f = AND` over a set `H` of at least two coordinates from the all-false
  context, no single change is visible, so the marginal set is empty, yet the empty set does not
  protect `f`, and any single coordinate of `H` does.

## Discovery by counterexamples

The minimal family is usually not given. A counterexample-guided loop (`cegis`) proposes a
transversal of the supports known so far and asks an exact counterexample oracle (`CexOracle`) for
an admissible adversarial intervention avoiding it.

* `cegis_sound`: whatever the loop returns protects `f`;
* `cex_new`, `cegis_terminates`: every counterexample support is new, so if all of them lie in a
  finite family `𝓜` (all adversarial supports, or the minimal ones for a minimizing oracle) the loop
  stops within `|𝓜| + 1` oracle calls, with no enumeration of interventions;
* `cegis_optimal`: if each proposal is a minimum-weight transversal of the known supports, the
  returned set is a minimum-weight protection;
* `threshold_rounds_from_empty` (**lower bound**): for the threshold consequence "at least `k`
  coordinates switched on", a loop whose proposals have minimum cardinality needs more than
  `(n choose k)` oracle calls, whatever the oracle. Every known family that misses one `k`-set has a
  transversal of size `n - k`, while every protection has size at least `n - k + 1`
  (`threshold_gap`, `threshold_no_early_stop`).
-/

namespace DecisionQuotient.Obligations

open Finset

variable {ι V β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq V]

/-- The coordinates an intervention modifies. -/
def supp (x a : ι → V) : Finset ι := univ.filter fun j => a j ≠ x j

/-- `R` protects the consequence `f` at context `x` against the admissible interventions `A`. -/
def Protects (f : (ι → V) → β) (x : ι → V) (A : Finset (ι → V)) (R : Finset ι) : Prop :=
  ∀ a ∈ A, Disjoint R (supp x a) → f a = f x

/-- Supports of the adversarial interventions. -/
def badSupports [DecidableEq β] (f : (ι → V) → β) (x : ι → V) (A : Finset (ι → V)) :
    Finset (Finset ι) :=
  (A.filter fun a => f a ≠ f x).image (supp x)

/-- Inclusion-minimal adversarial supports. -/
def minimalBad [DecidableEq β] (f : (ι → V) → β) (x : ι → V) (A : Finset (ι → V)) :
    Finset (Finset ι) :=
  (badSupports f x A).filter fun H => ∀ H' ∈ badSupports f x A, H' ⊆ H → H' = H

/-- `R` meets every member of the family. -/
def Hits (R : Finset ι) (𝓗 : Finset (Finset ι)) : Prop := ∀ H ∈ 𝓗, ¬ Disjoint R H

variable [DecidableEq β]

/-- Protection is exactly hitting every adversarial support. -/
theorem protects_iff_hits_bad (f : (ι → V) → β) (x : ι → V) (A : Finset (ι → V)) (R : Finset ι) :
    Protects f x A R ↔ Hits R (badSupports f x A) := by
  constructor
  · intro h H hH hdisj
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hH
    obtain ⟨haA, hbad⟩ := mem_filter.mp ha
    exact hbad (h a haA hdisj)
  · intro h a haA hdisj
    by_contra hbad
    exact h (supp x a) (mem_image.mpr ⟨a, mem_filter.mpr ⟨haA, hbad⟩, rfl⟩) hdisj

/-- Every adversarial support contains an inclusion-minimal adversarial support. -/
theorem exists_minimal_sub (f : (ι → V) → β) (x : ι → V) (A : Finset (ι → V)) :
    ∀ (k : ℕ) (H : Finset ι), H.card = k → H ∈ badSupports f x A →
      ∃ M ∈ minimalBad f x A, M ⊆ H := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro H hk hH
    by_cases hmin : ∀ H' ∈ badSupports f x A, H' ⊆ H → H' = H
    · exact ⟨H, mem_filter.mpr ⟨hH, hmin⟩, subset_refl _⟩
    · simp only [not_forall] at hmin
      obtain ⟨H', hH', hsub, hne⟩ := hmin
      have hlt : H'.card < H.card := card_lt_card (ssubset_of_subset_of_ne hsub hne)
      obtain ⟨M, hM, hMsub⟩ := ih H'.card (hk ▸ hlt) H' rfl hH'
      exact ⟨M, hM, hMsub.trans hsub⟩

/-- **Exact sufficiency**: `R` protects `f` iff it meets every inclusion-minimal adversarial
support. -/
theorem protects_iff_hits_minimal (f : (ι → V) → β) (x : ι → V) (A : Finset (ι → V))
    (R : Finset ι) : Protects f x A R ↔ Hits R (minimalBad f x A) := by
  rw [protects_iff_hits_bad]
  constructor
  · intro h H hH
    exact h H (mem_filter.mp hH).1
  · intro h H hH hdisj
    obtain ⟨M, hM, hMsub⟩ := exists_minimal_sub f x A H.card H rfl hH
    exact h M hM (disjoint_of_subset_right hMsub hdisj)

/-- **Weighted hitting set**: for any cost `w`, the optimal protections are exactly the optimal
transversals of the minimal adversarial family. -/
theorem optimal_protection_iff (f : (ι → V) → β) (x : ι → V) (A : Finset (ι → V))
    (w : ι → ℕ) (R : Finset ι) :
    (Protects f x A R ∧ ∀ R', Protects f x A R' → ∑ j ∈ R, w j ≤ ∑ j ∈ R', w j) ↔
      (Hits R (minimalBad f x A) ∧
        ∀ R', Hits R' (minimalBad f x A) → ∑ j ∈ R, w j ≤ ∑ j ∈ R', w j) := by
  simp only [protects_iff_hits_minimal]

/-- **Several consequences** are protected iff the union of their minimal families is hit. -/
theorem protects_all_iff {κ : Type*} (K : Finset κ) (f : κ → (ι → V) → β) (x : ι → V)
    (A : Finset (ι → V)) (R : Finset ι) :
    (∀ k ∈ K, Protects (f k) x A R) ↔ Hits R (K.biUnion fun k => minimalBad (f k) x A) := by
  simp only [protects_iff_hits_minimal, Hits, mem_biUnion]
  constructor
  · rintro h H ⟨k, hk, hH⟩
    exact h k hk H hH
  · intro h k hk H hH
    exact h H ⟨k, hk, hH⟩

/-- **Refutation: marginal protection is insufficient.** For `f = AND` over `H` with `|H| ≥ 2`,
from the all-false context and with all assignments admissible:
(1) no single-coordinate change alters `f`, so the marginal set is empty;
(2) the empty set does not protect `f`;
(3) every set meeting `H` protects `f`. -/
theorem marginal_insufficient (H : Finset ι) (hH : 1 < H.card) :
    let x : ι → Bool := fun _ => false
    let f : (ι → Bool) → Bool := fun a => decide (∀ j ∈ H, a j = true)
    (∀ j, f (Function.update x j true) = f x) ∧
      ¬ Protects f x univ ∅ ∧
      ∀ R : Finset ι, ¬ Disjoint R H → Protects f x univ R := by
  intro x f
  obtain ⟨a, b, ha, hb, hab⟩ := one_lt_card_iff.mp hH
  have hfx : f x = false := by
    simp only [f, x, decide_eq_false_iff_not, not_forall]
    exact ⟨a, ha, by simp⟩
  refine ⟨?_, ?_, ?_⟩
  · intro j
    rw [hfx]
    simp only [f, decide_eq_false_iff_not, not_forall]
    by_cases hja : j = a
    · refine ⟨b, hb, ?_⟩
      rw [Function.update_of_ne (by rw [hja]; exact Ne.symm hab)]
      simp [x]
    · refine ⟨a, ha, ?_⟩
      rw [Function.update_of_ne (Ne.symm hja)]
      simp [x]
  · intro hprot
    have h := hprot (fun j => decide (j ∈ H)) (mem_univ _) (disjoint_empty_left _)
    have h1 : f (fun j => decide (j ∈ H)) = true := by simp [f]
    rw [h1, hfx] at h
    simp at h
  · intro R hR a' _ hdisj
    obtain ⟨j, hjR, hjH⟩ := not_disjoint_iff.mp hR
    have hj : a' j = false := by
      by_contra hne
      exact disjoint_left.mp hdisj hjR (mem_filter.mpr ⟨mem_univ _, by simpa [x] using hne⟩)
    have h1 : f a' = false := by
      simp only [f, decide_eq_false_iff_not, not_forall]
      exact ⟨j, hjH, by simp [hj]⟩
    rw [h1, hfx]

/-! ### Discovery by counterexamples -/

/-- An exact counterexample oracle: on a proposal `R` it returns an admissible adversarial
intervention whose support avoids `R`, and returns `none` only when `R` protects. -/
structure CexOracle (f : (ι → V) → β) (x : ι → V) (A : Finset (ι → V)) where
  /-- The answer to a proposal. -/
  query : Finset ι → Option (ι → V)
  sound : ∀ R a, query R = some a → a ∈ A ∧ f a ≠ f x ∧ Disjoint R (supp x a)
  complete : ∀ R, query R = none → Protects f x A R

/-- The counterexample-guided loop with `n` oracle calls of fuel, from the known supports `K`. -/
def cegis {f : (ι → V) → β} {x : ι → V} {A : Finset (ι → V)} (O : CexOracle f x A)
    (propose : Finset (Finset ι) → Finset ι) : ℕ → Finset (Finset ι) → Option (Finset ι)
  | 0, _ => none
  | n + 1, K =>
    match O.query (propose K) with
    | none => some (propose K)
    | some a => cegis O propose n (insert (supp x a) K)

/-- A counterexample support is an adversarial support. -/
theorem cex_mem_bad {f : (ι → V) → β} {x : ι → V} {A : Finset (ι → V)} (O : CexOracle f x A)
    {R : Finset ι} {a : ι → V} (h : O.query R = some a) : supp x a ∈ badSupports f x A :=
  mem_image.mpr ⟨a, mem_filter.mpr ⟨(O.sound R a h).1, (O.sound R a h).2.1⟩, rfl⟩

omit [DecidableEq ι] [DecidableEq β] in
/-- A counterexample to a transversal of `K` has a support outside `K`. -/
theorem cex_new {f : (ι → V) → β} {x : ι → V} {A : Finset (ι → V)} (O : CexOracle f x A)
    {R : Finset ι} {K : Finset (Finset ι)} (hR : Hits R K) {a : ι → V}
    (h : O.query R = some a) : supp x a ∉ K :=
  fun hK => hR _ hK (O.sound R a h).2.2

omit [DecidableEq β] in
/-- **Soundness**: the loop only returns protections. -/
theorem cegis_sound {f : (ι → V) → β} {x : ι → V} {A : Finset (ι → V)} (O : CexOracle f x A)
    (propose : Finset (Finset ι) → Finset ι) :
    ∀ (n : ℕ) (K : Finset (Finset ι)) (R : Finset ι),
      cegis O propose n K = some R → Protects f x A R := by
  intro n
  induction n with
  | zero => intro K R h; simp [cegis] at h
  | succ n ih =>
    intro K R h
    cases hq : O.query (propose K) with
    | none =>
      simp only [cegis, hq, Option.some.injEq] at h
      exact h ▸ O.complete _ hq
    | some a =>
      simp only [cegis, hq] at h
      exact ih _ _ h

omit [DecidableEq β] in
/-- **Termination**: if every counterexample support lies in the finite family `𝓜`, the loop
started from `K ⊆ 𝓜` returns within `|𝓜| - |K| + 1` oracle calls. -/
theorem cegis_terminates {f : (ι → V) → β} {x : ι → V} {A : Finset (ι → V)}
    (O : CexOracle f x A) (propose : Finset (Finset ι) → Finset ι)
    (hprop : ∀ K, Hits (propose K) K) (𝓜 : Finset (Finset ι))
    (h𝓜 : ∀ R a, O.query R = some a → supp x a ∈ 𝓜) :
    ∀ (n : ℕ) (K : Finset (Finset ι)), K ⊆ 𝓜 → 𝓜.card < n + K.card →
      (cegis O propose n K).isSome := by
  intro n
  induction n with
  | zero =>
    intro K hK hn
    have := card_le_card hK
    omega
  | succ n ih =>
    intro K hK hn
    cases hq : O.query (propose K) with
    | none => simp [cegis, hq]
    | some a =>
      simp only [cegis, hq]
      have hnew := cex_new O (hprop K) hq
      apply ih _ (insert_subset (h𝓜 _ _ hq) hK)
      rw [card_insert_of_notMem hnew]
      omega

/-- With any exact oracle, `|adversarial supports| + 1` oracle calls suffice from scratch. -/
theorem cegis_terminates_of_exact {f : (ι → V) → β} {x : ι → V} {A : Finset (ι → V)}
    (O : CexOracle f x A) (propose : Finset (Finset ι) → Finset ι)
    (hprop : ∀ K, Hits (propose K) K) :
    (cegis O propose ((badSupports f x A).card + 1) ∅).isSome :=
  cegis_terminates O propose hprop _ (fun _ _ h => cex_mem_bad O h) _ ∅ (empty_subset _)
    (by rw [card_empty]; omega)

/-- **Optimality**: if every proposal is a minimum-weight transversal of the known supports, the
returned set is a minimum-weight protection. -/
theorem cegis_optimal {f : (ι → V) → β} {x : ι → V} {A : Finset (ι → V)} (O : CexOracle f x A)
    (propose : Finset (Finset ι) → Finset ι) (w : ι → ℕ)
    (hopt : ∀ K R', Hits R' K → ∑ j ∈ propose K, w j ≤ ∑ j ∈ R', w j) :
    ∀ (n : ℕ) (K : Finset (Finset ι)) (R : Finset ι), K ⊆ badSupports f x A →
      cegis O propose n K = some R →
      Protects f x A R ∧ ∀ R', Protects f x A R' → ∑ j ∈ R, w j ≤ ∑ j ∈ R', w j := by
  intro n
  induction n with
  | zero => intro K R _ h; simp [cegis] at h
  | succ n ih =>
    intro K R hK h
    cases hq : O.query (propose K) with
    | none =>
      simp only [cegis, hq, Option.some.injEq] at h
      subst h
      exact ⟨O.complete _ hq, fun R' hR' =>
        hopt K R' fun H hH => (protects_iff_hits_bad f x A R').mp hR' H (hK hH)⟩
    | some a =>
      simp only [cegis, hq] at h
      exact ih _ _ (insert_subset (cex_mem_bad O hq) hK) h

/-! ### A lower bound for minimum-cardinality proposals -/

/-- Threshold consequence from the all-false context: at least `k` coordinates are switched on. -/
def threshold (k : ℕ) (a : ι → Bool) : Bool := decide (k ≤ (supp (fun _ => false) a).card)

/-- The indicator of `S` modifies exactly `S`. -/
theorem supp_indicator (S : Finset ι) : supp (fun _ => false) (fun j => decide (j ∈ S)) = S := by
  ext j; simp [supp]

omit [DecidableEq ι] in
/-- The threshold is off at the base context. -/
theorem threshold_base {k : ℕ} (hk : 1 ≤ k) : threshold k (fun _ : ι => false) = false := by
  have h0 : supp (fun _ : ι => false) (fun _ : ι => false) = ∅ := by ext j; simp [supp]
  simp only [threshold, h0, card_empty, decide_eq_false_iff_not, not_le]
  omega

/-- Every protection of the threshold has at least `n - k + 1` coordinates. -/
theorem threshold_protects_card {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ Fintype.card ι) {R : Finset ι}
    (hR : Protects (threshold k) (fun _ => false) univ R) : Fintype.card ι - k < R.card := by
  by_contra hle
  rw [not_lt] at hle
  have hc : k ≤ Rᶜ.card := by rw [card_compl]; omega
  obtain ⟨S, hSR, hS⟩ := exists_subset_card_eq hc
  have h := hR (fun j => decide (j ∈ S)) (mem_univ _)
    (by rw [supp_indicator]; exact disjoint_of_subset_right hSR disjoint_compl_right)
  rw [threshold_base hk] at h
  simp [threshold, supp_indicator, hS] at h

/-- A known family of supports of size at least `k` that misses the `k`-set `S` has the
transversal `Sᶜ`, of size `n - k`, which does not protect the threshold. -/
theorem threshold_gap {k : ℕ} (hk : 1 ≤ k) (K : Finset (Finset ι)) (hK : ∀ T ∈ K, k ≤ T.card)
    (S : Finset ι) (hS : S.card = k) (hSK : S ∉ K) :
    Hits Sᶜ K ∧ ¬ Protects (threshold k) (fun _ => false) univ Sᶜ := by
  refine ⟨fun T hT hdisj => hSK ?_, fun hprot => ?_⟩
  · have hsub : T ⊆ S := fun j hj => by
      by_contra hjS
      exact disjoint_left.mp hdisj (mem_compl.mpr hjS) hj
    have hTS : T = S := eq_of_subset_of_card_le hsub (by rw [hS]; exact hK T hT)
    exact hTS ▸ hT
  · have h := hprot (fun j => decide (j ∈ S)) (mem_univ _)
      (by rw [supp_indicator]; exact disjoint_compl_left)
    rw [threshold_base hk] at h
    simp [threshold, supp_indicator, hS] at h

/-- A minimum-cardinality transversal of a known family that misses some `k`-set is not a
protection of the threshold. -/
theorem threshold_no_early_stop {k : ℕ} (hk : 1 ≤ k) (K : Finset (Finset ι))
    (hK : ∀ T ∈ K, k ≤ T.card) (S : Finset ι) (hS : S.card = k) (hSK : S ∉ K) (P : Finset ι)
    (hP : ∀ R', Hits R' K → P.card ≤ R'.card) :
    ¬ Protects (threshold k) (fun _ => false) univ P := by
  intro hprot
  have hkn : k ≤ Fintype.card ι := hS ▸ card_le_univ S
  have h1 := threshold_protects_card hk hkn hprot
  have h2 := hP _ (threshold_gap hk K hK S hS hSK).1
  rw [card_compl, hS] at h2
  omega

/-- **Round lower bound**: with minimum-cardinality proposals, a successful run from `K` has more
fuel than the number of `k`-sets missing from `K`, whatever the exact oracle. -/
theorem threshold_rounds {k : ℕ} (hk : 1 ≤ k)
    (O : CexOracle (threshold k) (fun _ : ι => false) univ)
    (propose : Finset (Finset ι) → Finset ι)
    (hopt : ∀ K R', Hits R' K → (propose K).card ≤ R'.card) :
    ∀ (n : ℕ) (K : Finset (Finset ι)), (∀ T ∈ K, k ≤ T.card) →
      (cegis O propose n K).isSome → (powersetCard k univ \ K).card < n := by
  intro n
  induction n with
  | zero => intro K _ h; simp [cegis] at h
  | succ n ih =>
    intro K hK h
    cases hq : O.query (propose K) with
    | none =>
      have hprot := O.complete _ hq
      suffices hE : powersetCard k univ \ K = ∅ by rw [hE, card_empty]; omega
      rw [eq_empty_iff_forall_notMem]
      intro S hS
      rw [mem_sdiff, mem_powersetCard] at hS
      exact threshold_no_early_stop hk K hK S hS.1.2 hS.2 _ (hopt K) hprot
    | some a =>
      simp only [cegis, hq] at h
      have hbad := (O.sound _ a hq).2.1
      have hcard : k ≤ (supp (fun _ => false) a).card := by
        by_contra hlt
        apply hbad
        rw [threshold_base hk]
        simp [threshold, hlt]
      have hrec := ih (insert (supp (fun _ => false) a) K)
        (fun T hT => (mem_insert.mp hT).elim (fun e => e ▸ hcard) (hK T)) h
      have hsub : powersetCard k univ \ K ⊆
          insert (supp (fun _ => false) a)
            (powersetCard k univ \ insert (supp (fun _ => false) a) K) := by
        intro T hT
        rw [mem_sdiff] at hT
        by_cases hTe : T = supp (fun _ => false) a
        · exact mem_insert.mpr (Or.inl hTe)
        · exact mem_insert_of_mem
            (mem_sdiff.mpr ⟨hT.1, fun hm => (mem_insert.mp hm).elim hTe hT.2⟩)
      have := (card_le_card hsub).trans (card_insert_le _ _)
      omega

/-- From scratch, a minimum-cardinality loop needs more than `(n choose k)` oracle calls. -/
theorem threshold_rounds_from_empty {k : ℕ} (hk : 1 ≤ k)
    (O : CexOracle (threshold k) (fun _ : ι => false) univ)
    (propose : Finset (Finset ι) → Finset ι)
    (hopt : ∀ K R', Hits R' K → (propose K).card ≤ R'.card) (n : ℕ)
    (h : (cegis O propose n ∅).isSome) : (Fintype.card ι).choose k < n := by
  have := threshold_rounds hk O propose hopt n ∅ (by simp) h
  simpa [card_powersetCard] using this

end DecisionQuotient.Obligations
