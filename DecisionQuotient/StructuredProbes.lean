import Mathlib

/-!
# Exact probes for a prescribed family of Boolean monomials

The observable is given by a subset expansion of its deviation from a reference. On a
downward-closed domain every nonzero coefficient forces a nonzero probe. The allowed
monomial family can be sparse even when the domain contains exponentially many masks.
-/

namespace DecisionQuotient.StructuredProbes

open Finset

variable {ι A : Type*} [DecidableEq ι] [AddCommGroup A]

def evaluate (coefficient : Finset ι → A) (mask : Finset ι) : A :=
  ∑ t ∈ mask.powerset, coefficient t

def Downward (domain : Finset ι → Prop) : Prop :=
  ∀ ⦃t s : Finset ι⦄, t ⊆ s → domain s → domain t

/-- Triangular recovery of coefficients on a downward-closed region. The queried masks are
precisely the supplied monomial candidates inside the region. -/
theorem coefficients_zero (family : Finset (Finset ι)) (domain : Finset ι → Prop)
    (closed : Downward domain) (coefficient : Finset ι → A)
    (outside : ∀ t ∉ family, coefficient t = 0)
    (probe : ∀ t ∈ family, domain t → evaluate coefficient t = 0) :
    ∀ t, domain t → coefficient t = 0 := by
  intro t
  induction t using (measure (fun s : Finset ι => s.card)).wf.induction with
  | h t ih =>
    intro hdom
    by_cases ht : t ∈ family
    · have hsum : evaluate coefficient t = coefficient t := by
        unfold evaluate
        refine Finset.sum_eq_single t ?_ ?_
        · intro s hs hne
          have hsub := Finset.mem_powerset.mp hs
          exact ih s (Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩))
            (closed hsub hdom)
        · intro hn
          exact (hn (Finset.mem_powerset.mpr (Subset.rfl))).elim
      exact hsum.symm.trans (probe t ht hdom)
    · exact outside t ht

theorem zero_on_domain_iff_probes (family : Finset (Finset ι)) (domain : Finset ι → Prop)
    (closed : Downward domain) (coefficient : Finset ι → A)
    (outside : ∀ t ∉ family, coefficient t = 0) :
    (∀ s, domain s → evaluate coefficient s = 0) ↔
      ∀ t ∈ family, domain t → evaluate coefficient t = 0 := by
  constructor
  · exact fun h t _ ht => h t ht
  · intro probe s hs
    have hz := coefficients_zero family domain closed coefficient outside probe
    exact Finset.sum_eq_zero (fun t ht => hz t (closed (Finset.mem_powerset.mp ht) hs))

/-- If the interaction order is bounded by `d`, it suffices to probe disturbances of size at
most `d` disjoint from the protected variables. The reduction presumes the degree bound. -/
theorem protection_by_bounded_probes [Fintype ι] (R : Finset ι) (d : ℕ)
    (coefficient : Finset ι → A) (bound : ∀ t, d < t.card → coefficient t = 0) :
    (∀ s, Disjoint R s → evaluate coefficient s = 0) ↔
      ∀ t, Disjoint R t → t.card ≤ d → evaluate coefficient t = 0 := by
  let family := (Finset.univ : Finset (Finset ι)).filter (fun t => t.card ≤ d)
  have closed : Downward (Disjoint R) := by
    intro _ _ hsub hd
    exact disjoint_of_subset_right hsub hd
  have hout : ∀ t ∉ family, coefficient t = 0 := by
    intro t ht
    exact bound t (lt_of_not_ge (fun hn => ht (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩)))
  rw [zero_on_domain_iff_probes family (Disjoint R) closed coefficient hout]
  constructor
  · intro h t ht hd
    exact h t (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩) ht
  · intro h t ht hd
    exact h t hd (Finset.mem_filter.mp ht).2

/-- The single monomial on `needle` is a nonzero deviation exactly on its upward closure. -/
theorem single_monomial (needle mask : Finset ι) (weight : A) :
    evaluate (fun t => if t = needle then weight else 0) mask =
      if needle ⊆ mask then weight else 0 := by
  classical
  by_cases h : needle ⊆ mask
  · rw [if_pos h]
    unfold evaluate
    calc
      _ = (if needle = needle then weight else 0) :=
        Finset.sum_eq_single needle (fun t _ hne => if_neg hne)
          (fun hn => (hn (Finset.mem_powerset.mpr h)).elim)
      _ = weight := if_pos rfl
  · rw [if_neg h]
    unfold evaluate
    apply Finset.sum_eq_zero
    intro t ht
    apply if_neg
    intro he
    subst t
    exact h (Finset.mem_powerset.mp ht)

/-- Low-order probes alone do not validate their own order bound. -/
theorem unverified_degree_fails (needle : Finset ι) (d : ℕ) (large : d < needle.card) :
    ∃ coefficient : Finset ι → ℤ,
      (∀ s, s.card ≤ d → evaluate coefficient s = 0) ∧ evaluate coefficient needle = 1 := by
  refine ⟨fun t => if t = needle then 1 else 0, ?_, ?_⟩
  · intro s hs
    rw [single_monomial, if_neg]
    exact fun h => (not_lt_of_ge ((Finset.card_le_card h).trans hs)) large
  · rw [single_monomial, if_pos (Subset.rfl)]

end DecisionQuotient.StructuredProbes
