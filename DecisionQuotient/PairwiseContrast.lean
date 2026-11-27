import Mathlib

/-!
# Decisions are certified by pairwise contrasts

A decision on logits `z` (top-1 or a top-k set) survives a shift `δ` exactly when every pairwise
contrast of `z` beats the opposite contrast of `δ`:

* `top1_preserved_iff`: `i` stays the strict argmax iff `δ_j - δ_i < z_i - z_j` for every `j ≠ i`;
* `top1_robust_iff`: for a whole set `Δ` of admissible shifts, iff every contrast `z_i - z_j` exceeds
  every admissible `δ_j - δ_i` (the supremum condition `z_i - z_j > sup (δ_j - δ_i)`);
* `topk_preserved_iff`: the same for a top set `S` (every member beats every non-member);
* `top1_of_margin`: a margin larger than `2ρ` suffices when `|δ_k| ≤ ρ`, and `margin_tight` shows that
  a margin of exactly `2ρ` does not;
* `contrast_add_const`: contrasts, hence all these certificates, ignore constant shifts.
-/

namespace DecisionQuotient

/-- Top-1 preservation is exactly the pairwise contrast condition. -/
theorem top1_preserved_iff {ι : Type*} (z δ : ι → ℝ) (i : ι) :
    (∀ j, j ≠ i → z j + δ j < z i + δ i) ↔ ∀ j, j ≠ i → δ j - δ i < z i - z j := by
  constructor
  · intro h j hj; have := h j hj; linarith
  · intro h j hj; have := h j hj; linarith

/-- Robust certificate over a set of admissible shifts. -/
theorem top1_robust_iff {ι : Type*} (z : ι → ℝ) (Δ : Set (ι → ℝ)) (i : ι) :
    (∀ δ ∈ Δ, ∀ j, j ≠ i → z j + δ j < z i + δ i) ↔
      ∀ j, j ≠ i → ∀ δ ∈ Δ, δ j - δ i < z i - z j := by
  constructor
  · intro h j hj δ hδ; have := h δ hδ j hj; linarith
  · intro h δ hδ j hj; have := h j hj δ hδ; linarith

/-- A top set `S` (every member above every non-member) is preserved iff the contrast condition
holds for every member/non-member pair. -/
theorem topk_preserved_iff {ι : Type*} (z δ : ι → ℝ) (S : Set ι) :
    (∀ i ∈ S, ∀ j ∉ S, z j + δ j < z i + δ i) ↔ ∀ i ∈ S, ∀ j ∉ S, δ j - δ i < z i - z j := by
  constructor
  · intro h i hi j hj; have := h i hi j hj; linarith
  · intro h i hi j hj; have := h i hi j hj; linarith

/-- Margin sufficiency: if `|δ_k| ≤ ρ` for all `k` and every competitor is behind by more than `2ρ`,
the top-1 is preserved. -/
theorem top1_of_margin {ι : Type*} (z δ : ι → ℝ) (i : ι) (ρ : ℝ) (hδ : ∀ k, |δ k| ≤ ρ)
    (hm : ∀ j, j ≠ i → z j + 2 * ρ < z i) : ∀ j, j ≠ i → z j + δ j < z i + δ i := by
  intro j hj
  have h1 := (abs_le.mp (hδ j)).2
  have h2 := (abs_le.mp (hδ i)).1
  have := hm j hj
  linarith

/-- The margin `2ρ` cannot be lowered to `2ρ` itself: with margin exactly `2` and `|δ_k| ≤ 1`, the
decision can be lost (here, a tie). -/
theorem margin_tight :
    ∃ z δ : Fin 2 → ℝ, (∀ k, |δ k| ≤ 1) ∧ z 1 + 2 = z 0 ∧ ¬ (z 1 + δ 1 < z 0 + δ 0) := by
  refine ⟨![2, 0], ![-1, 1], ?_, by simp, by norm_num⟩
  intro k; fin_cases k <;> simp

/-- Contrasts ignore constant shifts: `(δ_j + c) - (δ_i + c) = δ_j - δ_i`. -/
theorem contrast_add_const {ι : Type*} (δ : ι → ℝ) (c : ℝ) (i j : ι) :
    (δ j + c) - (δ i + c) = δ j - δ i := by ring

end DecisionQuotient
