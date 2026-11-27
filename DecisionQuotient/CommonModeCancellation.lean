import Mathlib

/-!
# Correlated perturbation rows: the common component cancels in every contrast

Logit perturbations produced by a perturbed linear head are `δ_j = e_j ⬝ x`, one row `e_j` per
class. When the rows share a common component, `e_j = c + r_j`, every contrast `δ_j - δ_i`
depends only on the residual rows `r_j - r_i`:

* `contrast_common_mode`: `(c + r_j) ⬝ x - (c + r_i) ⬝ x = (r_j - r_i) ⬝ x`;
* `top1_of_residual_contrasts`: a decision certified by residual contrasts holds for every common
  component `c`, of any size;
* `per_row_certificate_unbounded`: a certificate that bounds each row separately can need an
  arbitrarily large margin on instances where the residual certificate needs none. Bounding the
  pairwise differences carries strictly less information than bounding every row.
-/

namespace DecisionQuotient

open Matrix

/-- The common component cancels in every contrast. -/
theorem contrast_common_mode {ι m : Type*} [Fintype m] (c : m → ℝ) (r : ι → m → ℝ) (x : m → ℝ)
    (i j : ι) : (c + r j) ⬝ᵥ x - (c + r i) ⬝ᵥ x = (r j - r i) ⬝ᵥ x := by
  rw [add_dotProduct, add_dotProduct, sub_dotProduct]; ring

/-- Residual contrasts certify the decision for every common component. -/
theorem top1_of_residual_contrasts {ι m : Type*} [Fintype m] (z : ι → ℝ) (r : ι → m → ℝ)
    (x : m → ℝ) (i : ι) (h : ∀ j, j ≠ i → (r j - r i) ⬝ᵥ x < z i - z j) (c : m → ℝ) :
    ∀ j, j ≠ i → z j + (c + r j) ⬝ᵥ x < z i + (c + r i) ⬝ᵥ x := by
  intro j hj
  have hc := contrast_common_mode c r x i j
  have := h j hj
  linarith

/-- Per-row certificates can be arbitrarily worse. For every `M` there is an instance where each
perturbed logit has size `M`, so a per-row certificate needs a margin of at least `2M`, while every
residual contrast is `0`. -/
theorem per_row_certificate_unbounded (M : ℝ) (hM : 0 ≤ M) :
    ∃ (c : Fin 1 → ℝ) (r : Fin 2 → Fin 1 → ℝ) (x : Fin 1 → ℝ),
      (∀ j, |(c + r j) ⬝ᵥ x| = M) ∧ ∀ i j, (r j - r i) ⬝ᵥ x = 0 := by
  refine ⟨fun _ => M, fun _ => 0, fun _ => 1, ?_, ?_⟩
  · intro j; simp [dotProduct, abs_of_nonneg hM]
  · intro i j; simp [dotProduct]

end DecisionQuotient
