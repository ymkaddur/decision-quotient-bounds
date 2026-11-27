import Mathlib

/-!
# Softmax shifts: exact KL identity, gauge invariance, Hoeffding bound, and a refutation

For logits `z` and a shift `δ`, with `p = softmax z`:

* `kl_softmax_shift`: `KL(p ‖ softmax (z + δ)) = log (∑ p_i e^(δ_i)) - ∑ p_i δ_i`, exactly;
* `softmax_add_const`, `kl_shift_add_const`: adding a constant to every logit changes nothing
  (gauge invariance), so only the class of `δ` modulo constants matters;
* `log_mean_exp_sub_mean_le`: Hoeffding's lemma for a finite distribution,
  `log E_p e^δ - E_p δ ≤ (b - a)^2 / 8` when `a ≤ δ_i ≤ b` (from Mathlib's sub-Gaussian lemma);
* `kl_softmax_shift_le`: hence `KL ≤ (max δ - min δ)^2 / 8`;
* `small_kl_flips_top1` (**refutation**): for every `η > 0` there is a shift with `KL < η` that
  changes the top-1 class. A KL guard, however tight, does not protect decisions.
-/

namespace DecisionQuotient

open Real Finset MeasureTheory

variable {n : ℕ}

/-- Softmax of logits `z`. -/
noncomputable def softmax (z : Fin n → ℝ) (i : Fin n) : ℝ := exp (z i) / ∑ j, exp (z j)

/-- Kullback-Leibler divergence of finite distributions, `∑ p_i log (p_i / q_i)`. -/
noncomputable def kl (p q : Fin n → ℝ) : ℝ := ∑ i, p i * log (p i / q i)

theorem sum_exp_pos [NeZero n] (z : Fin n → ℝ) : 0 < ∑ j, exp (z j) :=
  sum_pos (fun _ _ => exp_pos _) univ_nonempty

theorem softmax_pos [NeZero n] (z : Fin n → ℝ) (i : Fin n) : 0 < softmax z i :=
  div_pos (exp_pos _) (sum_exp_pos z)

theorem sum_softmax [NeZero n] (z : Fin n → ℝ) : ∑ i, softmax z i = 1 := by
  unfold softmax
  rw [← sum_div, div_self (sum_exp_pos z).ne']

/-- Gauge invariance: adding the same constant to every logit does not change the softmax. -/
theorem softmax_add_const [NeZero n] (z : Fin n → ℝ) (c : ℝ) :
    softmax (fun i => z i + c) = softmax z := by
  funext i
  unfold softmax
  simp only [exp_add]
  rw [← sum_mul, mul_div_mul_right _ _ (exp_pos c).ne']

theorem log_softmax [NeZero n] (z : Fin n → ℝ) (i : Fin n) :
    log (softmax z i) = z i - log (∑ j, exp (z j)) := by
  unfold softmax
  rw [log_div (exp_pos _).ne' (sum_exp_pos z).ne', log_exp]

/-- The mean of `e^δ` under `softmax z` is the ratio of the two partition functions. -/
theorem mean_exp_eq [NeZero n] (z δ : Fin n → ℝ) :
    ∑ i, softmax z i * exp (δ i) = (∑ j, exp (z j + δ j)) / ∑ j, exp (z j) := by
  unfold softmax
  rw [sum_div]
  refine sum_congr rfl fun i _ => ?_
  rw [exp_add]; ring

/-- **The exact KL identity of a logit shift.** -/
theorem kl_softmax_shift [NeZero n] (z δ : Fin n → ℝ) :
    kl (softmax z) (softmax (z + δ)) =
      log (∑ i, softmax z i * exp (δ i)) - ∑ i, softmax z i * δ i := by
  have hZ := sum_exp_pos z
  have hZ' := sum_exp_pos (z + δ)
  have hterm : ∀ i, softmax z i * log (softmax z i / softmax (z + δ) i) =
      softmax z i * (log (∑ j, exp (z j + δ j)) - log (∑ j, exp (z j)) - δ i) := by
    intro i
    rw [log_div (softmax_pos z i).ne' (softmax_pos _ i).ne', log_softmax, log_softmax]
    simp only [Pi.add_apply]
    ring
  unfold kl
  rw [sum_congr rfl fun i _ => hterm i, mean_exp_eq,
    log_div (by simpa using hZ'.ne') hZ.ne']
  have hsplit : ∑ i, softmax z i * (log (∑ j, exp (z j + δ j)) - log (∑ j, exp (z j)) - δ i) =
      (log (∑ j, exp (z j + δ j)) - log (∑ j, exp (z j))) * ∑ i, softmax z i -
        ∑ i, softmax z i * δ i := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    ring
  rw [hsplit, sum_softmax, mul_one]

/-- Gauge invariance of the divergence: `δ` and `δ + c` give the same KL. -/
theorem kl_shift_add_const [NeZero n] (z δ : Fin n → ℝ) (c : ℝ) :
    kl (softmax z) (softmax (z + fun i => δ i + c)) = kl (softmax z) (softmax (z + δ)) := by
  have h : (z + fun i => δ i + c) = fun i => (z + δ) i + c := by
    funext i; simp [add_assoc]
  rw [h, softmax_add_const]

/-- **Hoeffding's lemma for a finite distribution**: if `a ≤ δ_i ≤ b` for all `i`, then
`log (∑ p_i e^(δ_i)) - ∑ p_i δ_i ≤ (b - a)^2 / 8`. -/
theorem log_mean_exp_sub_mean_le {p : Fin n → ℝ} (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (δ : Fin n → ℝ) {a b : ℝ} (hab : ∀ i, δ i ∈ Set.Icc a b) :
    log (∑ i, p i * exp (δ i)) - ∑ i, p i * δ i ≤ (b - a) ^ 2 / 8 := by
  have hsum' : ∑ i, ENNReal.ofReal (p i) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hp i), hsum, ENNReal.ofReal_one]
  let P : PMF (Fin n) := PMF.ofFintype (fun i => ENNReal.ofReal (p i)) hsum'
  have hint : ∀ f : Fin n → ℝ, ∫ i, f i ∂P.toMeasure = ∑ i, p i * f i := by
    intro f
    rw [PMF.integral_eq_sum]
    refine sum_congr rfl fun i _ => ?_
    simp [P, PMF.ofFintype_apply, ENNReal.toReal_ofReal (hp i)]
  have hX : AEMeasurable δ P.toMeasure := (Measurable.of_discrete).aemeasurable
  have hb : ∀ᵐ i ∂P.toMeasure, δ i ∈ Set.Icc a b := Filter.Eventually.of_forall hab
  have hmgf := (ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc hX hb).mgf_le 1
  rw [ProbabilityTheory.mgf, hint] at hmgf
  simp only [one_mul, hint δ] at hmgf
  set m := ∑ i, p i * δ i with hm
  -- `∑ p_i e^(δ_i - m) = e^(-m) ∑ p_i e^(δ_i)`
  have hfac : ∑ i, p i * exp (δ i - m) = exp (-m) * ∑ i, p i * exp (δ i) := by
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [sub_eq_add_neg, exp_add]; ring
  rw [hfac] at hmgf
  have hpos : 0 < ∑ i, p i * exp (δ i) := by
    obtain ⟨i, hi⟩ : ∃ i, 0 < p i := by
      by_contra hcon
      simp only [not_exists, not_lt] at hcon
      have : ∑ i, p i ≤ 0 := sum_nonpos fun i _ => hcon i
      linarith
    exact lt_of_lt_of_le (mul_pos hi (exp_pos _))
      (single_le_sum (f := fun i => p i * exp (δ i))
        (fun j _ => mul_nonneg (hp j) (exp_pos _).le) (mem_univ i))
  have hlog := log_le_log (mul_pos (exp_pos _) hpos) hmgf
  rw [log_mul (exp_pos _).ne' hpos.ne', log_exp, log_exp] at hlog
  have hc : (((‖b - a‖₊ / 2) ^ 2 : NNReal) : ℝ) = (b - a) ^ 2 / 4 := by
    push_cast
    rw [Real.norm_eq_abs, div_pow, sq_abs]
    norm_num
  rw [hc] at hlog
  linarith

/-- KL of a logit shift with `a ≤ δ_i ≤ b` is at most `(b - a)^2 / 8`. -/
theorem kl_softmax_shift_le [NeZero n] (z δ : Fin n → ℝ) {a b : ℝ}
    (hab : ∀ i, δ i ∈ Set.Icc a b) :
    kl (softmax z) (softmax (z + δ)) ≤ (b - a) ^ 2 / 8 := by
  rw [kl_softmax_shift]
  exact log_mean_exp_sub_mean_le (fun i => (softmax_pos z i).le) (sum_softmax z) δ hab

/-- **Refutation: a small KL does not protect the top-1 decision.** For every `η > 0` there are two
logits and a shift such that the KL divergence is below `η` while the top class changes. -/
theorem small_kl_flips_top1 (η : ℝ) (hη : 0 < η) :
    ∃ z δ : Fin 2 → ℝ, kl (softmax z) (softmax (z + δ)) < η ∧ z 1 < z 0 ∧
      (z + δ) 0 < (z + δ) 1 := by
  set ε := min 1 η / 2 with hε
  have hm1 : min 1 η ≤ 1 := min_le_left _ _
  have hm2 : min 1 η ≤ η := min_le_right _ _
  have hm0 : 0 < min 1 η := lt_min one_pos hη
  have hε0 : 0 < ε := by positivity
  refine ⟨![ε, 0], ![0, 2 * ε], ?_, ?_, ?_⟩
  · have hb : ∀ i, (![0, 2 * ε] : Fin 2 → ℝ) i ∈ Set.Icc 0 (2 * ε) := by
      intro i
      fin_cases i <;> simp <;> linarith
    calc kl (softmax ![ε, 0]) (softmax (![ε, 0] + ![0, 2 * ε]))
        ≤ (2 * ε - 0) ^ 2 / 8 := kl_softmax_shift_le _ _ hb
      _ = (min 1 η) ^ 2 / 8 := by rw [hε]; ring
      _ < η := by nlinarith
  · simp [hε0]
  · simp; linarith

end DecisionQuotient
