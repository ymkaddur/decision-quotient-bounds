import Mathlib

/-!
# Common-message decoding with side information

Feasibility is a common-intersection condition on each receiver's side and message fiber.
Exact requests and scalar interval requests admit pairwise certificates. General acceptance
sets lead to finite obstructions whose members cannot all share a codeword.
-/

namespace DecisionQuotient.ConfusionDecoding

variable {X Y I M : Type*} {S O : I → Type*}

/-- A receiver may select any acceptable output using only its side value and the common message. -/
def Serves (side : (i : I) → X → S i) (accept : (i : I) → X → O i → Prop)
    (message : X → M) : Prop :=
  ∃ decoder : (i : I) → S i → M → O i,
    ∀ i x, accept i x (decoder i (side i x) (message x))

theorem serves_iff_fibers (side : (i : I) → X → S i) (accept : (i : I) → X → O i → Prop)
    (message : X → M) :
    Serves side accept message ↔ ∀ i s m, ∃ o : O i,
      ∀ x, side i x = s → message x = m → accept i x o := by
  constructor
  · rintro ⟨decoder, hdec⟩ i s m
    exact ⟨decoder i s m, fun x hs hm => by simpa only [hs, hm] using hdec i x⟩
  · intro h
    exact ⟨fun i s m => Classical.choose (h i s m), fun i x =>
      Classical.choose_spec (h i (side i x) (message x)) x rfl rfl⟩

/-- Two states create an edge if some receiver has the same side value and distinct demands. -/
def Confused (side : (i : I) → X → S i) (demand : (i : I) → X → O i) (x y : X) : Prop :=
  ∃ i, side i x = side i y ∧ demand i x ≠ demand i y

theorem exact_iff_coloring [∀ i, Nonempty (O i)] (side : (i : I) → X → S i)
    (demand : (i : I) → X → O i) (message : X → M) :
    Serves side (fun i x o => o = demand i x) message ↔
      ∀ x y, Confused side demand x y → message x ≠ message y := by
  rw [serves_iff_fibers]
  constructor
  · rintro h x y ⟨i, hs, hd⟩ hm
    obtain ⟨o, ho⟩ := h i (side i y) (message y)
    exact hd ((ho x hs hm).symm.trans (ho y rfl rfl))
  · intro h i s m
    by_cases reach : ∃ p, side i p = s ∧ message p = m
    · obtain ⟨p, hp, hm⟩ := reach
      refine ⟨demand i p, fun x hx hxm => ?_⟩
      by_contra hne
      exact h p x ⟨i, hp.trans hx.symm, hne⟩ (hm.trans hxm.symm)
    · exact ⟨Classical.choice (inferInstance : Nonempty (O i)), fun x hx hm =>
        (reach ⟨x, hx, hm⟩).elim⟩

def confusionGraph (side : (i : I) → X → S i) (demand : (i : I) → X → O i) : SimpleGraph X where
  Adj := Confused side demand
  symm := by
    constructor
    rintro x y ⟨i, hs, hd⟩
    exact ⟨i, hs.symm, Ne.symm hd⟩
  loopless := by
    constructor
    rintro x ⟨i, _, hd⟩
    exact hd rfl

/-- Feasible budgets of common alphabet symbols are the bounds on the chromatic number. -/
theorem alphabet_budget_iff_chromatic [∀ i, Nonempty (O i)]
    (side : (i : I) → X → S i) (demand : (i : I) → X → O i) (symbols : ℕ) :
    (∃ message : X → Fin symbols, Serves side (fun i x o => o = demand i x) message) ↔
      (confusionGraph side demand).chromaticNumber ≤ symbols := by
  rw [SimpleGraph.chromaticNumber_le_iff_colorable]
  constructor
  · rintro ⟨message, h⟩
    exact ⟨SimpleGraph.Coloring.mk message (fun {x y} hx => (exact_iff_coloring side demand message).mp h x y hx)⟩
  · rintro ⟨color⟩
    exact ⟨color, (exact_iff_coloring side demand color).mpr (fun _ _ h => color.valid h)⟩

/-- Factoring the entire receiver contract through a surjective summary preserves feasibility
for every common alphabet. A section chooses one concrete input per summary for the reverse law. -/
theorem summary_preserves_alphabets (q : X → Y) (sectionMap : Y → X)
    (hsection : ∀ y, q (sectionMap y) = y)
    (side : (i : I) → Y → S i) (accept : (i : I) → Y → O i → Prop) :
    (∃ message : X → M,
      Serves (fun i x => side i (q x)) (fun i x => accept i (q x)) message) ↔
      ∃ message : Y → M, Serves side accept message := by
  constructor
  · rintro ⟨message, decoder, h⟩
    exact ⟨fun y => message (sectionMap y), decoder, fun i y => by
      simpa only [hsection] using h i (sectionMap y)⟩
  · rintro ⟨message, decoder, h⟩
    exact ⟨fun x => message (q x), decoder, fun i x => h i (q x)⟩

/-- One representative per summary suffices if its admissible outputs are acceptable throughout
that summary for every receiver. The receiver's side value must also factor through the summary. -/
theorem dominant_representatives (q : X → Y) (representative : Y → X)
    (sectionLaw : ∀ y, q (representative y) = y)
    (side : (i : I) → Y → S i) (accept : (i : I) → X → O i → Prop)
    (dominates : ∀ i x o, accept i (representative (q x)) o → accept i x o) :
    (∃ message : X → M, Serves (fun i x => side i (q x)) accept message) ↔
      ∃ message : Y → M, Serves side (fun i y => accept i (representative y)) message := by
  constructor
  · rintro ⟨message, decoder, h⟩
    exact ⟨fun y => message (representative y), decoder, fun i y => by
      simpa only [sectionLaw] using h i (representative y)⟩
  · rintro ⟨message, decoder, h⟩
    exact ⟨fun x => message (q x), decoder, fun i x => dominates i x _ (h i (q x))⟩

/-- A transition-compatible summary commutes with every finite common schedule. -/
theorem summary_after_schedule {Act : Type*} (q : X → Y) (step : X → Act → X)
    (abstractStep : Y → Act → Y) (commutes : ∀ x a, q (step x a) = abstractStep (q x) a)
    (schedule : List Act) (x : X) :
    q (schedule.foldl step x) = schedule.foldl abstractStep (q x) := by
  induction schedule generalizing x with
  | nil => rfl
  | cons a tail ih =>
    simp only [List.foldl_cons]
    rw [ih, commutes]

/-- Every small subset of a fiber having an acceptable output suffices under the stated
finite intersection property of the receiver contract. -/
theorem bounded_obstructions [Fintype X] (side : (i : I) → X → S i)
    (accept : (i : I) → X → O i → Prop) (message : X → M) (k : ℕ)
    (intersection : ∀ i (F : Finset X),
      (∀ T ⊆ F, T.card ≤ k → ∃ o, ∀ x ∈ T, accept i x o) →
      ∃ o, ∀ x ∈ F, accept i x o) :
    Serves side accept message ↔ ∀ i s m (T : Finset X), T.card ≤ k →
      (∀ x ∈ T, side i x = s ∧ message x = m) → ∃ o, ∀ x ∈ T, accept i x o := by
  classical
  rw [serves_iff_fibers]
  constructor
  · intro h i s m T _ hT
    obtain ⟨o, ho⟩ := h i s m
    exact ⟨o, fun x hx => ho x (hT x hx).1 (hT x hx).2⟩
  · intro h i s m
    let F := Finset.univ.filter (fun x : X => side i x = s ∧ message x = m)
    obtain ⟨o, ho⟩ := intersection i F (fun T hTF hk => h i s m T hk
      (fun x hx => (Finset.mem_filter.mp (hTF hx)).2))
    exact ⟨o, fun x hs hm => ho x (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs, hm⟩)⟩

/-- Scalar interval feasibility can be checked by retaining only each fiber's largest lower and
smallest upper endpoint. The condition includes repeated states, so invalid intervals are caught. -/
theorem intervals_iff_pairwise [Fintype X] (side : (i : I) → X → S i)
    (lower upper : I → X → ℝ) (message : X → M) :
    Serves side (O := fun _ => ℝ) (fun i x o => lower i x ≤ o ∧ o ≤ upper i x) message ↔
      ∀ i x y, side i x = side i y → message x = message y → lower i x ≤ upper i y := by
  classical
  rw [serves_iff_fibers]
  constructor
  · intro h i x y hs hm
    obtain ⟨o, ho⟩ := h i (side i y) (message y)
    exact (ho x hs hm).1.trans (ho y rfl rfl).2
  · intro h i s m
    let F := Finset.univ.filter (fun x : X => side i x = s ∧ message x = m)
    by_cases hF : F.Nonempty
    · obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image F (lower i) hF
      have hpair : side i p = s ∧ message p = m := (Finset.mem_filter.mp hp).2
      refine ⟨lower i p, fun x hs hm => ?_⟩
      have hx : x ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs, hm⟩
      exact ⟨hmax x hx, h i p x (hpair.1.trans hs.symm) (hpair.2.trans hm.symm)⟩
    · exact ⟨0, fun x hs hm => (hF ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs, hm⟩⟩).elim⟩

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- A linear encoder collapses a group of states to a given state's code exactly when its kernel
contains their difference span. This tests higher-order monochromatic obstructions by a basis. -/
theorem common_linear_code_iff (encode : V →ₗ[K] W) (base : V) (F : Set V) :
    (∀ x ∈ F, encode x = encode base) ↔
      Submodule.span K ((fun x => x - base) '' F) ≤ LinearMap.ker encode := by
  rw [Submodule.span_le]
  constructor
  · rintro h _ ⟨x, hx, rfl⟩
    change x - base ∈ LinearMap.ker encode
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
    exact h x hx
  · intro h x hx
    have hd : x - base ∈ LinearMap.ker encode := h (Set.mem_image_of_mem (fun y => y - base) hx)
    rwa [LinearMap.mem_ker, map_sub, sub_eq_zero] at hd

/-- With complementary sides, two encoders in one additive alphabet can share their sum.
Side-dependent demands and decoders are allowed. -/
theorem shared_additive_message {U T G P Q : Type*} [AddCommGroup G]
    (first : U → G) (second : T → G) (readFirst : T → G → P) (readSecond : U → G → Q)
    (p : U → T → P) (q : U → T → Q)
    (hp : ∀ u t, readFirst t (first u) = p u t)
    (hq : ∀ u t, readSecond u (second t) = q u t) :
    ∃ message : U → T → G, ∀ u t,
      readFirst t (message u t - second t) = p u t ∧
      readSecond u (message u t - first u) = q u t := by
  refine ⟨fun u t => first u + second t, fun u t => ⟨?_, ?_⟩⟩
  · simpa only [add_sub_cancel_right] using hp u t
  · simpa only [add_comm (first u), add_sub_cancel_right] using hq u t

def diskA (x y : ℝ) : Prop := x ^ 2 + y ^ 2 ≤ 1
def diskB (x y : ℝ) : Prop := (x - 2) ^ 2 + y ^ 2 ≤ 1
def diskC (x y : ℝ) : Prop := (x - 1) ^ 2 + (y - 3 / 2) ^ 2 ≤ 1

/-- Three rationally centered unit disks have pairwise intersections and empty triple intersection. -/
theorem pairwise_vector_contract_fails :
    (∃ x y, diskA x y ∧ diskB x y) ∧ (∃ x y, diskA x y ∧ diskC x y) ∧
    (∃ x y, diskB x y ∧ diskC x y) ∧ ¬ (∃ x y, diskA x y ∧ diskB x y ∧ diskC x y) := by
  refine ⟨⟨1, 0, by norm_num [diskA, diskB]⟩, ⟨1 / 2, 3 / 4, by norm_num [diskA, diskC]⟩,
    ⟨3 / 2, 3 / 4, by norm_num [diskB, diskC]⟩, ?_⟩
  rintro ⟨x, y, ha, hb, hc⟩
  unfold diskA at ha
  unfold diskB at hb
  have hx : (x - 1) ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg y]) (sq_nonneg _)
  have hy : y ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg (x - 1)]) (sq_nonneg _)
  have hx' : x = 1 := sub_eq_zero.mp ((mul_eq_zero.mp (by simpa only [pow_two] using hx)).elim id id)
  have hy' : y = 0 := (mul_eq_zero.mp (by simpa only [pow_two] using hy)).elim id id
  norm_num [diskC, hx', hy'] at hc

end DecisionQuotient.ConfusionDecoding
