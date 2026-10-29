/-
WagnerWhitin/SilverMeal.lean

A self-contained Lean 4 formalization of the Silver-Meal stopping rule.

Literature-style definition:
For a replenishment at period 0, define the average cost per covered period

  A(ℓ) = (s + h * Σ_{j=0}^{ℓ-1} j * D_j) / ℓ

Silver-Meal chooses the first L such that
  A(L+1) ≥ A(L),
with strict decrease before that:
  A(j+1) < A(j) for all 1 ≤ j < L.

This file gives:
  - the basic definitions,
  - a generic constructor theorem,
  - a worked example showing stop at L = 2.

Key design choice:
Instead of defining the prefix holding term using List.range/map/sum/getD,
we define it recursively. This is much easier for Lean to simplify over ℝ.

*** Personal note:
We introduce a new structural characterization of Silver–Meal as the
first nondecrease point, prove it formally, and validate it empirically.
(“We extracted and formalized the exact mathematical structure
underlying a widely used heuristic.”)


Paper contributions:
1) Lean formalization of Silver–Meal
2) Two new theorems:
2)1) existence (via first nondecrease)
2)2) characterization (first nondecrease ↔ stop)
3) Python experiments (100k–500k) validating behavior
4) (killer lemma: theorem nondecrease_iff_inequality)
We derive an equivalent algebraic form of the Silver–Meal stopping condition
that eliminates division and expresses the rule as a finite set of polynomial
inequalities over demands and prefix sums. This formulation enables direct
encoding into SMT and neural network verification frameworks.
Bottom line
..We “turn it into a tool for verification”..:
.eliminate division
.express everything as inequalities
.show equivalence
.optionally encode in Python/SMT
..
.."z3 artifact (tool)":
We further provide a solver-oriented encoding of the stopping rule.
Using the proved equivalence between average-cost nondecrease and
the algebraic inequality condition, a candidate Silver–Meal stopping index
can be checked by a finite family of arithmetic constraints. We implemented
this encoding in Python/Z3 as a lightweight verification artifact.
..

Silver–Meal rule is described procedurally:
Extend the order horizon while average cost per period decreases; stop when it increases.
So in words, the rule already corresponds to:
a) decreasing phase
b) then first non-decrease → stop
What the literature does not do

What is typically missing:
1) No formal predicate like ours
No explicit definition of:
isFirstNondecreasePoint
2) No equivalence theorem
We proved: stop ⇔ first nondecrease point
In papers, this is never stated as an iff theorem
3) No machine-checked formalization
Certainly not in Lean / theorem prover

Next steps:
how to check the stopping point without simulating the heuristic
or how to embed the rule into a verification pipeline

***

-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace WagnerWhitin
namespace SilverMeal

noncomputable section

/-- Parameters of a Silver-Meal instance. -/
structure Problem where
  setupCost : ℝ
  holdingCost : ℝ
  demands     : List ℝ

/-- Extensionality principle for ordinary Silver-Meal problems. -/
@[ext]
theorem Problem.ext'
    {P Q : Problem}
    (hsetup : P.setupCost = Q.setupCost)
    (hholding : P.holdingCost = Q.holdingCost)
    (hdemands : P.demands = Q.demands) :
    P = Q := by
  cases P
  cases Q
  simp_all

/-- Planning horizon. -/
def horizon (P : Problem) : ℕ :=
  P.demands.length

/--
Auxiliary recursive weighted prefix sum.

`holdingPrefixAux ds ℓ i` means:
take the first `ℓ` demands from `ds`, starting with time-index `i`,
and compute Σ (time-index) * demand.
-/
def holdingPrefixAux : List ℝ → ℕ → ℕ → ℝ
  | _, 0, _ => 0
  | [], _ + 1, _ => 0
  | d :: ds, ℓ + 1, i => (i : ℝ) * d + holdingPrefixAux ds ℓ (i + 1)

/-- Prefix holding term over the zero-based Lean demand list.

This corresponds to the paper notation
`H(ℓ) = ∑_{t=1}^{ℓ} (t - 1) d_t`:
Lean list position `j` represents paper period `t = j + 1`. -/
def holdingPrefix (P : Problem) (ℓ : ℕ) : ℝ :=
  holdingPrefixAux P.demands ℓ 0

/-- Average cost per covered period:
    A(ℓ) = (s + h * holdingPrefix(ℓ)) / ℓ. -/
def avgCost (P : Problem) (ℓ : ℕ) : ℝ :=
  (P.setupCost + P.holdingCost * holdingPrefix P ℓ) / (ℓ : ℝ)

/--
Optional well-formedness predicate.
This is not needed to make the example compute, but it expresses the usual
inventory-theoretic assumptions: nonnegative costs and nonnegative demands.
-/
def Valid (P : Problem) : Prop :=
  0 ≤ P.setupCost ∧
  0 ≤ P.holdingCost ∧
  ∀ d ∈ P.demands, 0 ≤ d

/-- `L` is a Silver-Meal stopping index if:
    - `1 ≤ L < horizon`
    - for every earlier `j < L`, average cost strictly decreases
    - at `L`, extending one more period does not decrease average cost. -/
def isSilverMealStop (P : Problem) (L : ℕ) : Prop :=
  1 ≤ L ∧
  L < horizon P ∧
  (∀ j : ℕ, 1 ≤ j → j < L → avgCost P (j + 1) < avgCost P j) ∧
  avgCost P (L + 1) ≥ avgCost P L

/-- Generic constructor theorem:
    if the defining Silver-Meal inequalities hold, then `L` is a stop. -/
theorem first_nondecrease_is_stop
    (P : Problem) (L : ℕ)
    (hL1 : 1 ≤ L)
    (hLh : L < horizon P)
    (hdec : ∀ j : ℕ, 1 ≤ j → j < L → avgCost P (j + 1) < avgCost P j)
    (hstop : avgCost P (L + 1) ≥ avgCost P L) :
    isSilverMealStop P L := by
  exact ⟨hL1, hLh, hdec, hstop⟩

/-! ## Worked example -/

/-- Example instance:
    s = 500, h = 2, demands = [100, 200, 150, 250]. -/
def exampleProblem : Problem :=
  { setupCost := 500
    holdingCost := 2
    demands := [100, 200, 150, 250] }

example : horizon exampleProblem = 4 := by
  rfl

example : Valid exampleProblem := by
  constructor
  · norm_num [exampleProblem]
  · constructor
    · norm_num [exampleProblem]
    · intro d hd
      simp [exampleProblem] at hd
      rcases hd with rfl | rfl | rfl | rfl <;> norm_num

/-- Concrete prefix values:
    holdingPrefix 1 = 0
    holdingPrefix 2 = 200
    holdingPrefix 3 = 500
    holdingPrefix 4 = 1250 -/
example : holdingPrefix exampleProblem 1 = 0 := by
  norm_num [holdingPrefix, holdingPrefixAux, exampleProblem]

example : holdingPrefix exampleProblem 2 = 200 := by
  norm_num [holdingPrefix, holdingPrefixAux, exampleProblem]

example : holdingPrefix exampleProblem 3 = 500 := by
  norm_num [holdingPrefix, holdingPrefixAux, exampleProblem]

example : holdingPrefix exampleProblem 4 = 1250 := by
  norm_num [holdingPrefix, holdingPrefixAux, exampleProblem]

/-- Average-cost values:
    A(1)=500, A(2)=450, A(3)=500, A(4)=750. -/
example : avgCost exampleProblem 1 = 500 := by
  norm_num [avgCost, holdingPrefix, holdingPrefixAux, exampleProblem]

example : avgCost exampleProblem 2 = 450 := by
  norm_num [avgCost, holdingPrefix, holdingPrefixAux, exampleProblem]

example : avgCost exampleProblem 3 = 500 := by
  norm_num [avgCost, holdingPrefix, holdingPrefixAux, exampleProblem]

example : avgCost exampleProblem 4 = 750 := by
  norm_num [avgCost, holdingPrefix, holdingPrefixAux, exampleProblem]

/-- Main theorem for the example:
    Silver-Meal stops at L = 2. -/
theorem example_stop_at_two : isSilverMealStop exampleProblem 2 := by
  apply first_nondecrease_is_stop
  · norm_num
  · norm_num [horizon, exampleProblem]
  · intro j hj1 hjlt
    have hj : j = 1 := by omega
    subst hj
    norm_num [avgCost, holdingPrefix, holdingPrefixAux, exampleProblem]
  · norm_num [avgCost, holdingPrefix, holdingPrefixAux, exampleProblem]

/-- It does not stop at L = 1. -/
theorem example_not_stop_at_one : ¬ isSilverMealStop exampleProblem 1 := by
  intro h
  rcases h with ⟨h1k, hhorizon, hdec, hstop⟩
  norm_num [avgCost, holdingPrefix, holdingPrefixAux, exampleProblem] at hstop


/-
####### NEW THEOREM START existence theorem in finite-horizon form
-/
/-
Second part: existence theorem for Silver-Meal stopping points.
Add this near the end of the file, before the final `end` lines.
-/

/-- A candidate index where the average cost no longer decreases. -/
def isNondecreasePoint (P : Problem) (L : ℕ) : Prop :=
  1 ≤ L ∧
  L < horizon P ∧
  avgCost P (L + 1) ≥ avgCost P L

/--
If there exists any index `L` at which the average cost stops decreasing,
then the first such index is a Silver-Meal stopping point.
-/
theorem exists_stop_of_exists_nondecrease
    (P : Problem)
    (hex : ∃ L, isNondecreasePoint P L) :
    ∃ L, isSilverMealStop P L := by
  classical
  let L := Nat.find hex
  have hL : isNondecreasePoint P L := Nat.find_spec hex
  rcases hL with ⟨hL1, hLh, hstop⟩
  refine ⟨L, ?_⟩
  refine ⟨hL1, hLh, ?_, hstop⟩
  intro j hj1 hjlt
  have hnot : ¬ avgCost P (j + 1) ≥ avgCost P j := by
    intro hge
    have hle : L ≤ j := by
      apply Nat.find_min' hex
      exact ⟨hj1, lt_trans hjlt hLh, hge⟩
    exact (not_le_of_gt hjlt) hle
  linarith

/--
A corollary with the usual inventory-style validity assumptions.

These assumptions are not needed for the proof above, but this version
matches the kind of statement one often gives in a paper.
-/
theorem exists_stop_of_exists_nondecrease_valid
    (P : Problem)
    --(hV : Valid P)
    (hex : ∃ L, isNondecreasePoint P L) :
    ∃ L, isSilverMealStop P L := by
  exact exists_stop_of_exists_nondecrease P hex

/-- In the worked example, `L = 2` is a nondecrease point. -/
example : isNondecreasePoint exampleProblem 2 := by
  constructor
  · norm_num
  constructor
  · norm_num [horizon, exampleProblem]
  · norm_num [avgCost, holdingPrefix, holdingPrefixAux, exampleProblem]

/-- Therefore the worked example has a Silver-Meal stopping point. -/
example : ∃ L, isSilverMealStop exampleProblem L := by
  apply exists_stop_of_exists_nondecrease
  refine ⟨2, ?_⟩
  constructor
  · norm_num
  constructor
  · norm_num [horizon, exampleProblem]
  · norm_num [avgCost, holdingPrefix, holdingPrefixAux, exampleProblem]

lemma example_nondecrease_at_two : isNondecreasePoint exampleProblem 2 := by
  constructor
  · norm_num
  constructor
  · norm_num [horizon, exampleProblem]
  · norm_num [avgCost, holdingPrefix, holdingPrefixAux, exampleProblem]

lemma exampleProblem_valid : Valid exampleProblem := by
  constructor
  · norm_num [exampleProblem]
  constructor
  · norm_num [exampleProblem]
  · intro d hd
    simp [exampleProblem] at hd
    rcases hd with rfl | rfl | rfl | rfl
    all_goals norm_num

/-- The existence theorem can also be invoked through `Valid`. -/
example : ∃ L, isSilverMealStop exampleProblem L := by
  apply exists_stop_of_exists_nondecrease
  exact ⟨2, example_nondecrease_at_two⟩

/-
####### NEW THEOREM FINISH existence theorem in finite-horizon form
-/



/-
#######
####### NEW THEOREM: CHARACTERIZATION, START
-/

/-
Third part: characterization theorem.
A Silver-Meal stopping index is exactly the first nondecrease point.
-/

/-- `L` is the first nondecrease point if:
    - `L` is a nondecrease point
    - every earlier admissible index still has strict decrease. -/
def isFirstNondecreasePoint (P : Problem) (L : ℕ) : Prop :=
  isNondecreasePoint P L ∧
  (∀ j : ℕ, 1 ≤ j → j < L → avgCost P (j + 1) < avgCost P j)

/--
Characterization theorem:
`L` is a Silver-Meal stopping index if and only if `L` is the first
nondecrease point of the average-cost sequence.
-/
theorem silverMealStop_iff_firstNondecreasePoint
    (P : Problem) (L : ℕ) :
    isSilverMealStop P L ↔ isFirstNondecreasePoint P L := by
  constructor
  · intro h
    rcases h with ⟨hL1, hLh, hdec, hstop⟩
    refine ⟨?_, hdec⟩
    exact ⟨hL1, hLh, hstop⟩
  · intro h
    rcases h with ⟨hnd, hdec⟩
    rcases hnd with ⟨hL1, hLh, hstop⟩
    exact ⟨hL1, hLh, hdec, hstop⟩

/-- A direct constructor from "first nondecrease point" to Silver-Meal stop. -/
theorem firstNondecreasePoint_is_stop
    (P : Problem) (L : ℕ)
    (h : isFirstNondecreasePoint P L) :
    isSilverMealStop P L := by
  exact (silverMealStop_iff_firstNondecreasePoint P L).2 h

/-- A direct constructor from Silver-Meal stop to "first nondecrease point". -/
theorem stop_is_firstNondecreasePoint
    (P : Problem) (L : ℕ)
    (h : isSilverMealStop P L) :
    isFirstNondecreasePoint P L := by
  exact (silverMealStop_iff_firstNondecreasePoint P L).1 h

/-- In the worked example, `L = 2` is the first nondecrease point. -/
lemma example_first_nondecrease_at_two : isFirstNondecreasePoint exampleProblem 2 := by
  apply (silverMealStop_iff_firstNondecreasePoint exampleProblem 2).1
  exact example_stop_at_two

/-- Conversely, the characterization theorem recovers the Silver-Meal stop. -/
example : isSilverMealStop exampleProblem 2 := by
  apply (silverMealStop_iff_firstNondecreasePoint exampleProblem 2).2
  exact example_first_nondecrease_at_two

/-- So the worked example identifies `L = 2` exactly as the first nondecrease point. -/
example : isFirstNondecreasePoint exampleProblem 2 ∧ isSilverMealStop exampleProblem 2 := by
  constructor
  · exact example_first_nondecrease_at_two
  · exact example_stop_at_two

/-
#######
####### NEW THEOREM: CHARACTERIZATION, END
-/

/-
#######
#######
####### SILVER MEAL AS A VERIFICATION TOOL, START
-/

/-
Fourth part: verification-oriented encoding of the Silver-Meal nondecrease test.

We define an algebraic inequality condition equivalent to

  avgCost P (ℓ+1) ≥ avgCost P ℓ

for admissible indices ℓ ≥ 1.

This removes division and rewrites the stopping condition as a finite inequality
over setup cost, holding cost, the ℓ-th demand, and the weighted prefix sum.
-/

/-- Specialization of the weighted-prefix recursion at zero-based list
position `ℓ`.

In the paper's one-based notation:
  H(ℓ + 1) = H(ℓ) + ℓ * d_(ℓ + 1).

The Lean expression `P.demands.getD ℓ 0` corresponds to paper demand
`d_(ℓ + 1)`. -/
lemma holdingPrefixAux_succ (ds : List ℝ) (ℓ i : ℕ) :
    holdingPrefixAux ds (ℓ + 1) i
      = holdingPrefixAux ds ℓ i + ((i + ℓ : ℕ) : ℝ) * ds.getD ℓ 0 := by
  induction ds generalizing ℓ i with
  | nil =>
      cases ℓ <;> simp [holdingPrefixAux]
  | cons d ds ih =>
      cases ℓ with
      | zero =>
          simp [holdingPrefixAux]
      | succ ℓ =>
          simp [holdingPrefixAux, ih,
            add_assoc, add_comm, add_left_comm]

/--
One-step weighted-prefix recurrence.

Lean list position `ℓ` corresponds to paper period `ℓ + 1`.
Hence the paper-level recurrence is

  H(ℓ + 1) = H(ℓ) + ℓ * d_(ℓ + 1).
-/
lemma holdingPrefix_succ (P : Problem) (ℓ : ℕ) :
    holdingPrefix P (ℓ + 1)
      = holdingPrefix P ℓ + (ℓ : ℝ) * P.demands.getD ℓ 0 := by
  simpa [holdingPrefix] using holdingPrefixAux_succ P.demands ℓ 0

/--
Verification-oriented algebraic encoding of the nondecrease test.
This is the denominator-free inequality corresponding to
`avgCost P (ℓ+1) ≥ avgCost P ℓ`.

For `1 ≤ ℓ`, the paper-level equivalence is

  A(ℓ + 1) ≥ A(ℓ)
    ↔
  h * (ℓ^2 * d_(ℓ + 1) - H(ℓ)) ≥ s.

In Lean, `P.demands.getD ℓ 0` represents `d_(ℓ + 1)`.
-/
def inequalityCondition (P : Problem) (ℓ : ℕ) : Prop :=
  P.holdingCost *
      ((ℓ : ℝ) * ((ℓ : ℝ) * P.demands.getD ℓ 0) - holdingPrefix P ℓ)
    ≥ P.setupCost

/--
Nondecrease is equivalent to the algebraic inequality condition.
For admissible coverage lengths `ℓ ≥ 1`, the paper-level equivalence is

  A(ℓ + 1) ≥ A(ℓ)
iff
  h * (ℓ^2 * d_(ℓ + 1) - H(ℓ)) ≥ s.

In Lean, `P.demands.getD ℓ 0` represents the paper demand `d_(ℓ + 1)`.
-/
theorem nondecrease_iff_inequality
    (P : Problem) {ℓ : ℕ} (hl : 1 ≤ ℓ) :
    avgCost P (ℓ + 1) ≥ avgCost P ℓ ↔ inequalityCondition P ℓ := by
  have hl_ne : (ℓ : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hl)
  have hl1_ne : ((ℓ + 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero ℓ
  rw [avgCost, avgCost, holdingPrefix_succ]
  unfold inequalityCondition
  constructor
  · intro h
    field_simp [hl_ne, hl1_ne] at h
    norm_num at h ⊢
    ring_nf at h ⊢
    linarith
  · intro h
    field_simp [hl_ne, hl1_ne]
    norm_num at h ⊢
    ring_nf at h ⊢
    linarith

/-- The verification-oriented inequality holds at `ℓ = 2` in the worked example. -/
example : inequalityCondition exampleProblem 2 := by
  norm_num [inequalityCondition, holdingPrefix, holdingPrefixAux, exampleProblem]

/-- In the worked example, the algebraic inequality exactly matches nondecrease. -/
example : avgCost exampleProblem 3 ≥ avgCost exampleProblem 2
    ↔ inequalityCondition exampleProblem 2 := by
  apply nondecrease_iff_inequality
  norm_num

/--
A solver-friendly restatement of the Silver-Meal stop predicate:
strict decrease before `L`, and the algebraic inequality at `L`.
-/
theorem silverMealStop_iff_verificationCondition
    (P : Problem) {L : ℕ} (hL : 1 ≤ L) :
    isSilverMealStop P L ↔
      (1 ≤ L ∧
       L < horizon P ∧
       (∀ j : ℕ, 1 ≤ j → j < L → avgCost P (j + 1) < avgCost P j) ∧
       inequalityCondition P L) := by
  constructor
  · intro h
    rcases h with ⟨hL1, hLh, hdec, hnd⟩
    refine ⟨hL1, hLh, hdec, ?_⟩
    exact (nondecrease_iff_inequality P hL).1 hnd
  · intro h
    rcases h with ⟨hL1, hLh, hdec, hineq⟩
    refine ⟨hL1, hLh, hdec, ?_⟩
    exact (nondecrease_iff_inequality P hL).2 hineq

/-
#######
#######
####### SILVER MEAL AS A VERIFICATION TOOL, END
-/


/-!
###############################################################################
# ROBUST SILVER-MEAL: PERIOD-WISE TRIMMED DEMAND AGGREGATION
###############################################################################

This section extends the verified Silver-Meal development with an aggregation
layer placed before the heuristic.

For every period `t`, we assume a finite list of scenario forecasts

  d_t^(1), ..., d_t^(m).

An aggregation operator maps this list to one representative demand `d̂_t`.
The classical Silver-Meal definitions and proofs are then applied unchanged to
the aggregated demand sequence.

The concrete robust estimator below is a symmetric `k`-trimmed mean: sort the
forecasts, remove the `k` smallest and `k` largest observations, and average the
remaining values.
-/

/-- A scenario-based Silver-Meal instance.

`periodForecasts[j]` stores the forecast panel for paper period
`t = j + 1`. Thus Lean list position `j` corresponds to the panel
`F_(j + 1) = (d_(j + 1)^(1), ..., d_(j + 1)^(m))`
for planning period `t`. -/
structure ScenarioProblem where
  setupCost : ℝ
  holdingCost     : ℝ
  periodForecasts : List (List ℝ)

/-- Planning horizon of a scenario problem. -/
def scenarioHorizon (S : ScenarioProblem) : ℕ :=
  S.periodForecasts.length

/-- An aggregation operator maps the forecasts for one period to one demand. -/
abbrev DemandAggregator := List ℝ → ℝ

/-- Apply an aggregation operator independently at every period. -/
def aggregateDemands (agg : DemandAggregator) (S : ScenarioProblem) : List ℝ :=
  S.periodForecasts.map agg

/-- Convert a scenario problem into an ordinary Silver-Meal problem. -/
def ScenarioProblem.aggregate (agg : DemandAggregator) (S : ScenarioProblem) : Problem :=
  { setupCost := S.setupCost
    holdingCost := S.holdingCost
    demands := aggregateDemands agg S }

@[simp] theorem horizon_aggregate
    (agg : DemandAggregator) (S : ScenarioProblem) :
    horizon (S.aggregate agg) = scenarioHorizon S := by
  simp [ScenarioProblem.aggregate, horizon, scenarioHorizon, aggregateDemands]

/-- Generic aggregated weighted-prefix cost. -/
def aggregatedHoldingPrefix
    (agg : DemandAggregator) (S : ScenarioProblem) (ℓ : ℕ) : ℝ :=
  holdingPrefix (S.aggregate agg) ℓ

/-- Generic aggregated average cost. -/
def aggregatedAvgCost
    (agg : DemandAggregator) (S : ScenarioProblem) (ℓ : ℕ) : ℝ :=
  avgCost (S.aggregate agg) ℓ

/-- Generic aggregated Silver-Meal stopping predicate. -/
def isAggregatedSilverMealStop
    (agg : DemandAggregator) (S : ScenarioProblem) (L : ℕ) : Prop :=
  isSilverMealStop (S.aggregate agg) L

/-- Generic aggregated nondecrease predicate. -/
def isAggregatedNondecreasePoint
    (agg : DemandAggregator) (S : ScenarioProblem) (L : ℕ) : Prop :=
  isNondecreasePoint (S.aggregate agg) L

/-- Generic aggregated first-nondecrease predicate. -/
def isAggregatedFirstNondecreasePoint
    (agg : DemandAggregator) (S : ScenarioProblem) (L : ℕ) : Prop :=
  isFirstNondecreasePoint (S.aggregate agg) L

/-- Generic aggregated denominator-free verification condition. -/
def aggregatedInequalityCondition
    (agg : DemandAggregator) (S : ScenarioProblem) (ℓ : ℕ) : Prop :=
  inequalityCondition (S.aggregate agg) ℓ

/-- Aggregation preserves the structural Silver-Meal characterization. -/
theorem aggregatedSilverMealStop_iff_firstNondecreasePoint
    (agg : DemandAggregator) (S : ScenarioProblem) (L : ℕ) :
    isAggregatedSilverMealStop agg S L ↔
      isAggregatedFirstNondecreasePoint agg S L := by
  exact silverMealStop_iff_firstNondecreasePoint (S.aggregate agg) L

/-- If an aggregated average-cost sequence has a nondecrease point, then it has
an aggregated Silver-Meal stopping index. -/
theorem exists_aggregated_stop_of_exists_nondecrease
    (agg : DemandAggregator) (S : ScenarioProblem)
    (hex : ∃ L, isAggregatedNondecreasePoint agg S L) :
    ∃ L, isAggregatedSilverMealStop agg S L := by
  exact exists_stop_of_exists_nondecrease (S.aggregate agg) hex

/-- The one-step prefix recurrence survives arbitrary period-wise aggregation. -/
theorem aggregatedHoldingPrefix_succ
    (agg : DemandAggregator) (S : ScenarioProblem) (ℓ : ℕ) :
    aggregatedHoldingPrefix agg S (ℓ + 1) =
      aggregatedHoldingPrefix agg S ℓ +
        (ℓ : ℝ) * (aggregateDemands agg S).getD ℓ 0 := by
  exact holdingPrefix_succ (S.aggregate agg) ℓ

/-- The central solver-oriented theorem also survives arbitrary aggregation.

For any admissible `ℓ`, nondecrease of the aggregated average-cost sequence is
equivalent to the denominator-free inequality over the aggregated demand. -/
theorem aggregated_nondecrease_iff_inequality
    (agg : DemandAggregator) (S : ScenarioProblem) {ℓ : ℕ} (hl : 1 ≤ ℓ) :
    aggregatedAvgCost agg S (ℓ + 1) ≥ aggregatedAvgCost agg S ℓ ↔
      aggregatedInequalityCondition agg S ℓ := by
  exact nondecrease_iff_inequality (S.aggregate agg) hl

/-- Solver-friendly characterization of an aggregated Silver-Meal stop. -/
theorem aggregatedSilverMealStop_iff_verificationCondition
    (agg : DemandAggregator) (S : ScenarioProblem) {L : ℕ} (hL : 1 ≤ L) :
    isAggregatedSilverMealStop agg S L ↔
      (1 ≤ L ∧
       L < scenarioHorizon S ∧
       (∀ j : ℕ, 1 ≤ j → j < L →
          aggregatedAvgCost agg S (j + 1) < aggregatedAvgCost agg S j) ∧
       aggregatedInequalityCondition agg S L) := by
  change isSilverMealStop (S.aggregate agg) L ↔ _
  rw [silverMealStop_iff_verificationCondition (S.aggregate agg) hL]
  simp only [horizon_aggregate]
  rfl

/-! ## Concrete symmetric trimmed mean -/

/-- Sort a list of real-valued forecasts in nondecreasing order. -/
def sortForecasts (xs : List ℝ) : List ℝ :=
  xs.mergeSort (fun x y => decide (x ≤ y))

/-- Values retained after deleting the `k` smallest and `k` largest values.

If `2*k ≥ xs.length`, the retained list is empty. The well-formedness
predicate below excludes this degenerate case when the estimator is used. -/
def trimmedCore (k : ℕ) (xs : List ℝ) : List ℝ :=
  let ys := sortForecasts xs
  (ys.drop k).take (ys.length - 2 * k)

/-- Symmetric `k`-trimmed mean.

The empty-core branch is defined as zero so that this is a total Lean function.
The intended use is guarded by `TrimmedMeanAdmissible k xs`. -/
def trimmedMean (k : ℕ) (xs : List ℝ) : ℝ :=
  let core := trimmedCore k xs
  if core.length = 0 then
    0
  else
    core.sum / (core.length : ℝ)

/-- The trimming parameter leaves at least one forecast after removing both
extremes. -/
def TrimmedMeanAdmissible (k : ℕ) (xs : List ℝ) : Prop :=
  2 * k < xs.length

/-- Every period contains enough forecasts for symmetric `k`-trimming. -/
def ScenarioProblem.TrimmedValid (k : ℕ) (S : ScenarioProblem) : Prop :=
  ∀ xs ∈ S.periodForecasts, TrimmedMeanAdmissible k xs


/--
Two forecast panels are `k`-tail equivalent when symmetric trimming is
admissible for both panels and their retained central blocks are identical.
Thus, the panels may differ in observations removed from the lower and upper
tails, but not in the observations used by the trimmed mean.
-/
def TailEquivalent (k : ℕ) (xs ys : List ℝ) : Prop :=
  TrimmedMeanAdmissible k xs ∧
  TrimmedMeanAdmissible k ys ∧
  trimmedCore k xs = trimmedCore k ys

/--
Two forecasting scenarios are period-wise `k`-tail equivalent when their cost
parameters agree and corresponding forecast panels are `k`-tail equivalent.
-/
def PeriodwiseTailEquivalent
    (k : ℕ) (S₁ S₂ : ScenarioProblem) : Prop :=
  S₁.setupCost = S₂.setupCost ∧
  S₁.holdingCost = S₂.holdingCost ∧
  List.Forall₂ (TailEquivalent k) S₁.periodForecasts S₂.periodForecasts

/-- Tail-equivalent forecast panels have identical symmetric trimmed means. -/
lemma trimmedMean_eq_of_tailEquivalent
    {k : ℕ} {xs ys : List ℝ}
    (hTail : TailEquivalent k xs ys) :
    trimmedMean k xs = trimmedMean k ys := by
  rcases hTail with ⟨_, _, hcore⟩
  simp [trimmedMean, hcore]

/-- Robust demand sequence produced by period-wise trimmed aggregation. -/
def robustDemands (k : ℕ) (S : ScenarioProblem) : List ℝ :=
  aggregateDemands (trimmedMean k) S

/-- Ordinary Silver-Meal problem obtained after robust aggregation. -/
def ScenarioProblem.robustProblem (k : ℕ) (S : ScenarioProblem) : Problem :=
  S.aggregate (trimmedMean k)

/-- Robust weighted prefix cost. -/
def robustHoldingPrefix (k : ℕ) (S : ScenarioProblem) (ℓ : ℕ) : ℝ :=
  holdingPrefix (S.robustProblem k) ℓ

/-- Robust average cost

  A_k(ℓ) = (s + h * Σ_{j=0}^{ℓ-1} j * d̂_j) / ℓ,

where `d̂_j` is the period-wise `k`-trimmed mean. -/
def robustAvgCost (k : ℕ) (S : ScenarioProblem) (ℓ : ℕ) : ℝ :=
  avgCost (S.robustProblem k) ℓ

/-- Robust Silver-Meal stopping predicate. -/
def isRobustSilverMealStop
    (k : ℕ) (S : ScenarioProblem) (L : ℕ) : Prop :=
  isSilverMealStop (S.robustProblem k) L

/-- Robust denominator-free verification condition. -/
def robustInequalityCondition
    (k : ℕ) (S : ScenarioProblem) (ℓ : ℕ) : Prop :=
  inequalityCondition (S.robustProblem k) ℓ

@[simp] theorem robustProblem_demands
    (k : ℕ) (S : ScenarioProblem) :
    (S.robustProblem k).demands = robustDemands k S := by
  rfl

@[simp] theorem robustProblem_horizon
    (k : ℕ) (S : ScenarioProblem) :
    horizon (S.robustProblem k) = scenarioHorizon S := by
  exact horizon_aggregate (trimmedMean k) S



/-- Helper. Tail-equivalent forecast panels produce equal lists of trimmed means. -/
lemma map_trimmedMean_eq_of_forall₂_tailEquivalent
    (k : ℕ)
    {xs ys : List (List ℝ)}
    (h : List.Forall₂ (TailEquivalent k) xs ys) :
    xs.map (trimmedMean k) = ys.map (trimmedMean k) := by
  induction h with
  | nil =>
      rfl
  | cons hxy hrest ih =>
      simp [trimmedMean_eq_of_tailEquivalent hxy, ih]


/-- Period-wise tail equivalence preserves the complete robust demand sequence. -/
theorem robustDemands_eq_of_tailEquivalent
    (k : ℕ) {S₁ S₂ : ScenarioProblem}
    (hTail : PeriodwiseTailEquivalent k S₁ S₂) :
    robustDemands k S₁ = robustDemands k S₂ := by
  rcases hTail with ⟨_, _, hpanels⟩
  unfold robustDemands aggregateDemands
  exact map_trimmedMean_eq_of_forall₂_tailEquivalent k hpanels

/--
Period-wise tail equivalence preserves the complete aggregated Silver-Meal
problem, including cost parameters and the robust demand sequence.
-/
theorem robustProblem_eq_of_tailEquivalent
    (k : ℕ) {S₁ S₂ : ScenarioProblem}
    (hTail : PeriodwiseTailEquivalent k S₁ S₂) :
    S₁.robustProblem k = S₂.robustProblem k := by
  have hdemands : robustDemands k S₁ = robustDemands k S₂ :=
    robustDemands_eq_of_tailEquivalent k hTail
  rcases hTail with ⟨hsetup, hholding, _⟩
  apply Problem.ext'
  · exact hsetup
  · exact hholding
  · simpa [ScenarioProblem.robustProblem, robustDemands,
      ScenarioProblem.aggregate] using hdemands

/--
Robust Stopping Preservation Theorem.

If two scenarios differ only through admissible perturbations of forecast
values discarded by period-wise symmetric trimming, then every robust
Silver-Meal stopping decision is unchanged.
-/
theorem robustSilverMealStop_iff_of_tailEquivalent
    (k : ℕ) {S₁ S₂ : ScenarioProblem}
    (hTail : PeriodwiseTailEquivalent k S₁ S₂)
    (L : ℕ) :
    isRobustSilverMealStop k S₁ L ↔
      isRobustSilverMealStop k S₂ L := by
  unfold isRobustSilverMealStop
  rw [robustProblem_eq_of_tailEquivalent k hTail]

/-- Robust prefix recurrence in the paper's one-based notation:

  H_k(ℓ + 1) = H_k(ℓ) + ℓ * d̂_(ℓ + 1). -/
theorem robustHoldingPrefix_succ
    (k : ℕ) (S : ScenarioProblem) (ℓ : ℕ) :
    robustHoldingPrefix k S (ℓ + 1) =
      robustHoldingPrefix k S ℓ +
        (ℓ : ℝ) * (robustDemands k S).getD ℓ 0 := by
  exact holdingPrefix_succ (S.robustProblem k) ℓ

/-- Robust algebraic characterization
This is the direct robust counterpart of `nondecrease_iff_inequality`.
Robust algebraic characterization in one-based paper notation:

  A_k(ℓ + 1) ≥ A_k(ℓ)
iff
  h * (ℓ^2 * d̂_(ℓ + 1) - H_k(ℓ)) ≥ s.
-/
theorem robust_nondecrease_iff_inequality
    (k : ℕ) (S : ScenarioProblem) {ℓ : ℕ} (hl : 1 ≤ ℓ) :
    robustAvgCost k S (ℓ + 1) ≥ robustAvgCost k S ℓ ↔
      robustInequalityCondition k S ℓ := by
  exact nondecrease_iff_inequality (S.robustProblem k) hl

/-- Auxiliary first-nondecrease characterization of the robust stopping predicate. -/
lemma robustSilverMealStop_iff_firstNondecreasePoint
    (k : ℕ) (S : ScenarioProblem) (L : ℕ) :
    isRobustSilverMealStop k S L ↔
      isFirstNondecreasePoint (S.robustProblem k) L := by
  exact silverMealStop_iff_firstNondecreasePoint (S.robustProblem k) L

/-- Existence of a robust stop whenever the robust average-cost sequence has a
nondecrease point. -/
theorem exists_robust_stop_of_exists_nondecrease
    (k : ℕ) (S : ScenarioProblem)
    (hex : ∃ L, isNondecreasePoint (S.robustProblem k) L) :
    ∃ L, isRobustSilverMealStop k S L := by
  exact exists_stop_of_exists_nondecrease (S.robustProblem k) hex

/-- Solver-friendly characterization of the robust stopping predicate. -/
theorem robustSilverMealStop_iff_verificationCondition
    (k : ℕ) (S : ScenarioProblem) {L : ℕ} (hL : 1 ≤ L) :
    isRobustSilverMealStop k S L ↔
      (1 ≤ L ∧
       L < scenarioHorizon S ∧
       (∀ j : ℕ, 1 ≤ j → j < L →
          robustAvgCost k S (j + 1) < robustAvgCost k S j) ∧
       robustInequalityCondition k S L) := by
  change isSilverMealStop (S.robustProblem k) L ↔ _
  rw [silverMealStop_iff_verificationCondition (S.robustProblem k) hL]
  simp only [robustProblem_horizon]
  rfl

/-! ## Error propagation and decision-stability theory -/

/-- Pointwise error bound between an aggregated demand sequence and a reference
(clean) demand sequence. -/
def DemandErrorBound
    (estimated reference bounds : List ℝ) : Prop :=
  estimated.length = reference.length ∧
  reference.length = bounds.length ∧
  ∀ j : ℕ, j < reference.length →
    |estimated.getD j 0 - reference.getD j 0| ≤ bounds.getD j 0

/-- Absolute error of the denominator-free Silver-Meal score at index `ℓ`.

This score is the left-hand side minus the setup cost. -/
def stoppingScore (P : Problem) (ℓ : ℕ) : ℝ :=
  P.holdingCost *
      ((ℓ : ℝ) * ((ℓ : ℝ) * P.demands.getD ℓ 0) - holdingPrefix P ℓ) -
    P.setupCost

/-- The verification condition is equivalently nonnegativity of the stopping
score. -/
theorem inequalityCondition_iff_stoppingScore_nonneg
    (P : Problem) (ℓ : ℕ) :
    inequalityCondition P ℓ ↔ 0 ≤ stoppingScore P ℓ := by
  unfold inequalityCondition stoppingScore
  constructor
  · intro h
    linarith
  · intro h
    linarith


/-- A generic margin lemma: a Boolean threshold decision is preserved whenever
an approximation error is strictly smaller than the clean positive margin. -/
theorem nonnegative_decision_preserved_of_positive_margin
    {clean estimated ε : ℝ}
    (herr : |estimated - clean| ≤ ε)
    (hmargin : ε < clean) :
    0 < estimated := by
  have hlower : clean - ε ≤ estimated := by
    rw [abs_le] at herr
    linarith
  linarith

/-- Symmetric negative-margin counterpart: the continue decision is preserved
when the error is smaller than the magnitude of a clean negative margin. -/
theorem negative_decision_preserved_of_negative_margin
    {clean estimated ε : ℝ}
    (herr : |estimated - clean| ≤ ε)
    (hmargin : ε < -clean) :
    estimated < 0 := by
  have hupper : estimated ≤ clean + ε := by
    rw [abs_le] at herr
    linarith
  linarith

/-! ## Worked robust aggregation example

Each period has three forecasts. With `k = 1`, the smallest and largest values
are deleted, so the retained value is the median. The central forecasts recreate
the original worked example `[100, 200, 150, 250]` despite one low and one high
outlier per period.
-/

def robustExample : ScenarioProblem :=
  { setupCost := 500
    holdingCost := 2
    periodForecasts :=
      [ [0, 100, 1000],
        [10, 200, 2000],
        [20, 150, 1500],
        [30, 250, 2500] ] }

example : scenarioHorizon robustExample = 4 := by
  rfl



/-- This theorem states the intended outcome of the concrete estimator.
It is kept as an explicit computational checkpoint for the artifact. -/
example : robustDemands 1 robustExample = [100, 200, 150, 250] := by
  norm_num [robustDemands, aggregateDemands, robustExample, trimmedMean,
    trimmedCore, sortForecasts, List.mergeSort]

example : robustExample.robustProblem 1 = exampleProblem := by
  ext <;>
    norm_num [ScenarioProblem.robustProblem, ScenarioProblem.aggregate,
      robustDemands, aggregateDemands, robustExample, exampleProblem,
      trimmedMean, trimmedCore, sortForecasts, List.mergeSort]

/-- Consequently, robust Silver-Meal stops at `L = 2`. -/
theorem robustExample_stop_at_two :
    isRobustSilverMealStop 1 robustExample 2 := by
  change isSilverMealStop (robustExample.robustProblem 1) 2
  convert example_stop_at_two using 1
  ext <;>
    norm_num [ScenarioProblem.robustProblem, ScenarioProblem.aggregate,
      aggregateDemands, robustExample, exampleProblem, trimmedMean,
      trimmedCore, sortForecasts, List.mergeSort]

/-!
The results above establish the compositional theory needed by the paper:

1. period-wise aggregation produces a standard Silver-Meal instance;
2. admissible tail perturbations preserve every period-wise trimmed aggregate;
3. equality of the robust demand sequence propagates to equality of the full
   aggregated problem and invariance of every stopping decision;
4. the first-nondecrease and denominator-free algebraic characterizations are
   retained as auxiliary verification results; and
5. generic margin lemmas support further decision-stability analyses beyond
   exact tail invariance.

-/

end
end SilverMeal
end WagnerWhitin
