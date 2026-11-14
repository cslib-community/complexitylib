/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.BinarySearch
public import CslibFrontier.Computability.Complexity.Classes.Oracle.BoundedQuery
public import CslibFrontier.Computability.Complexity.Classes.Oracle.PolyTime
public import CslibFrontier.Computability.Complexity.FineGrained.MaxSAT.Histogram
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Logics.Propositional.CNF.ModelCount
import CslibFrontier.Logics.Propositional.CNF.Eval
import CslibFrontier.Computability.Complexity.Classes.NP.Closure
import CslibFrontier.Computability.Complexity.Classes.NP.Image
import CslibFrontier.Computability.Complexity.Classes.Oracle.Closure
import CslibFrontier.Computability.Complexity.Classes.Oracle.Monotone
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Complexity.Problems.SAT.Units
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinarySizeFacts
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Tactic.EncLen

/-!
# Threshold optimization by binary search and witness recovery

Optimization over a bounded integer objective `[0, bound x]` reduces to logarithmic threshold
decision queries followed by witness search at the optimal threshold
[Papadimitriou, Section 17.1][Papadimitriou94], [Arora and Barak, Section 2.5][AroraBarak09].

1. **Abstract `TimeM` threshold optimization (`MaxThresholdSpec`, `MinThresholdSpec`)**:
   bisection via `Cslib.Algorithms.Lean.lowerBoundM` finds the exact maximum or minimum feasible
   objective value (or `none` when no valid witness exists) in at most
   `Nat.log 2 (bound x + 1) + 1` threshold probes, and composes with a witness-at-threshold
   finder to return an optimal witness.
2. **Native oracle binary search (`bisectProgram`,
   `computableInPolyTimeWithOracleQueries_bisect`)**: a fixed-iteration adaptive `WordQueryComp`
   loop over `[lo x, hi x)` runs `(hi x - lo x).size` rounds, agrees identically with
   `lowerBoundM`, makes at most `(hi x - lo x).size ≤ Nat.log 2 (hi x - lo x) + 1` oracle
   requests (all at midpoints in `[lo x, hi x)`), and is strict oracle PPT (`IsOraclePPTOn`) even
   for exponentially large binary bounds `hi x`. Sequencing with an oracle witness-recovery
   program (`ComputableInPolyTimeWithOracleQueries.bind_with`) recovers both the optimal value
   and an optimal witness, collapsing to plain `ComputableInPolyTime` when the oracle lies in `P`.
3. **Max-SAT optimization and optimal assignment recovery (`MaxSATThreshold`, `solveMaxSAT`)**:
   for `φ : CNF ℕ`, binary search over `MaxSATQuery` (`[1, φ.length + 1)`) finds the maximum
   satisfied-clause count `maxClauseScore φ`, and variable-by-variable partial evaluation over
   `φ.distinctVars` recovers an assignment achieving `maxClauseScore φ` in at most
   `φ.length.size + φ.numVars ≤ (Nat.log 2 φ.length + 1) + φ.numVars` queries to the `NP`
   language `MaxSATThreshold`, with every queried instance no longer than `⟨φ, φ.length⟩`.

The Max-SAT client here works in `P^NP`: instances are bare `φ : CNF ℕ`, every assignment
`ℕ → Bool` is admissible, the query `MaxSATQuery` carries a binary target, and the oracle is the
`NP` language `MaxSATThreshold` itself. `FineGrained.MaxSAT.Reduction` instead fixes a declared
variable count (`MaxSAT.StructInstance`, assignments in `BitString n`), takes a unary cutoff
(`MaxSAT.ThresholdQuery`), and compiles each threshold query through `MaxSAT.thresholdCircuit` to a
3-CNF for a supplied fixed-width `k`-SAT solver (`optimumByBinarySearchM`,
`optimizeByBinarySearchM`). The two optima agree on well-formed instances:
`MaxSAT.maxClauseScore_eq_optimum` gives `maxClauseScore φ = MaxSAT.optimum (n, φ)` when every
variable of `φ` is below `n`.

## Main definitions

* `Cslib.Complexity.BisectInterval`, `Cslib.Complexity.bisectStep`: interval state and single
  bisection step.
* `Cslib.Complexity.OracleThresholdQuery`, `Cslib.Complexity.OptSolution`: typed query and
  value-witness structures with encodings `encOracleThresholdQuery` and `encOptSolution`.
* `Cslib.Complexity.MaxThresholdSpec`, `Cslib.Complexity.MinThresholdSpec`: bounded maximization
  and minimization threshold specifications with `TimeM` solvers.
* `Cslib.Complexity.bisectProgram`: native adaptive oracle bisection program.
* `Cslib.Complexity.MaxSATQuery`, `Cslib.Complexity.MaxSATSolution`,
  `Cslib.Complexity.MaxSATThreshold`, `Cslib.Complexity.MaxSAT.solveMaxSAT`: Max-SAT threshold
  language and oracle optimization-with-witness solver.

## Main results

* `Cslib.Complexity.iterate_bisectStep_eq_lowerBoundM`: `(hi - lo).size` bisection steps equal
  `lowerBoundM`.
* `Cslib.Complexity.MaxThresholdSpec.maxOptWitnessM_spec`,
  `Cslib.Complexity.MinThresholdSpec.minOptWitnessM_spec`: correctness and `O(log M)` probe bounds
  for `TimeM` maximization and minimization with witness recovery.
* `Cslib.Complexity.ComputableInPolyTimeWithOracleQueries.bind_with`: query-bounded sequential
  oracle composition.
* `Cslib.Complexity.computableInPolyTimeWithOracleQueries_bisect`: polynomial-time oracle
  bisection with explicit query count `(hi x - lo x).size ≤ Nat.log 2 (hi x - lo x) + 1` and
  midpoint query-length control.
* `Cslib.Complexity.MaxSAT.computableInPolyTimeWithOracleQueries_solveMaxSAT`,
  `Cslib.Complexity.MaxSAT.solveMaxSAT_spec`,
  `Cslib.Complexity.MaxSAT.computableInPolyTime_solveMaxSAT_of_mem_P`: Max-SAT optimal value
  and optimal assignment recovery relative to `MaxSATThreshold ∈ NP` and when
  `encMaxSATQuery '' MaxSATThreshold ∈ P encBits`.
* `Cslib.Complexity.MaxSAT.maxClauseScore_eq_optimum`: on declared-range formulas, the
  binary-search optimum equals the fine-grained `MaxSAT.optimum`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [C. H. Papadimitriou, *Computational Complexity*][Papadimitriou94]
-/

public section

namespace Cslib

/-- Every request made during `n` rounds of `OracleComp.iterate` arises from `step` at a state
satisfying any invariant preserved by `interpret (m := Id) answer`. -/
theorem OracleComp.mem_queriesWith_iterate {ι State : Type} {spec : OracleSpec.{0, 0} ι}
    (answer : (q : ι) → spec q) {step : State → OracleComp spec State} {st₀ : State}
    {inv : State → Prop} (hinv0 : inv st₀)
    (hpres : ∀ st, inv st → inv (interpret (m := Id) answer (step st)))
    {n : ℕ} {q : ι} (hq : q ∈ queriesWith answer (iterate n step st₀)) :
    ∃ st, inv st ∧ q ∈ queriesWith answer (step st) := by
  induction n generalizing st₀ with
  | zero => simp at hq
  | succ n ih =>
    rw [iterate_succ_bind, queriesWith_bind, List.mem_append] at hq
    rcases hq with hfirst | hrest
    · exact ⟨st₀, hinv0, hfirst⟩
    · exact ih (hpres st₀ hinv0) hrest

namespace Complexity

open Cslib.Algorithms.Lean Cslib.Logic.PL Probability Turing.MultiTapeTM

/-! ### Structures and encodings -/

/-- Active half-open interval `[lo, hi)` maintained during threshold binary search. -/
structure BisectInterval where
  /-- Inclusive lower bound of the remaining search interval. -/
  lo : ℕ
  /-- Exclusive upper bound of the remaining search interval. -/
  hi : ℕ
  deriving DecidableEq, Repr

/-- Framed binary-pair encoding of `BisectInterval`. -/
enc_structure encBisectInterval : BisectInterval where
  lo : encNat, hi : encNat

/-- An instance `inst` paired with an integer objective threshold `target`. -/
structure OracleThresholdQuery (α : Type) where
  /-- Underlying problem instance. -/
  inst : α
  /-- Candidate objective threshold. -/
  target : ℕ
  deriving DecidableEq, Repr

/-- Encoding of `OracleThresholdQuery α` as the framed pair of `encA` and binary `encNat`. -/
@[expose]
def encOracleThresholdQuery {α : Type} (encA : α ↪ List Bool) :
    OracleThresholdQuery α ↪ List Bool :=
  ⟨fun q => encPair encA encNat (q.inst, q.target), fun x y h => by
    have h' := (encPair encA encNat).injective h
    cases x; cases y; simp_all⟩

@[simp] theorem encOracleThresholdQuery_apply {α : Type} (encA : α ↪ List Bool)
    (q : OracleThresholdQuery α) :
    encOracleThresholdQuery encA q = encPair encA encNat (q.inst, q.target) :=
  rfl

private theorem computableInDegree_thresholdQueryFields {α : Type} (encA : α ↪ List Bool) :
    ComputableInDegree (fun q : OracleThresholdQuery α => (q.inst, q.target))
      (encOracleThresholdQuery encA) (encPair encA encNat) 1 1 :=
  ComputableInDegree.of_eq fun _ => rfl

/-- Projecting `OracleThresholdQuery.inst` is polynomial-time. -/
@[scoped fun_prop]
theorem encOracleThresholdQuery_inst_polyTime {α γ : Type} {encA : α ↪ List Bool}
    {encIn : γ ↪ List Bool} {g : γ → OracleThresholdQuery α}
    (h : ComputableInPolyTime g encIn (encOracleThresholdQuery encA)) :
    ComputableInPolyTime (fun a => (g a).inst) encIn encA :=
  (ComputableInDegree.fst' (computableInDegree_thresholdQueryFields encA)).computableInPolyTime.comp
    h

/-- Projecting `OracleThresholdQuery.target` is polynomial-time. -/
@[scoped fun_prop]
theorem encOracleThresholdQuery_target_polyTime {α γ : Type} {encA : α ↪ List Bool}
    {encIn : γ ↪ List Bool} {g : γ → OracleThresholdQuery α}
    (h : ComputableInPolyTime g encIn (encOracleThresholdQuery encA)) :
    ComputableInPolyTime (fun a => (g a).target) encIn encNat :=
  (ComputableInDegree.snd' (computableInDegree_thresholdQueryFields encA)).computableInPolyTime.comp
    h

/-- Constructing an `OracleThresholdQuery` from polynomial-time components is polynomial-time. -/
@[scoped fun_prop]
theorem encOracleThresholdQuery_mk_polyTime {α γ : Type} {encA : α ↪ List Bool}
    {encIn : γ ↪ List Bool} {inst : γ → α} {target : γ → ℕ}
    (hi : ComputableInPolyTime inst encIn encA)
    (ht : ComputableInPolyTime target encIn encNat) :
    ComputableInPolyTime (fun a => OracleThresholdQuery.mk (inst a) (target a))
      encIn (encOracleThresholdQuery encA) :=
  (hi.prod ht).of_enc_eq fun _ => rfl

/-- An optimal objective value paired with a witness attaining it. -/
structure OptSolution (β : Type) where
  /-- Optimal objective value. -/
  optValue : ℕ
  /-- Witness attaining `optValue`. -/
  witness : β
  deriving DecidableEq, Repr

/-- Encoding of `OptSolution β` as the framed pair of binary `encNat` and `encB`. -/
@[expose]
def encOptSolution {β : Type} (encB : β ↪ List Bool) : OptSolution β ↪ List Bool :=
  ⟨fun s => encPair encNat encB (s.optValue, s.witness), fun x y h => by
    have h' := (encPair encNat encB).injective h
    cases x; cases y; simp_all⟩

@[simp] theorem encOptSolution_apply {β : Type} (encB : β ↪ List Bool) (s : OptSolution β) :
    encOptSolution encB s = encPair encNat encB (s.optValue, s.witness) :=
  rfl

private theorem computableInDegree_optSolutionFields {β : Type} (encB : β ↪ List Bool) :
    ComputableInDegree (fun s : OptSolution β => (s.optValue, s.witness))
      (encOptSolution encB) (encPair encNat encB) 1 1 :=
  ComputableInDegree.of_eq fun _ => rfl

/-- Projecting `OptSolution.optValue` is polynomial-time. -/
@[scoped fun_prop]
theorem encOptSolution_optValue_polyTime {β γ : Type} {encB : β ↪ List Bool}
    {encIn : γ ↪ List Bool} {g : γ → OptSolution β}
    (h : ComputableInPolyTime g encIn (encOptSolution encB)) :
    ComputableInPolyTime (fun a => (g a).optValue) encIn encNat :=
  (ComputableInDegree.fst' (computableInDegree_optSolutionFields encB)).computableInPolyTime.comp h

/-- Projecting `OptSolution.witness` is polynomial-time. -/
@[scoped fun_prop]
theorem encOptSolution_witness_polyTime {β γ : Type} {encB : β ↪ List Bool}
    {encIn : γ ↪ List Bool} {g : γ → OptSolution β}
    (h : ComputableInPolyTime g encIn (encOptSolution encB)) :
    ComputableInPolyTime (fun a => (g a).witness) encIn encB :=
  (ComputableInDegree.snd' (computableInDegree_optSolutionFields encB)).computableInPolyTime.comp h

/-- Constructing an `OptSolution` from polynomial-time components is polynomial-time. -/
@[scoped fun_prop]
theorem encOptSolution_mk_polyTime {β γ : Type} {encB : β ↪ List Bool}
    {encIn : γ ↪ List Bool} {v : γ → ℕ} {w : γ → β}
    (hv : ComputableInPolyTime v encIn encNat)
    (hw : ComputableInPolyTime w encIn encB) :
    ComputableInPolyTime (fun a => OptSolution.mk (v a) (w a)) encIn (encOptSolution encB) :=
  (hv.prod hw).of_enc_eq fun _ => rfl

/-! ### Pure bisection iteration and `lowerBoundM` bridge -/

/-- One pure step of bisection on `[iv.lo, iv.hi)` for a Boolean test `test`. -/
def bisectStep (test : ℕ → Bool) (iv : BisectInterval) : BisectInterval :=
  if iv.lo < iv.hi then
    let mid := (iv.lo + iv.hi) / 2
    if test mid then ⟨mid + 1, iv.hi⟩ else ⟨iv.lo, mid⟩
  else iv

private theorem bisectStep_width_le (test : ℕ → Bool) (iv : BisectInterval) :
    (bisectStep test iv).hi - (bisectStep test iv).lo ≤ (iv.hi - iv.lo) / 2 := by
  unfold bisectStep
  dsimp only
  split_ifs with hlt hb
  · change iv.hi - ((iv.lo + iv.hi) / 2 + 1) ≤ (iv.hi - iv.lo) / 2
    omega
  · change (iv.lo + iv.hi) / 2 - iv.lo ≤ (iv.hi - iv.lo) / 2
    omega
  · omega

private theorem iterate_bisectStep_width_le (test : ℕ → Bool) (k : ℕ) (iv : BisectInterval) :
    ((bisectStep test)^[k] iv).hi - ((bisectStep test)^[k] iv).lo ≤ (iv.hi - iv.lo) / 2 ^ k := by
  induction k generalizing iv with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    calc ((bisectStep test)^[k] (bisectStep test iv)).hi -
          ((bisectStep test)^[k] (bisectStep test iv)).lo
        ≤ ((bisectStep test iv).hi - (bisectStep test iv).lo) / 2 ^ k := ih _
      _ ≤ ((iv.hi - iv.lo) / 2) / 2 ^ k := Nat.div_le_div_right (bisectStep_width_le test iv)
      _ = (iv.hi - iv.lo) / 2 ^ (k + 1) := by rw [Nat.div_div_eq_div_mul, ← pow_succ']

/-- **Correctness of fixed-count bisection.** If `test` is antitone on `[lo, hi)`, iterating
`bisectStep test` `(hi - lo).size` times from `⟨lo, hi⟩` yields an index `k` in `[lo, max lo hi]`
such that `test` holds on `[lo, k)` and fails on `[k, hi)`. -/
theorem iterate_bisectStep_spec {test : ℕ → Bool} {lo hi : ℕ}
    (hmono : ∀ m m', lo ≤ m → m ≤ m' → m' < hi → test m' = true → test m = true) :
    let k := ((bisectStep test)^[(hi - lo).size] ⟨lo, hi⟩).lo
    lo ≤ k ∧ k ≤ max lo hi ∧
      (∀ m, lo ≤ m → m < k → test m = true) ∧
      (∀ m, k ≤ m → m < hi → test m = false) := by
  have hinv : ∀ s,
      let iv := (bisectStep test)^[s] ⟨lo, hi⟩
      lo ≤ iv.lo ∧ iv.lo ≤ max lo hi ∧ (iv.lo < iv.hi → iv.hi ≤ hi) ∧
        (∀ m, lo ≤ m → m < iv.lo → test m = true) ∧
        (∀ m, max iv.lo iv.hi ≤ m → m < hi → test m = false) := by
    intro s
    induction s with
    | zero =>
      dsimp only [Function.iterate_zero, id_eq]
      refine ⟨le_refl _, le_max_left _ _, fun _ => le_refl _, fun _ h1 h2 => by omega,
        fun _ h1 h2 => by omega⟩
    | succ s ih =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := ih
      rw [Function.iterate_succ_apply']
      set iv := (bisectStep test)^[s] ⟨lo, hi⟩
      unfold bisectStep
      dsimp only
      split_ifs with hlt hb
      · have hhi := h3 hlt
        simp only
        refine ⟨by omega, by omega, fun _ => hhi, fun m hm hmk => ?_, fun m hm hmk => ?_⟩
        · rcases Nat.lt_or_ge m iv.lo with hmlo | hmge
          · exact h4 m hm hmlo
          · exact hmono m ((iv.lo + iv.hi) / 2) hm (by omega) (by omega) hb
        · exact h5 m (by omega) hmk
      · have hhi := h3 hlt
        simp only
        refine ⟨h1, h2, fun _ => by omega, h4, fun m hm hmk => ?_⟩
        rcases Nat.lt_or_ge m iv.hi with hmhi | hmge
        · cases htm : test m
          · rfl
          · have ht := hmono ((iv.lo + iv.hi) / 2) m (by omega) (by omega) hmk htm
            exact absurd ht hb
        · exact h5 m (by omega) hmk
      · exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨h1, h2, -, h4, h5⟩ := hinv (hi - lo).size
  have hw := iterate_bisectStep_width_le test (hi - lo).size ⟨lo, hi⟩
  dsimp only at hw
  set final := (bisectStep test)^[(hi - lo).size] ⟨lo, hi⟩
  have hdiv : (hi - lo) / 2 ^ (hi - lo).size = 0 :=
    Nat.div_eq_of_lt (Nat.lt_size_self (hi - lo))
  have hmax : max final.lo final.hi = final.lo := max_eq_left (by omega)
  exact ⟨h1, h2, h4, fun m hm hmk => h5 m (by omega) hmk⟩

/-- **Fixed-count bisection equals `lowerBoundM`** on every antitone test. -/
theorem iterate_bisectStep_eq_lowerBoundM (t : ℕ → TimeM ℕ Bool) {lo hi : ℕ}
    (hmono : ∀ m m', lo ≤ m → m ≤ m' → m' < hi → (t m').ret = true → (t m).ret = true) :
    ((bisectStep (fun m => (t m).ret))^[(hi - lo).size] ⟨lo, hi⟩).lo =
      (lowerBoundM t lo hi).ret := by
  obtain ⟨h1, h2, h3, h4⟩ := iterate_bisectStep_spec (test := fun m => (t m).ret) hmono
  obtain ⟨g1, g2, g3, g4⟩ := lowerBoundM_spec t hmono
  set k₁ := ((bisectStep (fun m => (t m).ret))^[(hi - lo).size] ⟨lo, hi⟩).lo
  set k₂ := (lowerBoundM t lo hi).ret
  rcases Nat.lt_or_ge lo hi with hlt | hge
  · have hm1 : k₁ ≤ hi := by omega
    have hm2 : k₂ ≤ hi := by omega
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hk | hk
    · have ht := g3 k₁ h1 hk
      have hf := h4 k₁ (le_refl _) (by omega)
      rw [ht] at hf
      exact Bool.noConfusion hf
    · have ht := h3 k₂ g1 hk
      have hf := g4 k₂ (le_refl _) (by omega)
      rw [ht] at hf
      exact Bool.noConfusion hf
  · have : max lo hi = lo := max_eq_left hge
    omega

/-! ### Bounded maximization and minimization in `TimeM` -/

/-- Specification of a bounded integer maximization problem on instances `α` and witnesses `β`:
valid witnesses of `x` have integer score bounded by `bound x`. -/
structure MaxThresholdSpec (α β : Type) where
  /-- Feasibility predicate for candidate witnesses of an instance. -/
  valid : α → β → Prop
  /-- Objective score of a candidate witness. -/
  score : α → β → ℕ
  /-- Upper bound on achievable scores for each instance. -/
  bound : α → ℕ
  /-- Every valid witness has score at most `bound x`. -/
  score_le_bound : ∀ x w, valid x w → score x w ≤ bound x

namespace MaxThresholdSpec

variable {α β : Type} (S : MaxThresholdSpec α β)

/-- Threshold decision predicate: some valid witness of `x` achieves score at least `q`. -/
@[expose]
def atLeast (x : α) (q : ℕ) : Prop :=
  ∃ w, S.valid x w ∧ q ≤ S.score x w

theorem atLeast_antitone {x : α} {q q' : ℕ} (hle : q ≤ q') (hq' : S.atLeast x q') :
    S.atLeast x q := by
  obtain ⟨w, hw, hsc⟩ := hq'
  exact ⟨w, hw, hle.trans hsc⟩

theorem not_atLeast_succ_bound (x : α) : ¬ S.atLeast x (S.bound x + 1) := by
  rintro ⟨w, hw, hsc⟩
  have := S.score_le_bound x w hw
  omega

/-- Find the exact maximum score of `x` (or `none` if `x` has no valid witness) by bisection on
`[0, S.bound x + 1)` in `TimeM`. -/
def maxOptM (probe : α → ℕ → TimeM ℕ Bool) (x : α) : TimeM ℕ (Option ℕ) := do
  let k ← lowerBoundM (probe x) 0 (S.bound x + 1)
  return if k = 0 then none else some (k - 1)

/-- Correctness of `maxOptM`: returns `none` iff no valid witness exists, and `some v` when `v`
is the exact maximum score over valid witnesses. -/
theorem maxOptM_spec {probe : α → ℕ → TimeM ℕ Bool} {x : α}
    (hprobe : ∀ q, q ≤ S.bound x → ((probe x q).ret = true ↔ S.atLeast x q)) :
    ((S.maxOptM probe x).ret = none ↔ ¬ ∃ w, S.valid x w) ∧
      ∀ v, (S.maxOptM probe x).ret = some v →
        v ≤ S.bound x ∧ S.atLeast x v ∧ ∀ w, S.valid x w → S.score x w ≤ v := by
  have hmono : ∀ m m', 0 ≤ m → m ≤ m' → m' < S.bound x + 1 →
      (probe x m').ret = true → (probe x m).ret = true := by
    intro m m' _ hmm' hm' ht
    exact (hprobe m (by omega)).mpr
      (S.atLeast_antitone hmm' ((hprobe m' (by omega)).mp ht))
  obtain ⟨hlo, hhi, htrue, hfalse⟩ := lowerBoundM_spec (probe x) (lo := 0) (hi := S.bound x + 1)
    hmono
  simp only [maxOptM, TimeM.ret_bind, TimeM.ret_pure]
  set k := (lowerBoundM (probe x) 0 (S.bound x + 1)).ret
  have hk_le : k ≤ S.bound x + 1 := by omega
  constructor
  · constructor
    · intro hnone ⟨w, hw⟩
      split_ifs at hnone with hk0
      have hf := hfalse 0 (by omega) (by omega)
      have ht : (probe x 0).ret = true := (hprobe 0 (Nat.zero_le _)).mpr ⟨w, hw, Nat.zero_le _⟩
      rw [ht] at hf
      exact Bool.noConfusion hf
    · intro hno
      split_ifs with hk0
      · rfl
      · exfalso
        have ht := htrue 0 (Nat.zero_le _) (by omega)
        obtain ⟨w, hw, -⟩ := (hprobe 0 (Nat.zero_le _)).mp ht
        exact hno ⟨w, hw⟩
  · intro v hv
    split_ifs at hv with hk0
    injection hv with hv'
    subst hv'
    have hv_le : k - 1 ≤ S.bound x := by omega
    have hat : S.atLeast x (k - 1) :=
      (hprobe (k - 1) hv_le).mp (htrue (k - 1) (Nat.zero_le _) (by omega))
    refine ⟨hv_le, hat, fun w hw => ?_⟩
    by_contra! hgt
    have hle' : k ≤ S.bound x := by
      have := S.score_le_bound x w hw
      omega
    have ht : (probe x k).ret = true := (hprobe k hle').mpr ⟨w, hw, by omega⟩
    have hf := hfalse k (le_refl k) (by omega)
    rw [ht] at hf
    exact Bool.noConfusion hf

/-- Time bound for `maxOptM`: at most `c * (⌊log₂ (bound x + 1)⌋ + 1)` ticks when each probe
costs at most `c`. -/
theorem maxOptM_time_le (probe : α → ℕ → TimeM ℕ Bool) {x : α} {c : ℕ}
    (hc : ∀ q, (probe x q).time ≤ c) :
    (S.maxOptM probe x).time ≤ c * (Nat.log 2 (S.bound x + 1) + 1) := by
  simpa [maxOptM] using lowerBoundM_time_le (probe x) hc 0 (S.bound x + 1)

/-- Recover both the maximum score and an optimal witness in `TimeM` by running `maxOptM` and
invoking `findWitness` once at the optimal threshold. -/
def maxOptWitnessM (probe : α → ℕ → TimeM ℕ Bool) (findWitness : α → ℕ → TimeM ℕ β) (x : α) :
    TimeM ℕ (Option (OptSolution β)) := do
  match ← S.maxOptM probe x with
  | none => return none
  | some v =>
    let w ← findWitness x v
    return some ⟨v, w⟩

/-- Correctness of `maxOptWitnessM`. -/
theorem maxOptWitnessM_spec {probe : α → ℕ → TimeM ℕ Bool} {findWitness : α → ℕ → TimeM ℕ β}
    {x : α} (hprobe : ∀ q, q ≤ S.bound x → ((probe x q).ret = true ↔ S.atLeast x q))
    (hwit : ∀ q, q ≤ S.bound x → S.atLeast x q →
      S.valid x (findWitness x q).ret ∧ q ≤ S.score x (findWitness x q).ret) :
    ((S.maxOptWitnessM probe findWitness x).ret = none ↔ ¬ ∃ w, S.valid x w) ∧
      ∀ sol, (S.maxOptWitnessM probe findWitness x).ret = some sol →
        sol.optValue ≤ S.bound x ∧ S.valid x sol.witness ∧
          S.score x sol.witness = sol.optValue ∧
          ∀ w, S.valid x w → S.score x w ≤ sol.optValue := by
  obtain ⟨hnone, hsome⟩ := S.maxOptM_spec hprobe
  unfold maxOptWitnessM
  rw [TimeM.ret_bind]
  cases hm : (S.maxOptM probe x).ret with
  | none =>
    simp only [TimeM.ret_pure, true_iff, reduceCtorEq, IsEmpty.forall_iff, implies_true, and_true]
    exact hnone.mp hm
  | some v =>
    obtain ⟨hv_le, hat, hmax⟩ := hsome v hm
    obtain ⟨hvw, hvsc⟩ := hwit v hv_le hat
    simp only [TimeM.ret_bind, TimeM.ret_pure, reduceCtorEq, false_iff, Option.some.injEq,
      forall_eq']
    exact ⟨fun hno => hno ⟨_, hvw⟩, hv_le, hvw, le_antisymm (hmax _ hvw) hvsc, hmax⟩

theorem maxOptWitnessM_time_le (probe : α → ℕ → TimeM ℕ Bool)
    (findWitness : α → ℕ → TimeM ℕ β) {x : α} {cp cw : ℕ}
    (hcp : ∀ q, (probe x q).time ≤ cp)
    (hcw : ∀ q, q ≤ S.bound x → (findWitness x q).time ≤ cw)
    (hprobe : ∀ q, q ≤ S.bound x → ((probe x q).ret = true ↔ S.atLeast x q)) :
    (S.maxOptWitnessM probe findWitness x).time ≤
      cp * (Nat.log 2 (S.bound x + 1) + 1) + cw := by
  have hbase := S.maxOptM_time_le probe hcp
  obtain ⟨-, hsome⟩ := S.maxOptM_spec hprobe
  unfold maxOptWitnessM
  rw [TimeM.time_bind]
  cases hm : (S.maxOptM probe x).ret with
  | none =>
    simp only [TimeM.time_pure]
    omega
  | some v =>
    have hv_le := (hsome v hm).1
    have hw := hcw v hv_le
    simp only [TimeM.time_bind, TimeM.time_pure]
    omega

end MaxThresholdSpec

/-- Specification of a bounded integer minimization problem on instances `α` and witnesses `β`:
valid witnesses of `x` have integer cost bounded by `bound x`. -/
structure MinThresholdSpec (α β : Type) where
  /-- Feasibility predicate for candidate witnesses of an instance. -/
  valid : α → β → Prop
  /-- Objective cost of a candidate witness. -/
  cost : α → β → ℕ
  /-- Upper bound on the cost of valid witnesses. -/
  bound : α → ℕ
  /-- Every valid witness has cost at most `bound x`. -/
  cost_le_bound : ∀ x w, valid x w → cost x w ≤ bound x

namespace MinThresholdSpec

variable {α β : Type} (S : MinThresholdSpec α β)

/-- Threshold decision predicate: some valid witness of `x` has cost at most `q`. -/
@[expose]
def atMost (x : α) (q : ℕ) : Prop :=
  ∃ w, S.valid x w ∧ S.cost x w ≤ q

theorem atMost_monotone {x : α} {q q' : ℕ} (hle : q ≤ q') (hq : S.atMost x q) :
    S.atMost x q' := by
  obtain ⟨w, hw, hc⟩ := hq
  exact ⟨w, hw, hc.trans hle⟩

/-- Find the exact minimum cost of `x` (or `none` if `x` has no valid witness) by bisecting the
negated threshold predicate on `[0, S.bound x + 1)` in `TimeM`. -/
def minOptM (probe : α → ℕ → TimeM ℕ Bool) (x : α) : TimeM ℕ (Option ℕ) := do
  let k ← lowerBoundM (fun q => Bool.not <$> probe x q) 0 (S.bound x + 1)
  return if k ≤ S.bound x then some k else none

/-- Recover both the minimum cost and an optimal witness in `TimeM`. -/
def minOptWitnessM (probe : α → ℕ → TimeM ℕ Bool) (findWitness : α → ℕ → TimeM ℕ β) (x : α) :
    TimeM ℕ (Option (OptSolution β)) := do
  match ← S.minOptM probe x with
  | none => return none
  | some v =>
    let w ← findWitness x v
    return some ⟨v, w⟩

/-- Correctness of `minOptWitnessM`. -/
theorem minOptWitnessM_spec {probe : α → ℕ → TimeM ℕ Bool} {findWitness : α → ℕ → TimeM ℕ β}
    {x : α} (hprobe : ∀ q, q ≤ S.bound x → ((probe x q).ret = true ↔ S.atMost x q))
    (hwit : ∀ q, q ≤ S.bound x → S.atMost x q →
      S.valid x (findWitness x q).ret ∧ S.cost x (findWitness x q).ret ≤ q) :
    ((S.minOptWitnessM probe findWitness x).ret = none ↔ ¬ ∃ w, S.valid x w) ∧
      ∀ sol, (S.minOptWitnessM probe findWitness x).ret = some sol →
        sol.optValue ≤ S.bound x ∧ S.valid x sol.witness ∧
          S.cost x sol.witness = sol.optValue ∧
          ∀ w, S.valid x w → sol.optValue ≤ S.cost x w := by
  have hmono : ∀ m m', 0 ≤ m → m ≤ m' → m' < S.bound x + 1 →
      (Bool.not <$> probe x m').ret = true → (Bool.not <$> probe x m).ret = true := by
    intro m m' _ hmm' hm' ht
    simp only [TimeM.ret_map, Bool.not_eq_true'] at ht ⊢
    cases hm_val : (probe x m).ret
    · rfl
    · have hat := S.atMost_monotone hmm' ((hprobe m (by omega)).mp hm_val)
      have ht' := (hprobe m' (by omega)).mpr hat
      rw [ht] at ht'
      exact Bool.noConfusion ht'
  obtain ⟨-, hhi, htrue, hfalse⟩ :=
    lowerBoundM_spec (fun q => Bool.not <$> probe x q) (lo := 0) (hi := S.bound x + 1) hmono
  set k := (lowerBoundM (fun q => Bool.not <$> probe x q) 0 (S.bound x + 1)).ret with hk_def
  unfold minOptWitnessM minOptM
  simp only [TimeM.ret_bind, TimeM.ret_pure, ← hk_def]
  by_cases hle : k ≤ S.bound x
  · simp only [hle, ↓reduceIte, TimeM.ret_bind, TimeM.ret_pure]
    have hf := hfalse k (le_refl k) (by omega)
    simp only [TimeM.ret_map, Bool.not_eq_false'] at hf
    have hat : S.atMost x k := (hprobe k hle).mp hf
    obtain ⟨hvw, hvc⟩ := hwit k hle hat
    have hmin : ∀ w, S.valid x w → k ≤ S.cost x w := by
      intro w hw
      by_contra! hlt
      have ht := htrue (S.cost x w) (Nat.zero_le _) hlt
      simp only [TimeM.ret_map, Bool.not_eq_true'] at ht
      have ht' := (hprobe (S.cost x w) (S.cost_le_bound x w hw)).mpr ⟨w, hw, le_refl _⟩
      rw [ht] at ht'
      exact Bool.noConfusion ht'
    refine ⟨⟨fun hno => (by cases hno), fun hno => absurd ⟨_, hvw⟩ hno⟩, ?_⟩
    rintro sol hsol
    injection hsol with hsol
    subst hsol
    exact ⟨hle, hvw, le_antisymm hvc (hmin _ hvw), hmin⟩
  · simp only [hle, ↓reduceIte, TimeM.ret_pure, true_iff, reduceCtorEq, IsEmpty.forall_iff,
      implies_true, and_true]
    rintro ⟨w, hw⟩
    have hwb := S.cost_le_bound x w hw
    have ht := htrue (S.cost x w) (Nat.zero_le _) (by omega)
    simp only [TimeM.ret_map, Bool.not_eq_true'] at ht
    have ht' := (hprobe (S.cost x w) hwb).mpr ⟨w, hw, le_refl _⟩
    rw [ht] at ht'
    exact Bool.noConfusion ht'

theorem minOptWitnessM_time_le (probe : α → ℕ → TimeM ℕ Bool)
    (findWitness : α → ℕ → TimeM ℕ β) {x : α} {cp cw : ℕ}
    (hcp : ∀ q, (probe x q).time ≤ cp)
    (hcw : ∀ q, q ≤ S.bound x → (findWitness x q).time ≤ cw) :
    (S.minOptWitnessM probe findWitness x).time ≤
      cp * (Nat.log 2 (S.bound x + 1) + 1) + cw := by
  have hbase : (S.minOptM probe x).time ≤ cp * (Nat.log 2 (S.bound x + 1) + 1) := by
    simpa [minOptM] using lowerBoundM_time_le (fun q => Bool.not <$> probe x q)
      (fun q => by simpa using hcp q) 0 (S.bound x + 1)
  have hbound : ∀ v, (S.minOptM probe x).ret = some v → v ≤ S.bound x := by
    intro v hv
    simp only [minOptM, TimeM.ret_bind, TimeM.ret_pure] at hv
    split_ifs at hv with hle
    injection hv with hv'
    omega
  unfold minOptWitnessM
  rw [TimeM.time_bind]
  cases hm : (S.minOptM probe x).ret with
  | none =>
    simp only [TimeM.time_pure]
    omega
  | some v =>
    have hw := hcw v (hbound v hm)
    simp only [TimeM.time_bind, TimeM.time_pure]
    omega

end MinThresholdSpec

/-! ### Sequential composition for query-bounded oracle programs -/

namespace ComputableInPolyTimeWithOracleQueries

/-- **Query-bounded sequential composition.** If `first` computes `f : α → β` with at most `r₁ |a|`
requests and `second` computes `g : α × β → γ` with at most `r₂ |encPair input middle (a, b)|`
requests, and the intermediate encoding length is bounded by `midLen |a|`, then `a ↦ g a (f a)`
is computable in polynomial time relative to `A` with at most `r₁ |a| + r₂ (midLen |a|)`
requests. -/
theorem bind_with {α β γ : Type} {A : Set (List Bool)} {r₁ r₂ midLen : ℕ → ℕ}
    {input : α ↪ List Bool} {middle : β ↪ List Bool} {output : γ ↪ List Bool}
    {f : α → β} {g : α → β → γ}
    (hf : ComputableInPolyTimeWithOracleQueries A r₁ f input middle)
    (hg : ComputableInPolyTimeWithOracleQueries A r₂ (fun p : α × β => g p.1 p.2)
      (encPair input middle) output)
    (hr₂ : Monotone r₂)
    (hmid : ∀ a, (encPair input middle (a, f a)).length ≤ midLen (input a).length) :
    ComputableInPolyTimeWithOracleQueries A (fun n => r₁ n + r₂ (midLen n))
      (fun a => g a (f a)) input output := by
  obtain ⟨p₁, hp₁_cert, hp₁⟩ := hf
  obtain ⟨p₂, hp₂_cert, hp₂⟩ := hg
  refine ⟨fun a => p₁ a >>= fun b => p₂ (a, b), ?_, fun a => ⟨?_, ?_⟩⟩
  · simpa only [OracleComp.interpret_bind] using hp₁_cert.bind_with hp₂_cert
  · rw [OracleComp.interpret_bind]
    change OracleComp.interpret (m := Id) (languageOracle A)
      (p₂ (a, OracleComp.interpret (m := Id) (languageOracle A) (p₁ a))) = g a (f a)
    rw [(hp₁ a).1, (hp₂ (a, f a)).1]
  · rw [OracleComp.queriesWith_bind, List.length_append, (hp₁ a).1]
    exact Nat.add_le_add (hp₁ a).2 ((hp₂ (a, f a)).2.trans (hr₂ (hmid a)))

/-- Preprocess the input of a query-bounded oracle computation when the preprocessing map stretches
encoded lengths by at most `stretch`. -/
theorem preprocess {α β γ : Type} {A : Set (List Bool)} {r stretch : ℕ → ℕ}
    {input : α ↪ List Bool} {middle : β ↪ List Bool} {output : γ ↪ List Bool}
    {f : β → γ} {g : α → β}
    (hf : ComputableInPolyTimeWithOracleQueries A r f middle output)
    (hg : ComputableInPolyTime g input middle)
    (hr : Monotone r)
    (hstretch : ∀ a, (middle (g a)).length ≤ stretch (input a).length) :
    ComputableInPolyTimeWithOracleQueries A (fun n => r (stretch n)) (fun a => f (g a))
      input output := by
  obtain ⟨prog, hcert, hprog⟩ := hf
  exact ⟨fun a => prog (g a), hcert.preprocess' hg, fun a =>
    ⟨(hprog (g a)).1, (hprog (g a)).2.trans (hr (hstretch a))⟩⟩

end ComputableInPolyTimeWithOracleQueries

/-! ### Native oracle bisection program -/

/-- One adaptive step of oracle bisection: if `iv.lo < iv.hi`, query `req a ((iv.lo + iv.hi) / 2)`
via `queryBit` and narrow `iv`; otherwise leave `iv` unchanged without querying. -/
def bisectStepProgram {α : Type} (req : α → ℕ → List Bool) (a : α) (iv : BisectInterval) :
    WordQueryComp Unit BisectInterval :=
  if iv.lo < iv.hi then
    let mid := (iv.lo + iv.hi) / 2
    (fun b => if b then ⟨mid + 1, iv.hi⟩ else ⟨iv.lo, mid⟩) <$> queryBit (req a mid)
  else pure iv

/-- Adaptive oracle bisection on `[lo a, hi a)`: iterate `bisectStepProgram` `(hi a - lo a).size`
times and return the final `lo`. -/
def bisectProgram {α : Type} (req : α → ℕ → List Bool) (lo hi : α → ℕ) (a : α) :
    WordQueryComp Unit ℕ :=
  BisectInterval.lo <$>
    OracleComp.iterate ((hi a - lo a).size) (bisectStepProgram req a) ⟨lo a, hi a⟩

open Classical in
/-- Against `languageOracle A`, one step of `bisectStepProgram` is `bisectStep`. -/
theorem interpret_bisectStepProgram {α : Type} (A : Set (List Bool)) (req : α → ℕ → List Bool)
    (a : α) (iv : BisectInterval) :
    OracleComp.interpret (m := Id) (languageOracle A) (bisectStepProgram req a iv) =
      bisectStep (fun m => decide (req a m ∈ A)) iv := by
  unfold bisectStepProgram bisectStep
  split_ifs
  · rw [OracleComp.interpret_map, interpret_queryBit]
    rfl
  · rfl

open Classical in
/-- Against `languageOracle A`, `bisectProgram` computes
`((bisectStep ...)^[(hi a - lo a).size] ⟨lo a, hi a⟩).lo`. -/
theorem interpret_bisectProgram {α : Type} (A : Set (List Bool)) (req : α → ℕ → List Bool)
    (lo hi : α → ℕ) (a : α) :
    OracleComp.interpret (m := Id) (languageOracle A) (bisectProgram req lo hi a) =
      ((bisectStep (fun m => decide (req a m ∈ A)))^[(hi a - lo a).size] ⟨lo a, hi a⟩).lo := by
  rw [bisectProgram, OracleComp.interpret_map, OracleComp.interpret_id_iterate]
  have hfun : (fun iv => OracleComp.interpret (m := Id) (languageOracle A)
      (bisectStepProgram req a iv)) = bisectStep (fun m => decide (req a m ∈ A)) :=
    funext (interpret_bisectStepProgram A req a)
  exact congrArg (fun f => (f^[(hi a - lo a).size] ⟨lo a, hi a⟩).lo) hfun

/-- `bisectProgram` makes at most `(hi a - lo a).size` requests (hence at most
`Nat.log 2 (hi a - lo a) + 1`). -/
theorem length_queriesWith_bisectProgram_le {α : Type}
    (answer : Unit × List Bool → List Bool) (req : α → ℕ → List Bool) (lo hi : α → ℕ) (a : α) :
    (OracleComp.queriesWith answer (bisectProgram req lo hi a)).length ≤ (hi a - lo a).size := by
  rw [bisectProgram, OracleComp.queriesWith_map]
  have hstep : ∀ iv, (OracleComp.queriesWith answer (bisectStepProgram req a iv)).length ≤ 1 := by
    intro iv
    unfold bisectStepProgram
    split_ifs <;> simp
  simpa using OracleComp.length_queriesWith_iterate_le answer hstep ((hi a - lo a).size)
    ⟨lo a, hi a⟩

/-- Every word queried by `bisectProgram` is `req a m` for a midpoint `lo a ≤ m < hi a`. -/
theorem mem_queriesWith_bisectProgram {α : Type}
    (answer : Unit × List Bool → List Bool) (req : α → ℕ → List Bool) (lo hi : α → ℕ) (a : α)
    {q : Unit × List Bool}
    (hq : q ∈ OracleComp.queriesWith answer (bisectProgram req lo hi a)) :
    ∃ m, lo a ≤ m ∧ m < hi a ∧ q = ((), req a m) := by
  rw [bisectProgram, OracleComp.queriesWith_map] at hq
  obtain ⟨iv, ⟨hlo, hhi⟩, hq_step⟩ := Cslib.OracleComp.mem_queriesWith_iterate answer
    (inv := fun iv : BisectInterval => lo a ≤ iv.lo ∧ (iv.lo < iv.hi → iv.hi ≤ hi a))
    ⟨le_refl _, fun _ => le_refl _⟩
    (fun iv ⟨hlo, hhi⟩ => by
      unfold bisectStepProgram
      split_ifs with hlt
      · rw [OracleComp.interpret_map]
        have hhi' := hhi hlt
        set b : Bool := OracleComp.interpret (m := Id) answer
          (queryBit (req a ((iv.lo + iv.hi) / 2)))
        change lo a ≤ (if b then BisectInterval.mk ((iv.lo + iv.hi) / 2 + 1) iv.hi
            else BisectInterval.mk iv.lo ((iv.lo + iv.hi) / 2)).lo ∧
          ((if b then BisectInterval.mk ((iv.lo + iv.hi) / 2 + 1) iv.hi
            else BisectInterval.mk iv.lo ((iv.lo + iv.hi) / 2)).lo <
           (if b then BisectInterval.mk ((iv.lo + iv.hi) / 2 + 1) iv.hi
            else BisectInterval.mk iv.lo ((iv.lo + iv.hi) / 2)).hi →
           (if b then BisectInterval.mk ((iv.lo + iv.hi) / 2 + 1) iv.hi
            else BisectInterval.mk iv.lo ((iv.lo + iv.hi) / 2)).hi ≤ hi a)
        cases b <;> simp only [↓reduceIte, Bool.false_eq_true] <;>
          refine ⟨by omega, fun _ => by omega⟩
      · exact ⟨hlo, hhi⟩)
    hq
  unfold bisectStepProgram at hq_step
  split_ifs at hq_step with hlt
  · rw [OracleComp.queriesWith_map] at hq_step
    simp only [queryBit, OracleComp.queriesWith_map, OracleComp.queriesWith_query,
      List.mem_singleton] at hq_step
    have hhi' := hhi hlt
    exact ⟨(iv.lo + iv.hi) / 2, by omega, by omega, hq_step⟩
  · simp at hq_step

open ComputableInPolyTime in
private theorem computableInPolyTime_midpoint :
    ComputableInPolyTime (fun iv : BisectInterval => (iv.lo + iv.hi) / 2)
      encBisectInterval encNat := by
  have hsum : ComputableInPolyTime (fun iv : BisectInterval => iv.lo + iv.hi)
      encBisectInterval encNat :=
    binary_add' (by fun_prop) (by fun_prop)
  exact (binary_shiftRight' hsum (const 1)).of_enc_eq fun iv => by
    rw [Nat.shiftRight_eq_div_pow, pow_one]

open ComputableInPolyTime in
private theorem isOraclePPTOn_bisectStepProgram {α : Type} {encA : α ↪ List Bool}
    {req : α → ℕ → List Bool}
    (hreq : ComputableInPolyTime (fun q : OracleThresholdQuery α => req q.inst q.target)
      (encOracleThresholdQuery encA) encBits) :
    IsOraclePPTOn (encPair encA encBisectInterval) encBisectInterval
      (fun pair => OracleComp.interpret ProbOracleComp.query
        (bisectStepProgram req pair.1 pair.2)) := by
  have hmid : ComputableInPolyTime
      (fun pair : α × BisectInterval => (pair.2.lo + pair.2.hi) / 2)
      (encPair encA encBisectInterval) encNat :=
    computableInPolyTime_midpoint.comp (snd encA encBisectInterval)
  have hq : ComputableInPolyTime
      (fun pair : α × BisectInterval =>
        OracleThresholdQuery.mk pair.1 ((pair.2.lo + pair.2.hi) / 2))
      (encPair encA encBisectInterval) (encOracleThresholdQuery encA) :=
    encOracleThresholdQuery_mk_polyTime (fst encA encBisectInterval) hmid
  have hword : ComputableInPolyTime
      (fun pair : α × BisectInterval => req pair.1 ((pair.2.lo + pair.2.hi) / 2))
      (encPair encA encBisectInterval) encBits :=
    hreq.comp hq
  have hcond : ComputableInPolyTime
      (fun pair : α × BisectInterval => decide (pair.2.lo < pair.2.hi))
      (encPair encA encBisectInterval) encBool :=
    binary_lt' (by fun_prop) (by fun_prop)
  have hbranch : ComputableInPolyTime
      (fun p : (α × BisectInterval) × Bool =>
        let mid := (p.1.2.lo + p.1.2.hi) / 2
        if p.2 then BisectInterval.mk (mid + 1) p.1.2.hi else BisectInterval.mk p.1.2.lo mid)
      (encPair (encPair encA encBisectInterval) encBool) encBisectInterval := by
    have hmid' : ComputableInPolyTime
        (fun p : (α × BisectInterval) × Bool => (p.1.2.lo + p.1.2.hi) / 2)
        (encPair (encPair encA encBisectInterval) encBool) encNat :=
      hmid.comp (fst _ _)
    have hmid1 : ComputableInPolyTime
        (fun p : (α × BisectInterval) × Bool => (p.1.2.lo + p.1.2.hi) / 2 + 1)
        (encPair (encPair encA encBisectInterval) encBool) encNat :=
      binary_add' hmid' (const 1)
    have hleft : ComputableInPolyTime
        (fun p : (α × BisectInterval) × Bool =>
          BisectInterval.mk ((p.1.2.lo + p.1.2.hi) / 2 + 1) p.1.2.hi)
        (encPair (encPair encA encBisectInterval) encBool) encBisectInterval :=
      encBisectInterval_mk_polyTime hmid1 (by fun_prop)
    have hright : ComputableInPolyTime
        (fun p : (α × BisectInterval) × Bool =>
          BisectInterval.mk p.1.2.lo ((p.1.2.lo + p.1.2.hi) / 2))
        (encPair (encPair encA encBisectInterval) encBool) encBisectInterval :=
      encBisectInterval_mk_polyTime (by fun_prop) hmid'
    exact (ComputableInPolyTime.ite' (snd _ _) hleft hright).of_enc_eq fun p => by
      cases p.2 <;> rfl
  have hyes := (isOraclePPTOn_queryBit hword).map_with'
    (f := fun (pair : α × BisectInterval) (b : Bool) =>
      let mid := (pair.2.lo + pair.2.hi) / 2
      if b then BisectInterval.mk (mid + 1) pair.2.hi else BisectInterval.mk pair.2.lo mid)
    hbranch
  have hno : IsOraclePPTOn (Operation := Unit) (encPair encA encBisectInterval) encBisectInterval
      (fun pair : α × BisectInterval => pure pair.2) :=
    (snd encA encBisectInterval).isOraclePPTOn
  refine (IsOraclePPTOn.ite' (condition := fun pair : α × BisectInterval => pair.2.lo < pair.2.hi)
    hcond hyes hno).congr fun pair State oracle s => ?_
  unfold bisectStepProgram
  split_ifs <;> simp only [OracleComp.interpret_map, OracleComp.interpret_pure]

/-- `bisectProgram` is strict oracle PPT whenever `lo`, `hi`, and the threshold request builder
`req` are polynomial-time. -/
theorem isOraclePPTOn_bisectProgram {α : Type} {encA : α ↪ List Bool}
    {req : α → ℕ → List Bool} {lo hi : α → ℕ}
    (hreq : ComputableInPolyTime (fun q : OracleThresholdQuery α => req q.inst q.target)
      (encOracleThresholdQuery encA) encBits)
    (hlo : ComputableInPolyTime lo encA encNat)
    (hhi : ComputableInPolyTime hi encA encNat) :
    IsOraclePPTOn encA encNat
      (fun a => OracleComp.interpret ProbOracleComp.query (bisectProgram req lo hi a)) := by
  open ComputableInPolyTime in
  have hcount : ComputableInPolyTime (fun a => (hi a - lo a).size) encA encUnary :=
    binary_size.comp (binary_sub' hhi hlo)
  have hinit : ComputableInPolyTime (fun a => BisectInterval.mk (lo a) (hi a))
      encA encBisectInterval :=
    encBisectInterval_mk_polyTime hlo hhi
  obtain ⟨tL, _, htL, _, hmL⟩ := hlo
  obtain ⟨cL, dL, hlenL⟩ := polynomiallyBounded_iff_le.mp htL
  obtain ⟨tH, _, htH, _, hmH⟩ := hhi
  obtain ⟨cH, dH, hlenH⟩ := polynomiallyBounded_iff_le.mp htH
  have hsize : PolyBounded (fun a => (encA a).length)
      (fun a => 4 * (cL * ((encA a).length + 1) ^ dL + cH * ((encA a).length + 1) ^ dH) + 4) := by
    growth_poly
  have hit := IsOraclePPTOn.iterateWith_spec' (input := encA)
    (stateEncoding := encBisectInterval)
    (count := fun a => (hi a - lo a).size)
    (initial := fun a => BisectInterval.mk (lo a) (hi a))
    (step := fun a iv => OracleComp.interpret ProbOracleComp.query (bisectStepProgram req a iv))
    hcount hinit (isOraclePPTOn_bisectStepProgram hreq)
    (fun a _ iv => iv.lo ≤ max (lo a) (hi a) ∧ iv.hi ≤ max (lo a) (hi a))
    (fun a => ⟨le_max_left _ _, le_max_right _ _⟩)
    (fun a _ iv _ ⟨h1, h2⟩ next hnext => by
      unfold bisectStepProgram at hnext
      split_ifs at hnext with hlt
      · rw [OracleComp.interpret_map] at hnext
        obtain ⟨b, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
        cases b <;> simp only [↓reduceIte, Bool.false_eq_true] <;> exact ⟨by omega, by omega⟩
      · simp only [OracleComp.interpret_pure] at hnext
        have heq_next : next = iv := by simpa [OracleComp.support] using hnext
        subst heq_next
        exact ⟨h1, h2⟩)
    hsize
    (fun a _ iv _ ⟨h1, h2⟩ => by
      have hcap : (encNat (max (lo a) (hi a))).length ≤
          cL * ((encA a).length + 1) ^ dL + cH * ((encA a).length + 1) ^ dH := by
        rcases max_choice (lo a) (hi a) with heq | heq <;> rw [heq]
        · exact ((hmL.length_le a).trans (hlenL _)).trans (Nat.le_add_right _ _)
        · exact ((hmH.length_le a).trans (hlenH _)).trans (Nat.le_add_left _ _)
      have h1' := (length_encNat_mono h1).trans hcap
      have h2' := (length_encNat_mono h2).trans hcap
      simp only [encBisectInterval_apply, encBisectIntervalFields]
      enc_len)
  have hproj : ComputableInPolyTime BisectInterval.lo encBisectInterval encNat := by fun_prop
  simpa only [bisectProgram, OracleComp.interpret_map, OracleComp.interpret_iterate] using
    hit.1.map' hproj

open Classical in
/-- **Polynomial-time oracle bisection with logarithmic query count.** Given polynomial-time
endpoints `lo, hi : α → ℕ` and threshold request builder `req`,
`((bisectStep ...)^[(hi a - lo a).size] ⟨lo a, hi a⟩).lo` is computable in polynomial time
relative to `A` with at most `r |encA a|` requests whenever
`(hi a - lo a).size ≤ r (encA a).length`. -/
theorem computableInPolyTimeWithOracleQueries_bisect {α : Type} {encA : α ↪ List Bool}
    (A : Set (List Bool)) {req : α → ℕ → List Bool} {lo hi : α → ℕ} {r : ℕ → ℕ}
    (hreq : ComputableInPolyTime (fun q : OracleThresholdQuery α => req q.inst q.target)
      (encOracleThresholdQuery encA) encBits)
    (hlo : ComputableInPolyTime lo encA encNat)
    (hhi : ComputableInPolyTime hi encA encNat)
    (hr : ∀ a, (hi a - lo a).size ≤ r (encA a).length) :
    ComputableInPolyTimeWithOracleQueries A r
      (fun a => ((bisectStep (fun m => decide (req a m ∈ A)))^[(hi a - lo a).size]
        ⟨lo a, hi a⟩).lo)
      encA encNat :=
  ⟨bisectProgram req lo hi, isOraclePPTOn_bisectProgram hreq hlo hhi, fun a =>
    ⟨interpret_bisectProgram A req lo hi a,
      (length_queriesWith_bisectProgram_le (languageOracle A) req lo hi a).trans (hr a)⟩⟩

/-! ### Max-SAT threshold optimization and optimal assignment recovery -/

/-- A CNF formula paired with a target number of satisfied clauses. -/
structure MaxSATQuery where
  /-- Formula in conjunctive normal form over natural-number variables. -/
  formula : CNF ℕ
  /-- Target number of satisfied clauses (counted with multiplicity). -/
  target : ℕ
  deriving DecidableEq, Repr

/-- Framed encoding of `MaxSATQuery` (`encCNF` paired with binary `encNat`). -/
enc_structure encMaxSATQuery : MaxSATQuery where
  formula : encCNF, target : encNat

/-- Optimal Max-SAT result: maximum satisfied-clause count paired with a raw assignment bitstring
for `SAT.assignment`. -/
structure MaxSATSolution where
  /-- Maximum number of clauses of `φ` simultaneously satisfiable. -/
  optValue : ℕ
  /-- Bitstring of length `φ.vars.length` read by `SAT.assignment φ`. -/
  assignmentBits : List Bool
  deriving DecidableEq, Repr

/-- Framed encoding of `MaxSATSolution` (binary `encNat` paired with `encBits`). -/
enc_structure encMaxSATSolution : MaxSATSolution where
  optValue : encNat, assignmentBits : encBits

/-- The threshold decision language for unweighted Max-SAT: `q ∈ MaxSATThreshold` iff some
assignment satisfies at least `q.target` clauses of `q.formula`. -/
def MaxSATThreshold : Set MaxSATQuery :=
  {q | ∃ σ : ℕ → Bool, q.target ≤ q.formula.countP (Clause.eval σ)}

theorem mem_MaxSATThreshold_iff {q : MaxSATQuery} :
    q ∈ MaxSATThreshold ↔ ∃ σ : ℕ → Bool, q.target ≤ q.formula.countP (Clause.eval σ) :=
  Iff.rfl

namespace MaxSAT

/-- Polynomial-time NP verifier for `MaxSATThreshold`. -/
def thresholdVerifier (p : MaxSATQuery × List Bool) : Bool :=
  decide (p.1.target ≤ p.1.formula.countP (Clause.eval (SAT.assignment p.1.formula p.2)))

theorem isVerifier_threshold :
    IsVerifier encMaxSATQuery Polynomial.X thresholdVerifier MaxSATThreshold := by
  refine IsVerifier.of_padding (fun q w _ h => ?_) fun q hq => ?_
  · simp only [thresholdVerifier, decide_eq_true_eq] at h
    exact ⟨_, h⟩
  · obtain ⟨σ, hσ⟩ := hq
    have hvars : q.formula.vars.length ≤ (encMaxSATQuery q).length := by
      have h1 := SAT.length_vars_le q.formula
      simp only [encMaxSATQuery_apply, encMaxSATQueryFields]
      exact h1.trans (length_le_encPair_left encCNF encNat (q.formula, q.target))
    refine ⟨q.formula.vars.map σ, by simpa using hvars, fun k => ?_⟩
    simp only [thresholdVerifier, decide_eq_true_eq]
    refine hσ.trans (CNF.countP_eval_congr fun v hv => ?_).le
    exact (SAT.assignment_vars_map_append _ σ _ hv).symm

@[fun_prop]
theorem computableInPolyTime_thresholdVerifier :
    ComputableInPolyTime thresholdVerifier (encPair encMaxSATQuery encBits) encBool := by
  open ComputableInPolyTime in
  have hφ : ComputableInPolyTime (fun p : MaxSATQuery × List Bool => p.1.formula)
      (encPair encMaxSATQuery encBits) (encList (encList (encPair encNat encBool))) :=
    encMaxSATQuery_formula_polyTime (fst _ _)
  have hcnt : ComputableInPolyTime
      (fun p : MaxSATQuery × List Bool =>
        p.1.formula.countP (Clause.eval (SAT.assignment p.1.formula p.2)))
      (encPair encMaxSATQuery encBits) encNat := by
    have hcl : ComputableInPolyTime
        (fun x : (MaxSATQuery × List Bool) × Clause ℕ =>
          Clause.eval (SAT.assignment x.1.1.formula x.1.2) x.2)
        (encPair (encPair encMaxSATQuery encBits) (encList (encPair encNat encBool))) encBool :=
      SAT.computableInPolyTime_clause.comp
        (((hφ.comp (fst _ _)).prod ((snd _ _).comp (fst _ _))).prod (snd _ _))
    exact unary_to_binary.comp (countPWithInput hφ hcl)
  exact binary_le' (encMaxSATQuery_target_polyTime (fst _ _)) hcnt

/-- `MaxSATThreshold` belongs to `NP`. -/
theorem mem_NP_threshold : MaxSATThreshold ∈ NP encMaxSATQuery :=
  ⟨Polynomial.X, thresholdVerifier, computableInPolyTime_thresholdVerifier, isVerifier_threshold⟩

/-- Specification of unweighted Max-SAT as a `MaxThresholdSpec`. -/
def thresholdSpec : MaxThresholdSpec (CNF ℕ) (ℕ → Bool) where
  valid _ _ := True
  score φ σ := φ.countP (Clause.eval σ)
  bound φ := φ.length
  score_le_bound _ _ _ := List.countP_le_length

open Classical in
/-- The exact maximum number of simultaneously satisfiable clauses of `φ`. -/
noncomputable def maxClauseScore (φ : CNF ℕ) : ℕ :=
  (lowerBoundM (fun q => pure (decide (MaxSATQuery.mk φ q ∈ MaxSATThreshold)))
    1 (φ.length + 1)).ret - 1

/-- `maxClauseScore φ` is attained by some assignment and upper-bounds every assignment's score. -/
theorem maxClauseScore_spec (φ : CNF ℕ) :
    maxClauseScore φ ≤ φ.length ∧
      (∃ σ : ℕ → Bool, φ.countP (Clause.eval σ) = maxClauseScore φ) ∧
      ∀ σ : ℕ → Bool, φ.countP (Clause.eval σ) ≤ maxClauseScore φ := by
  classical
  set t : ℕ → TimeM ℕ Bool := fun q => pure (decide (MaxSATQuery.mk φ q ∈ MaxSATThreshold))
  have hmono : ∀ m m', 1 ≤ m → m ≤ m' → m' < φ.length + 1 → (t m').ret = true → (t m).ret = true :=
    fun m m' _ hmm' _ ht => by
      simp only [t, TimeM.ret_pure, decide_eq_true_eq, mem_MaxSATThreshold_iff] at ht ⊢
      obtain ⟨σ, hσ⟩ := ht
      exact ⟨σ, hmm'.trans hσ⟩
  obtain ⟨hlo, hhi, htrue, hfalse⟩ := lowerBoundM_spec t (lo := 1) (hi := φ.length + 1) hmono
  set k := (lowerBoundM t 1 (φ.length + 1)).ret
  have hk_le : k ≤ φ.length + 1 := by omega
  have hupper : ∀ σ : ℕ → Bool, φ.countP (Clause.eval σ) ≤ k - 1 := by
    intro σ
    by_contra! hgt
    have hsc_le : φ.countP (Clause.eval σ) ≤ φ.length := List.countP_le_length
    have hf := hfalse k (le_refl k) (by omega)
    simp only [t, TimeM.ret_pure, decide_eq_false_iff_not, mem_MaxSATThreshold_iff] at hf
    exact hf ⟨σ, by omega⟩
  have hex : ∃ σ : ℕ → Bool, k - 1 ≤ φ.countP (Clause.eval σ) := by
    rcases Nat.eq_or_lt_of_le hlo with hk1 | hgt1
    · exact ⟨fun _ => false, by omega⟩
    · have ht := htrue (k - 1) (by omega) (by omega)
      simpa only [t, TimeM.ret_pure, decide_eq_true_eq, mem_MaxSATThreshold_iff] using ht
  obtain ⟨σ, hσ⟩ := hex
  refine ⟨by change k - 1 ≤ φ.length; omega,
    ⟨σ, le_antisymm (hupper σ) hσ⟩, hupper⟩

/-- Every declared-range assignment score is below `maxClauseScore φ`, for any declared variable
count `n`. -/
theorem optimum_le_maxClauseScore (n : ℕ) (φ : CNF ℕ) : optimum (n, φ) ≤ maxClauseScore φ := by
  obtain ⟨x, hx⟩ := exists_score_eq_optimum (n, φ)
  rw [← hx]
  exact (maxClauseScore_spec φ).2.2 (assignment n x)

/-- When every variable of `φ` is below `n`, the binary-search value `maxClauseScore φ` over
`ℕ → Bool` equals the declared-variable optimum `MaxSAT.optimum (n, φ)` over `BitString n` from
`FineGrained.MaxSAT.Histogram`. Without the hypothesis, undeclared variables read `false` in
`MaxSAT.score`, so the inequality `optimum_le_maxClauseScore` can be strict. -/
theorem maxClauseScore_eq_optimum {n : ℕ} {φ : CNF ℕ} (hφ : ∀ v ∈ φ.vars, v < n) :
    maxClauseScore φ = optimum (n, φ) := by
  refine le_antisymm ?_ (optimum_le_maxClauseScore n φ)
  obtain ⟨-, ⟨σ, hσ⟩, -⟩ := maxClauseScore_spec φ
  rw [← hσ]
  refine le_of_eq_of_le ?_ (score_le_optimum (n, φ) fun i => σ i)
  exact CNF.countP_eval_congr fun v hv => by simp [assignment, hφ v hv]

/-! ### Variable-by-variable witness recovery under partial assignments -/

/-- Number of clauses of `φ` already satisfied by at least one fixed literal in `answers`. -/
def satisfiedBy (answers : List (Literal ℕ)) (φ : CNF ℕ) : ℕ :=
  φ.countP fun c => c.any fun l => answers.any (· == l)

/-- Residual CNF after dropping clauses satisfied by `answers` and removing falsified literals. -/
def applyPartial (answers : List (Literal ℕ)) (φ : CNF ℕ) : CNF ℕ :=
  (φ.filter fun c => !c.any fun l => answers.any (· == l)).map fun c =>
    c.filter fun l => !answers.any (· == (l.1, !l.2))

/-- Lookup the Boolean assigned to `v` in `answers` (defaulting to `false`). -/
def lookupVar (answers : List (Literal ℕ)) (v : ℕ) : Bool :=
  match answers.find? (fun l => l.1 == v) with
  | some l => l.2
  | none => false

private theorem lookupVar_eq_of_mem {answers : List (Literal ℕ)}
    (hnodup : (answers.map Prod.fst).Nodup) {v : ℕ} {b : Bool} (hmem : (v, b) ∈ answers) :
    lookupVar answers v = b := by
  induction answers with
  | nil => simp at hmem
  | cons hd tl ih =>
    rw [List.map_cons, List.nodup_cons] at hnodup
    unfold lookupVar at ih ⊢
    rcases List.mem_cons.mp hmem with rfl | htl
    · simp
    · have hv_tl : v ∈ tl.map Prod.fst := List.mem_map_of_mem (f := Prod.fst) htl
      have hne : (hd.1 == v) = false := by
        rw [beq_eq_false_iff_ne]
        intro heq
        exact hnodup.1 (heq ▸ hv_tl)
      rw [List.find?_cons_of_neg (by simp [hne])]
      exact ih hnodup.2 htl

private theorem countP_eval_eq_satisfiedBy_add_applyPartial {answers : List (Literal ℕ)}
    {σ : ℕ → Bool} (hagree : ∀ l ∈ answers, σ l.1 = l.2) (φ : CNF ℕ) :
    φ.countP (Clause.eval σ) =
      satisfiedBy answers φ + (applyPartial answers φ).countP (Clause.eval σ) := by
  induction φ with
  | nil => rfl
  | cons c cs ih =>
    simp only [satisfiedBy, applyPartial] at ih ⊢
    by_cases hsat : (c.any fun l => answers.any (· == l)) = true
    · obtain ⟨l, hlc, hla⟩ := List.any_eq_true.mp hsat
      obtain ⟨l', hl'a, heq⟩ := List.any_eq_true.mp hla
      have hll' : l' = l := by simpa [beq_iff_eq] using heq
      subst hll'
      have heval_c' : Clause.eval σ c = true :=
        (Clause.eval_eq_true_iff σ c).mpr
          ⟨l', hlc, by
            have hag := hagree l' hl'a
            rcases l' with ⟨v', false | true⟩ <;> simp_all⟩
      have hfilt : (List.filter (fun c : Clause ℕ => !c.any fun l => answers.any (· == l))
          (c :: cs)) =
          List.filter (fun c : Clause ℕ => !c.any fun l => answers.any (· == l)) cs :=
        List.filter_cons_of_neg (p := fun c : Clause ℕ => !c.any fun l => answers.any (· == l))
          (by simp [hsat])
      rw [hfilt]
      simp only [List.countP_cons, heval_c', hsat, ↓reduceIte]
      omega
    · have hsatF : (c.any fun l => answers.any (· == l)) = false := Bool.eq_false_iff.mpr hsat
      have heval_eq :
          Clause.eval σ (c.filter fun l => !answers.any (· == (l.1, !l.2))) = Clause.eval σ c := by
        apply Bool.eq_iff_iff.mpr
        simp only [Clause.eval_eq_true_iff, List.mem_filter, Bool.not_eq_true', List.any_eq_false]
        constructor
        · rintro ⟨l, ⟨hlc, -⟩, hl⟩
          exact ⟨l, hlc, hl⟩
        · rintro ⟨l, hlc, hl⟩
          refine ⟨l, ⟨hlc, fun l' hl'a hcontra => ?_⟩, hl⟩
          have heq' : l' = (l.1, !l.2) := beq_iff_eq.mp hcontra
          subst heq'
          have hσ := hagree (l.1, !l.2) hl'a
          cases l.2 <;> simp [hσ] at hl
      have hfilt : (List.filter (fun c : Clause ℕ => !c.any fun l => answers.any (· == l))
          (c :: cs)) =
          c :: List.filter (fun c : Clause ℕ => !c.any fun l => answers.any (· == l)) cs :=
        List.filter_cons_of_pos (p := fun c : Clause ℕ => !c.any fun l => answers.any (· == l))
          (by simp [hsatF])
      rw [hfilt, List.map_cons]
      simp only [List.countP_cons, hsatF, Bool.false_eq_true, ↓reduceIte, heval_eq]
      omega

private theorem not_mem_vars_applyPartial {answers : List (Literal ℕ)} {φ : CNF ℕ} {v : ℕ}
    (hv : v ∈ answers.map Prod.fst) : v ∉ (applyPartial answers φ).vars := by
  obtain ⟨⟨v', b⟩, hmem, rfl⟩ := List.mem_map.mp hv
  dsimp only at hmem ⊢
  intro hcontra
  obtain ⟨c', hc', b', hb'⟩ := CNF.mem_vars.mp hcontra
  simp only [applyPartial, List.mem_map, List.mem_filter] at hc'
  obtain ⟨c, ⟨_, hnot_sat⟩, rfl⟩ := hc'
  simp only [List.mem_filter] at hb'
  obtain ⟨hlc, hnot_neg⟩ := hb'
  cases hbb : (b == b')
  · have hb_eq : b = !b' := by cases b <;> cases b' <;> simp_all
    subst hb_eq
    have : (answers.any (· == (v', !b'))) = true :=
      List.any_eq_true.mpr ⟨(v', !b'), hmem, by simp⟩
    simp [this] at hnot_neg
  · have hb_eq : b = b' := by simpa using hbb
    subst hb_eq
    have : (c.any fun l => answers.any (· == l)) = true :=
      List.any_eq_true.mpr ⟨(v', b), hlc, List.any_eq_true.mpr ⟨(v', b), hmem, by simp⟩⟩
    simp [this] at hnot_sat

/-- Querying `MaxSATThreshold` on `(applyPartial answers φ, target - satisfiedBy answers φ)`
characterizes whether `answers` extends to a full assignment satisfying at least `target`
clauses of `φ`. -/
theorem mem_MaxSATThreshold_applyPartial_iff {answers : List (Literal ℕ)}
    (hnodup : (answers.map Prod.fst).Nodup) (φ : CNF ℕ) (target : ℕ) :
    MaxSATQuery.mk (applyPartial answers φ) (target - satisfiedBy answers φ) ∈ MaxSATThreshold ↔
      ∃ σ : ℕ → Bool, (∀ l ∈ answers, σ l.1 = l.2) ∧ target ≤ φ.countP (Clause.eval σ) := by
  rw [mem_MaxSATThreshold_iff]
  dsimp only
  constructor
  · rintro ⟨τ, hτ⟩
    let σ : ℕ → Bool := fun u => if u ∈ answers.map Prod.fst then lookupVar answers u else τ u
    have hagree : ∀ l ∈ answers, σ l.1 = l.2 := by
      intro ⟨u, b⟩ hmem
      have hu : u ∈ answers.map Prod.fst := List.mem_map_of_mem (f := Prod.fst) hmem
      simp only [σ, hu, ↓reduceIte, lookupVar_eq_of_mem hnodup hmem]
    have hcongr : (applyPartial answers φ).countP (Clause.eval σ) =
        (applyPartial answers φ).countP (Clause.eval τ) :=
      CNF.countP_eval_congr fun u hu => by
        have hnot : u ∉ answers.map Prod.fst := fun hm => not_mem_vars_applyPartial hm hu
        exact ite_eq_right_iff.mpr fun hm => absurd hm hnot
    refine ⟨σ, hagree, ?_⟩
    rw [countP_eval_eq_satisfiedBy_add_applyPartial hagree φ, hcongr]
    omega
  · rintro ⟨σ, hagree, hσ⟩
    refine ⟨σ, ?_⟩
    rw [countP_eval_eq_satisfiedBy_add_applyPartial hagree φ] at hσ
    omega

/-- Encoded length of `applyPartial answers φ` never exceeds that of `φ`. -/
theorem length_encCNF_applyPartial_le (answers : List (Literal ℕ)) (φ : CNF ℕ) :
    (encCNF (applyPartial answers φ)).length ≤ (encCNF φ).length := by
  have hcl : ∀ (p : Literal ℕ → Bool) (c : Clause ℕ),
      (encList (encPair encNat encBool) (c.filter p)).length ≤
        (encList (encPair encNat encBool) c).length := by
    intro p c
    induction c with
    | nil => simp
    | cons l ls ih =>
      by_cases hp : p l
      · simp only [List.filter_cons_of_pos hp, encList_cons, List.length_append]
        exact Nat.add_le_add_left ih _
      · simp only [List.filter_cons_of_neg hp]
        exact ih.trans (by simp [encList_cons])
  induction φ with
  | nil => simp [applyPartial, encCNF]
  | cons c cs ih =>
    simp only [applyPartial] at ih ⊢
    by_cases hsat : (!c.any fun l => answers.any (· == l)) = true
    · rw [List.filter_cons_of_pos
        (p := fun c : Clause ℕ => !c.any fun l => answers.any (· == l)) hsat, List.map_cons]
      simp only [encCNF, encList_cons, List.length_append] at ih ⊢
      set pLit : Literal ℕ → Bool := fun l => !answers.any (· == (l.1, !l.2))
      have hsub : (encList (encPair encNat encBool) (c.filter pLit)).length ≤
          (encList (encPair encNat encBool) c).length := hcl pLit c
      have hfr : (frame (encList (encPair encNat encBool) (c.filter pLit))).length ≤
          (frame (encList (encPair encNat encBool) c)).length := by
        enc_len
      exact Nat.add_le_add hfr ih
    · rw [List.filter_cons_of_neg
        (p := fun c : Clause ℕ => !c.any fun l => answers.any (· == l)) hsat]
      refine ih.trans ?_
      simp only [encCNF, encList_cons, List.length_append]
      exact Nat.le_add_left _ _

/-- Query tested at one step of `MaxSAT` witness recovery. -/
def recoverQuery (q : MaxSATQuery) (answers : List (Literal ℕ)) : MaxSATQuery :=
  let v := q.formula.distinctVars.getD answers.length 0
  let cand := answers ++ [(v, true)]
  ⟨applyPartial cand q.formula, q.target - satisfiedBy cand q.formula⟩

theorem length_encMaxSATQuery_recoverQuery_le (q : MaxSATQuery) (answers : List (Literal ℕ)) :
    (encMaxSATQuery (recoverQuery q answers)).length ≤ (encMaxSATQuery q).length := by
  simp only [recoverQuery, encMaxSATQuery_apply, encMaxSATQueryFields]
  have h1 := length_encCNF_applyPartial_le
    (answers ++ [(q.formula.distinctVars.getD answers.length 0, true)]) q.formula
  have h2 := length_encNat_mono (Nat.sub_le q.target
    (satisfiedBy (answers ++ [(q.formula.distinctVars.getD answers.length 0, true)]) q.formula))
  enc_len

/-- Pure step of `MaxSAT` witness recovery over `q.formula.distinctVars`. -/
def recoverStep (D : MaxSATQuery → Bool) (q : MaxSATQuery) (answers : List (Literal ℕ)) :
    List (Literal ℕ) :=
  if answers.length < q.formula.distinctVars.length then
    let v := q.formula.distinctVars.getD answers.length 0
    answers ++ [(v, D (recoverQuery q answers))]
  else answers

/-- Adaptive oracle step of `MaxSAT` witness recovery. -/
def recoverStepProgram (q : MaxSATQuery) (answers : List (Literal ℕ)) :
    WordQueryComp Unit (List (Literal ℕ)) :=
  if answers.length < q.formula.distinctVars.length then
    let v := q.formula.distinctVars.getD answers.length 0
    (fun b => answers ++ [(v, b)]) <$> queryBit (encMaxSATQuery (recoverQuery q answers))
  else pure answers

/-- Adaptive oracle program recovering an assignment for `q : MaxSATQuery` in `q.formula.numVars`
queries. -/
def recoverProgram (q : MaxSATQuery) : WordQueryComp Unit (List Bool) :=
  (fun answers => q.formula.vars.map (lookupVar answers)) <$>
    OracleComp.iterate q.formula.numVars (recoverStepProgram q) []

open Classical in
/-- Pure witness-recovery function matching `recoverProgram` against `MaxSATThreshold`. -/
noncomputable def recoverBits (D : MaxSATQuery → Bool) (q : MaxSATQuery) : List Bool :=
  q.formula.vars.map
    (lookupVar ((recoverStep D q)^[q.formula.numVars] []))

open Classical in
theorem interpret_recoverProgram (A : Set (List Bool)) (q : MaxSATQuery) :
    OracleComp.interpret (m := Id) (languageOracle A) (recoverProgram q) =
      recoverBits (fun r => decide (encMaxSATQuery r ∈ A)) q := by
  rw [recoverProgram, OracleComp.interpret_map, OracleComp.interpret_id_iterate, recoverBits]
  have hfun : (fun answers => OracleComp.interpret (m := Id) (languageOracle A)
      (recoverStepProgram q answers)) =
      recoverStep (fun r => decide (encMaxSATQuery r ∈ A)) q := by
    funext answers
    unfold recoverStepProgram recoverStep
    split_ifs
    · rw [OracleComp.interpret_map, interpret_queryBit]
      rfl
    · rfl
  exact congrArg (fun f => q.formula.vars.map (lookupVar (f^[q.formula.numVars] []))) hfun

theorem length_queriesWith_recoverProgram_le
    (answer : Unit × List Bool → List Bool) (q : MaxSATQuery) :
    (OracleComp.queriesWith answer (recoverProgram q)).length ≤ CNF.numVars q.formula := by
  rw [recoverProgram, OracleComp.queriesWith_map]
  have hstep : ∀ ans, (OracleComp.queriesWith answer (recoverStepProgram q ans)).length ≤ 1 := by
    intro ans
    unfold recoverStepProgram
    split_ifs <;> simp
  simpa using OracleComp.length_queriesWith_iterate_le answer hstep (CNF.numVars q.formula) []

theorem mem_queriesWith_recoverProgram_length_le
    (answer : Unit × List Bool → List Bool) (q : MaxSATQuery) {req : Unit × List Bool}
    (hreq : req ∈ OracleComp.queriesWith answer (recoverProgram q)) :
    req.2.length ≤ (encMaxSATQuery q).length := by
  rw [recoverProgram, OracleComp.queriesWith_map] at hreq
  obtain ⟨ans, -, hstep⟩ := Cslib.OracleComp.mem_queriesWith_iterate answer
    (inv := fun _ => True) trivial (fun _ _ => trivial) hreq
  unfold recoverStepProgram at hstep
  split_ifs at hstep
  · simp only [queryBit, OracleComp.queriesWith_map, OracleComp.queriesWith_query,
      List.mem_singleton] at hstep
    subst hstep
    exact length_encMaxSATQuery_recoverQuery_le q ans
  · simp at hstep

/-- If `q ∈ MaxSATThreshold` and `D` decides `MaxSATThreshold` on queries no longer than `q`,
`recoverBits D q` yields an assignment satisfying at least `q.target` clauses of `q.formula`. -/
theorem target_le_countP_recoverBits {D : MaxSATQuery → Bool} {q : MaxSATQuery}
    (hD : ∀ r, (encMaxSATQuery r).length ≤ (encMaxSATQuery q).length →
      (D r = true ↔ r ∈ MaxSATThreshold))
    (hq : q ∈ MaxSATThreshold) :
    q.target ≤ q.formula.countP (Clause.eval (SAT.assignment q.formula (recoverBits D q))) := by
  have hnodup_dv : q.formula.distinctVars.Nodup := CNF.nodup_distinctVars q.formula
  have hloop : ∀ i, i ≤ q.formula.distinctVars.length →
      let ans := (recoverStep D q)^[i] []
      ans.map Prod.fst = q.formula.distinctVars.take i ∧
        ∃ σ : ℕ → Bool, (∀ l ∈ ans, σ l.1 = l.2) ∧
          q.target ≤ q.formula.countP (Clause.eval σ) := by
    intro i hi
    induction i with
    | zero =>
      obtain ⟨σ, hσ⟩ := hq
      exact ⟨rfl, σ, fun _ h => by simp at h, hσ⟩
    | succ i ih =>
      obtain ⟨hfst, σ, hagree, hσ⟩ := ih (by omega)
      set ans := (recoverStep D q)^[i] []
      have hlen : ans.length = i := by
        have := congrArg List.length hfst
        rw [List.length_map, List.length_take] at this
        omega
      have hlt_i : i < q.formula.distinctVars.length := by omega
      have hlt : ans.length < q.formula.distinctVars.length := by omega
      rw [Function.iterate_succ_apply', recoverStep, ite_eq_left hlt]
      set v := q.formula.distinctVars.getD ans.length 0
      have hv_eq : v = q.formula.distinctVars[i] := by
        dsimp only [v]
        rw [hlen, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt_i, Option.getD_some]
      have hfst_step : ∀ b : Bool,
          (ans ++ [(v, b)]).map Prod.fst = q.formula.distinctVars.take (i + 1) := by
        intro b
        rw [List.map_append, hfst, List.map_singleton, hv_eq, List.take_add_one,
          List.getElem?_eq_getElem hlt_i, Option.toList_some]
      have hnodup_cand : ((ans ++ [(v, true)]).map Prod.fst).Nodup := by
        rw [hfst_step true]
        exact hnodup_dv.take
      have hqlen := length_encMaxSATQuery_recoverQuery_le q ans
      refine ⟨hfst_step _, ?_⟩
      cases hb : D (recoverQuery q ans)
      · have hnot : recoverQuery q ans ∉ MaxSATThreshold :=
          fun hm => Bool.noConfusion (hb.symm.trans ((hD _ hqlen).mpr hm))
        rw [recoverQuery, mem_MaxSATThreshold_applyPartial_iff hnodup_cand] at hnot
        have hσv : σ v = false := by
          cases hsv : σ v
          · rfl
          · exfalso
            refine hnot ⟨σ, fun l hl => ?_, hσ⟩
            rcases List.mem_append.mp hl with hl1 | hl2
            · exact hagree l hl1
            · rw [List.mem_singleton] at hl2
              subst hl2
              exact hsv
        refine ⟨σ, fun l hl => ?_, hσ⟩
        rcases List.mem_append.mp hl with hl1 | hl2
        · exact hagree l hl1
        · rw [List.mem_singleton] at hl2
          subst hl2
          exact hσv
      · have hm : recoverQuery q ans ∈ MaxSATThreshold := (hD _ hqlen).mp hb
        rw [recoverQuery, mem_MaxSATThreshold_applyPartial_iff hnodup_cand] at hm
        exact hm
  have hnv : q.formula.numVars = q.formula.distinctVars.length :=
    (CNF.length_distinctVars q.formula).symm
  obtain ⟨hfst, σ, hagree, hσ⟩ := hloop q.formula.numVars (by omega)
  rw [hnv, List.take_length] at hfst
  rw [← hnv] at hfst
  set ans := (recoverStep D q)^[q.formula.numVars] []
  have hnodup_ans : (ans.map Prod.fst).Nodup := by
    rw [hfst]
    exact hnodup_dv
  have hcongr : q.formula.countP (Clause.eval (SAT.assignment q.formula (recoverBits D q))) =
      q.formula.countP (Clause.eval σ) := by
    refine CNF.countP_eval_congr fun v hv => ?_
    have hbits : SAT.assignment q.formula (recoverBits D q) v = lookupVar ans v :=
      SAT.assignment_vars_map _ _ hv
    rw [hbits]
    have hdv : v ∈ ans.map Prod.fst := by
      rw [hfst, CNF.mem_distinctVars]
      exact hv
    obtain ⟨⟨v', b⟩, hmem, rfl⟩ := List.mem_map.mp hdv
    dsimp only at hmem ⊢
    rw [lookupVar_eq_of_mem hnodup_ans hmem, hagree (v', b) hmem]
  rw [hcongr]
  exact hσ

open ComputableInPolyTime in
private theorem computableInPolyTime_nextRecoverVar :
    ComputableInPolyTime
      (fun p : MaxSATQuery × List (Literal ℕ) => p.1.formula.distinctVars.getD p.2.length 0)
      (encPair encMaxSATQuery (encList (encPair encNat encBool))) encNat :=
  listGetDWithInput
    (SAT.computableInPolyTime_distinctVars.comp (encMaxSATQuery_formula_polyTime (fst _ _)))
    ((length_list _).comp (snd _ _)) 0

open ComputableInPolyTime in
private theorem computableInPolyTime_recoverQuery :
    ComputableInPolyTime (fun p : MaxSATQuery × List (Literal ℕ) => recoverQuery p.1 p.2)
      (encPair encMaxSATQuery (encList (encPair encNat encBool))) encMaxSATQuery := by
  have hφ : ComputableInPolyTime (fun p : MaxSATQuery × List (Literal ℕ) => p.1.formula)
      (encPair encMaxSATQuery (encList (encPair encNat encBool)))
      (encList (encList (encPair encNat encBool))) :=
    encMaxSATQuery_formula_polyTime (fst _ _)
  have hcand : ComputableInPolyTime
      (fun p : MaxSATQuery × List (Literal ℕ) =>
        p.2 ++ [(p.1.formula.distinctVars.getD p.2.length 0, true)])
      (encPair encMaxSATQuery (encList (encPair encNat encBool)))
      (encList (encPair encNat encBool)) :=
    listAppend' (snd _ _) (cons' (computableInPolyTime_nextRecoverVar.prod (const true)) (const []))
  have hlitEq : ComputableInPolyTime
      (fun x : Literal ℕ × Literal ℕ => x.1 == x.2)
      (encPair (encPair encNat encBool) (encPair encNat encBool)) encBool := by
    have h1 := decide_eq' (encB := encNat)
      ((fst (encPair encNat encBool) (encPair encNat encBool)).fst')
      ((snd (encPair encNat encBool) (encPair encNat encBool)).fst')
    have h2 := decide_eq' (encB := encBool)
      ((fst (encPair encNat encBool) (encPair encNat encBool)).snd')
      ((snd (encPair encNat encBool) (encPair encNat encBool)).snd')
    exact (bool_and' h1 h2).of_enc_eq fun ⟨⟨n1, b1⟩, ⟨n2, b2⟩⟩ =>
      congrArg encBool (Bool.eq_iff_iff.mpr (by simp))
  have hclauseSat : ComputableInPolyTime
      (fun x : List (Literal ℕ) × Clause ℕ => x.2.any fun l => x.1.any (· == l))
      (encPair (encList (encPair encNat encBool)) (encList (encPair encNat encBool))) encBool :=
    anyWithInput (snd _ _) (anyWithInput ((fst _ _).comp (fst _ _))
      (hlitEq.comp ((snd _ _).prod ((snd _ _).comp (fst _ _)))))
  have hsatBy : ComputableInPolyTime
      (fun p : MaxSATQuery × List (Literal ℕ) =>
        satisfiedBy (p.2 ++ [(p.1.formula.distinctVars.getD p.2.length 0, true)]) p.1.formula)
      (encPair encMaxSATQuery (encList (encPair encNat encBool))) encNat :=
    unary_to_binary.comp (countPWith hclauseSat hcand hφ)
  have hap : ComputableInPolyTime
      (fun p : MaxSATQuery × List (Literal ℕ) =>
        applyPartial (p.2 ++ [(p.1.formula.distinctVars.getD p.2.length 0, true)]) p.1.formula)
      (encPair encMaxSATQuery (encList (encPair encNat encBool))) encCNF := by
    have hkeepClause : ComputableInPolyTime
        (fun x : (MaxSATQuery × List (Literal ℕ)) × Clause ℕ =>
          !x.2.any fun l =>
            (x.1.2 ++ [(x.1.1.formula.distinctVars.getD x.1.2.length 0, true)]).any (· == l))
        (encPair (encPair encMaxSATQuery (encList (encPair encNat encBool)))
          (encList (encPair encNat encBool))) encBool :=
      bool_not.comp (hclauseSat.comp ((hcand.comp (fst _ _)).prod (snd _ _)))
    have hf1 := filterWithInput
      (test := fun (p : MaxSATQuery × List (Literal ℕ)) (c : Clause ℕ) =>
        !c.any fun l =>
          (p.2 ++ [(p.1.formula.distinctVars.getD p.2.length 0, true)]).any (· == l))
      hφ hkeepClause
    have hkeepLit : ComputableInPolyTime
        (fun y : ((MaxSATQuery × List (Literal ℕ)) × Clause ℕ) × Literal ℕ =>
          !(y.1.1.2 ++ [(y.1.1.1.formula.distinctVars.getD y.1.1.2.length 0, true)]).any
            (· == (y.2.1, !y.2.2)))
        (encPair (encPair (encPair encMaxSATQuery (encList (encPair encNat encBool)))
          (encList (encPair encNat encBool))) (encPair encNat encBool)) encBool := by
      have hnegLit : ComputableInPolyTime
          (fun y : ((MaxSATQuery × List (Literal ℕ)) × Clause ℕ) × Literal ℕ => (y.2.1, !y.2.2))
          (encPair (encPair (encPair encMaxSATQuery (encList (encPair encNat encBool)))
            (encList (encPair encNat encBool))) (encPair encNat encBool))
          (encPair encNat encBool) :=
        ((snd _ _).fst').prod (bool_not.comp ((snd _ _).snd'))
      have hany := anyWithInput
        (test := fun (y : ((MaxSATQuery × List (Literal ℕ)) × Clause ℕ) × Literal ℕ)
          (m : Literal ℕ) => m == (y.2.1, !y.2.2))
        ((hcand.comp (fst _ _)).comp (fst _ _))
        (hlitEq.comp ((snd _ _).prod (hnegLit.comp (fst _ _))))
      exact bool_not.comp hany
    have hfLit : ComputableInPolyTime
        (fun x : (MaxSATQuery × List (Literal ℕ)) × Clause ℕ =>
          x.2.filter fun l =>
            !(x.1.2 ++ [(x.1.1.formula.distinctVars.getD x.1.2.length 0, true)]).any
              (· == (l.1, !l.2)))
        (encPair (encPair encMaxSATQuery (encList (encPair encNat encBool)))
          (encList (encPair encNat encBool)))
        (encList (encPair encNat encBool)) :=
      filterWithInput
        (test := fun (x : (MaxSATQuery × List (Literal ℕ)) × Clause ℕ) (l : Literal ℕ) =>
          !(x.1.2 ++ [(x.1.1.formula.distinctVars.getD x.1.2.length 0, true)]).any
            (· == (l.1, !l.2)))
        (snd _ _) hkeepLit
    exact .of_tidy (ComputableTidilyInPolyTime.mapWithInput hf1.tidy hfLit.tidy)
  exact encMaxSATQuery_mk_polyTime hap
    (binary_sub' (encMaxSATQuery_target_polyTime (fst _ _)) hsatBy)

open ComputableInPolyTime in
private theorem isOraclePPTOn_recoverStepProgram :
    IsOraclePPTOn (encPair encMaxSATQuery (encList (encPair encNat encBool)))
      (encList (encPair encNat encBool))
      (fun pair => OracleComp.interpret ProbOracleComp.query
        (recoverStepProgram pair.1 pair.2)) := by
  have hcond : ComputableInPolyTime
      (fun pair : MaxSATQuery × List (Literal ℕ) =>
        decide (pair.2.length < pair.1.formula.distinctVars.length))
      (encPair encMaxSATQuery (encList (encPair encNat encBool))) encBool :=
    unary_lt.comp (((length_list _).comp (snd _ _)).prod
      ((length_list _).comp
        (SAT.computableInPolyTime_distinctVars.comp (encMaxSATQuery_formula_polyTime (fst _ _)))))
  have hreq : ComputableInPolyTime
      (fun pair : MaxSATQuery × List (Literal ℕ) =>
        encMaxSATQuery (recoverQuery pair.1 pair.2))
      (encPair encMaxSATQuery (encList (encPair encNat encBool))) encBits :=
    computableInPolyTime_recoverQuery.encoding_comp
  have hpost : ComputableInPolyTime
      (fun p : (MaxSATQuery × List (Literal ℕ)) × Bool =>
        p.1.2 ++ [(p.1.1.formula.distinctVars.getD p.1.2.length 0, p.2)])
      (encPair (encPair encMaxSATQuery (encList (encPair encNat encBool))) encBool)
      (encList (encPair encNat encBool)) :=
    listAppend' ((snd _ _).comp (fst _ _))
      (cons' ((computableInPolyTime_nextRecoverVar.comp (fst _ _)).prod (snd _ _)) (const []))
  have hyes := (isOraclePPTOn_queryBit hreq).map_with'
    (f := fun (pair : MaxSATQuery × List (Literal ℕ)) (b : Bool) =>
      pair.2 ++ [(pair.1.formula.distinctVars.getD pair.2.length 0, b)]) hpost
  have hno : IsOraclePPTOn (Operation := Unit)
      (encPair encMaxSATQuery (encList (encPair encNat encBool)))
      (encList (encPair encNat encBool))
      (fun pair : MaxSATQuery × List (Literal ℕ) => pure pair.2) :=
    (snd _ _).isOraclePPTOn
  refine (IsOraclePPTOn.ite'
    (condition := fun pair : MaxSATQuery × List (Literal ℕ) =>
      pair.2.length < pair.1.formula.distinctVars.length)
    hcond hyes hno).congr fun pair State oracle s => ?_
  unfold recoverStepProgram
  split_ifs <;> simp only [OracleComp.interpret_map, OracleComp.interpret_pure]

open ComputableInPolyTime in
/-- `recoverProgram` is strict oracle PPT on `encMaxSATQuery`. -/
theorem isOraclePPTOn_recoverProgram :
    IsOraclePPTOn encMaxSATQuery encBits
      (fun q => OracleComp.interpret ProbOracleComp.query (recoverProgram q)) := by
  have hcount : ComputableInPolyTime (fun q : MaxSATQuery => CNF.numVars q.formula)
      encMaxSATQuery encUnary :=
    SAT.computableInPolyTime_numVars.comp (encMaxSATQuery_formula_polyTime id')
  have hsize : PolyBounded (fun q : MaxSATQuery => (encMaxSATQuery q).length)
      (fun q => (encMaxSATQuery q).length * (4 * (encMaxSATQuery q).length + 5)) := by
    growth_poly
  have hit := IsOraclePPTOn.iterateWith_spec' (input := encMaxSATQuery)
    (stateEncoding := encList (encPair encNat encBool))
    (count := fun q => CNF.numVars q.formula)
    (initial := fun _ => [])
    (step := fun q ans => OracleComp.interpret ProbOracleComp.query (recoverStepProgram q ans))
    hcount (const []) isOraclePPTOn_recoverStepProgram
    (fun q i ans => ans.map Prod.fst = q.formula.distinctVars.take i)
    (fun _ => rfl)
    (fun q i ans hi hinv next hnext => by
      have hnv := (CNF.length_distinctVars q.formula).symm
      have hlen : ans.length = i := by
        have := congrArg List.length hinv
        rw [List.length_map, List.length_take] at this
        omega
      have hlt_i : i < q.formula.distinctVars.length := by omega
      unfold recoverStepProgram at hnext
      rw [ite_eq_left (by omega), OracleComp.interpret_map] at hnext
      obtain ⟨b, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
      rw [List.map_append, hinv, List.map_singleton, List.take_add_one,
        List.getElem?_eq_getElem hlt_i, Option.toList_some, hlen,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt_i, Option.getD_some])
    hsize
    (fun q i ans hi hinv => by
      have hnv := (CNF.length_distinctVars q.formula).symm
      have hmem : ∀ l ∈ ans, l.1 ∈ q.formula.vars := fun l hl => by
        have hdv : l.1 ∈ q.formula.distinctVars :=
          List.mem_of_mem_take (hinv ▸ List.mem_map_of_mem hl)
        exact CNF.mem_distinctVars.mp hdv
      have hlen : ans.length ≤ CNF.numVars q.formula := by
        have := congrArg List.length hinv
        rw [List.length_map, List.length_take] at this
        omega
      have hnv_le : CNF.numVars q.formula ≤ (encMaxSATQuery q).length := by
        have h1 : CNF.numVars q.formula ≤ q.formula.vars.length :=
          CNF.numVars_le_length_vars q.formula
        have h2 := SAT.length_vars_le q.formula
        simp only [encMaxSATQuery_apply, encMaxSATQueryFields]
        exact (h1.trans h2).trans (length_le_encPair_left encCNF encNat (q.formula, q.target))
      have hcnf_le : (encCNF q.formula).length ≤ (encMaxSATQuery q).length := by
        simp only [encMaxSATQuery_apply, encMaxSATQueryFields]
        exact length_le_encPair_left encCNF encNat (q.formula, q.target)
      calc (encList (encPair encNat encBool) ans).length
          ≤ ans.length * (4 * (encCNF q.formula).length + 5) :=
            SAT.length_encList_le_of_mem_vars hmem
        _ ≤ (encMaxSATQuery q).length * (4 * (encMaxSATQuery q).length + 5) :=
            Nat.mul_le_mul (hlen.trans hnv_le) (by omega))
  have hlookup : ComputableInPolyTime
      (fun x : (MaxSATQuery × List (Literal ℕ)) × ℕ => lookupVar x.1.2 x.2)
      (encPair (encPair encMaxSATQuery (encList (encPair encNat encBool))) encNat) encBool := by
    have heq_var : ComputableInPolyTime
        (fun p : ((MaxSATQuery × List (Literal ℕ)) × ℕ) × Literal ℕ => p.2.1 == p.1.2)
        (encPair (encPair (encPair encMaxSATQuery (encList (encPair encNat encBool))) encNat)
          (encPair encNat encBool)) encBool := by
      have h1 := decide_eq' (encB := encNat)
        ((fst encNat encBool).comp (snd _ _))
        ((snd (encPair encMaxSATQuery (encList (encPair encNat encBool))) encNat).comp (fst _ _))
      exact h1.of_enc_eq fun ⟨⟨_, v⟩, ⟨u, _⟩⟩ => by
        dsimp only [Function.comp]
        exact congrArg encBool (Bool.eq_iff_iff.mpr (by simp))
    have hfnd := findWithInput
      (test := fun (x : (MaxSATQuery × List (Literal ℕ)) × ℕ) (l : Literal ℕ) => l.1 == x.2)
      (list := fun x : (MaxSATQuery × List (Literal ℕ)) × ℕ => x.1.2)
      ((snd _ _).comp (fst _ _)) heq_var
    have hget : ComputableInPolyTime
        (fun o : Option (Literal ℕ) => match o with | some l => l.2 | none => false)
        (encOption (encPair encNat encBool)) encBool := by
      have hcond : ComputableInPolyTime Option.isSome (encOption (encPair encNat encBool))
          encBool := by fun_prop
      have hval : ComputableInPolyTime
          (fun o : Option (Literal ℕ) => (o.getD (0, false)).2)
          (encOption (encPair encNat encBool)) encBool := by fun_prop
      exact (ComputableInPolyTime.ite' hcond hval (const false)).of_enc_eq fun o => by
        cases o <;> rfl
    exact hget.comp hfnd
  have hpost : ComputableInPolyTime
      (fun pair : MaxSATQuery × List (Literal ℕ) =>
        pair.1.formula.vars.map (lookupVar pair.2))
      (encPair encMaxSATQuery (encList (encPair encNat encBool))) encBits := by
    have hvars := SAT.computableInPolyTime_vars.comp
      (encMaxSATQuery_formula_polyTime (fst encMaxSATQuery (encList (encPair encNat encBool))))
    have hmap : ComputableInPolyTime
        (fun pair : MaxSATQuery × List (Literal ℕ) =>
          pair.1.formula.vars.map (lookupVar pair.2))
        (encPair encMaxSATQuery (encList (encPair encNat encBool))) (encList encBool) :=
      .of_tidy (ComputableTidilyInPolyTime.mapWithInput hvars.tidy hlookup.tidy)
    exact listToBits.comp hmap
  simpa only [recoverProgram, OracleComp.interpret_map, OracleComp.interpret_iterate] using
    hit.1.map_with' (f := fun (q : MaxSATQuery) (ans : List (Literal ℕ)) =>
      q.formula.vars.map (lookupVar ans)) hpost

/-- Combined adaptive oracle program solving Max-SAT optimization and optimal witness recovery:
bisect on `[1, φ.length + 1)`, subtract `1` for `optValue`, and run
`recoverProgram ⟨φ, optValue⟩`. -/
def solveMaxSATProgram (φ : CNF ℕ) : WordQueryComp Unit MaxSATSolution := do
  let k ← bisectProgram (fun ψ m => encMaxSATQuery ⟨ψ, m⟩) (fun _ => 1) (fun ψ => ψ.length + 1) φ
  let opt := k - 1
  let bits ← recoverProgram ⟨φ, opt⟩
  return ⟨opt, bits⟩

open Classical in
/-- Pure function computed by `solveMaxSATProgram` against an oracle language `A`. -/
noncomputable def solveMaxSAT (A : Set (List Bool)) (φ : CNF ℕ) : MaxSATSolution :=
  OracleComp.interpret (m := Id) (languageOracle A) (solveMaxSATProgram φ)

/-- `solveMaxSATProgram φ` makes at most `φ.length.size + φ.numVars` queries (hence at most
`(Nat.log 2 φ.length + 1) + φ.numVars`), and every queried word has encoded length at most
`(encMaxSATQuery ⟨φ, φ.length⟩).length`. -/
theorem solveMaxSATProgram_query_bounds (answer : Unit × List Bool → List Bool) (φ : CNF ℕ) :
    (OracleComp.queriesWith answer (solveMaxSATProgram φ)).length ≤
      φ.length.size + CNF.numVars φ ∧
    ∀ req ∈ OracleComp.queriesWith answer (solveMaxSATProgram φ),
      req.2.length ≤ (encMaxSATQuery ⟨φ, φ.length⟩).length := by
  unfold solveMaxSATProgram
  rw [OracleComp.queriesWith_bind]
  set k : ℕ := OracleComp.interpret (m := Id) answer
    (bisectProgram (fun ψ m => encMaxSATQuery ⟨ψ, m⟩) (fun _ => 1) (fun ψ => ψ.length + 1) φ)
  have hk_le : k - 1 ≤ φ.length := by
    have hiter : ∀ s (iv : BisectInterval),
        iv.lo ≤ φ.length + 1 → iv.hi ≤ φ.length + 1 →
        (OracleComp.interpret (m := Id) answer
          (OracleComp.iterate s
            (bisectStepProgram (fun ψ m => encMaxSATQuery ⟨ψ, m⟩) φ) iv) : BisectInterval).lo ≤
          φ.length + 1 := by
      intro s
      induction s with
      | zero => intro iv h1 _; exact h1
      | succ s' ih =>
        intro iv h1 h2
        rw [OracleComp.iterate_succ_bind, OracleComp.interpret_bind]
        have hstep :
            let iv' : BisectInterval := OracleComp.interpret (m := Id) answer
              (bisectStepProgram (fun ψ m => encMaxSATQuery ⟨ψ, m⟩) φ iv)
            iv'.lo ≤ φ.length + 1 ∧ iv'.hi ≤ φ.length + 1 := by
          unfold bisectStepProgram
          split_ifs
          · rw [OracleComp.interpret_map]
            set b : Bool := OracleComp.interpret (m := Id) answer _
            change (if b then BisectInterval.mk ((iv.lo + iv.hi) / 2 + 1) iv.hi
                else BisectInterval.mk iv.lo ((iv.lo + iv.hi) / 2)).lo ≤ φ.length + 1 ∧
              (if b then BisectInterval.mk ((iv.lo + iv.hi) / 2 + 1) iv.hi
                else BisectInterval.mk iv.lo ((iv.lo + iv.hi) / 2)).hi ≤ φ.length + 1
            cases b <;> simp only [↓reduceIte, Bool.false_eq_true] <;> exact ⟨by omega, by omega⟩
          · exact ⟨h1, h2⟩
        exact ih _ hstep.1 hstep.2
    have hk_eq : k = (OracleComp.interpret (m := Id) answer
        (OracleComp.iterate ((φ.length + 1 - 1).size)
          (bisectStepProgram (fun ψ m => encMaxSATQuery ⟨ψ, m⟩) φ) ⟨1, φ.length + 1⟩) :
        BisectInterval).lo := by
      simp only [k, bisectProgram, OracleComp.interpret_map]
      rfl
    have hk_bound : k ≤ φ.length + 1 := by
      rw [hk_eq]
      exact hiter ((φ.length + 1 - 1).size) ⟨1, φ.length + 1⟩
        (Nat.le_add_left 1 φ.length) (le_refl _)
    omega
  constructor
  · rw [List.length_append]
    have h1 := length_queriesWith_bisectProgram_le answer
      (fun ψ m => encMaxSATQuery ⟨ψ, m⟩) (fun _ => 1) (fun ψ => ψ.length + 1) φ
    have h2 : (OracleComp.queriesWith answer
        (recoverProgram ⟨φ, k - 1⟩ >>= fun bits => pure (MaxSATSolution.mk (k - 1) bits))).length ≤
        CNF.numVars φ := by
      rw [OracleComp.queriesWith_bind, OracleComp.queriesWith_pure, List.append_nil]
      exact length_queriesWith_recoverProgram_le answer ⟨φ, k - 1⟩
    simp only [Nat.add_sub_cancel] at h1
    exact Nat.add_le_add h1 h2
  · intro req hreq
    rw [List.mem_append] at hreq
    rcases hreq with h1 | h2
    · obtain ⟨m, _, hm_lt, rfl⟩ := mem_queriesWith_bisectProgram answer
        (fun ψ m => encMaxSATQuery ⟨ψ, m⟩) (fun _ => 1) (fun ψ => ψ.length + 1) φ h1
      simp only [encMaxSATQuery_apply, encMaxSATQueryFields]
      have hm_le : (encNat m).length ≤ (encNat φ.length).length := length_encNat_mono (by omega)
      enc_len
    · rw [OracleComp.queriesWith_bind, OracleComp.queriesWith_pure, List.append_nil] at h2
      have hlen_rec := mem_queriesWith_recoverProgram_length_le answer ⟨φ, k - 1⟩ h2
      refine hlen_rec.trans ?_
      simp only [encMaxSATQuery_apply, encMaxSATQueryFields]
      have hk_enc := length_encNat_mono hk_le
      enc_len

/-- **Correctness of `solveMaxSAT` against `encMaxSATQuery '' MaxSATThreshold`.** Recovers both
`optValue = maxClauseScore φ` and an assignment achieving `maxClauseScore φ`. -/
theorem solveMaxSAT_spec (φ : CNF ℕ) :
    let sol := solveMaxSAT (encMaxSATQuery '' MaxSATThreshold) φ
    sol.optValue = maxClauseScore φ ∧
      φ.countP (Clause.eval (SAT.assignment φ sol.assignmentBits)) = maxClauseScore φ ∧
      ∀ σ : ℕ → Bool, φ.countP (Clause.eval σ) ≤ sol.optValue := by
  classical
  set A := encMaxSATQuery '' MaxSATThreshold
  have hmem_iff : ∀ r : MaxSATQuery,
      decide (encMaxSATQuery r ∈ A) = true ↔ r ∈ MaxSATThreshold := by
    intro r
    rw [decide_eq_true_iff, encMaxSATQuery.injective.mem_set_image]
  have hmono : ∀ m m', 1 ≤ m → m ≤ m' → m' < φ.length + 1 →
      (pure (decide (MaxSATQuery.mk φ m' ∈ MaxSATThreshold)) : TimeM ℕ Bool).ret = true →
      (pure (decide (MaxSATQuery.mk φ m ∈ MaxSATThreshold)) : TimeM ℕ Bool).ret = true := by
    intro m m' _ hmm' _ ht
    simp only [TimeM.ret_pure, decide_eq_true_eq, mem_MaxSATThreshold_iff] at ht ⊢
    obtain ⟨σ, hσ⟩ := ht
    exact ⟨σ, hmm'.trans hσ⟩
  set k_val : ℕ := OracleComp.interpret (m := Id) (languageOracle A)
    (bisectProgram (fun ψ m => encMaxSATQuery ⟨ψ, m⟩) (fun _ => 1) (fun ψ => ψ.length + 1) φ)
  have hbisect : k_val - 1 = maxClauseScore φ := by
    have hk_eq : k_val =
        ((bisectStep (fun m => decide (encMaxSATQuery ⟨φ, m⟩ ∈ A)))^[(φ.length + 1 - 1).size]
          ⟨1, φ.length + 1⟩).lo :=
      interpret_bisectProgram A (fun ψ m => encMaxSATQuery ⟨ψ, m⟩) (fun _ => 1)
        (fun ψ => ψ.length + 1) φ
    rw [hk_eq, maxClauseScore]
    have hfn : (fun m => decide (encMaxSATQuery ⟨φ, m⟩ ∈ A)) =
        (fun m => (pure (decide (MaxSATQuery.mk φ m ∈ MaxSATThreshold)) : TimeM ℕ Bool).ret) := by
      funext m
      apply Bool.eq_iff_iff.mpr
      simp only [TimeM.ret_pure, decide_eq_true_eq]
      exact (decide_eq_true_iff.symm.trans (hmem_iff (MaxSATQuery.mk φ m)))
    rw [hfn, iterate_bisectStep_eq_lowerBoundM _ hmono]
  have hsol : solveMaxSAT A φ =
      MaxSATSolution.mk (maxClauseScore φ)
        (recoverBits (fun r => decide (encMaxSATQuery r ∈ A)) ⟨φ, maxClauseScore φ⟩) := by
    have hraw : solveMaxSAT A φ =
        MaxSATSolution.mk (k_val - 1)
          (recoverBits (fun r => decide (encMaxSATQuery r ∈ A)) ⟨φ, k_val - 1⟩) := by
      simp only [solveMaxSAT, solveMaxSATProgram, OracleComp.interpret_bind,
        interpret_recoverProgram, OracleComp.interpret_pure]
      rfl
    rw [hraw, hbisect]
  dsimp only
  rw [hsol]
  obtain ⟨_, ⟨σ₀, hσ₀⟩, hupper⟩ := maxClauseScore_spec φ
  have hq_mem : MaxSATQuery.mk φ (maxClauseScore φ) ∈ MaxSATThreshold :=
    ⟨σ₀, hσ₀.symm.le⟩
  have hge := target_le_countP_recoverBits (fun r _ => hmem_iff r) hq_mem
  dsimp only at hge
  exact ⟨rfl, le_antisymm (hupper _) hge, hupper⟩

/-- **Polynomial-time oracle certificate for `solveMaxSAT`** relative to any oracle `A`, making
at most `2 * |encCNF φ| + 1` requests (and per-instance `φ.length.size + φ.numVars`). -/
theorem computableInPolyTimeWithOracleQueries_solveMaxSAT (A : Set (List Bool)) :
    ComputableInPolyTimeWithOracleQueries A (fun n => 2 * n + 1) (solveMaxSAT A)
      encCNF encMaxSATSolution := by
  open ComputableInPolyTime in
  have hreq : ComputableInPolyTime
      (fun q : OracleThresholdQuery (CNF ℕ) => encMaxSATQuery ⟨q.inst, q.target⟩)
      (encOracleThresholdQuery encCNF) encBits :=
    (encMaxSATQuery_mk_polyTime (encOracleThresholdQuery_inst_polyTime id')
      (encOracleThresholdQuery_target_polyTime id')).encoding_comp
  have hhi : ComputableInPolyTime (fun φ : CNF ℕ => φ.length + 1) encCNF encNat :=
    binary_add' (unary_to_binary.comp (SAT.computableInPolyTime_length id')) (const 1)
  have hb_cert := isOraclePPTOn_bisectProgram
    (req := fun ψ m => encMaxSATQuery ⟨ψ, m⟩) hreq (const 1) hhi
  have hrec_pair : IsOraclePPTOn (encPair encCNF encNat) encMaxSATSolution
      (fun p : CNF ℕ × ℕ => do
        let bits ← OracleComp.interpret ProbOracleComp.query (recoverProgram ⟨p.1, p.2 - 1⟩)
        pure (MaxSATSolution.mk (p.2 - 1) bits)) := by
    have hprep : ComputableInPolyTime (fun p : CNF ℕ × ℕ => MaxSATQuery.mk p.1 (p.2 - 1))
        (encPair encCNF encNat) encMaxSATQuery :=
      encMaxSATQuery_mk_polyTime (fst _ _) (binary_sub' (snd _ _) (const 1))
    have hpost : ComputableInPolyTime
        (fun x : (CNF ℕ × ℕ) × List Bool => MaxSATSolution.mk (x.1.2 - 1) x.2)
        (encPair (encPair encCNF encNat) encBits) encMaxSATSolution :=
      encMaxSATSolution_mk_polyTime (binary_sub' ((snd _ _).comp (fst _ _)) (const 1)) (snd _ _)
    simpa only [← bind_pure_comp] using
      (isOraclePPTOn_recoverProgram.preprocess' hprep).map_with'
        (f := fun (p : CNF ℕ × ℕ) (bits : List Bool) => MaxSATSolution.mk (p.2 - 1) bits) hpost
  refine ⟨solveMaxSATProgram, ?_, fun φ => ⟨rfl, ?_⟩⟩
  · refine (hb_cert.bind_with
      (second := fun (ψ : CNF ℕ) (k : ℕ) => do
        let bits ← OracleComp.interpret ProbOracleComp.query (recoverProgram ⟨ψ, k - 1⟩)
        pure (MaxSATSolution.mk (k - 1) bits)) hrec_pair).congr fun φ State oracle s => ?_
    simp only [solveMaxSATProgram, OracleComp.interpret_bind, OracleComp.interpret_pure]
  · have hlen_le : ∀ ψ : CNF ℕ, ψ.length ≤ (encCNF ψ).length := by
      intro ψ
      induction ψ with
      | nil => simp
      | cons c cs ih =>
        simp only [List.length_cons, encCNF, encList_cons, List.length_append] at ih ⊢
        have hfr : 1 ≤ (frame (encList (encPair encNat encBool) c)).length := by enc_len
        exact (Nat.add_comm cs.length 1).trans_le (Nat.add_le_add hfr ih)
    have hqb := (solveMaxSATProgram_query_bounds (languageOracle A) φ).1
    have hsize_le : φ.length.size ≤ (encCNF φ).length :=
      (Nat.size_le_size (hlen_le φ)).trans (Nat.size_le.mpr Nat.lt_two_pow_self)
    have hnv_le : CNF.numVars φ ≤ (encCNF φ).length :=
      (CNF.numVars_le_length_vars φ).trans (SAT.length_vars_le φ)
    dsimp only
    omega

/-- If `encMaxSATQuery '' MaxSATThreshold ∈ P encBits`, then `solveMaxSAT` computes both the exact
maximum satisfied-clause count and an optimal assignment in polynomial time. -/
theorem computableInPolyTime_solveMaxSAT_of_mem_P
    (hP : encMaxSATQuery '' MaxSATThreshold ∈ P encBits) :
    ComputableInPolyTime (solveMaxSAT (encMaxSATQuery '' MaxSATThreshold))
      encCNF encMaxSATSolution :=
  (computableInPolyTimeWithOracleQueries_solveMaxSAT
    (encMaxSATQuery '' MaxSATThreshold)).computableInPolyTimeWithOracle.computableInPolyTime hP

end MaxSAT

end Complexity

end Cslib
