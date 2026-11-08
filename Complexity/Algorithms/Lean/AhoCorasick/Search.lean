/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.Lean.AhoCorasick.Basic
public import Cslib.Algorithms.Lean.TimeM

/-!
# Aho–Corasick Multi-Pattern String Matching

This module implements the pattern matching machine of `[AhoCorasick1975]` in
`Cslib.Algorithms.Lean.TimeM`: the scan of a text by a machine with given failure and output
tables (Algorithm 1, `scanM`), the breadth-first construction of the failure and output tables
(Algorithm 3, `buildM`), and their composition (`searchM`, `search`). It proves that the scan with
valid tables reports exactly the keyword occurrences `occurrences P t` of
`Complexity.Algorithms.Lean.AhoCorasick.Basic`, that the construction produces valid tables, and
the transition bounds of `[AhoCorasick1975]`, Theorems 2 and 4.

## Source conventions

* **States:** as in `[AhoCorasick1975]`, Section 4, a state is represented by its string
  (`IsNode P`). The goto function is the prefix test `IsNode P (u ++ [a])`, and the start state
  loops on every symbol that does not begin a keyword. The explicit trie of Algorithm 2 (integer
  states and goto table) is not constructed.
* **Output:** reported pairs `(i, y)` give the `1`-indexed end position `i` of the keyword `y`, as
  printed by Algorithm 1. A keyword listed several times in `P` is reported once per end position,
  and the empty keyword is never reported.
* **Tables:** a `Machine α` bundles a failure table and an output table, both functions on
  strings. `Machine.IsValid P M` says they agree with `failure P` and `output P` on every state.

## Cost model

* **Charged (`1` `TimeM` tick):** every goto transition (including the start state's self-loop),
  every failure transition, and every reported pair `(i, y)`.
* **Uncharged:** the goto test `IsNode P (u ++ [a])`, reads and writes of the failure and output
  tables, and list construction (constant-time operations in the integer-state machine of
  `[AhoCorasick1975]`).
* **Uncharged and not linear:** the per-round bookkeeping of `buildM`, which scans all of `P` at
  each of the depths `1, …, maxLength P - 1` for the keywords longer than that depth. This is
  `|P| * (maxLength P - 1)` keyword visits, which can be quadratic in the total keyword length
  (one keyword of length `40` and `40` one-letter keywords give `1599` visits against total
  length `80`). So `time_buildM_le` bounds the goto and failure transitions counted in the proof
  of `[AhoCorasick1975]`, Theorem 4, not the total construction time. Moreover, Algorithm 3
  visits each state once, while `buildM` recomputes the failure state of a prefix shared by
  several keywords once per keyword (with the same result), so its transition bound is per
  keyword.
* **Guarded failure loop:** `stepM` stops at the start state if a failure transition does not
  shorten the state. This never happens with a valid table; it makes the scan terminate, and its
  cost bounds hold, for an arbitrary failure table. The guard's length comparison and the abort
  are uncharged.

Using the potential "length of the current state", one operating cycle satisfies
`(stepM P f u a).time + (stepM P f u a).ret.length ≤ u.length + 2` (`time_stepM_le`), for any
failure table `f`.

## Main definitions

* `Cslib.Algorithms.Lean.AhoCorasick.Machine`: failure and output tables.
* `Cslib.Algorithms.Lean.AhoCorasick.Machine.IsValid`: the tables agree with `failure` and
  `output` on every state.
* `Cslib.Algorithms.Lean.AhoCorasick.stepM`: one operating cycle of Algorithm 1.
* `Cslib.Algorithms.Lean.AhoCorasick.scanM`: Algorithm 1.
* `Cslib.Algorithms.Lean.AhoCorasick.buildM`, `build`: Algorithm 3.
* `Cslib.Algorithms.Lean.AhoCorasick.searchM`, `search`: build the machine, then scan.

## Main results

* `Cslib.Algorithms.Lean.AhoCorasick.ret_scanM`: with valid tables, the scan reports exactly
  `occurrences P t` (`[AhoCorasick1975]`, Theorem 1 for Algorithm 1).
* `Cslib.Algorithms.Lean.AhoCorasick.time_scanM_silent_lt`: on a nonempty text of length `n`,
  the guarded Algorithm 1 makes fewer than `2n` goto and failure transitions, for any failure
  table (`[AhoCorasick1975]`, Theorem 2); `time_scanM_lt` adds one tick per reported pair, and
  `time_scanM_eq` splits the cost into transitions and reported pairs.
* `Cslib.Algorithms.Lean.AhoCorasick.isValid_build`: Algorithm 3 computes valid tables
  (`[AhoCorasick1975]`, Theorem 1 for Algorithm 3).
* `Cslib.Algorithms.Lean.AhoCorasick.time_buildM_le`: Algorithm 3 makes at most
  `2 * (p.length - 1)` goto and failure transitions per keyword `p` (the transitions counted in
  `[AhoCorasick1975]`, Theorem 4; the level bookkeeping is not charged).
* `Cslib.Algorithms.Lean.AhoCorasick.search_eq`, `mem_search_iff` and `time_searchM_le`.

## References

* [A. V. Aho and M. J. Corasick, *Efficient String Matching: An Aid to Bibliographic
  Search*][AhoCorasick1975]
-/

public section

namespace Cslib.Algorithms.Lean.AhoCorasick

variable {α : Type*} [DecidableEq α]

/-! ## Machines and validity -/

/-- Failure and output tables of a pattern matching machine whose states are represented by their
strings. -/
structure Machine (α : Type*) where
  /-- The failure function. -/
  fail : List α → List α
  /-- The output function. -/
  out : List α → List (List α)

/-- `M` has the correct failure and output values at `u`. -/
@[expose] def Machine.AgreesAt (P : List (List α)) (M : Machine α) (u : List α) : Prop :=
  M.fail u = failure P u ∧ M.out u = output P u

/-- `M` has the failure function and output function of `P` (`[AhoCorasick1975]`, Lemmas 1 and 2)
on every goto-graph state. This is stronger than the paper's (behavioural) validity, which only
asks that Algorithm 1 report the right occurrences: it fixes the tables on every state. -/
@[expose] def Machine.IsValid (P : List (List α)) (M : Machine α) : Prop :=
  ∀ u, IsNode P u → M.AgreesAt P u

open Cslib.Algorithms.Lean TimeM

/-! ## One operating cycle -/

/-- One operating cycle of Algorithm 1 of `[AhoCorasick1975]` with failure table `f`, charging one
tick per goto or failure transition. A failure transition that does not shorten the state (which
cannot happen for a valid table) stops at the start state. -/
def stepM (P : List (List α)) (f : List α → List α) (u : List α) (a : α) :
    TimeM ℕ (List α) :=
  if IsNode P (u ++ [a]) then do
    ✓ return u ++ [a]
  else if u = [] then do
    ✓ return []
  else if _hlt : (f u).length < u.length then do
    ✓ stepM P f (f u) a
  else
    return []
termination_by u.length

theorem ret_stepM {P : List (List α)} {f : List α → List α} {u : List α} (a : α)
    (hf : ∀ v, IsNode P v → v.length ≤ u.length → f v = failure P v) (hu : IsNode P u) :
    (stepM P f u a).ret = nextMove P u a := by
  induction h : u.length using Nat.strongRecOn generalizing u with
  | ind n ih =>
    rw [stepM]
    split_ifs with hnode hnil hlt
    · rw [nextMove_of_isNode hnode]
      rfl
    · rw [nextMove_of_not_isNode_of_eq_nil hnode hnil]
      rfl
    · rw [nextMove_of_not_isNode hnode hnil]
      have hfu : f u = failure P u := hf u hu (Nat.le_refl _)
      simp only [TimeM.ret_bind]
      rw [hfu] at hlt ⊢
      exact ih _ (h ▸ hlt) (fun v hv hvl => hf v hv (by omega)) (isNode_failure P u) rfl
    · exact absurd (hf u hu (Nat.le_refl _) ▸ length_failure_lt P hnil) hlt

/-- Amortized cost of one operating cycle with potential the depth of the state. -/
theorem time_stepM_le (P : List (List α)) (f : List α → List α) (u : List α) (a : α) :
    (stepM P f u a).time + (stepM P f u a).ret.length ≤ u.length + 2 ∧
      (stepM P f u a).time ≤ u.length + 1 := by
  induction h : u.length using Nat.strongRecOn generalizing u with
  | ind n ih =>
    rw [stepM]
    split_ifs with hnode hnil hlt
    · simp only [TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, TimeM.ret_bind,
        TimeM.ret_pure, List.length_append, List.length_singleton]
      omega
    · simp only [TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, TimeM.ret_bind,
        TimeM.ret_pure, List.length_nil]
      omega
    · simp only [TimeM.time_bind, TimeM.time_tick, TimeM.ret_bind]
      have := ih _ (h ▸ hlt) _ rfl
      omega
    · simp only [TimeM.time_pure, TimeM.ret_pure, List.length_nil]
      omega

/-! ## Algorithm 1: the scan -/

/-- The operating cycles of Algorithm 1 of `[AhoCorasick1975]` on the remaining text `t`, from
state `u` after `i` symbols. Each reported occurrence costs one tick. -/
def scanLoopM (P : List (List α)) (M : Machine α) :
    List α → ℕ → List α → TimeM ℕ (List (ℕ × List α))
  | [], _, _ => return []
  | a :: t, i, u => do
    let v ← stepM P M.fail u a
    let found := (M.out v).map fun y => (i + 1, y)
    let rest ← scanLoopM P M t (i + 1) v
    ✓[found.length] return found ++ rest

/-- Algorithm 1 of `[AhoCorasick1975]`: run the pattern matching machine `M` on `t`, reporting
each keyword occurrence as its end position and the keyword. -/
def scanM (P : List (List α)) (M : Machine α) (t : List α) : TimeM ℕ (List (ℕ × List α)) :=
  scanLoopM P M t 0 []

theorem ret_scanLoopM {P : List (List α)} {M : Machine α} (hM : M.IsValid P) (w t : List α) :
    occurrences P w ++ (scanLoopM P M t w.length (longestNodeSuffix P w)).ret =
      occurrences P (w ++ t) := by
  induction t generalizing w with
  | nil => simp only [scanLoopM, TimeM.ret_pure, List.append_nil]
  | cons a t ih =>
    have hstep :
        (stepM P M.fail (longestNodeSuffix P w) a).ret = longestNodeSuffix P (w ++ [a]) := by
      rw [ret_stepM a (fun v hv _ => (hM v hv).1) (isNode_longestNodeSuffix P w),
        longestNodeSuffix_append_singleton_eq_nextMove]
    simp only [scanLoopM, TimeM.ret_bind, TimeM.ret_pure, hstep]
    have hout : M.out (longestNodeSuffix P (w ++ [a])) = output P (w ++ [a]) := by
      rw [(hM _ (isNode_longestNodeSuffix P _)).2, output_longestNodeSuffix]
    have := ih (w ++ [a])
    rw [List.length_append, List.length_singleton] at this
    rw [hout, ← List.append_assoc, ← occurrences_append_singleton, this, List.append_assoc,
      List.singleton_append]

/-- Correctness of Algorithm 1 (`[AhoCorasick1975]`, Theorem 1): with valid failure and output
tables, the scan reports exactly the keyword occurrences. -/
theorem ret_scanM {P : List (List α)} {M : Machine α} (hM : M.IsValid P) (t : List α) :
    (scanM P M t).ret = occurrences P t := by
  have := ret_scanLoopM hM [] t
  rwa [occurrences_nil, List.nil_append, List.nil_append, List.length_nil, longestNodeSuffix_nil]
    at this

theorem time_scanLoopM_le (P : List (List α)) (M : Machine α) (t : List α) (i : ℕ) (u : List α)
    (ht : t ≠ []) :
    (scanLoopM P M t i u).time + 1 ≤
      u.length + 2 * t.length + (scanLoopM P M t i u).ret.length := by
  induction t generalizing i u with
  | nil => exact absurd rfl ht
  | cons a t ih =>
    have hs := time_stepM_le P M.fail u a
    simp only [scanLoopM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, TimeM.ret_bind,
      TimeM.ret_pure, List.length_append, List.length_cons, List.length_map]
    rcases t with _ | ⟨b, t⟩
    · simp only [scanLoopM, TimeM.time_pure, TimeM.ret_pure, List.length_nil]
      omega
    · have := ih (i + 1) (stepM P M.fail u a).ret (List.cons_ne_nil b t)
      simp only [List.length_cons] at this ⊢
      omega

/-- `[AhoCorasick1975]`, Theorem 2, with output charged: on a nonempty text of length `n` the scan
makes fewer than `2n` goto and failure transitions plus one tick per reported occurrence. -/
theorem time_scanM_lt (P : List (List α)) (M : Machine α) {t : List α} (ht : t ≠ []) :
    (scanM P M t).time < 2 * t.length + (scanM P M t).ret.length := by
  have := time_scanLoopM_le P M t 0 [] ht
  rw [List.length_nil] at this
  unfold scanM
  omega

theorem time_scanM_le (P : List (List α)) (M : Machine α) (t : List α) :
    (scanM P M t).time ≤ 2 * t.length + (scanM P M t).ret.length := by
  rcases t with _ | ⟨a, t⟩
  · simp only [scanM, scanLoopM, TimeM.time_pure, Nat.zero_le]
  · exact Nat.le_of_lt (time_scanM_lt P M (List.cons_ne_nil a t))

/-- With emission suppressed, the scan's cost is its number of goto and failure transitions; the
scan's cost is that number plus the number of reported occurrences. -/
theorem time_scanLoopM_eq (P : List (List α)) (M : Machine α) (t : List α) (i : ℕ) (u : List α) :
    (scanLoopM P M t i u).time =
      (scanLoopM P ⟨M.fail, fun _ => []⟩ t i u).time + (scanLoopM P M t i u).ret.length := by
  induction t generalizing i u with
  | nil => simp only [scanLoopM, TimeM.time_pure, TimeM.ret_pure, List.length_nil, Nat.add_zero]
  | cons a t ih =>
    simp only [scanLoopM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, TimeM.ret_bind,
      TimeM.ret_pure, List.length_append, List.length_map, List.map_nil, List.length_nil, ih]
    omega

/-- The scan's cost is its number of goto and failure transitions (the cost with emission
suppressed) plus the number of reported pairs. -/
theorem time_scanM_eq (P : List (List α)) (M : Machine α) (t : List α) :
    (scanM P M t).time = (scanM P ⟨M.fail, fun _ => []⟩ t).time + (scanM P M t).ret.length := by
  unfold scanM
  exact time_scanLoopM_eq P M t 0 []

private theorem ret_scanLoopM_silent (P : List (List α)) (f : List α → List α) (t : List α)
    (i : ℕ) (u : List α) : (scanLoopM P ⟨f, fun _ => []⟩ t i u).ret = [] := by
  induction t generalizing i u with
  | nil => rfl
  | cons a t ih =>
    simp only [scanLoopM, TimeM.ret_bind, TimeM.ret_pure, List.map_nil, List.nil_append, ih]

/-- `[AhoCorasick1975]`, Theorem 2: on a nonempty text of length `n`, Algorithm 1 makes fewer than
`2n` goto and failure transitions. This holds for any failure table, because the failure loop of
`stepM` is guarded (a failure transition that does not shorten the state stops at the start
state; with a valid table the guard never fires). The guard's comparison and abort are
uncharged. -/
theorem time_scanM_silent_lt (P : List (List α)) (f : List α → List α) {t : List α}
    (ht : t ≠ []) : (scanM P ⟨f, fun _ => []⟩ t).time < 2 * t.length := by
  have h := time_scanM_lt P ⟨f, fun _ => []⟩ ht
  rw [scanM, ret_scanLoopM_silent, List.length_nil, Nat.add_zero] at h
  exact h

/-! ## Algorithm 3: the failure and output functions -/

/-- Record the failure state `f` of the state `v`, and its output (`[AhoCorasick1975]`, the last
two statements of Algorithm 3). -/
def Machine.set (P : List (List α)) (M : Machine α) (v f : List α) : Machine α where
  fail w := if w = v then f else M.fail w
  out w := if w = v then (if v ∈ P then [v] else []) ++ M.out f else M.out w

/-- The tables before Algorithm 3's main loop: the start state and the states of depth `1` fail to
the start state, and the output of a state of depth `1` is the state itself if it is a keyword. -/
def initMachine (P : List (List α)) : Machine α where
  fail _ := []
  out w := if w ≠ [] ∧ w ∈ P then [w] else []

/-- One round of Algorithm 3 of `[AhoCorasick1975]` (depth `d` to depth `d + 1`): for each keyword
`p` longer than `d`, compute the failure state of `p.take (d + 1)` by one operating cycle from the
failure state of `p.take d`, charging the transitions. Shared prefixes are recomputed with the
same result. The scan of the keyword list itself (including keywords not longer than `d`) is not
charged. -/
def levelM (P : List (List α)) (d : ℕ) : List (List α) → Machine α → TimeM ℕ (Machine α)
  | [], M => return M
  | p :: ps, M =>
    if h : d < p.length then do
      let f ← stepM P M.fail (M.fail (p.take d)) (p[d]'h)
      levelM P d ps (M.set P (p.take (d + 1)) f)
    else
      levelM P d ps M

/-- Rounds `d, d + 1, …, d + n - 1` of Algorithm 3. -/
def buildLoopM (P : List (List α)) : ℕ → ℕ → Machine α → TimeM ℕ (Machine α)
  | 0, _, M => return M
  | n + 1, d, M => do
    let M' ← levelM P d P M
    buildLoopM P n (d + 1) M'

/-- The length of the longest keyword. -/
def maxLength (P : List (List α)) : ℕ :=
  P.foldr (fun p m => max p.length m) 0

omit [DecidableEq α] in
theorem length_le_maxLength {P : List (List α)} {p : List α} (hp : p ∈ P) :
    p.length ≤ maxLength P := by
  induction P with
  | nil => exact absurd hp List.not_mem_nil
  | cons q P ih =>
    simp only [maxLength, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.mp hp with rfl | hp
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hp) (Nat.le_max_right _ _)

/-- Algorithm 3 of `[AhoCorasick1975]`: the failure and output functions, built level by level.
Only goto and failure transitions are charged; the per-depth scan of all of `P`
(`|P| * (maxLength P - 1)` keyword visits) is not. -/
def buildM (P : List (List α)) : TimeM ℕ (Machine α) :=
  buildLoopM P (maxLength P - 1) 1 (initMachine P)

/-- The pattern matching machine of `P`. -/
def build (P : List (List α)) : Machine α :=
  (buildM P).ret

/-- Build the machine of `P` and run it on `t`. -/
def searchM (P : List (List α)) (t : List α) : TimeM ℕ (List (ℕ × List α)) := do
  let M ← buildM P
  scanM P M t

/-- All keyword occurrences, computed by the Aho–Corasick algorithm. -/
def search (P : List (List α)) (t : List α) : List (ℕ × List α) :=
  (searchM P t).ret

/-- `M` has the correct failure and output values on all states of depth at most `d`. -/
private def AgreesUpTo (P : List (List α)) (M : Machine α) (d : ℕ) : Prop :=
  ∀ w, IsNode P w → w.length ≤ d → M.AgreesAt P w

private theorem agreesUpTo_initMachine (P : List (List α)) : AgreesUpTo P (initMachine P) 1 := by
  intro w hw hlen
  refine ⟨(failure_eq_nil_of_length_le_one P hlen).symm, ?_⟩
  match w, hlen with
  | [], _ => simp only [initMachine, ne_eq, not_true_eq_false, false_and, ↓reduceIte, output_nil]
  | [b], _ =>
    simp only [initMachine, ne_eq, List.cons_ne_nil, not_false_eq_true, true_and, output_cons,
      output_nil]

/-- The failure state computed for `p.take (d + 1)`. -/
private theorem stepM_spec {P : List (List α)} {M : Machine α} {d : ℕ} (hd : 1 ≤ d)
    (hM : AgreesUpTo P M d) {p : List α} (hp : p ∈ P) (h : d < p.length) :
    (stepM P M.fail (M.fail (p.take d)) (p[d]'h)).ret = failure P (p.take (d + 1)) ∧
      M.fail (p.take d) = failure P (p.take d) := by
  have hlen : (p.take d).length = d := List.length_take_of_le (Nat.le_of_lt h)
  have hne : p.take d ≠ [] := fun h0 => by rw [h0, List.length_nil] at hlen; omega
  have hfd : M.fail (p.take d) = failure P (p.take d) :=
    (hM _ (isNode_take hp d) (Nat.le_of_eq hlen)).1
  refine ⟨?_, hfd⟩
  have hflt := length_failure_lt P hne
  rw [hfd, ret_stepM _ (fun v hv hvl => (hM v hv (by omega)).1) (isNode_failure P _),
    List.take_add_one, getElem?_pos p d h, Option.toList_some, failure_append_singleton P hne]

/-- `Machine.set` changes the tables only at `v`. -/
private theorem agreesAt_set_of_ne {P : List (List α)} {M : Machine α} {v f w : List α}
    (hw : w ≠ v) (h : M.AgreesAt P w) : (M.set P v f).AgreesAt P w := by
  simp only [Machine.AgreesAt, Machine.set, hw, ↓reduceIte]
  exact h

/-- Recording the correct failure state of a nonempty state `v` whose failure state already has
the correct output makes the tables correct at `v`. -/
private theorem agreesAt_set {P : List (List α)} {M : Machine α} {v : List α} (hv : v ≠ [])
    (hout : M.out (failure P v) = output P (failure P v)) :
    (M.set P v (failure P v)).AgreesAt P v := by
  simp only [Machine.AgreesAt, Machine.set, ↓reduceIte, hout, true_and]
  exact (output_eq_of_ne_nil P hv).symm

private theorem levelM_spec {P : List (List α)} {d : ℕ} (hd : 1 ≤ d) :
    ∀ (ps : List (List α)) (M : Machine α), (∀ p ∈ ps, p ∈ P) → AgreesUpTo P M d →
      (∀ w, M.AgreesAt P w → (levelM P d ps M).ret.AgreesAt P w) ∧
      ∀ p ∈ ps, (h : d < p.length) → (levelM P d ps M).ret.AgreesAt P (p.take (d + 1)) := by
  intro ps
  induction ps with
  | nil =>
    intro M _ _
    exact ⟨fun w hw => hw, fun p hp => absurd hp List.not_mem_nil⟩
  | cons q ps ih =>
    intro M hps hM
    have hqP : q ∈ P := hps q List.mem_cons_self
    have hpsP : ∀ p ∈ ps, p ∈ P := fun p hp => hps p (List.mem_cons_of_mem q hp)
    rw [levelM]
    split_ifs with hq
    · obtain ⟨hstep, _⟩ := stepM_spec hd hM hqP hq
      simp only [TimeM.ret_bind]
      rw [hstep]
      set v := q.take (d + 1)
      set M1 := M.set P v (failure P v)
      have hvlen : v.length = d + 1 := List.length_take_of_le hq
      have hvne : v ≠ [] := fun h0 => by rw [h0, List.length_nil] at hvlen; omega
      have hflt := length_failure_lt P hvne
      have hM1v : M1.AgreesAt P v :=
        agreesAt_set hvne (hM _ (isNode_failure P v) (by omega)).2
      have hpres : ∀ w, M.AgreesAt P w → M1.AgreesAt P w := fun w hw => by
        by_cases hwv : w = v
        · rw [hwv]; exact hM1v
        · exact agreesAt_set_of_ne hwv hw
      have hM1 : AgreesUpTo P M1 d := fun w hw hwl => hpres w (hM w hw hwl)
      obtain ⟨ih1, ih2⟩ := ih M1 hpsP hM1
      refine ⟨fun w hw => ih1 w (hpres w hw), fun p hp hpd => ?_⟩
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ih1 _ hM1v
      · exact ih2 p hp hpd
    · obtain ⟨ih1, ih2⟩ := ih M hpsP hM
      refine ⟨ih1, fun p hp hpd => ?_⟩
      rcases List.mem_cons.mp hp with rfl | hp
      · exact absurd hpd hq
      · exact ih2 p hp hpd

private theorem agreesUpTo_levelM {P : List (List α)} {d : ℕ} (hd : 1 ≤ d) {M : Machine α}
    (hM : AgreesUpTo P M d) : AgreesUpTo P (levelM P d P M).ret (d + 1) := by
  obtain ⟨h1, h2⟩ := levelM_spec hd P M (fun p hp => hp) hM
  intro w hw hwl
  by_cases hwd : w.length ≤ d
  · exact h1 w (hM w hw hwd)
  · rcases hw with rfl | ⟨p, hp, hwp⟩
    · rw [List.length_nil] at hwd; omega
    · have hwlen : w.length = d + 1 := by omega
      have hpd : d < p.length := by have := hwp.length_le; omega
      have hwt : w = p.take (d + 1) := by rw [← hwlen]; exact List.prefix_iff_eq_take.mp hwp
      rw [hwt]
      exact h2 p hp hpd

private theorem agreesUpTo_buildLoopM {P : List (List α)} :
    ∀ (n d : ℕ) (M : Machine α), 1 ≤ d → AgreesUpTo P M d →
      AgreesUpTo P (buildLoopM P n d M).ret (d + n) := by
  intro n
  induction n with
  | zero => intro d M _ hM; exact hM
  | succ n ih =>
    intro d M hd hM
    simp only [buildLoopM, TimeM.ret_bind]
    have := ih (d + 1) _ (by omega) (agreesUpTo_levelM hd hM)
    rwa [Nat.add_assoc, Nat.add_comm 1 n] at this

/-- Correctness of Algorithm 3 (`[AhoCorasick1975]`, Lemmas 1 and 2, Theorem 1): the constructed
failure and output functions are those of `P` on every state. -/
theorem isValid_build (P : List (List α)) : (build P).IsValid P := by
  have h := agreesUpTo_buildLoopM (P := P) (maxLength P - 1) 1 (initMachine P) (Nat.le_refl 1)
    (agreesUpTo_initMachine P)
  intro w hw
  refine h w hw ?_
  rcases hw with rfl | ⟨p, hp, hwp⟩
  · exact Nat.zero_le _
  · have := hwp.length_le
    have := length_le_maxLength hp
    omega

/-- Remaining-cost potential of keyword `p` before round `d` of Algorithm 3. -/
private def pot (P : List (List α)) (d : ℕ) (p : List α) : ℕ :=
  (failure P (p.take d)).length + 2 * (p.length - d)

private theorem time_levelM_le {P : List (List α)} {d : ℕ} (hd : 1 ≤ d) :
    ∀ (ps : List (List α)) (M : Machine α), (∀ p ∈ ps, p ∈ P) → AgreesUpTo P M d →
      (levelM P d ps M).time + (ps.map (pot P (d + 1))).sum ≤ (ps.map (pot P d)).sum := by
  intro ps
  induction ps with
  | nil =>
    intro M _ _
    simp only [levelM, TimeM.time_pure, List.map_nil, List.sum_nil, Nat.add_zero, Nat.le_refl]
  | cons q ps ih =>
    intro M hps hM
    have hqP : q ∈ P := hps q List.mem_cons_self
    have hpsP : ∀ p ∈ ps, p ∈ P := fun p hp => hps p (List.mem_cons_of_mem q hp)
    rw [levelM, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
    split_ifs with hq
    · obtain ⟨hstep, hfd⟩ := stepM_spec hd hM hqP hq
      rw [hfd] at hstep
      have hcost := (time_stepM_le P M.fail (failure P (q.take d)) (q[d]'hq)).1
      rw [hstep] at hcost
      simp only [TimeM.time_bind]
      rw [hfd, hstep]
      have hvlen : (q.take (d + 1)).length = d + 1 := List.length_take_of_le hq
      have hM1 : AgreesUpTo P (M.set P (q.take (d + 1)) (failure P (q.take (d + 1)))) d :=
        fun w hw hwl => agreesAt_set_of_ne (fun h => by rw [h] at hwl; omega) (hM w hw hwl)
      have := ih _ hpsP hM1
      simp only [pot] at this ⊢
      omega
    · have hge : ∀ e, d ≤ e → pot P e q = pot P d q := fun e he => by
        simp only [pot, List.take_of_length_le (show q.length ≤ e by omega),
          List.take_of_length_le (show q.length ≤ d by omega)]
        omega
      have := ih M hpsP hM
      rw [hge (d + 1) (by omega)]
      omega

private theorem time_buildLoopM_le {P : List (List α)} :
    ∀ (n d : ℕ) (M : Machine α), 1 ≤ d → AgreesUpTo P M d →
      (buildLoopM P n d M).time ≤ (P.map (pot P d)).sum := by
  intro n
  induction n with
  | zero => intro d M _ _; simp only [buildLoopM, TimeM.time_pure, Nat.zero_le]
  | succ n ih =>
    intro d M hd hM
    simp only [buildLoopM, TimeM.time_bind]
    have h1 := time_levelM_le hd P M (fun p hp => hp) hM
    have h2 := ih (d + 1) _ (by omega) (agreesUpTo_levelM hd hM)
    omega

/-- The transition bound of `[AhoCorasick1975]`, Theorem 4: Algorithm 3 makes at most
`2 * (|p| - 1)` goto and failure transitions per keyword `p`. This bounds the charged transitions
only, not total construction time: the per-depth scan of `P` in `buildM` is uncharged and can be
quadratic in the total keyword length. -/
theorem time_buildM_le (P : List (List α)) :
    (buildM P).time ≤ (P.map fun p => 2 * (p.length - 1)).sum := by
  have h := time_buildLoopM_le (P := P) (maxLength P - 1) 1 (initMachine P) (Nat.le_refl 1)
    (agreesUpTo_initMachine P)
  have hpot : P.map (pot P 1) = P.map fun p => 2 * (p.length - 1) := by
    refine List.map_congr_left fun p _ => ?_
    rw [pot, failure_eq_nil_of_length_le_one P (List.length_take_le 1 p), List.length_nil,
      Nat.zero_add]
  rw [hpot] at h
  exact h

/-- Correctness of the Aho–Corasick algorithm (`[AhoCorasick1975]`, Theorem 1). -/
theorem search_eq (P : List (List α)) (t : List α) : search P t = occurrences P t := by
  simp only [search, searchM, TimeM.ret_bind]
  exact ret_scanM (isValid_build P) t

theorem mem_search_iff {P : List (List α)} {t : List α} {i : ℕ} {y : List α} :
    (i, y) ∈ search P t ↔ IsOccurrence P t i y := by
  rw [search_eq, mem_occurrences_iff]

/-- Charged cost of the Aho–Corasick algorithm: at most `2 * (|p| - 1)` goto and failure
transitions per keyword `p` to build the machine (the transitions of `[AhoCorasick1975]`,
Theorem 4; the construction's level bookkeeping is not charged), at most `2 * |t|` transitions
to scan (Theorem 2), and one tick per reported occurrence. -/
theorem time_searchM_le (P : List (List α)) (t : List α) :
    (searchM P t).time ≤
      (P.map fun p => 2 * (p.length - 1)).sum + 2 * t.length + (occurrences P t).length := by
  simp only [searchM, TimeM.time_bind]
  have h1 := time_buildM_le P
  have h2 := time_scanM_le P (buildM P).ret t
  have h3 : (scanM P (buildM P).ret t).ret = occurrences P t := ret_scanM (isValid_build P) t
  rw [h3] at h2
  omega

end Cslib.Algorithms.Lean.AhoCorasick
