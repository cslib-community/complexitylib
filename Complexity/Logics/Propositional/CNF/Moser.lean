/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.ExactDistinct
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.FinRange

/-!
# Moser's resampling algorithm for `k`-SAT

Moser's algorithm [Moser, Algorithms 2.1 and 2.2][Moser2009] searches for a satisfying assignment
of a CNF formula `φ` by local corrections. `Solve` starts from a random assignment and scans the
clauses. On a violated clause `C` it calls `Fix C`, which resamples the variables of `C` with fresh
random bits and then, as long as some clause sharing a variable with `C` (`C` included) is
violated, calls `Fix D` on the first such clause `D`.

The randomness is an explicit tape `x : ℕ → Bool`. The initial assignment is `x 0, …, x (n - 1)`,
and the `j`-th resampling gives the `i`-th variable of its clause the bit `x (n + j k + i)`. The
recursion of `Fix` is unrolled into a machine whose state records the stack of active `Fix` calls,
the position of the scan of `Solve`, the resampled clauses and the current assignment. A run is
given a *budget* of `t` resamplings: when the next move would resample for the `t + 1`-st time,
the machine stops instead.

Every run stops within `m + 2 t` steps, where `m` is the number of clauses (`move_final`). A run
that does not use up its budget ends with a satisfying assignment (`eval_final_of_not_exhausts`),
and a run with budget `t` reads only the first `n + t k` tape bits (`exhausts_congr`). The
entropy-compression argument bounding the number of tapes that use up the budget is in
`Complexity.Logics.Propositional.CNF.Moser.Compression`, and its probabilistic consequences are in
`Complexity.Logics.Propositional.CNF.Moser.Probability`.

`Fix` takes the first violated clause in index order, as Moser takes the lexicographically first
one; `Solve` also takes the first violated clause (`lt_of_move_eq_root`). `Solve` makes one pass
over the clauses, as in Fortnow's exposition [Fortnow2009]: a returning `Fix` call leaves every
clause it found satisfied satisfied (`Sound`), so a rescan from the first clause would find the
same clause. Moser's restarts, which serve his running-time analysis, are omitted.

## Main definitions

* `Cslib.Logic.PL.Moser.Shares`, `Cslib.Logic.PL.Moser.neighbors`, `Cslib.Logic.PL.Moser.degree`:
  clauses sharing a variable.
* `Cslib.Logic.PL.Moser.resample`: resampling a clause from the tape.
* `Cslib.Logic.PL.Moser.State`, `Cslib.Logic.PL.Moser.move`, `Cslib.Logic.PL.Moser.step`,
  `Cslib.Logic.PL.Moser.run`, `Cslib.Logic.PL.Moser.final`: the machine.
* `Cslib.Logic.PL.Moser.Exhausts`: the run uses up its budget of resamplings.

## Main results

* `Cslib.Logic.PL.Moser.move_final`: every run stops within `m + 2 t` steps.
* `Cslib.Logic.PL.Moser.eval_final_of_not_exhausts`: **correctness**.
* `Cslib.Logic.PL.Moser.lt_of_move_eq_root`: `Solve` fixes the first violated clause.
* `Cslib.Logic.PL.Moser.Exhausts.mono`, `Cslib.Logic.PL.Moser.final_eq_of_not_exhausts`: runs with
  larger budgets.
* `Cslib.Logic.PL.Moser.exhausts_congr`: a run with budget `t` reads `n + t k` tape bits.

## References

* [R. A. Moser, *A constructive proof of the Lovász Local Lemma*][Moser2009]
* [L. Fortnow, *A Kolmogorov Complexity Proof of the Lovász Local Lemma*][Fortnow2009]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Finset

/-- A clause is false exactly when each of its literals is read against its polarity. -/
theorem Clause.eval_eq_false_iff {V : Type*} (σ : V → Bool) (c : Clause V) :
    c.eval σ = false ↔ ∀ l ∈ c, σ l.1 = !l.2 := by
  rw [← Bool.not_eq_true, Clause.eval_eq_true_iff]
  simp only [not_exists, not_and]
  refine forall₂_congr fun l _ => ?_
  cases σ l.1 <;> cases l.2 <;> simp

/-- A clause only depends on the values of its variables. -/
theorem Clause.eval_congr {V : Type*} {σ τ : V → Bool} {c : Clause V}
    (h : ∀ l ∈ c, σ l.1 = τ l.1) : c.eval σ = c.eval τ := by
  rw [Bool.eq_iff_iff, Clause.eval_eq_true_iff, Clause.eval_eq_true_iff]
  exact exists_congr fun l => and_congr_right fun hl => by rw [h l hl]

namespace Moser

variable {n : ℕ}

/-! ### Clauses and resampling -/

/-- The variables of a clause, in order of occurrence. -/
abbrev vbl (c : Clause (Fin n)) : List (Fin n) := c.map Prod.fst

/-- Two clauses share a variable. -/
def Shares (c d : Clause (Fin n)) : Prop := ∃ v ∈ vbl c, v ∈ vbl d

instance (c d : Clause (Fin n)) : Decidable (Shares c d) :=
  inferInstanceAs (Decidable (∃ v ∈ vbl c, v ∈ vbl d))

theorem shares_self {c : Clause (Fin n)} (hc : c ≠ []) : Shares c c := by
  obtain ⟨l, hl⟩ := List.exists_mem_of_ne_nil c hc
  exact ⟨l.1, List.mem_map.2 ⟨l, hl, rfl⟩, List.mem_map.2 ⟨l, hl, rfl⟩⟩

/-- Replace the values of the variables of `c` by tape bits: the `i`-th variable of `c` receives
`x (o + i)`, and every other variable keeps its value. -/
def resample (c : Clause (Fin n)) (x : ℕ → Bool) (o : ℕ) (σ : Fin n → Bool) : Fin n → Bool :=
  fun v => if v ∈ vbl c then x (o + (vbl c).idxOf v) else σ v

/-- Undo the resampling of a clause that was violated before it: its variables get the values that
falsify their literals. -/
def unresample (c : Clause (Fin n)) (σ : Fin n → Bool) : Fin n → Bool :=
  fun v => match c.find? (fun l => l.1 == v) with
    | some l => !l.2
    | none => σ v

theorem resample_of_not_mem {c : Clause (Fin n)} {x : ℕ → Bool} {o : ℕ} {σ : Fin n → Bool}
    {v : Fin n} (h : v ∉ vbl c) : resample c x o σ v = σ v := ite_eq_right h

theorem resample_getElem {c : Clause (Fin n)} (hc : (vbl c).Nodup) (x : ℕ → Bool) (o : ℕ)
    (σ : Fin n → Bool) (i : ℕ) (hi : i < (vbl c).length) :
    resample c x o σ (vbl c)[i] = x (o + i) := by
  rw [resample, ite_eq_left (List.getElem_mem hi), hc.idxOf_getElem]

/-- A violated clause is recovered from its resampling. -/
theorem unresample_resample {c : Clause (Fin n)} {σ : Fin n → Bool} (hc : c.eval σ = false)
    (x : ℕ → Bool) (o : ℕ) : unresample c (resample c x o σ) = σ := by
  funext v
  cases h : c.find? (fun l => l.1 == v) with
  | some l =>
    have hlv : l.1 = v := by simpa using List.find?_some h
    simp only [unresample, h]
    rw [← hlv, (Clause.eval_eq_false_iff σ c).1 hc l (List.mem_of_find?_eq_some h)]
  | none =>
    have hv : v ∉ vbl c := by
      intro hv
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hv
      exact List.find?_eq_none.1 h l hl (by simp)
    simp only [unresample, h]
    exact resample_of_not_mem hv

theorem eval_resample_of_not_shares {c d : Clause (Fin n)} (h : ¬Shares c d) (x : ℕ → Bool)
    (o : ℕ) (σ : Fin n → Bool) : d.eval (resample c x o σ) = d.eval σ :=
  Clause.eval_congr fun l hl =>
    resample_of_not_mem fun hv => h ⟨l.1, hv, List.mem_map.2 ⟨l, hl, rfl⟩⟩

/-- Resampling only reads the tape bits `x o, …, x (o + |c| - 1)`. -/
theorem resample_congr {c : Clause (Fin n)} {x y : ℕ → Bool} {o : ℕ}
    (h : ∀ i < (vbl c).length, x (o + i) = y (o + i)) (σ : Fin n → Bool) :
    resample c x o σ = resample c y o σ := by
  funext v
  by_cases hv : v ∈ vbl c
  · simp only [resample, hv, ite_true]
    exact h _ (List.idxOf_lt_length_of_mem hv)
  · rw [resample_of_not_mem hv, resample_of_not_mem hv]

/-! ### The machine -/

/-- The control state of `Fix`/`Solve`: the stack of active `Fix` calls (innermost first), the
position of the scan of `Solve`, and the resampled clauses (latest first). -/
structure Control (m : ℕ) where
  /-- The active `Fix` calls, innermost first. -/
  stack : List (Fin m)
  /-- The position of the scan of `Solve`. -/
  ptr : ℕ
  /-- The resampled clauses, latest first. -/
  trace : List (Fin m)

/-- A state of `Fix`/`Solve`: the control state and the current assignment. -/
structure State (n m : ℕ) extends Control m where
  /-- The current assignment. -/
  assignment : Fin n → Bool

/-- The moves of the machine. -/
inductive Move (m : ℕ) where
  /-- `Solve` passes over a satisfied clause. -/
  | skip
  /-- `Solve` calls `Fix c` on the violated clause `c` at its scan position. -/
  | root (c : Fin m)
  /-- `Fix` calls `Fix d` on the first violated clause `d`, at position `pos` among the clauses
  sharing a variable with the innermost call. -/
  | child (pos : ℕ) (d : Fin m)
  /-- The innermost `Fix` call returns. -/
  | pop
  /-- The run is over: `Solve` has finished its scan, or the budget of resamplings is used up. -/
  | stop

variable (φ : CNF (Fin n))

/-- The clauses sharing a variable with clause `c` (including `c`, if it is nonempty), in index
order. -/
def neighbors (c : Fin φ.length) : List (Fin φ.length) :=
  (List.finRange φ.length).filter fun d => decide (Shares φ[c] φ[d])

/-- The number of other clauses sharing a variable with clause `i`. -/
def degree (i : Fin φ.length) : ℕ := #{j : Fin φ.length | j ≠ i ∧ Shares φ[i] φ[j]}

/-- The next move with a budget of `t` resamplings. -/
def move (t : ℕ) (s : State n φ.length) : Move φ.length :=
  match s.stack with
  | [] =>
    if h : s.ptr < φ.length then
      if φ[s.ptr].eval s.assignment then .skip
      else if s.trace.length < t then .root ⟨s.ptr, h⟩ else .stop
    else .stop
  | c :: _ =>
    match (neighbors φ c).find? (fun d => !φ[d].eval s.assignment) with
    | some d => if s.trace.length < t then .child ((neighbors φ c).idxOf d) d else .stop
    | none => .pop

/-- Perform a move. The `j`-th resampling reads the tape bits `x (n + j k), …,
x (n + j k + k - 1)`. -/
def apply (k : ℕ) (x : ℕ → Bool) (s : State n φ.length) : Move φ.length → State n φ.length
  | .skip => { s with ptr := s.ptr + 1 }
  | .root c =>
    { assignment := resample φ[c] x (n + s.trace.length * k) s.assignment
      stack := [c]
      ptr := s.ptr + 1
      trace := c :: s.trace }
  | .child _ d =>
    { assignment := resample φ[d] x (n + s.trace.length * k) s.assignment
      stack := d :: s.stack
      ptr := s.ptr
      trace := d :: s.trace }
  | .pop => { s with stack := s.stack.tail }
  | .stop => s

/-- One step of the machine with a budget of `t` resamplings. -/
def step (k t : ℕ) (x : ℕ → Bool) (s : State n φ.length) : State n φ.length :=
  apply φ k x s (move φ t s)

/-- The initial state: the first `n` tape bits are the assignment. -/
def init (x : ℕ → Bool) : State n φ.length :=
  { assignment := fun v => x v, stack := [], ptr := 0, trace := [] }

/-- The state after `N` steps. -/
def run (k t : ℕ) (x : ℕ → Bool) : ℕ → State n φ.length
  | 0 => init φ x
  | N + 1 => step φ k t x (run k t x N)

/-- Enough steps for every run with a budget of `t` resamplings to stop. -/
def fuel (t : ℕ) : ℕ := φ.length + 2 * t

/-- The final state of the run with a budget of `t` resamplings. -/
def final (k t : ℕ) (x : ℕ → Bool) : State n φ.length := run φ k t x (fuel φ t)

/-- The run on the tape `x` uses up its budget of `t` resamplings. -/
def Exhausts (k t : ℕ) (x : ℕ → Bool) : Prop := t ≤ (final φ k t x).trace.length

instance (k t : ℕ) (x : ℕ → Bool) : Decidable (Exhausts φ k t x) :=
  inferInstanceAs (Decidable (t ≤ _))

variable {φ}

theorem mem_neighbors {c d : Fin φ.length} : d ∈ neighbors φ c ↔ Shares φ[c] φ[d] := by
  simp [neighbors, List.mem_filter, List.mem_finRange]

/-- The clauses sharing a variable with a clause are at most one more than its degree. -/
theorem length_neighbors_le (c : Fin φ.length) : (neighbors φ c).length ≤ degree φ c + 1 := by
  have hnd : (neighbors φ c).Nodup := (List.nodup_finRange _).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  calc #(neighbors φ c).toFinset
      ≤ #(insert c ({j : Fin φ.length | j ≠ c ∧ Shares φ[c] φ[j]} : Finset _)) := by
        apply card_le_card
        intro j hj
        rw [List.mem_toFinset, mem_neighbors] at hj
        rw [mem_insert, mem_filter]
        by_cases h : j = c
        · exact Or.inl h
        · exact Or.inr ⟨mem_univ _, h, hj⟩
    _ ≤ degree φ c + 1 := card_insert_le _ _

theorem getElem_mem_fin (c : Fin φ.length) : φ[c] ∈ φ := List.getElem_mem c.2

theorem run_succ (k t : ℕ) (x : ℕ → Bool) (N : ℕ) :
    run φ k t x (N + 1) = step φ k t x (run φ k t x N) := rfl

/-- The five kinds of moves, with the facts that determine them. -/
theorem move_cases (t : ℕ) (s : State n φ.length) :
    (move φ t s = .skip ∧ s.stack = [] ∧
      ∃ h : s.ptr < φ.length, φ[(⟨s.ptr, h⟩ : Fin φ.length)].eval s.assignment = true) ∨
    (∃ c : Fin φ.length, move φ t s = .root c ∧ s.stack = [] ∧ c.1 = s.ptr ∧
      φ[c].eval s.assignment = false ∧ s.trace.length < t) ∨
    (∃ e st d, move φ t s = .child ((neighbors φ e).idxOf d) d ∧ s.stack = e :: st ∧
      d ∈ neighbors φ e ∧ φ[d].eval s.assignment = false ∧ s.trace.length < t) ∨
    (∃ e st, move φ t s = .pop ∧ s.stack = e :: st ∧
      ∀ d ∈ neighbors φ e, φ[d].eval s.assignment = true) ∨
    (move φ t s = .stop ∧ (t ≤ s.trace.length ∨ (s.stack = [] ∧ φ.length ≤ s.ptr))) := by
  obtain ⟨⟨stack, ptr, trace⟩, σ⟩ := s
  cases stack with
  | nil =>
    by_cases hp : ptr < φ.length
    · by_cases hc : φ[ptr].eval σ = true
      · exact Or.inl ⟨by simp [move, hp, hc], rfl, hp, hc⟩
      · by_cases ht : trace.length < t
        · exact Or.inr (Or.inl ⟨⟨ptr, hp⟩, by simp [move, hp, hc, ht], rfl, rfl,
            by simpa using hc, ht⟩)
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by simp [move, hp, hc, ht],
            Or.inl (Nat.le_of_not_lt ht)⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by simp [move, hp],
        Or.inr ⟨rfl, Nat.le_of_not_lt hp⟩⟩)))
  | cons e st =>
    cases hf : (neighbors φ e).find? (fun d => !φ[d].eval σ) with
    | some d =>
      have hd := List.mem_of_find?_eq_some hf
      have hev : φ[d].eval σ = false := by simpa using List.find?_some hf
      by_cases ht : trace.length < t
      · exact Or.inr (Or.inr (Or.inl ⟨e, st, d, by simp only [move, hf, ht, ite_true], rfl, hd,
          hev, ht⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by simp only [move, hf, ht, ite_false],
          Or.inl (Nat.le_of_not_lt ht)⟩)))
    | none =>
      refine Or.inr (Or.inr (Or.inr (Or.inl ⟨e, st, by simp only [move, hf], rfl, fun d hd => ?_⟩)))
      simpa using List.find?_eq_none.1 hf d hd

/-! ### Correctness -/

variable (φ) in
/-- The invariant of `Fix`/`Solve`: a violated clause lies at or after the scan position, or shares
a variable with an active `Fix` call. -/
def Sound (s : State n φ.length) : Prop :=
  ∀ j : Fin φ.length, φ[j].eval s.assignment = false →
    s.ptr ≤ j.1 ∨ ∃ e ∈ s.stack, Shares φ[e] φ[j]

theorem sound_init (x : ℕ → Bool) : Sound φ (init φ x) := fun _ _ => Or.inl (Nat.zero_le _)

theorem sound_step (hne : ∀ c ∈ φ, c ≠ []) (k t : ℕ) (x : ℕ → Bool) {s : State n φ.length}
    (hs : Sound φ s) : Sound φ (step φ k t x s) := by
  rcases move_cases t s with ⟨hm, hst, hp, hev⟩ | ⟨c, hm, hst, hc, -, -⟩ |
    ⟨e, st, d, hm, -, -, -, -⟩ | ⟨e, st, hm, hst, hall⟩ | ⟨hm, -⟩
  · intro j hj
    simp only [step, hm, apply] at hj ⊢
    rcases hs j hj with h | ⟨e, he, -⟩
    · rcases Nat.lt_or_eq_of_le h with h | h
      · exact Or.inl h
      · have hj' : j = ⟨s.ptr, hp⟩ := Fin.ext h.symm
        subst hj'
        rw [hev] at hj
        exact absurd hj (by decide)
    · rw [hst] at he
      exact absurd he List.not_mem_nil
  · intro j hj
    simp only [step, hm, apply] at hj ⊢
    by_cases hsh : Shares φ[c] φ[j]
    · exact Or.inr ⟨c, List.mem_singleton_self c, hsh⟩
    · rw [eval_resample_of_not_shares hsh] at hj
      left
      rcases hs j hj with h | ⟨e, he, -⟩
      · rcases Nat.lt_or_eq_of_le h with h | h
        · exact h
        · have hjc : j = c := Fin.ext (h.symm.trans hc.symm)
          subst hjc
          exact absurd (shares_self (hne _ (getElem_mem_fin j))) hsh
      · rw [hst] at he
        exact absurd he List.not_mem_nil
  · intro j hj
    simp only [step, hm, apply] at hj ⊢
    by_cases hsh : Shares φ[d] φ[j]
    · exact Or.inr ⟨d, List.mem_cons_self, hsh⟩
    · rw [eval_resample_of_not_shares hsh] at hj
      rcases hs j hj with h | ⟨e, he, hshe⟩
      · exact Or.inl h
      · exact Or.inr ⟨e, List.mem_cons_of_mem _ he, hshe⟩
  · intro j hj
    simp only [step, hm, apply] at hj ⊢
    rcases hs j hj with h | ⟨e', he', hshe⟩
    · exact Or.inl h
    · rw [hst] at he' ⊢
      rw [List.tail_cons]
      rcases List.mem_cons.1 he' with rfl | he'
      · rw [hall j (mem_neighbors.2 hshe)] at hj
        exact absurd hj (by decide)
      · exact Or.inr ⟨e', he', hshe⟩
  · simp only [step, hm, apply]
    exact hs

/-- When `Solve` has finished its scan with no active `Fix` call, the assignment satisfies `φ`. -/
theorem eval_of_sound {s : State n φ.length} (hs : Sound φ s) (hst : s.stack = [])
    (hp : φ.length ≤ s.ptr) : φ.eval s.assignment = true := by
  rw [CNF.eval_eq_true_iff]
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hc
  by_contra hf
  rw [Bool.not_eq_true] at hf
  rcases hs ⟨i, hi⟩ hf with h | ⟨e, he, -⟩
  · exact absurd (lt_of_lt_of_le hi hp) (not_lt.2 h)
  · rw [hst] at he
    exact absurd he List.not_mem_nil

theorem sound_run (hne : ∀ c ∈ φ, c ≠ []) (k t : ℕ) (x : ℕ → Bool) (N : ℕ) :
    Sound φ (run φ k t x N) := by
  induction N with
  | zero => exact sound_init x
  | succ N ih => exact sound_step hne k t x ih

/-- `Solve` calls `Fix` on the first violated clause: in a sound state, every clause before the one
it fixes is satisfied. -/
theorem lt_of_move_eq_root {t : ℕ} {s : State n φ.length} (hs : Sound φ s) {c : Fin φ.length}
    (hm : move φ t s = .root c) {j : Fin φ.length} (hj : j < c) :
    φ[j].eval s.assignment = true := by
  rcases move_cases t s with ⟨hm', -⟩ | ⟨c', hm', hst, hc', -⟩ | ⟨e, st, d, hm', -⟩ |
    ⟨e, st, hm', -⟩ | ⟨hm', -⟩ <;> rw [hm] at hm' <;> cases hm'
  by_contra hf
  rw [Bool.not_eq_true] at hf
  rcases hs j hf with h | ⟨e, he, -⟩
  · have : j.1 < c.1 := hj
    omega
  · rw [hst] at he
    exact absurd he List.not_mem_nil

/-! ### Termination -/

variable (φ) in
/-- The termination measure: each move other than `stop` decreases it. -/
def potential (t : ℕ) (s : State n φ.length) : ℕ :=
  (φ.length - s.ptr) + 2 * (t - s.trace.length) + s.stack.length

theorem potential_step_lt (k t : ℕ) (x : ℕ → Bool) {s : State n φ.length}
    (hm : move φ t s ≠ .stop) : potential φ t (step φ k t x s) < potential φ t s := by
  rcases move_cases t s with ⟨hm', -, hp, -⟩ | ⟨c, hm', hst, hc, -, ht⟩ |
    ⟨e, st, d, hm', -, -, -, ht⟩ | ⟨e, st, hm', hst, -⟩ | ⟨hm', -⟩
  · simp only [potential, step, hm', apply]
    omega
  · have := c.2
    simp only [potential, step, hm', apply, List.length_cons, hst, List.length_nil]
    omega
  · simp only [potential, step, hm', apply, List.length_cons]
    omega
  · simp only [potential, step, hm', apply, hst, List.tail_cons, List.length_cons]
    omega
  · exact absurd hm' hm

theorem move_eq_stop_of_potential_eq_zero {t : ℕ} {s : State n φ.length}
    (h : potential φ t s = 0) : move φ t s = .stop := by
  rcases move_cases t s with ⟨-, -, hp, -⟩ | ⟨c, -, -, -, -, ht⟩ |
    ⟨e, st, d, -, -, -, -, ht⟩ | ⟨e, st, -, hst, -⟩ | ⟨hm, -⟩
  · simp only [potential] at h
    omega
  · simp only [potential] at h
    omega
  · simp only [potential] at h
    omega
  · simp only [potential, hst, List.length_cons] at h
    omega
  · exact hm

theorem step_eq_self {k t : ℕ} {x : ℕ → Bool} {s : State n φ.length} (h : move φ t s = .stop) :
    step φ k t x s = s := by
  simp only [step, h, apply]

theorem potential_run_add_le (k t : ℕ) (x : ℕ → Bool) (N : ℕ) :
    move φ t (run φ k t x N) = .stop ∨ potential φ t (run φ k t x N) + N ≤ fuel φ t := by
  induction N with
  | zero =>
    right
    simp [potential, run, init, fuel]
  | succ N ih =>
    rcases ih with h | h
    · left
      rw [run_succ, step_eq_self h]
      exact h
    · by_cases hm : move φ t (run φ k t x N) = .stop
      · left
        rw [run_succ, step_eq_self hm]
        exact hm
      · right
        have := potential_step_lt k t x hm
        rw [run_succ]
        omega

/-- **Termination.** Every run with a budget of `t` resamplings stops within `m + 2 t` steps. -/
theorem move_final (k t : ℕ) (x : ℕ → Bool) : move φ t (final φ k t x) = .stop := by
  unfold final
  rcases potential_run_add_le k t x (fuel φ t) with h | h
  · exact h
  · exact move_eq_stop_of_potential_eq_zero (by omega)

theorem run_eq_final {k t : ℕ} {x : ℕ → Bool} {N : ℕ} (hN : fuel φ t ≤ N) :
    run φ k t x N = final φ k t x := by
  induction N, hN using Nat.le_induction with
  | base => rfl
  | succ N hN ih => rw [run_succ, ih, step_eq_self (move_final k t x)]

/-- A run that does not use up its budget ends with `Solve` done: no active `Fix` call and a
finished scan. -/
theorem final_halted {k t : ℕ} {x : ℕ → Bool} (h : ¬Exhausts φ k t x) :
    (final φ k t x).stack = [] ∧ φ.length ≤ (final φ k t x).ptr := by
  rcases move_cases t (final φ k t x) with ⟨hm, -⟩ | ⟨c, hm, -⟩ | ⟨e, st, d, hm, -⟩ |
    ⟨e, st, hm, -⟩ | ⟨-, ht | hh⟩
  · simp [move_final] at hm
  · simp [move_final] at hm
  · simp [move_final] at hm
  · simp [move_final] at hm
  · exact absurd ht h
  · exact hh

/-- **Correctness.** A run that does not use up its budget of `t` resamplings ends with a
satisfying assignment. -/
theorem eval_final_of_not_exhausts (hne : ∀ c ∈ φ, c ≠ []) {k t : ℕ} {x : ℕ → Bool}
    (h : ¬Exhausts φ k t x) : φ.eval (final φ k t x).assignment = true :=
  eval_of_sound (sound_run hne k t x _) (final_halted h).1 (final_halted h).2

/-! ### Budgets -/

theorem length_trace_le_step (k t : ℕ) (x : ℕ → Bool) (s : State n φ.length) :
    s.trace.length ≤ (step φ k t x s).trace.length := by
  rcases move_cases t s with ⟨hm, -⟩ | ⟨c, hm, -⟩ | ⟨e, st, d, hm, -⟩ | ⟨e, st, hm, -⟩ |
    ⟨hm, -⟩ <;> simp only [step, hm, apply, List.length_cons] <;> omega

theorem length_trace_run_le (k t : ℕ) (x : ℕ → Bool) (N : ℕ) :
    (run φ k t x N).trace.length ≤ t := by
  induction N with
  | zero => exact Nat.zero_le _
  | succ N ih =>
    rw [run_succ]
    rcases move_cases t (run φ k t x N) with ⟨hm, -⟩ | ⟨c, hm, -, -, -, ht⟩ |
      ⟨e, st, d, hm, -, -, -, ht⟩ | ⟨e, st, hm, -⟩ | ⟨hm, -⟩
    · simp only [step, hm, apply]
      exact ih
    · simp only [step, hm, apply, List.length_cons]
      omega
    · simp only [step, hm, apply, List.length_cons]
      omega
    · simp only [step, hm, apply]
      exact ih
    · simp only [step, hm, apply]
      exact ih

theorem length_trace_final_eq {k t : ℕ} {x : ℕ → Bool} (h : Exhausts φ k t x) :
    (final φ k t x).trace.length = t :=
  le_antisymm (length_trace_run_le k t x _) h

theorem move_eq_move_of_lt {t t' : ℕ} {s : State n φ.length} (h : s.trace.length < t)
    (h' : s.trace.length < t') : move φ t s = move φ t' s := by
  simp only [move, h, h', ite_true]

theorem run_budget {k t t' : ℕ} (ht : t ≤ t') (x : ℕ → Bool) (N : ℕ) :
    t ≤ (run φ k t x N).trace.length ∨ run φ k t x N = run φ k t' x N := by
  induction N with
  | zero => exact Or.inr rfl
  | succ N ih =>
    by_cases hl : t ≤ (run φ k t x N).trace.length
    · exact Or.inl (hl.trans (length_trace_le_step k t x _))
    · rcases ih with h | h
      · exact absurd h hl
      · right
        rw [run_succ, run_succ, ← h]
        simp only [step]
        rw [move_eq_move_of_lt (t := t) (t' := t') (Nat.lt_of_not_le hl)
          (lt_of_lt_of_le (Nat.lt_of_not_le hl) ht)]

/-- A run that uses up a budget of `t'` resamplings uses up any budget `t ≤ t'`. -/
theorem Exhausts.mono {k t t' : ℕ} {x : ℕ → Bool} (ht : t ≤ t') (h : Exhausts φ k t' x) :
    Exhausts φ k t x := by
  have hf : run φ k t x (fuel φ t') = final φ k t x :=
    run_eq_final (by simp only [fuel]; omega)
  rcases run_budget (k := k) ht x (fuel φ t') with h' | h'
  · rw [hf] at h'
    exact h'
  · rw [hf] at h'
    unfold Exhausts
    rw [h']
    exact ht.trans h

/-- A run that stops within its budget is not affected by a larger budget. -/
theorem final_eq_of_not_exhausts {k t t' : ℕ} {x : ℕ → Bool} (ht : t ≤ t')
    (h : ¬Exhausts φ k t x) : final φ k t' x = final φ k t x := by
  have hf : run φ k t x (fuel φ t') = final φ k t x :=
    run_eq_final (by simp only [fuel]; omega)
  rcases run_budget (k := k) ht x (fuel φ t') with h' | h'
  · rw [hf] at h'
    exact absurd h' h
  · rw [hf] at h'
    exact h'.symm

/-! ### Prefix dependence -/

theorem resample_congr_block {k t : ℕ} (hφ : φ.IsExactDistinct k) {x y : ℕ → Bool}
    (hxy : ∀ i < n + t * k, x i = y i) (c : Fin φ.length) {j : ℕ} (hj : j < t)
    (σ : Fin n → Bool) : resample φ[c] x (n + j * k) σ = resample φ[c] y (n + j * k) σ := by
  refine resample_congr (fun i hi => hxy _ ?_) σ
  rw [List.length_map, (hφ _ (getElem_mem_fin c)).1] at hi
  have := Nat.mul_le_mul_right k (Nat.succ_le_of_lt hj)
  rw [Nat.succ_mul] at this
  omega

/-- A run with a budget of `t` resamplings reads only the first `n + t k` tape bits. -/
theorem run_congr {k : ℕ} (hφ : φ.IsExactDistinct k) {t : ℕ} {x y : ℕ → Bool}
    (hxy : ∀ i < n + t * k, x i = y i) (N : ℕ) : run φ k t x N = run φ k t y N := by
  induction N with
  | zero =>
    have h : (fun v : Fin n => x v) = fun v : Fin n => y v :=
      funext fun v => hxy _ (lt_of_lt_of_le v.2 (Nat.le_add_right _ _))
    simp only [run, init, h]
  | succ N ih =>
    rw [run_succ, run_succ, ← ih]
    simp only [step]
    rcases move_cases t (run φ k t x N) with ⟨hm, -⟩ | ⟨c, hm, -, -, -, ht⟩ |
      ⟨e, st, d, hm, -, -, -, ht⟩ | ⟨e, st, hm, -⟩ | ⟨hm, -⟩
    · simp only [hm, apply]
    · simp only [hm, apply, resample_congr_block hφ hxy c ht]
    · simp only [hm, apply, resample_congr_block hφ hxy d ht]
    · simp only [hm, apply]
    · simp only [hm, apply]

/-- Whether a run uses up its budget of `t` resamplings depends only on the first `n + t k` tape
bits. -/
theorem exhausts_congr {k : ℕ} (hφ : φ.IsExactDistinct k) {t : ℕ} {x y : ℕ → Bool}
    (hxy : ∀ i < n + t * k, x i = y i) : Exhausts φ k t x ↔ Exhausts φ k t y := by
  unfold Exhausts final
  rw [run_congr hφ hxy]

end Moser

end Cslib.Logic.PL
