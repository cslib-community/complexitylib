/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.STCON
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Nondeterministic
import Complexity.Foundations.Relation.RelatesWithinSteps

/-!
# Directed connectivity by a nondeterministic search in logarithmic space

A nondeterministic counter program (`Cslib.Complexity.STCON.searchProgram`) decides directed
`s`–`t` connectivity on the adjacency-matrix encoding `Cslib.Complexity.encSTCON` in logarithmic
space [Sipser, Example 8.19][Sipser2013]. It counts the unary header to learn `n`, `s` and `t`,
then walks from `s`: at each step it accepts if the current vertex is `t`, rejects once it has
taken `n` steps, and otherwise guesses the next vertex `v` by incrementing a counter from `0` as
long as its choices say so, rejecting when the counter reaches `n`, and moves to `v` when the
matrix has an arc from the current vertex to `v`. It stores only the header values, the current
vertex, the number of steps taken and the counter, all at most the length of the input, and every
branch halts.

The proof uses an invariant of every branch (`Cslib.Complexity.STCON.Search.Inv`): it records the
values of the registers at every label, and in particular that the current vertex is reachable
from `s`, which gives soundness at the accepting label. Every step decreases a rank
(`Cslib.Complexity.STCON.Search.rank`), which bounds the length of every branch. Conversely, a
shortest path from `s` to `t`, which has fewer than `n` arcs, is followed by an accepting branch.

## Main definitions

* `Cslib.Complexity.STCON.searchProgram`: the nondeterministic search.

## Main results

* `Cslib.Complexity.STCON.accepts_searchProgram_iff`: the search accepts exactly the instances
  in `STCON`.
* `Cslib.Complexity.STCON.exists_decidesInLogSpace`: one nondeterministic machine decides
  `STCON` in logarithmic space, every branch halting.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Example 8.19][Sipser2013]
-/

@[expose] public section

namespace Cslib.Complexity

namespace STCON

open Turing CounterProgram Instr Expr

/-- **The nondeterministic search for a path.** Register `0` holds the choice, registers `1`,
`2` and `3` the header values `n`, `s` and `t`, register `4` the current vertex, register `5` the
number of steps taken and register `6` the guessed vertex. Label `17` accepts and label `18`
rejects. -/
def searchProgram : CounterProgram where
  code := [
    -- 0, 1: count the vertices
    read (reg 1) 1 2 18,
    assign 1 (add (reg 1) (const 1)) 0,
    -- 2, 3: count the source
    read (add (add (reg 1) (const 1)) (reg 2)) 3 4 18,
    assign 2 (add (reg 2) (const 1)) 2,
    -- 4, 5: count the target
    read (add (add (add (add (reg 1) (const 1)) (reg 2)) (const 1)) (reg 3)) 5 6 18,
    assign 3 (add (reg 3) (const 1)) 4,
    -- 6: start at the source
    assign 4 (reg 2) 7,
    -- 7, 8: accept at the target
    lt (reg 4) (reg 3) 9 8,
    lt (reg 3) (reg 4) 9 17,
    -- 9: reject after `n` steps
    lt (reg 5) (reg 1) 10 18,
    -- 10 to 13: guess the next vertex
    assign 6 (const 0) 11,
    lt (reg 0) (const 1) 14 12,
    assign 6 (add (reg 6) (const 1)) 13,
    lt (reg 6) (reg 1) 11 18,
    -- 14 to 16: follow an arc to the guessed vertex
    read (add (add (add (add (reg 1) (reg 2)) (reg 3)) (const 3))
      (add (mul (reg 4) (reg 1)) (reg 6))) 15 18 18,
    assign 4 (reg 6) 16,
    assign 5 (add (reg 5) (const 1)) 7,
    -- 17, 18
    accept,
    reject]
  registers := 7

namespace Search

/-- Compute a step of the search. -/
macro (name := searchStep) "search_step" : tactic => `(tactic| simp only [step_eq,
  CounterProgram.halted, CounterProgram.exec, CounterProgram.query, instr, searchProgram,
  Instr.exec, Instr.query, Instr.halts, eval_reg, eval_add, eval_const, eval_mul,
  List.getD_cons_succ, List.getD_cons_zero, Bool.false_eq_true, ↓reduceIte, withChoice,
  List.set_cons_zero, List.set_cons_succ, readLabel])

variable (I : STCONInstance)

/-- The vertex `cur` is reachable from the source. -/
def Reach (cur : ℕ) : Prop := ∃ h : cur < I.n, Relation.ReflTransGen I.Adj I.s ⟨cur, h⟩

/-- The registers of the main loop: the current vertex is reachable, at most `n` steps were taken
and the guessed vertex is a vertex. -/
def Loop (cur steps v : ℕ) : Prop := Reach I cur ∧ steps ≤ I.n ∧ v < I.n

/-- The values of the registers `1` to `6` at each label. -/
def Phase : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Prop
  | 0, n, s, t, cur, steps, v => n ≤ I.n ∧ s = 0 ∧ t = 0 ∧ cur = 0 ∧ steps = 0 ∧ v = 0
  | 1, n, s, t, cur, steps, v => n < I.n ∧ s = 0 ∧ t = 0 ∧ cur = 0 ∧ steps = 0 ∧ v = 0
  | 2, n, s, t, cur, steps, v => n = I.n ∧ s ≤ I.s ∧ t = 0 ∧ cur = 0 ∧ steps = 0 ∧ v = 0
  | 3, n, s, t, cur, steps, v => n = I.n ∧ s < I.s ∧ t = 0 ∧ cur = 0 ∧ steps = 0 ∧ v = 0
  | 4, n, s, t, cur, steps, v => n = I.n ∧ s = I.s ∧ t ≤ I.t ∧ cur = 0 ∧ steps = 0 ∧ v = 0
  | 5, n, s, t, cur, steps, v => n = I.n ∧ s = I.s ∧ t < I.t ∧ cur = 0 ∧ steps = 0 ∧ v = 0
  | 6, n, s, t, cur, steps, v => n = I.n ∧ s = I.s ∧ t = I.t ∧ cur = 0 ∧ steps = 0 ∧ v = 0
  | 7, n, s, t, cur, steps, v => n = I.n ∧ s = I.s ∧ t = I.t ∧ Loop I cur steps v
  | 8, n, s, t, cur, steps, v => n = I.n ∧ s = I.s ∧ t = I.t ∧ Loop I cur steps v ∧ t ≤ cur
  | 9, n, s, t, cur, steps, v => n = I.n ∧ s = I.s ∧ t = I.t ∧ Loop I cur steps v
  | 10, n, s, t, cur, steps, v =>
    n = I.n ∧ s = I.s ∧ t = I.t ∧ Loop I cur steps v ∧ steps < I.n
  | 11, n, s, t, cur, steps, v =>
    n = I.n ∧ s = I.s ∧ t = I.t ∧ Loop I cur steps v ∧ steps < I.n
  | 12, n, s, t, cur, steps, v =>
    n = I.n ∧ s = I.s ∧ t = I.t ∧ Loop I cur steps v ∧ steps < I.n
  | 13, n, s, t, cur, steps, v =>
    n = I.n ∧ s = I.s ∧ t = I.t ∧ Reach I cur ∧ steps < I.n ∧ v ≤ I.n
  | 14, n, s, t, cur, steps, v =>
    n = I.n ∧ s = I.s ∧ t = I.t ∧ Loop I cur steps v ∧ steps < I.n
  | 15, n, s, t, cur, steps, v =>
    n = I.n ∧ s = I.s ∧ t = I.t ∧ Loop I cur steps v ∧ steps < I.n ∧
      ∃ (hc : cur < I.n) (hv : v < I.n), I.Adj ⟨cur, hc⟩ ⟨v, hv⟩
  | 16, n, s, t, cur, steps, v =>
    n = I.n ∧ s = I.s ∧ t = I.t ∧ Loop I cur steps v ∧ steps < I.n
  | 17, _, _, _, _, _, _ => I ∈ STCON
  | 18, _, _, _, _, _, _ => True
  | _, _, _, _, _, _, _ => False

/-- The registers `1` to `6` stay below the header values. -/
def Bounded (n s t cur steps v : ℕ) : Prop :=
  n ≤ I.n ∧ s ≤ I.s ∧ t ≤ I.t ∧ cur ≤ I.n ∧ steps ≤ I.n ∧ v ≤ I.n

/-- **The invariant of every branch.** -/
def Inv (cfg : Config) : Prop :=
  ∃ c n s t cur steps v, cfg.2 = [c, n, s, t, cur, steps, v] ∧ c ≤ 1 ∧
    Bounded I n s t cur steps v ∧ Phase I cfg.1 n s t cur steps v

private theorem inv_mk {l c n s t cur steps v : ℕ} :
    Inv I (l, [c, n, s, t, cur, steps, v]) ↔
      c ≤ 1 ∧ Bounded I n s t cur steps v ∧ Phase I l n s t cur steps v := by
  constructor
  · rintro ⟨c, n, s, t, cur, steps, v, h, hc⟩
    simp only [List.cons.injEq, and_true] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
    exact hc
  · intro h
    exact ⟨c, n, s, t, cur, steps, v, rfl, h⟩

/-- The total budget of the rank. -/
def budget : ℕ := 2 * I.n + 2 * I.s + 2 * I.t + 4 + (3 * I.n + 12) * (I.n + 1) + 1

/-- The progress made by a configuration: it increases with every step. -/
def progress (cfg : Config) : ℕ :=
  let base := 2 * I.n + 2 * I.s + 2 * I.t + 4
  let W := 3 * I.n + 12
  let steps := cfg.2.getD 5 0
  let v := cfg.2.getD 6 0
  match cfg.1 with
  | 0 => 2 * cfg.2.getD 1 0
  | 1 => 2 * cfg.2.getD 1 0 + 1
  | 2 => 2 * I.n + 1 + 2 * cfg.2.getD 2 0
  | 3 => 2 * I.n + 2 + 2 * cfg.2.getD 2 0
  | 4 => 2 * I.n + 2 * I.s + 2 + 2 * cfg.2.getD 3 0
  | 5 => 2 * I.n + 2 * I.s + 3 + 2 * cfg.2.getD 3 0
  | 6 => 2 * I.n + 2 * I.s + 2 * I.t + 3
  | 7 => base + W * steps
  | 8 => base + W * steps + 1
  | 9 => base + W * steps + 2
  | 10 => base + W * steps + 3
  | 11 => base + W * steps + 4 + 3 * v
  | 12 => base + W * steps + 5 + 3 * v
  | 13 => base + W * steps + 3 + 3 * v
  | 14 => base + W * steps + 3 * I.n + 8
  | 15 => base + W * steps + 3 * I.n + 9
  | 16 => base + W * steps + 3 * I.n + 10
  | _ => base + W * (I.n + 1)

/-- **The rank**: the budget left. -/
def rank (cfg : Config) : ℕ := budget I - progress I cfg

/-! ### Every branch -/

private theorem reach_source : Reach I I.s := ⟨I.s.isLt, .refl⟩

/-- A step that makes progress, from a configuration within the budget, decreases the rank. -/
private theorem rank_lt {cfg cfg' : Config} (h : progress I cfg < progress I cfg')
    (hb : progress I cfg < budget I) : rank I cfg' < rank I cfg := by
  unfold rank
  omega

/-- Finish a case of `inv_step`, with additional facts for `simp`. -/
macro (name := searchFinish) "search_finish" " [" ts:term,* "]" : tactic => `(tactic| (
  refine ⟨?_, rank_lt _ ?_ ?_⟩ <;>
  simp only [inv_mk, Bounded, Phase, Loop, progress, budget, List.getD_cons_succ,
    List.getD_cons_zero, List.set_cons_succ, List.set_cons_zero, true_and, and_true, and_self,
    $[$ts:term],*] <;>
  omega))

/-- A step in the `n` and `s` header-counting phase (`l < 4`) preserves the invariant and decreases
the rank. -/
private theorem inv_step_header_n_s {l c n s t cur steps v : ℕ} (hl : l < 4)
    (hB : Bounded I n s t cur steps v) (hP : Phase I l n s t cur steps v) (b : Bool) :
    Inv I (withChoice (searchProgram.step I.encode (l, [c, n, s, t, cur, steps, v])) b) ∧
      rank I (withChoice (searchProgram.step I.encode (l, [c, n, s, t, cur, steps, v])) b) <
        rank I (l, [c, n, s, t, cur, steps, v]) := by
  obtain ⟨hn, hs, ht, hcur, hsteps, hv⟩ := hB
  have hsI := I.s.isLt
  have hb : b.toNat ≤ 1 := Bool.toNat_le b
  interval_cases l <;> simp only [Phase] at hP
  case «0» =>
    obtain ⟨hnI, rfl, rfl, rfl, rfl, rfl⟩ := hP
    search_step
    rw [I.getElem?_encode_n hnI]
    by_cases h : n < I.n
    · simp only [h, decide_true]
      search_finish []
    · obtain rfl : n = I.n := by omega
      simp only [h, decide_false]
      search_finish []
  case «1» =>
    obtain ⟨hnI, rfl, rfl, rfl, rfl, rfl⟩ := hP
    search_step
    search_finish []
  case «2» =>
    obtain ⟨rfl, hsI', rfl, rfl, rfl, rfl⟩ := hP
    search_step
    rw [I.getElem?_encode_s hsI']
    by_cases h : s < I.s
    · simp only [h, decide_true]
      search_finish []
    · obtain rfl : s = I.s := by omega
      simp only [h, decide_false]
      search_finish []
  case «3» =>
    obtain ⟨rfl, hsI', rfl, rfl, rfl, rfl⟩ := hP
    search_step
    search_finish []

/-- A step in the `t` header-counting and loop-entry phase (`4 ≤ l < 7`) preserves the invariant and
decreases the rank. -/
private theorem inv_step_header_t {l c n s t cur steps v : ℕ} (hl4 : 4 ≤ l) (hl7 : l < 7)
    (hB : Bounded I n s t cur steps v) (hP : Phase I l n s t cur steps v) (b : Bool) :
    Inv I (withChoice (searchProgram.step I.encode (l, [c, n, s, t, cur, steps, v])) b) ∧
      rank I (withChoice (searchProgram.step I.encode (l, [c, n, s, t, cur, steps, v])) b) <
        rank I (l, [c, n, s, t, cur, steps, v]) := by
  obtain ⟨hn, hs, ht, hcur, hsteps, hv⟩ := hB
  have hsI := I.s.isLt
  have htI := I.t.isLt
  have hb : b.toNat ≤ 1 := Bool.toNat_le b
  interval_cases l <;> simp only [Phase] at hP
  case «4» =>
    obtain ⟨rfl, rfl, htI', rfl, rfl, rfl⟩ := hP
    search_step
    rw [I.getElem?_encode_t htI']
    by_cases h : t < I.t
    · simp only [h, decide_true]
      search_finish []
    · obtain rfl : t = I.t := by omega
      simp only [h, decide_false]
      search_finish []
  case «5» =>
    obtain ⟨rfl, rfl, htI', rfl, rfl, rfl⟩ := hP
    search_step
    search_finish []
  case «6» =>
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hP
    search_step
    refine ⟨(inv_mk I).2 ⟨hb, by simp only [Bounded]; omega, rfl, rfl, rfl, reach_source I,
      by omega, by omega⟩, rank_lt _ ?_ ?_⟩ <;>
      simp only [progress, budget, List.getD_cons_succ, List.getD_cons_zero] <;> omega

/-- A step in the target/step-bound check (`7 ≤ l < 11`) preserves the invariant and decreases the
rank. -/
private theorem inv_step_check {l c n s t cur steps v : ℕ} (hl7 : 7 ≤ l) (hl11 : l < 11)
    (hB : Bounded I n s t cur steps v) (hP : Phase I l n s t cur steps v) (b : Bool) :
    Inv I (withChoice (searchProgram.step I.encode (l, [c, n, s, t, cur, steps, v])) b) ∧
      rank I (withChoice (searchProgram.step I.encode (l, [c, n, s, t, cur, steps, v])) b) <
        rank I (l, [c, n, s, t, cur, steps, v]) := by
  obtain ⟨hn, hs, ht, hcur, hsteps, hv⟩ := hB
  have htI := I.t.isLt
  have hb : b.toNat ≤ 1 := Bool.toNat_le b
  have hW2 : (3 * I.n + 12) * steps ≤ (3 * I.n + 12) * I.n := Nat.mul_le_mul_left _ hsteps
  have hW3 : (3 * I.n + 12) * (I.n + 1) = (3 * I.n + 12) * I.n + (3 * I.n + 12) := by ring
  interval_cases l <;> simp only [Phase] at hP
  case «7» =>
    obtain ⟨rfl, rfl, rfl, hR, hst, hvn⟩ := hP
    search_step
    by_cases h : cur < I.t
    · simp only [h, ↓reduceIte]
      search_finish [hR]
    · simp only [h, ↓reduceIte]
      search_finish [hR]
  case «8» =>
    obtain ⟨rfl, rfl, rfl, ⟨hR, hst, hvn⟩, hle⟩ := hP
    search_step
    by_cases h : (I.t : ℕ) < cur
    · simp only [h, ↓reduceIte]
      search_finish [hR]
    · have hmem : I ∈ STCON := by
        obtain ⟨hlt, hr⟩ := hR
        have hcur_eq : (⟨cur, hlt⟩ : Fin I.n) = I.t := Fin.ext (show cur = I.t by omega)
        rwa [hcur_eq] at hr
      simp only [h, ↓reduceIte]
      search_finish [hmem]
  case «9» =>
    obtain ⟨rfl, rfl, rfl, hR, hst, hvn⟩ := hP
    search_step
    by_cases h : steps < I.n
    · simp only [h, ↓reduceIte]
      search_finish [hR]
    · simp only [h, ↓reduceIte]
      search_finish []
  case «10» =>
    obtain ⟨rfl, rfl, rfl, ⟨hR, hst, hvn⟩, hlt⟩ := hP
    search_step
    search_finish [hR]

/-- A step in the vertex-guessing phase (`11 ≤ l < 14`) preserves the invariant and decreases the
rank. -/
private theorem inv_step_guess {l c n s t cur steps v : ℕ} (hl11 : 11 ≤ l) (hl14 : l < 14)
    (hB : Bounded I n s t cur steps v) (hP : Phase I l n s t cur steps v) (b : Bool) :
    Inv I (withChoice (searchProgram.step I.encode (l, [c, n, s, t, cur, steps, v])) b) ∧
      rank I (withChoice (searchProgram.step I.encode (l, [c, n, s, t, cur, steps, v])) b) <
        rank I (l, [c, n, s, t, cur, steps, v]) := by
  obtain ⟨hn, hs, ht, hcur, hsteps, hv⟩ := hB
  have hb : b.toNat ≤ 1 := Bool.toNat_le b
  have hW2 : (3 * I.n + 12) * steps ≤ (3 * I.n + 12) * I.n := Nat.mul_le_mul_left _ hsteps
  have hW3 : (3 * I.n + 12) * (I.n + 1) = (3 * I.n + 12) * I.n + (3 * I.n + 12) := by ring
  interval_cases l <;> simp only [Phase] at hP
  case «11» =>
    obtain ⟨rfl, rfl, rfl, ⟨hR, hst, hvn⟩, hlt⟩ := hP
    search_step
    by_cases h : c < 1
    · simp only [h, ↓reduceIte]
      search_finish [hR]
    · simp only [h, ↓reduceIte]
      search_finish [hR]
  case «12» =>
    obtain ⟨rfl, rfl, rfl, ⟨hR, hst, hvn⟩, hlt⟩ := hP
    search_step
    search_finish [hR]
  case «13» =>
    obtain ⟨rfl, rfl, rfl, hR, hlt, hvn⟩ := hP
    search_step
    by_cases h : v < I.n
    · simp only [h, ↓reduceIte]
      search_finish [hR]
    · simp only [h, ↓reduceIte]
      search_finish []

/-- A step in the arc-following phase (`14 ≤ l ≤ 16`) preserves the invariant and decreases the
rank. -/
private theorem inv_step_edge {l c n s t cur steps v : ℕ} (hl14 : 14 ≤ l) (hl16 : l ≤ 16)
    (hB : Bounded I n s t cur steps v) (hP : Phase I l n s t cur steps v) (b : Bool) :
    Inv I (withChoice (searchProgram.step I.encode (l, [c, n, s, t, cur, steps, v])) b) ∧
      rank I (withChoice (searchProgram.step I.encode (l, [c, n, s, t, cur, steps, v])) b) <
        rank I (l, [c, n, s, t, cur, steps, v]) := by
  obtain ⟨hn, hs, ht, hcur, hsteps, hv⟩ := hB
  have hb : b.toNat ≤ 1 := Bool.toNat_le b
  have hW1 : (3 * I.n + 12) * (steps + 1) = (3 * I.n + 12) * steps + (3 * I.n + 12) := by ring
  have hW2 : (3 * I.n + 12) * steps ≤ (3 * I.n + 12) * I.n := Nat.mul_le_mul_left _ hsteps
  have hW3 : (3 * I.n + 12) * (I.n + 1) = (3 * I.n + 12) * I.n + (3 * I.n + 12) := by ring
  interval_cases l <;> simp only [Phase] at hP
  case «14» =>
    obtain ⟨rfl, rfl, rfl, ⟨hR, hst, hvn⟩, hlt⟩ := hP
    search_step
    rw [I.getElem?_encode_matrix hR.1 hvn]
    cases hadj : I.adj ⟨cur, hR.1⟩ ⟨v, hvn⟩
    · search_finish []
    · have hA : ∃ (hc : cur < I.n) (hv : v < I.n), I.Adj ⟨cur, hc⟩ ⟨v, hv⟩ := ⟨hR.1, hvn, hadj⟩
      search_finish [hR, hA]
  case «15» =>
    obtain ⟨rfl, rfl, rfl, ⟨⟨hc', hr⟩, hst, hvn⟩, hlt, hc'', hv'', hadj⟩ := hP
    search_step
    have hR' : Reach I v := ⟨hvn, hr.tail hadj⟩
    search_finish [hR']
  case «16» =>
    obtain ⟨rfl, rfl, rfl, ⟨hR, hst, hvn⟩, hlt⟩ := hP
    search_step
    search_finish [hR]

/-- **Every step from a running configuration preserves the invariant and decreases the rank.** -/
private theorem inv_step (cfg : Config) (hinv : Inv I cfg) (hrun : searchProgram.halted cfg = false)
    (b : Bool) :
    Inv I (withChoice (searchProgram.step I.encode cfg) b) ∧
      rank I (withChoice (searchProgram.step I.encode cfg) b) < rank I cfg := by
  obtain ⟨l, regs⟩ := cfg
  obtain ⟨c, n, s, t, cur, steps, v, rfl, _hc, hB, hP⟩ := hinv
  by_cases hl4 : l < 4
  · exact inv_step_header_n_s I hl4 hB hP b
  by_cases hl7 : l < 7
  · exact inv_step_header_t I (by omega) hl7 hB hP b
  by_cases hl11 : l < 11
  · exact inv_step_check I (by omega) hl11 hB hP b
  by_cases hl14 : l < 14
  · exact inv_step_guess I (by omega) hl14 hB hP b
  by_cases hl16 : l ≤ 16
  · exact inv_step_edge I (by omega) hl16 hB hP b
  have hl : l ≤ 18 := by
    by_contra h
    rcases l with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | l
    all_goals first | omega | exact hP
  interval_cases l <;> simp [CounterProgram.halted, instr, searchProgram, Instr.halts] at hrun

private theorem inv_init : Inv I searchProgram.init := by
  change Inv I (0, [0, 0, 0, 0, 0, 0, 0])
  exact (inv_mk I).2 ⟨by omega, by simp [Bounded], by simp [Phase]⟩

/-- **The invariant holds on every branch.** -/
theorem inv_run (choices : List Bool) :
    Inv I (searchProgram.toNondeterministicQueryMachine.run I.encode choices) :=
  forall_run_of_rank (Inv I) (inv_init I) (fun s hs hh b => (inv_step I s hs hh b).1) choices

/-- **Every branch halts.** -/
theorem haltsWithin :
    searchProgram.toNondeterministicQueryMachine.HaltsWithin I.encode
      (rank I searchProgram.init) :=
  haltsWithin_of_rank (Inv I) (rank I) (inv_init I) (fun s hs hh b => inv_step I s hs hh b)

/-- **The registers of every branch are at most the length of the input.** -/
private theorem le_length_of_mem_run (choices : List Bool) {r : ℕ}
    (hr : r ∈ (searchProgram.toNondeterministicQueryMachine.run I.encode choices).2) :
    r ≤ I.encode.length := by
  obtain ⟨c, n, s, t, cur, steps, v, h, hc, ⟨hn, hs, ht, hcur, hsteps, hv⟩, -⟩ := inv_run I choices
  have hlen := I.length_encode
  have := I.s.isLt
  have := I.t.isLt
  rw [h] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- **An accepting branch is sound**: the invariant at the accepting label says that `t` is
reachable from `s`. -/
theorem mem_of_accepts (h : searchProgram.toNondeterministicQueryMachine.Accepts I.encode) :
    I ∈ STCON := by
  obtain ⟨choices, hhalt, hacc⟩ := h
  have hi := instr_of_accepts hhalt hacc
  obtain ⟨c, n, s, t, cur, steps, v, -, -, -, hP⟩ := inv_run I choices
  generalize (searchProgram.toNondeterministicQueryMachine.run I.encode choices).1 = l at hi hP
  have hl : l ≤ 18 := by
    by_contra h
    rcases l with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | l
    all_goals first | omega | exact hP
  interval_cases l <;> first | exact hP | simp [instr, searchProgram] at hi

/-! ### An accepting branch -/

/-- Take one step of an accepting branch with the given choice. -/
macro (name := searchHead) "search_head" b:term : tactic => `(tactic| (
  refine Branches.head (by simp [CounterProgram.halted, instr, searchProgram, Instr.halts]) $b ?_;
  search_step))

private theorem branches_count_n : ∀ j ≤ I.n, ∀ c, Branches (P := searchProgram) (w := I.encode)
    (0, [c, j, 0, 0, 0, 0, 0]) (2, [0, I.n, 0, 0, 0, 0, 0]) := by
  intro j hj
  induction h : I.n - j generalizing j with
  | zero =>
    intro c
    have : j = I.n := by omega
    subst this
    search_head false
    rw [I.getElem?_encode_n le_rfl]
    simp only [lt_irrefl, decide_false]
    exact Branches.refl _
  | succ k ih =>
    intro c
    search_head false
    rw [I.getElem?_encode_n hj]
    simp only [show j < I.n by omega, decide_true]
    search_head false
    exact ih (j + 1) (by omega) (by omega) 0

private theorem branches_count_s : ∀ j ≤ (I.s : ℕ), ∀ c,
    Branches (P := searchProgram) (w := I.encode)
    (2, [c, I.n, j, 0, 0, 0, 0]) (4, [0, I.n, I.s, 0, 0, 0, 0]) := by
  intro j hj
  induction h : (I.s : ℕ) - j generalizing j with
  | zero =>
    intro c
    have : j = I.s := by omega
    subst this
    search_head false
    rw [I.getElem?_encode_s le_rfl]
    simp only [lt_irrefl, decide_false]
    exact Branches.refl _
  | succ k ih =>
    intro c
    search_head false
    rw [I.getElem?_encode_s hj]
    simp only [show j < I.s by omega, decide_true]
    search_head false
    exact ih (j + 1) (by omega) (by omega) 0

private theorem branches_count_t : ∀ j ≤ (I.t : ℕ), ∀ c,
    Branches (P := searchProgram) (w := I.encode)
    (4, [c, I.n, I.s, j, 0, 0, 0]) (6, [0, I.n, I.s, I.t, 0, 0, 0]) := by
  intro j hj
  induction h : (I.t : ℕ) - j generalizing j with
  | zero =>
    intro c
    have : j = I.t := by omega
    subst this
    search_head false
    rw [I.getElem?_encode_t le_rfl]
    simp only [lt_irrefl, decide_false]
    exact Branches.refl _
  | succ k ih =>
    intro c
    search_head false
    rw [I.getElem?_encode_t hj]
    simp only [show j < I.t by omega, decide_true]
    search_head false
    exact ih (j + 1) (by omega) (by omega) 0

/-- The header is read, and the walk starts at the source. -/
private theorem branches_header : Branches (P := searchProgram) (w := I.encode) searchProgram.init
    (7, [0, I.n, I.s, I.t, I.s, 0, 0]) := by
  refine (branches_count_n I 0 (Nat.zero_le _) 0).trans ?_
  refine (branches_count_s I 0 (Nat.zero_le _) 0).trans ?_
  refine (branches_count_t I 0 (Nat.zero_le _) 0).trans ?_
  search_head false
  exact Branches.refl _

/-- The guess of the vertex `target`: the choices are `true` until the counter reaches it. -/
private theorem branches_guess (cur steps target : ℕ) (ht : target < I.n) :
    ∀ j ≤ target, Branches (P := searchProgram) (w := I.encode)
      (11, [(decide (j < target)).toNat, I.n, I.s, I.t, cur, steps, j])
      (14, [0, I.n, I.s, I.t, cur, steps, target]) := by
  intro j hj
  induction h : target - j generalizing j with
  | zero =>
    have : j = target := by omega
    subst this
    search_head false
    simp only [lt_irrefl, decide_false, Bool.toNat_false, Nat.lt_one_iff, ↓reduceIte]
    exact Branches.refl _
  | succ k ih =>
    search_head false
    simp only [show j < target by omega, decide_true, Bool.toNat_true, lt_irrefl, ↓reduceIte]
    search_head false
    search_head (decide (j + 1 < target))
    simp only [show j + 1 < I.n by omega, ↓reduceIte]
    exact ih (j + 1) (by omega) (by omega)

/-- Accepting in two steps from label `7` when the current vertex is the target. -/
private theorem branches_at_target (steps c v : ℕ) :
    Branches (P := searchProgram) (w := I.encode)
      (7, [c, I.n, I.s, I.t, I.t, steps, v]) (17, [0, I.n, I.s, I.t, I.t, steps, v]) := by
  search_head false
  simp only [lt_irrefl, ↓reduceIte]
  search_head false
  simp only [lt_irrefl, ↓reduceIte]
  exact Branches.refl _

/-- Following one arc from `cur ≠ I.t` to `next` in one iteration of the main loop. -/
private theorem branches_step {cur steps c v next : ℕ} (hc : cur < I.n) (hnext : next < I.n)
    (hct : cur ≠ I.t) (hlt : steps < I.n) (hadj : I.Adj ⟨cur, hc⟩ ⟨next, hnext⟩) :
    Branches (P := searchProgram) (w := I.encode)
      (7, [c, I.n, I.s, I.t, cur, steps, v])
      (7, [0, I.n, I.s, I.t, next, steps + 1, next]) := by
  have hto9 : Branches (P := searchProgram) (w := I.encode)
      (7, [c, I.n, I.s, I.t, cur, steps, v]) (9, [0, I.n, I.s, I.t, cur, steps, v]) := by
    by_cases h : cur < I.t
    · search_head false
      simp only [h, ↓reduceIte]
      exact Branches.refl _
    · search_head false
      simp only [h, ↓reduceIte]
      search_head false
      simp only [show (I.t : ℕ) < cur by omega, ↓reduceIte]
      exact Branches.refl _
  refine hto9.trans ?_
  search_head false
  simp only [hlt, ↓reduceIte]
  search_head (decide (0 < next))
  refine (branches_guess I cur steps next hnext 0 (Nat.zero_le _)).trans ?_
  search_head false
  rw [I.getElem?_encode_matrix hc hnext]
  simp only [show I.adj ⟨cur, hc⟩ ⟨next, hnext⟩ = true from hadj]
  search_head false
  search_head false
  exact Branches.refl _

/-- **The walk along a path**: from a vertex with a path of `m` arcs to the target, after
`steps` steps with `steps + m < n`, some branch reaches the accepting halt. -/
private theorem branches_walk : ∀ (m cur steps c v : ℕ) (hc : cur < I.n),
    Relation.RelatesInSteps I.Adj ⟨cur, hc⟩ I.t m → steps + m < I.n →
      ∃ regs, Branches (P := searchProgram) (w := I.encode)
        (7, [c, I.n, I.s, I.t, cur, steps, v]) (17, regs) := by
  intro m
  induction m with
  | zero =>
    intro cur steps c v hc hpath _
    have hct : cur = I.t := congrArg Fin.val (Relation.RelatesInSteps.zero hpath)
    subst hct
    exact ⟨_, branches_at_target I steps c v⟩
  | succ m ih =>
    intro cur steps c v hc hpath hlt
    obtain ⟨⟨next, hnext⟩, hadj, hrest⟩ := hpath.succ'
    by_cases hct : cur = I.t
    · subst hct
      exact ⟨_, branches_at_target I steps c v⟩
    · obtain ⟨regs, hregs⟩ := ih next (steps + 1) 0 next hnext hrest (by omega)
      exact ⟨regs, (branches_step I hc hnext hct (by omega) hadj).trans hregs⟩

/-- **An accepting branch exists** when `t` is reachable from `s`: a shortest path has fewer
than `n` arcs. -/
theorem accepts_of_mem (h : I ∈ STCON) :
    searchProgram.toNondeterministicQueryMachine.Accepts I.encode := by
  have hn := I.n_pos
  obtain ⟨m, hm, hpath⟩ := (Relation.reflTransGen_iff_relatesWithinSteps
    (N := I.n - 1) (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)).mp h
  obtain ⟨regs, hregs⟩ := branches_walk I m I.s 0 0 0 I.s.isLt hpath (by omega)
  exact accepts_of_branches ((branches_header I).trans hregs) rfl

end Search

open Search in
/-- **The search accepts exactly the instances in `STCON`.** -/
theorem accepts_searchProgram_iff (I : STCONInstance) :
    searchProgram.toNondeterministicQueryMachine.Accepts I.encode ↔ I ∈ STCON :=
  ⟨mem_of_accepts I, accepts_of_mem I⟩

open Search in
/-- **Directed `s`–`t` connectivity in nondeterministic logarithmic space**
[Sipser, Example 8.19][Sipser2013]: one finite-state nondeterministic machine decides `STCON` on
the encoding `encSTCON` within space `c * (Nat.log2 n + 1)` on encodings of length `n`, every
branch halting. -/
theorem exists_decidesInLogSpace :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (ntm : Turing.MultiTapeNTM k Bool State) (c : ℕ),
      ntm.DecidesInSpace encSTCON STCON fun I => c * (Nat.log2 (encSTCON I).length + 1) :=
  searchProgram.exists_decidesInLogSpace (fun I => rank I searchProgram.init) 1
    (fun I => haltsWithin I)
    (fun I choices r hr => by
      have := le_length_of_mem_run I choices hr
      simp only [encSTCON_apply, pow_one]
      omega)
    (fun I => (accepts_searchProgram_iff I).symm)


end STCON

end Cslib.Complexity
