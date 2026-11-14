/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.StronglyConnected
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Nondeterministic
import CslibFrontier.Foundations.Data.Nat.Div
import CslibFrontier.Foundations.Relation.RelatesWithinSteps

/-!
# Strong connectivity by a nondeterministic search in logarithmic space

A nondeterministic counter program (`Cslib.Complexity.StronglyConnected.searchProgram`) decides
strong connectivity on the adjacency-matrix encoding `Cslib.Complexity.encDigraph` in logarithmic
space. It counts the unary header to learn `n`, then runs through the pairs of vertices
`(p / n, p % n)` for `p < n * n`: for each pair it walks from `p / n` as the search for directed
connectivity does (`Cslib.Complexity.STCON.searchProgram`), passing to the next pair once the
current vertex is `p % n`, rejecting once it has taken `n` steps, and guessing the next vertex `v`
by incrementing a counter from `0` as long as its choices say so. It accepts after the last pair.
It stores only `n`, the pair, the current vertex, the number of steps and the counter, all at most
the length of the input, and every branch halts.

The proof follows that of `Cslib.Complexity.STCON.searchProgram`, from which this module adapts
its step tactics, per-label invariant and termination argument: a private invariant of every
branch records the values of the registers at every label, in particular that every pair before
the current one is connected and that the current vertex is reachable from the first vertex of
the current pair, and a private rank decreases with every step. Conversely, for each
pair a shortest path, with fewer than `n` arcs, is followed.

## Main definitions

* `Cslib.Complexity.StronglyConnected.searchProgram`: the nondeterministic search.

## Main results

* `Cslib.Complexity.StronglyConnected.accepts_searchProgram_iff`: the search accepts exactly the
  strongly connected digraphs.
* `Cslib.Complexity.StronglyConnected.exists_decidesInLogSpace`: one nondeterministic machine
  decides `StronglyConnected` in logarithmic space, every branch halting.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Exercise 4.4][AroraBarak09]
* [M. Sipser, *Introduction to the Theory of Computation*, Example 8.19][Sipser2013]
-/

public section

namespace Cslib.Complexity

namespace StronglyConnected

open Turing CounterProgram Instr Expr

/-- **The nondeterministic search for paths between all pairs.** Register `0` holds the choice,
register `1` the number `n` of vertices, register `2` the index `p` of the pair
`(p / n, p % n)`, register `3` the current vertex, register `4` the number of steps taken and
register `5` the guessed vertex. Label `16` accepts and label `17` rejects. -/
def searchProgram : CounterProgram where
  code := [
    -- 0, 1: count the vertices
    read (reg 1) 1 2 17,
    assign 1 (add (reg 1) (const 1)) 0,
    -- 2: accept after the last pair
    lt (reg 2) (mul (reg 1) (reg 1)) 3 16,
    -- 3, 4: start at the first vertex of the pair
    assign 3 (div (reg 2) (reg 1)) 4,
    assign 4 (const 0) 5,
    -- 5, 6: pass to the next pair at its second vertex
    lt (reg 3) (mod (reg 2) (reg 1)) 7 6,
    lt (mod (reg 2) (reg 1)) (reg 3) 7 15,
    -- 7: reject after `n` steps
    lt (reg 4) (reg 1) 8 17,
    -- 8 to 11: guess the next vertex
    assign 5 (const 0) 9,
    lt (reg 0) (const 1) 12 10,
    assign 5 (add (reg 5) (const 1)) 11,
    lt (reg 5) (reg 1) 9 17,
    -- 12 to 14: follow an arc to the guessed vertex
    read (add (add (reg 1) (const 1)) (add (mul (reg 3) (reg 1)) (reg 5))) 13 17 17,
    assign 3 (reg 5) 14,
    assign 4 (add (reg 4) (const 1)) 5,
    -- 15: the next pair
    assign 2 (add (reg 2) (const 1)) 2,
    -- 16, 17
    accept,
    reject]
  registers := 6

namespace Search

/-- Compute a step of the search. -/
local macro (name := searchStep) "search_step" : tactic => `(tactic| simp only [step_eq,
  CounterProgram.halted, CounterProgram.exec, CounterProgram.query, instr, searchProgram,
  Instr.exec, Instr.query, Instr.halts, eval_reg, eval_add, eval_const, eval_mul, eval_div,
  eval_mod, List.getD_cons_succ, List.getD_cons_zero, Bool.false_eq_true, ↓reduceIte,
  withChoice, List.set_cons_zero, List.set_cons_succ, readLabel])

variable (G : DigraphInstance)

/-- The vertex `b` is reachable from the vertex `a`. -/
private def Reach (a b : ℕ) : Prop :=
  ∃ (ha : a < G.n) (hb : b < G.n), Relation.ReflTransGen G.Adj ⟨a, ha⟩ ⟨b, hb⟩

/-- Every pair before the pair of index `p` is connected. -/
private def Done (p : ℕ) : Prop := ∀ q < p, Reach G (q / G.n) (q % G.n)

/-- The pair of index `p` is a pair of vertices and every pair before it is connected. -/
private def Pair (p : ℕ) : Prop := p < G.n * G.n ∧ Done G p

/-- The registers of the walk: the current vertex is reachable from the first vertex of the pair
and at most `n` steps were taken. -/
private def Loop (p cur steps : ℕ) : Prop := Reach G (p / G.n) cur ∧ steps ≤ G.n

/-- The values of the registers `1` to `5` at each label. -/
private def Phase : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Prop
  | 0, n, p, cur, steps, v => n ≤ G.n ∧ p = 0 ∧ cur = 0 ∧ steps = 0 ∧ v = 0
  | 1, n, p, cur, steps, v => n < G.n ∧ p = 0 ∧ cur = 0 ∧ steps = 0 ∧ v = 0
  | 2, n, p, _, _, _ => n = G.n ∧ p ≤ G.n * G.n ∧ Done G p
  | 3, n, p, _, _, _ => n = G.n ∧ Pair G p
  | 4, n, p, cur, _, _ => n = G.n ∧ Pair G p ∧ cur = p / G.n
  | 5, n, p, cur, steps, _ => n = G.n ∧ Pair G p ∧ Loop G p cur steps
  | 6, n, p, cur, steps, _ => n = G.n ∧ Pair G p ∧ Loop G p cur steps ∧ p % G.n ≤ cur
  | 7, n, p, cur, steps, _ => n = G.n ∧ Pair G p ∧ Loop G p cur steps
  | 8, n, p, cur, steps, _ => n = G.n ∧ Pair G p ∧ Loop G p cur steps ∧ steps < G.n
  | 9, n, p, cur, steps, v =>
    n = G.n ∧ Pair G p ∧ Loop G p cur steps ∧ steps < G.n ∧ v < G.n
  | 10, n, p, cur, steps, v =>
    n = G.n ∧ Pair G p ∧ Loop G p cur steps ∧ steps < G.n ∧ v < G.n
  | 11, n, p, cur, steps, v =>
    n = G.n ∧ Pair G p ∧ Reach G (p / G.n) cur ∧ steps < G.n ∧ v ≤ G.n
  | 12, n, p, cur, steps, v =>
    n = G.n ∧ Pair G p ∧ Loop G p cur steps ∧ steps < G.n ∧ v < G.n
  | 13, n, p, cur, steps, v =>
    n = G.n ∧ Pair G p ∧ Loop G p cur steps ∧ steps < G.n ∧
      ∃ (hc : cur < G.n) (hv : v < G.n), G.Adj ⟨cur, hc⟩ ⟨v, hv⟩
  | 14, n, p, cur, steps, _ => n = G.n ∧ Pair G p ∧ Loop G p cur steps ∧ steps < G.n
  | 15, n, p, _, _, _ =>
    n = G.n ∧ p < G.n * G.n ∧ Done G (p + 1)
  | 16, _, _, _, _, _ => G ∈ StronglyConnected
  | 17, _, _, _, _, _ => True
  | _, _, _, _, _, _ => False

/-- The registers `1` to `5` stay below `n` or `n * n`. -/
private def Bounded (n p cur steps v : ℕ) : Prop :=
  n ≤ G.n ∧ p ≤ G.n * G.n ∧ cur ≤ G.n ∧ steps ≤ G.n ∧ v ≤ G.n

/-- **The invariant of every branch.** -/
private def Inv (cfg : Config) : Prop :=
  ∃ c n p cur steps v, cfg.2 = [c, n, p, cur, steps, v] ∧ c ≤ 1 ∧
    Bounded G n p cur steps v ∧ Phase G cfg.1 n p cur steps v

private theorem inv_mk {l c n p cur steps v : ℕ} :
    Inv G (l, [c, n, p, cur, steps, v]) ↔
      c ≤ 1 ∧ Bounded G n p cur steps v ∧ Phase G l n p cur steps v := by
  constructor
  · rintro ⟨c, n, p, cur, steps, v, h, hc⟩
    simp only [List.cons.injEq, and_true] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
    exact hc
  · intro h
    exact ⟨c, n, p, cur, steps, v, rfl, h⟩

/-- The weight of one step of a walk. -/
private def stepWeight : ℕ := 3 * G.n + 12

/-- The weight of one pair. -/
private def pairWeight : ℕ := stepWeight G * (G.n + 1) + 4

/-- The total budget of the rank. -/
private def budget : ℕ := 2 * G.n + 1 + pairWeight G * (G.n * G.n + 1) + 1

/-- The progress made by a configuration: it increases with every step. -/
private def progress (cfg : Config) : ℕ :=
  let base := 2 * G.n + 1 + pairWeight G * cfg.2.getD 2 0
  let walk := base + 3 + stepWeight G * cfg.2.getD 4 0
  let v := cfg.2.getD 5 0
  match cfg.1 with
  | 0 => 2 * cfg.2.getD 1 0
  | 1 => 2 * cfg.2.getD 1 0 + 1
  | 2 => base
  | 3 => base + 1
  | 4 => base + 2
  | 5 => walk
  | 6 => walk + 1
  | 7 => walk + 2
  | 8 => walk + 3
  | 9 => walk + 4 + 3 * v
  | 10 => walk + 5 + 3 * v
  | 11 => walk + 3 + 3 * v
  | 12 => walk + 3 * G.n + 8
  | 13 => walk + 3 * G.n + 9
  | 14 => walk + 3 * G.n + 10
  | 15 => base + 3 + stepWeight G * (G.n + 1)
  | _ => 2 * G.n + 1 + pairWeight G * (G.n * G.n + 1)

/-- **The rank**: the budget left. -/
private def rank (cfg : Config) : ℕ := budget G - progress G cfg

/-! ### Every branch -/

/-- A step that makes progress, from a configuration within the budget, decreases the rank. -/
private theorem rank_lt {cfg cfg' : Config} (h : progress G cfg < progress G cfg')
    (hb : progress G cfg < budget G) : rank G cfg' < rank G cfg := by
  unfold rank
  omega

/-- The arithmetic facts about the weights that every case uses. -/
private theorem weights {p steps : ℕ} (hp : p ≤ G.n * G.n) (hsteps : steps ≤ G.n) :
    stepWeight G = 3 * G.n + 12 ∧ pairWeight G = stepWeight G * (G.n + 1) + 4 ∧
      stepWeight G * (steps + 1) = stepWeight G * steps + stepWeight G ∧
      stepWeight G * steps ≤ stepWeight G * G.n ∧
      stepWeight G * (G.n + 1) = stepWeight G * G.n + stepWeight G ∧
      pairWeight G * (p + 1) = pairWeight G * p + pairWeight G ∧
      pairWeight G * p ≤ pairWeight G * (G.n * G.n) ∧
      pairWeight G * (G.n * G.n + 1) = pairWeight G * (G.n * G.n) + pairWeight G ∧
      (p < G.n * G.n → pairWeight G * (p + 1) ≤ pairWeight G * (G.n * G.n)) :=
  ⟨rfl, rfl, by ring, Nat.mul_le_mul_left _ hsteps, by ring, by ring, Nat.mul_le_mul_left _ hp,
    by ring, fun h => Nat.mul_le_mul_left _ h⟩

/-- Finish a case of `inv_step`, with additional facts for `simp`. -/
local macro (name := searchFinish) "search_finish" " [" ts:term,* "]" : tactic => `(tactic| (
  refine ⟨?_, rank_lt _ ?_ ?_⟩ <;>
  simp only [inv_mk, Bounded, Phase, Pair, Loop, progress, budget, List.getD_cons_succ,
    List.getD_cons_zero, List.set_cons_succ, List.set_cons_zero, true_and, and_true, and_self,
    $[$ts:term],*] <;>
  omega))

/-- A pair index below `n * n` has its first vertex below `n`. -/
private theorem div_lt {p : ℕ} (hp : p < G.n * G.n) : p / G.n < G.n :=
  Nat.div_lt_of_lt_mul hp

/-- A pair index below `n * n` has its second vertex below `n`. -/
private theorem mod_lt {p : ℕ} (hp : p < G.n * G.n) : p % G.n < G.n :=
  Nat.mod_lt _ (Nat.pos_of_ne_zero fun h0 => by simp [h0] at hp)

/-- A step reading the header or entering a pair (`l < 5`) preserves the invariant and decreases
the rank. -/
private theorem inv_step_header {l c n p cur steps v : ℕ} (hl : l < 5)
    (hB : Bounded G n p cur steps v) (hP : Phase G l n p cur steps v) (b : Bool) :
    Inv G (withChoice (searchProgram.step G.encode (l, [c, n, p, cur, steps, v])) b) ∧
      rank G (withChoice (searchProgram.step G.encode (l, [c, n, p, cur, steps, v])) b) <
        rank G (l, [c, n, p, cur, steps, v]) := by
  obtain ⟨hn, hp, hcur, hsteps, hv⟩ := hB
  obtain ⟨hW, hWp, hW1, hW2, hW3, hP1, hP2, hP3, hP4⟩ := weights G hp hsteps
  have hb : b.toNat ≤ 1 := Bool.toNat_le b
  interval_cases l <;> simp only [Phase] at hP
  case «0» =>
    obtain ⟨hnG, rfl, rfl, rfl, rfl⟩ := hP
    search_step
    rw [G.getElem?_encode_n hnG]
    by_cases h : n < G.n
    · simp only [h, decide_true]
      search_finish []
    · obtain rfl : n = G.n := by omega
      simp only [h, decide_false]
      have hdone : Done G 0 := fun _ h => absurd h (Nat.not_lt_zero _)
      search_finish [hdone]
  case «1» =>
    obtain ⟨hnG, rfl, rfl, rfl, rfl⟩ := hP
    search_step
    search_finish []
  case «2» =>
    obtain ⟨rfl, hpN, hdone⟩ := hP
    search_step
    by_cases h : p < G.n * G.n
    · simp only [h, ↓reduceIte]
      search_finish [hdone]
    · have hmem : G ∈ StronglyConnected := by
        intro a b
        obtain ⟨ha, hb', hr⟩ := hdone (a * G.n + b) (by
          have := Nat.mul_add_lt_mul_of_lt_of_lt a.isLt b.isLt
          rw [Nat.mul_comm] at this
          omega)
        have hdiv : (a * G.n + b) / G.n = a := Nat.mul_add_div_fin a b
        have hmod : (a * G.n + b) % G.n = b := by
          rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt b.isLt]
        convert hr <;> simp [hdiv, hmod]
      simp only [h, ↓reduceIte]
      search_finish [hmem]
  case «3» =>
    obtain ⟨rfl, hpN, hdone⟩ := hP
    search_step
    have := div_lt G hpN
    search_finish [hdone]
  case «4» =>
    obtain ⟨rfl, ⟨hpN, hdone⟩, rfl⟩ := hP
    search_step
    have := div_lt G hpN
    have hR : Reach G (p / G.n) (p / G.n) := ⟨div_lt G hpN, div_lt G hpN, .refl⟩
    search_finish [hdone, hR]

/-- A step in the walk checks (`5 ≤ l < 9`) preserves the invariant and decreases the rank. -/
private theorem inv_step_check {l c n p cur steps v : ℕ} (hl5 : 5 ≤ l) (hl9 : l < 9)
    (hB : Bounded G n p cur steps v) (hP : Phase G l n p cur steps v) (b : Bool) :
    Inv G (withChoice (searchProgram.step G.encode (l, [c, n, p, cur, steps, v])) b) ∧
      rank G (withChoice (searchProgram.step G.encode (l, [c, n, p, cur, steps, v])) b) <
        rank G (l, [c, n, p, cur, steps, v]) := by
  obtain ⟨hn, hp, hcur, hsteps, hv⟩ := hB
  obtain ⟨hW, hWp, hW1, hW2, hW3, hP1, hP2, hP3, hP4⟩ := weights G hp hsteps
  have hb : b.toNat ≤ 1 := Bool.toNat_le b
  interval_cases l <;> simp only [Phase] at hP
  case «5» =>
    obtain ⟨rfl, ⟨hpN, hdone⟩, hR, hst⟩ := hP
    have := hP4 hpN
    search_step
    by_cases h : cur < p % G.n
    · simp only [h, ↓reduceIte]
      search_finish [hdone, hR]
    · simp only [h, ↓reduceIte]
      search_finish [hdone, hR]
  case «6» =>
    obtain ⟨rfl, ⟨hpN, hdone⟩, ⟨hR, hst⟩, hle⟩ := hP
    have := hP4 hpN
    search_step
    by_cases h : p % G.n < cur
    · simp only [h, ↓reduceIte]
      search_finish [hdone, hR]
    · have hdone' : Done G (p + 1) := by
        intro q hq
        rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq | rfl
        · exact hdone q hq
        · rwa [show cur = q % G.n by omega] at hR
      simp only [h, ↓reduceIte]
      search_finish [hdone']
  case «7» =>
    obtain ⟨rfl, ⟨hpN, hdone⟩, hR, hst⟩ := hP
    have := hP4 hpN
    search_step
    by_cases h : steps < G.n
    · simp only [h, ↓reduceIte]
      search_finish [hdone, hR]
    · simp only [h, ↓reduceIte]
      search_finish []
  case «8» =>
    obtain ⟨rfl, ⟨hpN, hdone⟩, ⟨hR, hst⟩, hlt⟩ := hP
    have := hP4 hpN
    search_step
    search_finish [hdone, hR]

/-- A step in the guess of the next vertex and the walk along its arc (`9 ≤ l < 15`) preserves the
invariant and decreases the rank. -/
private theorem inv_step_guess {l c n p cur steps v : ℕ} (hl9 : 9 ≤ l) (hl15 : l < 15)
    (hB : Bounded G n p cur steps v) (hP : Phase G l n p cur steps v) (b : Bool) :
    Inv G (withChoice (searchProgram.step G.encode (l, [c, n, p, cur, steps, v])) b) ∧
      rank G (withChoice (searchProgram.step G.encode (l, [c, n, p, cur, steps, v])) b) <
        rank G (l, [c, n, p, cur, steps, v]) := by
  obtain ⟨hn, hp, hcur, hsteps, hv⟩ := hB
  obtain ⟨hW, hWp, hW1, hW2, hW3, hP1, hP2, hP3, hP4⟩ := weights G hp hsteps
  have hb : b.toNat ≤ 1 := Bool.toNat_le b
  interval_cases l <;> simp only [Phase] at hP
  case «9» =>
    obtain ⟨rfl, ⟨hpN, hdone⟩, ⟨hR, hst⟩, hlt, hvn⟩ := hP
    have := hP4 hpN
    search_step
    by_cases h : c < 1
    · simp only [h, ↓reduceIte]
      search_finish [hdone, hR]
    · simp only [h, ↓reduceIte]
      search_finish [hdone, hR]
  case «10» =>
    obtain ⟨rfl, ⟨hpN, hdone⟩, ⟨hR, hst⟩, hlt, hvn⟩ := hP
    have := hP4 hpN
    search_step
    search_finish [hdone, hR]
  case «11» =>
    obtain ⟨rfl, ⟨hpN, hdone⟩, hR, hlt, hvn⟩ := hP
    have := hP4 hpN
    search_step
    by_cases h : v < G.n
    · simp only [h, ↓reduceIte]
      search_finish [hdone, hR]
    · simp only [h, ↓reduceIte]
      search_finish []
  case «12» =>
    obtain ⟨rfl, ⟨hpN, hdone⟩, ⟨hR, hst⟩, hlt, hvn⟩ := hP
    have := hP4 hpN
    search_step
    rw [G.getElem?_encode_matrix hR.2.1 hvn]
    cases hadj : G.adj ⟨cur, hR.2.1⟩ ⟨v, hvn⟩
    · search_finish []
    · have hA : ∃ (hc : cur < G.n) (hv : v < G.n), G.Adj ⟨cur, hc⟩ ⟨v, hv⟩ :=
        ⟨hR.2.1, hvn, hadj⟩
      search_finish [hdone, hR, hA]
  case «13» =>
    obtain ⟨rfl, ⟨hpN, hdone⟩, ⟨⟨ha, hc', hr⟩, hst⟩, hlt, hc'', hv'', hadj⟩ := hP
    have := hP4 hpN
    search_step
    have hR' : Reach G (p / G.n) v := ⟨ha, hv'', hr.tail hadj⟩
    search_finish [hdone, hR']
  case «14» =>
    obtain ⟨rfl, ⟨hpN, hdone⟩, ⟨hR, hst⟩, hlt⟩ := hP
    have := hP4 hpN
    search_step
    search_finish [hdone, hR]

/-- A step to the next pair (`l = 15`) preserves the invariant and decreases the rank. -/
private theorem inv_step_next {c n p cur steps v : ℕ}
    (hB : Bounded G n p cur steps v) (hP : Phase G 15 n p cur steps v) (b : Bool) :
    Inv G (withChoice (searchProgram.step G.encode (15, [c, n, p, cur, steps, v])) b) ∧
      rank G (withChoice (searchProgram.step G.encode (15, [c, n, p, cur, steps, v])) b) <
        rank G (15, [c, n, p, cur, steps, v]) := by
  obtain ⟨hn, hp, hcur, hsteps, hv⟩ := hB
  obtain ⟨hW, hWp, hW1, hW2, hW3, hP1, hP2, hP3, hP4⟩ := weights G hp hsteps
  have hb : b.toNat ≤ 1 := Bool.toNat_le b
  obtain ⟨rfl, hpN, hdone⟩ := hP
  have := hP4 hpN
  search_step
  search_finish [hdone]

/-- **Every step from a running configuration preserves the invariant and decreases the rank.** -/
private theorem inv_step (cfg : Config) (hinv : Inv G cfg)
    (hrun : searchProgram.halted cfg = false) (b : Bool) :
    Inv G (withChoice (searchProgram.step G.encode cfg) b) ∧
      rank G (withChoice (searchProgram.step G.encode cfg) b) < rank G cfg := by
  obtain ⟨l, regs⟩ := cfg
  obtain ⟨c, n, p, cur, steps, v, rfl, _hc, hB, hP⟩ := hinv
  by_cases hl5 : l < 5
  · exact inv_step_header G hl5 hB hP b
  by_cases hl9 : l < 9
  · exact inv_step_check G (by omega) hl9 hB hP b
  by_cases hl15 : l < 15
  · exact inv_step_guess G (by omega) hl15 hB hP b
  by_cases hl : l = 15
  · subst hl
    exact inv_step_next G hB hP b
  have hl : l ≤ 17 := by
    by_contra h
    rcases l with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | l
    all_goals first | omega | exact hP
  interval_cases l <;> simp_all [CounterProgram.halted, instr, searchProgram, Instr.halts]

private theorem inv_init : Inv G searchProgram.init := by
  change Inv G (0, [0, 0, 0, 0, 0, 0])
  exact (inv_mk G).2 ⟨by omega, by simp [Bounded], by simp [Phase]⟩

/-- **The invariant holds on every branch.** -/
private theorem inv_run (choices : List Bool) :
    Inv G (searchProgram.toNondeterministicQueryMachine.run G.encode choices) :=
  forall_run_of_rank (Inv G) (inv_init G) (fun s hs hh b => (inv_step G s hs hh b).1) choices

/-- **Every branch halts.** -/
private theorem haltsWithin :
    searchProgram.toNondeterministicQueryMachine.HaltsWithin G.encode
      (rank G searchProgram.init) :=
  haltsWithin_of_rank (Inv G) (rank G) (inv_init G) (fun s hs hh b => inv_step G s hs hh b)

/-- **The registers of every branch are at most the length of the input.** -/
private theorem le_length_of_mem_run (choices : List Bool) {r : ℕ}
    (hr : r ∈ (searchProgram.toNondeterministicQueryMachine.run G.encode choices).2) :
    r ≤ G.encode.length := by
  obtain ⟨c, n, p, cur, steps, v, h, hc, ⟨hn, hp, hcur, hsteps, hv⟩, -⟩ := inv_run G choices
  have hlen := G.length_encode
  rw [h] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- **An accepting branch is sound**: the invariant at the accepting label says that the digraph
is strongly connected. -/
theorem mem_of_accepts (h : searchProgram.toNondeterministicQueryMachine.Accepts G.encode) :
    G ∈ StronglyConnected := by
  obtain ⟨choices, hhalt, hacc⟩ := h
  have hi := instr_of_accepts hhalt hacc
  obtain ⟨c, n, p, cur, steps, v, -, -, -, hP⟩ := inv_run G choices
  generalize (searchProgram.toNondeterministicQueryMachine.run G.encode choices).1 = l at hi hP
  have hl : l ≤ 17 := by
    by_contra h
    rcases l with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | l
    all_goals first | omega | exact hP
  interval_cases l <;> first | exact hP | simp [instr, searchProgram] at hi

/-! ### An accepting branch -/

/-- Take one step of an accepting branch with the given choice. -/
local macro (name := searchHead) "search_head" b:term : tactic => `(tactic| (
  refine Branches.head (by simp [CounterProgram.halted, instr, searchProgram, Instr.halts]) $b ?_;
  search_step))

private theorem branches_count_n : ∀ j ≤ G.n, ∀ c, Branches (P := searchProgram) (w := G.encode)
    (0, [c, j, 0, 0, 0, 0]) (2, [0, G.n, 0, 0, 0, 0]) := by
  intro j hj
  induction h : G.n - j generalizing j with
  | zero =>
    intro c
    have : j = G.n := by omega
    subst this
    search_head false
    rw [G.getElem?_encode_n le_rfl]
    simp only [lt_irrefl, decide_false]
    exact Branches.refl _
  | succ k ih =>
    intro c
    search_head false
    rw [G.getElem?_encode_n hj]
    simp only [show j < G.n by omega, decide_true]
    search_head false
    exact ih (j + 1) (by omega) (by omega) 0

/-- The guess of the vertex `target`: the choices are `true` until the counter reaches it. -/
private theorem branches_guess (p cur steps target : ℕ) (ht : target < G.n) :
    ∀ j ≤ target, Branches (P := searchProgram) (w := G.encode)
      (9, [(decide (j < target)).toNat, G.n, p, cur, steps, j])
      (12, [0, G.n, p, cur, steps, target]) := by
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
    simp only [show j + 1 < G.n by omega, ↓reduceIte]
    exact ih (j + 1) (by omega) (by omega)

/-- Passing to the next pair from label `5` when the current vertex is the second vertex of the
pair. -/
private theorem branches_at_target (p steps c v : ℕ) :
    Branches (P := searchProgram) (w := G.encode)
      (5, [c, G.n, p, p % G.n, steps, v]) (2, [0, G.n, p + 1, p % G.n, steps, v]) := by
  search_head false
  simp only [lt_irrefl, ↓reduceIte]
  search_head false
  simp only [lt_irrefl, ↓reduceIte]
  search_head false
  exact Branches.refl _

/-- Following one arc from `cur`, not the second vertex of the pair, to `next`. -/
private theorem branches_step {p cur steps c v next : ℕ} (hc : cur < G.n) (hnext : next < G.n)
    (hct : cur ≠ p % G.n) (hlt : steps < G.n) (hadj : G.Adj ⟨cur, hc⟩ ⟨next, hnext⟩) :
    Branches (P := searchProgram) (w := G.encode)
      (5, [c, G.n, p, cur, steps, v])
      (5, [0, G.n, p, next, steps + 1, next]) := by
  have hto7 : Branches (P := searchProgram) (w := G.encode)
      (5, [c, G.n, p, cur, steps, v]) (7, [0, G.n, p, cur, steps, v]) := by
    by_cases h : cur < p % G.n
    · search_head false
      simp only [h, ↓reduceIte]
      exact Branches.refl _
    · search_head false
      simp only [h, ↓reduceIte]
      search_head false
      simp only [show p % G.n < cur by omega, ↓reduceIte]
      exact Branches.refl _
  refine hto7.trans ?_
  search_head false
  simp only [hlt, ↓reduceIte]
  search_head (decide (0 < next))
  refine (branches_guess G p cur steps next hnext 0 (Nat.zero_le _)).trans ?_
  search_head false
  rw [G.getElem?_encode_matrix hc hnext]
  simp only [show G.adj ⟨cur, hc⟩ ⟨next, hnext⟩ = true from hadj]
  search_head false
  search_head false
  exact Branches.refl _

/-- **The walk along a path**: from a vertex with a path of `m` arcs to the second vertex of the
pair, after `steps` steps with `steps + m < n`, some branch passes to the next pair. -/
private theorem branches_walk {p : ℕ} (hp : p < G.n * G.n) : ∀ (m cur steps c v : ℕ)
    (hc : cur < G.n),
    Relation.RelatesInSteps G.Adj ⟨cur, hc⟩ ⟨p % G.n, mod_lt G hp⟩ m → steps + m < G.n →
      ∃ x y z, Branches (P := searchProgram) (w := G.encode)
        (5, [c, G.n, p, cur, steps, v]) (2, [0, G.n, p + 1, x, y, z]) := by
  intro m
  induction m with
  | zero =>
    intro cur steps c v hc hpath _
    have hct : cur = p % G.n := congrArg Fin.val (Relation.RelatesInSteps.zero hpath)
    subst hct
    exact ⟨_, _, _, branches_at_target G p steps c v⟩
  | succ m ih =>
    intro cur steps c v hc hpath hlt
    obtain ⟨⟨next, hnext⟩, hadj, hrest⟩ := hpath.succ'
    by_cases hct : cur = p % G.n
    · subst hct
      exact ⟨_, _, _, branches_at_target G p steps c v⟩
    · obtain ⟨x, y, z, hregs⟩ := ih next (steps + 1) 0 next hnext hrest (by omega)
      exact ⟨x, y, z, (branches_step G hc hnext hct (by omega) hadj).trans hregs⟩

/-- **One pair**: when the digraph is strongly connected, some branch passes from the pair `p` to
the pair `p + 1`. -/
private theorem branches_pair (h : G ∈ StronglyConnected) {p : ℕ} (hp : p < G.n * G.n)
    (c x y z : ℕ) : ∃ x' y' z', Branches (P := searchProgram) (w := G.encode)
      (2, [c, G.n, p, x, y, z]) (2, [0, G.n, p + 1, x', y', z']) := by
  have hn : 0 < G.n := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hp
  obtain ⟨m, hm, hpath⟩ := (Relation.reflTransGen_iff_relatesWithinSteps
    (N := G.n - 1) (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)).mp
    (h ⟨p / G.n, div_lt G hp⟩ ⟨p % G.n, mod_lt G hp⟩)
  obtain ⟨x', y', z', hwalk⟩ := branches_walk G hp m (p / G.n) 0 0 z (div_lt G hp) hpath (by omega)
  refine ⟨x', y', z', ?_⟩
  search_head false
  simp only [hp, ↓reduceIte]
  search_head false
  search_head false
  exact hwalk

/-- **An accepting branch exists** when the digraph is strongly connected. -/
theorem accepts_of_mem (h : G ∈ StronglyConnected) :
    searchProgram.toNondeterministicQueryMachine.Accepts G.encode := by
  have hpairs : ∀ p ≤ G.n * G.n, ∃ x y z, Branches (P := searchProgram) (w := G.encode)
      searchProgram.init (2, [0, G.n, p, x, y, z]) := by
    intro p
    induction p with
    | zero => exact fun _ => ⟨0, 0, 0, branches_count_n G 0 (Nat.zero_le _) 0⟩
    | succ p ih =>
      intro hp
      obtain ⟨x, y, z, hb⟩ := ih (by omega)
      obtain ⟨x', y', z', hb'⟩ := branches_pair G h (p := p) (by omega) 0 x y z
      exact ⟨x', y', z', hb.trans hb'⟩
  obtain ⟨x, y, z, hb⟩ := hpairs (G.n * G.n) le_rfl
  refine accepts_of_branches (hb.trans ?_) (s := (16, [0, G.n, G.n * G.n, x, y, z])) rfl
  search_head false
  simp only [lt_irrefl, ↓reduceIte]
  exact Branches.refl _

end Search

open Search in
/-- **The search accepts exactly the strongly connected digraphs.** -/
theorem accepts_searchProgram_iff (G : DigraphInstance) :
    searchProgram.toNondeterministicQueryMachine.Accepts G.encode ↔ G ∈ StronglyConnected :=
  ⟨mem_of_accepts G, accepts_of_mem G⟩

open Search in
/-- **Strong connectivity in nondeterministic logarithmic space**: one finite-state
nondeterministic machine decides `StronglyConnected` on the encoding `encDigraph` within space
`c * (Nat.log2 n + 1)` on encodings of length `n`, every branch halting. -/
theorem exists_decidesInLogSpace :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (ntm : Turing.MultiTapeNTM k Bool State) (c : ℕ),
      ntm.DecidesInSpace encDigraph StronglyConnected
        fun G => c * (Nat.log2 (encDigraph G).length + 1) :=
  searchProgram.exists_decidesInLogSpace (fun G => rank G searchProgram.init) 1
    (fun G => haltsWithin G)
    (fun G choices r hr => by
      have := le_length_of_mem_run G choices hr
      simp only [encDigraph_apply, pow_one]
      omega)
    (fun G => (accepts_searchProgram_iff G).symm)

end StronglyConnected

end Cslib.Complexity
