/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.TransitiveClosure.Loop
public import CslibFrontier.Algorithms.Reachability.InductiveCounting.Semantics
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Step

/-!
# Inductive counting for negated closures

A negated closure `¬ TC E s₀ z₀` over `k`-tuples of a universe of size `n` is certified
nondeterministically by the inductive counting of [Immerman1988] and [Szelepcsenyi1987]. Tuples
are coded by numbers below `n ^ k`: the code of `xs` is `(finFunctionFinEquiv xs : ℕ)`, which is
`Cslib.Logic.tupleIndex xs` by definition, spelled as in the closure loop and `codeE`. Round `i`
is the set of codes reachable from the code of `s₀`
within `i` steps (`Cslib.InductiveCounting.roundSet` for `codeEdge E`). Knowing the size of
round `i`, one test decides membership of a code `y` in round `i + 1`: it guesses the members of
round `i` in increasing order, certifies each by a walk of at most `i` steps, certifies for each
whether it reaches `y` in at most one step, and checks the number guessed. Counting the members
of round `i + 1` this way gives its size; the final test of the code of `z₀` at round `n ^ k`
decides reachability.

## Main definitions

* `Cslib.Logic.FO.Ordered.TCModelChecker.codeEdge`: the edge relation on codes.
* `Cslib.Logic.FO.Ordered.TCModelChecker.countRound`: round `i`, the codes reachable within `i`
  steps.
* `Cslib.Logic.FO.Ordered.TCModelChecker.TestPre`: the state before one test.

## Main results

* `Cslib.Logic.FO.Ordered.TCModelChecker.mem_roundSet_codeEdge_iff`: rounds are bounded
  reachability.
* `Cslib.Logic.FO.Ordered.TCModelChecker.test_sound`,
  `Cslib.Logic.FO.Ordered.TCModelChecker.test_complete`: one test.
* `Cslib.Logic.FO.Ordered.TCModelChecker.count_sound`,
  `Cslib.Logic.FO.Ordered.TCModelChecker.count_complete`: the counting block.

## References

* [N. Immerman, *Nondeterministic Space is Closed Under Complementation*][Immerman1988]
* [R. Szelepcsényi, *The Method of Forcing for Nondeterministic Automata*][Szelepcsenyi1987]
-/

public section

namespace Cslib.Logic.FO.Ordered.TCModelChecker

open Turing Turing.CounterProgram Turing.CounterProgram.Block Expr Vocabulary.ModelChecker
open Cslib.InductiveCounting (roundSet Graph prefixCount)
open ClosureKernel (digitE)

section Semantics

variable {n k : ℕ} {E : (Fin k → Fin n) → (Fin k → Fin n) → Prop}

open scoped Classical in
/-- The edge relation `E` on tuples, on their codes below `n ^ k`. -/
noncomputable def codeEdge (E : (Fin k → Fin n) → (Fin k → Fin n) → Prop) (c d : ℕ) :
    Bool :=
  if h : c < n ^ k ∧ d < n ^ k then
    decide (E (finFunctionFinEquiv.symm ⟨c, h.1⟩) (finFunctionFinEquiv.symm ⟨d, h.2⟩))
  else false

theorem codeEdge_code (xs ys : Fin k → Fin n) :
    codeEdge E (finFunctionFinEquiv xs) (finFunctionFinEquiv ys) = true ↔ E xs ys := by
  have h : (finFunctionFinEquiv xs : ℕ) < n ^ k ∧ (finFunctionFinEquiv ys : ℕ) < n ^ k :=
    ⟨(finFunctionFinEquiv xs).isLt, (finFunctionFinEquiv ys).isLt⟩
  simp only [codeEdge, h, and_self, ↓reduceDIte, Fin.eta, Equiv.symm_apply_apply,
    decide_eq_true_eq]

private theorem graph_iff {c d : ℕ} :
    Graph (n ^ k) (codeEdge E) c d ↔ ∃ (hc : c < n ^ k) (hd : d < n ^ k),
      E (finFunctionFinEquiv.symm ⟨c, hc⟩) (finFunctionFinEquiv.symm ⟨d, hd⟩) := by
  constructor
  · rintro ⟨hc, hd, he⟩
    refine ⟨hc, hd, ?_⟩
    simpa only [codeEdge, hc, hd, and_self, ↓reduceDIte, decide_eq_true_eq] using he
  · rintro ⟨hc, hd, he⟩
    exact ⟨hc, hd, by simpa only [codeEdge, hc, hd, and_self, ↓reduceDIte, decide_eq_true_eq]⟩

private theorem relatesInSteps_of_graph {xs : Fin k → Fin n} {m : ℕ} :
    ∀ {d : ℕ}, Relation.RelatesInSteps (Graph (n ^ k) (codeEdge E)) (finFunctionFinEquiv xs) d m →
      ∃ hd : d < n ^ k, Relation.RelatesInSteps E xs (finFunctionFinEquiv.symm ⟨d, hd⟩) m := by
  induction m with
  | zero =>
    intro d h
    obtain rfl := h.zero
    exact ⟨(finFunctionFinEquiv xs).isLt, by
      rw [Fin.eta, Equiv.symm_apply_apply]; exact .refl _⟩
  | succ m ih =>
    intro d h
    obtain ⟨c, hc, hcd⟩ := h.succ
    obtain ⟨hc', hsteps⟩ := ih hc
    obtain ⟨_, hd, he⟩ := graph_iff.mp hcd
    exact ⟨hd, .tail _ _ _ _ hsteps he⟩

/-- Walks between codes are walks between tuples. -/
theorem relatesWithinSteps_codeEdge_iff {xs ys : Fin k → Fin n} {m : ℕ} :
    Relation.RelatesWithinSteps (Graph (n ^ k) (codeEdge E)) (finFunctionFinEquiv xs)
      (finFunctionFinEquiv ys) m ↔ Relation.RelatesWithinSteps E xs ys m := by
  constructor
  · rintro ⟨m', hm', h⟩
    obtain ⟨_, h'⟩ := relatesInSteps_of_graph h
    rw [Fin.eta, Equiv.symm_apply_apply] at h'
    exact ⟨m', hm', h'⟩
  · rintro ⟨m', hm', h⟩
    refine ⟨m', hm', h.map (r' := Graph (n ^ k) (codeEdge E))
      (fun x => (finFunctionFinEquiv x : ℕ)) fun a b hab => ?_⟩
    exact ⟨(finFunctionFinEquiv a).isLt, (finFunctionFinEquiv b).isLt, (codeEdge_code a b).mpr hab⟩

/-- **Rounds are bounded reachability**: the code of `ys` is in round `i` exactly when `ys` is
reached from `xs` within `i` steps. -/
theorem mem_roundSet_codeEdge_iff {xs ys : Fin k → Fin n} {i : ℕ} :
    (finFunctionFinEquiv ys : ℕ) ∈ roundSet (n ^ k) (codeEdge E) (finFunctionFinEquiv xs) i ↔
      Relation.RelatesWithinSteps E xs ys i := by
  rw [InductiveCounting.mem_roundSet (finFunctionFinEquiv xs).isLt, relatesWithinSteps_codeEdge_iff]

/-- Round `n ^ k` is reachability. -/
theorem mem_roundSet_pow_iff {xs ys : Fin k → Fin n} :
    (finFunctionFinEquiv ys : ℕ) ∈ roundSet (n ^ k) (codeEdge E) (finFunctionFinEquiv xs) (n ^ k) ↔
      Relation.ReflTransGen E xs ys := by
  rw [mem_roundSet_codeEdge_iff]
  refine ⟨Relation.RelatesWithinSteps.reflTransGen, fun h => ?_⟩
  have hpos : 0 < n ^ k := Nat.pos_of_ne_zero fun h0 => by
    have := (finFunctionFinEquiv xs).isLt; omega
  have hcard : Nat.card (Fin k → Fin n) ≤ n ^ k - 1 + 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]; omega
  exact ((Relation.reflTransGen_iff_relatesWithinSteps hcard).mp h).mono (by omega)

variable (E) in
/-- Round `i` of inductive counting from `s₀`: the codes of the tuples reached from `s₀` within
`i` steps. -/
noncomputable def countRound (s₀ : Fin k → Fin n) (i : ℕ) : Finset ℕ :=
  roundSet (n ^ k) (codeEdge E) (finFunctionFinEquiv s₀) i

variable {s₀ : Fin k → Fin n}

private theorem mem_countRound_iff {ys : Fin k → Fin n} {i : ℕ} :
    (finFunctionFinEquiv ys : ℕ) ∈ countRound E s₀ i ↔ Relation.RelatesWithinSteps E s₀ ys i :=
  mem_roundSet_codeEdge_iff

private theorem mem_countRound_pow {ys : Fin k → Fin n} :
    (finFunctionFinEquiv ys : ℕ) ∈ countRound E s₀ (n ^ k) ↔ Relation.ReflTransGen E s₀ ys :=
  mem_roundSet_pow_iff

private theorem lt_of_mem_countRound {i c : ℕ} (h : c ∈ countRound E s₀ i) : c < n ^ k :=
  InductiveCounting.lt_of_mem_roundSet h

private theorem card_countRound_le {i : ℕ} : (countRound E s₀ i).card ≤ n ^ k :=
  InductiveCounting.roundSet_card_le

private theorem countRound_zero : countRound E s₀ 0 = {(finFunctionFinEquiv s₀ : ℕ)} :=
  InductiveCounting.roundSet_zero (finFunctionFinEquiv s₀).isLt

private theorem mem_countRound_succ {i y : ℕ} (hy : y < n ^ k) :
    y ∈ countRound E s₀ (i + 1) ↔ ∃ c ∈ countRound E s₀ i, c = y ∨ codeEdge E c y = true :=
  InductiveCounting.mem_roundSet_succ (finFunctionFinEquiv s₀).isLt hy

end Semantics


section Parts

variable {P : CounterProgram}

theorem countTestCode_parts {b base k : ℕ} {src : Fin k → Expr} {wb et ef : List Instr}
    {T R w₁ : ℕ} (hw : w₁ = b + 14 + 5 * k + wb.length)
    (hP : P.CodeAt b (countTestCode b base k src wb et ef T R)) :
    P.instr b = (Instr.assign (base + 6) (const 0) (b + 1)).shift ∧
    P.instr (b + 1) = (Instr.assign (base + 5) (const 0) (b + 2)).shift ∧
    P.instr (b + 2) = (Instr.assign (base + 4) (const 0) (b + 3)).shift ∧
    P.instr (b + 3) = (Instr.lt (reg (base + 4)) (pow (reg 0) k) (b + 4)
      (w₁ + 10 + et.length + ef.length)).shift ∧
    P.instr (b + 4) = (Instr.lt (const 0) (const 0) (b + 5) (b + 5)).shift ∧
    P.instr (b + 5) = .lt (reg 0) (const 1) (b + 6) (w₁ + 9 + et.length + ef.length) ∧
    P.CodeAt (b + 6) (assignChain (b + 6) (base + 7) k (digitE (base + 4))) ∧
    P.CodeAt (b + 6 + k) (assignChain (b + 6 + k) (base + 7 + k) k (digitE (base + 3))) ∧
    P.CodeAt (b + 6 + 2 * k) (tcCode (b + 6 + 2 * k) (base + 7 + 2 * k) k src
      (fun i => digitE (base + 4) i) (reg base) wb w₁ R) ∧
    P.instr w₁ = (Instr.assign (base + 5) (add (reg (base + 5)) (const 1)) (w₁ + 1)).shift ∧
    P.instr (w₁ + 1) = (Instr.lt (const 0) (const 0) (w₁ + 2) (w₁ + 2)).shift ∧
    P.instr (w₁ + 2) = .lt (reg 0) (const 1) (w₁ + 3) (w₁ + 8 + et.length) ∧
    P.instr (w₁ + 3) = (Instr.lt (const 0) (const 0) (w₁ + 4) (w₁ + 4)).shift ∧
    P.instr (w₁ + 4) = .lt (reg 0) (const 1) (w₁ + 5) (w₁ + 8) ∧
    P.instr (w₁ + 5) = (Instr.lt (const 0) (distE (base + 4) (base + 3)) R (w₁ + 6)).shift ∧
    P.instr (w₁ + 6) =
      (Instr.assign (base + 6) (const 1) (w₁ + 9 + et.length + ef.length)).shift ∧
    P.instr (w₁ + 7) =
      (Instr.assign (base + 6) (const 1) (w₁ + 9 + et.length + ef.length)).shift ∧
    P.CodeAt (w₁ + 8) et ∧
    P.instr (w₁ + 8 + et.length) =
      (Instr.lt (const 0) (distE (base + 4) (base + 3)) (w₁ + 9 + et.length) R).shift ∧
    P.CodeAt (w₁ + 9 + et.length) ef ∧
    P.instr (w₁ + 9 + et.length + ef.length) =
      (Instr.assign (base + 4) (add (reg (base + 4)) (const 1)) (b + 3)).shift ∧
    P.instr (w₁ + 10 + et.length + ef.length) =
      (Instr.lt (const 0) (distE (base + 5) (base + 1)) R T).shift := by
  subst hw
  simp only [countTestCode, codeAt_append, codeAt_cons, codeAt_nil, List.length_append,
    length_assignChain, List.length_cons, List.length_nil, length_tcCode] at hP
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2, h3, h4, h5, h6, -⟩, h7⟩, h8⟩, h9⟩, h10, h11, h12, h13, h14, h15, h16, h17,
    -⟩, h18⟩, h19, -⟩, h20⟩, h21, h22, -⟩ := hP
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact instr_of_eq h1 (by omega)
  · exact instr_of_eq h2 (by omega)
  · exact instr_of_eq h3 (by omega)
  · exact instr_of_eq h4 (by omega)
  · exact instr_of_eq h5 (by omega)
  · exact instr_of_eq h6 (by omega)
  · exact codeAt_of_eq h7 (by omega)
  · exact codeAt_of_eq h8 (by omega)
  · exact codeAt_of_eq h9 (by omega)
  · exact instr_of_eq h10 (by omega)
  · exact instr_of_eq h11 (by omega)
  · exact instr_of_eq h12 (by omega)
  · exact instr_of_eq h13 (by omega)
  · exact instr_of_eq h14 (by omega)
  · exact instr_of_eq h15 (by omega)
  · exact instr_of_eq h16 (by omega)
  · exact instr_of_eq h17 (by omega)
  · exact codeAt_of_eq h18 (by omega)
  · exact instr_of_eq h19 (by omega)
  · exact codeAt_of_eq h20 (by omega)
  · exact instr_of_eq h21 (by omega)
  · exact instr_of_eq h22 (by omega)

theorem countCode_parts {b base k : ℕ} {dst : Fin k → Expr} {t₁ t₂ : List Instr} {T R : ℕ}
    (hP : P.CodeAt b (countCode b base k dst t₁ t₂ T R)) :
    P.instr b = (Instr.assign base (const 0) (b + 1)).shift ∧
    P.instr (b + 1) = (Instr.assign (base + 1) (const 1) (b + 2)).shift ∧
    P.instr (b + 2) = (Instr.lt (add (reg base) (const 1)) (pow (reg 0) k) (b + 3)
      (b + t₁.length + 10)).shift ∧
    P.instr (b + 3) = (Instr.assign (base + 2) (const 0) (b + 4)).shift ∧
    P.instr (b + 4) = (Instr.assign (base + 3) (const 0) (b + 5)).shift ∧
    P.instr (b + 5) = (Instr.lt (reg (base + 3)) (pow (reg 0) k) (b + 6)
      (b + t₁.length + 8)).shift ∧
    P.CodeAt (b + 6) t₁ ∧
    P.instr (b + t₁.length + 6) =
      (Instr.assign (base + 2) (add (reg (base + 2)) (reg (base + 6))) (b + t₁.length + 7)).shift ∧
    P.instr (b + t₁.length + 7) =
      (Instr.assign (base + 3) (add (reg (base + 3)) (const 1)) (b + 5)).shift ∧
    P.instr (b + t₁.length + 8) =
      (Instr.assign (base + 1) (reg (base + 2)) (b + t₁.length + 9)).shift ∧
    P.instr (b + t₁.length + 9) = (Instr.assign base (add (reg base) (const 1)) (b + 2)).shift ∧
    P.instr (b + t₁.length + 10) =
      (Instr.assign (base + 3) (codeE k dst) (b + t₁.length + 11)).shift ∧
    P.CodeAt (b + t₁.length + 11) t₂ ∧
    P.instr (b + t₁.length + 11 + t₂.length) = (Instr.lt (reg (base + 6)) (const 1) T R).shift := by
  simp only [countCode, codeAt_append, codeAt_cons, codeAt_nil, List.length_append,
    List.length_cons, List.length_nil] at hP
  obtain ⟨⟨⟨⟨⟨h1, h2, h3, h4, h5, h6, -⟩, h7⟩, h8, h9, h10, h11, h12, -⟩, h13⟩, h14, -⟩ := hP
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact instr_of_eq h1 (by omega)
  · exact instr_of_eq h2 (by omega)
  · exact instr_of_eq h3 (by omega)
  · exact instr_of_eq h4 (by omega)
  · exact instr_of_eq h5 (by omega)
  · exact instr_of_eq h6 (by omega)
  · exact codeAt_of_eq h7 (by omega)
  · exact instr_of_eq h8 (by omega)
  · exact instr_of_eq h9 (by omega)
  · exact instr_of_eq h10 (by omega)
  · exact instr_of_eq h11 (by omega)
  · exact instr_of_eq h12 (by omega)
  · exact codeAt_of_eq h13 (by omega)
  · exact instr_of_eq h14 (by omega)

end Parts

section Helpers

variable {P : CounterProgram} {w : List Bool} {B : ℕ}

private theorem lt_eval_distE {x y : ℕ} {regs : List ℕ} :
    (const 0).eval regs < (distE x y).eval regs ↔ regs.getD x 0 ≠ regs.getD y 0 := by
  simp only [distE, eval_const, eval_add, eval_sub, eval_reg]
  omega

private theorem reaches_noop {l l' : ℕ} {regs : List ℕ}
    (hl : P.instr l = (Instr.lt (const 0) (const 0) l' l').shift) (hB : ∀ r ∈ regs, r ≤ B) :
    P.Reaches w (P.Oblivious B) (l, 0 :: regs) (l', 0 :: regs) := by
  cp_step

private theorem reaches_assign {l i next v : ℕ} {e : Expr} {regs : List ℕ}
    (hl : P.instr l = (Instr.assign i e next).shift) (he : e.eval regs = v) (hv : v ≤ B)
    (hB : ∀ r ∈ regs, r ≤ B) :
    P.Reaches w (P.Oblivious B) (l, 0 :: regs) (next, 0 :: regs.set i v) ∧
      ∀ r ∈ regs.set i v, r ≤ B := by
  exact ⟨by cp_step [he], List.forall_mem_set_of_forall_mem hB hv⟩

private theorem reaches_dist_eq {l yes no x y : ℕ} {regs : List ℕ}
    (hl : P.instr l = (Instr.lt (const 0) (distE x y) yes no).shift) (hB : ∀ r ∈ regs, r ≤ B)
    (h : regs.getD x 0 = regs.getD y 0) :
    P.Reaches w (P.Oblivious B) (l, 0 :: regs) (no, 0 :: regs) := by
  cp_step [↓mt lt_eval_distE.mp (not_not.mpr h)]

private theorem reaches_dist_ne {l yes no x y : ℕ} {regs : List ℕ}
    (hl : P.instr l = (Instr.lt (const 0) (distE x y) yes no).shift) (hB : ∀ r ∈ regs, r ≤ B)
    (h : regs.getD x 0 ≠ regs.getD y 0) :
    P.Reaches w (P.Oblivious B) (l, 0 :: regs) (yes, 0 :: regs) := by
  cp_step [↓lt_eval_distE.mpr h]

theorem eval_codeE {n k : ℕ} {z : Fin k → Expr} {zs : Fin k → Fin n} {regs : List ℕ}
    (h0 : regs.getD 0 0 = n) (hz : ∀ i, (z i).eval regs = zs i) :
    (codeE k z).eval regs = finFunctionFinEquiv zs := by
  rw [finFunctionFinEquiv_apply, Fin.sum_univ_def, codeE, eval_sum, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp_apply, eval_mul, eval_pow, eval_reg, h0, hz]

end Helpers

section Test

variable {P : CounterProgram} {w : List Bool} {B : ℕ} {Post : Config → Prop}
  {n k b base T R w₁ : ℕ} {src : Fin k → Expr} {wb et ef : List Instr}
  {E : (Fin k → Fin n) → (Fin k → Fin n) → Prop} {s₀ : Fin k → Fin n} {regs₀ : List ℕ}

variable (B base E s₀ regs₀) in
/-- The state before one test of inductive counting: registers below `base` as in `regs₀`, the
round `i < n ^ k` in register `base`, its size in `base + 1`, and the candidate `y < n ^ k` in
`base + 3`. -/
structure TestPre (i y : ℕ) (regs : List ℕ) : Prop where
  /-- The registers below `base` and the length are kept, and every register is bounded. -/
  kept : Kept B base regs₀ regs
  /-- The test's registers exist. -/
  le_length : base + 9 + 4 * k ≤ regs.length
  /-- The universe size is in register `0`. -/
  size : regs.getD 0 0 = n
  /-- The round is in register `base`. -/
  round : regs.getD base 0 = i
  /-- The round is below `n ^ k`. -/
  round_lt : i < n ^ k
  /-- The size of the round is in register `base + 1`. -/
  card : regs.getD (base + 1) 0 = (countRound E s₀ i).card
  /-- The candidate is in register `base + 3`. -/
  cand : regs.getD (base + 3) 0 = y
  /-- The candidate is below `n ^ k`. -/
  cand_lt : y < n ^ k

variable (B base E s₀) in
/-- The scan invariant of a test: the codes selected so far are members of round `i` below `m`,
counted in register `base + 5`, and register `base + 6` records whether one of them is `y` or
an edge to `y`. -/
private structure ScanInv (i y x m : ℕ) (Sel : Finset ℕ) (regsT regs : List ℕ) : Prop where
  /-- The registers below `base + 4` and the length are kept from the state `regsT` before the
  test, and every register is bounded. -/
  kept : Kept B (base + 4) regsT regs
  /-- The scanned code is in register `base + 4`. -/
  cur : regs.getD (base + 4) 0 = x
  /-- The codes selected are members of round `i`. -/
  subset : Sel ⊆ countRound E s₀ i
  /-- The codes selected are below `m`. -/
  lt_bound : ∀ c ∈ Sel, c < m
  /-- The number of codes selected is in register `base + 5`. -/
  count : regs.getD (base + 5) 0 = Sel.card
  /-- Register `base + 6` records whether a selected code is `y` or an edge to `y`. -/
  hit : regs.getD (base + 6) 0 = if ∃ c ∈ Sel, c = y ∨ codeEdge E c y = true then 1 else 0

/-- The state before a test persists through the scan, which writes only registers from
`base + 4`. -/
private theorem TestPre.of_kept {i y : ℕ} {regsT regs : List ℕ}
    (hpre : TestPre B base E s₀ regs₀ i y regsT) (hk : Kept B (base + 4) regsT regs) :
    TestPre B base E s₀ regs₀ i y regs where
  kept := hpre.kept.trans (hk.mono (by omega))
  le_length := by rw [hk.length_eq]; exact hpre.le_length
  size := by rw [hk.getD_eq 0 (by omega), hpre.size]
  round := by rw [hk.getD_eq _ (by omega), hpre.round]
  round_lt := hpre.round_lt
  card := by rw [hk.getD_eq _ (by omega), hpre.card]
  cand := by rw [hk.getD_eq _ (by omega), hpre.cand]
  cand_lt := hpre.cand_lt

private theorem scan_start (hw : w₁ = b + 14 + 5 * k + wb.length)
    (hP : P.CodeAt b (countTestCode b base k src wb et ef T R)) {i y : ℕ} {regs : List ℕ}
    (hlen : base + 7 ≤ regs.length) (hB : ∀ r ∈ regs, r ≤ B) :
    ∃ regs', P.Reaches w (P.Oblivious B) (b, 0 :: regs) (b + 3, 0 :: regs') ∧
      ScanInv B base E s₀ i y 0 0 ∅ regs regs' := by
  obtain ⟨h1, h2, h3, -⟩ := countTestCode_parts hw hP
  obtain ⟨hr₁, hB₁⟩ := reaches_assign (w := w) (v := 0) h1 rfl (Nat.zero_le B) hB
  obtain ⟨hr₂, hB₂⟩ := reaches_assign (w := w) (v := 0) h2 rfl (Nat.zero_le B) hB₁
  obtain ⟨hr₃, -⟩ := reaches_assign (w := w) (v := 0) h3 rfl (Nat.zero_le B) hB₂
  refine ⟨((regs.set (base + 6) 0).set (base + 5) 0).set (base + 4) 0, hr₁.trans (hr₂.trans hr₃),
    ((((Kept.refl hB).set_right (by omega) (Nat.zero_le B)).set_right (by omega)
      (Nat.zero_le B)).set_right le_rfl (Nat.zero_le B)), ?_, Finset.empty_subset _,
    fun c hc => absurd hc (Finset.notMem_empty c), ?_, ?_⟩
  · rw [List.getD_set_self (by simp only [List.length_set]; omega)]
  · rw [List.getD_set_ne (by omega), List.getD_set_self (by simp only [List.length_set]; omega),
      Finset.card_empty]
  · rw [List.getD_set_ne (by omega), List.getD_set_ne (by omega),
      List.getD_set_self (by omega)]
    simp

private theorem scan_enter (hw : w₁ = b + 14 + 5 * k + wb.length)
    (hP : P.CodeAt b (countTestCode b base k src wb et ef T R)) {x : ℕ} {regs : List ℕ}
    (hB : ∀ r ∈ regs, r ≤ B) (h0 : regs.getD 0 0 = n) (hX : regs.getD (base + 4) 0 = x)
    (hx : x < n ^ k) :
    P.Reaches w (P.Oblivious B) (b + 3, 0 :: regs) (b + 5, 0 :: regs) := by
  obtain ⟨-, -, -, h4, h5, -⟩ := countTestCode_parts hw hP
  cp_step [h0, hX, hx]
  cp_step

private theorem scan_leave (hw : w₁ = b + 14 + 5 * k + wb.length)
    (hP : P.CodeAt b (countTestCode b base k src wb et ef T R)) {x : ℕ} {regs : List ℕ}
    (hB : ∀ r ∈ regs, r ≤ B) (h0 : regs.getD 0 0 = n) (hX : regs.getD (base + 4) 0 = x)
    (hx : n ^ k ≤ x) :
    P.Reaches w (P.Oblivious B) (b + 3, 0 :: regs)
      (w₁ + 10 + et.length + ef.length, 0 :: regs) := by
  obtain ⟨-, -, -, h4, -⟩ := countTestCode_parts hw hP
  cp_step [h0, hX]

private theorem scan_post {i y x m : ℕ} {regsT regs : List ℕ} (hy : y < n ^ k)
    (hinv : ScanInv B base E s₀ i y x m (countRound E s₀ i) regsT regs) :
    Kept B (base + 4) regsT regs ∧
      regs.getD (base + 6) 0 = if y ∈ countRound E s₀ (i + 1) then 1 else 0 := by
  refine ⟨hinv.kept, ?_⟩
  rw [hinv.hit]
  by_cases h : y ∈ countRound E s₀ (i + 1)
  · rw [ite_eq_left h, ite_eq_left ((mem_countRound_succ hy).mp h)]
  · rw [ite_eq_right h, ite_eq_right fun h' => h ((mem_countRound_succ hy).mpr h')]

private theorem scan_check_sound (hw : w₁ = b + 14 + 5 * k + wb.length)
    (hP : P.CodeAt b (countTestCode b base k src wb et ef T R)) (hB1 : 1 ≤ B)
    (hR : (P.instr R).halts = true) (hPost : ∀ s : Config, s.1 = R → Post s)
    {i y x m : ℕ} {Sel : Finset ℕ} {regsT regs : List ℕ}
    (hpre : TestPre B base E s₀ regs₀ i y regsT)
    (hinv : ScanInv B base E s₀ i y x m Sel regsT regs) :
    Sound P w B Post (w₁ + 10 + et.length + ef.length) regs T (fun regs' =>
      Kept B (base + 4) regsT regs' ∧
        regs'.getD (base + 6) 0 = if y ∈ countRound E s₀ (i + 1) then 1 else 0) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h22⟩ :=
    countTestCode_parts hw hP
  have hC := (hpre.of_kept hinv.kept).card
  have hB := hinv.kept.bounded
  by_cases hS : Sel.card = (countRound E s₀ i).card
  · have hsel : Sel = countRound E s₀ i := Finset.eq_of_subset_of_card_le hinv.subset hS.ge
    subst hsel
    exact Sound.of_oblivious hB1 (reaches_dist_eq h22 hB (by rw [hinv.count, hC]))
      (Sound.exit (scan_post hpre.cand_lt hinv))
  · exact Sound.of_oblivious hB1 (reaches_dist_ne h22 hB (by rw [hinv.count, hC]; exact hS))
      (Sound.halt hB1 hR (fun _ => hPost _ rfl) hB)

private theorem scan_check_complete (hw : w₁ = b + 14 + 5 * k + wb.length)
    (hP : P.CodeAt b (countTestCode b base k src wb et ef T R))
    {i y x m : ℕ} {regsT regs : List ℕ} (hpre : TestPre B base E s₀ regs₀ i y regsT)
    (hinv : ScanInv B base E s₀ i y x m (countRound E s₀ i) regsT regs) :
    Complete P w (w₁ + 10 + et.length + ef.length) regs T (fun regs' =>
      Kept B (base + 4) regsT regs' ∧
        regs'.getD (base + 6) 0 = if y ∈ countRound E s₀ (i + 1) then 1 else 0) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h22⟩ :=
    countTestCode_parts hw hP
  exact Complete.of_oblivious (reaches_dist_eq h22 hinv.kept.bounded
    (by rw [hinv.count, (hpre.of_kept hinv.kept).card]))
    (Complete.refl (scan_post hpre.cand_lt hinv))

private theorem walk_dst {regs₂ : List ℕ} {x : ℕ} {xs : Fin k → Fin n}
    (h0 : regs₂.getD 0 0 = n) (hX : regs₂.getD (base + 4) 0 = x)
    (hxs : (finFunctionFinEquiv xs : ℕ) = x) :
    ∀ regs : List ℕ, (∀ j < base + 7 + 2 * k, regs.getD j 0 = regs₂.getD j 0) →
      ∀ j : Fin k, (digitE (base + 4) j).eval regs = xs j := by
  intro regs h j
  rw [ClosureKernel.eval_digitE ((h 0 (by omega)).trans h0) (finFunctionFinEquiv xs)
    (by rw [h _ (by omega), hX, hxs]), Equiv.symm_apply_apply]

private theorem walk_M {regs₂ : List ℕ} {i : ℕ} (hI : regs₂.getD base 0 = i) :
    ∀ regs : List ℕ, (∀ j < base + 7 + 2 * k, regs.getD j 0 = regs₂.getD j 0) →
      (reg base).eval regs = i := fun regs h => by
  rw [eval_reg, h base (by omega), hI]

private theorem walk_sound (hw : w₁ = b + 14 + 5 * k + wb.length)
    (hP : P.CodeAt b (countTestCode b base k src wb et ef T R)) (hB1 : 1 ≤ B) (hnB : n ≤ B)
    (hNB : n ^ k ≤ B) (hR : (P.instr R).halts = true) (hPost : ∀ s : Config, s.1 = R → Post s)
    (hsrc : ∀ regs, (∀ j < base, regs.getD j 0 = regs₀.getD j 0) → ∀ j, (src j).eval regs = s₀ j)
    (hwb : ∀ regsW us ws t regs₃, Kept B base regs₀ regsW →
      LoopMid n B (base + 7 + 2 * k) k regsW us ws t regs₃ →
      Sound P w B Post (b + 6 + 2 * k + 2 * k + 7) regs₃ (b + 6 + 2 * k + 2 * k + 7 + wb.length)
        (fun regs' => Kept B (base + 7 + 2 * k + 2 * k + 2) regs₃ regs' ∧ E us ws))
    {i x : ℕ} {xs : Fin k → Fin n} {regs₂ : List ℕ} (hk : Kept B base regs₀ regs₂)
    (hlen : base + 9 + 4 * k ≤ regs₂.length) (h0 : regs₂.getD 0 0 = n)
    (hI : regs₂.getD base 0 = i) (hiB : i ≤ B) (hX : regs₂.getD (base + 4) 0 = x)
    (hxs : (finFunctionFinEquiv xs : ℕ) = x) :
    Sound P w B Post (b + 6 + 2 * k) regs₂ w₁ (fun regs' =>
      Kept B (base + 7 + 2 * k) regs₂ regs' ∧ Relation.RelatesWithinSteps E s₀ xs i) := by
  obtain ⟨-, -, -, -, -, -, -, -, h9, -⟩ := countTestCode_parts hw hP
  have hsrc' : ∀ regs, (∀ j < base + 7 + 2 * k, regs.getD j 0 = regs₂.getD j 0) →
      ∀ j, (src j).eval regs = s₀ j := fun regs h =>
    hsrc regs fun j hj => (h j (by omega)).trans (hk.getD_eq j hj)
  obtain ⟨regsI, hrI, hinvI⟩ := loop_init (w := w) h9 (by omega) hnB hk.bounded hsrc'
  refine Sound.of_oblivious hB1 hrI ?_
  exact loop_sound h9 (by omega) hB1 hnB hNB hiB h0 hR hPost (walk_dst h0 hX hxs) (walk_M hI)
    (fun us ws t regs₃ hmid => hwb regs₂ us ws t regs₃ hk hmid) _ 0 s₀ regsI rfl
    (Nat.zero_le _) hinvI (Relation.RelatesWithinSteps.refl _)

private theorem walk_complete (hw : w₁ = b + 14 + 5 * k + wb.length)
    (hP : P.CodeAt b (countTestCode b base k src wb et ef T R)) (hnB : n ≤ B) (hNB : n ^ k ≤ B)
    (hsrc : ∀ regs, (∀ j < base, regs.getD j 0 = regs₀.getD j 0) → ∀ j, (src j).eval regs = s₀ j)
    (hwb : ∀ regsW us ws t regs₃, Kept B base regs₀ regsW →
      LoopMid n B (base + 7 + 2 * k) k regsW us ws t regs₃ → E us ws →
      Complete P w (b + 6 + 2 * k + 2 * k + 7) regs₃ (b + 6 + 2 * k + 2 * k + 7 + wb.length)
        (Kept B (base + 7 + 2 * k + 2 * k + 2) regs₃))
    {i x : ℕ} {xs : Fin k → Fin n} {regs₂ : List ℕ} (hk : Kept B base regs₀ regs₂)
    (hlen : base + 9 + 4 * k ≤ regs₂.length) (h0 : regs₂.getD 0 0 = n)
    (hI : regs₂.getD base 0 = i) (hiB : i ≤ B) (hX : regs₂.getD (base + 4) 0 = x)
    (hxs : (finFunctionFinEquiv xs : ℕ) = x) (hpath : Relation.RelatesWithinSteps E s₀ xs i) :
    Complete P w (b + 6 + 2 * k) regs₂ w₁ (Kept B (base + 7 + 2 * k) regs₂) := by
  obtain ⟨-, -, -, -, -, -, -, -, h9, -⟩ := countTestCode_parts hw hP
  have hsrc' : ∀ regs, (∀ j < base + 7 + 2 * k, regs.getD j 0 = regs₂.getD j 0) →
      ∀ j, (src j).eval regs = s₀ j := fun regs h =>
    hsrc regs fun j hj => (h j (by omega)).trans (hk.getD_eq j hj)
  obtain ⟨regsI, hrI, hinvI⟩ := loop_init (w := w) h9 (by omega) hnB hk.bounded hsrc'
  obtain ⟨m, hm, hsteps⟩ := hpath
  exact Complete.of_oblivious hrI (loop_complete h9 (by omega) hnB hNB hiB h0
    (walk_dst h0 hX hxs) (walk_M hI)
    (fun us ws t regs₃ hmid hE => hwb regs₂ us ws t regs₃ hk hmid hE)
    m 0 s₀ regsI hsteps (by omega) hinvI)

private theorem scan_decode (hw : w₁ = b + 14 + 5 * k + wb.length)
    (hP : P.CodeAt b (countTestCode b base k src wb et ef T R)) (hnB : n ≤ B) {x y : ℕ}
    {regs : List ℕ} (hlen : base + 9 + 4 * k ≤ regs.length) (h0 : regs.getD 0 0 = n)
    (hB : ∀ r ∈ regs, r ≤ B) (hX : regs.getD (base + 4) 0 = x) (hx : x < n ^ k)
    (hY : regs.getD (base + 3) 0 = y) (hy : y < n ^ k) :
    ∃ (regs₂ : List ℕ) (xs ys : Fin k → Fin n),
      P.Reaches w (P.Oblivious B) (b + 6, 0 :: regs) (b + 6 + 2 * k, 0 :: regs₂) ∧
      Kept B (base + 7) regs regs₂ ∧ (finFunctionFinEquiv xs : ℕ) = x ∧
      (finFunctionFinEquiv ys : ℕ) = y ∧ (∀ j : Fin k, regs₂.getD (base + 7 + j) 0 = xs j) ∧
      ∀ j : Fin k, regs₂.getD (base + 7 + k + j) 0 = ys j := by
  obtain ⟨-, -, -, -, -, -, h7, h8, -⟩ := countTestCode_parts hw hP
  obtain ⟨regs₁, hr₁, hlen₁, hout₁, hin₁, hB₁⟩ := reaches_digits (w := w) h7 (by omega)
    (by omega) (by omega) h0 hnB hB ⟨x, hx⟩ hX
  obtain ⟨regs₂, hr₂, hlen₂, hout₂, hin₂, hB₂⟩ := reaches_digits (w := w) h8 (by omega)
    (by omega) (by rw [hlen₁]; omega) (by rw [hout₁ 0 (by omega)]; exact h0) hnB hB₁ ⟨y, hy⟩
    (by rw [hout₁ _ (by omega)]; exact hY)
  refine ⟨regs₂, finFunctionFinEquiv.symm ⟨x, hx⟩, finFunctionFinEquiv.symm ⟨y, hy⟩, ?_,
    ⟨by rw [hlen₂, hlen₁], fun j hj => by rw [hout₂ j (by omega), hout₁ j (by omega)], hB₂⟩,
    by rw [Equiv.apply_symm_apply], by rw [Equiv.apply_symm_apply], fun j => ?_, hin₂⟩
  · rw [show b + 6 + 2 * k = b + 6 + k + k by omega]
    exact hr₁.trans hr₂
  · have := j.isLt
    rw [hout₂ _ (by omega), hin₁ j]

private theorem scan_count (hw : w₁ = b + 14 + 5 * k + wb.length)
    (hP : P.CodeAt b (countTestCode b base k src wb et ef T R)) {s : ℕ} {regs : List ℕ}
    (hlen : base + 7 ≤ regs.length) (hB : ∀ r ∈ regs, r ≤ B)
    (hS : regs.getD (base + 5) 0 = s) (hsB : s + 1 ≤ B) :
    ∃ regs', P.Reaches w (P.Oblivious B) (w₁, 0 :: regs) (w₁ + 2, 0 :: regs') ∧
      Kept B (base + 5) regs regs' ∧ regs'.getD (base + 5) 0 = s + 1 ∧
      ∀ j, j ≠ base + 5 → regs'.getD j 0 = regs.getD j 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h10, h11, -⟩ := countTestCode_parts hw hP
  obtain ⟨hr, hB'⟩ := reaches_assign (w := w) (v := s + 1) h10
    (by simp only [eval_add, eval_reg, eval_const, hS]) hsB hB
  refine ⟨regs.set (base + 5) (s + 1), hr.trans (reaches_noop h11 hB'),
    (Kept.refl hB).set_right le_rfl hsB, List.getD_set_self (by omega),
    fun j hj => List.getD_set_ne (Ne.symm hj)⟩

private theorem scan_xinc (hw : w₁ = b + 14 + 5 * k + wb.length)
    (hP : P.CodeAt b (countTestCode b base k src wb et ef T R)) {i y x m : ℕ} {Sel : Finset ℕ}
    {regsT regs : List ℕ} (hinv : ScanInv B base E s₀ i y x m Sel regsT regs)
    (hlen : base + 7 ≤ regs.length) (hxB : x + 1 ≤ B) :
    ∃ regs', P.Reaches w (P.Oblivious B) (w₁ + 9 + et.length + ef.length, 0 :: regs)
      (b + 3, 0 :: regs') ∧ ScanInv B base E s₀ i y (x + 1) m Sel regsT regs' := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h21, -⟩ :=
    countTestCode_parts hw hP
  obtain ⟨hk, hX, hsub, hlt, hS, hH⟩ := hinv
  obtain ⟨hr, -⟩ := reaches_assign (w := w) (v := x + 1) h21
    (by simp only [eval_add, eval_reg, eval_const, hX]) hxB hk.bounded
  refine ⟨regs.set (base + 4) (x + 1), hr, hk.set_right le_rfl hxB,
    List.getD_set_self (by omega), hsub, hlt, ?_, ?_⟩
  · rw [List.getD_set_ne (by omega), hS]
  · rw [List.getD_set_ne (by omega), hH]

private theorem reaches_setH {l next : ℕ} {regs : List ℕ}
    (hl : P.instr l = (Instr.assign (base + 6) (const 1) next).shift) (hB1 : 1 ≤ B)
    (hB : ∀ r ∈ regs, r ≤ B) :
    P.Reaches w (P.Oblivious B) (l, 0 :: regs) (next, 0 :: regs.set (base + 6) 1) :=
  (reaches_assign hl rfl hB1 hB).1

private theorem scanInv_hit {i y x : ℕ} {Sel : Finset ℕ} {regsT regs regs' : List ℕ}
    (hinv : ScanInv B base E s₀ i y x x Sel regsT regs) (hmem : x ∈ countRound E s₀ i)
    (hk : Kept B (base + 5) regs regs') (hS : regs'.getD (base + 5) 0 = Sel.card + 1)
    (hlen : base + 7 ≤ regs'.length) (hB1 : 1 ≤ B) (hhit : x = y ∨ codeEdge E x y = true) :
    ScanInv B base E s₀ i y x (x + 1) (insert x Sel) regsT (regs'.set (base + 6) 1) := by
  obtain ⟨hk₀, hX, hsub, hlt, -, -⟩ := hinv
  have hx : x ∉ Sel := fun h => Nat.lt_irrefl _ (hlt x h)
  refine ⟨hk₀.trans ((hk.mono (by omega)).set_right (by omega) hB1), ?_,
    Finset.insert_subset hmem hsub, fun c hc => ?_, ?_, ?_⟩
  · rw [List.getD_set_ne (by omega), hk.getD_eq _ (by omega), hX]
  · rcases Finset.mem_insert.mp hc with rfl | hc
    · exact Nat.lt_succ_self _
    · exact (hlt c hc).trans (Nat.lt_succ_self _)
  · rw [List.getD_set_ne (by omega), hS, Finset.card_insert_of_notMem hx]
  · rw [List.getD_set_self (by omega),
      ite_eq_left (show ∃ c ∈ insert x Sel, c = y ∨ codeEdge E c y = true from
        ⟨x, Finset.mem_insert_self x Sel, hhit⟩)]

private theorem scanInv_nohit {i y x : ℕ} {Sel : Finset ℕ} {regsT regs regs' : List ℕ}
    (hinv : ScanInv B base E s₀ i y x x Sel regsT regs) (hmem : x ∈ countRound E s₀ i)
    (hk : Kept B (base + 5) regs regs') (hS : regs'.getD (base + 5) 0 = Sel.card + 1)
    (hH : regs'.getD (base + 6) 0 = regs.getD (base + 6) 0)
    (hnohit : ¬ (x = y ∨ codeEdge E x y = true)) :
    ScanInv B base E s₀ i y x (x + 1) (insert x Sel) regsT regs' := by
  obtain ⟨hk₀, hX, hsub, hlt, -, hH₀⟩ := hinv
  have hx : x ∉ Sel := fun h => Nat.lt_irrefl _ (hlt x h)
  have hiff : (∃ c ∈ insert x Sel, c = y ∨ codeEdge E c y = true) ↔
      ∃ c ∈ Sel, c = y ∨ codeEdge E c y = true := by
    constructor
    · rintro ⟨c, hc, hcy⟩
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact absurd hcy hnohit
      · exact ⟨c, hc, hcy⟩
    · rintro ⟨c, hc, hcy⟩
      exact ⟨c, Finset.mem_insert_of_mem hc, hcy⟩
  refine ⟨hk₀.trans (hk.mono (by omega)), ?_, Finset.insert_subset hmem hsub, fun c hc => ?_,
    ?_, ?_⟩
  · rw [hk.getD_eq _ (by omega), hX]
  · rcases Finset.mem_insert.mp hc with rfl | hc
    · exact Nat.lt_succ_self _
    · exact (hlt c hc).trans (Nat.lt_succ_self _)
  · rw [hS, Finset.card_insert_of_notMem hx]
  · rw [hH, hH₀]
    by_cases h : ∃ c ∈ Sel, c = y ∨ codeEdge E c y = true
    · rw [ite_eq_left h, ite_eq_left (hiff.mpr h)]
    · rw [ite_eq_right h, ite_eq_right fun h' => h (hiff.mp h')]

private theorem scanInv_weaken {i y x m : ℕ} {Sel : Finset ℕ} {regsT regs : List ℕ}
    (h : ScanInv B base E s₀ i y x m Sel regsT regs) :
    ScanInv B base E s₀ i y x (m + 1) Sel regsT regs :=
  { h with lt_bound := fun c hc => (h.lt_bound c hc).trans (Nat.lt_succ_self _) }

private theorem scan_mid (hw : w₁ = b + 14 + 5 * k + wb.length)
    (hP : P.CodeAt b (countTestCode b base k src wb et ef T R)) (hNB : n ^ k ≤ B) {i y x : ℕ}
    {Sel : Finset ℕ} {regsT regs regs₂ regs₃ : List ℕ}
    (hpre : TestPre B base E s₀ regs₀ i y regsT) (hinv : ScanInv B base E s₀ i y x x Sel regsT regs)
    (hmem : x ∈ countRound E s₀ i) (hk₂ : Kept B (base + 7) regs regs₂)
    (hk₃ : Kept B (base + 7 + 2 * k) regs₂ regs₃) {xs ys : Fin k → Fin n}
    (hxs : ∀ j : Fin k, regs₂.getD (base + 7 + j) 0 = xs j)
    (hys : ∀ j : Fin k, regs₂.getD (base + 7 + k + j) 0 = ys j) :
    ∃ regs₄, P.Reaches w (P.Oblivious B) (w₁, 0 :: regs₃) (w₁ + 2, 0 :: regs₄) ∧
      Kept B (base + 5) regs regs₄ ∧ Kept B base regs₀ regs₄ ∧ base + 9 + 4 * k ≤ regs₄.length ∧
      regs₄.getD (base + 4) 0 = x ∧ regs₄.getD (base + 3) 0 = y ∧
      regs₄.getD (base + 5) 0 = Sel.card + 1 ∧ regs₄.getD (base + 6) 0 = regs.getD (base + 6) 0 ∧
      (∀ j : Fin k, regs₄.getD (base + 7 + j) 0 = xs j) ∧
      ∀ j : Fin k, regs₄.getD (base + 7 + k + j) 0 = ys j := by
  obtain ⟨hkR, hlen, -, -, -, -, hY, -⟩ := hpre.of_kept hinv.kept
  obtain ⟨-, hX, hsub, hlt, hS, -⟩ := hinv
  have hx : x ∉ Sel := fun h => Nat.lt_irrefl _ (hlt x h)
  have hcard : Sel.card + 1 ≤ B := by
    have := Finset.card_le_card (Finset.insert_subset hmem hsub)
    rw [Finset.card_insert_of_notMem hx] at this
    exact this.trans (card_countRound_le.trans hNB)
  have hS₃ : regs₃.getD (base + 5) 0 = Sel.card := by
    rw [hk₃.getD_eq _ (by omega), hk₂.getD_eq _ (by omega), hS]
  obtain ⟨regs₄, hr₄, hk₄, hS₄, hout₄⟩ := scan_count (w := w) hw hP
    (by rw [hk₃.length_eq, hk₂.length_eq]; omega) hk₃.bounded hS₃ hcard
  have hk₂₄ : Kept B (base + 5) regs regs₄ :=
    ((hk₂.mono (by omega)).trans (hk₃.mono (by omega))).trans hk₄
  refine ⟨regs₄, hr₄, hk₂₄, hkR.trans (hk₂₄.mono (by omega)), by rw [hk₂₄.length_eq]; exact hlen,
    by rw [hk₂₄.getD_eq _ (by omega), hX], by rw [hk₂₄.getD_eq _ (by omega), hY], hS₄, ?_,
    fun j => ?_, fun j => ?_⟩
  · rw [hout₄ _ (by omega), hk₃.getD_eq _ (by omega), hk₂.getD_eq _ (by omega)]
  · have := j.isLt
    rw [hout₄ _ (by omega), hk₃.getD_eq _ (by omega), hxs]
  · have := j.isLt
    rw [hout₄ _ (by omega), hk₃.getD_eq _ (by omega), hys]

private theorem scan_next_sound (hw : w₁ = b + 14 + 5 * k + wb.length)
    (hP : P.CodeAt b (countTestCode b base k src wb et ef T R)) (hB1 : 1 ≤ B) {i y x : ℕ}
    {Sel : Finset ℕ} {regsT regs : List ℕ} {G : List ℕ → Prop}
    (hinv : ScanInv B base E s₀ i y x (x + 1) Sel regsT regs) (hlen : base + 7 ≤ regs.length)
    (hxB : x + 1 ≤ B)
    (ih : ∀ regs', ScanInv B base E s₀ i y (x + 1) (x + 1) Sel regsT regs' →
      Sound P w B Post (b + 3) regs' T G) :
    Sound P w B Post (w₁ + 9 + et.length + ef.length) regs T G := by
  obtain ⟨regs', hr, hinv'⟩ := scan_xinc (w := w) hw hP hinv hlen hxB
  exact Sound.of_oblivious hB1 hr (ih regs' hinv')

private theorem scan_next_complete (hw : w₁ = b + 14 + 5 * k + wb.length)
    (hP : P.CodeAt b (countTestCode b base k src wb et ef T R)) {i y x : ℕ}
    {Sel : Finset ℕ} {regsT regs : List ℕ} {G : List ℕ → Prop}
    (hinv : ScanInv B base E s₀ i y x (x + 1) Sel regsT regs) (hlen : base + 7 ≤ regs.length)
    (hxB : x + 1 ≤ B)
    (ih : ∀ regs', ScanInv B base E s₀ i y (x + 1) (x + 1) Sel regsT regs' →
      Complete P w (b + 3) regs' T G) :
    Complete P w (w₁ + 9 + et.length + ef.length) regs T G := by
  obtain ⟨regs', hr, hinv'⟩ := scan_xinc (w := w) hw hP hinv hlen hxB
  exact Complete.of_oblivious hr (ih regs' hinv')

private theorem scan_sound (hw : w₁ = b + 14 + 5 * k + wb.length)
    (hP : P.CodeAt b (countTestCode b base k src wb et ef T R)) (hB1 : 1 ≤ B) (hnB : n ≤ B)
    (hNB : n ^ k ≤ B) (hR : (P.instr R).halts = true) (hPost : ∀ s : Config, s.1 = R → Post s)
    (hsrc : ∀ regs, (∀ j < base, regs.getD j 0 = regs₀.getD j 0) → ∀ j, (src j).eval regs = s₀ j)
    (hwb : ∀ regsW us ws t regs₃, Kept B base regs₀ regsW →
      LoopMid n B (base + 7 + 2 * k) k regsW us ws t regs₃ →
      Sound P w B Post (b + 6 + 2 * k + 2 * k + 7) regs₃ (b + 6 + 2 * k + 2 * k + 7 + wb.length)
        (fun regs' => Kept B (base + 7 + 2 * k + 2 * k + 2) regs₃ regs' ∧ E us ws))
    (het : ∀ regs₂ (xs ys : Fin k → Fin n), Kept B base regs₀ regs₂ →
      (∀ j : Fin k, regs₂.getD (base + 7 + j) 0 = xs j) →
      (∀ j : Fin k, regs₂.getD (base + 7 + k + j) 0 = ys j) →
      Sound P w B Post (w₁ + 8) regs₂ (w₁ + 7)
        (fun regs' => Kept B (base + 7 + 2 * k) regs₂ regs' ∧ E xs ys))
    (hef : ∀ regs₂ (xs ys : Fin k → Fin n), Kept B base regs₀ regs₂ →
      (∀ j : Fin k, regs₂.getD (base + 7 + j) 0 = xs j) →
      (∀ j : Fin k, regs₂.getD (base + 7 + k + j) 0 = ys j) →
      Sound P w B Post (w₁ + 9 + et.length) regs₂ (w₁ + 9 + et.length + ef.length)
        (fun regs' => Kept B (base + 7 + 2 * k) regs₂ regs' ∧ ¬ E xs ys))
    {i y : ℕ} {regsT : List ℕ} (hpre : TestPre B base E s₀ regs₀ i y regsT) :
    ∀ e x Sel regs, n ^ k - x = e → ScanInv B base E s₀ i y x x Sel regsT regs →
      Sound P w B Post (b + 3) regs T (fun regs' =>
        Kept B (base + 4) regsT regs' ∧
          regs'.getD (base + 6) 0 = if y ∈ countRound E s₀ (i + 1) then 1 else 0) := by
  obtain ⟨-, -, -, -, -, h6, -, -, -, -, -, h12, h13, h14, h15, h16, h17, -, h19, -⟩ :=
    countTestCode_parts hw hP
  have hiB : i ≤ B := by have := hpre.round_lt; omega
  have hy := hpre.cand_lt
  intro e
  induction e with
  | zero =>
    intro x Sel regs he hinv
    exact Sound.of_oblivious hB1 (scan_leave hw hP hinv.kept.bounded (hpre.of_kept hinv.kept).size
      hinv.cur (by omega)) (scan_check_sound hw hP hB1 hR hPost hpre hinv)
  | succ e ih =>
    intro x Sel regs he hinv
    obtain ⟨hkR, hlen, h0', hI, -, -, hY, -⟩ := hpre.of_kept hinv.kept
    have hx : x < n ^ k := by omega
    have hxB : x + 1 ≤ B := by omega
    have hB := hinv.kept.bounded
    have hnext : ∀ Sel' regs', ScanInv B base E s₀ i y x (x + 1) Sel' regsT regs' →
        base + 7 ≤ regs'.length →
        Sound P w B Post (w₁ + 9 + et.length + ef.length) regs' T (fun regs' =>
          Kept B (base + 4) regsT regs' ∧
            regs'.getD (base + 6) 0 = if y ∈ countRound E s₀ (i + 1) then 1 else 0) :=
      fun Sel' regs' hinv' hlen' => scan_next_sound hw hP hB1 hinv' hlen' hxB
        fun regs'' hinv'' => ih (x + 1) Sel' regs'' (by omega) hinv''
    refine Sound.of_oblivious hB1 (scan_enter hw hP hB h0' hinv.cur hx)
      (Sound.choice hB1 h6 hB ?_ (hnext Sel regs (scanInv_weaken hinv) (by omega)))
    -- select `x`: decode, walk, count
    obtain ⟨regs₂, xs, ys, hr₂, hk₂, hxs, hys, hxs₂, hys₂⟩ := scan_decode (w := w) hw hP hnB hlen
      h0' hB hinv.cur hx hY hy
    have hk₀₂ : Kept B base regs₀ regs₂ := hkR.trans (hk₂.mono (by omega))
    refine Sound.of_oblivious hB1 hr₂ ((walk_sound (i := i) (x := x) (xs := xs) hw hP hB1 hnB hNB hR
      hPost hsrc hwb hk₀₂
      (by rw [hk₂.length_eq]; omega) (by rw [hk₂.getD_eq 0 (by omega)]; exact h0')
      (by rw [hk₂.getD_eq _ (by omega)]; exact hI) hiB
      (by rw [hk₂.getD_eq _ (by omega)]; exact hinv.cur) hxs).bind fun regs₃ ⟨hk₃, hpath⟩ => ?_)
    have hmem : x ∈ countRound E s₀ i := by rw [← hxs]; exact mem_countRound_iff.mpr hpath
    obtain ⟨regs₄, hr₄, hk₄, hk₀₄, hlen₄, hX₄, hY₄, hS₄, hH₄, hxs₄, hys₄⟩ :=
      scan_mid (w := w) hw hP hNB hpre hinv hmem hk₂ hk₃ hxs₂ hys₂
    have hB₄ := hk₄.bounded
    have hedge : codeEdge E x y = true ↔ E xs ys := by rw [← hxs, ← hys]; exact codeEdge_code xs ys
    have hlenH : base + 7 ≤ (regs₄.set (base + 6) 1).length := by
      rw [List.length_set]; omega
    refine Sound.of_oblivious hB1 hr₄ (Sound.choice hB1 h12 hB₄ ?_ ?_)
    · -- a hit: `x = y` or an edge from `x` to `y`
      refine Sound.of_oblivious hB1 (reaches_noop h13 hB₄) (Sound.choice hB1 h14 hB₄ ?_ ?_)
      · by_cases hxy : x = y
        · refine Sound.of_oblivious hB1 ((reaches_dist_eq h15 hB₄ (by rw [hX₄, hY₄, hxy])).trans
            (reaches_setH h16 hB1 hB₄)) ?_
          exact hnext _ _ (scanInv_hit hinv hmem hk₄ hS₄ (by omega) hB1 (Or.inl hxy)) hlenH
        · exact Sound.of_oblivious hB1 (reaches_dist_ne h15 hB₄ (by rw [hX₄, hY₄]; exact hxy))
            (Sound.halt hB1 hR (fun _ => hPost _ rfl) hB₄)
      · refine (het regs₄ xs ys hk₀₄ hxs₄ hys₄).bind fun regs₅ ⟨hk₅, hE⟩ => ?_
        have hk₄₅ : Kept B (base + 5) regs regs₅ := hk₄.trans (hk₅.mono (by omega))
        refine Sound.of_oblivious hB1 (reaches_setH h17 hB1 hk₅.bounded) ?_
        exact hnext _ _ (scanInv_hit hinv hmem hk₄₅ (by rw [hk₅.getD_eq _ (by omega), hS₄])
          (by rw [hk₄₅.length_eq]; omega) hB1 (Or.inr (hedge.mpr hE)))
          (by rw [List.length_set, hk₄₅.length_eq]; omega)
    · -- no hit: `x ≠ y` and no edge from `x` to `y`
      by_cases hxy : x = y
      · exact Sound.of_oblivious hB1 (reaches_dist_eq h19 hB₄ (by rw [hX₄, hY₄, hxy]))
          (Sound.halt hB1 hR (fun _ => hPost _ rfl) hB₄)
      refine Sound.of_oblivious hB1 (reaches_dist_ne h19 hB₄ (by rw [hX₄, hY₄]; exact hxy))
        ((hef regs₄ xs ys hk₀₄ hxs₄ hys₄).bind fun regs₅ ⟨hk₅, hE⟩ => ?_)
      have hk₄₅ : Kept B (base + 5) regs regs₅ := hk₄.trans (hk₅.mono (by omega))
      exact hnext _ _ (scanInv_nohit hinv hmem hk₄₅ (by rw [hk₅.getD_eq _ (by omega), hS₄])
        (by rw [hk₅.getD_eq _ (by omega), hH₄]) fun h => h.elim hxy fun h' => hE (hedge.mp h'))
        (by rw [hk₄₅.length_eq]; omega)

private theorem scan_complete (hw : w₁ = b + 14 + 5 * k + wb.length)
    (hP : P.CodeAt b (countTestCode b base k src wb et ef T R)) (hB1 : 1 ≤ B) (hnB : n ≤ B)
    (hNB : n ^ k ≤ B)
    (hsrc : ∀ regs, (∀ j < base, regs.getD j 0 = regs₀.getD j 0) → ∀ j, (src j).eval regs = s₀ j)
    (hwb : ∀ regsW us ws t regs₃, Kept B base regs₀ regsW →
      LoopMid n B (base + 7 + 2 * k) k regsW us ws t regs₃ → E us ws →
      Complete P w (b + 6 + 2 * k + 2 * k + 7) regs₃ (b + 6 + 2 * k + 2 * k + 7 + wb.length)
        (Kept B (base + 7 + 2 * k + 2 * k + 2) regs₃))
    (het : ∀ regs₂ (xs ys : Fin k → Fin n), Kept B base regs₀ regs₂ →
      (∀ j : Fin k, regs₂.getD (base + 7 + j) 0 = xs j) →
      (∀ j : Fin k, regs₂.getD (base + 7 + k + j) 0 = ys j) → E xs ys →
      Complete P w (w₁ + 8) regs₂ (w₁ + 7) (Kept B (base + 7 + 2 * k) regs₂))
    (hef : ∀ regs₂ (xs ys : Fin k → Fin n), Kept B base regs₀ regs₂ →
      (∀ j : Fin k, regs₂.getD (base + 7 + j) 0 = xs j) →
      (∀ j : Fin k, regs₂.getD (base + 7 + k + j) 0 = ys j) → ¬ E xs ys →
      Complete P w (w₁ + 9 + et.length) regs₂ (w₁ + 9 + et.length + ef.length)
        (Kept B (base + 7 + 2 * k) regs₂))
    {i y : ℕ} {regsT : List ℕ} (hpre : TestPre B base E s₀ regs₀ i y regsT) :
    ∀ e x regs, n ^ k - x = e →
      ScanInv B base E s₀ i y x x ((countRound E s₀ i).filter (· < x)) regsT regs →
      Complete P w (b + 3) regs T (fun regs' =>
        Kept B (base + 4) regsT regs' ∧
          regs'.getD (base + 6) 0 = if y ∈ countRound E s₀ (i + 1) then 1 else 0) := by
  obtain ⟨-, -, -, -, -, h6, -, -, -, -, -, h12, h13, h14, h15, h16, h17, -, h19, -⟩ :=
    countTestCode_parts hw hP
  have hiB : i ≤ B := by have := hpre.round_lt; omega
  have hy := hpre.cand_lt
  intro e
  induction e with
  | zero =>
    intro x regs he hinv
    have h0 := (hpre.of_kept hinv.kept).size
    have hfull : (countRound E s₀ i).filter (· < x) = countRound E s₀ i :=
      Finset.filter_true_of_mem fun c hc => by
        have := lt_of_mem_countRound hc
        change c < x
        omega
    rw [hfull] at hinv
    exact Complete.of_oblivious (scan_leave hw hP hinv.kept.bounded h0 hinv.cur (by omega))
      (scan_check_complete hw hP hpre hinv)
  | succ e ih =>
    intro x regs he hinv
    obtain ⟨hkR, hlen, h0', hI, -, -, hY, -⟩ := hpre.of_kept hinv.kept
    have hx : x < n ^ k := by omega
    have hxB : x + 1 ≤ B := by omega
    have hB := hinv.kept.bounded
    have hnext : ∀ regs', ScanInv B base E s₀ i y x (x + 1)
        ((countRound E s₀ i).filter (· < x + 1)) regsT regs' → base + 7 ≤ regs'.length →
        Complete P w (w₁ + 9 + et.length + ef.length) regs' T (fun regs' =>
          Kept B (base + 4) regsT regs' ∧
            regs'.getD (base + 6) 0 = if y ∈ countRound E s₀ (i + 1) then 1 else 0) :=
      fun regs' hinv' hlen' => scan_next_complete hw hP hinv' hlen' hxB
        fun regs'' hinv'' => ih (x + 1) regs'' (by omega) hinv''
    by_cases hmem : x ∈ countRound E s₀ i
    · rw [InductiveCounting.filter_lt_succ_of_mem hmem] at hnext
      refine Complete.choice (scan_enter hw hP hB h0' hinv.cur hx) (by omega) h6 (Or.inl ?_)
      obtain ⟨regs₂, xs, ys, hr₂, hk₂, hxs, hys, hxs₂, hys₂⟩ := scan_decode (w := w) hw hP hnB
        hlen h0' hB hinv.cur hx hY hy
      have hk₀₂ : Kept B base regs₀ regs₂ := hkR.trans (hk₂.mono (by omega))
      have hpath : Relation.RelatesWithinSteps E s₀ xs i := by
        rw [← hxs] at hmem; exact mem_countRound_iff.mp hmem
      refine Complete.of_oblivious hr₂ ((walk_complete (i := i) (x := x) (xs := xs) hw hP hnB hNB
        hsrc hwb hk₀₂
        (by rw [hk₂.length_eq]; omega) (by rw [hk₂.getD_eq 0 (by omega)]; exact h0')
        (by rw [hk₂.getD_eq _ (by omega)]; exact hI) hiB
        (by rw [hk₂.getD_eq _ (by omega)]; exact hinv.cur) hxs hpath).bind fun regs₃ hk₃ => ?_)
      obtain ⟨regs₄, hr₄, hk₄, hk₀₄, hlen₄, hX₄, hY₄, hS₄, hH₄, hxs₄, hys₄⟩ :=
        scan_mid (w := w) hw hP hNB hpre hinv hmem hk₂ hk₃ hxs₂ hys₂
      have hB₄ := hk₄.bounded
      have hedge : codeEdge E x y = true ↔ E xs ys := by
        rw [← hxs, ← hys]; exact codeEdge_code xs ys
      have hlenH : base + 7 ≤ (regs₄.set (base + 6) 1).length := by
        rw [List.length_set]; omega
      by_cases hxy : x = y
      · refine Complete.choice hr₄ (by omega) h12 (Or.inl ?_)
        refine Complete.choice (reaches_noop h13 hB₄) (by omega) h14 (Or.inl ?_)
        refine Complete.of_oblivious ((reaches_dist_eq h15 hB₄ (by rw [hX₄, hY₄, hxy])).trans
          (reaches_setH h16 hB1 hB₄)) ?_
        exact hnext _ (scanInv_hit hinv hmem hk₄ hS₄ (by omega) hB1 (Or.inl hxy)) hlenH
      by_cases hE : E xs ys
      · refine Complete.choice hr₄ (by omega) h12 (Or.inl ?_)
        refine Complete.choice (reaches_noop h13 hB₄) (by omega) h14 (Or.inr ?_)
        refine (het regs₄ xs ys hk₀₄ hxs₄ hys₄ hE).bind fun regs₅ hk₅ => ?_
        have hk₄₅ : Kept B (base + 5) regs regs₅ := hk₄.trans (hk₅.mono (by omega))
        refine Complete.of_oblivious (reaches_setH h17 hB1 hk₅.bounded) ?_
        exact hnext _ (scanInv_hit hinv hmem hk₄₅ (by rw [hk₅.getD_eq _ (by omega), hS₄])
          (by rw [hk₄₅.length_eq]; omega) hB1 (Or.inr (hedge.mpr hE)))
          (by rw [List.length_set, hk₄₅.length_eq]; omega)
      · refine Complete.choice hr₄ (by omega) h12 (Or.inr ?_)
        refine Complete.of_oblivious (reaches_dist_ne h19 hB₄ (by rw [hX₄, hY₄]; exact hxy))
          ((hef regs₄ xs ys hk₀₄ hxs₄ hys₄ hE).bind fun regs₅ hk₅ => ?_)
        have hk₄₅ : Kept B (base + 5) regs regs₅ := hk₄.trans (hk₅.mono (by omega))
        exact hnext _ (scanInv_nohit hinv hmem hk₄₅ (by rw [hk₅.getD_eq _ (by omega), hS₄])
          (by rw [hk₅.getD_eq _ (by omega), hH₄]) fun h => h.elim hxy fun h' => hE (hedge.mp h'))
          (by rw [hk₄₅.length_eq]; omega)
    · rw [InductiveCounting.filter_lt_succ_of_notMem hmem] at hnext
      exact Complete.choice (scan_enter hw hP hB h0' hinv.cur hx) (by omega) h6
        (Or.inr (hnext regs (scanInv_weaken hinv) (by omega)))

/-- **Soundness of one test**: from the state before a test of `y` against round `i`, every
branch rejects or reaches `T` with register `base + 6` recording whether `y` is in round
`i + 1`, given sound walk and edge codes. -/
theorem test_sound (hw : w₁ = b + 14 + 5 * k + wb.length)
    (hP : P.CodeAt b (countTestCode b base k src wb et ef T R)) (hB1 : 1 ≤ B) (hnB : n ≤ B)
    (hNB : n ^ k ≤ B) (hR : (P.instr R).halts = true) (hPost : ∀ s : Config, s.1 = R → Post s)
    (hsrc : ∀ regs, (∀ j < base, regs.getD j 0 = regs₀.getD j 0) → ∀ j, (src j).eval regs = s₀ j)
    (hwb : ∀ regsW us ws t regs₃, Kept B base regs₀ regsW →
      LoopMid n B (base + 7 + 2 * k) k regsW us ws t regs₃ →
      Sound P w B Post (b + 6 + 2 * k + 2 * k + 7) regs₃ (b + 6 + 2 * k + 2 * k + 7 + wb.length)
        (fun regs' => Kept B (base + 7 + 2 * k + 2 * k + 2) regs₃ regs' ∧ E us ws))
    (het : ∀ regs₂ (xs ys : Fin k → Fin n), Kept B base regs₀ regs₂ →
      (∀ j : Fin k, regs₂.getD (base + 7 + j) 0 = xs j) →
      (∀ j : Fin k, regs₂.getD (base + 7 + k + j) 0 = ys j) →
      Sound P w B Post (w₁ + 8) regs₂ (w₁ + 7)
        (fun regs' => Kept B (base + 7 + 2 * k) regs₂ regs' ∧ E xs ys))
    (hef : ∀ regs₂ (xs ys : Fin k → Fin n), Kept B base regs₀ regs₂ →
      (∀ j : Fin k, regs₂.getD (base + 7 + j) 0 = xs j) →
      (∀ j : Fin k, regs₂.getD (base + 7 + k + j) 0 = ys j) →
      Sound P w B Post (w₁ + 9 + et.length) regs₂ (w₁ + 9 + et.length + ef.length)
        (fun regs' => Kept B (base + 7 + 2 * k) regs₂ regs' ∧ ¬ E xs ys))
    {i y : ℕ} {regs : List ℕ} (hpre : TestPre B base E s₀ regs₀ i y regs) :
    Sound P w B Post b regs T (fun regs' =>
      Kept B (base + 4) regs regs' ∧
        regs'.getD (base + 6) 0 = if y ∈ countRound E s₀ (i + 1) then 1 else 0) := by
  obtain ⟨regs₁, hr₁, hinv₁⟩ := scan_start (w := w) (E := E) (s₀ := s₀) (i := i) (y := y) hw hP
    (by have := hpre.le_length; omega) hpre.kept.bounded
  exact Sound.of_oblivious hB1 hr₁ (scan_sound hw hP hB1 hnB hNB hR hPost hsrc hwb het hef hpre
    _ 0 ∅ regs₁ rfl hinv₁)

/-- **Completeness of one test**: from the state before a test of `y` against round `i`, some
branch reaches `T` with register `base + 6` recording whether `y` is in round `i + 1`, given
complete walk and edge codes. -/
theorem test_complete (hw : w₁ = b + 14 + 5 * k + wb.length)
    (hP : P.CodeAt b (countTestCode b base k src wb et ef T R)) (hB1 : 1 ≤ B) (hnB : n ≤ B)
    (hNB : n ^ k ≤ B)
    (hsrc : ∀ regs, (∀ j < base, regs.getD j 0 = regs₀.getD j 0) → ∀ j, (src j).eval regs = s₀ j)
    (hwb : ∀ regsW us ws t regs₃, Kept B base regs₀ regsW →
      LoopMid n B (base + 7 + 2 * k) k regsW us ws t regs₃ → E us ws →
      Complete P w (b + 6 + 2 * k + 2 * k + 7) regs₃ (b + 6 + 2 * k + 2 * k + 7 + wb.length)
        (Kept B (base + 7 + 2 * k + 2 * k + 2) regs₃))
    (het : ∀ regs₂ (xs ys : Fin k → Fin n), Kept B base regs₀ regs₂ →
      (∀ j : Fin k, regs₂.getD (base + 7 + j) 0 = xs j) →
      (∀ j : Fin k, regs₂.getD (base + 7 + k + j) 0 = ys j) → E xs ys →
      Complete P w (w₁ + 8) regs₂ (w₁ + 7) (Kept B (base + 7 + 2 * k) regs₂))
    (hef : ∀ regs₂ (xs ys : Fin k → Fin n), Kept B base regs₀ regs₂ →
      (∀ j : Fin k, regs₂.getD (base + 7 + j) 0 = xs j) →
      (∀ j : Fin k, regs₂.getD (base + 7 + k + j) 0 = ys j) → ¬ E xs ys →
      Complete P w (w₁ + 9 + et.length) regs₂ (w₁ + 9 + et.length + ef.length)
        (Kept B (base + 7 + 2 * k) regs₂))
    {i y : ℕ} {regs : List ℕ} (hpre : TestPre B base E s₀ regs₀ i y regs) :
    Complete P w b regs T (fun regs' =>
      Kept B (base + 4) regs regs' ∧
        regs'.getD (base + 6) 0 = if y ∈ countRound E s₀ (i + 1) then 1 else 0) := by
  obtain ⟨regs₁, hr₁, hinv₁⟩ := scan_start (w := w) (E := E) (s₀ := s₀) (i := i) (y := y) hw hP
    (by have := hpre.le_length; omega) hpre.kept.bounded
  have hempty : (countRound E s₀ i).filter (· < 0) = ∅ :=
    Finset.filter_false_of_mem fun c _ => Nat.not_lt_zero c
  rw [← hempty] at hinv₁
  exact Complete.of_oblivious hr₁ (scan_complete hw hP hB1 hnB hNB hsrc hwb het hef hpre
    _ 0 regs₁ rfl hinv₁)

end Test

section Count

variable {P : CounterProgram} {w : List Bool} {B : ℕ} {Post : Config → Prop}
  {n k b base T R : ℕ} {dst : Fin k → Expr} {t₁ t₂ : List Instr}
  {E : (Fin k → Fin n) → (Fin k → Fin n) → Prop} {s₀ z₀ : Fin k → Fin n} {regs₀ : List ℕ}

variable (B base E s₀ regs₀) in
/-- The invariant at the round head: round `i` with `i + 1 ≤ n ^ k` in register `base` and its
size in register `base + 1`. -/
private structure RoundInv (i : ℕ) (regs : List ℕ) : Prop where
  /-- The registers below `base` and the length are kept, and every register is bounded. -/
  kept : Kept B base regs₀ regs
  /-- The block's registers exist. -/
  le_length : base + 9 + 4 * k ≤ regs.length
  /-- The universe size is in register `0`. -/
  size : regs.getD 0 0 = n
  /-- The round is in register `base`. -/
  round : regs.getD base 0 = i
  /-- The next round is at most `n ^ k`. -/
  succ_le : i + 1 ≤ n ^ k
  /-- The size of the round is in register `base + 1`. -/
  card : regs.getD (base + 1) 0 = (countRound E s₀ i).card

variable (B base E s₀ regs₀) in
/-- The invariant at the candidate head: also `i + 1 < n ^ k`, the candidate `y` in register
`base + 3`, and the number of members of round `i + 1` below `y` (the `prefixCount` of
inductive counting) in register `base + 2`. -/
private structure YInv (i y : ℕ) (regs : List ℕ) : Prop
    extends RoundInv B base E s₀ regs₀ i regs where
  /-- The next round is below `n ^ k`. -/
  succ_lt : i + 1 < n ^ k
  /-- The number of members of round `i + 1` below `y` is in register `base + 2`. -/
  below : regs.getD (base + 2) 0 = prefixCount (n ^ k) (codeEdge E) (finFunctionFinEquiv s₀) i y
  /-- The candidate is in register `base + 3`. -/
  cand : regs.getD (base + 3) 0 = y

/-- The exit of the candidate loop at `y = n ^ k`: store the size of round `i + 1` and advance
to the next round head. -/
private theorem count_y_exit (hP : P.CodeAt b (countCode b base k dst t₁ t₂ T R))
    (hbase : 0 < base) (hNB : n ^ k ≤ B) {i y : ℕ} {regs : List ℕ}
    (hinv : YInv B base E s₀ regs₀ i y regs) (hy : n ^ k ≤ y) :
    ∃ regs', P.Reaches w (P.Oblivious B) (b + 5, 0 :: regs) (b + 2, 0 :: regs') ∧
      RoundInv B base E s₀ regs₀ (i + 1) regs' := by
  obtain ⟨-, -, -, -, -, c6, -, -, -, c10, c11, -⟩ := countCode_parts hP
  obtain ⟨⟨hk, hlen, h0, hI, -, -⟩, hi1, hD, hY⟩ := hinv
  have hfull : prefixCount (n ^ k) (codeEdge E) (finFunctionFinEquiv s₀) i y =
      (countRound E s₀ (i + 1)).card := InductiveCounting.prefixCount_of_le (by omega)
  have hcB : (countRound E s₀ (i + 1)).card ≤ B := card_countRound_le.trans hNB
  obtain ⟨hr₁, hB₁⟩ := reaches_assign (w := w) (v := (countRound E s₀ (i + 1)).card) c10
    (by rw [eval_reg, hD, hfull]) hcB hk.bounded
  obtain ⟨hr₂, -⟩ := reaches_assign (w := w) (v := i + 1) c11
    (by rw [eval_add, eval_reg, eval_const, List.getD_set_ne (by omega), hI]) (by omega) hB₁
  have hB := hk.bounded
  refine ⟨_, Reaches.trans ?_ (hr₁.trans hr₂), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cp_step [hY, h0]
  · exact (hk.set_right (by omega) hcB).set_right le_rfl (by omega)
  · simp only [List.length_set]; omega
  · rw [List.getD_set_ne (by omega), List.getD_set_ne (by omega), h0]
  · exact List.getD_set_self (by simp only [List.length_set]; omega)
  · omega
  · rw [List.getD_set_ne (by omega), List.getD_set_self (by omega)]

/-- Entering the test of a candidate `y < n ^ k`: the state before the test. -/
private theorem count_y_enter (hP : P.CodeAt b (countCode b base k dst t₁ t₂ T R))
    {i y : ℕ} {regs : List ℕ} (hinv : YInv B base E s₀ regs₀ i y regs) (hy : y < n ^ k) :
    P.Reaches w (P.Oblivious B) (b + 5, 0 :: regs) (b + 6, 0 :: regs) ∧
      TestPre B base E s₀ regs₀ i y regs := by
  obtain ⟨-, -, -, -, -, c6, -⟩ := countCode_parts hP
  obtain ⟨⟨hk, hlen, h0, hI, -, hC⟩, hi1, -, hY⟩ := hinv
  have hB := hk.bounded
  refine ⟨?_, hk, hlen, h0, hI, by omega, hC, hY, hy⟩
  cp_step [hY, h0, hy]

/-- After the test of `y`: add its outcome to the prefix count and advance to the candidate
`y + 1`. -/
private theorem count_y_record (hP : P.CodeAt b (countCode b base k dst t₁ t₂ T R))
    (hNB : n ^ k ≤ B) {i y : ℕ} {regs regs' : List ℕ}
    (hinv : YInv B base E s₀ regs₀ i y regs) (hy : y < n ^ k)
    (hk' : Kept B (base + 4) regs regs')
    (hH : regs'.getD (base + 6) 0 = if y ∈ countRound E s₀ (i + 1) then 1 else 0) :
    ∃ regs'', P.Reaches w (P.Oblivious B) (b + t₁.length + 6, 0 :: regs') (b + 5, 0 :: regs'') ∧
      YInv B base E s₀ regs₀ i (y + 1) regs'' := by
  obtain ⟨-, -, -, -, -, -, -, c8, c9, -⟩ := countCode_parts hP
  obtain ⟨⟨hk, hlen, h0, hI, hi, hC⟩, hi1, hD, hY⟩ := hinv
  have hlen' : regs'.length = regs.length := hk'.length_eq
  have hD' : regs'.getD (base + 2) 0 =
      prefixCount (n ^ k) (codeEdge E) (finFunctionFinEquiv s₀) i y := by
    rw [hk'.getD_eq _ (by omega), hD]
  have hY' : regs'.getD (base + 3) 0 = y := by rw [hk'.getD_eq _ (by omega), hY]
  have hcard : prefixCount (n ^ k) (codeEdge E) (finFunctionFinEquiv s₀) i (y + 1) =
      prefixCount (n ^ k) (codeEdge E) (finFunctionFinEquiv s₀) i y +
        if y ∈ countRound E s₀ (i + 1) then 1 else 0 :=
    InductiveCounting.prefixCount_succ y
  have hcB : prefixCount (n ^ k) (codeEdge E) (finFunctionFinEquiv s₀) i (y + 1) ≤ B :=
    InductiveCounting.prefixCount_le.trans hNB
  obtain ⟨hr₁, hB₁⟩ := reaches_assign (w := w)
    (v := prefixCount (n ^ k) (codeEdge E) (finFunctionFinEquiv s₀) i (y + 1)) c8
    (by rw [eval_add, eval_reg, eval_reg, hD', hH, hcard]) hcB hk'.bounded
  obtain ⟨hr₂, -⟩ := reaches_assign (w := w) (v := y + 1) c9
    (by rw [eval_add, eval_reg, eval_const, List.getD_set_ne (by omega), hY']) (by omega) hB₁
  refine ⟨_, hr₁.trans hr₂, ⟨?_, ?_, ?_, ?_, hi, ?_⟩, hi1, ?_, ?_⟩
  · exact ((hk.trans (hk'.mono (by omega))).set_right (by omega) hcB).set_right (by omega)
      (by omega)
  · simp only [List.length_set]; omega
  · rw [List.getD_set_ne (by omega), List.getD_set_ne (by omega), hk'.getD_eq 0 (by omega), h0]
  · rw [List.getD_set_ne (by omega), List.getD_set_ne (by omega), hk'.getD_eq _ (by omega), hI]
  · rw [List.getD_set_ne (by omega), List.getD_set_ne (by omega), hk'.getD_eq _ (by omega), hC]
  · rw [List.getD_set_ne (by omega), List.getD_set_self (by omega)]
  · exact List.getD_set_self (by simp only [List.length_set]; omega)

private theorem count_y_sound (hP : P.CodeAt b (countCode b base k dst t₁ t₂ T R))
    (hbase : 0 < base) (hB1 : 1 ≤ B) (hNB : n ^ k ≤ B)
    (ht₁ : ∀ i y regs, TestPre B base E s₀ regs₀ i y regs →
      Sound P w B Post (b + 6) regs (b + t₁.length + 6) (fun regs' =>
        Kept B (base + 4) regs regs' ∧
          regs'.getD (base + 6) 0 = if y ∈ countRound E s₀ (i + 1) then 1 else 0))
    {G : List ℕ → Prop} {i : ℕ}
    (hnext : ∀ regs, RoundInv B base E s₀ regs₀ (i + 1) regs → Sound P w B Post (b + 2) regs T G) :
    ∀ e y regs, n ^ k - y = e → YInv B base E s₀ regs₀ i y regs →
      Sound P w B Post (b + 5) regs T G := by
  intro e
  induction e with
  | zero =>
    intro y regs he hinv
    obtain ⟨regs', hr, hinv'⟩ := count_y_exit (w := w) hP hbase hNB hinv (by omega)
    exact Sound.of_oblivious hB1 hr (hnext _ hinv')
  | succ e ih =>
    intro y regs he hinv
    obtain ⟨hr, hpre⟩ := count_y_enter (w := w) hP hinv (by omega)
    refine Sound.of_oblivious hB1 hr ((ht₁ i y regs hpre).bind fun regs' ⟨hk', hH⟩ => ?_)
    obtain ⟨regs'', hr', hinv'⟩ := count_y_record (w := w) hP hNB hinv (by omega) hk' hH
    exact Sound.of_oblivious hB1 hr' (ih (y + 1) _ (by omega) hinv')

private theorem count_y_complete (hP : P.CodeAt b (countCode b base k dst t₁ t₂ T R))
    (hbase : 0 < base) (hNB : n ^ k ≤ B)
    (ht₁ : ∀ i y regs, TestPre B base E s₀ regs₀ i y regs →
      Complete P w (b + 6) regs (b + t₁.length + 6) (fun regs' =>
        Kept B (base + 4) regs regs' ∧
          regs'.getD (base + 6) 0 = if y ∈ countRound E s₀ (i + 1) then 1 else 0))
    {G : List ℕ → Prop} {i : ℕ}
    (hnext : ∀ regs, RoundInv B base E s₀ regs₀ (i + 1) regs → Complete P w (b + 2) regs T G) :
    ∀ e y regs, n ^ k - y = e → YInv B base E s₀ regs₀ i y regs →
      Complete P w (b + 5) regs T G := by
  intro e
  induction e with
  | zero =>
    intro y regs he hinv
    obtain ⟨regs', hr, hinv'⟩ := count_y_exit (w := w) hP hbase hNB hinv (by omega)
    exact Complete.of_oblivious hr (hnext _ hinv')
  | succ e ih =>
    intro y regs he hinv
    obtain ⟨hr, hpre⟩ := count_y_enter (w := w) hP hinv (by omega)
    refine Complete.of_oblivious hr ((ht₁ i y regs hpre).bind fun regs' ⟨hk', hH⟩ => ?_)
    obtain ⟨regs'', hr', hinv'⟩ := count_y_record (w := w) hP hNB hinv (by omega) hk' hH
    exact Complete.of_oblivious hr' (ih (y + 1) _ (by omega) hinv')

/-- Entering the candidate loop of round `i` with `i + 1 < n ^ k`: clear the prefix count and the
candidate. -/
private theorem count_round_enter (hP : P.CodeAt b (countCode b base k dst t₁ t₂ T R))
    (hbase : 0 < base) {i : ℕ} {regs : List ℕ}
    (hinv : RoundInv B base E s₀ regs₀ i regs) (hlt : i + 1 < n ^ k) :
    ∃ regs', P.Reaches w (P.Oblivious B) (b + 2, 0 :: regs) (b + 5, 0 :: regs') ∧
      YInv B base E s₀ regs₀ i 0 regs' := by
  obtain ⟨-, -, c3, c4, c5, -⟩ := countCode_parts hP
  obtain ⟨hk, hlen, h0, hI, hi, hC⟩ := hinv
  obtain ⟨hr₁, hB₁⟩ := reaches_assign (w := w) (v := 0) c4 rfl (Nat.zero_le B) hk.bounded
  obtain ⟨hr₂, -⟩ := reaches_assign (w := w) (v := 0) c5 rfl (Nat.zero_le B) hB₁
  have hB := hk.bounded
  refine ⟨_, Reaches.trans ?_ (hr₁.trans hr₂), ⟨?_, ?_, ?_, ?_, hi, ?_⟩, hlt, ?_, ?_⟩
  · cp_step [hI, h0, hlt]
  · exact (hk.set_right (by omega) (Nat.zero_le B)).set_right (by omega) (Nat.zero_le B)
  · simp only [List.length_set]; omega
  · rw [List.getD_set_ne (by omega), List.getD_set_ne (by omega), h0]
  · rw [List.getD_set_ne (by omega), List.getD_set_ne (by omega), hI]
  · rw [List.getD_set_ne (by omega), List.getD_set_ne (by omega), hC]
  · rw [List.getD_set_ne (by omega), List.getD_set_self (by omega),
      InductiveCounting.prefixCount_zero]
  · exact List.getD_set_self (by simp only [List.length_set]; omega)

/-- Leaving the rounds at `i + 1 = n ^ k`: `Y := code z₀`, ready for the final test of it
against round `n ^ k`. -/
private theorem count_final (hP : P.CodeAt b (countCode b base k dst t₁ t₂ T R))
    (hbase : 0 < base) (hNB : n ^ k ≤ B)
    (hdst : ∀ regs, (∀ j < base, regs.getD j 0 = regs₀.getD j 0) →
      ∀ j, (dst j).eval regs = z₀ j)
    {i : ℕ} {regs : List ℕ} (hinv : RoundInv B base E s₀ regs₀ i regs) (hiN : i + 1 = n ^ k) :
    P.Reaches w (P.Oblivious B) (b + 2, 0 :: regs)
        (b + t₁.length + 11, 0 :: regs.set (base + 3) (finFunctionFinEquiv z₀)) ∧
      TestPre B base E s₀ regs₀ i (finFunctionFinEquiv z₀) (regs.set (base + 3)
        (finFunctionFinEquiv z₀)) ∧
      ((finFunctionFinEquiv z₀ : ℕ) ∈ countRound E s₀ (i + 1) ↔ Relation.ReflTransGen E s₀ z₀) := by
  obtain ⟨-, -, c3, -, -, -, -, -, -, -, -, c12, -⟩ := countCode_parts hP
  obtain ⟨hk, hlen, h0, hI, hi, hC⟩ := hinv
  have hzB : (finFunctionFinEquiv z₀ : ℕ) ≤ B := (finFunctionFinEquiv z₀).isLt.le.trans hNB
  obtain ⟨hr₁, -⟩ :=
    reaches_assign (w := w) c12 (eval_codeE h0 (hdst regs hk.getD_eq)) hzB hk.bounded
  have hB := hk.bounded
  refine ⟨Reaches.trans ?_ hr₁,
    ⟨hk.set_right (by omega) hzB, ?_, ?_, ?_, by omega, ?_, ?_, (finFunctionFinEquiv z₀).isLt⟩,
    by rw [hiN]; exact mem_countRound_pow⟩
  · cp_step [hI, h0]
  · simp only [List.length_set]; omega
  · rw [List.getD_set_ne (by omega), h0]
  · rw [List.getD_set_ne (by omega), hI]
  · rw [List.getD_set_ne (by omega), hC]
  · exact List.getD_set_self (by omega)

private theorem count_round_sound (hP : P.CodeAt b (countCode b base k dst t₁ t₂ T R))
    (hbase : 0 < base) (hB1 : 1 ≤ B) (hNB : n ^ k ≤ B) (hR : (P.instr R).halts = true)
    (hPost : ∀ s : Config, s.1 = R → Post s)
    (hdst : ∀ regs, (∀ j < base, regs.getD j 0 = regs₀.getD j 0) →
      ∀ j, (dst j).eval regs = z₀ j)
    (ht₁ : ∀ i y regs, TestPre B base E s₀ regs₀ i y regs →
      Sound P w B Post (b + 6) regs (b + t₁.length + 6) (fun regs' =>
        Kept B (base + 4) regs regs' ∧
          regs'.getD (base + 6) 0 = if y ∈ countRound E s₀ (i + 1) then 1 else 0))
    (ht₂ : ∀ i y regs, TestPre B base E s₀ regs₀ i y regs →
      Sound P w B Post (b + t₁.length + 11) regs (b + t₁.length + 11 + t₂.length) (fun regs' =>
        Kept B (base + 4) regs regs' ∧
          regs'.getD (base + 6) 0 = if y ∈ countRound E s₀ (i + 1) then 1 else 0)) :
    ∀ e i regs, n ^ k - i = e → RoundInv B base E s₀ regs₀ i regs →
      Sound P w B Post (b + 2) regs T (fun regs' =>
        Kept B base regs₀ regs' ∧ ¬ Relation.ReflTransGen E s₀ z₀) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, c14⟩ := countCode_parts hP
  intro e
  induction e with
  | zero => intro i regs he hinv; have := hinv.succ_le; omega
  | succ e ih =>
    intro i regs he hinv
    by_cases hlt : i + 1 < n ^ k
    · obtain ⟨regs', hr, hinv'⟩ := count_round_enter (w := w) hP hbase hinv hlt
      exact Sound.of_oblivious hB1 hr (count_y_sound hP hbase hB1 hNB ht₁
        (fun regs' hinv'' => ih (i + 1) regs' (by omega) hinv'') _ 0 regs' rfl hinv')
    · obtain ⟨hr, hpre, hmem⟩ := count_final (w := w) hP hbase hNB hdst hinv (by omega)
      refine Sound.of_oblivious hB1 hr ((ht₂ i _ _ hpre).bind fun regs' ⟨hk', hH⟩ => ?_)
      have hB' := hk'.bounded
      by_cases hreach : Relation.ReflTransGen E s₀ z₀
      · rw [ite_eq_left (hmem.mpr hreach)] at hH
        refine Sound.of_oblivious hB1 ?_ (Sound.halt hB1 hR (fun _ => hPost _ rfl) hB')
        cp_step [hH]
      · rw [ite_eq_right fun h => hreach (hmem.mp h)] at hH
        refine Sound.of_oblivious hB1 ?_
          (Sound.exit ⟨hpre.kept.trans (hk'.mono (by omega)), hreach⟩)
        cp_step [hH]

private theorem count_round_complete (hP : P.CodeAt b (countCode b base k dst t₁ t₂ T R))
    (hbase : 0 < base) (hNB : n ^ k ≤ B)
    (hdst : ∀ regs, (∀ j < base, regs.getD j 0 = regs₀.getD j 0) →
      ∀ j, (dst j).eval regs = z₀ j)
    (ht₁ : ∀ i y regs, TestPre B base E s₀ regs₀ i y regs →
      Complete P w (b + 6) regs (b + t₁.length + 6) (fun regs' =>
        Kept B (base + 4) regs regs' ∧
          regs'.getD (base + 6) 0 = if y ∈ countRound E s₀ (i + 1) then 1 else 0))
    (ht₂ : ∀ i y regs, TestPre B base E s₀ regs₀ i y regs →
      Complete P w (b + t₁.length + 11) regs (b + t₁.length + 11 + t₂.length) (fun regs' =>
        Kept B (base + 4) regs regs' ∧
          regs'.getD (base + 6) 0 = if y ∈ countRound E s₀ (i + 1) then 1 else 0))
    (hreach : ¬ Relation.ReflTransGen E s₀ z₀) :
    ∀ e i regs, n ^ k - i = e → RoundInv B base E s₀ regs₀ i regs →
      Complete P w (b + 2) regs T (Kept B base regs₀) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, c14⟩ := countCode_parts hP
  intro e
  induction e with
  | zero => intro i regs he hinv; have := hinv.succ_le; omega
  | succ e ih =>
    intro i regs he hinv
    by_cases hlt : i + 1 < n ^ k
    · obtain ⟨regs', hr, hinv'⟩ := count_round_enter (w := w) hP hbase hinv hlt
      exact Complete.of_oblivious hr (count_y_complete hP hbase hNB ht₁
        (fun regs' hinv'' => ih (i + 1) regs' (by omega) hinv'') _ 0 regs' rfl hinv')
    · obtain ⟨hr, hpre, hmem⟩ := count_final (w := w) hP hbase hNB hdst hinv (by omega)
      refine Complete.of_oblivious hr ((ht₂ i _ _ hpre).bind fun regs' ⟨hk', hH⟩ => ?_)
      rw [ite_eq_right fun h => hreach (hmem.mp h)] at hH
      have hB' := hk'.bounded
      refine Complete.of_oblivious (B := B) ?_
        (Complete.refl (hpre.kept.trans (hk'.mono (by omega))))
      cp_step [hH]

private theorem count_init (hP : P.CodeAt b (countCode b base k dst t₁ t₂ T R))
    (hbase : 0 < base) (hB1 : 1 ≤ B) {regs : List ℕ}
    (hlen : base + 9 + 4 * k ≤ regs.length) (h0 : regs.getD 0 0 = n) (hB : ∀ r ∈ regs, r ≤ B) :
    P.Reaches w (P.Oblivious B) (b, 0 :: regs)
      (b + 2, 0 :: (regs.set base 0).set (base + 1) 1) ∧
      RoundInv B base E s₀ regs 0 ((regs.set base 0).set (base + 1) 1) := by
  obtain ⟨c1, c2, -⟩ := countCode_parts hP
  have hpos : 0 < n ^ k := by have := (finFunctionFinEquiv s₀).isLt; omega
  obtain ⟨hr₁, hB₁⟩ := reaches_assign (w := w) (v := 0) c1 rfl (Nat.zero_le B) hB
  obtain ⟨hr₂, -⟩ := reaches_assign (w := w) (v := 1) c2 rfl hB1 hB₁
  refine ⟨hr₁.trans hr₂, ((Kept.refl hB).set_right le_rfl (Nat.zero_le B)).set_right (by omega) hB1,
    ?_, ?_, ?_, by omega, ?_⟩
  · simp only [List.length_set]; omega
  · rw [List.getD_set_ne (by omega), List.getD_set_ne (by omega), h0]
  · rw [List.getD_set_ne (by omega), List.getD_set_self (by omega)]
  · rw [List.getD_set_self (by simp only [List.length_set]; omega), countRound_zero,
      Finset.card_singleton]

/-- **Soundness of the counting block**: every branch rejects or reaches `T` with the target
`z₀` not reachable from `s₀`, given sound tests. -/
theorem count_sound (hP : P.CodeAt b (countCode b base k dst t₁ t₂ T R))
    (hbase : 0 < base) (hB1 : 1 ≤ B) (hNB : n ^ k ≤ B) (hR : (P.instr R).halts = true)
    (hPost : ∀ s : Config, s.1 = R → Post s)
    (hdst : ∀ regs, (∀ j < base, regs.getD j 0 = regs₀.getD j 0) →
      ∀ j, (dst j).eval regs = z₀ j)
    (ht₁ : ∀ i y regs, TestPre B base E s₀ regs₀ i y regs →
      Sound P w B Post (b + 6) regs (b + t₁.length + 6) (fun regs' =>
        Kept B (base + 4) regs regs' ∧
          regs'.getD (base + 6) 0 = if y ∈ countRound E s₀ (i + 1) then 1 else 0))
    (ht₂ : ∀ i y regs, TestPre B base E s₀ regs₀ i y regs →
      Sound P w B Post (b + t₁.length + 11) regs (b + t₁.length + 11 + t₂.length) (fun regs' =>
        Kept B (base + 4) regs regs' ∧
          regs'.getD (base + 6) 0 = if y ∈ countRound E s₀ (i + 1) then 1 else 0))
    (hlen : base + 9 + 4 * k ≤ regs₀.length) (h0 : regs₀.getD 0 0 = n)
    (hB : ∀ r ∈ regs₀, r ≤ B) :
    Sound P w B Post b regs₀ T (fun regs' =>
      Kept B base regs₀ regs' ∧ ¬ Relation.ReflTransGen E s₀ z₀) := by
  obtain ⟨hr, hinv⟩ := count_init (w := w) (E := E) (s₀ := s₀) hP hbase hB1 hlen h0 hB
  exact Sound.of_oblivious hB1 hr
    (count_round_sound hP hbase hB1 hNB hR hPost hdst ht₁ ht₂ _ 0 _ rfl hinv)

/-- **Completeness of the counting block**: when the target `z₀` is not reachable from `s₀`,
some branch reaches `T`, given complete tests. -/
theorem count_complete (hP : P.CodeAt b (countCode b base k dst t₁ t₂ T R))
    (hbase : 0 < base) (hB1 : 1 ≤ B) (hNB : n ^ k ≤ B)
    (hdst : ∀ regs, (∀ j < base, regs.getD j 0 = regs₀.getD j 0) →
      ∀ j, (dst j).eval regs = z₀ j)
    (ht₁ : ∀ i y regs, TestPre B base E s₀ regs₀ i y regs →
      Complete P w (b + 6) regs (b + t₁.length + 6) (fun regs' =>
        Kept B (base + 4) regs regs' ∧
          regs'.getD (base + 6) 0 = if y ∈ countRound E s₀ (i + 1) then 1 else 0))
    (ht₂ : ∀ i y regs, TestPre B base E s₀ regs₀ i y regs →
      Complete P w (b + t₁.length + 11) regs (b + t₁.length + 11 + t₂.length) (fun regs' =>
        Kept B (base + 4) regs regs' ∧
          regs'.getD (base + 6) 0 = if y ∈ countRound E s₀ (i + 1) then 1 else 0))
    (hlen : base + 9 + 4 * k ≤ regs₀.length) (h0 : regs₀.getD 0 0 = n)
    (hB : ∀ r ∈ regs₀, r ≤ B) (hreach : ¬ Relation.ReflTransGen E s₀ z₀) :
    Complete P w b regs₀ T (Kept B base regs₀) := by
  obtain ⟨hr, hinv⟩ := count_init (w := w) (E := E) (s₀ := s₀) hP hbase hB1 hlen h0 hB
  exact Complete.of_oblivious hr
    (count_round_complete hP hbase hNB hdst ht₁ ht₂ hreach _ 0 _ rfl hinv)

end Count

end Cslib.Logic.FO.Ordered.TCModelChecker
