/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.TwoSAT.Layout
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.AllBranches
import Complexity.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD

/-!
# Routines reading an encoded formula

Counter-program routines that navigate the flat layout of an encoded formula
(`Cslib.Complexity.TwoSAT.literalBits`, `Cslib.Complexity.TwoSAT.clauseBits`) with positions held
in registers, each placed at a label and continuing at given labels:

* `Cslib.Complexity.TwoSAT.skipLitCode` moves a position past a literal, group by group;
* `Cslib.Complexity.TwoSAT.skipClauseCode` moves a position past a clause, literal by literal;
* `Cslib.Complexity.TwoSAT.cmpVarCode` compares the variables of two literals digit by digit;
* `Cslib.Complexity.TwoSAT.signCode` reads the polarity of a literal.

None of them reads register `0`, so they can be part of nondeterministic counter programs. Their
specifications are deterministic runs (`Turing.CounterProgram.Reaches`) through configurations
with bounded registers at instructions that do not read the choice
(`Turing.CounterProgram.Oblivious`).

## Main definitions

* `Cslib.Complexity.TwoSAT.skipLitCode`, `Cslib.Complexity.TwoSAT.skipClauseCode`,
  `Cslib.Complexity.TwoSAT.cmpVarCode`, `Cslib.Complexity.TwoSAT.signCode`.

## Main results

* `Cslib.Complexity.TwoSAT.reaches_skipLitCode`, `Cslib.Complexity.TwoSAT.reaches_skipClauseCode`,
  `Cslib.Complexity.TwoSAT.reaches_cmpVarCode`, `Cslib.Complexity.TwoSAT.reaches_signCode`: their
  runs.
-/

@[expose] public section

namespace Cslib.Complexity

namespace TwoSAT

open _root_.Turing _root_.Turing.CounterProgram _root_.Turing.CounterProgram.Instr
  _root_.Turing.CounterProgram.Expr Cslib.Logic.PL

variable {P : CounterProgram} {w : List Bool} {B : ℕ}

/-- The register `r` of a bounded list is bounded. -/
private theorem getD_le {regs : List ℕ} (hB : ∀ r ∈ regs, r ≤ B) (i : ℕ) :
    regs.getD i 0 ≤ B := by
  rcases lt_or_ge i regs.length with h | h
  · rw [List.getD_eq_getElem _ _ h]
    exact hB _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ h]
    exact Nat.zero_le _

/-! ### Skipping a literal -/

/-- The code moving the position in register `p` past the literal there: groups with a marker
as fourth bit are digits, eight bits long, and the end group is ten bits long. -/
def skipLitCode (b p exit : ℕ) : List Instr :=
  [read (add (reg p) (const 3)) (b + 1) (b + 2) (b + 2),
   assign p (add (reg p) (const 8)) b,
   assign p (add (reg p) (const 10)) exit]

/-- **Skipping a literal.** -/
theorem reaches_skipLitCode {b p exit : ℕ} (hcode : P.CodeAt b (skipLitCode b p exit))
    (hp : p ≠ 0) {regs : List ℕ} (hlen : p < regs.length) {pos v : ℕ} {sgn : Bool}
    (hlit : InfixAt w pos (literalBits v sgn)) (hpos : regs.getD p 0 = pos)
    (hB : ∀ r ∈ regs, r ≤ B) (hend : pos + (literalBits v sgn).length ≤ B) :
    P.Reaches w (P.Oblivious B) (b, regs)
      (exit, regs.set p (pos + (literalBits v sgn).length)) := by
  simp only [skipLitCode, codeAt_cons, codeAt_nil, and_true] at hcode
  obtain ⟨h₀, h₁, h₂⟩ := hcode
  rw [show b + 1 + 1 = b + 2 by omega] at h₂
  have hp' : (reg p).readsChoice = false := by simp [Expr.readsChoice, hp]
  rw [length_literalBits] at hend ⊢
  have hBk : ∀ k ≤ v.bits.length, ∀ r ∈ regs.set p (pos + 8 * k), r ≤ B := fun k hk =>
    List.forall_mem_set_of_forall_mem hB (by omega)
  have loop : ∀ e k, v.bits.length - k = e → k ≤ v.bits.length →
      P.Reaches w (P.Oblivious B) (b, regs.set p (pos + 8 * k))
        (exit, regs.set p (pos + (8 * v.bits.length + 10))) := by
    intro e
    induction e with
    | zero =>
      intro k he hk
      obtain rfl : k = v.bits.length := by omega
      refine Reaches.oread h₀ (by simp [Expr.readsChoice, hp]) (hBk _ le_rfl) ?_
      simp only [eval_add, eval_reg, eval_const, List.getD_set_self hlen,
        hlit.literal_end.2.1, readLabel]
      refine Reaches.oassign h₂ hp (by simp [Expr.readsChoice, hp]) (hBk _ le_rfl) ?_
      simp only [eval_add, eval_reg, eval_const, List.getD_set_self hlen, List.set_set]
      rw [Nat.add_assoc]
      exact Reaches.refl _
    | succ e ih =>
      intro k he hk
      have hk' : k < v.bits.length := by omega
      refine Reaches.oread h₀ (by simp [Expr.readsChoice, hp]) (hBk _ hk) ?_
      simp only [eval_add, eval_reg, eval_const, List.getD_set_self hlen,
        (hlit.literal_digit hk').2.1, readLabel]
      refine Reaches.oassign h₁ hp (by simp [Expr.readsChoice, hp]) (hBk _ hk) ?_
      simp only [eval_add, eval_reg, eval_const, List.getD_set_self hlen, List.set_set]
      rw [show pos + 8 * k + 8 = pos + 8 * (k + 1) by ring]
      exact ih (k + 1) (by omega) (by omega)
  have := loop v.bits.length 0 (by omega) (Nat.zero_le _)
  rw [Nat.mul_zero, Nat.add_zero] at this
  rwa [show regs.set p pos = regs by rw [← hpos, set_getD_self hlen]] at this

/-! ### Skipping a clause -/

/-- The code moving the position in register `p` past the clause there, literal by literal. -/
def skipClauseCode (b p exit : ℕ) : List Instr :=
  [read (reg p) (b + 1) (b + 4) (b + 4)] ++ skipLitCode (b + 1) p b ++
    [assign p (add (reg p) (const 1)) exit]

/-- **Skipping a clause.** -/
theorem reaches_skipClauseCode {b p exit : ℕ} (hcode : P.CodeAt b (skipClauseCode b p exit))
    (hp : p ≠ 0) {regs : List ℕ} (hlen : p < regs.length) {pos : ℕ} {ls : Clause ℕ}
    (hls : LitsAt w pos ls) (hpos : regs.getD p 0 = pos) (hB : ∀ r ∈ regs, r ≤ B)
    (hend : pos + (ls.flatMap fun l => literalBits l.1 l.2).length + 1 ≤ B) :
    P.Reaches w (P.Oblivious B) (b, regs)
      (exit, regs.set p (pos + (ls.flatMap fun l => literalBits l.1 l.2).length + 1)) := by
  have hc := codeAt_append.mp hcode
  have hc' := codeAt_append.mp hc.1
  have h₀ : P.instr b = read (reg p) (b + 1) (b + 4) (b + 4) := (codeAt_cons.mp hc'.1).1
  have hskip : P.CodeAt (b + 1) (skipLitCode (b + 1) p b) := by simpa using hc'.2
  have h₄ : P.instr (b + 4) = assign p (add (reg p) (const 1)) exit := by
    simpa [skipLitCode] using (codeAt_cons.mp hc.2).1
  induction ls generalizing pos regs with
  | nil =>
    refine Reaches.oread h₀ (by simp [Expr.readsChoice, hp]) hB ?_
    simp only [eval_reg, hpos, hls.getElem?_nil, readLabel]
    refine Reaches.oassign h₄ hp (by simp [Expr.readsChoice, hp]) hB ?_
    simp only [eval_add, eval_reg, eval_const, hpos, List.flatMap_nil, List.length_nil,
      Nat.add_zero]
    exact Reaches.refl _
  | cons l ls ih =>
    obtain ⟨hl, hrest⟩ := hls.cons
    have hlB : pos + (literalBits l.1 l.2).length ≤ B := by
      simp only [List.flatMap_cons, List.length_append] at hend
      omega
    refine Reaches.oread h₀ (by simp [Expr.readsChoice, hp]) hB ?_
    simp only [eval_reg, hpos, hl.literal_start, readLabel]
    refine (reaches_skipLitCode hskip hp hlen hl hpos hB hlB).trans ?_
    have := ih (regs := regs.set p (pos + (literalBits l.1 l.2).length)) (by simpa using hlen)
      hrest (List.getD_set_self hlen) (List.forall_mem_set_of_forall_mem hB hlB)
      (by simp only [List.flatMap_cons, List.length_append] at hend; omega)
    rw [List.set_set] at this
    simpa [List.flatMap_cons, Nat.add_assoc] using this

/-! ### Comparing variables -/

/-- The code comparing the variables of the literals at the positions in registers `p₁` and `p₂`,
digit by digit, with cursors in registers `t₁` and `t₂`: it continues at `eq` when they are the
same variable and at `ne` otherwise. -/
def cmpVarCode (b p₁ p₂ t₁ t₂ eq ne : ℕ) : List Instr :=
  [assign t₁ (reg p₁) (b + 1),
   assign t₂ (reg p₂) (b + 2),
   read (add (reg t₁) (const 3)) (b + 3) (b + 4) (b + 4),
   read (add (reg t₂) (const 3)) (b + 5) ne ne,
   read (add (reg t₂) (const 3)) ne eq eq,
   read (add (reg t₁) (const 7)) (b + 6) (b + 7) (b + 7),
   read (add (reg t₂) (const 7)) (b + 8) ne ne,
   read (add (reg t₂) (const 7)) ne (b + 8) (b + 8),
   assign t₁ (add (reg t₁) (const 8)) (b + 9),
   assign t₂ (add (reg t₂) (const 8)) (b + 2)]

/-- The register list with the two variable-comparison cursors at digit `k`. -/
private abbrev cmpCur (regs : List ℕ) (t₁ t₂ pos₁ pos₂ k : ℕ) : List ℕ :=
  -- the cursors after `k` digits
  (regs.set t₁ (pos₁ + 8 * k)).set t₂ (pos₂ + 8 * k)

/-- Reading the first variable-comparison cursor at digit `k`. -/
private theorem getD_cmpCur_left {regs : List ℕ} {t₁ t₂ pos₁ pos₂ k : ℕ} (htt : t₁ ≠ t₂)
    (hlen₁ : t₁ < regs.length) : (cmpCur regs t₁ t₂ pos₁ pos₂ k).getD t₁ 0 = pos₁ + 8 * k := by
  simp only [cmpCur, List.getD_set_ne htt.symm, List.getD_set_self hlen₁]

/-- Reading the second variable-comparison cursor at digit `k`. -/
private theorem getD_cmpCur_right {regs : List ℕ} {t₁ t₂ pos₁ pos₂ k : ℕ}
    (hlen₂ : t₂ < regs.length) : (cmpCur regs t₁ t₂ pos₁ pos₂ k).getD t₂ 0 = pos₂ + 8 * k :=
  List.getD_set_self (by simpa using hlen₂)

section CmpVar

variable {b p₁ p₂ t₁ t₂ eq ne : ℕ} {regs : List ℕ} {pos₁ pos₂ v₁ v₂ k : ℕ} {s₁ s₂ : Bool}
  (hcode : P.CodeAt b (cmpVarCode b p₁ p₂ t₁ t₂ eq ne))
  (ht₁ : t₁ ≠ 0) (ht₂ : t₂ ≠ 0) (htt : t₁ ≠ t₂)
  (hlen₁ : t₁ < regs.length) (hlen₂ : t₂ < regs.length)
  (hl₁ : InfixAt w pos₁ (literalBits v₁ s₁)) (hl₂ : InfixAt w pos₂ (literalBits v₂ s₂))
  (hB : ∀ r ∈ regs, r ≤ B) (hend₁ : pos₁ + (literalBits v₁ s₁).length ≤ B)
  (hend₂ : pos₂ + (literalBits v₂ s₂).length ≤ B)

include hB hend₁ hend₂

/-- The registers remain bounded by `B` while the cursors advance through the two literals. -/
private theorem forall_mem_cmpCur (t₁ t₂ : ℕ) (hk₁ : k ≤ v₁.bits.length)
    (hk₂ : k ≤ v₂.bits.length) : ∀ r ∈ cmpCur regs t₁ t₂ pos₁ pos₂ k, r ≤ B := by
  rw [length_literalBits] at hend₁ hend₂
  exact List.forall_mem_set_of_forall_mem (List.forall_mem_set_of_forall_mem hB (by omega))
    (by omega)

include hcode ht₁ ht₂ htt hlen₁ hlen₂

/-- Advancing both variable-comparison cursors by `8` to the next digit. -/
private theorem reaches_cmpVarCode_advance (hk₁ : k < v₁.bits.length) (hk₂ : k < v₂.bits.length) :
    P.Reaches w (P.Oblivious B) (b + 8, cmpCur regs t₁ t₂ pos₁ pos₂ k)
      (b + 2, cmpCur regs t₁ t₂ pos₁ pos₂ (k + 1)) := by
  have hi (i : ℕ) (h : i < 10) := hcode i (by simp [cmpVarCode]; omega)
  have hB' := forall_mem_cmpCur hB hend₁ hend₂ t₁ t₂ hk₁.le hk₂.le
  have hc₁ := getD_cmpCur_left htt hlen₁ (pos₁ := pos₁) (pos₂ := pos₂) (k := k)
  have hc₂ := getD_cmpCur_right hlen₂ (t₁ := t₁) (pos₁ := pos₁) (pos₂ := pos₂) (k := k)
  rw [length_literalBits] at hend₁
  refine Reaches.oassign (hi 8 (by omega)) ht₁ (by simp [Expr.readsChoice, ht₁]) hB' ?_
  refine Reaches.oassign (hi 9 (by omega)) ht₂ (by simp [Expr.readsChoice, ht₂])
    (List.forall_mem_set_of_forall_mem hB' (by rw [eval_add, eval_reg, eval_const, hc₁]; omega)) ?_
  have e₁ : (add (reg t₁) (const 8)).eval (cmpCur regs t₁ t₂ pos₁ pos₂ k) =
      pos₁ + 8 * (k + 1) := by
    rw [eval_add, eval_reg, eval_const, hc₁]
    ring
  rw [e₁]
  have e₂ : (add (reg t₂) (const 8)).eval
      ((cmpCur regs t₁ t₂ pos₁ pos₂ k).set t₁ (pos₁ + 8 * (k + 1))) = pos₂ + 8 * (k + 1) := by
    rw [eval_add, eval_reg, eval_const, List.getD_set_ne htt, hc₂]
    ring
  rw [e₂]
  simp only [cmpCur]
  rw [List.set_comm _ _ htt.symm, List.set_set, List.set_set]
  exact Reaches.refl _

include hl₁ hl₂

/-- The end of the variable-comparison loop, once at least one variable has no more digits. -/
private theorem reaches_cmpVarCode_end (hk₁ : k ≤ v₁.bits.length) (hk₂ : k ≤ v₂.bits.length)
    (hmin : min v₁.bits.length v₂.bits.length ≤ k)
    (hpre : ∀ k' (h₁ : k' < v₁.bits.length) (h₂ : k' < v₂.bits.length), k' < k →
      v₁.bits[k'] = v₂.bits[k']) :
    P.Reaches w (P.Oblivious B) (b + 2, cmpCur regs t₁ t₂ pos₁ pos₂ k)
      (if v₁ = v₂ then eq else ne, cmpCur regs t₁ t₂ pos₁ pos₂ k) := by
  have hi (i : ℕ) (h : i < 10) := hcode i (by simp [cmpVarCode]; omega)
  have hB' := forall_mem_cmpCur hB hend₁ hend₂ t₁ t₂ hk₁ hk₂
  refine Reaches.oread (hi 2 (by omega)) (by simp [Expr.readsChoice, ht₁]) hB' ?_
  rcases lt_or_eq_of_le hk₁ with hk₁' | rfl
  · -- the first variable has more digits
    have hk₂' : k = v₂.bits.length := by omega
    simp only [eval_add, eval_reg, eval_const, getD_cmpCur_left htt hlen₁,
      (hl₁.literal_digit hk₁').2.1, readLabel]
    refine Reaches.oread (hi 3 (by omega)) (by simp [Expr.readsChoice, ht₂]) hB' ?_
    have hne : v₁ ≠ v₂ := fun h => by rw [h] at hk₁'; omega
    simp only [eval_add, eval_reg, eval_const, getD_cmpCur_right hlen₂, hk₂',
      hl₂.literal_end.2.1, readLabel, hne, ↓reduceIte]
    exact Reaches.refl _
  · simp only [eval_add, eval_reg, eval_const, getD_cmpCur_left htt hlen₁, hl₁.literal_end.2.1,
      readLabel]
    refine Reaches.oread (hi 4 (by omega)) (by simp [Expr.readsChoice, ht₂]) hB' ?_
    simp only [eval_add, eval_reg, eval_const, getD_cmpCur_right hlen₂]
    rcases lt_or_eq_of_le hk₂ with hk₂' | hk₂'
    · have hne : v₁ ≠ v₂ := fun h => by rw [h] at hk₂'; omega
      simp only [(hl₂.literal_digit hk₂').2.1, readLabel, hne, ↓reduceIte]
      exact Reaches.refl _
    · rw [show pos₂ + 8 * v₁.bits.length + 3 = pos₂ + 8 * v₂.bits.length + 3 by rw [hk₂']]
      have heq : v₁ = v₂ := Turing.MultiTapeTM.encNat.injective
        (by simpa using List.ext_getElem hk₂' fun k' h₁ h₂ => hpre k' h₁ h₂ h₁)
      simp only [hl₂.literal_end.2.1, readLabel, heq, ↓reduceIte]
      exact Reaches.refl _

/-- Comparing the `k`-th digits of the two variables when both have a `k`-th digit. -/
private theorem reaches_cmpVarCode_digit (hk₁ : k < v₁.bits.length) (hk₂ : k < v₂.bits.length) :
    P.Reaches w (P.Oblivious B) (b + 2, cmpCur regs t₁ t₂ pos₁ pos₂ k)
      (if v₁.bits[k] = v₂.bits[k] then b + 8 else ne, cmpCur regs t₁ t₂ pos₁ pos₂ k) := by
  have hi (i : ℕ) (h : i < 10) := hcode i (by simp [cmpVarCode]; omega)
  have hB' := forall_mem_cmpCur hB hend₁ hend₂ t₁ t₂ hk₁.le hk₂.le
  have hc₁ := getD_cmpCur_left htt hlen₁ (pos₁ := pos₁) (pos₂ := pos₂) (k := k)
  have hc₂ := getD_cmpCur_right hlen₂ (t₁ := t₁) (pos₁ := pos₁) (pos₂ := pos₂) (k := k)
  refine Reaches.oread (hi 2 (by omega)) (by simp [Expr.readsChoice, ht₁]) hB' ?_
  simp only [eval_add, eval_reg, eval_const, hc₁, (hl₁.literal_digit hk₁).2.1, readLabel]
  refine Reaches.oread (hi 3 (by omega)) (by simp [Expr.readsChoice, ht₂]) hB' ?_
  simp only [eval_add, eval_reg, eval_const, hc₂, (hl₂.literal_digit hk₂).2.1, readLabel]
  refine Reaches.oread (hi 5 (by omega)) (by simp [Expr.readsChoice, ht₁]) hB' ?_
  simp only [eval_add, eval_reg, eval_const, hc₁, (hl₁.literal_digit hk₁).2.2]
  have hd₂ : w[(add (reg t₂) (const 7)).eval (cmpCur regs t₁ t₂ pos₁ pos₂ k)]? =
      some v₂.bits[k] := by
    simp only [eval_add, eval_reg, eval_const, hc₂, (hl₂.literal_digit hk₂).2.2]
  cases h₁ : v₁.bits[k]
  · refine Reaches.oread (hi 7 (by omega)) (by simp [Expr.readsChoice, ht₂]) hB' ?_
    rw [hd₂]
    cases v₂.bits[k] <;> exact Reaches.refl _
  · refine Reaches.oread (hi 6 (by omega)) (by simp [Expr.readsChoice, ht₂]) hB' ?_
    rw [hd₂]
    cases v₂.bits[k] <;> exact Reaches.refl _

/-- The loop of `cmpVarCode` from digit `k` onward. -/
private theorem reaches_cmpVarCode_loop :
    ∀ e k, min v₁.bits.length v₂.bits.length - k = e →
      k ≤ v₁.bits.length → k ≤ v₂.bits.length →
      (∀ k' (h₁ : k' < v₁.bits.length) (h₂ : k' < v₂.bits.length), k' < k →
        v₁.bits[k'] = v₂.bits[k']) →
      ∃ x y, x ≤ B ∧ y ≤ B ∧ P.Reaches w (P.Oblivious B) (b + 2, cmpCur regs t₁ t₂ pos₁ pos₂ k)
        (if v₁ = v₂ then eq else ne, (regs.set t₁ x).set t₂ y) := by
  intro e
  induction e with
  | zero =>
    intro k he hk₁ hk₂ hpre
    have h₁ := hend₁
    have h₂ := hend₂
    rw [length_literalBits] at h₁ h₂
    exact ⟨pos₁ + 8 * k, pos₂ + 8 * k, by omega, by omega,
      reaches_cmpVarCode_end hcode ht₁ ht₂ htt hlen₁ hlen₂ hl₁ hl₂ hB hend₁ hend₂ hk₁ hk₂
        (by omega) hpre⟩
  | succ e ih =>
    intro k he hk₁ hk₂ hpre
    have hk₁' : k < v₁.bits.length := by omega
    have hk₂' : k < v₂.bits.length := by omega
    have hdig := reaches_cmpVarCode_digit hcode ht₁ ht₂ htt hlen₁ hlen₂ hl₁ hl₂ hB hend₁ hend₂
      hk₁' hk₂'
    by_cases hd : v₁.bits[k] = v₂.bits[k]
    · -- equal digits, then the next ones
      rw [ite_eq_left hd] at hdig
      obtain ⟨x, y, hx, hy, hreach⟩ := ih (k + 1) (by omega) (by omega) (by omega)
        fun k' h₁ h₂ hk' => (lt_or_eq_of_le (Nat.lt_succ_iff.mp hk')).elim (hpre k' h₁ h₂)
          fun h => h ▸ hd
      exact ⟨x, y, hx, hy, hdig.trans ((reaches_cmpVarCode_advance hcode ht₁ ht₂ htt hlen₁ hlen₂
        hB hend₁ hend₂ hk₁' hk₂').trans hreach)⟩
    · rw [ite_eq_right hd] at hdig
      have hne : v₁ ≠ v₂ := fun h => by subst h; exact hd rfl
      have h₁ := hend₁
      have h₂ := hend₂
      rw [length_literalBits] at h₁ h₂
      refine ⟨pos₁ + 8 * k, pos₂ + 8 * k, by omega, by omega, ?_⟩
      simpa [hne] using hdig

end CmpVar

/-- **Comparing variables**: the run ends at `eq` exactly when the variables are equal, with the
cursors within the literals. -/
theorem reaches_cmpVarCode {b p₁ p₂ t₁ t₂ eq ne : ℕ}
    (hcode : P.CodeAt b (cmpVarCode b p₁ p₂ t₁ t₂ eq ne))
    (hp₁ : p₁ ≠ 0) (hp₂ : p₂ ≠ 0) (ht₁ : t₁ ≠ 0) (ht₂ : t₂ ≠ 0) (htt : t₁ ≠ t₂)
    (ht₁p₂ : t₁ ≠ p₂) {regs : List ℕ} (hlen₁ : t₁ < regs.length) (hlen₂ : t₂ < regs.length)
    {pos₁ pos₂ v₁ v₂ : ℕ} {s₁ s₂ : Bool}
    (hl₁ : InfixAt w pos₁ (literalBits v₁ s₁)) (hl₂ : InfixAt w pos₂ (literalBits v₂ s₂))
    (hpos₁ : regs.getD p₁ 0 = pos₁) (hpos₂ : regs.getD p₂ 0 = pos₂) (hB : ∀ r ∈ regs, r ≤ B)
    (hend₁ : pos₁ + (literalBits v₁ s₁).length ≤ B)
    (hend₂ : pos₂ + (literalBits v₂ s₂).length ≤ B) :
    ∃ x y, x ≤ B ∧ y ≤ B ∧ P.Reaches w (P.Oblivious B) (b, regs)
      (if v₁ = v₂ then eq else ne, (regs.set t₁ x).set t₂ y) := by
  have hi (i : ℕ) (h : i < 10) := hcode i (by simp [cmpVarCode]; omega)
  obtain ⟨x, y, hx, hy, hreach⟩ := reaches_cmpVarCode_loop hcode ht₁ ht₂ htt hlen₁ hlen₂ hl₁ hl₂
    hB hend₁ hend₂ _ 0 rfl (Nat.zero_le _) (Nat.zero_le _)
    fun _ _ _ h => absurd h (Nat.not_lt_zero _)
  have h₁ := hend₁
  rw [length_literalBits] at h₁
  refine ⟨x, y, hx, hy, ?_⟩
  refine Reaches.oassign (hi 0 (by omega)) ht₁ (by simp [Expr.readsChoice, hp₁]) hB ?_
  refine Reaches.oassign (hi 1 (by omega)) ht₂ (by simp [Expr.readsChoice, hp₂])
    (List.forall_mem_set_of_forall_mem hB (by rw [eval_reg, hpos₁]; omega)) ?_
  simpa only [eval_reg, hpos₁, List.getD_set_ne ht₁p₂, hpos₂, cmpCur, Nat.mul_zero,
    Nat.add_zero] using hreach

/-! ### Reading the polarity -/

/-- The code reading the polarity of the literal at the position in register `p`, with a cursor
in register `t`: it continues at `yes` for a positive literal and at `no` otherwise. -/
def signCode (b p t yes no : ℕ) : List Instr :=
  [assign t (reg p) (b + 1),
   read (add (reg t) (const 3)) (b + 2) (b + 3) (b + 3),
   assign t (add (reg t) (const 8)) (b + 1),
   read (add (reg t) (const 7)) yes no no]

/-- **Reading the polarity.** -/
theorem reaches_signCode {b p t yes no : ℕ} (hcode : P.CodeAt b (signCode b p t yes no))
    (hp : p ≠ 0) (ht : t ≠ 0) {regs : List ℕ} (hlen : t < regs.length) {pos v : ℕ} {sgn : Bool}
    (hlit : InfixAt w pos (literalBits v sgn)) (hpos : regs.getD p 0 = pos)
    (hB : ∀ r ∈ regs, r ≤ B) (hend : pos + (literalBits v sgn).length ≤ B) :
    P.Reaches w (P.Oblivious B) (b, regs)
      (if sgn then yes else no, regs.set t (pos + 8 * v.bits.length)) := by
  simp only [signCode, codeAt_cons, codeAt_nil, and_true] at hcode
  obtain ⟨h₀, h₁, h₂, h₃⟩ := hcode
  rw [show b + 1 + 1 = b + 2 by omega] at h₂
  rw [show b + 1 + 1 + 1 = b + 3 by omega] at h₃
  rw [length_literalBits] at hend
  have hBk : ∀ k ≤ v.bits.length, ∀ r ∈ regs.set t (pos + 8 * k), r ≤ B := fun k hk =>
    List.forall_mem_set_of_forall_mem hB (by omega)
  have loop : ∀ e k, v.bits.length - k = e → k ≤ v.bits.length →
      P.Reaches w (P.Oblivious B) (b + 1, regs.set t (pos + 8 * k))
        (if sgn then yes else no, regs.set t (pos + 8 * v.bits.length)) := by
    intro e
    induction e with
    | zero =>
      intro k he hk
      obtain rfl : k = v.bits.length := by omega
      refine Reaches.oread h₁ (by simp [Expr.readsChoice, ht]) (hBk _ le_rfl) ?_
      simp only [eval_add, eval_reg, eval_const, List.getD_set_self hlen,
        hlit.literal_end.2.1, readLabel]
      refine Reaches.oread h₃ (by simp [Expr.readsChoice, ht]) (hBk _ le_rfl) ?_
      simp only [eval_add, eval_reg, eval_const, List.getD_set_self hlen,
        hlit.literal_end.2.2, readLabel]
      cases sgn <;> exact Reaches.refl _
    | succ e ih =>
      intro k he hk
      have hk' : k < v.bits.length := by omega
      refine Reaches.oread h₁ (by simp [Expr.readsChoice, ht]) (hBk _ hk) ?_
      simp only [eval_add, eval_reg, eval_const, List.getD_set_self hlen,
        (hlit.literal_digit hk').2.1, readLabel]
      refine Reaches.oassign h₂ ht (by simp [Expr.readsChoice, ht]) (hBk _ hk) ?_
      simp only [eval_add, eval_reg, eval_const, List.getD_set_self hlen, List.set_set]
      rw [show pos + 8 * k + 8 = pos + 8 * (k + 1) by ring]
      exact ih (k + 1) (by omega) (by omega)
  refine Reaches.oassign h₀ ht (by simp [Expr.readsChoice, hp]) hB ?_
  have := loop v.bits.length 0 (by omega) (Nat.zero_le _)
  simpa only [eval_reg, hpos, Nat.mul_zero, Nat.add_zero] using this

end TwoSAT

end Cslib.Complexity
