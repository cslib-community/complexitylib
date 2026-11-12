/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.ClosureKernel
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Block
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Kept
public import CslibFrontier.Logics.FirstOrder.Operator.DeterministicTransitiveClosure
public import CslibFrontier.Foundations.Relation.RelatesWithinSteps
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# The deterministic closure loop

`dtcCode` decides reachability of a target tuple from a source tuple along unique successors of
the relation computed by compiled body code, in a universe of size `n`. It keeps the current tuple
and a step counter and tests the current tuple against the target. Otherwise it enumerates every
candidate below `n ^ k`, decodes its base-`n` digits and runs the body, remembering the first
successor found. With no successor, or a second one, the walk stops and the loop exits false;
with exactly one, it becomes the current tuple and the step is counted. After `n ^ k` steps the
loop exits false. The loop is deterministic: the body code exits at one label when the body holds
and at another when it fails, so no inductive counting is needed.

## Main definitions

* `Cslib.Logic.FO.Ordered.DTCModelChecker.dtcCode`: the loop.

## Main results

* `Cslib.Logic.FO.Ordered.DTCModelChecker.reaches_dtcCode`: the loop decides
  `Relation.ReflTransGen (DTC.deterministicReduct E)` from the source to the target tuple.

## References

* [N. Immerman, *Languages That Capture Complexity Classes*, Theorem 4.2][Immerman1987]
-/

public section

namespace Cslib.Logic.FO.Ordered.DTCModelChecker

open Turing Turing.CounterProgram Turing.CounterProgram.Block Expr
open ClosureKernel

/-- The deterministic closure loop around compiled body code `body`, placed at `b`, with
registers from `base`: the current tuple at `base + i`, the candidate at `base + k + i`, the
candidate code at `base + 2 * k`, the step counter at `base + 2 * k + 1`, the found flag at
`base + 2 * k + 2` and the successor found at `base + 2 * k + 3`. The body code is placed at
`b + 2 * k + 6` and exits to `b + 2 * k + 6 + body.length` when the body holds, to three labels
later when it fails. The loop exits to `T` once the current tuple is `dst`, to `F` when the walk
stops or after `n ^ k` steps. -/
@[expose] def dtcCode (b base k : ℕ) (src dst : Fin k → Expr) (body : List Instr) (T F : ℕ) :
    List Instr :=
  assignsCode b base k (fun i => if h : i < k then src ⟨i, h⟩ else const 0) ++
  [.assign (base + 2 * k + 1) (const 0) (b + k + 1),
   .lt (const 0) (testExpr base k dst) (b + k + 2) T,
   .lt (reg (base + 2 * k + 1)) (pow (reg 0) k) (b + k + 3) F,
   .assign (base + 2 * k + 2) (const 0) (b + k + 4),
   .assign (base + 2 * k) (const 0) (b + k + 5),
   .lt (reg (base + 2 * k)) (pow (reg 0) k) (b + k + 6) (b + 2 * k + 10 + body.length)] ++
  assignsCode (b + k + 6) (base + k) k (digitE (base + 2 * k)) ++
  body ++
  [.lt (reg (base + 2 * k + 2)) (const 1) (b + 2 * k + 7 + body.length) F,
   .assign (base + 2 * k + 2) (const 1) (b + 2 * k + 8 + body.length),
   .assign (base + 2 * k + 3) (reg (base + 2 * k)) (b + 2 * k + 9 + body.length),
   .assign (base + 2 * k) (add (reg (base + 2 * k)) (const 1)) (b + k + 5),
   .lt (reg (base + 2 * k + 2)) (const 1) F (b + 2 * k + 11 + body.length)] ++
  assignsCode (b + 2 * k + 11 + body.length) base k (digitE (base + 2 * k + 3)) ++
  [.assign (base + 2 * k + 1) (add (reg (base + 2 * k + 1)) (const 1)) (b + k + 1)]

@[simp] theorem length_dtcCode (b base k : ℕ) (src dst : Fin k → Expr) (body : List Instr)
    (T F : ℕ) : (dtcCode b base k src dst body T F).length = 3 * k + 12 + body.length := by
  simp only [dtcCode, List.length_append, length_assignsCode, List.length_cons, List.length_nil]
  omega

/-- The instructions and blocks of `dtcCode`, at their labels. -/
theorem dtcCode_parts {P : CounterProgram} {b base k : ℕ} {src dst : Fin k → Expr}
    {body : List Instr} {T F : ℕ} (hP : P.CodeAt b (dtcCode b base k src dst body T F)) :
    P.CodeAt b (assignsCode b base k (fun i => if h : i < k then src ⟨i, h⟩ else const 0)) ∧
    P.instr (b + k) = .assign (base + 2 * k + 1) (const 0) (b + k + 1) ∧
    P.instr (b + k + 1) = .lt (const 0) (testExpr base k dst) (b + k + 2) T ∧
    P.instr (b + k + 2) = .lt (reg (base + 2 * k + 1)) (pow (reg 0) k) (b + k + 3) F ∧
    P.instr (b + k + 3) = .assign (base + 2 * k + 2) (const 0) (b + k + 4) ∧
    P.instr (b + k + 4) = .assign (base + 2 * k) (const 0) (b + k + 5) ∧
    P.instr (b + k + 5) =
      .lt (reg (base + 2 * k)) (pow (reg 0) k) (b + k + 6) (b + 2 * k + 10 + body.length) ∧
    P.CodeAt (b + k + 6) (assignsCode (b + k + 6) (base + k) k (digitE (base + 2 * k))) ∧
    P.CodeAt (b + 2 * k + 6) body ∧
    P.instr (b + 2 * k + 6 + body.length) =
      .lt (reg (base + 2 * k + 2)) (const 1) (b + 2 * k + 7 + body.length) F ∧
    P.instr (b + 2 * k + 7 + body.length) =
      .assign (base + 2 * k + 2) (const 1) (b + 2 * k + 8 + body.length) ∧
    P.instr (b + 2 * k + 8 + body.length) =
      .assign (base + 2 * k + 3) (reg (base + 2 * k)) (b + 2 * k + 9 + body.length) ∧
    P.instr (b + 2 * k + 9 + body.length) =
      .assign (base + 2 * k) (add (reg (base + 2 * k)) (const 1)) (b + k + 5) ∧
    P.instr (b + 2 * k + 10 + body.length) =
      .lt (reg (base + 2 * k + 2)) (const 1) F (b + 2 * k + 11 + body.length) ∧
    P.CodeAt (b + 2 * k + 11 + body.length)
      (assignsCode (b + 2 * k + 11 + body.length) base k (digitE (base + 2 * k + 3))) ∧
    P.instr (b + 3 * k + 11 + body.length) =
      .assign (base + 2 * k + 1) (add (reg (base + 2 * k + 1)) (const 1)) (b + k + 1) := by
  simp only [dtcCode, codeAt_append, codeAt_cons, List.length_append, length_assignsCode,
    List.length_cons, List.length_nil] at hP
  obtain ⟨⟨⟨⟨⟨⟨h1, h2, h3, h4, h5, h6, h7, -⟩, h8⟩, h9⟩, h10, h11, h12, h13, h14, -⟩, h15⟩,
    h16, -⟩ := hP
  refine ⟨h1, h2, ?_, ?_, ?_, ?_, ?_, codeAt_of_eq h8 (by omega), codeAt_of_eq h9 (by omega),
    ?_, ?_, ?_, ?_, ?_, codeAt_of_eq h15 (by omega), instr_of_eq h16 (by omega)⟩ <;>
    first
    | exact instr_of_eq h3 (by omega) | exact instr_of_eq h4 (by omega)
    | exact instr_of_eq h5 (by omega) | exact instr_of_eq h6 (by omega)
    | exact instr_of_eq h7 (by omega) | exact instr_of_eq h10 (by omega)
    | exact instr_of_eq h11 (by omega) | exact instr_of_eq h12 (by omega)
    | exact instr_of_eq h13 (by omega) | exact instr_of_eq h14 (by omega)

section Loop

variable {P : CounterProgram} {w : List Bool} {n B b base k T F : ℕ}
  {src dst : Fin k → Expr} {body : List Instr} {regs₀ : List ℕ}

variable (n B base k regs₀) in
/-- The invariant at the loop test: registers below `base` and the length are kept, the current
tuple is in registers `base + i` and the step counter is `m`. -/
private def MainInv (us : Fin k → Fin n) (m : ℕ) (regs : List ℕ) : Prop :=
  Kept B base regs₀ regs ∧ (∀ i : Fin k, regs.getD (base + i) 0 = us i) ∧
    regs.getD (base + 2 * k + 1) 0 = m

variable (n B base k regs₀) (E : (Fin k → Fin n) → (Fin k → Fin n) → Prop) in
/-- The invariant at the candidate test: candidates below `j` are scanned, and either the flag is
`0` and none of them is a successor, or the flag is `1` and exactly one of them is, its code in
register `base + 2 * k + 3`. -/
private def ScanInv (us : Fin k → Fin n) (m j : ℕ) (regs : List ℕ) : Prop :=
  MainInv n B base k regs₀ us m regs ∧ regs.getD (base + 2 * k) 0 = j ∧
    ((regs.getD (base + 2 * k + 2) 0 = 0 ∧
        ∀ y : Fin k → Fin n, (finFunctionFinEquiv y : ℕ) < j → ¬ E us y) ∨
      ∃ y : Fin k → Fin n, regs.getD (base + 2 * k + 2) 0 = 1 ∧
        regs.getD (base + 2 * k + 3) 0 = finFunctionFinEquiv y ∧
        (finFunctionFinEquiv y : ℕ) < j ∧ E us y ∧
        ∀ y' : Fin k → Fin n, (finFunctionFinEquiv y' : ℕ) < j → E us y' → y' = y)

/-- The invariant holds of registers with the same length, bounded by `B`, that agree on the
registers below `base + k` and on the step counter. -/
private theorem MainInv.of_agree {us : Fin k → Fin n} {m : ℕ} {regs regs' : List ℕ}
    (h : MainInv n B base k regs₀ us m regs) (hl : regs'.length = regs.length)
    (hB : ∀ r ∈ regs', r ≤ B)
    (hagree : ∀ j, (j < base + k ∨ j = base + 2 * k + 1) → regs'.getD j 0 = regs.getD j 0) :
    MainInv n B base k regs₀ us m regs' :=
  ⟨⟨hl.trans h.1.length_eq, fun i hi => (hagree i (by omega)).trans (h.1.getD_eq i hi), hB⟩,
    fun i => (hagree _ (by omega)).trans (h.2.1 i), (hagree _ (by omega)).trans h.2.2⟩

private theorem MainInv.set {us : Fin k → Fin n} {m : ℕ} {regs : List ℕ}
    (h : MainInv n B base k regs₀ us m regs) {j x : ℕ} (hj : base + 2 * k ≤ j)
    (hj' : j ≠ base + 2 * k + 1) (hx : x ≤ B) : MainInv n B base k regs₀ us m (regs.set j x) :=
  h.of_agree (List.length_set ..) (List.forall_mem_set_of_forall_mem h.1.bounded hx)
    fun i hi => List.getD_set_ne (by omega)

private theorem MainInv.kept {us : Fin k → Fin n} {m : ℕ} {regs regs' : List ℕ} {base' : ℕ}
    (h : MainInv n B base k regs₀ us m regs) (hk : Kept B base' regs regs')
    (hb : base + 2 * k + 2 ≤ base') : MainInv n B base k regs₀ us m regs' :=
  h.of_agree hk.length_eq hk.bounded fun i hi => hk.getD_eq i (by omega)

private theorem reaches_assign {c i : ℕ} {e : Expr} {next v : ℕ} {regs : List ℕ}
    {s' : Config} (hc : P.instr c = .assign i e next) (hB : ∀ r ∈ regs, r ≤ B)
    (he : e.eval regs = v) (h : P.Reaches w (P.Running B) (next, regs.set i v) s') :
    P.Reaches w (P.Running B) (c, regs) s' :=
  Reaches.assign hc hB (by rw [he]; exact h)

private theorem reaches_lt_yes {c : ℕ} {x y : Expr} {yes no : ℕ} {regs : List ℕ}
    {s' : Config} (hc : P.instr c = .lt x y yes no) (hB : ∀ r ∈ regs, r ≤ B)
    (hlt : x.eval regs < y.eval regs) (h : P.Reaches w (P.Running B) (yes, regs) s') :
    P.Reaches w (P.Running B) (c, regs) s' :=
  Reaches.lt hc hB (by rw [ite_eq_left hlt]; exact h)

private theorem reaches_lt_no {c : ℕ} {x y : Expr} {yes no : ℕ} {regs : List ℕ}
    {s' : Config} (hc : P.instr c = .lt x y yes no) (hB : ∀ r ∈ regs, r ≤ B)
    (hlt : ¬ x.eval regs < y.eval regs) (h : P.Reaches w (P.Running B) (no, regs) s') :
    P.Reaches w (P.Running B) (c, regs) s' :=
  Reaches.lt hc hB (by rw [ite_eq_right hlt]; exact h)

private theorem flag_lt_one {regs : List ℕ} {f x : ℕ} (hf : regs.getD f 0 = x) :
    (reg f).eval regs < (const 1).eval regs ↔ x = 0 := by
  rw [Expr.eval_reg, Expr.eval_const, hf]
  omega

variable {E : (Fin k → Fin n) → (Fin k → Fin n) → Prop}

/-- The candidate scan: from the candidate test with candidates below `j` scanned, the loop either
exits to `F` when the current tuple has no unique successor, or returns to the loop test with
the unique successor as current tuple and the step counted. -/
private theorem loop_scan (hP : P.CodeAt b (dtcCode b base k src dst body T F))
    (hbase : 0 < base) (hlen : base + 2 * k + 4 ≤ regs₀.length) (h0 : regs₀.getD 0 0 = n)
    (hNB : n ^ k ≤ B) (hnB : n ≤ B) (h1B : 1 ≤ B)
    (hbody : ∀ regs (us ys : Fin k → Fin n), Kept B base regs₀ regs →
      (∀ i : Fin k, regs.getD (base + i) 0 = us i) →
      (∀ i : Fin k, regs.getD (base + k + i) 0 = ys i) →
      ∃ (res : Bool) (regs' : List ℕ), (res = true ↔ E us ys) ∧
        P.Reaches w (P.Running B) (b + 2 * k + 6, regs)
          (if res then b + 2 * k + 6 + body.length else b + 2 * k + 9 + body.length, regs') ∧
        Kept B (base + 2 * k + 4) regs regs')
    (us : Fin k → Fin n) (m : ℕ) (hm : m < n ^ k) :
    ∀ e j (regs : List ℕ), n ^ k - j = e → j ≤ n ^ k → ScanInv n B base k regs₀ E us m j regs →
      ∃ regs', (P.Reaches w (P.Running B) (b + k + 5, regs) (F, regs') ∧
          Kept B base regs₀ regs' ∧ ∀ y, ¬ DTC.deterministicReduct E us y) ∨
        ∃ y, DTC.deterministicReduct E us y ∧
          P.Reaches w (P.Running B) (b + k + 5, regs) (b + k + 1, regs') ∧
          MainInv n B base k regs₀ y (m + 1) regs' := by
  obtain ⟨-, -, -, -, -, -, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := dtcCode_parts hP
  intro e
  induction e with
  | zero =>
    intro j regs he hj hscan
    obtain ⟨hmain, hc, hcase⟩ := hscan
    have hjN : j = n ^ k := by omega
    have hl : regs.length = regs₀.length := hmain.1.length_eq
    have hN : (pow (reg 0) k).eval regs = n ^ k :=
      eval_pow_reg0 ((hmain.1.getD_eq 0 hbase).trans h0)
    have hr₁ : P.Reaches w (P.Running B) (b + k + 5, regs)
        (b + 2 * k + 10 + body.length, regs) :=
      reaches_lt_no h7 hmain.1.bounded (by rw [Expr.eval_reg, hc, hN]; omega) (Reaches.refl _)
    rcases hcase with ⟨hf, hnone⟩ | ⟨y, hf, hs, -, hy, huniq⟩
    · refine ⟨regs, Or.inl ⟨hr₁.trans (reaches_lt_yes h14 hmain.1.bounded
        ((flag_lt_one hf).mpr rfl) (Reaches.refl _)), hmain.1,
        fun y hy => hnone y (hjN ▸ (finFunctionFinEquiv y).isLt) hy.1⟩⟩
    · obtain ⟨regs₁, hr₂, hl₁, hout₁, hin₁, hB₁⟩ := reaches_digitsCode (w := w) h15
        (by omega) hbase (by omega) ((hmain.1.getD_eq 0 hbase).trans h0) hnB hmain.1.bounded
        (finFunctionFinEquiv y) hs
      have ht₁ : regs₁.getD (base + 2 * k + 1) 0 = m := by
        rw [hout₁ _ (by omega), hmain.2.2]
      refine ⟨regs₁.set (base + 2 * k + 1) (m + 1), Or.inr ⟨y, ⟨hy, fun y' hy' => huniq y'
        (hjN ▸ (finFunctionFinEquiv y').isLt) hy'⟩, ?_, ?_⟩⟩
      · refine hr₁.trans (reaches_lt_no h14 hmain.1.bounded
          (fun h => absurd ((flag_lt_one hf).mp h) one_ne_zero) (hr₂.trans ?_))
        refine reaches_assign (instr_of_eq h16 (by omega)) hB₁
          (by rw [Expr.eval_add, Expr.eval_reg, Expr.eval_const, ht₁]) (Reaches.refl _)
      · refine ⟨⟨by rw [List.length_set, hl₁, hl], fun i hi => ?_,
          List.forall_mem_set_of_forall_mem hB₁ (by omega)⟩, fun i => ?_, ?_⟩
        · rw [List.getD_set_ne (by omega), hout₁ i (by omega), hmain.1.getD_eq i hi]
        · rw [List.getD_set_ne (by omega), hin₁ i, Equiv.symm_apply_apply]
        · exact List.getD_set_self (by rw [hl₁, hl]; omega)
  | succ e ih =>
    intro j regs he hj hscan
    obtain ⟨hmain, hc, hcase⟩ := hscan
    have hjN : j < n ^ k := by omega
    have hl : regs.length = regs₀.length := hmain.1.length_eq
    have hr0 : regs.getD 0 0 = n := (hmain.1.getD_eq 0 hbase).trans h0
    obtain ⟨ys, hys⟩ : ∃ ys : Fin k → Fin n, (finFunctionFinEquiv ys : ℕ) = j :=
      ⟨finFunctionFinEquiv.symm ⟨j, hjN⟩, by rw [Equiv.apply_symm_apply]⟩
    have hsym : finFunctionFinEquiv.symm ⟨j, hjN⟩ = ys :=
      finFunctionFinEquiv.symm_apply_eq.mpr (Fin.ext hys.symm)
    -- decode the candidate
    obtain ⟨regs₁, hr₁, hl₁, hout₁, hin₁, hB₁⟩ := reaches_digitsCode (w := w) h8
      (by omega) (by omega) (by omega) hr0 hnB hmain.1.bounded ⟨j, hjN⟩ hc
    have hY₁ : ∀ i : Fin k, regs₁.getD (base + k + i) 0 = ys i := fun i => by
      rw [hin₁ i, hsym]
    have hmain₁ : MainInv n B base k regs₀ us m regs₁ :=
      hmain.of_agree hl₁ hB₁ fun i hi => hout₁ i (by omega)
    -- run the body
    obtain ⟨res, regs₂, hres, hr₂, hk₂⟩ :=
      hbody regs₁ us ys hmain₁.1 hmain₁.2.1 hY₁
    have hmain₂ : MainInv n B base k regs₀ us m regs₂ := hmain₁.kept hk₂ (by omega)
    have hl₂ : regs₂.length = regs₀.length := hmain₂.1.length_eq
    have hB₂ : ∀ r ∈ regs₂, r ≤ B := hk₂.bounded
    have hc₂ : regs₂.getD (base + 2 * k) 0 = j := by
      rw [hk₂.getD_eq _ (by omega), hout₁ _ (by omega), hc]
    have hf₂ : regs₂.getD (base + 2 * k + 2) 0 = regs.getD (base + 2 * k + 2) 0 := by
      rw [hk₂.getD_eq _ (by omega), hout₁ _ (by omega)]
    have hs₂ : regs₂.getD (base + 2 * k + 3) 0 = regs.getD (base + 2 * k + 3) 0 := by
      rw [hk₂.getD_eq _ (by omega), hout₁ _ (by omega)]
    have hpre : P.Reaches w (P.Running B) (b + k + 5, regs)
        (if res then b + 2 * k + 6 + body.length else b + 2 * k + 9 + body.length, regs₂) :=
      reaches_lt_yes h7 hmain.1.bounded (by rw [Expr.eval_reg, hc, eval_pow_reg0 hr0]; exact hjN)
        (hr₁.trans (by rw [show b + k + 6 + k = b + 2 * k + 6 by omega]; exact hr₂))
    -- continue the scan with the next candidate
    have he' : n ^ k - (j + 1) = e := by rw [Nat.sub_add_eq, he, Nat.add_sub_cancel]
    have cont : ∀ regs₃, P.Reaches w (P.Running B) (b + k + 5, regs) (b + k + 5, regs₃) →
        ScanInv n B base k regs₀ E us m (j + 1) regs₃ →
        ∃ regs', (P.Reaches w (P.Running B) (b + k + 5, regs) (F, regs') ∧
            Kept B base regs₀ regs' ∧ ∀ y, ¬ DTC.deterministicReduct E us y) ∨
          ∃ y, DTC.deterministicReduct E us y ∧
            P.Reaches w (P.Running B) (b + k + 5, regs) (b + k + 1, regs') ∧
            MainInv n B base k regs₀ y (m + 1) regs' := fun regs₃ hr₃ hscan₃ => by
      obtain ⟨regs', h | ⟨y, hy, hr', hinv'⟩⟩ := ih (j + 1) regs₃ he' hjN hscan₃
      · exact ⟨regs', Or.inl ⟨hr₃.trans h.1, h.2⟩⟩
      · exact ⟨regs', Or.inr ⟨y, hy, hr₃.trans hr', hinv'⟩⟩
    cases res with
    | true =>
      have hE : E us ys := hres.mp rfl
      rw [ite_eq_left rfl] at hpre
      rcases hcase with ⟨hf, hnone⟩ | ⟨y, hf, hs, hyj, hy, huniq⟩
      · -- the first successor: record it
        have hmain₃ : MainInv n B base k regs₀ us m
            (((regs₂.set (base + 2 * k + 2) 1).set (base + 2 * k + 3) j).set (base + 2 * k)
              (j + 1)) :=
          ((hmain₂.set (j := base + 2 * k + 2) (by omega) (by omega) h1B).set
            (j := base + 2 * k + 3) (by omega) (by omega) (by omega)).set
            (j := base + 2 * k) le_rfl (by omega) (by omega)
        refine cont _ (hpre.trans (reaches_lt_yes h10 hB₂ ((flag_lt_one (hf₂.trans hf)).mpr rfl)
          (reaches_assign h11 hB₂ (v := 1) (Expr.eval_const ..)
          (reaches_assign h12 (List.forall_mem_set_of_forall_mem hB₂ h1B) (v := j)
            (by rw [Expr.eval_reg, List.getD_set_ne (by omega), hc₂])
          (reaches_assign h13 (List.forall_mem_set_of_forall_mem
              (List.forall_mem_set_of_forall_mem hB₂ h1B) (by omega)) (v := j + 1)
            (by rw [Expr.eval_add, Expr.eval_reg, Expr.eval_const, List.getD_set_ne (by omega),
              List.getD_set_ne (by omega), hc₂]) (Reaches.refl _)))))) ⟨hmain₃, ?_, Or.inr
          ⟨ys, ?_, ?_, by omega, hE, fun y' hy' hE' => ?_⟩⟩
        · exact List.getD_set_self (by simp only [List.length_set]; omega)
        · rw [List.getD_set_ne (by omega), List.getD_set_ne (by omega),
            List.getD_set_self (by omega)]
        · rw [List.getD_set_ne (by omega),
            List.getD_set_self (by simp only [List.length_set]; omega), hys]
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hy' with hlt | heq
          · exact absurd hE' (hnone y' hlt)
          · exact finFunctionFinEquiv.injective (Fin.ext (heq.trans hys.symm))
      · -- a second successor: the walk stops
        refine ⟨regs₂, Or.inl ⟨hpre.trans (reaches_lt_no h10 hB₂
          (fun h => one_ne_zero ((flag_lt_one (hf₂.trans hf)).mp h)) (Reaches.refl _)),
          hmain₂.1, fun y'' hD => ?_⟩⟩
        have h1 : y = y'' := hD.2 y hy
        have h2 : ys = y'' := hD.2 ys hE
        have : (finFunctionFinEquiv y : ℕ) = finFunctionFinEquiv ys := by rw [h1, h2]
        omega
    | false =>
      have hE : ¬ E us ys := fun h => Bool.false_ne_true (hres.mpr h)
      rw [ite_eq_right Bool.false_ne_true] at hpre
      refine cont _ (hpre.trans (reaches_assign h13 hB₂ (v := j + 1)
        (by rw [Expr.eval_add, Expr.eval_reg, Expr.eval_const, hc₂]) (Reaches.refl _)))
        ⟨hmain₂.set (j := base + 2 * k) le_rfl (by omega) (by omega),
          List.getD_set_self (by omega), ?_⟩
      rw [List.getD_set_ne (by omega), List.getD_set_ne (by omega), hf₂, hs₂]
      rcases hcase with ⟨hf, hnone⟩ | ⟨y, hf, hs, hyj, hy, huniq⟩
      · refine Or.inl ⟨hf, fun y' hy' hE' => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hy' with hlt | heq
        · exact hnone y' hlt hE'
        · exact hE (finFunctionFinEquiv.injective (Fin.ext (heq.trans hys.symm)) ▸ hE')
      · refine Or.inr ⟨y, hf, hs, by omega, hy, fun y' hy' hE' => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hy' with hlt | heq
        · exact huniq y' hlt hE'
        · exact absurd (finFunctionFinEquiv.injective (Fin.ext (heq.trans hys.symm)) ▸ hE') hE

private theorem loop_test_eq (hP : P.CodeAt b (dtcCode b base k src dst body T F))
    {us z₀ : Fin k → Fin n} {m : ℕ} {regs : List ℕ} (hinv : MainInv n B base k regs₀ us m regs)
    (hdst : ∀ regs, (∀ j < base, regs.getD j 0 = regs₀.getD j 0) → ∀ i, (dst i).eval regs = z₀ i)
    (heq : us = z₀) : P.Reaches w (P.Running B) (b + k + 1, regs) (T, regs) := by
  obtain ⟨-, -, h3, -⟩ := dtcCode_parts hP
  exact reaches_lt_no h3 hinv.1.bounded
    (fun h => (lt_eval_testExpr hinv.2.1 (hdst regs hinv.1.getD_eq)).mp h heq) (Reaches.refl _)

private theorem loop_test_ne (hP : P.CodeAt b (dtcCode b base k src dst body T F))
    {us z₀ : Fin k → Fin n} {m : ℕ} {regs : List ℕ} (hinv : MainInv n B base k regs₀ us m regs)
    (hdst : ∀ regs, (∀ j < base, regs.getD j 0 = regs₀.getD j 0) → ∀ i, (dst i).eval regs = z₀ i)
    (hne : us ≠ z₀) : P.Reaches w (P.Running B) (b + k + 1, regs) (b + k + 2, regs) := by
  obtain ⟨-, -, h3, -⟩ := dtcCode_parts hP
  exact reaches_lt_yes h3 hinv.1.bounded
    ((lt_eval_testExpr hinv.2.1 (hdst regs hinv.1.getD_eq)).mpr hne) (Reaches.refl _)

/-- The main loop: from the loop test after `m` steps, the loop decides whether the target is
reachable along unique successors within the remaining `n ^ k - m` steps. -/
private theorem loop_main (hP : P.CodeAt b (dtcCode b base k src dst body T F))
    (hbase : 0 < base) (hlen : base + 2 * k + 4 ≤ regs₀.length) (h0 : regs₀.getD 0 0 = n)
    (hNB : n ^ k ≤ B) (hnB : n ≤ B) (h1B : 1 ≤ B)
    {z₀ : Fin k → Fin n}
    (hdst : ∀ regs, (∀ j < base, regs.getD j 0 = regs₀.getD j 0) → ∀ i, (dst i).eval regs = z₀ i)
    (hbody : ∀ regs (us ys : Fin k → Fin n), Kept B base regs₀ regs →
      (∀ i : Fin k, regs.getD (base + i) 0 = us i) →
      (∀ i : Fin k, regs.getD (base + k + i) 0 = ys i) →
      ∃ (res : Bool) (regs' : List ℕ), (res = true ↔ E us ys) ∧
        P.Reaches w (P.Running B) (b + 2 * k + 6, regs)
          (if res then b + 2 * k + 6 + body.length else b + 2 * k + 9 + body.length, regs') ∧
        Kept B (base + 2 * k + 4) regs regs') :
    ∀ e m (us : Fin k → Fin n) (regs : List ℕ), n ^ k - m = e → m ≤ n ^ k →
      MainInv n B base k regs₀ us m regs →
      ∃ (res : Bool) (regs' : List ℕ),
        (res = true ↔
          Relation.RelatesWithinSteps (DTC.deterministicReduct E) us z₀ (n ^ k - m)) ∧
        P.Reaches w (P.Running B) (b + k + 1, regs) (if res then T else F, regs') ∧
        Kept B base regs₀ regs' := by
  obtain ⟨-, -, -, h4, h5, h6, -⟩ := dtcCode_parts hP
  have hat : ∀ m (us : Fin k → Fin n) (regs : List ℕ), MainInv n B base k regs₀ us m regs →
      us = z₀ → ∃ (res : Bool) (regs' : List ℕ),
        (res = true ↔
          Relation.RelatesWithinSteps (DTC.deterministicReduct E) us z₀ (n ^ k - m)) ∧
        P.Reaches w (P.Running B) (b + k + 1, regs) (if res then T else F, regs') ∧
        Kept B base regs₀ regs' := fun m us regs hinv heq =>
    ⟨true, regs, iff_of_true rfl ⟨0, Nat.zero_le _, Relation.RelatesInSteps.zero_iff.mpr heq⟩,
      loop_test_eq hP hinv hdst heq, hinv.1⟩
  intro e
  induction e with
  | zero =>
    intro m us regs he hm hinv
    by_cases heq : us = z₀
    · exact hat m us regs hinv heq
    refine ⟨false, regs, iff_of_false Bool.false_ne_true fun h => heq ?_,
      (loop_test_ne hP hinv hdst heq).trans (reaches_lt_no h4 hinv.1.bounded
        (by rw [Expr.eval_reg, hinv.2.2, eval_pow_reg0 ((hinv.1.getD_eq 0 hbase).trans h0)]; omega)
        (Reaches.refl _)), hinv.1⟩
    rw [show n ^ k - m = 0 by omega] at h
    exact Relation.RelatesWithinSteps.zero h
  | succ e ih =>
    intro m us regs he hm hinv
    by_cases heq : us = z₀
    · exact hat m us regs hinv heq
    have hmN : m < n ^ k := by omega
    have hl : regs.length = regs₀.length := hinv.1.length_eq
    have hscan : ScanInv n B base k regs₀ E us m 0
        ((regs.set (base + 2 * k + 2) 0).set (base + 2 * k) 0) :=
      ⟨(hinv.set (j := base + 2 * k + 2) (by omega) (by omega) (Nat.zero_le _)).set
          (j := base + 2 * k) le_rfl (by omega) (Nat.zero_le _),
        List.getD_set_self (by simp only [List.length_set]; omega),
        Or.inl ⟨by rw [List.getD_set_ne (by omega), List.getD_set_self (by omega)],
          fun y hy => absurd hy (Nat.not_lt_zero _)⟩⟩
    have hr : P.Reaches w (P.Running B) (b + k + 1, regs)
        (b + k + 5, (regs.set (base + 2 * k + 2) 0).set (base + 2 * k) 0) :=
      (loop_test_ne hP hinv hdst heq).trans (reaches_lt_yes h4 hinv.1.bounded
        (by rw [Expr.eval_reg, hinv.2.2, eval_pow_reg0 ((hinv.1.getD_eq 0 hbase).trans h0)]
            exact hmN)
        (reaches_assign h5 hinv.1.bounded (Expr.eval_const ..)
          (reaches_assign h6 (List.forall_mem_set_of_forall_mem hinv.1.bounded (Nat.zero_le _))
            (Expr.eval_const ..) (Reaches.refl _))))
    obtain ⟨regs', ⟨hr', hk', hnone⟩ | ⟨y, hD, hr', hinv'⟩⟩ :=
      loop_scan hP hbase hlen h0 hNB hnB h1B hbody us m hmN _ 0 _ rfl (Nat.zero_le _) hscan
    · refine ⟨false, regs', iff_of_false Bool.false_ne_true ?_, hr.trans hr', hk'⟩
      rintro ⟨i, -, hi⟩
      cases i with
      | zero => exact heq hi.zero
      | succ i =>
        obtain ⟨t, ht, -⟩ := Relation.RelatesInSteps.succ'_iff.mp hi
        exact hnone t ht
    · obtain ⟨res, regs'', hres, hr'', hk''⟩ :=
        ih (m + 1) y regs' (by omega) hmN hinv'
      refine ⟨res, regs'', ?_, (hr.trans hr').trans hr'', hk''⟩
      rw [hres, show n ^ k - m = n ^ k - (m + 1) + 1 by omega,
        Relation.RelatesWithinSteps.succ_iff_of_unique hD
          (fun y' hy' => DTC.rightUnique_deterministicReduct E hy' hD) heq]

end Loop

/-- **The deterministic closure loop decides deterministic reachability.** Given compiled body
code deciding a relation `E` on `k`-tuples over a universe of size `n`, and source and target
expressions denoting `s₀` and `z₀`, the loop reaches `T` exactly when `z₀` is reachable from `s₀`
along unique `E`-successors, and otherwise `F`, keeping the registers below `base`. -/
theorem reaches_dtcCode {P : CounterProgram} {w : List Bool} {n B b base k T F : ℕ}
    {src dst : Fin k → Expr} {body : List Instr} {regs₀ : List ℕ}
    (hP : P.CodeAt b (dtcCode b base k src dst body T F))
    (hbase : 0 < base) (hlen : base + 2 * k + 4 ≤ regs₀.length) (h0 : regs₀.getD 0 0 = n)
    (hNB : n ^ k ≤ B) (hnB : n ≤ B) (h1B : 1 ≤ B) (hB : ∀ r ∈ regs₀, r ≤ B)
    {s₀ z₀ : Fin k → Fin n}
    (hsrc : ∀ regs, (∀ j < base, regs.getD j 0 = regs₀.getD j 0) → ∀ i, (src i).eval regs = s₀ i)
    (hdst : ∀ regs, (∀ j < base, regs.getD j 0 = regs₀.getD j 0) → ∀ i, (dst i).eval regs = z₀ i)
    {E : (Fin k → Fin n) → (Fin k → Fin n) → Prop}
    (hbody : ∀ regs (us ys : Fin k → Fin n), Kept B base regs₀ regs →
      (∀ i : Fin k, regs.getD (base + i) 0 = us i) →
      (∀ i : Fin k, regs.getD (base + k + i) 0 = ys i) →
      ∃ (res : Bool) (regs' : List ℕ), (res = true ↔ E us ys) ∧
        P.Reaches w (P.Running B) (b + 2 * k + 6, regs)
          (if res then b + 2 * k + 6 + body.length else b + 2 * k + 9 + body.length, regs') ∧
        Kept B (base + 2 * k + 4) regs regs') :
    ∃ (res : Bool) (regs' : List ℕ),
      (res = true ↔ Relation.ReflTransGen (DTC.deterministicReduct E) s₀ z₀) ∧
      P.Reaches w (P.Running B) (b, regs₀) (if res then T else F, regs') ∧
      Kept B base regs₀ regs' := by
  obtain ⟨h1, h2, -⟩ := dtcCode_parts hP
  obtain ⟨regs₁, hr₁, hl₁, hout₁, hin₁, hB₁⟩ := reaches_loadCode (w := w) h1
    (by omega) hnB hB hsrc
  have hinv : MainInv n B base k regs₀ s₀ 0 (regs₁.set (base + 2 * k + 1) 0) :=
    ⟨⟨by rw [List.length_set, hl₁], fun i hi => by rw [List.getD_set_ne (by omega),
        hout₁ i (by omega)], List.forall_mem_set_of_forall_mem hB₁ (Nat.zero_le _)⟩,
      fun i => by rw [List.getD_set_ne (by omega), hin₁ i],
      List.getD_set_self (by omega)⟩
  obtain ⟨res, regs', hres, hr', hk'⟩ :=
    loop_main hP hbase hlen h0 hNB hnB h1B hdst hbody _ 0 s₀ _ rfl (Nat.zero_le _) hinv
  refine ⟨res, regs', ?_, hr₁.trans (reaches_assign h2 hB₁ (Expr.eval_const ..) hr'), hk'⟩
  have hcard : Nat.card (Fin k → Fin n) ≤ n ^ k + 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    omega
  rw [hres, Nat.sub_zero, Relation.reflTransGen_iff_relatesWithinSteps hcard]

end Cslib.Logic.FO.Ordered.DTCModelChecker
