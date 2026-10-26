/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram
public import Complexity.Logics.FirstOrder.Basic
import Complexity.Foundations.Data.List.Lookup

/-!
# Shared first-order counter-program control

Compile Mathlib first-order formulas using one counter per bound variable. Equality compares
compiled term expressions; relation atoms execute a single supplied branch/read instruction.
Implication and universal quantification use the existing fixed-control model-checking recursion.
The atomic-handler correctness hypothesis is discharged by each concrete model checker.

This factors the control proof of the original order-free model checker without changing its
code lengths, quantifier order or empty-universe behavior.

## Main definitions

* `Cslib.Logic.FO.boundDepth`: the register depth of a bounded formula.
* `Cslib.Logic.Vocabulary.ModelChecker.AtomicCompiler`: term and relation handlers.
* `Cslib.Logic.Vocabulary.ModelChecker.formulaCodeWith`: shared formula compilation.

## Main results

* `Cslib.Logic.Vocabulary.ModelChecker.reaches_formulaCodeWith`: semantic correctness and
  register preservation, from the actual atomic-handler proofs.

## References

* [N. Immerman, *Descriptive Complexity*, Theorem 3.1][Immerman1999].
-/

@[expose] public section

universe u v

open FirstOrder Language Structure Turing Turing.CounterProgram

namespace Cslib.Logic

namespace FO

variable {L : Language.{u, v}}

/-- The number of bound variables in scope at the deepest point of a formula: the nesting depth of
its quantifiers, plus the number of bound variables in scope at the formula itself. -/
def boundDepth {α : Type*} : ∀ {k : ℕ}, L.BoundedFormula α k → ℕ
  | k, .falsum => k
  | k, .equal _ _ => k
  | k, .rel _ _ => k
  | _, .imp φ ψ => max (boundDepth φ) (boundDepth ψ)
  | _, .all φ => boundDepth φ

theorem le_boundDepth {α : Type*} : ∀ {k : ℕ} (φ : L.BoundedFormula α k), k ≤ boundDepth φ
  | _, .falsum => le_rfl
  | _, .equal _ _ => le_rfl
  | _, .rel _ _ => le_rfl
  | _, .imp φ _ => (le_boundDepth φ).trans (le_max_left _ _)
  | _, .all φ => (Nat.le_succ _).trans (le_boundDepth φ)

end FO

namespace Vocabulary.ModelChecker

open FO Expr

variable {L : Language.{u, v}}

/-- Compile terms to arithmetic expressions and relations to one branch/read instruction.
The handlers do not change registers. Their semantics are proved by `AtomicCompiler.Correct`. -/
structure AtomicCompiler (L : Language.{u, v}) (α : Type*) where
  /-- The expression computing a term, for every number of bound variables. -/
  term : ∀ {k : ℕ}, L.Term (α ⊕ Fin k) → Expr
  /-- The instruction branching on a relation atom. -/
  rel : ∀ {k r : ℕ}, L.Relations r → (Fin r → L.Term (α ⊕ Fin k)) → ℕ → ℕ → Instr

/-- The atomic handlers realize terms and relations in a concrete input structure, without
changing the assignment registers. This is an internal compiler specification, not a hypothesis
of the concrete query-language membership theorems. -/
structure AtomicCompiler.Correct {α : Type*} (C : AtomicCompiler L α) {n : ℕ}
    [L.Structure (Fin n)] (w : List Bool) (fv : α → ℕ) (base : ℕ) (val : α → Fin n) : Prop where
  /-- Term expressions compute the canonical natural index. -/
  term : ∀ {k : ℕ} (regs : List ℕ) (xs : Fin k → Fin n), regs.getD 0 0 = n →
    (∀ x, regs.getD (fv x) 0 = val x) →
    (∀ i : Fin k, regs.getD (base + i) 0 = xs i) →
    ∀ t, (C.term t).eval regs = (t.realize (Sum.elim val xs) : Fin n)
  /-- A relation instruction selects exactly its semantic branch. -/
  rel : ∀ {k r : ℕ} (R : L.Relations r) (ts : Fin r → L.Term (α ⊕ Fin k))
    (P : CounterProgram) (b T F B : ℕ) (regs : List ℕ) (xs : Fin k → Fin n),
    regs.getD 0 0 = n → (∀ x, regs.getD (fv x) 0 = val x) →
    (∀ i : Fin k, regs.getD (base + i) 0 = xs i) → (∀ x ∈ regs, x ≤ B) →
    P.instr b = C.rel R ts T F →
    ∃ res : Bool, (res = true ↔ RelMap R (fun i => (ts i).realize (Sum.elim val xs))) ∧
      P.Reaches w (P.Running B) (b, regs) (if res then T else F, regs)

/-- The number of instructions compiled from a formula
(`Cslib.Logic.Vocabulary.ModelChecker.formulaCodeWith`). -/
def codeLength {α : Type*} : ∀ {k : ℕ}, L.BoundedFormula α k → ℕ
  | _, .falsum => 1
  | _, .equal _ _ => 2
  | _, .rel _ _ => 1
  | _, .imp φ ψ => codeLength φ + codeLength ψ
  | _, .all φ => codeLength φ + 4

/-- The code evaluating a formula with free variables `α` and `k` bound variables, placed at the
label `b`: with the cardinality in register `0`, the values expected by the atomic handlers,
and the bound variable `i` in register `base + i`, it goes to `T` if the formula holds and to `F`
otherwise. A quantifier over the bound variable `k` loops over the values of
register `base + k` below the cardinality; equality compares two compiled expressions, and a
relation uses its supplied branch instruction. -/
def formulaCodeWith {α : Type*} (C : AtomicCompiler L α) (base : ℕ) :
    ∀ {k : ℕ}, L.BoundedFormula α k → ℕ → ℕ → ℕ → List Instr
  | _, .falsum, _, _, F => [.lt (const 0) (const 0) F F]
  | _, .equal t₁ t₂, b, T, F =>
    [.lt (C.term t₁) (C.term t₂) F (b + 1),
     .lt (C.term t₂) (C.term t₁) F T]
  | _, .rel R ts, _, T, F =>
    [C.rel R ts T F]
  | _, .imp φ ψ, b, T, F =>
    formulaCodeWith C base φ b (b + codeLength φ) T ++
      formulaCodeWith C base ψ (b + codeLength φ) T F
  | k, .all φ, b, T, F =>
    [.lt (const 0) (reg 0) (b + 1) T,
     .assign (base + k) (const 0) (b + 3),
     .lt (add (reg (base + k)) (const 1)) (reg 0) (b + 3 + codeLength φ) T] ++
    formulaCodeWith C base φ (b + 3) (b + 2) F ++
    [.assign (base + k) (add (reg (base + k)) (const 1)) (b + 3)]

theorem length_formulaCodeWith {α : Type*} (C : AtomicCompiler L α) (base : ℕ) :
    ∀ {k : ℕ} (φ : L.BoundedFormula α k) (b T F : ℕ),
      (formulaCodeWith C base φ b T F).length = codeLength φ
  | _, .falsum, _, _, _ => rfl
  | _, .equal _ _, _, _, _ => rfl
  | _, .rel _ _, _, _, _ => rfl
  | _, .imp φ ψ, _, _, _ => by
    simp only [formulaCodeWith, List.length_append, length_formulaCodeWith, codeLength]
  | _, .all φ, _, _, _ => by
    simp only [formulaCodeWith, List.length_append, length_formulaCodeWith, codeLength,
      List.length_cons, List.length_nil]
    omega

section Reaches

variable {P : CounterProgram} {w : List Bool} {n B : ℕ} [L.Structure (Fin n)] {α : Type*}
  {fv : α → ℕ} {base : ℕ} {val : α → Fin n} {C : AtomicCompiler L α}

private theorem reaches_formulaCodeWith_equal (hC : C.Correct w fv base val) {k : ℕ}
    (t₁ t₂ : L.Term (α ⊕ Fin k)) (b T F : ℕ) (regs : List ℕ) (xs : Fin k → Fin n)
    (hP : P.CodeAt b (formulaCodeWith C base (.equal t₁ t₂) b T F))
    (h0 : regs.getD 0 0 = n) (hB : ∀ r ∈ regs, r ≤ B) (hv : ∀ x, regs.getD (fv x) 0 = val x)
    (hxs : ∀ i : Fin k, regs.getD (base + i) 0 = xs i) :
    ∃ (res : Bool) (regs' : List ℕ),
      (res = true ↔ (BoundedFormula.equal t₁ t₂).Realize val xs) ∧
      P.Reaches w (P.Running B) (b, regs) (if res then T else F, regs') ∧
      regs'.length = regs.length ∧ (∀ i < base + k, regs'.getD i 0 = regs.getD i 0) ∧
      ∀ r ∈ regs', r ≤ B := by
  simp only [formulaCodeWith, codeAt_cons] at hP
  obtain ⟨h₀, h₁, -⟩ := hP
  have e₁ := hC.term regs xs h0 hv hxs t₁
  have e₂ := hC.term regs xs h0 hv hxs t₂
  refine ⟨decide (t₁.realize (Sum.elim val xs) = t₂.realize (Sum.elim val xs)), regs,
    by simp only [decide_eq_true_eq]; rfl, ?_, rfl, fun _ _ => rfl, hB⟩
  refine Reaches.lt h₀ hB ?_
  simp only [e₁, e₂]
  rcases lt_trichotomy (t₁.realize (Sum.elim val xs)) (t₂.realize (Sum.elim val xs)) with
    hlt | heq | hgt
  · simpa [hlt, hlt.ne] using Reaches.refl _
  · simp only [heq, lt_irrefl, ↓reduceIte, decide_true]
    exact Reaches.lt h₁ hB (by simp only [e₁, e₂, heq, lt_irrefl, ↓reduceIte]; exact Reaches.refl _)
  · simp only [show ¬ (((t₁.realize (Sum.elim val xs) : Fin n) : ℕ) <
        (t₂.realize (Sum.elim val xs) : Fin n)) from
      not_lt.mpr (Fin.le_iff_val_le_val.mp hgt.le), ↓reduceIte, hgt.ne', decide_false]
    exact Reaches.lt h₁ hB (by
      simp only [e₁, e₂, Fin.lt_def.mp hgt, ↓reduceIte, Bool.false_eq_true]; exact Reaches.refl _)

private theorem reaches_formulaCodeWith_imp (hbase : 0 < base) (hfv : ∀ x, fv x < base)
    {k : ℕ} (φ ψ : L.BoundedFormula α k) (b T F : ℕ) (regs : List ℕ) (xs : Fin k → Fin n)
    (hP : P.CodeAt b (formulaCodeWith C base (.imp φ ψ) b T F))
    (hd : base + boundDepth (.imp φ ψ) ≤ regs.length)
    (h0 : regs.getD 0 0 = n) (hB : ∀ r ∈ regs, r ≤ B) (hv : ∀ x, regs.getD (fv x) 0 = val x)
    (hxs : ∀ i : Fin k, regs.getD (base + i) 0 = xs i)
    (ihφ : ∀ b T F (regs : List ℕ) (xs : Fin k → Fin n),
      P.CodeAt b (formulaCodeWith C base φ b T F) →
      base + boundDepth φ ≤ regs.length → regs.getD 0 0 = n → (∀ r ∈ regs, r ≤ B) →
      (∀ x, regs.getD (fv x) 0 = val x) → (∀ i : Fin k, regs.getD (base + i) 0 = xs i) →
      ∃ (res : Bool) (regs' : List ℕ), (res = true ↔ φ.Realize val xs) ∧
        P.Reaches w (P.Running B) (b, regs) (if res then T else F, regs') ∧
        regs'.length = regs.length ∧ (∀ i < base + k, regs'.getD i 0 = regs.getD i 0) ∧
        ∀ r ∈ regs', r ≤ B)
    (ihψ : ∀ b T F (regs : List ℕ) (xs : Fin k → Fin n),
      P.CodeAt b (formulaCodeWith C base ψ b T F) →
      base + boundDepth ψ ≤ regs.length → regs.getD 0 0 = n → (∀ r ∈ regs, r ≤ B) →
      (∀ x, regs.getD (fv x) 0 = val x) → (∀ i : Fin k, regs.getD (base + i) 0 = xs i) →
      ∃ (res : Bool) (regs' : List ℕ), (res = true ↔ ψ.Realize val xs) ∧
        P.Reaches w (P.Running B) (b, regs) (if res then T else F, regs') ∧
        regs'.length = regs.length ∧ (∀ i < base + k, regs'.getD i 0 = regs.getD i 0) ∧
        ∀ r ∈ regs', r ≤ B) :
    ∃ (res : Bool) (regs' : List ℕ),
      (res = true ↔ (φ.imp ψ).Realize val xs) ∧
      P.Reaches w (P.Running B) (b, regs) (if res then T else F, regs') ∧
      regs'.length = regs.length ∧ (∀ i < base + k, regs'.getD i 0 = regs.getD i 0) ∧
      ∀ r ∈ regs', r ≤ B := by
  simp only [formulaCodeWith, codeAt_append, length_formulaCodeWith] at hP
  have hd₁ : base + boundDepth φ ≤ regs.length :=
    (Nat.add_le_add_left (le_max_left _ _) base).trans hd
  have hd₂ : base + boundDepth ψ ≤ regs.length :=
    (Nat.add_le_add_left (le_max_right _ _) base).trans hd
  obtain ⟨r₁, regs₁, hr₁, hreach₁, hlen₁, hkeep₁, hB₁⟩ :=
    ihφ b (b + codeLength φ) T regs xs hP.1 hd₁ h0 hB hv hxs
  cases r₁ with
  | false =>
    refine ⟨true, regs₁, ?_, by simpa using hreach₁, hlen₁, hkeep₁, hB₁⟩
    simp only [BoundedFormula.realize_imp, true_iff]
    exact fun h => absurd (hr₁.mpr h) (by simp)
  | true =>
    obtain ⟨r₂, regs₂, hr₂, hreach₂, hlen₂, hkeep₂, hB₂⟩ :=
      ihψ (b + codeLength φ) T F regs₁ xs hP.2 (hlen₁ ▸ hd₂)
        (by rw [hkeep₁ 0 (by omega), h0]) hB₁
        (fun x => by rw [hkeep₁ _ (by have := hfv x; omega), hv])
        (fun i => by rw [hkeep₁ _ (by omega), hxs])
    refine ⟨r₂, regs₂, ?_,
      (show P.Reaches _ _ _ (b + codeLength φ, regs₁) by simpa using hreach₁).trans hreach₂,
      hlen₂.trans hlen₁, fun i hi => (hkeep₂ i hi).trans (hkeep₁ i hi), hB₂⟩
    rw [BoundedFormula.realize_imp, hr₂]
    exact ⟨fun h _ => h, fun h => h (hr₁.mp rfl)⟩

private theorem reaches_formulaCodeWith_all_loop (hnB : n ≤ B) (hbase : 0 < base)
    (hfv : ∀ x, fv x < base) {k : ℕ} (φ : L.BoundedFormula α (k + 1)) (b T F : ℕ)
    (regs : List ℕ) (xs : Fin k → Fin n)
    (hc₂ : P.instr (b + 2) =
      .lt (add (reg (base + k)) (const 1)) (reg 0) (b + 3 + codeLength φ) T)
    (hc₃ : P.instr (b + 3 + codeLength φ) =
      .assign (base + k) (add (reg (base + k)) (const 1)) (b + 3))
    (hcφ : P.CodeAt (b + 3) (formulaCodeWith C base φ (b + 3) (b + 2) F))
    (hd : base + boundDepth φ ≤ regs.length) (hk : base + k < regs.length)
    (h0 : regs.getD 0 0 = n) (hv : ∀ x, regs.getD (fv x) 0 = val x)
    (hxs : ∀ i : Fin k, regs.getD (base + i) 0 = xs i)
    (ihφ : ∀ b T F (regs : List ℕ) (xs' : Fin (k + 1) → Fin n),
      P.CodeAt b (formulaCodeWith C base φ b T F) →
      base + boundDepth φ ≤ regs.length → regs.getD 0 0 = n → (∀ r ∈ regs, r ≤ B) →
      (∀ x, regs.getD (fv x) 0 = val x) → (∀ i : Fin (k + 1), regs.getD (base + i) 0 = xs' i) →
      ∃ (res : Bool) (regs' : List ℕ), (res = true ↔ φ.Realize val xs') ∧
        P.Reaches w (P.Running B) (b, regs) (if res then T else F, regs') ∧
        regs'.length = regs.length ∧ (∀ i < base + (k + 1), regs'.getD i 0 = regs.getD i 0) ∧
        ∀ r ∈ regs', r ≤ B) :
    ∀ e m (hm : m < n) (regsm : List ℕ), n - m = e →
      regsm.length = regs.length → (∀ i < base + k, regsm.getD i 0 = regs.getD i 0) →
      regsm.getD (base + k) 0 = m → (∀ r ∈ regsm, r ≤ B) →
      (∀ m' (hm' : m' < m), φ.Realize val (Fin.snoc xs ⟨m', hm'.trans hm⟩)) →
      ∃ (res : Bool) (regs' : List ℕ),
        (res = true ↔ ∀ y : Fin n, φ.Realize val (Fin.snoc xs y)) ∧
        P.Reaches w (P.Running B) (b + 3, regsm) (if res then T else F, regs') ∧
        regs'.length = regs.length ∧ (∀ i < base + k, regs'.getD i 0 = regs.getD i 0) ∧
        ∀ r ∈ regs', r ≤ B
  | 0, m, hm, _, he, _, _, _, _, _ => by omega
  | e + 1, m, hm, regsm, he, hlenm, hkeepm, hvm, hBm, hprev => by
    have hxs' (i : Fin (k + 1)) : regsm.getD (base + i) 0 =
        (Fin.snoc xs ⟨m, hm⟩ : Fin (k + 1) → Fin n) i :=
      i.lastCases (by simpa using hvm) fun i => by
        rw [Fin.snoc_castSucc, Fin.val_castSucc, hkeepm _ (by omega), hxs]
    obtain ⟨r₁, regs₁, hr₁, hreach₁, hlen₁, hkeep₁, hB₁⟩ :=
      ihφ (b + 3) (b + 2) F regsm (Fin.snoc xs ⟨m, hm⟩) hcφ (by omega)
        (by rw [hkeepm 0 (by omega), h0]) hBm
        (fun x => by rw [hkeepm _ (by have := hfv x; omega), hv]) hxs'
    cases r₁ with
    | false =>
      refine ⟨false, regs₁, ?_, by simpa using hreach₁, hlen₁.trans hlenm,
        fun i hi => (hkeep₁ i (by omega)).trans (hkeepm i hi), hB₁⟩
      simp only [Bool.false_eq_true, false_iff, not_forall]
      exact ⟨⟨m, hm⟩, fun h => absurd (hr₁.mpr h) (by simp)⟩
    | true =>
      have hv₁ : regs₁.getD (base + k) 0 = m := by rw [hkeep₁ _ (by omega), hvm]
      have h0₁ : regs₁.getD 0 0 = n := by rw [hkeep₁ 0 (by omega), hkeepm 0 (by omega), h0]
      have hprev' (m' : ℕ) (hm' : m' < m + 1) : φ.Realize val (Fin.snoc xs ⟨m', by omega⟩) :=
        (lt_or_eq_of_le (Nat.lt_succ_iff.mp hm')).elim (hprev m') (fun h => h ▸ hr₁.mp rfl)
      have hr₁' : P.Reaches w (P.Running B) (b + 3, regsm) (b + 2, regs₁) := by simpa using hreach₁
      by_cases hnext : m + 1 < n
      · obtain ⟨r, regs', hr, hreach, hlen, hkeep, hB'⟩ :=
          reaches_formulaCodeWith_all_loop hnB hbase hfv φ b T F regs xs hc₂ hc₃ hcφ hd hk h0 hv
            hxs ihφ e (m + 1) hnext (regs₁.set (base + k) (m + 1)) (by omega)
            (by rw [List.length_set, hlen₁, hlenm])
            (fun i hi => by rw [List.getD_set_ne (by omega), hkeep₁ i (by omega), hkeepm i hi])
            (List.getD_set_self (by rw [hlen₁, hlenm]; exact hk))
            (List.forall_mem_set_of_forall_mem hB₁ (by omega)) hprev'
        refine ⟨r, regs', hr, hr₁'.trans (Reaches.lt hc₂ hB₁ ?_), hlen, hkeep, hB'⟩
        simp only [eval_add, eval_reg, eval_const, hv₁, h0₁, hnext, ↓reduceIte]
        exact Reaches.assign hc₃ hB₁
          (by simpa only [eval_add, eval_reg, eval_const, hv₁] using hreach)
      · refine ⟨true, regs₁, by simpa using fun y : Fin n => hprev' y (by omega),
          hr₁'.trans (Reaches.lt hc₂ hB₁ ?_), hlen₁.trans hlenm,
          fun i hi => (hkeep₁ i (by omega)).trans (hkeepm i hi), hB₁⟩
        simp only [eval_add, eval_reg, eval_const, hv₁, h0₁, hnext, ↓reduceIte]
        exact Reaches.refl _

private theorem reaches_formulaCodeWith_all (hnB : n ≤ B) (hbase : 0 < base)
    (hfv : ∀ x, fv x < base) {k : ℕ} (φ : L.BoundedFormula α (k + 1)) (b T F : ℕ)
    (regs : List ℕ) (xs : Fin k → Fin n)
    (hP : P.CodeAt b (formulaCodeWith C base (.all φ) b T F))
    (hd : base + boundDepth (.all φ) ≤ regs.length)
    (h0 : regs.getD 0 0 = n) (hB : ∀ r ∈ regs, r ≤ B) (hv : ∀ x, regs.getD (fv x) 0 = val x)
    (hxs : ∀ i : Fin k, regs.getD (base + i) 0 = xs i)
    (ihφ : ∀ b T F (regs : List ℕ) (xs' : Fin (k + 1) → Fin n),
      P.CodeAt b (formulaCodeWith C base φ b T F) →
      base + boundDepth φ ≤ regs.length → regs.getD 0 0 = n → (∀ r ∈ regs, r ≤ B) →
      (∀ x, regs.getD (fv x) 0 = val x) → (∀ i : Fin (k + 1), regs.getD (base + i) 0 = xs' i) →
      ∃ (res : Bool) (regs' : List ℕ), (res = true ↔ φ.Realize val xs') ∧
        P.Reaches w (P.Running B) (b, regs) (if res then T else F, regs') ∧
        regs'.length = regs.length ∧ (∀ i < base + (k + 1), regs'.getD i 0 = regs.getD i 0) ∧
        ∀ r ∈ regs', r ≤ B) :
    ∃ (res : Bool) (regs' : List ℕ),
      (res = true ↔ φ.all.Realize val xs) ∧
      P.Reaches w (P.Running B) (b, regs) (if res then T else F, regs') ∧
      regs'.length = regs.length ∧ (∀ i < base + k, regs'.getD i 0 = regs.getD i 0) ∧
      ∀ r ∈ regs', r ≤ B := by
  simp only [formulaCodeWith, codeAt_append, codeAt_cons, List.length_cons, List.length_nil] at hP
  obtain ⟨⟨⟨hc₀, hc₁, hc₂, -⟩, hcφ⟩, hc₃, -⟩ := hP
  rw [show b + 1 + 1 = b + 2 by omega] at hc₂
  rw [show b + (0 + 1 + 1 + 1) = b + 3 by omega] at hcφ
  rw [List.length_append, length_formulaCodeWith] at hc₃
  simp only [List.length_cons, List.length_nil] at hc₃
  rw [show b + (0 + 1 + 1 + 1 + codeLength φ) = b + 3 + codeLength φ by omega] at hc₃
  have hk : base + k < regs.length := by
    have := le_boundDepth φ; simp only [boundDepth] at hd; omega
  by_cases hn : 0 < n
  · obtain ⟨res, regs', hres, hreach, hlen, hkeep, hB'⟩ :=
      reaches_formulaCodeWith_all_loop hnB hbase hfv φ b T F regs xs hc₂ hc₃ hcφ hd hk h0 hv hxs
        ihφ (n - 0) 0 hn (regs.set (base + k) 0) rfl (by rw [List.length_set])
        (fun i hi => List.getD_set_ne (by omega)) (List.getD_set_self hk)
        (List.forall_mem_set_of_forall_mem hB (Nat.zero_le _))
        (fun m' hm' => absurd hm' (Nat.not_lt_zero _))
    refine ⟨res, regs', by rw [hres, BoundedFormula.realize_all], ?_, hlen, hkeep, hB'⟩
    refine Reaches.lt hc₀ hB ?_
    simp only [eval_const, eval_reg, h0, hn, ↓reduceIte]
    exact Reaches.assign hc₁ hB (by simpa using hreach)
  · refine ⟨true, regs, ?_, ?_, rfl, fun _ _ => rfl, hB⟩
    · simp only [true_iff, BoundedFormula.realize_all]; exact fun y => absurd y.2 (by omega)
    · refine Reaches.lt hc₀ hB ?_
      simp only [eval_const, eval_reg, h0, hn, ↓reduceIte]; exact Reaches.refl _

end Reaches

/-- Compiled first-order control evaluates the formula and preserves the registers below the
current bound-variable scope. Only the atomic handlers depend on the input vocabulary/model. -/
theorem reaches_formulaCodeWith {P : CounterProgram} {w : List Bool} {n B : ℕ}
    [L.Structure (Fin n)] (hnB : n ≤ B) {α : Type*} (fv : α → ℕ) (base : ℕ)
    (hbase : 0 < base) (hfv : ∀ x, fv x < base) (val : α → Fin n)
    (C : AtomicCompiler L α) (hC : C.Correct w fv base val) :
    ∀ {k : ℕ} (φ : L.BoundedFormula α k) (b T F : ℕ) (regs : List ℕ) (xs : Fin k → Fin n),
      P.CodeAt b (formulaCodeWith C base φ b T F) → base + boundDepth φ ≤ regs.length →
      regs.getD 0 0 = n → (∀ r ∈ regs, r ≤ B) → (∀ x, regs.getD (fv x) 0 = val x) →
      (∀ i : Fin k, regs.getD (base + i) 0 = xs i) →
      ∃ (res : Bool) (regs' : List ℕ),
        (res = true ↔ φ.Realize val xs) ∧
        P.Reaches w (P.Running B) (b, regs) (if res then T else F, regs') ∧
        regs'.length = regs.length ∧ (∀ i < base + k, regs'.getD i 0 = regs.getD i 0) ∧
        ∀ r ∈ regs', r ≤ B
  | _, .falsum, b, T, F, regs, xs, hP, _, _, hB, _, _ => by
    simp only [formulaCodeWith, codeAt_cons] at hP
    exact ⟨false, regs, by simp [BoundedFormula.Realize],
      Reaches.lt hP.1 hB (by simpa using Reaches.refl _), rfl, fun _ _ => rfl, hB⟩
  | _, .equal t₁ t₂, b, T, F, regs, xs, hP, _, h0, hB, hv, hxs =>
    reaches_formulaCodeWith_equal hC t₁ t₂ b T F regs xs hP h0 hB hv hxs
  | _, .rel R ts, b, T, F, regs, xs, hP, _, h0, hB, hv, hxs => by
    obtain ⟨res, hres, hreach⟩ := hC.rel R ts P b T F B regs xs h0 hv hxs hB (codeAt_cons.mp hP).1
    exact ⟨res, regs, hres, hreach, rfl, fun _ _ => rfl, hB⟩
  | _, .imp φ ψ, b, T, F, regs, xs, hP, hd, h0, hB, hv, hxs =>
    reaches_formulaCodeWith_imp hbase hfv φ ψ b T F regs xs hP hd h0 hB hv hxs
      (reaches_formulaCodeWith hnB fv base hbase hfv val C hC φ)
      (reaches_formulaCodeWith hnB fv base hbase hfv val C hC ψ)
  | _, .all φ, b, T, F, regs, xs, hP, hd, h0, hB, hv, hxs =>
    reaches_formulaCodeWith_all hnB hbase hfv φ b T F regs xs hP hd h0 hB hv hxs
      (reaches_formulaCodeWith hnB fv base hbase hfv val C hC φ)

end Vocabulary.ModelChecker

end Cslib.Logic
