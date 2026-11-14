/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.DeterministicTransitiveClosure.Loop
public import CslibFrontier.Logics.FirstOrder.Operator.TransitiveClosure.Positive
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# Compiling FO(DTC) formulas to deterministic counter code

A formula over the canonical ordered language with closure operators, read with deterministic
closure `DTC.interpretation`, is compiled to deterministic counter code that exits at one label
when the formula holds and at another when it fails. First-order subformulas reuse the ordered
first-order checker. Negation swaps the two exits, conjunction runs its conjuncts in sequence,
and an existential quantifier tries the values of its variable in increasing order. A closure
becomes the loop `dtcCode` around the compiled code of its body.

Every block exits on both truth values, so unlike the FO(TC) compiler there is no polarity index
and a negated closure needs no inductive counting.

## Main definitions

* `Cslib.Logic.FO.Ordered.DTCModelChecker.compile`: the compiler.
* `Cslib.Logic.FO.Ordered.DTCModelChecker.Env`, `Cslib.Logic.FO.Ordered.DTCModelChecker.Correct`:
  the hypotheses and statement of compiler correctness.

## Main results

* `Cslib.Logic.FO.Ordered.DTCModelChecker.correct`: compiler correctness for every formula
  without free relation variables.

## References

* [N. Immerman, *Languages That Capture Complexity Classes*, Theorem 4.2][Immerman1987]
-/

public section

universe u v w

open FirstOrder Language

namespace Cslib.Logic.FO.Ordered.DTCModelChecker

open Turing Turing.CounterProgram Turing.CounterProgram.Block Expr Vocabulary.ModelChecker
open Operator (Formula RelEnv)
open ClosureKernel

variable {L : Language.{u, v}} [L.IsRelational] (v : Vocabulary L)

/-- The scratch registers used by the compiled code of a formula, above its free variables. -/
@[expose] def scratch : {Γ : List ℕ} → {α : Type w} → Formula (language L) TC.shape Γ α → ℕ
  | _, _, .ofFO φ => boundDepth φ
  | _, _, .rel _ _ => 0
  | _, _, .neg φ => scratch φ
  | _, _, .conj φ ψ => Max.max (scratch φ) (scratch ψ)
  | _, _, .ex φ => scratch φ + 1
  | _, _, .op k body _ => 2 * k + 4 + scratch (body ⟨0, Nat.one_pos⟩)

/-- The number of instructions compiled from a formula. -/
@[expose] def len : {Γ : List ℕ} → {α : Type w} → Formula (language L) TC.shape Γ α → ℕ
  | _, _, .ofFO φ => codeLength φ
  | _, _, .rel _ _ => 0
  | _, _, .neg φ => len φ
  | _, _, .conj φ ψ => len φ + len ψ
  | _, _, .ex φ => len φ + 3
  | _, _, .op k body _ => 3 * k + 12 + len (body ⟨0, Nat.one_pos⟩)

/-- The code for a formula, placed at `b`, with the free variable `x` in register `fv x` and
scratch registers from `base`. It exits to `T` when the formula holds and to `F` when it fails.
An existential quantifier tries the values of its variable, held in register `base`, in increasing
order. A closure of width `k` is the loop `dtcCode` with the compiled body above the loop's
`2 * k + 4` registers. A relation variable compiles to no code; it does not occur in a formula
without free relation variables. -/
@[expose] def compile : {Γ : List ℕ} → {α : Type w} → (α → ℕ) → ℕ →
    Formula (language L) TC.shape Γ α → ℕ → ℕ → ℕ → List Instr
  | _, _, fv, base, .ofFO φ, b, T, F => ModelChecker.formulaCode v fv base φ b T F
  | _, _, _, _, .rel _ _, _, _, _ => []
  | _, _, fv, base, .neg φ, b, T, F => compile fv base φ b F T
  | _, _, fv, base, .conj φ ψ, b, T, F =>
    compile fv base φ b (b + len φ) F ++ compile fv base ψ (b + len φ) T F
  | _, _, fv, base, .ex φ, b, T, F =>
    [.assign base (const 0) (b + 1),
     .lt (reg base) (reg 0) (b + 2) F] ++
    compile (fun x => x.elim base fv) (base + 1) φ (b + 2) T (b + 2 + len φ) ++
    [.assign base (add (reg base) (const 1)) (b + 1)]
  | _, α, fv, base, .op k body args, b, T, F =>
    dtcCode b base k (fun i => termE fv (TC.left args i)) (fun i => termE fv (TC.right args i))
      (compile (α := α ⊕ Fin ((TC.shape k).binder ⟨0, Nat.one_pos⟩).vars)
        (Sum.elim fv fun i => base + i.val) (base + 2 * k + 4) (body ⟨0, Nat.one_pos⟩)
        (b + 2 * k + 6) (b + 2 * k + 6 + len (body ⟨0, Nat.one_pos⟩))
        (b + 2 * k + 9 + len (body ⟨0, Nat.one_pos⟩))) T F

theorem length_compile : ∀ {Γ : List ℕ} {α : Type w} (fv : α → ℕ) (base : ℕ)
    (φ : Formula (language L) TC.shape Γ α) (b T F : ℕ),
    (compile v fv base φ b T F).length = len φ
  | _, _, fv, base, .ofFO φ, b, T, F => by
    simp only [compile, len, ModelChecker.formulaCode, length_formulaCodeWith]
  | _, _, _, _, .rel _ _, _, _, _ => rfl
  | _, _, fv, base, .neg φ, b, T, F => length_compile fv base φ b F T
  | _, _, fv, base, .conj φ ψ, b, T, F => by
    simp only [compile, len, List.length_append, length_compile]
  | _, _, fv, base, .ex φ, b, T, F => by
    simp only [compile, len, List.length_append, length_compile, List.length_cons,
      List.length_nil]
    omega
  | _, _, fv, base, .op k body args, b, T, F => by
    simp only [compile, len, length_dtcCode]
    rw [length_compile]

variable {v}

section Correct

variable {a : EncodedStructure} [L.Structure (Fin a.1)] [Fact (2 ≤ a.1)]
  {P : CounterProgram} {B : ℕ}

variable (v a B) in
/-- The hypotheses of the compiler correctness proof: correct atomic handlers, and a register
bound `B` dominating `1` and the cardinality. -/
structure Env : Prop where
  atomic : ∀ {β : Type} (fv : β → ℕ) (base : ℕ) (val : β → Fin a.1),
    (ModelChecker.atomicCompiler v fv base).Correct (encStructure a) fv base val
  one_le : 1 ≤ B
  card_le : a.1 ≤ B

variable (v a P B) in
/-- The compiled code of `φ` is correct: run with the free variables in their registers and
enough scratch registers, it exits to `T` exactly when `φ` holds and to `F` otherwise, keeping
the registers below `base` and every register at most `B`. -/
@[expose] def Correct {Γ : List ℕ} {α : Type} (φ : Formula (language L) TC.shape Γ α) : Prop :=
  Γ = [] → a.1 ^ TC.width φ ≤ B →
  ∀ (fv : α → ℕ) (base : ℕ) (val : α → Fin a.1) (ρ : RelEnv Γ (Fin a.1)) (b T F : ℕ)
    (regs : List ℕ),
    P.CodeAt b (compile v fv base φ b T F) → 0 < base → (∀ x, fv x < base) →
    base + scratch φ ≤ regs.length → regs.getD 0 0 = a.1 →
    (∀ x, regs.getD (fv x) 0 = val x) → (∀ r ∈ regs, r ≤ B) →
    ∃ (res : Bool) (regs' : List ℕ), (res = true ↔ φ.Realize DTC.interpretation ρ val) ∧
      P.Reaches (encStructure a) (P.Running B) (b, regs) (if res then T else F, regs') ∧
      Kept B base regs regs'

theorem correct_ofFO (hE : Env v a B) {Γ : List ℕ} {α : Type} (φ : (language L).Formula α) :
    Correct v a P B (Formula.ofFO (shape := TC.shape) (Γ := Γ) φ) := by
  intro _ _ fv base val ρ b T F regs hP hbase hfv hd h0 hv hregs
  obtain ⟨res, regs', hres, hreach, hk⟩ :=
    reaches_formulaCodeWith hE.card_le fv base hbase hfv val _ (hE.atomic fv base val) φ b T F
      regs default hP hd h0 hregs hv (fun i => i.elim0)
  exact ⟨res, regs', hres, hreach, hk.mono (Nat.le_add_right _ _)⟩

theorem correct_neg {Γ : List ℕ} {α : Type} {φ : Formula (language L) TC.shape Γ α}
    (ih : Correct v a P B φ) : Correct v a P B φ.neg := by
  intro hΓ hW fv base val ρ b T F regs hP hbase hfv hd h0 hv hregs
  obtain ⟨res, regs', hres, hreach, hk⟩ :=
    ih hΓ hW fv base val ρ b F T regs hP hbase hfv hd h0 hv hregs
  refine ⟨!res, regs', ?_, ?_, hk⟩
  · cases res
    · exact iff_of_true rfl fun h => Bool.false_ne_true (hres.mpr h)
    · exact iff_of_false Bool.false_ne_true fun h => h (hres.mp rfl)
  · cases res <;> exact hreach

theorem correct_conj {Γ : List ℕ} {α : Type} {φ ψ : Formula (language L) TC.shape Γ α}
    (ihφ : Correct v a P B φ) (ihψ : Correct v a P B ψ) : Correct v a P B (φ.conj ψ) := by
  intro hΓ hW fv base val ρ b T F regs hP hbase hfv hd h0 hv hregs
  have hn : 0 < a.1 := by have := (Fact.out : 2 ≤ a.1); omega
  have hWφ : a.1 ^ TC.width φ ≤ B := (Nat.pow_le_pow_right hn (le_max_left _ _)).trans hW
  have hWψ : a.1 ^ TC.width ψ ≤ B := (Nat.pow_le_pow_right hn (le_max_right _ _)).trans hW
  have hdφ : base + scratch φ ≤ regs.length := (Nat.add_le_add_left (le_max_left _ _) _).trans hd
  have hdψ : base + scratch ψ ≤ regs.length :=
    (Nat.add_le_add_left (le_max_right _ _) _).trans hd
  have hP' : P.CodeAt b (compile v fv base φ b (b + len φ) F ++
      compile v fv base ψ (b + len φ) T F) := hP
  rw [codeAt_append, length_compile] at hP'
  obtain ⟨hPφ, hPψ⟩ := hP'
  obtain ⟨r₁, regs₁, hr₁, hreach₁, hk₁⟩ :=
    ihφ hΓ hWφ fv base val ρ b (b + len φ) F regs hPφ hbase hfv hdφ h0 hv hregs
  cases r₁ with
  | false =>
    exact ⟨false, regs₁, iff_of_false Bool.false_ne_true fun h => Bool.false_ne_true (hr₁.mpr h.1),
      hreach₁, hk₁⟩
  | true =>
    obtain ⟨hd₁, h0₁, hv₁⟩ := hk₁.facts hbase hfv hdψ h0 hv
    obtain ⟨r₂, regs₂, hr₂, hreach₂, hk₂⟩ :=
      ihψ hΓ hWψ fv base val ρ (b + len φ) T F regs₁ hPψ hbase hfv hd₁ h0₁ hv₁ hk₁.bounded
    rw [ite_eq_left rfl] at hreach₁
    refine ⟨r₂, regs₂, ?_, hreach₁.trans hreach₂, hk₁.trans hk₂⟩
    rw [hr₂]
    exact ⟨fun h => ⟨hr₁.mp rfl, h⟩, fun h => h.2⟩

theorem correct_ex (hE : Env v a B) {Γ : List ℕ} {α : Type}
    {φ : Formula (language L) TC.shape Γ (Option α)}
    (ih : Correct v a P B φ) : Correct v a P B φ.ex := by
  intro hΓ hW fv base val ρ b T F regs hP hbase hfv hd h0 hv hregs
  have hdepth : base + 1 + scratch φ ≤ regs.length := by simp only [scratch] at hd; omega
  have hlen : base < regs.length := by omega
  have hfv' : ∀ y : Option α, y.elim base fv < base + 1 := fun y => by
    cases y with
    | none => simp
    | some y => have := hfv y; simp only [Option.elim_some]; omega
  have hP' : P.CodeAt b ([.assign base (const 0) (b + 1), .lt (reg base) (reg 0) (b + 2) F] ++
      compile v (fun x => x.elim base fv) (base + 1) φ (b + 2) T (b + 2 + len φ) ++
      [.assign base (add (reg base) (const 1)) (b + 1)]) := hP
  simp only [codeAt_append, codeAt_cons, List.length_append, List.length_cons, List.length_nil,
    length_compile] at hP'
  obtain ⟨⟨⟨h₀, h₁, -⟩, hPφ⟩, h₂, -⟩ := hP'
  replace hPφ := codeAt_of_eq (l' := b + 2) hPφ (by omega)
  replace h₂ := instr_of_eq (l' := b + 2 + len φ) h₂ (by omega)
  -- the loop test, with `m` values of the quantified variable checked
  have hstep : ∀ regs₁ : List ℕ, Kept B base regs regs₁ → ∀ m, regs₁.getD base 0 = m →
      P.Reaches (encStructure a) (P.Running B) (b + 1, regs₁)
        (if m < a.1 then b + 2 else F, regs₁) := fun regs₁ hk m hm =>
    Reaches.lt h₁ hk.bounded (by
      simp only [eval_reg, hm, (hk.getD_eq 0 hbase).trans h0]
      exact Reaches.refl _)
  have key : ∀ e m (regs₁ : List ℕ), a.1 - m = e → m ≤ a.1 → Kept B base regs regs₁ →
      regs₁.getD base 0 = m →
      (∀ x : Fin a.1, (x : ℕ) < m → ¬ φ.Realize DTC.interpretation ρ (Option.elim · x val)) →
      ∃ (res : Bool) (regs' : List ℕ), (res = true ↔ φ.ex.Realize DTC.interpretation ρ val) ∧
        P.Reaches (encStructure a) (P.Running B) (b + 1, regs₁) (if res then T else F, regs') ∧
        Kept B base regs regs' := by
    intro e
    induction e with
    | zero =>
      intro m regs₁ he hm hk hx hall
      refine ⟨false, regs₁, iff_of_false Bool.false_ne_true fun ⟨x, hx'⟩ => hall x (by omega) hx',
        ?_, hk⟩
      have hr := hstep regs₁ hk m hx
      rwa [ite_eq_right (show ¬ m < a.1 by omega)] at hr
    | succ e ih' =>
      intro m regs₁ he hm hk hx hall
      have hmn : m < a.1 := by omega
      have hr₁ := hstep regs₁ hk m hx
      rw [ite_eq_left hmn] at hr₁
      obtain ⟨r, regs₂, hr, hreach, hk₂⟩ :=
        ih hΓ hW (fun x => x.elim base fv) (base + 1) (Option.elim · ⟨m, hmn⟩ val) ρ (b + 2) T
          (b + 2 + len φ) regs₁ hPφ (by omega) hfv' (by rw [hk.length_eq]; omega)
          ((hk.getD_eq 0 hbase).trans h0)
          (getD_elim_eq (fun x => (hk.getD_eq _ (hfv x)).trans (hv x)) (c := ⟨m, hmn⟩) hx)
          hk.bounded
      cases r with
      | true =>
        rw [ite_eq_left rfl] at hreach
        exact ⟨true, regs₂, iff_of_true rfl ⟨⟨m, hmn⟩, hr.mp rfl⟩, hr₁.trans hreach,
          hk.trans (hk₂.mono (by omega))⟩
      | false =>
        rw [ite_eq_right Bool.false_ne_true] at hreach
        have hx₂ : regs₂.getD base 0 = m := by rw [hk₂.getD_eq base (by omega), hx]
        have hk₃ : Kept B base regs (regs₂.set base (m + 1)) :=
          (hk.trans (hk₂.mono (by omega))).set_right le_rfl (by have := hE.card_le; omega)
        have hinc : P.Reaches (encStructure a) (P.Running B) (b + 2 + len φ, regs₂)
            (b + 1, regs₂.set base (m + 1)) := by
          refine Reaches.assign h₂ hk₂.bounded ?_
          simp only [eval_add, eval_reg, eval_const, hx₂]
          exact Reaches.refl _
        obtain ⟨res, regs', hres, hreach', hk'⟩ := ih' (m + 1) _ (by omega) hmn hk₃
          (List.getD_set_self (by rw [hk₂.length_eq, hk.length_eq]; exact hlen)) fun x hxm => by
            rcases Nat.lt_succ_iff_lt_or_eq.mp hxm with hxm | hxm
            · exact hall x hxm
            · obtain rfl : x = ⟨m, hmn⟩ := Fin.ext hxm
              exact fun h => Bool.false_ne_true (hr.mpr h)
        exact ⟨res, regs', hres, (hr₁.trans hreach).trans (hinc.trans hreach'), hk'⟩
  have hk₀ : Kept B base regs (regs.set base 0) :=
    (Kept.refl hregs).set_right le_rfl (Nat.zero_le _)
  obtain ⟨res, regs', hres, hreach, hk'⟩ := key _ 0 _ rfl (Nat.zero_le _) hk₀
    (List.getD_set_self hlen) fun x hx => absurd hx (Nat.not_lt_zero _)
  exact ⟨res, regs', hres, Reaches.assign h₀ hregs hreach, hk'⟩

theorem correct_op (hE : Env v a B) {Γ : List ℕ} {α : Type} (k : ℕ)
    (body : (i : Fin (TC.shape k).slots) → Formula (language L) TC.shape
      (((TC.shape k).binder i).relations ++ Γ) (α ⊕ Fin ((TC.shape k).binder i).vars))
    (args : Fin (TC.shape k).arity → (language L).Term α)
    (ih : Correct v a P B (body ⟨0, Nat.one_pos⟩)) :
    Correct v a P B (Formula.op k body args) := by
  intro hΓ hW fv base val ρ b T F regs hP hbase hfv hd h0 hv hregs
  have hn : 0 < a.1 := by have := (Fact.out : 2 ≤ a.1); omega
  have hNB : a.1 ^ k ≤ B := (Nat.pow_le_pow_right hn (le_max_left _ _)).trans hW
  have hWb : a.1 ^ TC.width (body ⟨0, Nat.one_pos⟩) ≤ B :=
    (Nat.pow_le_pow_right hn (le_max_right _ _)).trans hW
  have hscratch : scratch (Formula.op (L := language L) (shape := TC.shape) (Γ := Γ) k body args) =
      2 * k + 4 + scratch (body ⟨0, Nat.one_pos⟩) := rfl
  -- the endpoint tuples and the edge relation
  let s₀ : Fin k → Fin a.1 := fun i => (TC.left args i).realize val
  let z₀ : Fin k → Fin a.1 := fun i => (TC.right args i).realize val
  let E : (Fin k → Fin a.1) → (Fin k → Fin a.1) → Prop := fun us ys =>
    (body ⟨0, Nat.one_pos⟩).Realize DTC.interpretation (RelEnv.empty.append ρ)
      (Sum.elim val (TC.pair us ys))
  have hsrc : ∀ regs' : List ℕ, (∀ j < base, regs'.getD j 0 = regs.getD j 0) →
      ∀ i, (termE fv (TC.left args i)).eval regs' = s₀ i := fun regs' h i =>
    eval_termE_of_atomic (hE.atomic fv 0 val) ((h 0 hbase).trans h0)
      (fun x => (h _ (hfv x)).trans (hv x)) _
  have hdst : ∀ regs' : List ℕ, (∀ j < base, regs'.getD j 0 = regs.getD j 0) →
      ∀ i, (termE fv (TC.right args i)).eval regs' = z₀ i := fun regs' h i =>
    eval_termE_of_atomic (hE.atomic fv 0 val) ((h 0 hbase).trans h0)
      (fun x => (h _ (hfv x)).trans (hv x)) _
  -- the body block
  let code := compile v (α := α ⊕ Fin ((TC.shape k).binder ⟨0, Nat.one_pos⟩).vars)
    (Sum.elim fv fun i => base + i.val) (base + 2 * k + 4) (body ⟨0, Nat.one_pos⟩)
    (b + 2 * k + 6) (b + 2 * k + 6 + len (body ⟨0, Nat.one_pos⟩))
    (b + 2 * k + 9 + len (body ⟨0, Nat.one_pos⟩))
  have hP' : P.CodeAt b (dtcCode b base k (fun i => termE fv (TC.left args i))
      (fun i => termE fv (TC.right args i)) code T F) := hP
  have hcl : code.length = len (body ⟨0, Nat.one_pos⟩) := length_compile ..
  obtain ⟨-, -, -, -, -, -, -, -, hbodyP, -⟩ := dtcCode_parts hP'
  have hbody : ∀ regs₁ (us ys : Fin k → Fin a.1), Kept B base regs regs₁ →
      (∀ i : Fin k, regs₁.getD (base + i) 0 = us i) →
      (∀ i : Fin k, regs₁.getD (base + k + i) 0 = ys i) →
      ∃ (res : Bool) (regs' : List ℕ), (res = true ↔ E us ys) ∧
        P.Reaches (encStructure a) (P.Running B) (b + 2 * k + 6, regs₁)
          (if res then b + 2 * k + 6 + code.length else b + 2 * k + 9 + code.length, regs') ∧
        Kept B (base + 2 * k + 4) regs₁ regs' := by
    intro regs₁ us ys hk hu hy
    rw [hcl]
    exact ih (by rw [hΓ]; rfl) hWb _ (base + 2 * k + 4) (Sum.elim val (TC.pair us ys))
      (RelEnv.empty.append ρ) (b + 2 * k + 6) _ _ regs₁ hbodyP (by omega)
      (fun x => by
        cases x with
        | inl x => have := hfv x; simp only [Sum.elim_inl]; omega
        | inr i => have : (i : ℕ) < 2 * k := i.isLt; simp only [Sum.elim_inr]; omega)
      (by rw [hk.length_eq]; omega) ((hk.getD_eq 0 hbase).trans h0)
      (fun x => by
        cases x with
        | inl x => simp only [Sum.elim_inl]; exact (hk.getD_eq _ (hfv x)).trans (hv x)
        | inr i => exact getD_pair hu hy i)
      hk.bounded
  obtain ⟨res, regs', hres, hreach, hk'⟩ := reaches_dtcCode (E := E) hP' hbase (by omega) h0
    hNB hE.card_le hE.one_le hregs hsrc hdst hbody
  exact ⟨res, regs', hres, hreach, hk'⟩

/-- **Compiler correctness** for every formula without free relation variables. -/
theorem correct (hE : Env v a B) :
    ∀ {Γ : List ℕ} {α : Type} (φ : Formula (language L) TC.shape Γ α), Correct v a P B φ
  | _, _, .ofFO φ => correct_ofFO hE φ
  | _, _, .rel r _ => fun hΓ => by subst hΓ; cases r
  | _, _, .neg φ => correct_neg (correct hE φ)
  | _, _, .conj φ ψ => correct_conj (correct hE φ) (correct hE ψ)
  | _, _, .ex φ => correct_ex hE (correct hE φ)
  | _, _, .op k body args => correct_op hE k body args (correct hE (body ⟨0, Nat.one_pos⟩))

end Correct

end Cslib.Logic.FO.Ordered.DTCModelChecker
