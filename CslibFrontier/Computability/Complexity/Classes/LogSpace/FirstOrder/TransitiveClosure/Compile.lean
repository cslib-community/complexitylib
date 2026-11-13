/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Block
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Kept
public import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.ClosureKernel
public import CslibFrontier.Logics.FirstOrder.Operator.TransitiveClosure.Positive
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Step

/-!
# Compiling FO(TC) formulas to nondeterministic counter code

A formula over the canonical ordered language with transitive-closure operators is compiled, at
a polarity `s`, to nondeterministic counter code that reaches a target label when the formula has
truth value `s` and otherwise rejects. First-order subformulas reuse the deterministic ordered
checker, shifted above the choice register. Conjunction and universal quantification at polarity
`true` (dually disjunction and existential quantification at `false`) run sequentially;
existential quantification and disjunction at polarity `true` guess. A closure at polarity `true`
becomes the bounded path loop `tcCode` around the compiled code of its body. A closure at polarity
`false` becomes the inductive-counting block `countCode`, whose tests `countTestCode` run the body
code at polarity `true` (walks and edges) and at polarity `false` (non-edges).

The correctness contract `Correct` states soundness and completeness of the compiled code of a
formula at each polarity, with every register at most `B`.

## Main definitions

* `Cslib.Logic.FO.Ordered.TCModelChecker.compile`: the polarity-indexed compiler.
* `Cslib.Logic.FO.Ordered.TCModelChecker.tcCode`: the bounded closure loop.
* `Cslib.Logic.FO.Ordered.TCModelChecker.countTestCode`,
  `Cslib.Logic.FO.Ordered.TCModelChecker.countCode`: one test and the counting block of
  inductive counting.
* `Cslib.Logic.FO.Ordered.TCModelChecker.Env`, `Cslib.Logic.FO.Ordered.TCModelChecker.Correct`:
  the hypotheses and statement of compiler correctness.

The register-machine kernel shared with the FO(DTC) compiler (term expressions, the loop test,
digit decoding and loading the source tuple) is in
`Cslib.Logic.FO.Ordered.ClosureKernel`; the effect of a block on the registers is
`Turing.CounterProgram.Kept`.

## Main results

* `Cslib.Logic.FO.Ordered.TCModelChecker.correct_ofFO`, `correct_neg`, `correct_conj`,
  `correct_ex`: correctness for the first-order constructors.

## References

* [N. Immerman, *Languages That Capture Complexity Classes*, Theorem 3.1][Immerman1987]
-/

public section

universe u v w

open FirstOrder Language
namespace Cslib.Logic.FO.Ordered.TCModelChecker

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
  | _, _, .op k body _ => 4 * k + 9 + scratch (body ⟨0, Nat.one_pos⟩)

/-- Straight-line assignments of `e i` to register `r + i` above the choice, for `i < k`. -/
@[expose] def assignChain (b r k : ℕ) (e : ℕ → Expr) : List Instr :=
  (List.range k).map fun i => (Instr.assign (r + i) (e i) (b + i + 1)).shift

theorem length_assignChain (b r k : ℕ) (e : ℕ → Expr) : (assignChain b r k e).length = k := by
  simp [assignChain]

/-- `assignChain` is the shifted block of assignments. -/
theorem assignChain_eq (b r k : ℕ) (e : ℕ → Expr) :
    assignChain b r k e = (assignsCode b r k e).map Instr.shift := by
  simp [assignChain, assignsCode, List.map_map, Function.comp_def]

/-- `|x - y|` for registers `x` and `y`: positive exactly when they differ. -/
@[expose] def distE (x y : ℕ) : Expr := add (sub (reg x) (reg y)) (sub (reg y) (reg x))

/-- The closure loop around compiled body code `body`, placed at `b`. The source tuple is
copied to registers `base + i`, the guessed successor is decoded into registers `base + k + i`,
register `base + 2 * k` holds the guess and `base + 2 * k + 1` the step counter. The loop reaches
`T` once the current tuple is `dst` and rejects at `R` after `M` steps. -/
@[expose] def tcCode (b base k : ℕ) (src dst : Fin k → Expr) (M : Expr) (body : List Instr)
    (T R : ℕ) : List Instr :=
  assignChain b base k (fun i => if h : i < k then src ⟨i, h⟩ else const 0) ++
  [(Instr.assign (base + 2 * k + 1) (const 0) (b + k + 1)).shift,
   (Instr.lt (const 0) (testExpr base k dst) (b + k + 2) T).shift,
   (Instr.lt (reg (base + 2 * k + 1)) M (b + k + 3) R).shift] ++
  guessCode (b + k + 3) (base + 2 * k) (pow (reg 0) k) (b + k + 7) R ++
  assignChain (b + k + 7) (base + k) k (digitE (base + 2 * k)) ++
  body ++
  assignChain (b + 2 * k + 7 + body.length) base k (fun i => reg (base + k + i)) ++
  [(Instr.assign (base + 2 * k + 1) (add (reg (base + 2 * k + 1)) (const 1))
    (b + k + 1)).shift]

theorem length_tcCode (b base k : ℕ) (src dst : Fin k → Expr) (M : Expr) (body : List Instr)
    (T R : ℕ) : (tcCode b base k src dst M body T R).length = 3 * k + 8 + body.length := by
  simp only [tcCode, List.length_append, length_assignChain, List.length_cons, List.length_nil,
    length_guessCode]
  omega

/-- The code of a tuple: `∑ i, z i * n ^ i`, inverse to `digitE`. -/
@[expose] def codeE (k : ℕ) (z : Fin k → Expr) : Expr :=
  Expr.sum ((List.finRange k).map fun i : Fin k => mul (z i) (pow (reg 0) i))

/-- One test of inductive counting, placed at `b`, with registers `I, C, Y, X, S, H` at
`base + 0, 1, 3, 4, 5, 6`, the decoded pair at `base + 7`, and the walk at `base + 7 + 2 * k`.
Given the size `C` of round `I`, it scans every `x < n ^ k`, guesses whether `x` is in round `I`,
certifies selected `x` by a walk of at most `I` steps from `src` (walk body `wb`), and guesses and
certifies whether `x` reaches `y` (the value of `Y`) in at most one step (edge codes `et`, `ef`).
It goes to `T` with `H = 1` exactly when `y` is in round `I + 1`, after checking that `C`
elements were selected; otherwise it rejects at `R`. -/
@[expose] def countTestCode (b base k : ℕ) (src : Fin k → Expr) (wb et ef : List Instr) (T R : ℕ) :
    List Instr :=
  let w₁ := b + 14 + 5 * k + wb.length
  [(Instr.assign (base + 6) (const 0) (b + 1)).shift,
   (Instr.assign (base + 5) (const 0) (b + 2)).shift,
   (Instr.assign (base + 4) (const 0) (b + 3)).shift,
   (Instr.lt (reg (base + 4)) (pow (reg 0) k) (b + 4) (w₁ + 10 + et.length + ef.length)).shift,
   (Instr.lt (const 0) (const 0) (b + 5) (b + 5)).shift,
   .lt (reg 0) (const 1) (b + 6) (w₁ + 9 + et.length + ef.length)] ++
  assignChain (b + 6) (base + 7) k (digitE (base + 4)) ++
  assignChain (b + 6 + k) (base + 7 + k) k (digitE (base + 3)) ++
  tcCode (b + 6 + 2 * k) (base + 7 + 2 * k) k src
    (fun i => digitE (base + 4) i) (reg base) wb w₁ R ++
  [(Instr.assign (base + 5) (add (reg (base + 5)) (const 1)) (w₁ + 1)).shift,
   (Instr.lt (const 0) (const 0) (w₁ + 2) (w₁ + 2)).shift,
   .lt (reg 0) (const 1) (w₁ + 3) (w₁ + 8 + et.length),
   (Instr.lt (const 0) (const 0) (w₁ + 4) (w₁ + 4)).shift,
   .lt (reg 0) (const 1) (w₁ + 5) (w₁ + 8),
   (Instr.lt (const 0) (distE (base + 4) (base + 3)) R (w₁ + 6)).shift,
   (Instr.assign (base + 6) (const 1) (w₁ + 9 + et.length + ef.length)).shift,
   (Instr.assign (base + 6) (const 1) (w₁ + 9 + et.length + ef.length)).shift] ++
  et ++
  [(Instr.lt (const 0) (distE (base + 4) (base + 3)) (w₁ + 9 + et.length) R).shift] ++
  ef ++
  [(Instr.assign (base + 4) (add (reg (base + 4)) (const 1)) (b + 3)).shift,
   (Instr.lt (const 0) (distE (base + 5) (base + 1)) R T).shift]

theorem length_countTestCode (b base k : ℕ) (src : Fin k → Expr) (wb et ef : List Instr)
    (T R : ℕ) : (countTestCode b base k src wb et ef T R).length =
      5 * k + 25 + wb.length + et.length + ef.length := by
  simp only [countTestCode, List.length_append, List.length_cons, List.length_nil,
    length_assignChain, length_tcCode]
  omega

/-- The inductive-counting block for a negated closure, placed at `b`: rounds `I < n ^ k - 1`
compute the size `D` of round `I + 1` from the size `C` of round `I` by one test per candidate
`y` (first test code `t₁`), and a final test (code `t₂`) of the target code at round `n ^ k - 1`
goes to `T` exactly when the target is not reached. -/
@[expose] def countCode (b base k : ℕ) (dst : Fin k → Expr) (t₁ t₂ : List Instr) (T R : ℕ) :
    List Instr :=
  [(Instr.assign base (const 0) (b + 1)).shift,
   (Instr.assign (base + 1) (const 1) (b + 2)).shift,
   (Instr.lt (add (reg base) (const 1)) (pow (reg 0) k) (b + 3) (b + t₁.length + 10)).shift,
   (Instr.assign (base + 2) (const 0) (b + 4)).shift,
   (Instr.assign (base + 3) (const 0) (b + 5)).shift,
   (Instr.lt (reg (base + 3)) (pow (reg 0) k) (b + 6) (b + t₁.length + 8)).shift] ++
  t₁ ++
  [(Instr.assign (base + 2) (add (reg (base + 2)) (reg (base + 6))) (b + t₁.length + 7)).shift,
   (Instr.assign (base + 3) (add (reg (base + 3)) (const 1)) (b + 5)).shift,
   (Instr.assign (base + 1) (reg (base + 2)) (b + t₁.length + 9)).shift,
   (Instr.assign base (add (reg base) (const 1)) (b + 2)).shift,
   (Instr.assign (base + 3) (codeE k dst) (b + t₁.length + 11)).shift] ++
  t₂ ++
  [(Instr.lt (reg (base + 6)) (const 1) T R).shift]

theorem length_countCode (b base k : ℕ) (dst : Fin k → Expr) (t₁ t₂ : List Instr)
    (T R : ℕ) : (countCode b base k dst t₁ t₂ T R).length = t₁.length + t₂.length + 12 := by
  simp only [countCode, List.length_append, List.length_cons, List.length_nil]
  omega

/-- The number of instructions compiled from a formula at a polarity. -/
@[expose] def len : {Γ : List ℕ} → {α : Type w} → Formula (language L) TC.shape Γ α → Bool → ℕ
  | _, _, .ofFO φ, _ => codeLength φ
  | _, _, .rel _ _, _ => 0
  | _, _, .neg φ, s => len φ (!s)
  | _, _, .conj φ ψ, true => len φ true + len ψ true
  | _, _, .conj φ ψ, false => 2 + len φ false + len ψ false
  | _, _, .ex φ, true => 4 + len φ true
  | _, _, .ex φ, false => 3 + len φ false
  | _, _, .op k body _, true => 3 * k + 8 + len (body ⟨0, Nat.one_pos⟩) true
  | _, _, .op k body _, false =>
    2 * (5 * k + 25 + 2 * len (body ⟨0, Nat.one_pos⟩) true + len (body ⟨0, Nat.one_pos⟩) false) +
      12

/-- The code for a formula at a polarity `s`, placed at `b`: registers above the choice; the free
variable `x` in register `fv x`, scratch registers from `base`. It goes to `T` when the formula has
truth value `s` and otherwise rejects at `R`. -/
@[expose] def compile : {Γ : List ℕ} → {α : Type w} → (α → ℕ) → ℕ →
    Formula (language L) TC.shape Γ α → Bool → ℕ → ℕ → ℕ → List Instr
  | _, _, fv, base, .ofFO φ, s, b, T, R =>
    (ModelChecker.formulaCode v fv base φ b (cond s T R) (cond s R T)).map Instr.shift
  | _, _, _, _, .rel _ _, _, _, _, _ => []
  | _, _, fv, base, .neg φ, s, b, T, R => compile fv base φ (!s) b T R
  | _, _, fv, base, .conj φ ψ, true, b, T, R =>
    compile fv base φ true b (b + len φ true) R ++ compile fv base ψ true (b + len φ true) T R
  | _, _, fv, base, .conj φ ψ, false, b, T, R =>
    [(Instr.lt (const 0) (const 0) (b + 1) (b + 1)).shift,
     .lt (reg 0) (const 1) (b + 2) (b + 2 + len φ false)] ++
    compile fv base φ false (b + 2) T R ++ compile fv base ψ false (b + 2 + len φ false) T R
  | _, _, fv, base, .ex φ, true, b, T, R =>
    guessCode b base (reg 0) (b + 4) R ++
    compile (fun x => x.elim base fv) (base + 1) φ true (b + 4) T R
  | _, _, fv, base, .ex φ, false, b, T, R =>
    [(Instr.assign base (const 0) (b + 1)).shift,
     (Instr.lt (reg base) (reg 0) (b + 2) T).shift] ++
    compile (fun x => x.elim base fv) (base + 1) φ false (b + 2) (b + 2 + len φ false) R ++
    [(Instr.assign base (add (reg base) (const 1)) (b + 1)).shift]
  | _, α, fv, base, .op k body args, true, b, T, R =>
    tcCode b base k (fun i => termE fv (TC.left args i)) (fun i => termE fv (TC.right args i))
      (pow (reg 0) k) (compile (α := α ⊕ Fin ((TC.shape k).binder ⟨0, Nat.one_pos⟩).vars)
        (Sum.elim fv fun i => base + i.val) (base + 2 * k + 2) (body ⟨0, Nat.one_pos⟩) true
        (b + 2 * k + 7) (b + 2 * k + 7 + len (body ⟨0, Nat.one_pos⟩) true) R) T R
  | _, α, fv, base, .op k body args, false, b, T, R =>
    let L₁ := len (body ⟨0, Nat.one_pos⟩) true
    let L₀ := len (body ⟨0, Nat.one_pos⟩) false
    let tL := 5 * k + 25 + 2 * L₁ + L₀
    let fw : α ⊕ Fin ((TC.shape k).binder ⟨0, Nat.one_pos⟩).vars → ℕ :=
      Sum.elim fv fun i => base + 7 + 2 * k + i.val
    let fe : α ⊕ Fin ((TC.shape k).binder ⟨0, Nat.one_pos⟩).vars → ℕ :=
      Sum.elim fv fun i => base + 7 + i.val
    let test := fun b₁ T₁ : ℕ =>
      countTestCode b₁ base k (fun i => termE fv (TC.left args i))
        (compile (α := α ⊕ Fin ((TC.shape k).binder ⟨0, Nat.one_pos⟩).vars) fw (base + 9 + 4 * k)
          (body ⟨0, Nat.one_pos⟩) true (b₁ + 6 + 2 * k + 2 * k + 7)
          (b₁ + 6 + 2 * k + 2 * k + 7 + L₁) R)
        (compile (α := α ⊕ Fin ((TC.shape k).binder ⟨0, Nat.one_pos⟩).vars) fe (base + 7 + 2 * k)
          (body ⟨0, Nat.one_pos⟩) true (b₁ + 22 + 5 * k + L₁) (b₁ + 21 + 5 * k + L₁) R)
        (compile (α := α ⊕ Fin ((TC.shape k).binder ⟨0, Nat.one_pos⟩).vars) fe (base + 7 + 2 * k)
          (body ⟨0, Nat.one_pos⟩) false (b₁ + 23 + 5 * k + 2 * L₁) (b₁ + 23 + 5 * k + 2 * L₁ + L₀)
          R)
        T₁ R
    countCode b base k (fun i => termE fv (TC.right args i)) (test (b + 6) (b + 6 + tL))
      (test (b + 11 + tL) (b + 11 + tL + tL)) T R

theorem length_compile : ∀ {Γ : List ℕ} {α : Type w} (fv : α → ℕ) (base : ℕ)
    (φ : Formula (language L) TC.shape Γ α) (s : Bool) (b T R : ℕ),
    (compile v fv base φ s b T R).length = len φ s
  | _, _, fv, base, .ofFO φ, s, b, T, R => by
    simp only [compile, len, List.length_map, ModelChecker.formulaCode, length_formulaCodeWith]
  | _, _, _, _, .rel _ _, _, _, _, _ => rfl
  | _, _, fv, base, .neg φ, s, b, T, R => length_compile fv base φ (!s) b T R
  | _, _, fv, base, .conj φ ψ, true, b, T, R => by
    simp only [compile, len, List.length_append, length_compile]
  | _, _, fv, base, .conj φ ψ, false, b, T, R => by
    simp only [compile, len, List.length_append, length_compile, List.length_cons,
      List.length_nil]
  | _, _, fv, base, .ex φ, true, b, T, R => by
    simp only [compile, len, List.length_append, length_compile, length_guessCode]
  | _, _, fv, base, .ex φ, false, b, T, R => by
    simp only [compile, len, List.length_append, length_compile, List.length_cons,
      List.length_nil]
    omega
  | _, _, fv, base, .op k body args, true, b, T, R => by
    simp only [compile, len, length_tcCode]
    rw [length_compile]
  | _, _, fv, base, .op k body args, false, b, T, R => by
    simp only [compile, len, length_countCode, length_countTestCode]
    rw [length_compile, length_compile, length_compile, length_compile, length_compile,
      length_compile]
    omega

variable {v}

private theorem codeAt_left {P : CounterProgram} {b : ℕ} {l₁ l₂ : List Instr}
    (h : P.CodeAt b (l₁ ++ l₂)) : P.CodeAt b l₁ := (codeAt_append.mp h).1

private theorem codeAt_right {P : CounterProgram} {b b' : ℕ} {l₁ l₂ : List Instr}
    (h : P.CodeAt b (l₁ ++ l₂)) (hb : b' = b + l₁.length) : P.CodeAt b' l₂ :=
  hb ▸ (codeAt_append.mp h).2

/-- Straight-line assignments, when each expression ignores the registers assigned. -/
theorem reaches_assignChain {P : CounterProgram} {w : List Bool} {B b r : ℕ} {e : ℕ → Expr}
    {k : ℕ} (hP : P.CodeAt b (assignChain b r k e)) {regs : List ℕ} (hlen : r + k ≤ regs.length)
    (he : ∀ i < k, ∀ regs' : List ℕ, (∀ j, (j < r ∨ r + k ≤ j) → regs'.getD j 0 = regs.getD j 0) →
      (e i).eval regs' = (e i).eval regs)
    (hB : ∀ x ∈ regs, x ≤ B) (heB : ∀ i < k, (e i).eval regs ≤ B) :
    ∃ regs', P.Reaches w (P.Oblivious B) (b, 0 :: regs) (b + k, 0 :: regs') ∧
      regs'.length = regs.length ∧
      (∀ j, (j < r ∨ r + k ≤ j) → regs'.getD j 0 = regs.getD j 0) ∧
      (∀ i < k, regs'.getD (r + i) 0 = (e i).eval regs) ∧ ∀ x ∈ regs', x ≤ B := by
  obtain ⟨regs', hr, hrest⟩ := reaches_assignsCode (w := w)
    (codeAt_padded b (assignsCode b r k e)) hlen he hB heB
  exact ⟨regs', Reaches.unpad (Nat.zero_le B) (assignChain_eq b r k e ▸ hP) hr, hrest⟩

section Correct

variable {a : EncodedStructure} [L.Structure (Fin a.1)] [Fact (2 ≤ a.1)]
  {P : CounterProgram} {B : ℕ} {Post : Config → Prop} {R : ℕ}

/-- A proposition with the truth value `s`. -/
@[expose] def Sat (s : Bool) (p : Prop) : Prop := cond s p (¬ p)

private theorem sat_not (s : Bool) (p : Prop) : Sat s (¬ p) ↔ Sat (!s) p := by
  cases s <;> simp [Sat]

variable (v a P B Post R) in
/-- The hypotheses of the compiler correctness proof. -/
structure Env : Prop where
  atomic : ∀ {β : Type} (fv : β → ℕ) (base : ℕ) (val : β → Fin a.1),
    (ModelChecker.atomicCompiler v fv base).Correct (encStructure a) fv base val
  one_le : 1 ≤ B
  card_le : a.1 ≤ B
  halts : (P.instr R).halts = true
  post : ∀ s : Config, s.1 = R → Post s

variable (v a P B Post R) in
/-- The compiled code of `φ` is correct at every polarity. -/
@[expose] def Correct {Γ : List ℕ} {α : Type} (φ : Formula (language L) TC.shape Γ α) : Prop :=
  Γ = [] → ∀ s : Bool, a.1 ^ TC.width φ ≤ B →
  ∀ (fv : α → ℕ) (base : ℕ) (val : α → Fin a.1) (ρ : RelEnv Γ (Fin a.1)) (b T : ℕ)
    (regs : List ℕ),
    P.CodeAt b (compile v fv base φ s b T R) → 0 < base → (∀ x, fv x < base) →
    base + scratch φ ≤ regs.length → regs.getD 0 0 = a.1 →
    (∀ x, regs.getD (fv x) 0 = val x) → (∀ r ∈ regs, r ≤ B) →
    Sound P (encStructure a) B Post b regs T
      (fun regs' => Kept B base regs regs' ∧ Sat s (φ.Realize TC.interpretation ρ val)) ∧
    (Sat s (φ.Realize TC.interpretation ρ val) →
      Complete P (encStructure a) b regs T (Kept B base regs))

theorem eval_termE (hE : Env v a P B Post R) {α : Type} (fv : α → ℕ) (val : α → Fin a.1)
    {regs : List ℕ} (h0 : regs.getD 0 0 = a.1) (hv : ∀ x, regs.getD (fv x) 0 = val x)
    (t : (language L).Term α) : (termE fv t).eval regs = ((t.realize val : Fin a.1) : ℕ) :=
  eval_termE_of_atomic (hE.atomic fv 0 val) h0 hv t

theorem correct_ofFO (hE : Env v a P B Post R) {Γ : List ℕ} {α : Type}
    (φ : (language L).Formula α) :
    Correct v a P B Post R (Formula.ofFO (shape := TC.shape) (Γ := Γ) φ) := by
  intro _ s _ fv base val ρ b T regs hP hbase hfv hd h0 hv hregs
  let code := ModelChecker.formulaCode v fv base φ b (cond s T R) (cond s R T)
  obtain ⟨res, regs', hres, hreach, hk'⟩ :=
    reaches_formulaCodeWith (P := padded b code) hE.card_le fv base hbase hfv val _
      (hE.atomic fv base val) φ b (cond s T R) (cond s R T) regs default (codeAt_padded b code)
      hd h0 hregs hv (fun i => i.elim0)
  have hP' : P.CodeAt b (code.map Instr.shift) := hP
  have hk : Kept B base regs regs' := hk'.mono (Nat.le_add_right _ _)
  have hX : (Formula.ofFO (shape := TC.shape) (Γ := Γ) φ).Realize TC.interpretation ρ val ↔
      res = true := hres.symm
  refine ⟨Sound.of_reaches hE.one_le hP' hreach ?_, fun hs => Complete.of_reaches hP' hreach ?_⟩
  · cases s <;> cases res <;>
      simp only [Bool.cond_true, Bool.cond_false, Bool.false_eq_true, ↓reduceIte]
    · exact Sound.exit ⟨hk, by simp [Sat, hX]⟩
    · exact Sound.halt hE.one_le hE.halts (fun _ => hE.post _ rfl) hk.bounded
    · exact Sound.halt hE.one_le hE.halts (fun _ => hE.post _ rfl) hk.bounded
    · exact Sound.exit ⟨hk, by simp [Sat, hX]⟩
  · cases s <;> cases res <;>
      simp only [Bool.cond_true, Bool.cond_false, Bool.false_eq_true, ↓reduceIte]
    · exact Complete.refl hk
    · exact absurd (hX.mpr rfl) hs
    · exact absurd hs (by simp [Sat, hX])
    · exact Complete.refl hk

theorem correct_neg {Γ : List ℕ} {α : Type} {φ : Formula (language L) TC.shape Γ α}
    (ih : Correct v a P B Post R φ) : Correct v a P B Post R φ.neg := by
  intro hΓ s hW fv base val ρ b T regs hP hbase hfv hd h0 hv hregs
  obtain ⟨hs, hc⟩ := ih hΓ (!s) hW fv base val ρ b T regs hP hbase hfv hd h0 hv hregs
  have hsat := sat_not s (φ.Realize TC.interpretation ρ val)
  exact ⟨hs.mono fun regs' h => ⟨h.1, hsat.mpr h.2⟩, fun h => hc (hsat.mp h)⟩

theorem correct_conj (hE : Env v a P B Post R) {Γ : List ℕ} {α : Type}
    {φ ψ : Formula (language L) TC.shape Γ α}
    (ihφ : Correct v a P B Post R φ) (ihψ : Correct v a P B Post R ψ) :
    Correct v a P B Post R (φ.conj ψ) := by
  intro hΓ s hW fv base val ρ b T regs hP hbase hfv hd h0 hv hregs
  have hn : 0 < a.1 := by have := (Fact.out : 2 ≤ a.1); omega
  have hWφ : a.1 ^ TC.width φ ≤ B := (Nat.pow_le_pow_right hn (le_max_left _ _)).trans hW
  have hWψ : a.1 ^ TC.width ψ ≤ B := (Nat.pow_le_pow_right hn (le_max_right _ _)).trans hW
  have hdφ : base + scratch φ ≤ regs.length :=
    (Nat.add_le_add_left (le_max_left _ _) _).trans hd
  have hdψ : base + scratch ψ ≤ regs.length :=
    (Nat.add_le_add_left (le_max_right _ _) _).trans hd
  cases s with
  | true =>
    have hPφ : P.CodeAt b (compile v fv base φ true b (b + len φ true) R) := codeAt_left hP
    have hPψ : P.CodeAt (b + len φ true) (compile v fv base ψ true (b + len φ true) T R) :=
      codeAt_right hP (by rw [length_compile])
    obtain ⟨sφ, cφ⟩ :=
      ihφ hΓ true hWφ fv base val ρ b (b + len φ true) regs hPφ hbase hfv hdφ h0 hv hregs
    refine ⟨sφ.bind fun regs₁ ⟨hk₁, hX⟩ => ?_, fun ⟨hX, hY⟩ => (cφ hX).bind fun regs₁ hk₁ => ?_⟩
    · obtain ⟨hd₁, h0₁, hv₁⟩ := hk₁.facts hbase hfv hdψ h0 hv
      obtain ⟨sψ, -⟩ := ihψ hΓ true hWψ fv base val ρ _ T regs₁ hPψ hbase hfv hd₁ h0₁ hv₁
        hk₁.bounded
      exact sψ.mono fun regs₂ ⟨hk₂, hY⟩ => ⟨hk₁.trans hk₂, hX, hY⟩
    · obtain ⟨hd₁, h0₁, hv₁⟩ := hk₁.facts hbase hfv hdψ h0 hv
      obtain ⟨-, cψ⟩ := ihψ hΓ true hWψ fv base val ρ _ T regs₁ hPψ hbase hfv hd₁ h0₁ hv₁
        hk₁.bounded
      exact (cψ hY).mono fun regs₂ hk₂ => hk₁.trans hk₂
  | false =>
    have hP' : P.CodeAt b ([(Instr.lt (const 0) (const 0) (b + 1) (b + 1)).shift,
        .lt (reg 0) (const 1) (b + 2) (b + 2 + len φ false)] ++
        compile v fv base φ false (b + 2) T R ++
        compile v fv base ψ false (b + 2 + len φ false) T R) := hP
    have h₀ : P.instr b = (Instr.lt (const 0) (const 0) (b + 1) (b + 1)).shift :=
      hP' 0 (by simp)
    have h₁ : P.instr (b + 1) = .lt (reg 0) (const 1) (b + 2) (b + 2 + len φ false) :=
      hP' 1 (by simp)
    have hPφ : P.CodeAt (b + 2) (compile v fv base φ false (b + 2) T R) :=
      codeAt_right (codeAt_left hP') rfl
    have hlen : b + 2 + len φ false = b + ([(Instr.lt (const 0) (const 0) (b + 1) (b + 1)).shift,
        .lt (reg 0) (const 1) (b + 2) (b + 2 + len φ false)] ++
        compile v fv base φ false (b + 2) T R).length := by
      simp only [List.length_append, List.length_cons, List.length_nil, length_compile]
      omega
    have hPψ : P.CodeAt (b + 2 + len φ false)
        (compile v fv base ψ false (b + 2 + len φ false) T R) :=
      codeAt_right hP' hlen
    obtain ⟨sφ, cφ⟩ :=
      ihφ hΓ false hWφ fv base val ρ (b + 2) T regs hPφ hbase hfv hdφ h0 hv hregs
    obtain ⟨sψ, cψ⟩ := ihψ hΓ false hWψ fv base val ρ (b + 2 + len φ false) T regs hPψ hbase
      hfv hdψ h0 hv hregs
    have hr : P.Reaches (encStructure a) (P.Oblivious B) (b, 0 :: regs) (b + 1, 0 :: regs) :=
      by cp_step
    refine ⟨Sound.of_oblivious hE.one_le hr (Sound.choice hE.one_le h₁ hregs
      (sφ.mono fun _ h => ⟨h.1, fun hc => h.2 hc.1⟩)
      (sψ.mono fun _ h => ⟨h.1, fun hc => h.2 hc.2⟩)), fun hn => ?_⟩
    by_cases hX : φ.Realize TC.interpretation ρ val
    · exact Complete.choice hr (by omega) h₁ (Or.inr (cψ fun hY => hn ⟨hX, hY⟩))
    · exact Complete.choice hr (by omega) h₁ (Or.inl (cφ hX))

@[simp] theorem sat_true (p : Prop) : Sat true p ↔ p := Iff.rfl

@[simp] theorem sat_false (p : Prop) : Sat false p ↔ ¬ p := Iff.rfl

theorem correct_ex (hE : Env v a P B Post R) {Γ : List ℕ} {α : Type}
    {φ : Formula (language L) TC.shape Γ (Option α)}
    (ih : Correct v a P B Post R φ) : Correct v a P B Post R φ.ex := by
  intro hΓ s hW fv base val ρ b T regs hP hbase hfv hd h0 hv hregs
  have hdepth : base + 1 + scratch φ ≤ regs.length := by
    simp only [scratch] at hd; omega
  have hlen : base < regs.length := by omega
  have hfv' : ∀ y : Option α, y.elim base fv < base + 1 := fun y => by
    cases y with
    | none => simp
    | some y => have := hfv y; simp only [Option.elim_some]; omega
  have hset : ∀ m ≤ a.1, ∀ r ∈ regs.set base m, r ≤ B := fun m hm =>
    List.forall_mem_set_of_forall_mem hregs (hm.trans hE.card_le)
  have h0set : ∀ m, (regs.set base m).getD 0 0 = a.1 := fun m => by
    rw [List.getD_set_ne (by omega), h0]
  cases s with
  | true =>
    have hP' : P.CodeAt b (guessCode b base (reg 0) (b + 4) R ++
        compile v (fun x => x.elim base fv) (base + 1) φ true (b + 4) T R) := hP
    have hPg := codeAt_left hP'
    have hPφ :
        P.CodeAt (b + 4) (compile v (fun x => x.elim base fv) (base + 1) φ true (b + 4) T R) :=
      codeAt_right hP' rfl
    have hbody : ∀ x : Fin a.1,
        Sound P (encStructure a) B Post (b + 4) (regs.set base x) T
          (fun regs' => Kept B (base + 1) (regs.set base x) regs' ∧
            Sat true (φ.Realize TC.interpretation ρ (Option.elim · x val))) ∧
        (Sat true (φ.Realize TC.interpretation ρ (Option.elim · x val)) →
          Complete P (encStructure a) (b + 4) (regs.set base x) T
            (Kept B (base + 1) (regs.set base x))) := fun x =>
      ih hΓ true hW _ (base + 1) _ ρ (b + 4) T _ hPφ (by omega) hfv'
        (by rw [List.length_set]; exact hdepth) (h0set x)
        (getD_elim_eq (fun y => by rw [List.getD_set_ne (by have := hfv y; omega), hv])
          (c := x) (List.getD_set_self hlen)) (hset x x.isLt.le)
    have hN : ∀ y, (reg 0).eval (regs.set base y) = (reg 0).eval regs := fun y => by
      simp only [eval_reg, h0set, h0]
    have hN' : (reg 0).eval regs = a.1 := by simp only [eval_reg, h0]
    refine ⟨(Sound.guess hE.one_le hPg hE.halts hE.post hlen hN (hN' ▸ hE.card_le) hregs).bind
      ?_, ?_⟩
    · rintro _ ⟨m, hm, rfl⟩
      rw [hN'] at hm
      exact ((hbody ⟨m, hm⟩).1).mono fun regs' h =>
        ⟨Kept.of_set h.1, ⟨⟨m, hm⟩, h.2⟩⟩
    · rintro ⟨x, hx⟩
      refine (Complete.guess hPg hlen hN (hN' ▸ hE.card_le) hregs
        (m := x) (by rw [hN']; exact x.isLt)).bind ?_
      rintro _ rfl
      exact ((hbody x).2 hx).mono fun regs' h => Kept.of_set h
  | false =>
    have hP' : P.CodeAt b ([(Instr.assign base (const 0) (b + 1)).shift,
        (Instr.lt (reg base) (reg 0) (b + 2) T).shift] ++
        compile v (fun x => x.elim base fv) (base + 1) φ false (b + 2) (b + 2 + len φ false) R ++
        [(Instr.assign base (add (reg base) (const 1)) (b + 1)).shift]) := hP
    have h₀ : P.instr b = (Instr.assign base (const 0) (b + 1)).shift := hP' 0 (by simp)
    have h₁ : P.instr (b + 1) = (Instr.lt (reg base) (reg 0) (b + 2) T).shift :=
      hP' 1 (by simp)
    have hPφ : P.CodeAt (b + 2) (compile v (fun x => x.elim base fv) (base + 1) φ false (b + 2)
        (b + 2 + len φ false) R) := codeAt_right (codeAt_left hP') rfl
    have h₂ : P.instr (b + 2 + len φ false) =
        (Instr.assign base (add (reg base) (const 1)) (b + 1)).shift := by
      have := hP' (2 + len φ false) (by
        simp only [List.length_append, List.length_cons, List.length_nil, length_compile]; omega)
      rw [← Nat.add_assoc] at this
      rw [this, List.getElem_append_right (by
        simp only [List.length_append, List.length_cons, List.length_nil, length_compile]; omega)]
      simp only [List.length_append, List.length_cons, List.length_nil, length_compile,
        Nat.sub_self, List.getElem_cons_zero]
    -- the state at the loop test: `m` checked values, all false
    have hbody : ∀ (x : Fin a.1) (regs₁ : List ℕ), Kept B base regs regs₁ →
        regs₁.getD base 0 = x →
        Sound P (encStructure a) B Post (b + 2) regs₁ (b + 2 + len φ false)
          (fun regs' => Kept B (base + 1) regs₁ regs' ∧
            Sat false (φ.Realize TC.interpretation ρ (Option.elim · x val))) ∧
        (Sat false (φ.Realize TC.interpretation ρ (Option.elim · x val)) →
          Complete P (encStructure a) (b + 2) regs₁ (b + 2 + len φ false)
            (Kept B (base + 1) regs₁)) := fun x regs₁ hk hx => by
      obtain ⟨hd₁, h0₁, hv₁⟩ := hk.facts hbase hfv (d := 1 + scratch φ) (by omega) h0 hv
      exact ih hΓ false hW _ (base + 1) _ ρ (b + 2) _ regs₁ hPφ (by omega) hfv'
        (by omega) h0₁ (getD_elim_eq hv₁ (c := x) hx) hk.bounded
    have hstep : ∀ regs₁ : List ℕ, Kept B base regs regs₁ → ∀ m, regs₁.getD base 0 = m →
        P.Reaches (encStructure a) (P.Oblivious B) (b + 1, 0 :: regs₁)
          (if m < a.1 then b + 2 else T, 0 :: regs₁) := fun regs₁ hk m hm => by
      have := hk.bounded
      cp_step [hm, (hk.facts hbase hfv (d := 0) (by omega) h0 hv).2.1]
    have hinc : ∀ regs₂ : List ℕ, (∀ r ∈ regs₂, r ≤ B) → ∀ m, regs₂.getD base 0 = m → m < B →
        P.Reaches (encStructure a) (P.Oblivious B) (b + 2 + len φ false, 0 :: regs₂)
          (b + 1, 0 :: regs₂.set base (m + 1)) := fun regs₂ hB m hm hmB => by
      cp_step [hm]
    have key : ∀ e m (regs₁ : List ℕ), a.1 - m = e → m ≤ a.1 → Kept B base regs regs₁ →
        regs₁.getD base 0 = m →
        (∀ x : Fin a.1, (x : ℕ) < m → ¬ φ.Realize TC.interpretation ρ (Option.elim · x val)) →
        Sound P (encStructure a) B Post (b + 1) regs₁ T
          (fun regs' => Kept B base regs regs' ∧
            Sat false (φ.ex.Realize TC.interpretation ρ val)) := by
      intro e
      induction e with
      | zero =>
        intro m regs₁ he hm hk hx hall
        refine Sound.of_oblivious hE.one_le (hstep regs₁ hk m hx) ?_
        rw [ite_eq_right (by omega)]
        exact Sound.exit ⟨hk, fun ⟨x, hx'⟩ => hall x (by omega) hx'⟩
      | succ e ih' =>
        intro m regs₁ he hm hk hx hall
        have hmn : m < a.1 := by omega
        refine Sound.of_oblivious hE.one_le (hstep regs₁ hk m hx) ?_
        rw [ite_eq_left hmn]
        refine Sound.bind (hbody ⟨m, hmn⟩ regs₁ hk hx).1 fun regs₂ ⟨hk₂, hn₂⟩ => ?_
        have hx₂ : regs₂.getD base 0 = m := by rw [hk₂.getD_eq base (by omega), hx]
        refine Sound.of_oblivious hE.one_le
          (hinc regs₂ hk₂.bounded m hx₂ (by have := hE.card_le; omega)) ?_
        refine ih' (m + 1) _ (by omega) hmn
          (hk.trans ((hk₂.mono (by omega)).set_right le_rfl (by have := hE.card_le; omega)))
          (by rw [List.getD_set_self (by rw [hk₂.length_eq, hk.length_eq]; exact hlen)])
          fun x hxm => ?_
        rcases Nat.lt_succ_iff_lt_or_eq.mp hxm with hxm | hxm
        · exact hall x hxm
        · have : x = ⟨m, hmn⟩ := Fin.ext hxm
          exact this ▸ hn₂
    have keyC : ∀ e m (regs₁ : List ℕ), a.1 - m = e → m ≤ a.1 → Kept B base regs regs₁ →
        regs₁.getD base 0 = m → ¬ φ.ex.Realize TC.interpretation ρ val →
        Complete P (encStructure a) (b + 1) regs₁ T (Kept B base regs) := by
      intro e
      induction e with
      | zero =>
        intro m regs₁ he hm hk hx hn
        refine Complete.of_oblivious (hstep regs₁ hk m hx) ?_
        rw [ite_eq_right (by omega)]
        exact Complete.refl hk
      | succ e ih' =>
        intro m regs₁ he hm hk hx hn
        have hmn : m < a.1 := by omega
        refine Complete.of_oblivious (hstep regs₁ hk m hx) ?_
        rw [ite_eq_left hmn]
        refine Complete.bind ((hbody ⟨m, hmn⟩ regs₁ hk hx).2 fun h => hn ⟨⟨m, hmn⟩, h⟩)
          fun regs₂ hk₂ => ?_
        have hx₂ : regs₂.getD base 0 = m := by rw [hk₂.getD_eq base (by omega), hx]
        refine Complete.of_oblivious
          (hinc regs₂ hk₂.bounded m hx₂ (by have := hE.card_le; omega)) ?_
        exact ih' (m + 1) _ (by omega) hmn
          (hk.trans ((hk₂.mono (by omega)).set_right le_rfl (by have := hE.card_le; omega)))
          (by rw [List.getD_set_self (by rw [hk₂.length_eq, hk.length_eq]; exact hlen)]) hn
    have hk₀ : Kept B base regs (regs.set base 0) :=
      ⟨List.length_set .., fun i hi => List.getD_set_ne (by omega) .., hset 0 (Nat.zero_le _)⟩
    have hr₀ : P.Reaches (encStructure a) (P.Oblivious B) (b, 0 :: regs)
        (b + 1, 0 :: regs.set base 0) :=
      Reaches.sassign h₀ (Nat.zero_le B) hregs (Reaches.refl _)
    refine ⟨Sound.of_oblivious hE.one_le hr₀
      (key _ 0 _ rfl (Nat.zero_le _) hk₀ (List.getD_set_self hlen)
        fun x hx => absurd hx (by omega)),
      fun hn => Complete.of_oblivious hr₀
        (keyC _ 0 _ rfl (Nat.zero_le _) hk₀ (List.getD_set_self hlen) hn)⟩

end Correct

end Cslib.Logic.FO.Ordered.TCModelChecker
