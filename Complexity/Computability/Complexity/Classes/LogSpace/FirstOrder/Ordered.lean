/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.LogSpace.FirstOrder
public import Complexity.Logics.FirstOrder.Ordered.Basic

/-!
# Canonical ordered first-order model checking in logarithmic space

For each fixed sentence over a finite relational input vocabulary expanded by canonical numeric
symbols, its encoded query language belongs to `L`. Numeric `0`, `1`, `max`, order and BIT have
the actual meanings on `Fin n`, for `n ≥ 2`, including inside quantified formulas. They are
computed from cardinality and indices, with no extra numeric input tables.

The input uses `encStructure`: unary cardinality followed by the framed input relation tables in
`tupleIndex` order. Malformed table shapes and cardinalities below two are rejected. The space
bound is logarithmic in the full encoded input length; the sentence and vocabulary are fixed.
This is a theorem at that encoding, with no assertion about raw words outside its image.

The program reuses the existing shape checker and shared quantified control. Terms become native
counter expressions; input relations read their actual table bits, order compares values, and
BIT uses Christian Reitwiessner's binary digit algorithm, certified in linear work space in the
binary value and index. The counter-program simulation charges intermediate expression storage.

This establishes ordered model checking. Ordered interpretations are computed in logarithmic
space, and `L` and `P` are closed under ordered first-order reductions, in
`Complexity.Computability.Complexity.Classes.LogSpace.FirstOrder.Ordered.Reduction`; capture
remains open.

## Main definitions

* `Cslib.Logic.FO.Ordered.queryLanguage`: valid encodings satisfying a fixed ordered sentence.
* `Cslib.Logic.FO.Ordered.ModelChecker.termExpr`: native values of terms with numeric constants.
* `Cslib.Logic.FO.Ordered.modelChecker`: the actual counter-program decider.

## Main results

* `Cslib.Logic.FO.Ordered.ModelChecker.atomicCompiler_correct`: the concrete atomic handlers.
* `Cslib.Logic.FO.Ordered.queryLanguage_mem_L`: ordered first-order data complexity is in `L`.

## References

* [N. Immerman, *Descriptive Complexity*, Theorem 3.1, pp. 57–59][Immerman1999]. The proof's
  fixed-formula argument is used with the library's explicit framing and table-order conventions.
* The original order-free counter model checker and Christian Reitwiessner's native binary
  arithmetic and binary digit access are reused, with their source authorship retained.
-/

@[expose] public section

universe u v

open FirstOrder Language Structure Turing Turing.CounterProgram

namespace Cslib.Logic.FO.Ordered

variable {L : Language.{u, v}} [L.IsRelational] (v : Vocabulary L)

/-- Valid encodings of canonical ordered structures satisfying the fixed sentence. Cardinalities
zero and one are excluded; the numeric vocabulary is computed rather than encoded. -/
def queryLanguage (φ : (language L).Sentence) : Set EncodedStructure :=
  {a | v.WellFormed a ∧ ∃ hn : 2 ≤ a.1,
    letI : Fact (2 ≤ a.1) := ⟨hn⟩
    letI := v.decode a
    Fin a.1 ⊨ φ}

/-- On an admissible cardinality, query membership is exactly shape validity and canonical
ordered truth. -/
theorem mem_queryLanguage {a : EncodedStructure} [Fact (2 ≤ a.1)]
    (φ : (language L).Sentence) :
    a ∈ queryLanguage v φ ↔ v.WellFormed a ∧ (letI := v.decode a; Fin a.1 ⊨ φ) := by
  simp only [queryLanguage, Set.mem_ofPred_eq]
  exact and_congr_right fun _ => ⟨fun ⟨_, h⟩ => h, fun h => ⟨Fact.out, h⟩⟩

/-- Universes smaller than the standard ordered convention are rejected. -/
theorem notMem_queryLanguage_of_lt_two {a : EncodedStructure} (hn : a.1 < 2)
    (φ : (language L).Sentence) : a ∉ queryLanguage v φ :=
  fun h => (Nat.not_le_of_gt hn) h.2.choose

namespace ModelChecker

open Expr Vocabulary.ModelChecker

/-- Compile a term to its natural index: variables use assignment registers, and the numeric
constants are `0`, `1`, and the truncated predecessor of register `0` (the cardinality). -/
def termExpr {α : Type*} (fv : α → ℕ) (base : ℕ) {k : ℕ} :
    (language L).Term (α ⊕ Fin k) → Expr
  | .var x => reg (Sum.elim fv (fun i : Fin k => base + i) x)
  | .func (.inl f) _ => isEmptyElim f
  | .func (.inr .zero) _ => const 0
  | .func (.inr .one) _ => const 1
  | .func (.inr .max) _ => sub (reg 0) (const 1)

variable {v}

/-- Compiled terms realize genuine numeric constants as well as variables. -/
private theorem eval_termExpr {n : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)]
    {α : Type*} {fv : α → ℕ} {base k : ℕ} {regs : List ℕ}
    {val : α → Fin n} {xs : Fin k → Fin n} (h0 : regs.getD 0 0 = n)
    (hv : ∀ x, regs.getD (fv x) 0 = val x)
    (hxs : ∀ i : Fin k, regs.getD (base + i) 0 = xs i)
    (t : (language L).Term (α ⊕ Fin k)) :
    (termExpr fv base t).eval regs = (t.realize (Sum.elim val xs) : Fin n) := by
  cases t with
  | var x => cases x <;> first | exact hv _ | exact hxs _
  | func f ts =>
    cases f with
    | inl f => exact isEmptyElim f
    | inr f =>
      cases f with
      | zero => rfl
      | one => rfl
      | max => exact congrArg (· - 1) h0

variable (v)

/-- Actual native handlers for canonical ordered atoms. Input relations use their framed table;
order and BIT use only the compiled numeric arguments. -/
def atomicCompiler {α : Type*} (fv : α → ℕ) (base : ℕ) : AtomicCompiler (language L) α where
  term := termExpr fv base
  rel
    | .inl R, ts, T, F =>
      .read (bitExprWith v (v.index ⟨_, R⟩) fun m => termExpr fv base (ts m)) T F F
    | .inr .le, ts, T, F => .lt (termExpr fv base (ts 1)) (termExpr fv base (ts 0)) F T
    | .inr .bit, ts, T, F =>
      .lt (const 0) (Expr.bit (termExpr fv base (ts 0)) (termExpr fv base (ts 1))) T F

variable {v}

/-- The ordered handlers compute their canonical semantics from the original encoded input. -/
theorem atomicCompiler_correct {a : EncodedStructure} (ha : v.WellFormed a)
    [Fact (2 ≤ a.1)] {α : Type*} (fv : α → ℕ) (base : ℕ) (val : α → Fin a.1) :
    letI := v.decode a
    (atomicCompiler v fv base).Correct (encStructure a) fv base val := by
  let _ := v.decode a
  constructor
  · intro k regs xs h0 hv hxs t
    exact eval_termExpr h0 hv hxs t
  · intro k r R ts P b T F B regs xs h0 hv hxs hB hinstr
    have ht (i : Fin r) := eval_termExpr h0 hv hxs (ts i)
    cases R with
    | inl R =>
      set x : Fin r → Fin a.1 := fun m => (ts m).realize (Sum.elim val xs)
      have hi : v.index ⟨_, R⟩ < a.2.length := ha.1 ▸ v.index_lt _
      have htab : v.table a ⟨_, R⟩ = a.2[v.index ⟨_, R⟩] := List.getD_eq_getElem _ _ hi
      have hj : tupleIndex x < a.2[v.index ⟨_, R⟩].length := by
        rw [← htab, ha.length_table]
        exact tupleIndex_lt x
      have hpos := eval_bitExprWith ha h0 (v.index_lt ⟨_, R⟩).le
        (fun m => termExpr fv base (ts m)) x ht
      refine ⟨a.2[v.index ⟨_, R⟩][tupleIndex x], ?_, ?_⟩
      · change _ ↔ RelMap R x
        simp only [Vocabulary.relMap_decode, htab]
        rw [List.getD_eq_getElem _ _ hj]
      · refine Reaches.read hinstr hB ?_
        rw [hpos, getElem?_encStructure_tableStart_two_mul_add_one hi hj]
        cases a.2[v.index ⟨_, R⟩][tupleIndex x] <;> exact Reaches.refl _
    | inr R =>
      cases R with
      | le =>
        let x := (ts 0).realize (Sum.elim val xs)
        let y := (ts 1).realize (Sum.elim val xs)
        refine ⟨decide (x ≤ y), by simp only [decide_eq_true_eq]; rfl, ?_⟩
        refine Reaches.lt hinstr hB ?_
        simp only [ht]
        change P.Reaches _ _ (if y.val < x.val then F else T, regs)
          (if decide (x ≤ y) then T else F, regs)
        by_cases h : x ≤ y
        · simp only [show ¬ y.val < x.val from Nat.not_lt.mpr h, h, decide_true, ↓reduceIte]
          exact Reaches.refl _
        · simp only [show y.val < x.val from Nat.lt_of_not_ge h, h, decide_false, ↓reduceIte]
          exact Reaches.refl _
      | bit =>
        refine ⟨((ts 0).realize (Sum.elim val xs) : Fin a.1).val.testBit
          ((ts 1).realize (Sum.elim val xs)).val, Iff.rfl, ?_⟩
        refine Reaches.lt hinstr hB ?_
        simp only [eval_const, eval_bit, ht]
        cases ((ts 0).realize (Sum.elim val xs) : Fin a.1).val.testBit
          ((ts 1).realize (Sum.elim val xs)).val <;> exact Reaches.refl _

variable (v)

/-- Shared quantified control instantiated with the actual ordered handlers. -/
def formulaCode {α : Type*} (fv : α → ℕ) (base : ℕ) {k : ℕ}
    (φ : (language L).BoundedFormula α k) (b T F : ℕ) : List Instr :=
  formulaCodeWith (atomicCompiler v fv base) base φ b T F

private theorem length_formulaCode {α : Type*} (fv : α → ℕ) (base : ℕ) {k : ℕ}
    (φ : (language L).BoundedFormula α k) (b T F : ℕ) :
    (formulaCode v fv base φ b T F).length = codeLength φ :=
  length_formulaCodeWith _ _ _ _ _ _

variable {v}

/-- Evaluation of every ordered formula, including genuine constants inside quantified atoms. -/
private theorem reaches_formulaCode {P : CounterProgram} {a : EncodedStructure}
    (ha : v.WellFormed a)
    [Fact (2 ≤ a.1)] {B : ℕ} (hnB : a.1 ≤ B) {α : Type*} (fv : α → ℕ) (base : ℕ)
    (hbase : 0 < base) (hfv : ∀ x, fv x < base) (val : α → Fin a.1) :
    ∀ {k : ℕ} (φ : (language L).BoundedFormula α k) (b T F : ℕ)
      (regs : List ℕ) (xs : Fin k → Fin a.1),
      P.CodeAt b (formulaCode v fv base φ b T F) → base + boundDepth φ ≤ regs.length →
      regs.getD 0 0 = a.1 → (∀ r ∈ regs, r ≤ B) → (∀ x, regs.getD (fv x) 0 = val x) →
      (∀ i : Fin k, regs.getD (base + i) 0 = xs i) →
      ∃ (res : Bool) (regs' : List ℕ),
        (res = true ↔ (letI := v.decode a; φ.Realize val xs)) ∧
        P.Reaches (encStructure a) (P.Running B) (b, regs) (if res then T else F, regs') ∧
        regs'.length = regs.length ∧ (∀ i < base + k, regs'.getD i 0 = regs.getD i 0) ∧
        ∀ r ∈ regs', r ≤ B := by
  let _ := v.decode a
  intro k
  exact reaches_formulaCodeWith (P := P) hnB fv base hbase hfv val (atomicCompiler v fv base)
    (atomicCompiler_correct ha fv base val)

end ModelChecker

open Expr Vocabulary.ModelChecker

/-- The ordered sentence decider: validate the original input tables, reject cardinalities below
two, evaluate the sentence with native numeric handlers, and emit one Boolean verdict. -/
def modelChecker (φ : (language L).Sentence) : CounterProgram where
  code :=
    let E := 4 + 6 * v.count
    let A := E + 1 + codeLength φ
    let F := A + 1
    shapeCode v 0 E F ++ [.lt (reg 0) (const 2) F (E + 1)] ++
      ModelChecker.formulaCode v (fun e : Empty => e.elim) 3 φ (E + 1) A F ++ [.accept, .reject]
  registers := 3 + boundDepth φ

/-- Every fixed canonical ordered first-order query is in `L` at the actual structure encoding.
The native decider rejects malformed table shapes and sizes zero/one; its numeric symbols are
computed from the indices, including under quantifiers. -/
theorem queryLanguage_mem_L (φ : (language L).Sentence) :
    queryLanguage v φ ∈ Complexity.L encStructure := by
  classical
  refine ⟨fun a => decide (a ∈ queryLanguage v φ), ?_, fun a => by simp⟩
  refine (modelChecker v φ).computableInLogSpace_of_reaches v.maxArity fun a => ?_
  let E := 4 + 6 * v.count
  let A := E + 1 + codeLength φ
  let F := A + 1
  have hE : (shapeCode v 0 E F).length = E := length_shapeCode v 0 E F
  have hC := ModelChecker.length_formulaCode v (fun e : Empty => e.elim) 3 φ (E + 1) A F
  have hcode : (modelChecker v φ).CodeAt 0 (modelChecker v φ).code :=
    codeAt_of_code_eq (pre := []) (post := []) (by simp)
  change (modelChecker v φ).CodeAt 0 (shapeCode v 0 E F ++
    [.lt (reg 0) (const 2) F (E + 1)] ++
    ModelChecker.formulaCode v (fun e : Empty => e.elim) 3 φ (E + 1) A F ++
    [.accept, .reject]) at hcode
  rw [codeAt_append, codeAt_append, codeAt_append] at hcode
  obtain ⟨⟨⟨hshape, hguard⟩, hcomp⟩, hhalt⟩ := hcode
  simp only [List.length_append, hE, hC, List.length_singleton, Nat.zero_add]
    at hguard hcomp hhalt
  obtain ⟨hacc, hrest⟩ := codeAt_cons.mp hhalt
  have hrej := (codeAt_cons.mp hrest).1
  replace hguard := (codeAt_cons.mp hguard).1
  have hwB := length_le_pow_maxArity v a
  have hnB := (card_le_length_encStructure a).trans hwB
  obtain ⟨regs₁, hreach₁, hlen₁, h0₁, hB₁⟩ :=
    reaches_shapeCode hshape (pow_arityAt_le v a) hwB (List.replicate (3 + boundDepth φ) 0)
      (by simp) (by simp) (by simp)
  by_cases hwf : v.WellFormed a
  · rw [ite_eq_left hwf] at hreach₁
    have hreachGuard : (modelChecker v φ).Reaches (encStructure a)
        ((modelChecker v φ).Running (((encStructure a).length + 1) ^ v.maxArity))
        (E, regs₁) (if a.1 < 2 then F else E + 1, regs₁) := by
      refine Reaches.lt hguard hB₁ ?_
      simp only [eval_reg, eval_const, h0₁ hwf]
      exact Reaches.refl _
    by_cases hn : 2 ≤ a.1
    · let _ : Fact (2 ≤ a.1) := ⟨hn⟩
      rw [ite_eq_right (Nat.not_lt.mpr hn)] at hreachGuard
      obtain ⟨res, regs₂, hres, hreach₂, -, -, hB₂⟩ :=
        ModelChecker.reaches_formulaCode hwf hnB (fun e : Empty => e.elim) 3 (by decide)
          (fun e => e.elim) default φ _ _ _ regs₁ default hcomp (by rw [hlen₁]; simp)
          (h0₁ hwf) hB₁ (fun e => e.elim) (fun i => i.elim0)
      refine ⟨(if res then A else F, regs₂), (hreach₁.trans hreachGuard).trans hreach₂, ?_, hB₂⟩
      have hmem : a ∈ queryLanguage v φ ↔ res = true := by
        rw [mem_queryLanguage v φ, hres]
        exact and_iff_right hwf
      cases res
      · rw [ite_eq_right Bool.false_ne_true, hrej]
        simp [hmem]
      · rw [ite_eq_left rfl, hacc]
        simp [hmem]
    · rw [ite_eq_left (Nat.lt_of_not_ge hn)] at hreachGuard
      refine ⟨(F, regs₁), hreach₁.trans hreachGuard, ?_, hB₁⟩
      rw [hrej]
      simp [notMem_queryLanguage_of_lt_two v (Nat.lt_of_not_ge hn) φ]
  · rw [ite_eq_right hwf] at hreach₁
    refine ⟨(F, regs₁), hreach₁, ?_, hB₁⟩
    rw [hrej]
    simp [queryLanguage, hwf]

end Cslib.Logic.FO.Ordered
