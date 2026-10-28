/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.LogSpace
public import Complexity.Computability.Complexity.Classes.LogSpace.FirstOrder.Formula
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram
public import Complexity.Logics.FirstOrder.Encoding.Layout
import Complexity.Foundations.Data.List.Lookup

/-!
# First-order model checking in logarithmic space

For every finite relational vocabulary and every first-order sentence `φ`, the inputs encoding
the finite structures satisfying `φ`, with malformed inputs rejected, form a problem in `L`
(`Cslib.Logic.Vocabulary.queryLanguage_mem_L`); so does the query language of every first-order
definable class of finite structures (`Cslib.Logic.FO.Definable.queryLanguage_mem_L`)
[Immerman, Theorem 3.1][Immerman1999]. The sentences are those of Mathlib's first-order logic over
the relational language: atomic formulas are equalities and relation symbols applied to
variables. Immerman's logic `FO` also has constant symbols and the built-in numeric predicates `≤`
and `BIT`; those are not covered here (a relational language has no constant symbols).

The helpers of the construction live in the namespace `Cslib.Logic.Vocabulary.ModelChecker`.

The decider is a counter program (`Turing.CounterProgram`) with random access to the encoded input
(`Cslib.Logic.Vocabulary.modelChecker`). It first checks the shape of the input
(`Cslib.Logic.Vocabulary.ModelChecker.shapeCode`): it counts the unary cardinality `n` by reading
the markers of its frame, then for each relation symbol checks, with a counter, that the next frame
holds exactly `n ^ k` bits for the arity `k` of the symbol, and finally that nothing follows the
last table. It then evaluates `φ` recursively
(`Cslib.Logic.Vocabulary.ModelChecker.formulaCode`), with one register per quantified variable, so
as many registers as the nesting depth of quantifiers, a constant of `φ`.
A quantifier loops over the values below `n`; an atomic formula compares two registers or reads
the bit of a truth table at the position computed from the registers by index arithmetic
(`Cslib.Logic.tupleIndex`). The compilation passes each subformula the labels to continue at when
it is true and when it is false, so the program needs no stack. Every register stays below a
polynomial in the input length, so the program runs in logarithmic space
(`Turing.CounterProgram.computableInLogSpace_of_reaches`).

The empty structure, `n = 0`, is included: universal quantifiers hold and existential ones fail
vacuously, and nullary relations are read from their one-bit tables.

## Main definitions

* `Cslib.Logic.Vocabulary.ModelChecker.shapeCode`: the code checking that an input is well formed.
* `Cslib.Logic.Vocabulary.ModelChecker.formulaCode`: the code evaluating a formula.
* `Cslib.Logic.Vocabulary.modelChecker`: the counter program deciding a sentence.

## Main results

* `Cslib.Logic.Vocabulary.ModelChecker.reaches_shapeCode`: the shape check accepts exactly the
  well-formed inputs.
* `Cslib.Logic.Vocabulary.ModelChecker.reaches_formulaCode`: the compiled code of a formula decides
  its truth in the decoded structure.
* `Cslib.Logic.Vocabulary.queryLanguage_mem_L`: first-order model checking is in `L`.
* `Cslib.Logic.FO.Definable.queryLanguage_mem_L`: the query language of a first-order definable
  class is in `L`.

## References

* [N. Immerman, *Descriptive Complexity*, Theorem 3.1][Immerman1999]
* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.4][Sipser2013]
-/

@[expose] public section

universe u v

open FirstOrder Language Structure CategoryTheory Turing Turing.CounterProgram

namespace Cslib.Logic

namespace Vocabulary

open FO Expr

variable {L : Language.{u, v}} (v : Vocabulary L)

namespace ModelChecker

/-! ### Index arithmetic -/

/-- The arity of the symbol at a position, `0` past the last one. -/
def arityAt (i : ℕ) : ℕ := if h : i < v.count then v.arity ⟨i, h⟩ else 0

/-- The number of bits of the table at a position, `n ^ k` for the cardinality `n` in register `0`
and the arity `k`. -/
def lenExpr (i : ℕ) : Expr := pow (reg 0) (arityAt v i)

/-- The position of the table at a position in a well-formed input. -/
def startExpr (i : ℕ) : Expr :=
  add (add (mul (const 2) (reg 0)) (const 1))
    (sum (List.ofFn fun j : Fin i => add (mul (const 2) (lenExpr v j)) (const 1)))

/-- The table index of a tuple of computed values. -/
def tupleExprWith {l : ℕ} (values : Fin l → Expr) : Expr :=
  sum (List.ofFn fun m : Fin l => mul (values m) (pow (reg 0) m))

/-- The index of the tuple of values of some registers. -/
def tupleExpr {l : ℕ} (vars : Fin l → ℕ) : Expr :=
  tupleExprWith fun m => reg (vars m)

/-- The position of a relation-table bit for a tuple of computed values. -/
def bitExprWith (i : ℕ) {l : ℕ} (values : Fin l → Expr) : Expr :=
  add (add (startExpr v i) (mul (const 2) (tupleExprWith values))) (const 1)

/-- The position of the bit of the table at position `i` at the tuple of values of some
registers, in a well-formed input. -/
def bitExpr (i : ℕ) {l : ℕ} (vars : Fin l → ℕ) : Expr :=
  bitExprWith v i fun m => reg (vars m)

variable {v}

private theorem eval_tupleExprWith {l n : ℕ} (values : Fin l → Expr) {regs : List ℕ}
    (h0 : regs.getD 0 0 = n) (x : Fin l → Fin n)
    (hx : ∀ m, (values m).eval regs = x m) :
    (tupleExprWith values).eval regs = tupleIndex x := by
  simp only [tupleExprWith, eval_sum, List.map_ofFn, List.sum_ofFn, Function.comp_def, eval_mul,
    eval_reg, eval_pow, hx, h0, tupleIndex_apply]

theorem eval_tupleExpr {l n : ℕ} (vars : Fin l → ℕ) {regs : List ℕ} (h0 : regs.getD 0 0 = n)
    (x : Fin l → Fin n) (hx : ∀ m, regs.getD (vars m) 0 = x m) :
    (tupleExpr vars).eval regs = tupleIndex x :=
  eval_tupleExprWith _ h0 x hx

private theorem eval_startExpr {a : EncodedStructure} (ha : v.WellFormed a) {regs : List ℕ}
    (h0 : regs.getD 0 0 = a.1) {i : ℕ} (hi : i ≤ v.count) :
    (startExpr v i).eval regs = tableStart a i := by
  simp only [startExpr, eval_add, eval_mul, eval_const, eval_reg, h0, eval_sum, List.map_ofFn,
    tableStart]
  congr 1
  have hl : (a.2.take i).map (fun t => 2 * t.length + 1) =
      List.ofFn (fun j : Fin i => 2 * a.1 ^ arityAt v j + 1) := by
    refine List.ext_getElem
      (by simp only [List.length_map, List.length_take, List.length_ofFn, ha.1]; omega)
      fun j h₁ h₂ => ?_
    simp only [List.getElem_map, List.getElem_take, List.getElem_ofFn]
    have hj : j < v.count := by simp only [List.length_ofFn] at h₂; omega
    have := ha.2 ⟨j, hj⟩
    rw [List.getD_eq_getElem _ _ (by rw [ha.1]; exact hj)] at this
    rw [this]
    simp [arityAt, hj]
  rw [hl, List.sum_ofFn, List.sum_ofFn]
  simp only [Function.comp_def, lenExpr, eval_add, eval_mul, eval_const, eval_pow, eval_reg, h0]

theorem eval_bitExprWith {a : EncodedStructure} (ha : v.WellFormed a) {regs : List ℕ}
    (h0 : regs.getD 0 0 = a.1) {i : ℕ} (hi : i ≤ v.count) {l : ℕ}
    (values : Fin l → Expr) (x : Fin l → Fin a.1)
    (hx : ∀ m, (values m).eval regs = x m) :
    (bitExprWith v i values).eval regs = tableStart a i + 2 * tupleIndex x + 1 := by
  simp only [bitExprWith, eval_add, eval_mul, eval_const, eval_startExpr ha h0 hi,
    eval_tupleExprWith values h0 x hx]

private theorem eval_bitExpr {a : EncodedStructure} (ha : v.WellFormed a) {regs : List ℕ}
    (h0 : regs.getD 0 0 = a.1) {i : ℕ} (hi : i ≤ v.count) {l : ℕ} (vars : Fin l → ℕ)
    (x : Fin l → Fin a.1) (hx : ∀ m, regs.getD (vars m) 0 = x m) :
    (bitExpr v i vars).eval regs = tableStart a i + 2 * tupleIndex x + 1 :=
  eval_bitExprWith ha h0 hi _ x hx

/-! ### Checking the shape of the input -/

section Shape

variable (v)

/-- The code checking the table at position `i`, placed at the label `c`, with the cardinality `n`
in register `0` and the position of the table in register `1`: register `2` counts the markers of
the table up to `n ^ k`, for the arity `k` of the symbol; then the code checks the terminator,
moves register `1` past the table and goes to `c + 6`. It goes to `F` on a missing marker, a
missing terminator, or the end of the input. -/
def tableCode (c i F : ℕ) : List Instr :=
  [.assign 2 (const 0) (c + 1),
   .lt (reg 2) (lenExpr v i) (c + 2) (c + 3),
   .read (add (reg 1) (mul (const 2) (reg 2))) (c + 4) F F,
   .read (add (reg 1) (mul (const 2) (lenExpr v i))) F (c + 5) F,
   .assign 2 (add (reg 2) (const 1)) (c + 1),
   .assign 1 (add (add (reg 1) (mul (const 2) (lenExpr v i))) (const 1)) (c + 6)]

/-- The code checking that an input is well formed, placed at the label `b`, with register `0`
holding `0`: it counts the markers of the unary cardinality into register `0`, checks every table
(`Cslib.Logic.Vocabulary.ModelChecker.tableCode`), and checks that the input ends after the last
table. It goes to `T` if the input is well formed, with its cardinality in register `0`, and to `F`
otherwise. -/
def shapeCode (b T F : ℕ) : List Instr :=
  [.read (mul (const 2) (reg 0)) (b + 1) (b + 2) F,
   .assign 0 (add (reg 0) (const 1)) b,
   .assign 1 (add (mul (const 2) (reg 0)) (const 1)) (b + 3)] ++
  (List.range v.count).flatMap (fun i => tableCode v (b + 3 + 6 * i) i F) ++
  [.read (reg 1) F F T]

private theorem length_tableCode (c i F : ℕ) : (tableCode v c i F).length = 6 := rfl

private theorem length_tables (b F : ℕ) :
    ((List.range v.count).flatMap fun i => tableCode v (b + 3 + 6 * i) i F).length =
      6 * v.count := by
  rw [List.length_flatMap]
  simp [length_tableCode, Nat.mul_comm]

theorem length_shapeCode (b T F : ℕ) : (shapeCode v b T F).length = 4 + 6 * v.count := by
  rw [shapeCode, List.length_append, List.length_append, length_tables]
  simp only [List.length_cons, List.length_nil]
  omega

/-- The table at position `i` exists and has `n ^ k` bits, for the arity `k` of the symbol. -/
def TableOk (a : EncodedStructure) (i : ℕ) : Prop :=
  ∃ h : i < a.2.length, a.2[i].length = a.1 ^ arityAt v i

instance (a : EncodedStructure) (i : ℕ) : Decidable (TableOk v a i) :=
  inferInstanceAs (Decidable (∃ h : i < a.2.length, a.2[i].length = a.1 ^ arityAt v i))

variable {v}

private theorem wellFormed_iff_tableOk {a : EncodedStructure} :
    v.WellFormed a ↔ (∀ i < v.count, TableOk v a i) ∧ a.2.length = v.count := by
  constructor
  · rintro ⟨hlen, htab⟩
    refine ⟨fun i hi => ⟨by omega, ?_⟩, hlen⟩
    have hai : arityAt v i = v.arity ⟨i, hi⟩ := by simp [arityAt, hi]
    have := htab ⟨i, hi⟩
    have hi' : i < a.2.length := by omega
    rwa [List.getD_eq_getElem _ _ hi', ← hai] at this
  · rintro ⟨hok, hlen⟩
    refine ⟨hlen, fun i => ?_⟩
    obtain ⟨hi, h⟩ := hok i i.2
    rw [List.getD_eq_getElem _ _ hi, h]
    simp [arityAt]

variable {P : CounterProgram} {a : EncodedStructure} {B : ℕ}

private theorem eval_lenExpr {regs : List ℕ} (h0 : regs.getD 0 0 = a.1) (i : ℕ) :
    (lenExpr v i).eval regs = a.1 ^ arityAt v i := by
  simp only [lenExpr, eval_pow, eval_reg, h0]

/-- Counting the markers of the unary cardinality. -/
private theorem reaches_count {b F : ℕ}
    (h₀ : P.instr b = .read (mul (const 2) (reg 0)) (b + 1) (b + 2) F)
    (h₁ : P.instr (b + 1) = .assign 0 (add (reg 0) (const 1)) b) (hnB : a.1 ≤ B) :
    ∀ e (regs : List ℕ), a.1 - regs.getD 0 0 = e → regs.getD 0 0 ≤ a.1 → 0 < regs.length →
      (∀ r ∈ regs, r ≤ B) →
      ∃ regs', P.Reaches (encStructure a) (P.Running B) (b, regs) (b + 2, regs') ∧
        regs'.length = regs.length ∧ regs'.getD 0 0 = a.1 ∧ ∀ r ∈ regs', r ≤ B := by
  intro e
  induction e with
  | zero =>
    intro regs he hle _ hB
    have hk : regs.getD 0 0 = a.1 := by omega
    refine ⟨regs, ?_, rfl, hk, hB⟩
    refine Reaches.read h₀ hB ?_
    simp only [eval_mul, eval_const, eval_reg, hk, getElem?_encStructure_two_mul_card]
    exact Reaches.refl _
  | succ e ih =>
    intro regs he hle hlen hB
    have hlt : regs.getD 0 0 < a.1 := by omega
    obtain ⟨regs', hreach, hlen', h0', hB'⟩ := ih (regs.set 0 (regs.getD 0 0 + 1))
      (by rw [List.getD_set_self hlen]; omega) (by rw [List.getD_set_self hlen]; omega)
      (by simpa using hlen) (List.forall_mem_set_of_forall_mem hB (by omega))
    refine ⟨regs', ?_, by simpa using hlen', h0', hB'⟩
    refine Reaches.read h₀ hB ?_
    simp only [eval_mul, eval_const, eval_reg, getElem?_encStructure_two_mul hlt]
    exact Reaches.assign h₁ hB (by simpa using hreach)

/-- The markers of a table, counted up to `n ^ k`. -/
private theorem reaches_markers {c i F : ℕ} (hP : P.CodeAt c (tableCode v c i F))
    (hi : i < a.2.length) (hLB : a.1 ^ arityAt v i ≤ B) :
    ∀ e j (regs : List ℕ), a.1 ^ arityAt v i - j = e → j ≤ a.1 ^ arityAt v i →
      j ≤ a.2[i].length → regs.getD 0 0 = a.1 → regs.getD 1 0 = tableStart a i →
      regs.getD 2 0 = j → 3 ≤ regs.length → (∀ r ∈ regs, r ≤ B) →
      ∃ regs', P.Reaches (encStructure a) (P.Running B) (c + 1, regs)
        (if a.1 ^ arityAt v i ≤ a.2[i].length then c + 3 else F, regs') ∧
        regs'.length = regs.length ∧ regs'.getD 0 0 = a.1 ∧ regs'.getD 1 0 = tableStart a i ∧
        (a.1 ^ arityAt v i ≤ a.2[i].length → regs'.getD 2 0 = a.1 ^ arityAt v i) ∧
        ∀ r ∈ regs', r ≤ B := by
  simp only [tableCode, codeAt_cons] at hP
  obtain ⟨-, h₁, h₂, -, h₄, -, -⟩ := hP
  rw [show c + 1 + 1 = c + 2 by omega] at h₂
  rw [show c + 1 + 1 + 1 + 1 = c + 4 by omega] at h₄
  intro e
  induction e with
  | zero =>
    intro j regs he hjL hjt h0 h1 h2 hlen hB
    have hj : j = a.1 ^ arityAt v i := by omega
    refine ⟨regs, ?_, rfl, h0, h1, fun _ => h2.trans hj, hB⟩
    refine Reaches.lt h₁ hB ?_
    simp only [eval_reg, eval_lenExpr h0, h2, hj, lt_irrefl, ↓reduceIte,
      show a.1 ^ arityAt v i ≤ a.2[i].length by omega]
    exact Reaches.refl _
  | succ e ih =>
    intro j regs he hjL hjt h0 h1 h2 hlen hB
    have hjL' : j < a.1 ^ arityAt v i := by omega
    rcases lt_or_eq_of_le hjt with hjt' | hjt'
    · obtain ⟨regs', hreach, hlen', h0', h1', h2', hB'⟩ :=
        ih (j + 1) (regs.set 2 (j + 1)) (by omega) (by omega) (by omega)
          (by rw [List.getD_set_ne (by omega), h0]) (by rw [List.getD_set_ne (by omega), h1])
          (List.getD_set_self (by omega)) (by simpa using hlen)
          (List.forall_mem_set_of_forall_mem hB (by omega))
      refine ⟨regs', ?_, by simpa using hlen', h0', h1', h2', hB'⟩
      refine Reaches.lt h₁ hB ?_
      simp only [eval_reg, eval_lenExpr h0, h2, hjL', ↓reduceIte]
      refine Reaches.read h₂ hB ?_
      simp only [eval_add, eval_mul, eval_const, eval_reg, h1, h2,
        getElem?_encStructure_tableStart_two_mul hi hjt', readLabel]
      refine Reaches.assign h₄ hB ?_
      simp only [eval_add, eval_reg, eval_const, h2]
      exact hreach
    · refine ⟨regs, ?_, rfl, h0, h1, fun h => absurd h (by omega), hB⟩
      refine Reaches.lt h₁ hB ?_
      simp only [eval_reg, eval_lenExpr h0, h2, hjL', ↓reduceIte]
      refine Reaches.read h₂ hB ?_
      simp only [eval_add, eval_mul, eval_const, eval_reg, h1, h2, hjt',
        getElem?_encStructure_tableStart_two_mul_length hi, readLabel,
        show ¬ (a.1 ^ arityAt v i ≤ a.2[i].length) by omega, ↓reduceIte]
      exact Reaches.refl _

/-- **Checking a table**: from the code of the table at position `i ≤ |tables|`, with the
cardinality in register `0` and the position of the table in register `1`, the program moves
register `1` past the table and goes to `c + 6` if the table exists and has `n ^ k` bits, and goes
to `F` otherwise. -/
private theorem reaches_tableCode {c i F : ℕ} (hP : P.CodeAt c (tableCode v c i F))
    (hi : i ≤ a.2.length) (hLB : a.1 ^ arityAt v i ≤ B) (hwB : (encStructure a).length ≤ B)
    (regs : List ℕ) (h0 : regs.getD 0 0 = a.1) (h1 : regs.getD 1 0 = tableStart a i)
    (hlen : 3 ≤ regs.length) (hB : ∀ r ∈ regs, r ≤ B) :
    ∃ regs', P.Reaches (encStructure a) (P.Running B) (c, regs)
      (if TableOk v a i then c + 6 else F, regs') ∧ regs'.length = regs.length ∧
      regs'.getD 0 0 = a.1 ∧ (TableOk v a i → regs'.getD 1 0 = tableStart a (i + 1)) ∧
      ∀ r ∈ regs', r ≤ B := by
  have hP' := hP
  simp only [tableCode, codeAt_cons] at hP'
  obtain ⟨h₀, h₁, h₂, h₃, -, h₅, -⟩ := hP'
  rw [show c + 1 + 1 = c + 2 by omega] at h₂
  rw [show c + 1 + 1 + 1 = c + 3 by omega] at h₃
  rw [show c + 1 + 1 + 1 + 1 + 1 = c + 5 by omega] at h₅
  have hB₀ : ∀ r ∈ regs.set 2 0, r ≤ B := List.forall_mem_set_of_forall_mem hB (Nat.zero_le _)
  have h0' : (regs.set 2 0).getD 0 0 = a.1 := by rw [List.getD_set_ne (by omega), h0]
  have h1' : (regs.set 2 0).getD 1 0 = tableStart a i := by rw [List.getD_set_ne (by omega), h1]
  have h2' : (regs.set 2 0).getD 2 0 = 0 := List.getD_set_self (by omega)
  rcases lt_or_eq_of_le hi with hi | hi
  · -- the table exists
    obtain ⟨regs₁, hreach₁, hlen₁, h0₁, h1₁, h2₁, hB₁⟩ :=
      reaches_markers hP hi hLB (a.1 ^ arityAt v i - 0) 0 (regs.set 2 0) rfl (Nat.zero_le _)
        (Nat.zero_le _) h0' h1' h2' (by simpa using hlen) hB₀
    by_cases hLt : a.1 ^ arityAt v i ≤ a.2[i].length
    · have hreach₁' : P.Reaches (encStructure a) (P.Running B) (c + 1, regs.set 2 0)
          (c + 3, regs₁) := by simpa [hLt] using hreach₁
      rcases lt_or_eq_of_le hLt with hlt | heq
      · -- too many bits
        have hok : ¬ TableOk v a i := fun ⟨_, h⟩ => by omega
        refine ⟨regs₁, ?_, by simpa using hlen₁, h0₁, fun h => absurd h hok, hB₁⟩
        simp only [hok, ↓reduceIte]
        refine Reaches.assign h₀ hB (hreach₁'.trans ?_)
        refine Reaches.read h₃ hB₁ ?_
        simp only [eval_add, eval_mul, eval_const, eval_reg, eval_lenExpr h0₁, h1₁,
          getElem?_encStructure_tableStart_two_mul hi hlt, readLabel]
        exact Reaches.refl _
      · -- exactly `n ^ k` bits
        have hok : TableOk v a i := ⟨hi, heq.symm⟩
        have hnext : tableStart a i + 2 * a.1 ^ arityAt v i + 1 = tableStart a (i + 1) := by
          rw [tableStart_succ hi, heq]
        refine ⟨regs₁.set 1 (tableStart a i + 2 * a.1 ^ arityAt v i + 1), ?_,
          by simp [hlen₁], by rw [List.getD_set_ne (by omega), h0₁], fun _ => ?_,
          List.forall_mem_set_of_forall_mem hB₁ ?_⟩
        · simp only [hok, ↓reduceIte]
          refine Reaches.assign h₀ hB (hreach₁'.trans ?_)
          refine Reaches.read h₃ hB₁ ?_
          simp only [eval_add, eval_mul, eval_const, eval_reg, eval_lenExpr h0₁, h1₁, heq,
            getElem?_encStructure_tableStart_two_mul_length hi, readLabel]
          refine Reaches.assign h₅ hB₁ ?_
          simp only [eval_add, eval_mul, eval_const, eval_reg, eval_lenExpr h0₁, h1₁, heq]
          exact Reaches.refl _
        · rw [List.getD_set_self (by simp only [List.length_set] at hlen₁; omega), hnext]
        · rw [hnext]
          exact (tableStart_le_length a _).trans hwB
    · -- too few bits
      have hok : ¬ TableOk v a i := fun ⟨_, h⟩ => by omega
      refine ⟨regs₁, ?_, by simpa using hlen₁, h0₁, fun h => absurd h hok, hB₁⟩
      simp only [hok, ↓reduceIte]
      exact Reaches.assign h₀ hB (by simpa [hLt] using hreach₁)
  · -- no table
    have hok : ¬ TableOk v a i := fun ⟨h, _⟩ => by omega
    have hend (q : ℕ) : (encStructure a)[tableStart a i + q]? = none := by
      rw [hi]
      exact getElem?_encStructure_tableStart_length_add a q
    refine ⟨regs.set 2 0, ?_, by simp, h0', fun h => absurd h hok, hB₀⟩
    simp only [hok, ↓reduceIte]
    refine Reaches.assign h₀ hB ?_
    refine Reaches.lt h₁ hB₀ ?_
    simp only [eval_const, eval_reg, eval_lenExpr h0', h2']
    by_cases hL0 : 0 < a.1 ^ arityAt v i
    · simp only [hL0, ↓reduceIte]
      refine Reaches.read h₂ hB₀ ?_
      simp only [eval_add, eval_mul, eval_const, eval_reg, h1', h2', hend, readLabel]
      exact Reaches.refl _
    · simp only [hL0, ↓reduceIte]
      refine Reaches.read h₃ hB₀ ?_
      simp only [eval_add, eval_mul, eval_const, eval_reg, eval_lenExpr h0', h1',
        show a.1 ^ arityAt v i = 0 by omega, hend, readLabel]
      exact Reaches.refl _

/-- **Checking the tables**, from the table at position `m` on. -/
private theorem reaches_tables {b F : ℕ}
    (hP : P.CodeAt (b + 3) ((List.range v.count).flatMap fun i => tableCode v (b + 3 + 6 * i) i F))
    (hLB : ∀ i, a.1 ^ arityAt v i ≤ B) (hwB : (encStructure a).length ≤ B) :
    ∀ e m (regs : List ℕ), v.count - m = e → m ≤ v.count → (∀ i < m, TableOk v a i) →
      regs.getD 0 0 = a.1 → regs.getD 1 0 = tableStart a m → 3 ≤ regs.length →
      (∀ r ∈ regs, r ≤ B) →
      ∃ regs', P.Reaches (encStructure a) (P.Running B) (b + 3 + 6 * m, regs)
        (if ∀ i < v.count, TableOk v a i then b + 3 + 6 * v.count else F, regs') ∧
        regs'.length = regs.length ∧ regs'.getD 0 0 = a.1 ∧
        ((∀ i < v.count, TableOk v a i) → regs'.getD 1 0 = tableStart a v.count) ∧
        ∀ r ∈ regs', r ≤ B := by
  intro e
  induction e with
  | zero =>
    intro m regs he hm hok h0 h1 hlen hB
    have hm' : m = v.count := by omega
    subst hm'
    refine ⟨regs, ?_, rfl, h0, fun _ => h1, hB⟩
    rw [ite_eq_left hok]
    exact Reaches.refl _
  | succ e ih =>
    intro m regs he hm hok h0 h1 hlen hB
    have hmc : m < v.count := by omega
    have hma : m ≤ a.2.length := by
      rcases Nat.eq_zero_or_pos m with h | h
      · omega
      · obtain ⟨h', -⟩ := hok (m - 1) (by omega)
        omega
    obtain ⟨regs₁, hreach₁, hlen₁, h0₁, h1₁, hB₁⟩ :=
      reaches_tableCode (CodeAt.flatMap_range (f := fun i => tableCode v (b + 3 + 6 * i) i F)
        (fun i => length_tableCode v _ i F) hP m hmc) hma (hLB m) hwB regs h0 h1 hlen hB
    by_cases hokm : TableOk v a m
    · obtain ⟨regs₂, hreach₂, hlen₂, h0₂, h1₂, hB₂⟩ :=
        ih (m + 1) regs₁ (by omega) (by omega)
          (fun i hi => by
            rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with h | h
            · exact hok i h
            · exact h ▸ hokm)
          h0₁ (h1₁ hokm) (hlen₁ ▸ hlen) hB₁
      refine ⟨regs₂, ?_, hlen₂.trans hlen₁, h0₂, h1₂, hB₂⟩
      refine (show P.Reaches _ _ _ (b + 3 + 6 * m + 6, regs₁) by simpa [hokm] using hreach₁).trans
        ?_
      rw [show b + 3 + 6 * m + 6 = b + 3 + 6 * (m + 1) by ring]
      exact hreach₂
    · have hall : ¬ ∀ i < v.count, TableOk v a i := fun h => hokm (h m hmc)
      refine ⟨regs₁, ?_, hlen₁, h0₁, fun h => absurd h hall, hB₁⟩
      simpa [hokm, hall] using hreach₁

/-- **The shape check accepts exactly the well-formed inputs**: from the code of the shape check,
with register `0` holding `0`, the program goes to `T` with the cardinality in register `0` if the
input is well formed, and to `F` otherwise. The registers stay below `B` if `B` bounds the length
of the input and the sizes `n ^ k` of the tables. -/
theorem reaches_shapeCode {b T F : ℕ} (hP : P.CodeAt b (shapeCode v b T F))
    (hLB : ∀ i, a.1 ^ arityAt v i ≤ B) (hwB : (encStructure a).length ≤ B) (regs : List ℕ)
    (h0 : regs.getD 0 0 = 0) (hlen : 3 ≤ regs.length) (hB : ∀ r ∈ regs, r ≤ B) :
    ∃ regs', P.Reaches (encStructure a) (P.Running B) (b, regs)
      (if v.WellFormed a then T else F, regs') ∧ regs'.length = regs.length ∧
      (v.WellFormed a → regs'.getD 0 0 = a.1) ∧ ∀ r ∈ regs', r ≤ B := by
  rw [shapeCode, codeAt_append, codeAt_append, List.length_append, length_tables] at hP
  obtain ⟨⟨h₃, htab⟩, hend⟩ := hP
  simp only [codeAt_cons, List.length_cons, List.length_nil] at h₃ htab hend
  obtain ⟨h₀, h₁, h₂, -⟩ := h₃
  rw [show b + 1 + 1 = b + 2 by omega] at h₂
  rw [show b + (0 + 1 + 1 + 1) = b + 3 by omega] at htab
  rw [show b + (0 + 1 + 1 + 1 + 6 * v.count) = b + 3 + 6 * v.count by omega] at hend
  replace hend := hend.1
  have hnB : a.1 ≤ B := (card_le_length_encStructure a).trans hwB
  -- the cardinality
  obtain ⟨regs₁, hreach₁, hlen₁, h0₁, hB₁⟩ :=
    reaches_count h₀ h₁ hnB (a.1 - regs.getD 0 0) regs rfl (by omega) (by omega) hB
  have hstart : 2 * a.1 + 1 = tableStart a 0 := by simp [tableStart]
  have hB₁' : ∀ r ∈ regs₁.set 1 (2 * a.1 + 1), r ≤ B :=
    List.forall_mem_set_of_forall_mem hB₁ ((two_mul_card_add_one_le_length a).trans hwB)
  -- the tables
  obtain ⟨regs₂, hreach₂, hlen₂, h0₂, h1₂, hB₂⟩ :=
    reaches_tables htab hLB hwB (v.count - 0) 0 (regs₁.set 1 (2 * a.1 + 1)) rfl
      (Nat.zero_le _) (fun _ h => absurd h (by omega))
      (by rw [List.getD_set_ne (by omega), h0₁])
      (by rw [List.getD_set_self (by omega), hstart]) (by simp only [List.length_set]; omega) hB₁'
  have hreach : P.Reaches (encStructure a) (P.Running B) (b, regs)
      (if ∀ i < v.count, TableOk v a i then b + 3 + 6 * v.count else F, regs₂) := by
    refine hreach₁.trans (Reaches.assign h₂ hB₁ ?_)
    simp only [eval_add, eval_mul, eval_const, eval_reg, h0₁]
    simpa using hreach₂
  by_cases hall : ∀ i < v.count, TableOk v a i
  · -- the end of the input
    have hca : v.count ≤ a.2.length := by
      rcases Nat.eq_zero_or_pos v.count with h | h
      · omega
      · obtain ⟨h', -⟩ := hall (v.count - 1) (by omega)
        omega
    rw [ite_eq_left hall] at hreach
    replace h1₂ := h1₂ hall
    refine ⟨regs₂, hreach.trans (Reaches.read hend hB₂ ?_), by simp [hlen₂, hlen₁],
      fun _ => h0₂, hB₂⟩
    simp only [eval_reg, h1₂]
    rcases lt_or_eq_of_le hca with hlt | heq
    · have hwf : ¬ v.WellFormed a := fun h => by
        rw [wellFormed_iff_tableOk] at h
        omega
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (getElem?_encStructure_tableStart_isSome hlt)
      rw [hx, ite_eq_right hwf]
      cases x <;> exact Reaches.refl _
    · have hwf : v.WellFormed a := wellFormed_iff_tableOk.mpr ⟨hall, heq.symm⟩
      have := getElem?_encStructure_tableStart_length_add a 0
      rw [Nat.add_zero, ← heq] at this
      rw [this, ite_eq_left hwf]
      exact Reaches.refl _
  · have hwf : ¬ v.WellFormed a := fun h => hall (wellFormed_iff_tableOk.mp h).1
    refine ⟨regs₂, ?_, by simp [hlen₂, hlen₁], fun h => absurd h hwf, hB₂⟩
    rw [ite_eq_right hall] at hreach
    rwa [ite_eq_right hwf]

variable (v)

theorem pow_arityAt_le (a : EncodedStructure) (i : ℕ) :
    a.1 ^ arityAt v i ≤ ((encStructure a).length + 1) ^ v.maxArity := by
  have h₁ : a.1 ≤ (encStructure a).length + 1 :=
    (card_le_length_encStructure a).trans (Nat.le_succ _)
  have h₂ : arityAt v i ≤ v.maxArity := by
    unfold arityAt
    split_ifs with h
    · exact v.arity_le_maxArity ⟨i, h⟩
    · exact Nat.zero_le _
  exact (Nat.pow_le_pow_left h₁ _).trans (Nat.pow_le_pow_right (Nat.succ_pos _) h₂)

theorem length_le_pow_maxArity (a : EncodedStructure) :
    (encStructure a).length ≤ ((encStructure a).length + 1) ^ v.maxArity :=
  (Nat.le_succ _).trans (Nat.le_self_pow (by simp [Vocabulary.maxArity]) _)

end Shape

/-! ### Evaluating formulas -/

variable [L.IsRelational]

section Eval

/-- The register holding the variable of a term of a relational language: `fv x` for the free
variable `x`, and `base + i` for the bound variable `i`. -/
def termReg {α : Type*} (fv : α → ℕ) (base : ℕ) {k : ℕ}
    (t : L.Term (α ⊕ Fin k)) : ℕ :=
  Sum.elim fv (fun i : Fin k => base + i) (termVar t)

/-- The register of the variable of a term holds the value of the term. -/
private theorem getD_termReg {α : Type*} {n : ℕ} [L.Structure (Fin n)] {fv : α → ℕ}
    {base k : ℕ} {regs : List ℕ} {val : α → Fin n} {xs : Fin k → Fin n}
    (hv : ∀ x, regs.getD (fv x) 0 = val x) (hxs : ∀ i : Fin k, regs.getD (base + i) 0 = xs i)
    (t : L.Term (α ⊕ Fin k)) :
    regs.getD (termReg fv base t) 0 = (t.realize (Sum.elim val xs) : Fin n) := by
  rw [realize_termVar, termReg]
  rcases termVar t with x | i
  · exact hv x
  · exact hxs i

variable (v)

/-- The original order-free atomic handlers: variables are stored in registers, and input
relations are read from their encoded truth tables. -/
def atomicCompiler {α : Type*} (fv : α → ℕ) (base : ℕ) : AtomicCompiler L α where
  term t := reg (termReg fv base t)
  rel R ts T F :=
    .read (bitExpr v (v.index ⟨_, R⟩) fun m => termReg fv base (ts m)) T F F

/-- The code evaluating an order-free formula, with the cardinality in register `0`, free
variables in registers `fv` and bound variables starting at `base`. -/
def formulaCode {α : Type*} (fv : α → ℕ) (base : ℕ) {k : ℕ}
    (φ : L.BoundedFormula α k) (b T F : ℕ) : List Instr :=
  formulaCodeWith (atomicCompiler v fv base) base φ b T F

private theorem length_formulaCode {α : Type*} (fv : α → ℕ) (base : ℕ) {k : ℕ}
    (φ : L.BoundedFormula α k) (b T F : ℕ) :
    (formulaCode v fv base φ b T F).length = codeLength φ :=
  length_formulaCodeWith _ _ _ _ _ _

variable {v}

/-- The order-free handlers implement their actual table/variable semantics. -/
theorem atomicCompiler_correct {a : EncodedStructure} (ha : v.WellFormed a)
    {α : Type*} (fv : α → ℕ) (base : ℕ) (val : α → Fin a.1) :
    let _ := v.decode a
    (atomicCompiler v fv base).Correct (encStructure a) fv base val := by
  let _ := v.decode a
  constructor
  · intro k regs xs _ hv hxs t
    exact getD_termReg hv hxs t
  · intro k r R ts P b T F B regs xs h0 hv hxs hB hinstr
    set x : Fin r → Fin a.1 := fun m => (ts m).realize (Sum.elim val xs)
    have hi : v.index ⟨_, R⟩ < a.2.length := ha.1 ▸ v.index_lt _
    have htab : v.table a ⟨_, R⟩ = a.2[v.index ⟨_, R⟩] := List.getD_eq_getElem _ _ hi
    have hj : tupleIndex x < a.2[v.index ⟨_, R⟩].length := by
      rw [← htab, ha.length_table]
      exact tupleIndex_lt x
    have hpos := eval_bitExpr ha h0 (v.index_lt ⟨_, R⟩).le
      (fun m => termReg fv base (ts m)) x (fun m => getD_termReg hv hxs (ts m))
    refine ⟨a.2[v.index ⟨_, R⟩][tupleIndex x], ?_, ?_⟩
    · change _ ↔ RelMap R x
      simp only [relMap_decode, htab]
      rw [List.getD_eq_getElem _ _ hj]
    · refine Reaches.read hinstr hB ?_
      rw [hpos, getElem?_encStructure_tableStart_two_mul_add_one hi hj]
      cases a.2[v.index ⟨_, R⟩][tupleIndex x] <;> exact Reaches.refl _

/-- **The compiled code of a formula decides its truth** in the decoded structure of a well-formed
input: from the code of `φ` at `b`, with the cardinality in register `0`, the values `val` of the
free variables in the registers `fv` below `base` and the values `xs` of the bound variables in the
registers from `base` on, the program goes to `T` if `φ` holds under `val` and `xs` and to `F`
otherwise, keeping the registers below `base + k` and the bound `B` of the registers. -/
theorem reaches_formulaCode {P : CounterProgram} {a : EncodedStructure} (ha : v.WellFormed a)
    {B : ℕ} (hnB : a.1 ≤ B) {α : Type*} (fv : α → ℕ) (base : ℕ) (hbase : 0 < base)
    (hfv : ∀ x, fv x < base) (val : α → Fin a.1) :
    ∀ {k : ℕ} (φ : L.BoundedFormula α k) (b T F : ℕ) (regs : List ℕ) (xs : Fin k → Fin a.1),
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

end Eval

end ModelChecker

open ModelChecker

variable [L.IsRelational]

/-! ### The model checker -/

/-- The counter program deciding a sentence: the shape check, then the evaluation of the sentence,
then a halt with output `[true]` or `[false]`. Its registers are the cardinality, the position and
the counter of the shape check, and one register per bound variable. -/
def modelChecker (φ : L.Sentence) : CounterProgram where
  code :=
    shapeCode v 0 (4 + 6 * v.count) (4 + 6 * v.count + codeLength φ + 1) ++
      formulaCode v (fun e : Empty => e.elim) 3 φ (4 + 6 * v.count) (4 + 6 * v.count + codeLength φ)
        (4 + 6 * v.count + codeLength φ + 1) ++
      [.accept, .reject]
  registers := 3 + boundDepth φ

/-- **First-order model checking is in logarithmic space**: for a finite relational vocabulary `v`
and a first-order sentence `φ`, the inputs encoding the finite structures that satisfy `φ` form
a problem in `L` [Immerman, Theorem 3.1][Immerman1999]. Malformed inputs are not in the problem;
the empty structure is included. The sentence uses the relation symbols of the vocabulary and
equality, without Immerman's constant symbols and built-in order and `BIT`. -/
theorem queryLanguage_mem_L (φ : L.Sentence) :
    v.queryLanguage {M | M ⊨ φ} ∈ Complexity.L encStructure := by
  classical
  refine ⟨fun a => decide (a ∈ v.queryLanguage {M | M ⊨ φ}), ?_, fun a => by simp⟩
  refine (v.modelChecker φ).computableInLogSpace_of_reaches v.maxArity fun a => ?_
  have hE := length_shapeCode v 0 (4 + 6 * v.count) (4 + 6 * v.count + codeLength φ + 1)
  have hC := length_formulaCode v (fun e : Empty => e.elim) 3 φ (4 + 6 * v.count)
    (4 + 6 * v.count + codeLength φ) (4 + 6 * v.count + codeLength φ + 1)
  have hcode : (v.modelChecker φ).CodeAt 0 (v.modelChecker φ).code :=
    codeAt_of_code_eq (pre := []) (post := []) (by simp)
  change (v.modelChecker φ).CodeAt 0 (_ ++ _ ++ _) at hcode
  rw [codeAt_append, codeAt_append] at hcode
  obtain ⟨⟨hshape, hcomp⟩, hhalt⟩ := hcode
  simp only [List.length_append, hE, hC, Nat.zero_add] at hcomp hhalt
  simp only [codeAt_cons] at hhalt
  obtain ⟨hacc, hrej, -⟩ := hhalt
  have hwB := length_le_pow_maxArity v a
  have hnB := (card_le_length_encStructure a).trans hwB
  obtain ⟨regs₁, hreach₁, hlen₁, h0₁, hB₁⟩ :=
    reaches_shapeCode hshape (pow_arityAt_le v a) hwB (List.replicate (3 + boundDepth φ) 0)
      (by simp) (by simp) (by simp)
  by_cases hwf : v.WellFormed a
  · rw [ite_eq_left hwf] at hreach₁
    obtain ⟨res, regs₂, hres, hreach₂, -, -, hB₂⟩ :=
      reaches_formulaCode hwf hnB (fun e : Empty => e.elim) 3 (by norm_num) (fun e => e.elim)
        default φ _ _ _ regs₁ default hcomp (by rw [hlen₁]; simp) (h0₁ hwf) hB₁ (fun e => e.elim)
        (fun i => i.elim0)
    refine ⟨(if res then 4 + 6 * v.count + codeLength φ else 4 + 6 * v.count + codeLength φ + 1,
      regs₂), hreach₁.trans hreach₂, ?_, hB₂⟩
    have hmem : a ∈ v.queryLanguage {M | M ⊨ φ} ↔ res = true := by
      rw [mem_queryLanguage, hres]
      exact and_iff_right hwf
    cases res
    · rw [ite_eq_right Bool.false_ne_true, hrej]
      simp [hmem]
    · rw [ite_eq_left rfl, hacc]
      simp [hmem]
  · rw [ite_eq_right hwf] at hreach₁
    refine ⟨(4 + 6 * v.count + codeLength φ + 1, regs₁), hreach₁, ?_, hB₁⟩
    rw [hrej]
    simp [mem_queryLanguage, hwf]

end Vocabulary

/-- **First-order definable classes have query languages in logarithmic space**: for a finite
relational vocabulary `v`, the query language of a first-order definable class of finite structures
is in `L` [Immerman, Theorem 3.1][Immerman1999]. Definable classes are closed under isomorphism
(`Cslib.Logic.FO.Definable.isoClosed`), so membership does not depend on the numbering of an
encoded structure (`Cslib.Logic.Vocabulary.mem_queryLanguage_encode`). The defining sentence is over
the relational language, without Immerman's constant symbols and built-in order and `BIT`. -/
theorem FO.Definable.queryLanguage_mem_L {L : Language.{u, v}} [L.IsRelational]
    (v : Vocabulary L) {K : Set (Bundled.{0} L.Structure)} (hK : FO.Definable K) :
    v.queryLanguage K ∈ Complexity.L encStructure := by
  obtain ⟨φ, hφ⟩ := hK
  have : v.queryLanguage K = v.queryLanguage {M | M ⊨ φ} := by
    ext a
    have : Finite (v.decoded a) := inferInstanceAs (Finite (Fin a.1))
    simp only [Vocabulary.mem_queryLanguage]
    exact and_congr_right fun _ => hφ (v.decoded a)
  rw [this]
  exact v.queryLanguage_mem_L φ

end Cslib.Logic
