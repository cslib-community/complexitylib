/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.FineGrained.Schoening
public import Complexity.Computability.WordRAM.ListArray
public import Complexity.Computability.WordRAM.Notation

/-!
# Finding the first falsified clause on the word RAM

A CNF formula on the variables `Fin n` is stored in word-RAM memory clause by clause: a clause
`c` occupies `c.length + 1` words, its length followed by the codes `2 v + b` of its literals
`(v, b)` (`Cslib.Algorithms.WordRAM.Schoening.encodeClause`). An assignment `σ : Fin n → Bool` is
stored as `n` words `0` or `1` (`Cslib.Algorithms.WordRAM.Schoening.AssignAt`).

`Cslib.Algorithms.WordRAM.Schoening.scan` scans the clauses in order, evaluating each one against
the stored assignment, and stops at the first falsified clause. It reports whether one was found
and, if so, the address of its encoding: exactly the clause chosen by
`Cslib.Complexity.Schoening.firstUnsat` (`Cslib.Algorithms.WordRAM.Schoening.scan_spec`). It runs
within `12 E + 4` instructions, where `E` is the number of words of the formula's encoding, and
leaves memory unchanged. The scan is the deterministic part of one step of Schöning's local search
and of the final satisfaction check.

The registers of the scan belong to a register file of 24 registers shared with the trial and
amplification programs of Schöning's algorithm (`Cslib.Algorithms.WordRAM.Schoening.Reg`).

## Main definitions

* `Cslib.Algorithms.WordRAM.Schoening.litCode`, `Cslib.Algorithms.WordRAM.Schoening.encodeClause`,
  `Cslib.Algorithms.WordRAM.Schoening.encodeClauses`, `Cslib.Algorithms.WordRAM.Schoening.encode`:
  the word encoding of literals, clauses and formulas; the input of a trial is `n` followed by the
  clauses.
* `Cslib.Algorithms.WordRAM.Schoening.AssignAt`,
  `Cslib.Algorithms.WordRAM.Schoening.assignmentAt`: storing and reading an assignment.
* `Cslib.Algorithms.WordRAM.Schoening.ScanResult`: the result registers of the scan, matched
  against `firstUnsat`.
* `Cslib.Algorithms.WordRAM.Schoening.scan`: the scan as a structured program.

## Main results

* `Cslib.Algorithms.WordRAM.Schoening.scan_spec`: the scan finds `firstUnsat` within `12 E + 4`
  instructions without changing memory.
* `Cslib.Algorithms.WordRAM.Schoening.assignmentAt_eq`: reading back a stored assignment.

## References

* [U. Schöning, *A probabilistic algorithm for k-SAT and constraint satisfaction
  problems*][Schoening1999]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Schoening

open Cslib.WordRAM Cslib.WordRAM.Block Cslib.Logic.PL Cslib.Complexity.Schoening

/-! ### Encoding -/

variable {n : ℕ}

/-- The word code `2 v + b` of the literal `(v, b)`. -/
def litCode (l : Literal (Fin n)) : ℕ := 2 * l.1.val + l.2.toNat

/-- A clause is stored as its length followed by the codes of its literals. -/
def encodeClause (c : Clause (Fin n)) : List ℕ := c.length :: c.map litCode

/-- The clauses of a formula, stored one after another. -/
def encodeClauses (φ : CNF (Fin n)) : List ℕ := φ.flatMap encodeClause

/-- The input of a trial of Schöning's algorithm: the number of variables, then the clauses. -/
def encode (φ : CNF (Fin n)) : List ℕ := n :: encodeClauses φ

@[simp]
theorem length_encodeClause (c : Clause (Fin n)) : (encodeClause c).length = c.length + 1 := by
  simp [encodeClause]

@[simp]
theorem encodeClauses_nil : encodeClauses ([] : CNF (Fin n)) = [] := rfl

@[simp]
theorem encodeClauses_cons (c : Clause (Fin n)) (φ : CNF (Fin n)) :
    encodeClauses (c :: φ) = encodeClause c ++ encodeClauses φ := by
  simp [encodeClauses]

/-- Literal codes are below `2 n`. -/
theorem litCode_lt (l : Literal (Fin n)) : litCode l < 2 * n := by
  obtain ⟨v, b⟩ := l
  have := v.isLt
  cases b <;> simp only [litCode, Bool.toNat_false, Bool.toNat_true] <;> omega

/-- Shifting a literal code right recovers its variable. -/
theorem litCode_shiftRight (l : Literal (Fin n)) : litCode l >>> 1 = l.1.val := by
  obtain ⟨v, b⟩ := l
  rw [Nat.shiftRight_eq_div_pow]
  cases b <;> simp only [litCode, Bool.toNat_false, Bool.toNat_true] <;> omega

/-- The low bit of a literal code is its sign. -/
theorem litCode_and_one (l : Literal (Fin n)) : litCode l &&& 1 = l.2.toNat := by
  obtain ⟨v, b⟩ := l
  rw [Nat.and_one_is_mod]
  cases b <;> simp only [litCode, Bool.toNat_false, Bool.toNat_true] <;> omega

/-- The assignment `σ` is stored as the words `(σ i).toNat` from address `base`. -/
def AssignAt (mem : ℕ → ℕ) (base : ℕ) (σ : Fin n → Bool) : Prop :=
  ∀ i : Fin n, mem (base + i) = (σ i).toNat

/-- The assignment read from the `n` words at address `base`: variable `i` is true when its word
is `1`. -/
def assignmentAt (mem : ℕ → ℕ) (base n : ℕ) : Fin n → Bool :=
  fun i => decide (mem (base + i) = 1)

/-- Reading back a stored assignment. -/
theorem assignmentAt_eq {mem : ℕ → ℕ} {base : ℕ} {σ : Fin n → Bool} (h : AssignAt mem base σ) :
    assignmentAt mem base n = σ := by
  funext i
  rw [assignmentAt, h i]
  cases σ i <;> rfl

private theorem toNat_eq_iff_beq (a b : Bool) : 1 - (a.toNat ^^^ b.toNat) = (a == b).toNat := by
  cases a <;> cases b <;> rfl

private theorem toNat_or (a b : Bool) : a.toNat ||| b.toNat = (a || b).toNat := by
  cases a <;> cases b <;> rfl

private theorem toNat_le_one (a : Bool) : a.toNat ≤ 1 := by
  cases a <;> decide

private theorem toNat_xor_le_one (a b : Bool) : a.toNat ^^^ b.toNat ≤ 1 := by
  cases a <;> cases b <;> decide

/-! ### Registers -/

/-! The 24 registers shared by the programs of Schöning's algorithm. -/

namespace Reg

/-- Constant `0`. -/
abbrev zero : Fin 24 := 0
/-- Constant `1`. -/
abbrev one : Fin 24 := 1
/-- Address of the first clause. -/
abbrev cBeg : Fin 24 := 2
/-- Address of the stored assignment, which is also the end of the clauses. -/
abbrev aBase : Fin 24 := 3
/-- The number `n` of variables. -/
abbrev nReg : Fin 24 := 4
/-- Address of the current clause. -/
abbrev ptr : Fin 24 := 5
/-- Length of the current clause. -/
abbrev len : Fin 24 := 6
/-- Address of the current literal. -/
abbrev lptr : Fin 24 := 7
/-- End address of the current clause. -/
abbrev lend : Fin 24 := 8
/-- Whether the current clause has a true literal so far. -/
abbrev sat : Fin 24 := 9
/-- The current literal code. -/
abbrev lit : Fin 24 := 10
/-- The current variable. -/
abbrev var : Fin 24 := 11
/-- The sign of the current literal. -/
abbrev sgn : Fin 24 := 12
/-- Scratch address. -/
abbrev addr : Fin 24 := 13
/-- Scratch value. -/
abbrev val : Fin 24 := 14
/-- Whether a falsified clause was found. -/
abbrev found : Fin 24 := 15
/-- Address of the falsified clause found. -/
abbrev cPtr : Fin 24 := 16
/-- Loop counter. -/
abbrev cnt : Fin 24 := 17
/-- Number of steps of the local search. -/
abbrev steps : Fin 24 := 18
/-- Output. -/
abbrev out : Fin 24 := 19

end Reg

open Reg

/-! ### The scan -/

/-- One literal: read its code, look up its variable, and record whether it is true. -/
def litBody : Code .standard 24 := ram[
  lit ← *lptr; var ← lit >>> one; sgn ← lit &&& one; addr ← aBase + var; val ← *addr;
  addr ← val ^^^ sgn; addr ← one - addr; sat ← sat ||| addr; lptr ← lptr + one ]

/-- Evaluate the literals in `[lptr, lend)`. -/
def litLoop : Code .standard 24 := .loop (.lt lptr lend) litBody

/-- Read the length of the clause at `ptr` and set up its literal loop. -/
def clauseInit : Code .standard 24 := ram[
  len ← *ptr; lptr ← ptr + one; lend ← lptr + len; sat ← zero ]

/-- After a clause: on a falsified clause record it and jump to the end, otherwise move on. -/
def clauseDone : Code .standard 24 := ram[
  if sat = zero then [ found ← one; cPtr ← ptr; ptr ← aBase ] else [ ptr ← lend ] ]

/-- One clause: evaluate it, and on a falsified clause record it and jump to the end. -/
def clauseBody : Code .standard 24 := ram[ ⟪clauseInit⟫; ⟪litLoop⟫; ⟪clauseDone⟫ ]

/-- Evaluate the clauses in `[ptr, aBase)` until a falsified one. -/
def clauseLoop : Code .standard 24 := .loop (.lt ptr aBase) clauseBody

/-- **The scan**: find the first clause falsified by the stored assignment. -/
def scan : Code .standard 24 := ram[ ptr ← cBeg; found ← zero; ⟪clauseLoop⟫ ]

/-- The result registers of the scan: no falsified clause, or the address `cptr` of the encoding
of the first one, which ends by address `e`. -/
def ScanResult (σ : Fin n → Bool) (φ : CNF (Fin n)) (mem : ℕ → ℕ) (e fnd cptr : ℕ) : Prop :=
  match firstUnsat φ σ with
  | none => fnd = 0
  | some c => fnd = 1 ∧ HoldsList cptr (encodeClause c) mem ∧ cptr + c.length + 1 ≤ e

theorem firstUnsat_cons (σ : Fin n → Bool) (c : Clause (Fin n)) (φ : CNF (Fin n)) :
    firstUnsat (c :: φ) σ = if c.eval σ then firstUnsat φ σ else some c := by
  cases h : c.eval σ <;> simp [firstUnsat, h]

/-- `firstUnsat` finds nothing exactly on satisfying assignments. -/
theorem firstUnsat_eq_none_iff (σ : Fin n → Bool) (φ : CNF (Fin n)) :
    firstUnsat φ σ = none ↔ φ.eval σ = true := by
  induction φ with
  | nil => simp [firstUnsat]
  | cons c φ ih =>
    rw [firstUnsat_cons, CNF.eval_cons]
    cases c.eval σ <;> simp [ih]

/-- A satisfied first clause does not change the scan result. -/
theorem scanResult_cons_of_eval {σ : Fin n → Bool} {c : Clause (Fin n)} {ψ : CNF (Fin n)}
    (h : c.eval σ = true) : ScanResult σ (c :: ψ) = ScanResult σ ψ := by
  funext mem e fnd cptr
  simp only [ScanResult, firstUnsat_cons, h, ↓reduceIte]

section Specs

variable {w : ℕ}

/-- **The literal loop.** Starting from `sat = s`, the loop over the literals `ls` ends with
`sat = s || ls.eval σ`, `lptr = lend`, and unchanged memory. -/
theorem litLoop_spec (σ : Fin n → Bool) (ls : Clause (Fin n)) (x : Data 24) (s : Bool)
    (hone : x.regs one = 1) (hl : HoldsList (x.regs lptr) (ls.map litCode) x.mem)
    (hend : x.regs lend = x.regs lptr + ls.length) (hs : x.regs sat = s.toNat)
    (hσ : AssignAt x.mem (x.regs aBase) σ) (hle : x.regs lend ≤ x.regs aBase + 2 * n)
    (hw : Fits w (x.regs aBase + 2 * n)) (hpos : 1 ≤ x.regs aBase + 2 * n) :
    ∃ y, ExecWithin w litLoop x y (11 * ls.length + 2) ∧ y.mem = x.mem ∧
      y.regs sat = (s || Clause.eval σ ls).toNat ∧ y.regs lptr = x.regs lend ∧
      y.regs aBase = x.regs aBase ∧ y.regs one = 1 := by
  induction ls generalizing x s with
  | nil =>
    refine ⟨x, (ExecWithin.loop_exit ?_).mono (by omega), rfl, ?_, ?_, rfl, hone⟩
    · simp only [Cond.holds_lt, hend, List.length_nil, Nat.add_zero, lt_irrefl, not_false_eq_true]
    · simp [hs]
    · simp [hend]
  | cons l ls ih =>
    have hc : (Cond.lt lptr lend).Holds x := by
      simp only [Cond.holds_lt, hend, List.length_cons]; omega
    have hlit : x.mem (x.regs lptr) = litCode l := by
      simpa using hl.get 0 (by simp)
    have hrest : HoldsList (x.regs lptr + 1) (ls.map litCode) x.mem := by
      have := (holdsList_append_iff (xs := [litCode l]) (ys := ls.map litCode)).mp
        (by simpa using hl)
      simpa using this.2
    have hval : x.mem (x.regs aBase + l.1.val) = (σ l.1).toNat := hσ l.1
    have hf1 : Fits w l.1.val := hw.of_le (by omega)
    have hf2 : Fits w l.2.toNat := hw.of_le (by have := toNat_le_one l.2; omega)
    have hf3 : Fits w (x.regs aBase + l.1.val) := hw.of_le (by omega)
    have hf4 : Fits w ((σ l.1).toNat ^^^ l.2.toNat) := hw.of_le (by
      have := toNat_xor_le_one (σ l.1) l.2; omega)
    have hf5 : Fits w (1 - ((σ l.1).toNat ^^^ l.2.toNat)) := hw.of_le (by omega)
    have hf6 : Fits w (s.toNat ||| (1 - ((σ l.1).toNat ^^^ l.2.toNat))) := hw.of_le (by
      rw [toNat_eq_iff_beq, toNat_or]; have := toNat_le_one (s || (σ l.1 == l.2)); omega)
    have hf7 : Fits w (x.regs lptr + 1) := hw.of_le (by simp only [List.length_cons] at hend; omega)
    obtain ⟨y, hy, hym, hys, hyp, hya, hyo⟩ := ih (((((((((x.set lit (litCode l)).set var
        l.1.val).set sgn l.2.toNat).set addr (x.regs aBase + l.1.val)).set val
        (σ l.1).toNat).set addr ((σ l.1).toNat ^^^ l.2.toNat)).set addr
        (1 - ((σ l.1).toNat ^^^ l.2.toNat))).set sat
        (s.toNat ||| (1 - ((σ l.1).toNat ^^^ l.2.toNat)))).set lptr (x.regs lptr + 1))
      (s || (σ l.1 == l.2))
      (by simp +decide [hone])
      (by simpa +decide [Function.update_apply] using hrest)
      (by simp only [List.length_cons] at hend; simp +decide [hend]; omega)
      (by simp +decide [toNat_eq_iff_beq, toNat_or])
      (by simpa +decide [Function.update_apply] using hσ)
      (by simp only [List.length_cons] at hend; simp +decide; omega)
      (by simpa +decide [Function.update_apply] using hw)
      (by simpa +decide [Function.update_apply] using hpos)
    have hbody : ExecWithin w litBody x (((((((((x.set lit (litCode l)).set var
        l.1.val).set sgn l.2.toNat).set addr (x.regs aBase + l.1.val)).set val
        (σ l.1).toNat).set addr ((σ l.1).toNat ^^^ l.2.toNat)).set addr
        (1 - ((σ l.1).toNat ^^^ l.2.toNat))).set sat
        (s.toNat ||| (1 - ((σ l.1).toNat ^^^ l.2.toNat)))).set lptr (x.regs lptr + 1)) 9 := by
      ram_eval [litBody, hone, hlit, hval, hs, litCode_shiftRight, litCode_and_one, hf1, hf2, hf3,
        hf4, hf5, hf6, hf7]
    refine ⟨y, (ExecWithin.loop_iter hc hbody hy).mono (by simp; omega), ?_, ?_, ?_, ?_, hyo⟩
    · simpa using hym
    · rw [hys, Clause.eval_cons, Literal.eval, Bool.or_assoc]
    · simpa +decide [Function.update_apply] using hyp
    · simpa +decide [Function.update_apply] using hya

/-- **The clause loop.** From `ptr` at the encoding of the clauses `ψ`, which end at `aBase`, and
`found = 0`, the loop ends with the scan result for `ψ` and unchanged memory. -/
theorem clauseLoop_spec (σ : Fin n → Bool) (ψ : CNF (Fin n)) (x : Data 24)
    (hzero : x.regs zero = 0) (hone : x.regs one = 1)
    (hp : HoldsList (x.regs ptr) (encodeClauses ψ) x.mem)
    (hend : x.regs ptr + (encodeClauses ψ).length = x.regs aBase) (hfound : x.regs found = 0)
    (hσ : AssignAt x.mem (x.regs aBase) σ)
    (hw : Fits w (x.regs aBase + 2 * n)) (hpos : 1 ≤ x.regs aBase + 2 * n) :
    ∃ y, ExecWithin w clauseLoop x y (12 * (encodeClauses ψ).length + 2) ∧ y.mem = x.mem ∧
      ScanResult σ ψ x.mem (x.regs aBase) (y.regs found) (y.regs cPtr) := by
  induction ψ generalizing x with
  | nil =>
    refine ⟨x, (ExecWithin.loop_exit ?_).mono le_rfl, rfl, ?_⟩
    · simp only [encodeClauses_nil, List.length_nil, Nat.add_zero] at hend
      simp [Cond.holds_lt, hend]
    · simp [ScanResult, firstUnsat, hfound]
  | cons c ψ ih =>
    rw [encodeClauses_cons] at hp hend
    obtain ⟨hpc, hpψ⟩ := holdsList_append_iff.mp hp
    simp only [List.length_append, length_encodeClause] at hend hpψ
    have hlen : x.mem (x.regs ptr) = c.length := by
      simpa [encodeClause] using hpc.get 0 (by simp)
    have hlits : HoldsList (x.regs ptr + 1) (c.map litCode) x.mem := by
      have := (holdsList_append_iff (xs := [c.length]) (ys := c.map litCode)).mp
        (by simpa [encodeClause] using hpc)
      simpa using this.2
    have hc : (Cond.lt ptr aBase).Holds x := by simp only [Cond.holds_lt]; omega
    have hf1 : Fits w (x.regs ptr + 1) := hw.of_le (by omega)
    have hf2 : Fits w (x.regs ptr + 1 + c.length) := hw.of_le (by omega)
    have hinit : ExecWithin w clauseInit x
        ((((x.set len c.length).set lptr (x.regs ptr + 1)).set lend
          (x.regs ptr + 1 + c.length)).set sat 0) 4 := by
      ram_eval [clauseInit, hlen, hone, hzero, hf1, hf2]
    obtain ⟨x₂, hlit, hm₂, hs₂, hp₂, ha₂, ho₂⟩ := litLoop_spec (w := w) σ c
      ((((x.set len c.length).set lptr (x.regs ptr + 1)).set lend
          (x.regs ptr + 1 + c.length)).set sat 0) false
      (by simp +decide [hone]) (by simpa +decide [Function.update_apply] using hlits)
      (by simp +decide)
      (by simp +decide) (by simpa +decide [Function.update_apply] using hσ)
      (by simp +decide; omega)
      (by simpa +decide [Function.update_apply] using hw)
      (by simpa +decide [Function.update_apply] using hpos)
    have hz₂ : x₂.regs zero = 0 := by
      rw [ExecWithin.regs_eq hlit (by decide)]; simpa +decide [Function.update_apply] using hzero
    have hptr₂ : x₂.regs ptr = x.regs ptr := by
      rw [ExecWithin.regs_eq hlit (by decide)]; simp +decide
    have hlend₂ : x₂.regs lend = x.regs ptr + 1 + c.length := by
      rw [ExecWithin.regs_eq hlit (by decide)]; simp +decide
    simp +decide only [Data.set_mem, Data.set_regs, Function.update_apply, Bool.false_or,
      ↓reduceIte] at hm₂ hs₂ hp₂ ha₂
    cases hce : c.eval σ with
    | false =>
      have hdone : ExecWithin w clauseDone x₂
          (((x₂.set found 1).set cPtr (x.regs ptr)).set ptr (x.regs aBase)) 4 := by
        have hfit : Fits w 1 := hw.of_le hpos
        ram_eval [clauseDone, hs₂, hce, hz₂, ho₂, hptr₂, ha₂, hfit]
      refine ⟨_, (ExecWithin.loop_iter hc (hinit.seq (hlit.seq hdone))
        (ExecWithin.loop_exit ?_)).mono ?_, ?_, ?_⟩
      · simp +decide [Cond.holds_lt, ha₂]
      · simp only [encodeClauses_cons, List.length_append, length_encodeClause]; omega
      · simpa using hm₂
      · simp +decide only [ScanResult, firstUnsat_cons, hce, Bool.false_eq_true, ↓reduceIte,
          Data.set_regs, Function.update_apply]
        exact ⟨trivial, hpc, by omega⟩
    | true =>
      have hdone : ExecWithin w clauseDone x₂ (x₂.set ptr (x.regs ptr + 1 + c.length)) 3 := by
        ram_eval [clauseDone, hs₂, hce, hz₂, hlend₂]
      obtain ⟨y, hy, hym, hyr⟩ := ih (x₂.set ptr (x.regs ptr + 1 + c.length))
        (by simpa +decide using hz₂) (by simpa +decide using ho₂)
        (by
          simp only [Data.set_regs, Function.update_self, Data.set_mem, hm₂]
          rw [show x.regs ptr + 1 + c.length = x.regs ptr + (c.length + 1) by omega]
          exact hpψ)
        (by simp +decide [ha₂]; omega)
        (by rw [Data.set_regs, Function.update_of_ne (by decide),
          ExecWithin.regs_eq hlit (by decide)]; simpa +decide [Function.update_apply] using hfound)
        (by simpa +decide [Function.update_apply, hm₂, ha₂] using hσ)
        (by simpa +decide [ha₂] using hw)
        (by simpa +decide [ha₂] using hpos)
      refine ⟨y, (ExecWithin.loop_iter hc (hinit.seq (hlit.seq hdone)) hy).mono ?_, ?_, ?_⟩
      · simp only [encodeClauses_cons, List.length_append, length_encodeClause]; omega
      · simpa [hm₂] using hym
      · rw [scanResult_cons_of_eval hce]
        simpa +decide [hm₂, ha₂] using hyr

/-- **The scan.** From the clauses of `φ` stored in `[cBeg, aBase)` and the assignment `σ` stored at
`aBase`, the scan reports `firstUnsat φ σ` within `12 E + 4` instructions, where `E` is the length
of the encoding, and leaves memory unchanged. -/
theorem scan_spec (σ : Fin n → Bool) (φ : CNF (Fin n)) (x : Data 24)
    (hzero : x.regs zero = 0) (hone : x.regs one = 1)
    (hcl : HoldsList (x.regs cBeg) (encodeClauses φ) x.mem)
    (hend : x.regs cBeg + (encodeClauses φ).length = x.regs aBase)
    (hσ : AssignAt x.mem (x.regs aBase) σ)
    (hw : Fits w (x.regs aBase + 2 * n)) (hpos : 1 ≤ x.regs aBase + 2 * n) :
    ∃ y, ExecWithin w scan x y (12 * (encodeClauses φ).length + 4) ∧ y.mem = x.mem ∧
      ScanResult σ φ x.mem (x.regs aBase) (y.regs found) (y.regs cPtr) := by
  obtain ⟨y, hy, hym, hyr⟩ := clauseLoop_spec (w := w) σ φ ((x.set ptr (x.regs cBeg)).set found 0)
    (by simpa +decide [Function.update_apply] using hzero)
    (by simpa +decide [Function.update_apply] using hone)
    (by simpa +decide [Function.update_apply] using hcl)
    (by simpa +decide [Function.update_apply] using hend) (by simp)
    (by simpa +decide [Function.update_apply] using hσ)
    (by simpa +decide [Function.update_apply] using hw)
    (by simpa +decide [Function.update_apply] using hpos)
  have hz : (x.set ptr (x.regs cBeg)).regs zero = 0 := by simpa +decide using hzero
  have hrun := ExecWithin.seq (ExecWithin.copy (w := w) (d := ptr) (s := cBeg) (x := x))
    (ExecWithin.seq (ExecWithin.copy (d := found) (s := zero)) (by rw [hz]; exact hy))
  refine ⟨y, hrun.mono (by omega), by simpa using hym, by simpa +decide using hyr⟩

end Specs

end Cslib.Algorithms.WordRAM.Schoening

end
