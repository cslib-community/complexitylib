/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.WordRAM.Schoening.Scan
public import Complexity.Computability.Complexity.FineGrained.PPZ

/-!
# Forced values of PPZ on the word RAM

A partial assignment `τ : Fin n → Option Bool` is stored as `n` words, `0` or `1` for a set
variable and `2` for an unset one (`Cslib.Algorithms.WordRAM.PPZ.PartialAt`). The formula is
stored as in `Cslib.Algorithms.WordRAM.Schoening.encodeClauses`: each clause is its length followed
by the codes `2 v + b` of its literals.

`Cslib.Algorithms.WordRAM.PPZ.unitScan` scans the clauses once and reports whether one of them is a
unit clause on the variable `x` with polarity `b` under `τ` (`Cslib.Complexity.PPZ.IsUnitOn`): a
clause that contains `(x, b)`, whose literals on `x` all have polarity `b`, and whose other literals
`τ` falsifies. `Cslib.Algorithms.WordRAM.PPZ.forcedCode` runs it for the polarity `true` and then,
if needed, for `false`, and stores the word of `Cslib.Complexity.PPZ.forced φ τ x`
(`Cslib.Algorithms.WordRAM.PPZ.forcedCode_spec`). Both leave memory unchanged and take
`O(E)` instructions, where `E` is the length of the encoding of the clauses.

## Main definitions

* `Cslib.Algorithms.WordRAM.PPZ.optCode`, `Cslib.Algorithms.WordRAM.PPZ.PartialAt`: storing a
  partial assignment.
* `Cslib.Algorithms.WordRAM.PPZ.litHas`, `Cslib.Algorithms.WordRAM.PPZ.litOk`: the two literal
  tests of a unit clause.
* `Cslib.Algorithms.WordRAM.PPZ.unitScan`, `Cslib.Algorithms.WordRAM.PPZ.forcedCode`: the scans.

## Main results

* `Cslib.Algorithms.WordRAM.PPZ.isUnitOn_iff`: a unit clause through its literal tests.
* `Cslib.Algorithms.WordRAM.PPZ.unitScan_spec`: the scan finds a unit clause exactly when there is
  one.
* `Cslib.Algorithms.WordRAM.PPZ.forcedCode_spec`: the forced value, within `28 E + 15`
  instructions.

## References

* [R. Paturi, P. Pudlák, F. Zane, *Satisfiability Coding Lemma*][PPZ1997]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.PPZ

open Cslib.WordRAM Cslib.WordRAM.Block Cslib.Logic.PL Cslib.Complexity.PPZ
open Cslib.Algorithms.WordRAM.Schoening (litCode encodeClause encodeClauses litCode_shiftRight
  litCode_and_one length_encodeClause encodeClauses_cons encodeClauses_nil litCode_lt)

variable {n : ℕ}

/-! ### Partial assignments -/

/-- The word of a value of a partial assignment: `0` or `1` when set, `2` when unset. -/
def optCode : Option Bool → ℕ
  | some b => b.toNat
  | none => 2

theorem optCode_le_two (o : Option Bool) : optCode o ≤ 2 := by
  rcases o with _ | b
  · exact le_rfl
  · cases b <;> decide

/-- The partial assignment `τ` is stored as the words `optCode (τ i)` from address `base`. -/
def PartialAt (mem : ℕ → ℕ) (base : ℕ) (τ : Fin n → Option Bool) : Prop :=
  ∀ i : Fin n, mem (base + i) = optCode (τ i)

/-! ### Unit clauses through literal tests -/

/-- Whether the literal `l` is `(x, b)`. -/
def litHas (x : Fin n) (b : Bool) (l : Literal (Fin n)) : Bool := l.1 == x && l.2 == b

/-- Whether the literal `l` may occur in a unit clause on `x` with polarity `b` under `τ`: a literal
on `x` must have polarity `b`, and `τ` must falsify any other literal. -/
def litOk (τ : Fin n → Option Bool) (x : Fin n) (b : Bool) (l : Literal (Fin n)) : Bool :=
  if l.1 = x then l.2 == b else τ l.1 == some (!l.2)

/-- A unit clause through its literal tests. -/
theorem isUnitOn_iff (τ : Fin n → Option Bool) (x : Fin n) (b : Bool) (c : Clause (Fin n)) :
    IsUnitOn τ x b c ↔ c.any (litHas x b) = true ∧ c.all (litOk τ x b) = true := by
  simp only [IsUnitOn, List.any_eq_true, List.all_eq_true, litHas, litOk, Bool.and_eq_true,
    beq_iff_eq]
  refine and_congr Iff.rfl (forall₂_congr fun l _ => ?_)
  split_ifs <;> simp

/-- Whether the clause `c` is a unit clause on `x` with polarity `b` under `τ`, through the literal
tests. -/
def unitTest (τ : Fin n → Option Bool) (x : Fin n) (b : Bool) (c : Clause (Fin n)) : Bool :=
  c.any (litHas x b) && c.all (litOk τ x b)

/-- The value forced by unit clauses, through the literal tests. -/
theorem forced_eq_ite (φ : CNF (Fin n)) (τ : Fin n → Option Bool) (x : Fin n) :
    forced φ τ x =
      if φ.any (unitTest τ x true) then some true
      else if φ.any (unitTest τ x false) then some false
      else none := by
  have key (b : Bool) : (∃ c ∈ φ, IsUnitOn τ x b c) ↔ φ.any (unitTest τ x b) = true := by
    simp only [isUnitOn_iff, unitTest, List.any_eq_true, Bool.and_eq_true]
  unfold forced
  simp only [key]

private theorem toNat_xor_eq (a b : Bool) : 1 - (a.toNat ^^^ b.toNat) = (a == b).toNat := by
  cases a <;> cases b <;> rfl

private theorem toNat_or (a b : Bool) : a.toNat ||| b.toNat = (a || b).toNat := by
  cases a <;> cases b <;> rfl

private theorem toNat_and (a b : Bool) : a.toNat &&& b.toNat = (a && b).toNat := by
  cases a <;> cases b <;> rfl

private theorem toNat_le_one (a : Bool) : a.toNat ≤ 1 := by
  cases a <;> decide

private theorem toNat_xor_le_one (a b : Bool) : a.toNat ^^^ b.toNat ≤ 1 := by
  cases a <;> cases b <;> decide

/-- The partial-assignment test of `litOk`: `τ v` is `some (!s)` exactly when its word is
`1 - s`. -/
private theorem optCode_eq_iff (o : Option Bool) (s : Bool) :
    optCode o = 1 - s.toNat ↔ o = some (!s) := by
  rcases o with _ | a
  · cases s <;> simp [optCode]
  · cases a <;> cases s <;> simp [optCode]

/-! ### Registers -/

namespace Reg

/-- Constant `0`. -/
abbrev zero : Fin 32 := 0
/-- Constant `1`. -/
abbrev one : Fin 32 := 1
/-- Address of the first clause. -/
abbrev cBeg : Fin 32 := 2
/-- End address of the clauses. -/
abbrev cEnd : Fin 32 := 3
/-- Address of the stored partial assignment. -/
abbrev tBase : Fin 32 := 4
/-- The number `n` of variables. -/
abbrev nReg : Fin 32 := 5
/-- Address of the current clause. -/
abbrev ptr : Fin 32 := 6
/-- Length of the current clause. -/
abbrev len : Fin 32 := 7
/-- Address of the current literal. -/
abbrev lptr : Fin 32 := 8
/-- End address of the current clause. -/
abbrev lend : Fin 32 := 9
/-- The current literal code. -/
abbrev lit : Fin 32 := 10
/-- The current variable. -/
abbrev var : Fin 32 := 11
/-- The sign of the current literal. -/
abbrev sgn : Fin 32 := 12
/-- Scratch address. -/
abbrev addr : Fin 32 := 13
/-- Scratch value. -/
abbrev val : Fin 32 := 14
/-- Scratch comparison. -/
abbrev eq : Fin 32 := 15
/-- Whether the current clause contains `(x, b)`. -/
abbrev hasLit : Fin 32 := 16
/-- Whether every literal of the current clause passes `litOk`. -/
abbrev ok : Fin 32 := 17
/-- Whether a unit clause was found. -/
abbrev fnd : Fin 32 := 18
/-- The variable `x`. -/
abbrev xReg : Fin 32 := 19
/-- The polarity `b`. -/
abbrev bReg : Fin 32 := 20
/-- The word of the forced value. -/
abbrev res : Fin 32 := 21
/-- Constant `2`. -/
abbrev two : Fin 32 := 22

end Reg

open Reg

/-! ### The scan -/

/-- One literal: read it, and update `hasLit` and `ok`. -/
def litBody : Code .standard 32 := ram[
  lit ← *lptr; var ← lit >>> one; sgn ← lit &&& one;
  if var = xReg then [ eq ← sgn ^^^ bReg; eq ← one - eq; hasLit ← hasLit ||| eq; ok ← ok &&& eq ]
  else [ addr ← tBase + var; val ← *addr; eq ← one - sgn;
    if val = eq then [ ok ← ok ] else [ ok ← zero ] ];
  lptr ← lptr + one ]

/-- Test the literals in `[lptr, lend)`. -/
def litLoop : Code .standard 32 := .loop (.lt lptr lend) litBody

/-- Read the length of the clause at `ptr` and set up its literal loop. -/
def clauseInit : Code .standard 32 := ram[
  len ← *ptr; lptr ← ptr + one; lend ← lptr + len; hasLit ← zero; ok ← one ]

/-- After a clause: record whether it is a unit clause and move on. -/
def clauseDone : Code .standard 32 := ram[ eq ← hasLit &&& ok; fnd ← fnd ||| eq; ptr ← lend ]

/-- One clause. -/
def clauseBody : Code .standard 32 := ram[ ⟪clauseInit⟫; ⟪litLoop⟫; ⟪clauseDone⟫ ]

/-- Test the clauses in `[ptr, cEnd)`. -/
def clauseLoop : Code .standard 32 := .loop (.lt ptr cEnd) clauseBody

/-- **The unit-clause scan**: whether some clause is a unit clause on `xReg` with polarity
`bReg`. -/
def unitScan : Code .standard 32 := ram[ ptr ← cBeg; fnd ← zero; ⟪clauseLoop⟫ ]

/-- **The forced value** of `xReg`, stored in `res` as `optCode (forced φ τ x)`. -/
def forcedCode : Code .standard 32 := ram[
  bReg ← one; ⟪unitScan⟫;
  if fnd = one then [ res ← one ]
  else [ bReg ← zero; ⟪unitScan⟫; if fnd = one then [ res ← zero ] else [ res ← two ] ] ]

section Specs

variable {w : ℕ}

/-- The registers the scan relies on. -/
structure ScanFrame (w : ℕ) (τ : Fin n → Option Bool) (x : Fin n) (y : Data 32) : Prop where
  zero_eq : y.regs zero = 0
  one_eq : y.regs one = 1
  two_eq : y.regs two = 2
  x_eq : y.regs xReg = x
  stored : PartialAt y.mem (y.regs tBase) τ
  fits : Fits w (y.regs tBase + 2 * n)
  pos : 1 ≤ y.regs tBase

/-- **One literal.** -/
theorem litBody_spec (τ : Fin n → Option Bool) (x : Fin n) (b : Bool) (l : Literal (Fin n))
    (h o : Bool) (y : Data 32) (hf : ScanFrame w τ x y) (hb : y.regs bReg = b.toNat)
    (hl : y.mem (y.regs lptr) = litCode l) (hh : y.regs hasLit = h.toNat)
    (ho : y.regs ok = o.toNat) (hlp : Fits w (y.regs lptr + 1)) :
    ∃ z, ExecWithin w litBody y z 12 ∧ z.mem = y.mem ∧
      z.regs hasLit = (h || litHas x b l).toNat ∧ z.regs ok = (o && litOk τ x b l).toNat ∧
      z.regs lptr = y.regs lptr + 1 := by
  have hvar : litCode l >>> 1 = l.1.val := litCode_shiftRight l
  have hsgn : litCode l &&& 1 = l.2.toNat := litCode_and_one l
  have hfv : Fits w l.1.val := hf.fits.of_le (by omega)
  have hfs : Fits w l.2.toNat := hf.fits.of_le (by have := toNat_le_one l.2; have := hf.pos; omega)
  have hone := hf.one_eq
  have hzero := hf.zero_eq
  have hxr := hf.x_eq
  by_cases hvx : l.1 = x
  · subst hvx
    have hf1 : Fits w (l.2.toNat ^^^ b.toNat) :=
      hf.fits.of_le (by have := toNat_xor_le_one l.2 b; have := hf.pos; omega)
    have hf2 : Fits w (1 - (l.2.toNat ^^^ b.toNat)) := hf.fits.of_le (by have := hf.pos; omega)
    have hf3 : Fits w (h.toNat ||| (1 - (l.2.toNat ^^^ b.toNat))) := hf.fits.of_le (by
      rw [toNat_xor_eq, toNat_or]; have := toNat_le_one (h || (l.2 == b)); have := hf.pos; omega)
    have hf4 : Fits w (o.toNat &&& (1 - (l.2.toNat ^^^ b.toNat))) := hf.fits.of_le (by
      rw [toNat_xor_eq, toNat_and]; have := toNat_le_one (o && (l.2 == b)); have := hf.pos; omega)
    refine ⟨((((((((y.set lit (litCode l)).set var l.1.val).set sgn l.2.toNat).set eq
      (l.2.toNat ^^^ b.toNat)).set eq (1 - (l.2.toNat ^^^ b.toNat))).set hasLit
      (h.toNat ||| (1 - (l.2.toNat ^^^ b.toNat)))).set ok
      (o.toNat &&& (1 - (l.2.toNat ^^^ b.toNat)))).set lptr (y.regs lptr + 1)), ?_, rfl, ?_, ?_,
      by simp⟩
    · ram_eval [litBody, hl, hone, hvar, hsgn, hxr, hb, hh, ho, hfv, hfs, hf1, hf2, hf3, hf4, hlp]
    · simp +decide [toNat_xor_eq, toNat_or, litHas]
    · simp +decide [toNat_xor_eq, toNat_and, litOk]
  · have hvx' : l.1.val ≠ x.val := fun h' => hvx (Fin.ext h')
    have hbx : (l.1 == x) = false := beq_eq_false_iff_ne.mpr hvx
    have hτv : y.mem (y.regs tBase + l.1.val) = optCode (τ l.1) := hf.stored l.1
    have hfa : Fits w (y.regs tBase + l.1.val) := hf.fits.of_le (by omega)
    have hfe : Fits w (1 - l.2.toNat) := hf.fits.of_le (by have := hf.pos; omega)
    by_cases hve : optCode (τ l.1) = 1 - l.2.toNat
    · refine ⟨((((((((y.set lit (litCode l)).set var l.1.val).set sgn l.2.toNat).set addr
        (y.regs tBase + l.1.val)).set val (optCode (τ l.1))).set eq (1 - l.2.toNat)).set ok
        o.toNat).set lptr (y.regs lptr + 1)), ?_, rfl, ?_, ?_, by simp⟩
      · ram_eval [litBody, hl, hone, hvar, hsgn, hxr, hvx', hτv, hve, hh, ho, hfv, hfs, hfa, hfe,
          hlp]
      · simp +decide [hh, litHas, hbx]
      · simp +decide [litOk, hvx, (optCode_eq_iff _ _).mp hve]
    · refine ⟨((((((((y.set lit (litCode l)).set var l.1.val).set sgn l.2.toNat).set addr
        (y.regs tBase + l.1.val)).set val (optCode (τ l.1))).set eq (1 - l.2.toNat)).set ok
        0).set lptr (y.regs lptr + 1)), ?_, rfl, ?_, ?_, by simp⟩
      · ram_eval [litBody, hl, hone, hzero, hvar, hsgn, hxr, hvx', hτv, hve, hh, ho, hfv, hfs, hfa,
          hfe, hlp]
      · simp +decide [hh, litHas, hbx]
      · have : (τ l.1 == some (!l.2)) = false := by
          rw [beq_eq_false_iff_ne]
          exact fun h' => hve ((optCode_eq_iff _ _).mpr h')
        simp +decide [litOk, hvx, this]

/-- Code that writes none of the registers of `ScanFrame`. -/
def PreservesScan (c : Code .standard 32) : Prop :=
  c.Preserves zero ∧ c.Preserves one ∧ c.Preserves two ∧ c.Preserves xReg ∧ c.Preserves tBase

instance (c : Code .standard 32) : Decidable (PreservesScan c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A run of code that keeps the scan registers and memory keeps the scan frame. -/
theorem ScanFrame.of_exec {τ : Fin n → Option Bool} {x : Fin n} {c : Code .standard 32}
    {y z : Data 32} {T : ℕ} (hf : ScanFrame w τ x y) (hc : PreservesScan c)
    (he : ExecWithin w c y z T) (hm : z.mem = y.mem) : ScanFrame w τ x z where
  zero_eq := (he.regs_eq hc.1).trans hf.zero_eq
  one_eq := (he.regs_eq hc.2.1).trans hf.one_eq
  two_eq := (he.regs_eq hc.2.2.1).trans hf.two_eq
  x_eq := (he.regs_eq hc.2.2.2.1).trans hf.x_eq
  stored := by rw [hm, he.regs_eq hc.2.2.2.2]; exact hf.stored
  fits := by rw [he.regs_eq hc.2.2.2.2]; exact hf.fits
  pos := by rw [he.regs_eq hc.2.2.2.2]; exact hf.pos

/-- The scan frame after setting a register outside it. -/
theorem ScanFrame.set {τ : Fin n → Option Bool} {x : Fin n} {y : Data 32} (hf : ScanFrame w τ x y)
    {i : Fin 32} (hi : i ≠ zero ∧ i ≠ one ∧ i ≠ two ∧ i ≠ xReg ∧ i ≠ tBase) (v : ℕ) :
    ScanFrame w τ x (y.set i v) where
  zero_eq := by rw [Data.set_regs, Function.update_of_ne hi.1.symm]; exact hf.zero_eq
  one_eq := by rw [Data.set_regs, Function.update_of_ne hi.2.1.symm]; exact hf.one_eq
  two_eq := by rw [Data.set_regs, Function.update_of_ne hi.2.2.1.symm]; exact hf.two_eq
  x_eq := by rw [Data.set_regs, Function.update_of_ne hi.2.2.2.1.symm]; exact hf.x_eq
  stored := by
    rw [Data.set_mem, Data.set_regs, Function.update_of_ne hi.2.2.2.2.symm]; exact hf.stored
  fits := by rw [Data.set_regs, Function.update_of_ne hi.2.2.2.2.symm]; exact hf.fits
  pos := by rw [Data.set_regs, Function.update_of_ne hi.2.2.2.2.symm]; exact hf.pos

/-- **The literal loop.** From `hasLit = h` and `ok = o`, the loop over the literals `ls` ends with
`hasLit = h || ls.any (litHas x b)` and `ok = o && ls.all (litOk τ x b)`, and unchanged memory. -/
theorem litLoop_spec (τ : Fin n → Option Bool) (x : Fin n) (b : Bool) (ls : Clause (Fin n))
    (h o : Bool) (y : Data 32) (hf : ScanFrame w τ x y) (hb : y.regs bReg = b.toNat)
    (hl : HoldsList (y.regs lptr) (ls.map litCode) y.mem)
    (hend : y.regs lend = y.regs lptr + ls.length) (hh : y.regs hasLit = h.toNat)
    (ho : y.regs ok = o.toNat) (hle : Fits w (y.regs lend)) :
    ∃ z, ExecWithin w litLoop y z (14 * ls.length + 2) ∧ z.mem = y.mem ∧
      z.regs hasLit = (h || ls.any (litHas x b)).toNat ∧
      z.regs ok = (o && ls.all (litOk τ x b)).toNat ∧ z.regs lptr = y.regs lend ∧
      ScanFrame w τ x z ∧ z.regs bReg = b.toNat ∧ z.regs lend = y.regs lend := by
  induction ls generalizing y h o with
  | nil =>
    refine ⟨y, (ExecWithin.loop_exit ?_).mono (by omega), rfl, by simpa using hh,
      by simpa using ho, by simp [hend], hf, hb, rfl⟩
    simp [Cond.holds_lt, hend]
  | cons l ls ih =>
    have hc : (Cond.lt lptr lend).Holds y := by
      simp only [Cond.holds_lt, hend, List.length_cons]; omega
    have hlit : y.mem (y.regs lptr) = litCode l := by
      simpa using hl.get 0 (by simp)
    have hrest : HoldsList (y.regs lptr + 1) (ls.map litCode) y.mem := by
      have := (holdsList_append_iff (xs := [litCode l]) (ys := ls.map litCode)).mp
        (by simpa using hl)
      simpa using this.2
    obtain ⟨z₁, he₁, hm₁, hh₁, ho₁, hp₁⟩ := litBody_spec τ x b l h o y hf hb hlit hh ho
      (hle.of_le (by simp only [List.length_cons] at hend; omega))
    have hf₁ := hf.of_exec (by decide) he₁ hm₁
    have hb₁ : z₁.regs bReg = b.toNat := by rw [he₁.regs_eq (by decide)]; exact hb
    have hlend₁ : z₁.regs lend = y.regs lend := he₁.regs_eq (by decide)
    obtain ⟨z, he, hm, hhz, hoz, hpz, hfz, hbz, hlz⟩ := ih (h || litHas x b l)
      (o && litOk τ x b l) z₁ hf₁ hb₁ (by rw [hp₁, hm₁]; exact hrest)
      (by rw [hlend₁, hp₁, hend, List.length_cons]; omega) hh₁ ho₁ (by rw [hlend₁]; exact hle)
    refine ⟨z, (ExecWithin.loop_iter hc he₁ he).mono (by simp only [List.length_cons]; omega),
      hm.trans hm₁, ?_, ?_, by rw [hpz, hlend₁], hfz, hbz, hlz.trans hlend₁⟩
    · rw [hhz, List.any_cons, Bool.or_assoc]
    · rw [hoz, List.all_cons, Bool.and_assoc]

/-- **The clause loop.** From `ptr` at the encoding of the clauses `ψ`, which end at `cEnd`, and
`fnd = f`, the loop ends with `fnd = f || ψ.any (unitTest τ x b)` and unchanged memory. -/
theorem clauseLoop_spec (τ : Fin n → Option Bool) (x : Fin n) (b : Bool) (ψ : CNF (Fin n))
    (f : Bool) (y : Data 32) (hf : ScanFrame w τ x y) (hb : y.regs bReg = b.toNat)
    (hp : HoldsList (y.regs ptr) (encodeClauses ψ) y.mem)
    (hend : y.regs ptr + (encodeClauses ψ).length = y.regs cEnd) (hfnd : y.regs fnd = f.toNat)
    (hce : Fits w (y.regs cEnd)) :
    ∃ z, ExecWithin w clauseLoop y z (14 * (encodeClauses ψ).length + 2) ∧ z.mem = y.mem ∧
      z.regs fnd = (f || ψ.any (unitTest τ x b)).toNat ∧ ScanFrame w τ x z ∧
      z.regs bReg = b.toNat ∧ z.regs cEnd = y.regs cEnd ∧ z.regs cBeg = y.regs cBeg := by
  induction ψ generalizing y f with
  | nil =>
    refine ⟨y, (ExecWithin.loop_exit ?_).mono le_rfl, rfl, by simpa using hfnd, hf, hb, rfl, rfl⟩
    simp only [encodeClauses_nil, List.length_nil, Nat.add_zero] at hend
    simp [Cond.holds_lt, hend]
  | cons c ψ ih =>
    rw [encodeClauses_cons] at hp hend
    obtain ⟨hpc, hpψ⟩ := holdsList_append_iff.mp hp
    simp only [List.length_append, length_encodeClause] at hend hpψ
    have hlen : y.mem (y.regs ptr) = c.length := by
      simpa [encodeClause] using hpc.get 0 (by simp)
    have hlits : HoldsList (y.regs ptr + 1) (c.map litCode) y.mem := by
      have := (holdsList_append_iff (xs := [c.length]) (ys := c.map litCode)).mp
        (by simpa [encodeClause] using hpc)
      simpa using this.2
    have hc : (Cond.lt ptr cEnd).Holds y := by simp only [Cond.holds_lt]; omega
    have hf1 : Fits w (y.regs ptr + 1) := hce.of_le (by omega)
    have hf2 : Fits w (y.regs ptr + 1 + c.length) := hce.of_le (by omega)
    have hone := hf.one_eq
    have hzero := hf.zero_eq
    let y₁ := ((((y.set len c.length).set lptr (y.regs ptr + 1)).set lend
      (y.regs ptr + 1 + c.length)).set hasLit 0).set ok 1
    have hinit : ExecWithin w clauseInit y y₁ 5 := by
      ram_eval [y₁, clauseInit, hlen, hone, hzero, hf1, hf2]
    have hfy₁ : ScanFrame w τ x y₁ :=
      ((((hf.set (by decide) _).set (by decide) _).set (by decide) _).set (by decide) _).set
        (by decide) _
    obtain ⟨z₂, he₂, hm₂, hh₂, ho₂, hp₂, hf₂, hb₂, hl₂⟩ := litLoop_spec τ x b c false true y₁ hfy₁
      (by simpa +decide [y₁] using hb) (by simpa +decide [y₁] using hlits) (by simp +decide [y₁])
      (by simp +decide [y₁]) (by simp +decide [y₁]) (by simpa +decide [y₁] using hf2)
    simp only [Bool.false_or, Bool.true_and] at hh₂ ho₂
    have hptr₂ : z₂.regs ptr = y.regs ptr := by
      rw [he₂.regs_eq (by decide)]; simp +decide [y₁]
    have hfnd₂ : z₂.regs fnd = f.toNat := by
      rw [he₂.regs_eq (by decide)]; simpa +decide [y₁] using hfnd
    have hcEnd₂ : z₂.regs cEnd = y.regs cEnd := by
      rw [he₂.regs_eq (by decide)]; simp +decide [y₁]
    have hcBeg₂ : z₂.regs cBeg = y.regs cBeg := by
      rw [he₂.regs_eq (by decide)]; simp +decide [y₁]
    have hl₂' : z₂.regs lend = y.regs ptr + 1 + c.length := by rw [hl₂]; simp +decide [y₁]
    have hm₂' : z₂.mem = y.mem := by rw [hm₂]; rfl
    have hu : Fits w ((c.any (litHas x b)).toNat &&& (c.all (litOk τ x b)).toNat) :=
      hf.fits.of_le (by rw [toNat_and]; have := toNat_le_one (c.any (litHas x b) &&
        c.all (litOk τ x b)); have := hf.pos; omega)
    have hu' : Fits w (f.toNat ||| ((c.any (litHas x b)).toNat &&& (c.all (litOk τ x b)).toNat)) :=
      hf.fits.of_le (by rw [toNat_and, toNat_or]; have := toNat_le_one (f ||
        (c.any (litHas x b) && c.all (litOk τ x b))); have := hf.pos; omega)
    let y₃ := ((z₂.set eq ((c.any (litHas x b)).toNat &&& (c.all (litOk τ x b)).toNat)).set fnd
      (f.toNat ||| ((c.any (litHas x b)).toNat &&& (c.all (litOk τ x b)).toNat))).set ptr
      (y.regs ptr + 1 + c.length)
    have hdone : ExecWithin w clauseDone z₂ y₃ 3 := by
      ram_eval [y₃, clauseDone, hh₂, ho₂, hfnd₂, hl₂', hu, hu', hf2]
    have hfy₃ : ScanFrame w τ x y₃ := ((hf₂.set (by decide) _).set (by decide) _).set (by decide) _
    obtain ⟨z, he, hm, hfz, hfrz, hbz, hcz, hcbz⟩ := ih (f || unitTest τ x b c) y₃ hfy₃
      (by simpa +decide [y₃] using hb₂)
      (by
        simp only [y₃, Data.set_regs, Function.update_self, Data.set_mem, hm₂']
        rw [show y.regs ptr + 1 + c.length = y.regs ptr + (c.length + 1) by omega]
        exact hpψ)
      (by simp +decide [y₃, hcEnd₂]; omega)
      (by simp +decide [y₃, unitTest, toNat_and, toNat_or])
      (by simpa +decide [y₃, hcEnd₂] using hce)
    refine ⟨z, (ExecWithin.loop_iter hc (hinit.seq (he₂.seq hdone)) he).mono ?_,
      by rw [hm]; simp [y₃, hm₂'], ?_, hfrz, hbz, by rw [hcz]; simp +decide [y₃, hcEnd₂],
      by rw [hcbz]; simp +decide [y₃, hcBeg₂]⟩
    · simp only [encodeClauses_cons, List.length_append, length_encodeClause]; omega
    · rw [hfz, List.any_cons, Bool.or_assoc]

/-- **The unit-clause scan.** From the clauses of `φ` stored in `[cBeg, cEnd)`, the scan reports
whether `φ` has a unit clause on `x` with polarity `b` under `τ`, within `14 E + 4` instructions,
where `E` is the length of the encoding, and leaves memory unchanged. -/
theorem unitScan_spec (τ : Fin n → Option Bool) (x : Fin n) (b : Bool) (φ : CNF (Fin n))
    (y : Data 32) (hf : ScanFrame w τ x y) (hb : y.regs bReg = b.toNat)
    (hcl : HoldsList (y.regs cBeg) (encodeClauses φ) y.mem)
    (hend : y.regs cBeg + (encodeClauses φ).length = y.regs cEnd) (hce : Fits w (y.regs cEnd)) :
    ∃ z, ExecWithin w unitScan y z (14 * (encodeClauses φ).length + 4) ∧ z.mem = y.mem ∧
      z.regs fnd = (φ.any (unitTest τ x b)).toNat ∧ ScanFrame w τ x z ∧
      z.regs bReg = b.toNat ∧ z.regs cEnd = y.regs cEnd ∧ z.regs cBeg = y.regs cBeg := by
  have hzero := hf.zero_eq
  obtain ⟨z, he, hm, hfz, hfr, hbz, hcz, hcbz⟩ := clauseLoop_spec τ x b φ false
    ((y.set ptr (y.regs cBeg)).set fnd 0) ((hf.set (by decide) _).set (by decide) _)
    (by simpa +decide using hb) (by simpa +decide using hcl) (by simpa +decide using hend)
    (by simp +decide) (by simpa +decide using hce)
  have hz : (y.set ptr (y.regs cBeg)).regs zero = 0 := by simpa +decide using hzero
  have hc₂ := ExecWithin.copy (B := .standard) (w := w) (d := fnd) (s := zero)
    (x := y.set ptr (y.regs cBeg))
  rw [hz] at hc₂
  refine ⟨z, ((ExecWithin.copy (B := .standard) (w := w) (d := ptr) (s := cBeg) (x := y)).seq
      (hc₂.seq he)).mono (by omega), by rw [hm]; rfl, by simpa using hfz, hfr, hbz,
    by rw [hcz]; simp +decide, by rw [hcbz]; simp +decide⟩

/-- **The forced value.** From the clauses of `φ` stored in `[cBeg, cEnd)` and the partial
assignment `τ` stored at `tBase`, `forcedCode` stores `optCode (forced φ τ x)` in `res` within
`28 E + 15` instructions, where `E` is the length of the encoding, and leaves memory unchanged. -/
theorem forcedCode_spec (φ : CNF (Fin n)) (τ : Fin n → Option Bool) (x : Fin n) (y : Data 32)
    (hf : ScanFrame w τ x y) (hcl : HoldsList (y.regs cBeg) (encodeClauses φ) y.mem)
    (hend : y.regs cBeg + (encodeClauses φ).length = y.regs cEnd) (hce : Fits w (y.regs cEnd)) :
    ∃ z, ExecWithin w forcedCode y z (28 * (encodeClauses φ).length + 15) ∧ z.mem = y.mem ∧
      z.regs res = optCode (forced φ τ x) ∧ ScanFrame w τ x z ∧ z.regs cEnd = y.regs cEnd ∧
      z.regs cBeg = y.regs cBeg := by
  have hone := hf.one_eq
  have hb₀ := ExecWithin.copy (B := .standard) (w := w) (d := bReg) (s := one) (x := y)
  rw [hone] at hb₀
  obtain ⟨z₁, he₁, hm₁, hfnd₁, hf₁, -, hce₁, hcb₁⟩ := unitScan_spec τ x true φ (y.set bReg 1)
    (hf.set (by decide) _) (by simp +decide) (by simpa +decide using hcl)
    (by simpa +decide using hend) (by simpa +decide using hce)
  rw [forced_eq_ite]
  by_cases ht : φ.any (unitTest τ x true) = true
  · have hc : (Cond.eq fnd one).Holds z₁ := by simp [Cond.Holds, hfnd₁, ht, hf₁.one_eq]
    have hr := ExecWithin.copy (B := .standard) (w := w) (d := res) (s := one) (x := z₁)
    rw [hf₁.one_eq] at hr
    refine ⟨z₁.set res 1, (hb₀.seq (he₁.seq (ExecWithin.branch_pos (neg := ram[ bReg ← zero;
        ⟪unitScan⟫; if fnd = one then [ res ← zero ] else [ res ← two ] ]) hc hr))).mono
        (by omega), by rw [Data.set_mem, hm₁]; rfl, by simp [ht, optCode],
      hf₁.set (by decide) _, by simp +decide [hce₁], by simp +decide [hcb₁]⟩
  · have hc : ¬(Cond.eq fnd one).Holds z₁ := by simp [Cond.Holds, hfnd₁, ht, hf₁.one_eq]
    have hb₁ := ExecWithin.copy (B := .standard) (w := w) (d := bReg) (s := zero) (x := z₁)
    rw [hf₁.zero_eq] at hb₁
    obtain ⟨z₂, he₂, hm₂, hfnd₂, hf₂, -, hce₂, hcb₂⟩ := unitScan_spec τ x false φ (z₁.set bReg 0)
      (hf₁.set (by decide) _) (by simp +decide)
      (by simpa +decide [hm₁, hcb₁] using hcl) (by simpa +decide [hce₁, hcb₁] using hend)
      (by simpa +decide [hce₁] using hce)
    simp only [ht, Bool.false_eq_true, ↓reduceIte]
    by_cases hf' : φ.any (unitTest τ x false) = true
    · have hc' : (Cond.eq fnd one).Holds z₂ := by simp [Cond.Holds, hfnd₂, hf', hf₂.one_eq]
      have hr := ExecWithin.copy (B := .standard) (w := w) (d := res) (s := zero) (x := z₂)
      rw [hf₂.zero_eq] at hr
      refine ⟨z₂.set res 0, (hb₀.seq (he₁.seq (ExecWithin.branch_neg (pos := ram[ res ← one ]) hc
          (hb₁.seq (he₂.seq (ExecWithin.branch_pos (neg := ram[ res ← two ]) hc' hr)))))).mono
          (by omega), by rw [Data.set_mem, hm₂]; simp [hm₁], by simp [hf', optCode],
        hf₂.set (by decide) _, by simp +decide [hce₂, hce₁], by simp +decide [hcb₂, hcb₁]⟩
    · have hc' : ¬(Cond.eq fnd one).Holds z₂ := by simp [Cond.Holds, hfnd₂, hf', hf₂.one_eq]
      have hr := ExecWithin.copy (B := .standard) (w := w) (d := res) (s := two) (x := z₂)
      rw [hf₂.two_eq] at hr
      refine ⟨z₂.set res 2, (hb₀.seq (he₁.seq (ExecWithin.branch_neg (pos := ram[ res ← one ]) hc
          (hb₁.seq (he₂.seq (ExecWithin.branch_neg (pos := ram[ res ← zero ]) hc' hr)))))).mono
          (by omega), by rw [Data.set_mem, hm₂]; simp [hm₁], by simp [hf', optCode],
        hf₂.set (by decide) _, by simp +decide [hce₂, hce₁], by simp +decide [hcb₂, hcb₁]⟩

end Specs

end Cslib.Algorithms.WordRAM.PPZ
