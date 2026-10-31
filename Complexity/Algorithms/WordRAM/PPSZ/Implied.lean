/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.WordRAM.PPSZ.Clauses
import Complexity.Computability.WordRAM.Sequence
import Mathlib.Data.Nat.Bitwise

/-!
# w-implication on the word RAM

`Cslib.Algorithms.WordRAM.PPSZ.impliedCode` computes the value w-implied on a variable
(`Cslib.Complexity.PPSZ.implied`), the oracle of PPSZ. The formula is stored as in
`Cslib.Algorithms.WordRAM.Schoening.encodeClauses`, the partial assignment as in
`Cslib.Algorithms.WordRAM.PPZ.PartialAt`, and the bound `s` on the number of clauses is stored in
the word after a scratch base address. The program runs the search
`Cslib.Algorithms.WordRAM.PPSZ.addrTest` for the polarity `true`, then, if needed, for `false`:

* an odometer `D` steps through every choice of `s` clause addresses
  (`Cslib.Algorithms.WordRAM.PPSZ.outerSearch`), and for each, an odometer `E` steps through every
  choice of one literal address in each chosen clause
  (`Cslib.Algorithms.WordRAM.PPSZ.innerSearch`);
* a choice of literals is tested for compatibility (`Cslib.Algorithms.WordRAM.PPSZ.goodTest`): no
  chosen literal is falsified by the partial assignment with `x` set to `!b`, and no two are
  complementary;
* `x = b` is implied when the assignment already sets `x` to `b`, or some choice of clauses has no
  compatible choice of literals.

Both odometers step with `Cslib.Algorithms.WordRAM.PPSZ.nextSection`, so they visit every section
(`Cslib.Algorithms.WordRAM.PPSZ.nextSection_sections`). The arrays `D` and `E` take `2 s` words of
scratch memory, which the program sets back to zero at the end. On scratch memory that starts out
zero, `Cslib.Algorithms.WordRAM.PPSZ.impliedCode_spec` therefore leaves memory unchanged and
stores the word of `implied φ s τ x`.

## Main definitions

* `Cslib.Algorithms.WordRAM.PPSZ.ImpFrame`: the registers and memory the search relies on.
* `Cslib.Algorithms.WordRAM.PPSZ.initD`, `Cslib.Algorithms.WordRAM.PPSZ.incD`,
  `Cslib.Algorithms.WordRAM.PPSZ.initE`, `Cslib.Algorithms.WordRAM.PPSZ.incE`: the odometers.
* `Cslib.Algorithms.WordRAM.PPSZ.goodTest`: the compatibility test.
* `Cslib.Algorithms.WordRAM.PPSZ.innerSearch`, `Cslib.Algorithms.WordRAM.PPSZ.outerSearch`,
  `Cslib.Algorithms.WordRAM.PPSZ.impScan`: the nested search.
* `Cslib.Algorithms.WordRAM.PPSZ.impliedCode`: the implied value.
* `Cslib.Algorithms.WordRAM.PPSZ.impliedTime`: its instruction bound.

## Main results

* `Cslib.Algorithms.WordRAM.PPSZ.impScan_spec`: the search decides w-implication.
* `Cslib.Algorithms.WordRAM.PPSZ.impliedCode_spec`: the implied value, within
  `impliedTime s E` instructions, where `E` is the length of the encoding of the clauses.
* `Cslib.Algorithms.WordRAM.PPSZ.impliedTime_le`: `impliedTime s E ≤ 140 (s + 1)² (E + 1)^(2 s)`.

## References

* [R. Paturi, P. Pudlák, M. Saks, F. Zane, *An improved exponential-time algorithm for
  k-SAT*][PaturiPudlakSaksZane2005]
* [T. Hertli, *3-SAT faster and simpler*][Hertli2011]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.PPSZ

open Cslib.WordRAM Cslib.WordRAM.Block Cslib.Logic.PL Cslib.Complexity.PPSZ
open Cslib.Algorithms.WordRAM.Schoening (litCode encodeClause encodeClauses litCode_lt
  litCode_shiftRight litCode_and_one encodeClauses_cons length_encodeClause)
open Cslib.Algorithms.WordRAM.PPZ (optCode PartialAt)
open Cslib.Algorithms.WordRAM.PPZ.Reg

variable {n : ℕ}

/-! ### Registers -/

namespace Reg

/-- The bound `s` on the number of clauses. -/
abbrev sReg : Fin 32 := 6
/-- Address of the array `D` of chosen clause addresses. -/
abbrev dBase : Fin 32 := 7
/-- Address of the array `E` of chosen literal addresses, `dBase + s`. -/
abbrev eBase : Fin 32 := 8
/-- Index into `D` and `E`. -/
abbrev jR : Fin 32 := 9
/-- Second index into `E`. -/
abbrev kR : Fin 32 := 10
/-- Scratch address. -/
abbrev adr : Fin 32 := 11
/-- A clause address. -/
abbrev dv : Fin 32 := 12
/-- A literal address. -/
abbrev ev : Fin 32 := 13
/-- A clause length, or a word of the partial assignment. -/
abbrev lenR : Fin 32 := 14
/-- An end address, or a comparison value. -/
abbrev stop : Fin 32 := 15
/-- A literal code. -/
abbrev litR : Fin 32 := 16
/-- A variable, or the code of the complementary literal. -/
abbrev auxR : Fin 32 := 17
/-- The result of a test or search. -/
abbrev sat : Fin 32 := 18
/-- Whether the clause odometer continues. -/
abbrev contO : Fin 32 := 26
/-- Whether the literal odometer continues. -/
abbrev contI : Fin 32 := 27
/-- A sign. -/
abbrev sgnR : Fin 32 := 28

end Reg

open Reg

/-! ### The frame of the search -/

/-- The registers and memory the search relies on: the constants, the variable `x`, the polarity
`b`, the clauses of `φ` stored from `C`, the partial assignment `τ` stored from `Tb`, the bound `s`,
and the arrays `D` at `Db` and `E` at `Db + s`, above the clauses, the partial assignment and the
literal codes. -/
structure ImpFrame (w : ℕ) (φ : CNF (Fin n)) (τ : Fin n → Option Bool) (x : Fin n) (b : Bool)
    (C Tb s Db : ℕ) (y : Data 32) : Prop where
  zero_eq : y.regs zero = 0
  one_eq : y.regs one = 1
  x_eq : y.regs xReg = x
  b_eq : y.regs bReg = b.toNat
  cBeg_eq : y.regs cBeg = C
  cEnd_eq : y.regs cEnd = C + (encodeClauses φ).length
  tBase_eq : y.regs tBase = Tb
  s_eq : y.regs sReg = s
  dBase_eq : y.regs dBase = Db
  eBase_eq : y.regs eBase = Db + s
  clauses : HoldsList C (encodeClauses φ) y.mem
  stored : PartialAt y.mem Tb τ
  clauses_le : C + (encodeClauses φ).length ≤ Db
  stored_le : Tb + n ≤ Db
  codes_le : 2 * n ≤ Db
  fits : Fits w (Db + 2 * s + 1)

/-- Code that writes none of the registers of `ImpFrame`. -/
def PreservesImp (c : Code .standard 32) : Prop :=
  c.Preserves zero ∧ c.Preserves one ∧ c.Preserves xReg ∧ c.Preserves bReg ∧ c.Preserves cBeg ∧
    c.Preserves cEnd ∧ c.Preserves tBase ∧ c.Preserves sReg ∧ c.Preserves dBase ∧
    c.Preserves eBase

instance (c : Code .standard 32) : Decidable (PreservesImp c) :=
  inferInstanceAs (Decidable (_ ∧ _))

section Frame

variable {w : ℕ} {φ : CNF (Fin n)} {τ : Fin n → Option Bool} {x : Fin n} {b : Bool}
  {C Tb s Db : ℕ}

/-- The frame survives a change that keeps its registers and the memory below `Db`. -/
theorem ImpFrame.congr {y z : Data 32} (h : ImpFrame w φ τ x b C Tb s Db y)
    (hr : ∀ i ∈ ({zero, one, xReg, bReg, cBeg, cEnd, tBase, sReg, dBase, eBase} :
      Finset (Fin 32)), z.regs i = y.regs i)
    (hm : ∀ a < Db, z.mem a = y.mem a) : ImpFrame w φ τ x b C Tb s Db z where
  zero_eq := (hr zero (by decide)).trans h.zero_eq
  one_eq := (hr one (by decide)).trans h.one_eq
  x_eq := (hr xReg (by decide)).trans h.x_eq
  b_eq := (hr bReg (by decide)).trans h.b_eq
  cBeg_eq := (hr cBeg (by decide)).trans h.cBeg_eq
  cEnd_eq := (hr cEnd (by decide)).trans h.cEnd_eq
  tBase_eq := (hr tBase (by decide)).trans h.tBase_eq
  s_eq := (hr sReg (by decide)).trans h.s_eq
  dBase_eq := (hr dBase (by decide)).trans h.dBase_eq
  eBase_eq := (hr eBase (by decide)).trans h.eBase_eq
  clauses := h.clauses.frame fun a _ ha => hm a (by have := h.clauses_le; omega)
  stored := fun v => (hm _ (by have := h.stored_le; omega)).trans (h.stored v)
  clauses_le := h.clauses_le
  stored_le := h.stored_le
  codes_le := h.codes_le
  fits := h.fits

/-- A run of code that keeps the frame registers and the memory below `Db` keeps the frame. -/
theorem ImpFrame.of_exec {c : Code .standard 32} {y z : Data 32} {T : ℕ}
    (h : ImpFrame w φ τ x b C Tb s Db y) (hc : PreservesImp c) (he : ExecWithin w c y z T)
    (hm : ∀ a < Db, z.mem a = y.mem a) : ImpFrame w φ τ x b C Tb s Db z := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hc
  refine h.congr (fun i hi => ?_) hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact he.regs_eq ‹_›

/-- The frame after setting a register outside it. -/
theorem ImpFrame.set {y : Data 32} (h : ImpFrame w φ τ x b C Tb s Db y) {i : Fin 32}
    (hi : i ∉ ({zero, one, xReg, bReg, cBeg, cEnd, tBase, sReg, dBase, eBase} :
      Finset (Fin 32))) (v : ℕ) : ImpFrame w φ τ x b C Tb s Db (y.set i v) :=
  h.congr (fun j hj => by
    rw [Data.set_regs, Function.update_of_ne]
    rintro rfl
    exact hi hj) fun _ _ => rfl

/-- The frame after a store at or above `Db`. -/
theorem ImpFrame.write {y : Data 32} (h : ImpFrame w φ τ x b C Tb s Db y) {a : ℕ} (ha : Db ≤ a)
    (v : ℕ) : ImpFrame w φ τ x b C Tb s Db (y.write a v) :=
  h.congr (fun _ _ => rfl) fun a' ha' => by
    rw [Data.write_mem, Function.update_of_ne (by omega)]

/-- Values up to the end of the arrays fit a word. -/
theorem ImpFrame.fits_le {y : Data 32} (h : ImpFrame w φ τ x b C Tb s Db y) {v : ℕ}
    (hv : v ≤ Db + 2 * s + 1) : Fits w v :=
  h.fits.of_le hv

end Frame

/-- A represented list with a first entry. -/
theorem holdsList_cons_iff {base a : ℕ} {l : List ℕ} {mem : ℕ → ℕ} :
    HoldsList base (a :: l) mem ↔ mem base = a ∧ HoldsList (base + 1) l mem := by
  rw [show a :: l = [a] ++ l from rfl, holdsList_append_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by simpa using h1.get 0 (by simp), by simpa using h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, by simpa using h2⟩
    obtain ⟨i, hi⟩ := i
    have hi' : i = 0 := by dsimp only at hi; simp at hi; omega
    subst hi'
    simpa [Block.read] using h1

/-! ### The clause odometer -/

/-- Set `D[j]` to the first clause address. -/
def initDBody : Code .standard 32 := ram[ adr ← dBase + jR; *adr ← cBeg; jR ← jR + one ]

/-- Set `D[j], …, D[s - 1]` to the first clause address. -/
def initDLoop : Code .standard 32 := .loop (.lt jR sReg) initDBody

/-- **Start the clause odometer**: every entry of `D` is the first clause address. -/
def initD : Code .standard 32 := ram[ jR ← zero; ⟪initDLoop⟫ ]

/-- Advance `D[j]` to the next clause address, or, after the last clause, return it to the first
one and carry into `D[j + 1]`. Without a carry, `jR` becomes `s + 1` and the loop stops. -/
def incDBody : Code .standard 32 := ram[
  adr ← dBase + jR; dv ← *adr; lenR ← *dv; dv ← dv + one; dv ← dv + lenR;
  if dv = cEnd then [ *adr ← cBeg; jR ← jR + one ] else [ *adr ← dv; jR ← sReg + one ] ]

/-- The carries of the clause odometer from `D[j]` on. -/
def incDLoop : Code .standard 32 := .loop (.lt jR sReg) incDBody

/-- **Step the clause odometer**: `contO` becomes `0` after the last choice of clauses, and `1`
otherwise. -/
def incD : Code .standard 32 := ram[ jR ← zero; ⟪incDLoop⟫; contO ← jR - sReg ]

section ClauseOdometer

variable {w : ℕ} {φ : CNF (Fin n)} {τ : Fin n → Option Bool} {x : Fin n} {b : Bool}
  {C Tb s Db : ℕ}

/-- **The start loop of the clause odometer** from entry `j`: it stores the first clause address
in `D[j], …, D[s - 1]` and keeps the memory outside them. -/
theorem initDLoop_spec : ∀ (d : ℕ) (y : Data 32), ImpFrame w φ τ x b C Tb s Db y →
    y.regs jR + d = s →
    ∃ z, ExecWithin w initDLoop y z (5 * d + 2) ∧ ImpFrame w φ τ x b C Tb s Db z ∧
      HoldsList (Db + y.regs jR) (List.replicate d C) z.mem ∧
      ∀ a, a < Db + y.regs jR ∨ Db + s ≤ a → z.mem a = y.mem a
  | 0, y, hf, hd => by
    have hc : ¬(Cond.lt jR sReg).Holds y := by simp [Cond.holds_lt, hf.s_eq]; omega
    exact ⟨y, (ExecWithin.loop_exit hc).mono (by omega), hf, by simp [holdsList_nil],
      fun _ _ => rfl⟩
  | d + 1, y, hf, hd => by
    obtain ⟨j, hj⟩ : ∃ j, y.regs jR = j := ⟨_, rfl⟩
    rw [hj] at hd ⊢
    have hc : (Cond.lt jR sReg).Holds y := by simp [Cond.holds_lt, hf.s_eq, hj]; omega
    have hf1 : Fits w (Db + j) := hf.fits_le (by omega)
    have hf2 : Fits w (j + 1) := hf.fits_le (by omega)
    let y₁ := ((y.set adr (Db + j)).write (Db + j) C).set jR (j + 1)
    have hrun : ExecWithin w initDBody y y₁ 3 := by
      ram_eval [y₁, initDBody, hf.dBase_eq, hj, hf.cBeg_eq, hf.one_eq, hf1, hf2]
    have hy₁ : ImpFrame w φ τ x b C Tb s Db y₁ :=
      ((hf.set (by decide) _).write (by omega) _).set (by decide) _
    obtain ⟨z, hz, hzf, hzl, hzm⟩ := initDLoop_spec d y₁ hy₁ (by simp [y₁]; omega)
    have hj₁ : y₁.regs jR = j + 1 := by simp [y₁]
    rw [hj₁] at hzl hzm
    refine ⟨z, (ExecWithin.loop_iter hc hrun hz).mono (by omega), hzf, ?_, fun a ha => ?_⟩
    · rw [List.replicate_succ, holdsList_cons_iff]
      refine ⟨?_, by simpa [Nat.add_assoc] using hzl⟩
      rw [hzm _ (by omega)]
      simp [y₁]
    · rw [hzm _ (by omega)]
      simp only [y₁, Data.set_mem, Data.write_mem]
      rw [Function.update_of_ne (by omega)]

/-- **Start the clause odometer**: `D` holds `s` copies of the first clause address, and the
memory outside `D` is unchanged, within `5 s + 3` instructions. -/
theorem initD_spec (y : Data 32) (hf : ImpFrame w φ τ x b C Tb s Db y) :
    ∃ z, ExecWithin w initD y z (5 * s + 3) ∧ ImpFrame w φ τ x b C Tb s Db z ∧
      HoldsList Db (List.replicate s C) z.mem ∧
      ∀ a, a < Db ∨ Db + s ≤ a → z.mem a = y.mem a := by
  have h₀ := ExecWithin.copy (B := .standard) (w := w) (d := jR) (s := zero) (x := y)
  rw [hf.zero_eq] at h₀
  obtain ⟨z, hz, hzf, hzl, hzm⟩ := initDLoop_spec s (y.set jR 0) (hf.set (by decide) 0)
    (by simp)
  simp only [Data.set_regs, Function.update_self, Nat.add_zero] at hzl hzm
  exact ⟨z, (h₀.seq hz).mono (by omega), hzf, hzl, fun a ha => by
    rw [hzm a (by omega)]; rfl⟩

/-- **The carry loop of the clause odometer** from entry `j`, on a choice `u` of clause addresses
in `D[j], …`: if the odometer step on `u` has a result, `D[j], …` holds it and `jR = s + 1`; if
not, `jR = s`. The memory outside `D[j], …, D[s - 1]` is unchanged. -/
theorem incDLoop_spec : ∀ (u : List ℕ) (y : Data 32), ImpFrame w φ τ x b C Tb s Db y →
    y.regs jR + u.length = s → (∀ a ∈ u, a ∈ clauseAddrs C φ) →
    HoldsList (Db + y.regs jR) u y.mem →
    ∃ z, ExecWithin w incDLoop y z (12 * u.length + 2) ∧ ImpFrame w φ τ x b C Tb s Db z ∧
      (∀ a, a < Db + y.regs jR ∨ Db + s ≤ a → z.mem a = y.mem a) ∧
      (∀ u', nextSection (List.replicate u.length (clauseAddrs C φ)) u = some u' →
        z.regs jR = s + 1 ∧ HoldsList (Db + y.regs jR) u' z.mem) ∧
      (nextSection (List.replicate u.length (clauseAddrs C φ)) u = none → z.regs jR = s)
  | [], y, hf, hd, _, _ => by
    simp only [List.length_nil, Nat.add_zero] at hd
    have hc : ¬(Cond.lt jR sReg).Holds y := by simp [Cond.holds_lt, hf.s_eq]; omega
    refine ⟨y, (ExecWithin.loop_exit hc).mono (by omega), hf, fun _ _ => rfl, ?_, ?_⟩
    · intro u' h; simp [nextSection] at h
    · intro _; simpa using hd
  | a :: u, y, hf, hd, hA, hl => by
    obtain ⟨j, hj⟩ : ∃ j, y.regs jR = j := ⟨_, rfl⟩
    rw [hj] at hd hl ⊢
    simp only [List.length_cons] at hd
    have haA : a ∈ clauseAddrs C φ := hA a (by simp)
    have hb := bounds_of_mem_clauseAddrs haA
    have hc : (Cond.lt jR sReg).Holds y := by simp [Cond.holds_lt, hf.s_eq, hj]; omega
    obtain ⟨hla, hlu⟩ := holdsList_cons_iff.mp hl
    have hlen : y.mem a = (clauseOf C φ a).length := mem_clauseAddr hf.clauses haA
    set len := (clauseOf C φ a).length with hlen_def
    have hf1 : Fits w (Db + j) := hf.fits_le (by omega)
    have hf2 : Fits w (a + 1) := hf.fits_le (by have := hf.clauses_le; omega)
    have hf3 : Fits w (a + 1 + len) := hf.fits_le (by have := hf.clauses_le; omega)
    have hsucc : succIn (clauseAddrs C φ) a =
        if a + 1 + len = C + (encodeClauses φ).length then none else some (a + 1 + len) :=
      succIn_clauseAddrs haA
    have hhead : (clauseAddrs C φ).headD 0 = C :=
      headD_clauseAddrs (fun h => by simp [h, clauseAddrs] at haA) 0
    by_cases hend : a + 1 + len = C + (encodeClauses φ).length
    · -- carry
      have hf4 : Fits w (j + 1) := hf.fits_le (by omega)
      let y₁ := ((((((y.set adr (Db + j)).set dv a).set lenR len).set dv (a + 1)).set dv
        (a + 1 + len)).write (Db + j) C).set jR (j + 1)
      have hrun : ExecWithin w incDBody y y₁ 9 := by
        ram_eval [y₁, incDBody, hf.dBase_eq, hj, hla, hlen, hf.one_eq, hf.cEnd_eq, eq_true hend,
          hf.cBeg_eq, hf1, hf2, hf3, hf4]
      have hy₁ : ImpFrame w φ τ x b C Tb s Db y₁ :=
        ((((((hf.set (by decide) _).set (by decide) _).set (by decide) _).set (by decide)
          _).set (by decide) _).write (by omega) _).set (by decide) _
      have hj₁ : y₁.regs jR = j + 1 := by simp [y₁]
      have hy₁m : ∀ a', a' ≠ Db + j → y₁.mem a' = y.mem a' := fun a' ha' => by
        simp only [y₁, Data.set_mem, Data.write_mem]; rw [Function.update_of_ne ha']
      obtain ⟨z, hz, hzf, hzm, hzs, hzn⟩ := incDLoop_spec u y₁ hy₁ (by rw [hj₁]; omega)
        (fun a' h => hA a' (by simp [h]))
        (by rw [hj₁]; exact hlu.frame fun a' h1 h2 => hy₁m a' (by omega))
      rw [hj₁] at hzm hzs
      have hzj : z.mem (Db + j) = C := by
        rw [hzm _ (by omega)]; simp [y₁]
      refine ⟨z, (ExecWithin.loop_iter hc hrun hz).mono (by simp; omega), hzf,
        fun a' ha' => by rw [hzm a' (by omega), hy₁m a' (by omega)], ?_, ?_⟩
      · intro u' h
        simp only [List.length_cons, List.replicate_succ, nextSection, hsucc, hend, ↓reduceIte,
          hhead] at h
        obtain ⟨u'', hu'', rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨hzj', hzl⟩ := hzs u'' hu''
        exact ⟨hzj', holdsList_cons_iff.mpr ⟨hzj, hzl⟩⟩
      · intro h
        simp only [List.length_cons, List.replicate_succ, nextSection, hsucc, hend, ↓reduceIte,
          Option.map_eq_none_iff] at h
        exact hzn h
    · -- no carry
      have hf4 : Fits w (s + 1) := hf.fits_le (by omega)
      let y₁ := ((((((y.set adr (Db + j)).set dv a).set lenR len).set dv (a + 1)).set dv
        (a + 1 + len)).write (Db + j) (a + 1 + len)).set jR (s + 1)
      have hrun : ExecWithin w incDBody y y₁ 10 := by
        ram_eval [y₁, incDBody, hf.dBase_eq, hj, hla, hlen, hf.one_eq, hf.cEnd_eq, eq_false hend,
          hf.s_eq, hf1, hf2, hf3, hf4]
      have hy₁ : ImpFrame w φ τ x b C Tb s Db y₁ :=
        ((((((hf.set (by decide) _).set (by decide) _).set (by decide) _).set (by decide)
          _).set (by decide) _).write (by omega) _).set (by decide) _
      have hc₁ : ¬(Cond.lt jR sReg).Holds y₁ := by
        simp +decide [Cond.holds_lt, y₁, hf.s_eq]
      refine ⟨y₁, (ExecWithin.loop_iter hc hrun (ExecWithin.loop_exit hc₁)).mono
        (by simp only [List.length_cons]; omega), hy₁, fun a' ha' => by
          simp only [y₁, Data.set_mem, Data.write_mem]; rw [Function.update_of_ne (by omega)],
        ?_, ?_⟩
      · intro u' h
        simp only [List.length_cons, List.replicate_succ, nextSection, hsucc, hend, ↓reduceIte,
          Option.some.injEq] at h
        subst h
        refine ⟨by simp [y₁], holdsList_cons_iff.mpr ⟨by simp [y₁], ?_⟩⟩
        exact hlu.frame fun a' h1 h2 => by
          simp only [y₁, Data.set_mem, Data.write_mem]; rw [Function.update_of_ne (by omega)]
      · intro h
        simp only [List.length_cons, List.replicate_succ, nextSection, hsucc, hend, ↓reduceIte,
          reduceCtorEq] at h

/-- **Step the clause odometer** on a choice `t` of `s` clause addresses in `D`: if the odometer
step on `t` has a result, `D` holds it and `contO = 1`; if not, `contO = 0`. The memory outside
`D` is unchanged, within `12 s + 4` instructions. -/
theorem incD_spec (t : List ℕ) (y : Data 32) (hf : ImpFrame w φ τ x b C Tb s Db y)
    (ht : t ∈ (List.replicate s (clauseAddrs C φ)).sections) (hl : HoldsList Db t y.mem) :
    ∃ z, ExecWithin w incD y z (12 * s + 4) ∧ ImpFrame w φ τ x b C Tb s Db z ∧
      (∀ a, a < Db ∨ Db + s ≤ a → z.mem a = y.mem a) ∧
      (∀ t', nextSection (List.replicate s (clauseAddrs C φ)) t = some t' →
        z.regs contO = 1 ∧ HoldsList Db t' z.mem) ∧
      (nextSection (List.replicate s (clauseAddrs C φ)) t = none → z.regs contO = 0) := by
  obtain ⟨hlen, hA⟩ := mem_sections_replicate.mp ht
  have h₀ := ExecWithin.copy (B := .standard) (w := w) (d := jR) (s := zero) (x := y)
  rw [hf.zero_eq] at h₀
  obtain ⟨z, hz, hzf, hzm, hzs, hzn⟩ := incDLoop_spec t (y.set jR 0) (hf.set (by decide) 0)
    (by simp [hlen]) hA (by simpa using hl)
  simp only [Data.set_regs, Function.update_self, Nat.add_zero, hlen] at hzm hzs hzn
  have hjz : z.regs jR ≤ s + 1 := by
    rcases hns : nextSection (List.replicate s (clauseAddrs C φ)) t with _ | t'
    · rw [hzn hns]; omega
    · rw [(hzs t' hns).1]
  have hfz : Fits w (z.regs jR - z.regs sReg) := hzf.fits_le (by rw [hzf.s_eq]; omega)
  have hout := ExecWithin.bin (w := w) (f := .sub) (d := contO) (i := jR) (j := sReg) (x := z) hfz
  refine ⟨_, (h₀.seq (hz.seq hout)).mono (by rw [hlen]; omega), hzf.set (by decide) _,
    fun a ha => by rw [Data.set_mem, hzm a ha]; rfl, ?_, ?_⟩
  · intro t' h
    obtain ⟨hj, hzl⟩ := hzs t' h
    exact ⟨by simp [BinOp.eval, hj, hzf.s_eq], hzl⟩
  · intro h
    simp [BinOp.eval, hzn h, hzf.s_eq]

end ClauseOdometer

/-! ### The literal odometer -/

/-- The addresses of the literal codes of the clause stored at address `p`. -/
def litAddrs (C : ℕ) (φ : CNF (Fin n)) (p : ℕ) : List ℕ :=
  List.range' (p + 1) (clauseOf C φ p).length

/-- Set `E[j]` to the first literal address of the clause `D[j]`, and clear `sat` if that clause
is empty. -/
def initEBody : Code .standard 32 := ram[
  adr ← dBase + jR; dv ← *adr; lenR ← *dv;
  if lenR = zero then [ sat ← zero ] else [ sat ← sat ];
  dv ← dv + one; adr ← eBase + jR; *adr ← dv; jR ← jR + one ]

/-- Start `E[j], …, E[s - 1]`. -/
def initELoop : Code .standard 32 := .loop (.lt jR sReg) initEBody

/-- **Start the literal odometer**: every entry of `E` is the first literal address of its clause,
and `sat = 1` exactly when no chosen clause is empty. -/
def initE : Code .standard 32 := ram[ sat ← one; jR ← zero; ⟪initELoop⟫ ]

/-- Advance `E[j]` to the next literal address of the clause `D[j]`, or, after its last literal,
return it to the first one and carry into `E[j + 1]`. Without a carry, `jR` becomes `s + 1` and
the loop stops. -/
def incEBody : Code .standard 32 := ram[
  adr ← eBase + jR; ev ← *adr; ev ← ev + one; dv ← dBase + jR; dv ← *dv; lenR ← *dv;
  stop ← dv + one; stop ← stop + lenR;
  if ev = stop then [ ev ← dv + one; *adr ← ev; jR ← jR + one ]
  else [ *adr ← ev; jR ← sReg + one ] ]

/-- The carries of the literal odometer from `E[j]` on. -/
def incELoop : Code .standard 32 := .loop (.lt jR sReg) incEBody

/-- **Step the literal odometer**: `contI` becomes `0` after the last choice of literals, and `1`
otherwise. -/
def incE : Code .standard 32 := ram[ jR ← zero; ⟪incELoop⟫; contI ← jR - sReg ]

section LiteralOdometer

variable {w : ℕ} {φ : CNF (Fin n)} {τ : Fin n → Option Bool} {x : Fin n} {b : Bool}
  {C Tb s Db : ℕ}

/-- **The start loop of the literal odometer** from entry `j`, on the clause addresses `u` in
`D[j], …`: it stores their first literal addresses in `E[j], …` and clears `sat` if one of the
clauses is empty. The memory outside `E[j], …, E[s - 1]` is unchanged. -/
theorem initELoop_spec : ∀ (u : List ℕ) (f : Bool) (y : Data 32),
    ImpFrame w φ τ x b C Tb s Db y → y.regs jR + u.length = s →
    (∀ a ∈ u, a ∈ clauseAddrs C φ) → HoldsList (Db + y.regs jR) u y.mem →
    y.regs sat = f.toNat →
    ∃ z, ExecWithin w initELoop y z (12 * u.length + 2) ∧ ImpFrame w φ τ x b C Tb s Db z ∧
      (∀ a, a < Db + s + y.regs jR ∨ Db + 2 * s ≤ a → z.mem a = y.mem a) ∧
      HoldsList (Db + s + y.regs jR) (u.map (· + 1)) z.mem ∧
      HoldsList (Db + y.regs jR) u z.mem ∧
      z.regs sat = (f && u.all fun a => (clauseOf C φ a).length != 0).toNat
  | [], f, y, hf, hd, _, _, hs => by
    simp only [List.length_nil, Nat.add_zero] at hd
    have hc : ¬(Cond.lt jR sReg).Holds y := by simp [Cond.holds_lt, hf.s_eq]; omega
    exact ⟨y, (ExecWithin.loop_exit hc).mono (by omega), hf, fun _ _ => rfl,
      by simp [holdsList_nil], by simp [holdsList_nil], by simpa using hs⟩
  | a :: u, f, y, hf, hd, hA, hl, hs => by
    obtain ⟨j, hj⟩ : ∃ j, y.regs jR = j := ⟨_, rfl⟩
    rw [hj] at hd hl ⊢
    simp only [List.length_cons] at hd
    have haA : a ∈ clauseAddrs C φ := hA a (by simp)
    have hb := bounds_of_mem_clauseAddrs haA
    have hc : (Cond.lt jR sReg).Holds y := by simp [Cond.holds_lt, hf.s_eq, hj]; omega
    obtain ⟨hla, hlu⟩ := holdsList_cons_iff.mp hl
    have hlen : y.mem a = (clauseOf C φ a).length := mem_clauseAddr hf.clauses haA
    set len := (clauseOf C φ a).length with hlen_def
    have hf1 : Fits w (Db + j) := hf.fits_le (by omega)
    have hf2 : Fits w (a + 1) := hf.fits_le (by have := hf.clauses_le; omega)
    have hf3 : Fits w (Db + s + j) := hf.fits_le (by omega)
    have hf4 : Fits w (j + 1) := hf.fits_le (by omega)
    let y₁ := (((((((y.set adr (Db + j)).set dv a).set lenR len).set sat
      (f && len != 0).toNat).set dv (a + 1)).set adr (Db + s + j)).write (Db + s + j)
      (a + 1)).set jR (j + 1)
    have hrun : ExecWithin w initEBody y y₁ 10 := by
      by_cases hl0 : len = 0
      · have h0 : (f && len != 0).toNat = 0 := by simp [hl0]
        ram_eval [y₁, initEBody, hf.dBase_eq, hj, hla, hlen, eq_true hl0, hf.zero_eq, h0,
          hf.one_eq, hf.eBase_eq, hf1, hf2, hf3, hf4]
      · have h1 : (f && len != 0).toNat = f.toNat := by
          rw [show (len != 0) = true from bne_iff_ne.mpr hl0, Bool.and_true]
        ram_eval [y₁, initEBody, hf.dBase_eq, hj, hla, hlen, eq_false hl0, hf.zero_eq, hs, h1,
          hf.one_eq, hf.eBase_eq, hf1, hf2, hf3, hf4]
    have hy₁ : ImpFrame w φ τ x b C Tb s Db y₁ :=
      (((((((hf.set (by decide) _).set (by decide) _).set (by decide) _).set (by decide) _).set
        (by decide) _).set (by decide) _).write (by omega) _).set (by decide) _
    have hj₁ : y₁.regs jR = j + 1 := by simp [y₁]
    have hy₁m : ∀ a', a' ≠ Db + s + j → y₁.mem a' = y.mem a' := fun a' ha' => by
      simp only [y₁, Data.set_mem, Data.write_mem]; rw [Function.update_of_ne ha']
    have hs₁ : y₁.regs sat = (f && len != 0).toNat := by
      simp +decide [y₁]
    obtain ⟨z, hz, hzf, hzm, hze, hzd, hzs⟩ := initELoop_spec u (f && len != 0) y₁ hy₁
      (by rw [hj₁]; omega) (fun a' h => hA a' (by simp [h]))
      (by rw [hj₁]; exact hlu.frame fun a' h1 h2 => hy₁m a' (by omega)) hs₁
    rw [hj₁] at hzm hze hzd
    refine ⟨z, (ExecWithin.loop_iter hc hrun hz).mono (by simp only [List.length_cons]; omega),
      hzf, fun a' ha' => by rw [hzm a' (by omega), hy₁m a' (by omega)], ?_, ?_, ?_⟩
    · rw [List.map_cons, holdsList_cons_iff]
      refine ⟨by rw [hzm _ (by omega)]; simp [y₁], by simpa [Nat.add_assoc] using hze⟩
    · rw [holdsList_cons_iff]
      refine ⟨by rw [hzm _ (by omega), hy₁m _ (by omega), hla], by simpa [Nat.add_assoc] using hzd⟩
    · rw [hzs, List.all_cons, Bool.and_assoc]

/-- **Start the literal odometer** on a choice `t` of `s` clause addresses in `D`: `E` holds their
first literal addresses, `sat = 1` exactly when none of the clauses is empty, `D` is kept, and the
memory outside `E` is unchanged, within `12 s + 4` instructions. -/
theorem initE_spec (t : List ℕ) (y : Data 32) (hf : ImpFrame w φ τ x b C Tb s Db y)
    (ht : t ∈ (List.replicate s (clauseAddrs C φ)).sections) (hl : HoldsList Db t y.mem) :
    ∃ z, ExecWithin w initE y z (12 * s + 4) ∧ ImpFrame w φ τ x b C Tb s Db z ∧
      (∀ a, a < Db + s ∨ Db + 2 * s ≤ a → z.mem a = y.mem a) ∧
      HoldsList (Db + s) (t.map (· + 1)) z.mem ∧
      z.regs sat = (t.all fun a => (clauseOf C φ a).length != 0).toNat := by
  obtain ⟨hlen, hA⟩ := mem_sections_replicate.mp ht
  have hs₀ := ExecWithin.copy (B := .standard) (w := w) (d := sat) (s := one) (x := y)
  rw [hf.one_eq] at hs₀
  have hj₀ := ExecWithin.copy (B := .standard) (w := w) (d := jR) (s := zero) (x := y.set sat 1)
  rw [show (y.set sat 1).regs zero = 0 by simp +decide [hf.zero_eq]] at hj₀
  obtain ⟨z, hz, hzf, hzm, hze, -, hzs⟩ := initELoop_spec t true ((y.set sat 1).set jR 0)
    ((hf.set (by decide) 1).set (by decide) 0) (by simp [hlen]) hA (by simpa using hl)
    (by simp +decide)
  simp only [Data.set_regs, Function.update_self, Nat.add_zero, Bool.true_and] at hzm hze hzs
  exact ⟨z, (hs₀.seq (hj₀.seq hz)).mono (by rw [hlen]; omega), hzf,
    fun a ha => by rw [hzm a ha]; rfl, hze, hzs⟩

/-- **The carry loop of the literal odometer** from entry `j`, on clause addresses `du` in
`D[j], …` and a choice `eu` of one literal address of each in `E[j], …`: if the odometer step on
`eu` has a result, `E[j], …` holds it and `jR = s + 1`; if not, `jR = s`. The memory outside
`E[j], …, E[s - 1]` is unchanged. -/
theorem incELoop_spec : ∀ (du eu : List ℕ) (y : Data 32), ImpFrame w φ τ x b C Tb s Db y →
    y.regs jR + du.length = s → (∀ a ∈ du, a ∈ clauseAddrs C φ) →
    HoldsList (Db + y.regs jR) du y.mem → HoldsList (Db + s + y.regs jR) eu y.mem →
    eu ∈ (du.map (litAddrs C φ)).sections →
    ∃ z, ExecWithin w incELoop y z (14 * du.length + 2) ∧ ImpFrame w φ τ x b C Tb s Db z ∧
      (∀ a, a < Db + s + y.regs jR ∨ Db + 2 * s ≤ a → z.mem a = y.mem a) ∧
      (∀ eu', nextSection (du.map (litAddrs C φ)) eu = some eu' →
        z.regs jR = s + 1 ∧ HoldsList (Db + s + y.regs jR) eu' z.mem) ∧
      (nextSection (du.map (litAddrs C φ)) eu = none → z.regs jR = s)
  | [], eu, y, hf, hd, _, _, _, he => by
    simp only [List.length_nil, Nat.add_zero] at hd
    simp only [List.map_nil, List.sections, List.mem_singleton] at he
    subst he
    have hc : ¬(Cond.lt jR sReg).Holds y := by simp [Cond.holds_lt, hf.s_eq]; omega
    refine ⟨y, (ExecWithin.loop_exit hc).mono (by omega), hf, fun _ _ => rfl, ?_, ?_⟩
    · intro eu' h; simp [nextSection] at h
    · intro _; exact hd
  | a :: du, eu, y, hf, hd, hA, hl, hle, he => by
    obtain ⟨j, hj⟩ : ∃ j, y.regs jR = j := ⟨_, rfl⟩
    rw [hj] at hd hl hle ⊢
    simp only [List.length_cons] at hd
    simp only [List.map_cons, List.sections, List.mem_flatMap, List.mem_map] at he
    obtain ⟨eu₀, he₀, e, hea, rfl⟩ := he
    have haA : a ∈ clauseAddrs C φ := hA a (by simp)
    have hb := bounds_of_mem_clauseAddrs haA
    have hc : (Cond.lt jR sReg).Holds y := by simp [Cond.holds_lt, hf.s_eq, hj]; omega
    obtain ⟨hla, hlu⟩ := holdsList_cons_iff.mp hl
    obtain ⟨hle₀, hleu⟩ := holdsList_cons_iff.mp hle
    have hlen : y.mem a = (clauseOf C φ a).length := mem_clauseAddr hf.clauses haA
    set len := (clauseOf C φ a).length with hlen_def
    have hea' : a + 1 ≤ e ∧ e < a + 1 + len := by
      simpa [litAddrs, List.mem_range'_1] using hea
    have hf1 : Fits w (Db + s + j) := hf.fits_le (by omega)
    have hf2 : Fits w (e + 1) := hf.fits_le (by have := hf.clauses_le; omega)
    have hf3 : Fits w (Db + j) := hf.fits_le (by omega)
    have hf4 : Fits w (a + 1) := hf.fits_le (by have := hf.clauses_le; omega)
    have hf5 : Fits w (a + 1 + len) := hf.fits_le (by have := hf.clauses_le; omega)
    have hsucc : succIn (litAddrs C φ a) e = if e + 1 = a + 1 + len then none else some (e + 1) :=
      succIn_range' hea
    have hhead : (litAddrs C φ a).headD 0 = a + 1 := by
      simp only [litAddrs]
      rcases hlz : len with _ | k
      · omega
      · rw [← hlen_def, hlz, List.range'_succ]; rfl
    by_cases hend : e + 1 = a + 1 + len
    · -- carry
      let y₁ := (((((((((y.set adr (Db + s + j)).set ev e).set ev (e + 1)).set dv (Db + j)).set
        dv a).set lenR len).set stop (a + 1)).set stop (a + 1 + len)).set ev (a + 1)).write
        (Db + s + j) (a + 1) |>.set jR (j + 1)
      have hf6 : Fits w (j + 1) := hf.fits_le (by omega)
      have hrun : ExecWithin w incEBody y y₁ 12 := by
        ram_eval [y₁, incEBody, hf.eBase_eq, hf.dBase_eq, hj, hle₀, hla, hlen, hf.one_eq,
          eq_true hend, hf1, hf2, hf3, hf4, hf5, hf6]
      have hy₁ : ImpFrame w φ τ x b C Tb s Db y₁ :=
        (((((((((((hf.set (by decide) _).set (by decide) _).set (by decide) _).set (by decide)
          _).set (by decide) _).set (by decide) _).set (by decide) _).set (by decide) _).set
          (by decide) _).write (by omega) _).set (by decide) _)
      have hj₁ : y₁.regs jR = j + 1 := by simp [y₁]
      have hy₁m : ∀ a', a' ≠ Db + s + j → y₁.mem a' = y.mem a' := fun a' ha' => by
        simp only [y₁, Data.set_mem, Data.write_mem]; rw [Function.update_of_ne ha']
      obtain ⟨z, hz, hzf, hzm, hzs, hzn⟩ := incELoop_spec du eu₀ y₁ hy₁ (by rw [hj₁]; omega)
        (fun a' h => hA a' (by simp [h]))
        (by rw [hj₁]; exact hlu.frame fun a' h1 h2 => hy₁m a' (by omega))
        (by rw [hj₁]; exact hleu.frame fun a' h1 h2 => hy₁m a' (by omega)) he₀
      rw [hj₁] at hzm hzs
      have hzj : z.mem (Db + s + j) = a + 1 := by
        rw [hzm _ (by omega)]; simp [y₁]
      refine ⟨z, (ExecWithin.loop_iter hc hrun hz).mono (by simp only [List.length_cons]; omega),
        hzf, fun a' ha' => by rw [hzm a' (by omega), hy₁m a' (by omega)], ?_, ?_⟩
      · intro eu' h
        simp only [List.map_cons, nextSection, hsucc, hend, ↓reduceIte, hhead] at h
        obtain ⟨eu'', hu'', rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨hzj', hzl⟩ := hzs eu'' hu''
        exact ⟨hzj', holdsList_cons_iff.mpr ⟨hzj, by simpa [Nat.add_assoc] using hzl⟩⟩
      · intro h
        simp only [List.map_cons, nextSection, hsucc, hend, ↓reduceIte,
          Option.map_eq_none_iff] at h
        exact hzn h
    · -- no carry
      have hf6 : Fits w (s + 1) := hf.fits_le (by omega)
      let y₁ := ((((((((y.set adr (Db + s + j)).set ev e).set ev (e + 1)).set dv (Db + j)).set
        dv a).set lenR len).set stop (a + 1)).set stop (a + 1 + len)).write (Db + s + j)
        (e + 1) |>.set jR (s + 1)
      have hrun : ExecWithin w incEBody y y₁ 12 := by
        ram_eval [y₁, incEBody, hf.eBase_eq, hf.dBase_eq, hj, hle₀, hla, hlen, hf.one_eq,
          eq_false hend, hf.s_eq, hf1, hf2, hf3, hf4, hf5, hf6]
      have hy₁ : ImpFrame w φ τ x b C Tb s Db y₁ :=
        ((((((((((hf.set (by decide) _).set (by decide) _).set (by decide) _).set (by decide)
          _).set (by decide) _).set (by decide) _).set (by decide) _).set (by decide) _).write
          (by omega) _).set (by decide) _)
      have hc₁ : ¬(Cond.lt jR sReg).Holds y₁ := by
        simp +decide [Cond.holds_lt, y₁, hf.s_eq]
      refine ⟨y₁, (ExecWithin.loop_iter hc hrun (ExecWithin.loop_exit hc₁)).mono
        (by simp only [List.length_cons]; omega), hy₁, fun a' ha' => by
          simp only [y₁, Data.set_mem, Data.write_mem]; rw [Function.update_of_ne (by omega)],
        ?_, ?_⟩
      · intro eu' h
        simp only [List.map_cons, nextSection, hsucc, hend, ↓reduceIte, Option.some.injEq] at h
        subst h
        refine ⟨by simp [y₁], holdsList_cons_iff.mpr ⟨by simp [y₁], ?_⟩⟩
        exact hleu.frame fun a' h1 h2 => by
          simp only [y₁, Data.set_mem, Data.write_mem]; rw [Function.update_of_ne (by omega)]
      · intro h
        simp only [List.map_cons, nextSection, hsucc, hend, ↓reduceIte, reduceCtorEq] at h

/-- **Step the literal odometer** on clause addresses `t` in `D` and a choice `e` of one literal
address of each in `E`: if the odometer step on `e` has a result, `E` holds it and `contI = 1`; if
not, `contI = 0`. The memory outside `E` is unchanged, within `14 s + 4` instructions. -/
theorem incE_spec (t e : List ℕ) (y : Data 32) (hf : ImpFrame w φ τ x b C Tb s Db y)
    (ht : t ∈ (List.replicate s (clauseAddrs C φ)).sections) (hl : HoldsList Db t y.mem)
    (hle : HoldsList (Db + s) e y.mem) (he : e ∈ (t.map (litAddrs C φ)).sections) :
    ∃ z, ExecWithin w incE y z (14 * s + 4) ∧ ImpFrame w φ τ x b C Tb s Db z ∧
      (∀ a, a < Db + s ∨ Db + 2 * s ≤ a → z.mem a = y.mem a) ∧
      (∀ e', nextSection (t.map (litAddrs C φ)) e = some e' →
        z.regs contI = 1 ∧ HoldsList (Db + s) e' z.mem) ∧
      (nextSection (t.map (litAddrs C φ)) e = none → z.regs contI = 0) := by
  obtain ⟨hlen, hA⟩ := mem_sections_replicate.mp ht
  have h₀ := ExecWithin.copy (B := .standard) (w := w) (d := jR) (s := zero) (x := y)
  rw [hf.zero_eq] at h₀
  obtain ⟨z, hz, hzf, hzm, hzs, hzn⟩ := incELoop_spec t e (y.set jR 0) (hf.set (by decide) 0)
    (by simp [hlen]) hA (by simpa using hl) (by simpa using hle) he
  simp only [Data.set_regs, Function.update_self, Nat.add_zero] at hzm hzs hzn
  have hjz : z.regs jR ≤ s + 1 := by
    rcases hns : nextSection (t.map (litAddrs C φ)) e with _ | e'
    · rw [hzn hns]; omega
    · rw [(hzs e' hns).1]
  have hfz : Fits w (z.regs jR - z.regs sReg) := hzf.fits_le (by rw [hzf.s_eq]; omega)
  have hout := ExecWithin.bin (w := w) (f := .sub) (d := contI) (i := jR) (j := sReg) (x := z) hfz
  refine ⟨_, (h₀.seq (hz.seq hout)).mono (by rw [hlen]; omega), hzf.set (by decide) _,
    fun a ha => by rw [Data.set_mem, hzm a ha]; rfl, ?_, ?_⟩
  · intro e' h
    obtain ⟨hj, hzl⟩ := hzs e' h
    exact ⟨by simp [BinOp.eval, hj, hzf.s_eq], hzl⟩
  · intro h
    simp [BinOp.eval, hzn h, hzf.s_eq]

end LiteralOdometer

/-! ### The compatibility test -/

/-- Compare the literal code at `E[k]` with `auxR`, the code of the complementary literal, and
clear `sat` if they are equal. -/
def pairBody : Code .standard 32 := ram[
  adr ← eBase + kR; ev ← *adr; ev ← *ev; if ev = auxR then [ sat ← zero ] else [ sat ← sat ];
  kR ← kR + one ]

/-- Compare the literal codes at `E[k], …, E[s - 1]` with `auxR`. -/
def pairLoop : Code .standard 32 := .loop (.lt kR sReg) pairBody

/-- Read the literal code at `E[j]` and clear `sat` if the literal is falsified: on `x` when its
sign is `b`, and elsewhere when the partial assignment sets its variable to the other sign. -/
def litHead : Code .standard 32 := ram[
  adr ← eBase + jR; dv ← *adr; litR ← *dv; auxR ← litR >>> one; sgnR ← litR &&& one;
  if auxR = xReg then [ if sgnR = bReg then [ sat ← zero ] else [ sat ← sat ] ]
  else [ adr ← tBase + auxR; lenR ← *adr; stop ← one - sgnR;
    if lenR = stop then [ sat ← zero ] else [ sat ← sat ] ] ]

/-- Test the literal at `E[j]`: it is not falsified, and no literal of `E` is its complement. -/
def litTest : Code .standard 32 := ram[
  ⟪litHead⟫; auxR ← litR ^^^ one; kR ← zero; ⟪pairLoop⟫; jR ← jR + one ]

/-- Test the literals at `E[j], …, E[s - 1]`. -/
def goodLoop : Code .standard 32 := .loop (.lt jR sReg) litTest

/-- **The compatibility test**: `sat = 1` exactly when the literals at the addresses in `E` are
compatible with the partial assignment with `x` set to `!b`. -/
def goodTest : Code .standard 32 := ram[ sat ← one; jR ← zero; ⟪goodLoop⟫ ]

/-- The code of the complementary literal stays below `2 n`. -/
theorem xor_one_lt {c m : ℕ} (h : c < 2 * m) : c ^^^ 1 < 2 * m := by
  rcases Nat.even_or_odd c with he | ho
  · rw [Nat.xor_one_of_even he]
    obtain ⟨k, rfl⟩ := he
    omega
  · rw [Nat.xor_one_of_odd ho]
    omega

section Compat

variable {w : ℕ} {φ : CNF (Fin n)} {τ : Fin n → Option Bool} {x : Fin n} {b : Bool}
  {C Tb s Db : ℕ}

/-- **The comparison loop** from entry `k`, on literal addresses `u` in `E[k], …`: `sat` is
cleared if one of their codes is `auxR`. The memory is unchanged. -/
theorem pairLoop_spec (cc : ℕ) : ∀ (u : List ℕ) (f : Bool) (y : Data 32),
    ImpFrame w φ τ x b C Tb s Db y → y.regs kR + u.length = s →
    HoldsList (Db + s + y.regs kR) u y.mem → y.regs sat = f.toNat → y.regs auxR = cc →
    ∃ z, ExecWithin w pairLoop y z (9 * u.length + 2) ∧ z.mem = y.mem ∧
      ImpFrame w φ τ x b C Tb s Db z ∧
      z.regs sat = (f && (u.map y.mem).all (· != cc)).toNat
  | [], f, y, hf, hd, _, hs, _ => by
    simp only [List.length_nil, Nat.add_zero] at hd
    have hc : ¬(Cond.lt kR sReg).Holds y := by simp [Cond.holds_lt, hf.s_eq]; omega
    exact ⟨y, (ExecWithin.loop_exit hc).mono (by omega), rfl, hf, by simpa using hs⟩
  | e :: u, f, y, hf, hd, hl, hs, hcc => by
    obtain ⟨k, hk⟩ : ∃ k, y.regs kR = k := ⟨_, rfl⟩
    rw [hk] at hd hl
    simp only [List.length_cons] at hd
    have hc : (Cond.lt kR sReg).Holds y := by simp [Cond.holds_lt, hf.s_eq, hk]; omega
    obtain ⟨hle, hlu⟩ := holdsList_cons_iff.mp hl
    have hf1 : Fits w (Db + s + k) := hf.fits_le (by omega)
    have hf2 : Fits w (k + 1) := hf.fits_le (by omega)
    let y₁ := ((((y.set adr (Db + s + k)).set ev e).set ev (y.mem e)).set sat
      (f && y.mem e != cc).toNat).set kR (k + 1)
    have hrun : ExecWithin w pairBody y y₁ 7 := by
      by_cases he : y.mem e = cc
      · have h0 : (f && y.mem e != cc).toNat = 0 := by simp [he]
        ram_eval [y₁, pairBody, hf.eBase_eq, hk, hle, hcc, eq_true he, hf.zero_eq, h0,
          hf.one_eq, hf1, hf2]
      · have h1 : (f && y.mem e != cc).toNat = f.toNat := by
          rw [show (y.mem e != cc) = true from bne_iff_ne.mpr he, Bool.and_true]
        ram_eval [y₁, pairBody, hf.eBase_eq, hk, hle, hcc, eq_false he, hf.zero_eq, hs, h1,
          hf.one_eq, hf1, hf2]
    have hy₁ : ImpFrame w φ τ x b C Tb s Db y₁ :=
      ((((hf.set (by decide) _).set (by decide) _).set (by decide) _).set (by decide) _).set
        (by decide) _
    obtain ⟨z, hz, hzm, hzf, hzs⟩ := pairLoop_spec cc u (f && y.mem e != cc) y₁ hy₁
      (by simp [y₁]; omega) (by simpa [y₁, Nat.add_assoc] using hlu) (by simp +decide [y₁])
      (by simp +decide [y₁, hcc])
    refine ⟨z, (ExecWithin.loop_iter hc hrun hz).mono (by simp only [List.length_cons]; omega),
      by rw [hzm]; rfl, hzf, ?_⟩
    rw [hzs]
    simp only [y₁, Data.set_mem, List.map_cons, List.all_cons, Bool.and_assoc]

/-- **The test of one literal** at `E[j]`, with code `c`: `sat` is cleared if the literal is
falsified or the code of its complement occurs in `E`. The memory is unchanged. -/
theorem litTest_spec (El : List ℕ) (y : Data 32) (hf : ImpFrame w φ τ x b C Tb s Db y)
    (hj : y.regs jR < s) (hEl : HoldsList (Db + s) El y.mem) (hlen : El.length = s)
    (hcodes : ∀ p ∈ El, y.mem p < 2 * n) (f : Bool) (hs : y.regs sat = f.toNat) :
    ∃ z, ExecWithin w litTest y z (9 * s + 20) ∧ z.mem = y.mem ∧
      ImpFrame w φ τ x b C Tb s Db z ∧ z.regs jR = y.regs jR + 1 ∧
      z.regs sat = (f && (litFine (fun v => y.mem (Tb + v)) x b.toNat
        (y.mem (El[y.regs jR]'(by omega))) &&
        (El.map y.mem).all (· != y.mem (El[y.regs jR]'(by omega)) ^^^ 1))).toNat := by
  obtain ⟨j, hjj⟩ : ∃ j, y.regs jR = j := ⟨_, rfl⟩
  simp only [hjj] at hj ⊢
  set p := El[j]'(by omega) with hp
  have hpE : y.mem (Db + s + j) = p := hEl.get j (by omega)
  set c := y.mem p with hc
  have hcl : c < 2 * n := hcodes p (List.getElem_mem _)
  have hvar : c >>> 1 < n := by rw [Nat.shiftRight_eq_div_pow]; omega
  have hsgn : c &&& 1 ≤ 1 := Nat.and_le_right
  have hf1 : Fits w (Db + s + j) := hf.fits_le (by omega)
  have hf2 : Fits w (c >>> 1) := hf.fits_le (by have := hf.stored_le; omega)
  have hf3 : Fits w (c &&& 1) := hf.fits_le (by omega)
  have hf4 : Fits w (Tb + (c >>> 1)) := hf.fits_le (by have := hf.stored_le; omega)
  have hf5 : Fits w (1 - (c &&& 1)) := hf.fits_le (by omega)
  set F := (f && litFine (fun v => y.mem (Tb + v)) x b.toNat c).toNat with hF
  -- the head
  obtain ⟨y₁, hy₁, hy₁f, hy₁m, hy₁s, hy₁l, hy₁j⟩ : ∃ y₁, ExecWithin w litHead y y₁ 13 ∧
      ImpFrame w φ τ x b C Tb s Db y₁ ∧ y₁.mem = y.mem ∧ y₁.regs sat = F ∧ y₁.regs litR = c ∧
      y₁.regs jR = j := by
    have hbase := (((((hf.set (i := adr) (by decide) (Db + s + j)).set (i := dv) (by decide)
      p).set (i := litR) (by decide) c).set (i := auxR) (by decide) (c >>> 1)).set (i := sgnR)
      (by decide) (c &&& 1))
    by_cases hx : c >>> 1 = x.val
    · by_cases hb : c &&& 1 = b.toNat
      · have h0 : F = 0 := by simp [hF, litFine, hx, hb]
        refine ⟨_, ?_, hbase.set (i := sat) (by decide) 0, rfl, by simp +decide [h0],
          by simp +decide,
          by simp +decide [hjj]⟩
        ram_eval [litHead, hf.eBase_eq, hjj, hpE, ← hc, hf.one_eq, hf.x_eq, hf.b_eq, eq_true hx,
          eq_true hb, hf.zero_eq, hf1, hf2, hf3]
      · have h1 : F = f.toNat := by
          simp only [hF, litFine, hx, ↓reduceIte]
          rw [show (c &&& 1 != b.toNat) = true from bne_iff_ne.mpr hb, Bool.and_true]
        refine ⟨_, ?_, hbase.set (i := sat) (by decide) f.toNat, rfl, by simp +decide [h1],
          by simp +decide, by simp +decide [hjj]⟩
        ram_eval [litHead, hf.eBase_eq, hjj, hpE, ← hc, hf.one_eq, hf.x_eq, hf.b_eq, eq_true hx,
          eq_false hb, hs, hf1, hf2, hf3]
    · have hbase' := ((hbase.set (i := adr) (by decide) (Tb + (c >>> 1))).set (i := lenR)
        (by decide) (y.mem (Tb + (c >>> 1)))).set (i := stop) (by decide) (1 - (c &&& 1))
      by_cases ht : y.mem (Tb + (c >>> 1)) = 1 - (c &&& 1)
      · have h0 : F = 0 := by simp [hF, litFine, hx, ht]
        refine ⟨_, ?_, hbase'.set (i := sat) (by decide) 0, rfl, by simp +decide [h0],
          by simp +decide,
          by simp +decide [hjj]⟩
        ram_eval [litHead, hf.eBase_eq, hjj, hpE, ← hc, hf.one_eq, hf.x_eq, hf.tBase_eq,
          eq_false hx,
          eq_true ht, hf.zero_eq, hf1, hf2, hf3, hf4, hf5]
      · have h1 : F = f.toNat := by
          simp only [hF, litFine, hx, ↓reduceIte]
          rw [show (y.mem (Tb + (c >>> 1)) != 1 - (c &&& 1)) = true from bne_iff_ne.mpr ht,
            Bool.and_true]
        refine ⟨_, ?_, hbase'.set (i := sat) (by decide) f.toNat, rfl, by simp +decide [h1],
          by simp +decide, by simp +decide [hjj]⟩
        ram_eval [litHead, hf.eBase_eq, hjj, hpE, ← hc, hf.one_eq, hf.x_eq, hf.tBase_eq,
          eq_false hx,
          eq_false ht, hs, hf1, hf2, hf3, hf4, hf5]
  -- the complement and the comparisons
  have hf6 : Fits w (c ^^^ 1) := hf.fits_le (by have := xor_one_lt hcl; have := hf.codes_le; omega)
  let y₂ := (y₁.set auxR (c ^^^ 1)).set kR 0
  have h₂a : ExecWithin w (ram[ auxR ← litR ^^^ one ] : Code .standard 32) y₁
      (y₁.set auxR (c ^^^ 1)) 1 := by
    ram_eval [hy₁l, hy₁f.one_eq, hf6]
  have h₂b : ExecWithin w (ram[ kR ← zero ] : Code .standard 32) (y₁.set auxR (c ^^^ 1)) y₂ 1 := by
    ram_eval [y₂, hy₁f.zero_eq]
  have hy₂ : ImpFrame w φ τ x b C Tb s Db y₂ := (hy₁f.set (by decide) _).set (by decide) _
  obtain ⟨z₃, hz₃, hz₃m, hz₃f, hz₃s⟩ := pairLoop_spec (c ^^^ 1) El (F == 1) y₂ hy₂
    (by simp +decide [y₂, hlen]) (by simpa [y₂, hy₁m] using hEl)
    (by
      simp +decide only [y₂, Data.set_regs, Function.update_of_ne, ne_eq, hy₁s, hF]
      cases (f && litFine (fun v => y.mem (Tb + v)) x b.toNat c) <;> rfl)
    (by simp +decide [y₂])
  have hj₃ : z₃.regs jR = j := by rw [hz₃.regs_eq (by decide)]; simp +decide [y₂, hy₁j]
  have hf7 : Fits w (j + 1) := hf.fits_le (by omega)
  have h₄ := ExecWithin.bin (w := w) (f := .add) (d := jR) (i := jR) (j := one) (x := z₃)
    (by rw [hj₃, hz₃f.one_eq]; exact hf7)
  refine ⟨_, (hy₁.seq (h₂a.seq (h₂b.seq (hz₃.seq h₄)))).mono (by omega), ?_,
    hz₃f.set (i := jR) (by decide) _, ?_, ?_⟩
  · rw [Data.set_mem, hz₃m]; simp [y₂, hy₁m]
  · simp [BinOp.eval, hj₃, hz₃f.one_eq]
  · rw [Data.set_regs, Function.update_of_ne (by decide), hz₃s]
    simp only [y₂, Data.set_mem, hy₁m, hF, ← Bool.and_assoc, List.all_map]
    cases (f && litFine (fun v => y.mem (Tb + v)) x b.toNat c) <;> rfl

end Compat

section Good

variable {w : ℕ} {φ : CNF (Fin n)} {τ : Fin n → Option Bool} {x : Fin n} {b : Bool}
  {C Tb s Db : ℕ}

/-- **The loop of the compatibility test** from entry `j`, on the literal addresses
`u = E[j], …` of the full list `El` in `E`. The memory is unchanged. -/
theorem goodLoop_spec (El : List ℕ) (hlen : El.length = s) : ∀ (u : List ℕ) (f : Bool)
    (y : Data 32), ImpFrame w φ τ x b C Tb s Db y → u = El.drop (y.regs jR) →
    y.regs jR ≤ s → HoldsList (Db + s) El y.mem → (∀ p ∈ El, y.mem p < 2 * n) →
    y.regs sat = f.toNat →
    ∃ z, ExecWithin w goodLoop y z (u.length * (9 * s + 22) + 2) ∧ z.mem = y.mem ∧
      ImpFrame w φ τ x b C Tb s Db z ∧
      z.regs sat = (f && u.all fun p => litFine (fun v => y.mem (Tb + v)) x b.toNat (y.mem p) &&
        (El.map y.mem).all (· != y.mem p ^^^ 1)).toNat
  | [], f, y, hf, hu, hj, _, _, hs => by
    have hj' : s ≤ y.regs jR := by
      have := congrArg List.length hu; simp at this; omega
    have hc : ¬(Cond.lt jR sReg).Holds y := by simp [Cond.holds_lt, hf.s_eq]; omega
    exact ⟨y, (ExecWithin.loop_exit hc).mono (by omega), rfl, hf, by simpa using hs⟩
  | p :: u, f, y, hf, hu, hj, hEl, hcodes, hs => by
    have hjs : y.regs jR < s := by
      have := congrArg List.length hu; simp at this; omega
    rw [List.drop_eq_getElem_cons (by omega), List.cons.injEq] at hu
    obtain ⟨hp, hu⟩ := hu
    have hc : (Cond.lt jR sReg).Holds y := by simp [Cond.holds_lt, hf.s_eq]; omega
    obtain ⟨z₁, hz₁, hz₁m, hz₁f, hz₁j, hz₁s⟩ := litTest_spec El y hf hjs hEl hlen hcodes f hs
    obtain ⟨z, hz, hzm, hzf, hzs⟩ := goodLoop_spec El hlen u _ z₁ hz₁f
      (by rw [hz₁j]; exact hu) (by omega) (by rw [hz₁m]; exact hEl)
      (by rw [hz₁m]; exact hcodes) hz₁s
    refine ⟨z, (ExecWithin.loop_iter hc hz₁ hz).mono (by simp only [List.length_cons]; nlinarith),
      by rw [hzm, hz₁m], hzf, ?_⟩
    rw [hzs, hz₁m, ← hp, List.all_cons, Bool.and_assoc]

/-- The time of the compatibility test on `s` literals. -/
def goodTime (s : ℕ) : ℕ := s * (9 * s + 22) + 4

/-- **The compatibility test**: `sat = 1` exactly when the literal codes at the addresses `El` in
`E` are compatible (`compatCodes`), within `goodTime s` instructions. The memory is unchanged. -/
theorem goodTest_spec (El : List ℕ) (hlen : El.length = s) (y : Data 32)
    (hf : ImpFrame w φ τ x b C Tb s Db y) (hEl : HoldsList (Db + s) El y.mem)
    (hcodes : ∀ p ∈ El, y.mem p < 2 * n) :
    ∃ z, ExecWithin w goodTest y z (goodTime s) ∧ z.mem = y.mem ∧
      ImpFrame w φ τ x b C Tb s Db z ∧
      z.regs sat = (compatCodes (fun v => y.mem (Tb + v)) x b.toNat (El.map y.mem)).toNat := by
  have hs₀ := ExecWithin.copy (B := .standard) (w := w) (d := sat) (s := one) (x := y)
  rw [hf.one_eq] at hs₀
  have hj₀ := ExecWithin.copy (B := .standard) (w := w) (d := jR) (s := zero) (x := y.set sat 1)
  rw [show (y.set sat 1).regs zero = 0 by simp +decide [hf.zero_eq]] at hj₀
  obtain ⟨z, hz, hzm, hzf, hzs⟩ := goodLoop_spec El hlen El true ((y.set sat 1).set jR 0)
    ((hf.set (by decide) 1).set (by decide) 0) (by simp) (by simp) (by simpa using hEl)
    (by simpa using hcodes) (by simp +decide)
  refine ⟨z, (hs₀.seq (hj₀.seq hz)).mono (by simp only [goodTime, hlen]; omega),
    by rw [hzm]; rfl, hzf, ?_⟩
  rw [hzs]
  simp only [Data.set_mem, Bool.true_and, compatCodes, List.all_map, Function.comp_def]

end Good

/-! ### Sections: shape and size -/

/-- With an empty list among `L`, there is no section. -/
theorem sections_eq_nil_of_nil_mem {α : Type*} : ∀ {L : List (List α)}, [] ∈ L → L.sections = []
  | [], h => by simp at h
  | l :: L, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · simp [sections_eq_nil_of_nil_mem h]

/-- Without an empty list among `L`, the first section picks the first entry of every list. -/
theorem sections_eq_cons_headD {α : Type*} (d : α) : ∀ {L : List (List α)},
    (∀ l ∈ L, l ≠ []) → ∃ xs, L.sections = L.map (·.headD d) :: xs
  | [], _ => ⟨[], rfl⟩
  | l :: L, h => by
    obtain ⟨xs, hxs⟩ := sections_eq_cons_headD d (L := L) fun l' hl' =>
      h l' (List.mem_cons_of_mem _ hl')
    obtain ⟨a, l', rfl⟩ := List.exists_cons_of_ne_nil (h l (by simp))
    refine ⟨l'.map (· :: L.map (·.headD d)) ++ xs.flatMap (fun t => (a :: l').map (· :: t)), ?_⟩
    simp only [List.sections, hxs, List.flatMap_cons, List.map_cons, List.cons_append,
      List.headD_cons]

/-- The number of sections of lists of length at most `m`. -/
theorem length_sections_le {α : Type*} {m : ℕ} : ∀ {L : List (List α)},
    (∀ l ∈ L, l.length ≤ m) → L.sections.length ≤ m ^ L.length
  | [], _ => by simp
  | l :: L, h => by
    have ih := length_sections_le (L := L) fun l' hl' => h l' (by simp [hl'])
    simp only [List.sections, List.length_flatMap, List.length_map, List.length_cons, pow_succ]
    rw [List.map_const', List.sum_replicate, smul_eq_mul]
    have := h l (by simp)
    calc L.sections.length * l.length ≤ m ^ L.length * m := Nat.mul_le_mul ih this

/-- `List.all` depends only on the values of the test on the list. -/
theorem all_congr_of_mem {α : Type*} {l : List α} {f g : α → Bool} (h : ∀ a ∈ l, f a = g a) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons, h a (by simp), ih fun b hb => h b (by simp [hb])]

/-- Compatibility through codes reads only the codes and the words of their variables. -/
theorem compatCodes_congr {m₁ m₂ : ℕ → ℕ} {Tb x b : ℕ} {El : List ℕ}
    (hE : ∀ p ∈ El, m₁ p = m₂ p) (hc : ∀ p ∈ El, m₁ p < 2 * n)
    (hτ : ∀ v < n, m₁ (Tb + v) = m₂ (Tb + v)) :
    compatCodes (fun v => m₁ (Tb + v)) x b (El.map m₁) =
      compatCodes (fun v => m₂ (Tb + v)) x b (El.map m₂) := by
  rw [← List.map_congr_left hE]
  unfold compatCodes
  refine all_congr_of_mem fun c hc' => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc'
  have hv : m₁ p >>> 1 < n := by rw [Nat.shiftRight_eq_div_pow]; have := hc p hp; omega
  simp only [litFine, hτ _ hv]

/-- The literal addresses of a clause address hold literal codes, below `2 n`. -/
theorem mem_litAddr_lt {mem : ℕ → ℕ} {C : ℕ} {φ : CNF (Fin n)}
    (hφ : HoldsList C (encodeClauses φ) mem) {a : ℕ} (ha : a ∈ clauseAddrs C φ) {p : ℕ}
    (hp : p ∈ litAddrs C φ a) : mem p < 2 * n := by
  have hc := holdsList_clauseOf hφ ha
  simp only [litAddrs, List.mem_range'_1] at hp
  obtain ⟨i, rfl⟩ : ∃ i, p = a + 1 + i := ⟨p - (a + 1), by omega⟩
  have := hc.get (i + 1) (by simp [encodeClause]; omega)
  rw [show a + (i + 1) = a + 1 + i by omega] at this
  rw [this]
  simp only [encodeClause, List.getElem_cons_succ, List.getElem_map]
  exact litCode_lt _

/-- The literal addresses of a clause address lie in the encoding of the clauses. -/
theorem lt_of_mem_litAddrs {C : ℕ} {φ : CNF (Fin n)} {a : ℕ} (ha : a ∈ clauseAddrs C φ) {p : ℕ}
    (hp : p ∈ litAddrs C φ a) : p < C + (encodeClauses φ).length := by
  have := bounds_of_mem_clauseAddrs ha
  simp only [litAddrs, List.mem_range'_1] at hp
  omega

/-- The literal addresses of a clause are duplicate-free. -/
theorem litAddrs_nodup (C : ℕ) (φ : CNF (Fin n)) (a : ℕ) : (litAddrs C φ a).Nodup :=
  List.nodup_range'

/-- A clause has at most as many literals as the encoding has words. -/
theorem length_litAddrs_le {C : ℕ} {φ : CNF (Fin n)} {a : ℕ} (ha : a ∈ clauseAddrs C φ) :
    (litAddrs C φ a).length ≤ (encodeClauses φ).length := by
  have := bounds_of_mem_clauseAddrs ha
  simp only [litAddrs, List.length_range']
  omega

/-- There are at most as many clauses as the encoding has words. -/
theorem length_clauseAddrs_le : ∀ (a : ℕ) (φ : CNF (Fin n)),
    (clauseAddrs a φ).length ≤ (encodeClauses φ).length
  | _, [] => by simp [clauseAddrs]
  | a, c :: φ => by
    have := length_clauseAddrs_le (a + 1 + c.length) φ
    simp only [clauseAddrs, List.length_cons, encodeClauses_cons, List.length_append,
      length_encodeClause]
    omega

/-! ### The search over choices of literals -/

/-- One step of the literal search: test the current choice, and stop if it is compatible;
otherwise step the odometer. -/
def innerBody : Code .standard 32 := ram[
  ⟪goodTest⟫; if sat = one then [ contI ← zero ] else [ ⟪incE⟫ ] ]

/-- The literal search from the current choice on. -/
def innerLoop : Code .standard 32 := .loop (.lt zero contI) innerBody

/-- **The literal search**: `sat = 1` exactly when some choice of one literal address from each
clause in `D` is compatible. -/
def innerSearch : Code .standard 32 := ram[
  ⟪initE⟫; if sat = one then [ contI ← one; ⟪innerLoop⟫ ] else [ sat ← sat ] ]

/-- The time of one step of the literal search. -/
def innerIter (s : ℕ) : ℕ := goodTime s + 14 * s + 9

/-- The time of the literal search, with at most `E ^ s` choices of literals. -/
def innerTime (s E : ℕ) : ℕ := 12 * s + 8 + E ^ s * innerIter s

section Inner

variable {w : ℕ} {φ : CNF (Fin n)} {τ : Fin n → Option Bool} {x : Fin n} {b : Bool}
  {C Tb s Db : ℕ}

/-- The test of the literal search, on the memory `m`. -/
def litOk (m : ℕ → ℕ) (Tb : ℕ) (x : Fin n) (b : Bool) (e : List ℕ) : Bool :=
  compatCodes (fun v => m (Tb + v)) x b.toNat (e.map m)

/-- **The loop of the literal search**, on the clause addresses `t` in `D`, from the choice `e`
in `E`, followed by the choices `xs`: `sat = 1` exactly when one of them is compatible. The memory
outside `E` is unchanged. -/
theorem innerLoop_spec (t : List ℕ) (ht : t ∈ (List.replicate s (clauseAddrs C φ)).sections) :
    ∀ (xs : List (List ℕ)) (e : List ℕ) (y : Data 32), ImpFrame w φ τ x b C Tb s Db y →
      HoldsList Db t y.mem → HoldsList (Db + s) e y.mem → y.regs contI = 1 →
      Enumerates (t.map (litAddrs C φ)) (e :: xs) →
      (∀ e' ∈ e :: xs, e' ∈ (t.map (litAddrs C φ)).sections) →
      ∃ z, ExecWithin w innerLoop y z ((xs.length + 1) * innerIter s + 2) ∧
        ImpFrame w φ τ x b C Tb s Db z ∧
        (∀ a, a < Db + s ∨ Db + 2 * s ≤ a → z.mem a = y.mem a) ∧
        z.regs sat = ((e :: xs).any (litOk y.mem Tb x b)).toNat := by
  obtain ⟨htlen, htA⟩ := mem_sections_replicate.mp ht
  -- facts about a choice of literals
  have hchoice : ∀ e' ∈ (t.map (litAddrs C φ)).sections, ∀ p ∈ e', ∃ a ∈ t, p ∈ litAddrs C φ a := by
    intro e' he' p hp
    have h2 := List.mem_sections.mp he'
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    have hlen2 := h2.length_eq
    have := (List.forall₂_iff_get.mp h2).2 i hi (by simpa [← hlen2] using hi)
    simp only [List.get_eq_getElem, List.getElem_map] at this
    exact ⟨_, List.getElem_mem _, this⟩
  have hlen : ∀ e' ∈ (t.map (litAddrs C φ)).sections, e'.length = s := fun e' he' => by
    rw [List.mem_sections_length he', List.length_map, htlen]
  have hcodes : ∀ (m : ℕ → ℕ), HoldsList C (encodeClauses φ) m →
      ∀ e' ∈ (t.map (litAddrs C φ)).sections, ∀ p ∈ e', m p < 2 * n := by
    intro m hm e' he' p hp
    obtain ⟨a, ha, hpa⟩ := hchoice e' he' p hp
    exact mem_litAddr_lt hm (htA a ha) hpa
  -- the test is stable under changes of memory at or above `Db`
  have hstable : ∀ (y z : Data 32), ImpFrame w φ τ x b C Tb s Db y →
      (∀ a < Db, z.mem a = y.mem a) → ∀ e' ∈ (t.map (litAddrs C φ)).sections,
        litOk z.mem Tb x b e' = litOk y.mem Tb x b e' := by
    intro y z hf hm e' he'
    have hlt : ∀ p ∈ e', p < Db := fun p hp => by
      obtain ⟨a, ha, hpa⟩ := hchoice e' he' p hp
      have := lt_of_mem_litAddrs (htA a ha) hpa
      have := hf.clauses_le
      omega
    refine compatCodes_congr (n := n) (fun p hp => hm p (hlt p hp)) (fun p hp => ?_)
      (fun v hv => ?_)
    · rw [hm p (hlt p hp)]; exact hcodes _ hf.clauses e' he' p hp
    · exact hm _ (by have := hf.stored_le; omega)
  -- one test, then either stop or step the odometer
  have hstep : ∀ (e : List ℕ) (y : Data 32), ImpFrame w φ τ x b C Tb s Db y →
      HoldsList Db t y.mem → HoldsList (Db + s) e y.mem →
      e ∈ (t.map (litAddrs C φ)).sections →
      ∃ z₁, ExecWithin w goodTest y z₁ (goodTime s) ∧ z₁.mem = y.mem ∧
        ImpFrame w φ τ x b C Tb s Db z₁ ∧ z₁.regs sat = (litOk y.mem Tb x b e).toNat := by
    intro e y hf ht' he he'
    exact goodTest_spec e (hlen e he') y hf he (hcodes _ hf.clauses e he')
  intro xs
  induction xs with
  | nil =>
    intro e y hf ht' he hc hen hmem
    have he' := hmem e (by simp)
    have hcond : (Cond.lt zero contI).Holds y := by simp [Cond.holds_lt, hf.zero_eq, hc]
    obtain ⟨z₁, hz₁, hz₁m, hz₁f, hz₁s⟩ := hstep e y hf ht' he he'
    rcases hok : litOk y.mem Tb x b e
    · -- not compatible: step the odometer, which stops
      have hc₁ : ¬(Cond.eq sat one).Holds z₁ := by
        simp [Cond.holds_eq, hz₁s, hok, hz₁f.one_eq]
      obtain ⟨z₂, hz₂, hz₂f, hz₂m, -, hz₂n⟩ := incE_spec t e z₁ hz₁f ht (by rw [hz₁m]; exact ht')
        (by rw [hz₁m]; exact he) he'
      have hn : nextSection (t.map (litAddrs C φ)) e = none := by simpa using hen.head
      have hcz : ¬(Cond.lt zero contI).Holds z₂ := by
        simp [Cond.holds_lt, hz₂f.zero_eq, hz₂n hn]
      have hsz : z₂.regs sat = 0 := by
        rw [hz₂.regs_eq (by decide), hz₁s, hok]; rfl
      refine ⟨z₂, (ExecWithin.loop_iter hcond (hz₁.seq (ExecWithin.branch_neg
        (pos := ram[ contI ← zero ]) hc₁ hz₂)) (ExecWithin.loop_exit hcz)).mono
        (by simp only [innerIter, List.length_nil]; omega), hz₂f,
        fun a ha => by rw [hz₂m a ha, hz₁m], ?_⟩
      simp [hsz, hok]
    · -- compatible: stop
      have hc₁ : (Cond.eq sat one).Holds z₁ := by
        simp [Cond.holds_eq, hz₁s, hok, hz₁f.one_eq]
      have hcp := ExecWithin.copy (B := .standard) (w := w) (d := contI) (s := zero) (x := z₁)
      rw [hz₁f.zero_eq] at hcp
      have hcz : ¬(Cond.lt zero contI).Holds (z₁.set contI 0) := by
        simp +decide [Cond.holds_lt, hz₁f.zero_eq]
      refine ⟨z₁.set contI 0, (ExecWithin.loop_iter hcond (hz₁.seq (ExecWithin.branch_pos
        (neg := ram[ ⟪incE⟫ ]) hc₁ hcp)) (ExecWithin.loop_exit hcz)).mono
        (by simp only [innerIter, List.length_nil]; omega), hz₁f.set (by decide) _,
        fun a _ => by rw [Data.set_mem, hz₁m], ?_⟩
      simp +decide [hz₁s, hok]
  | cons e' xs ih =>
    intro e y hf ht' he hc hen hmem
    have he' := hmem e (by simp)
    have hcond : (Cond.lt zero contI).Holds y := by simp [Cond.holds_lt, hf.zero_eq, hc]
    obtain ⟨z₁, hz₁, hz₁m, hz₁f, hz₁s⟩ := hstep e y hf ht' he he'
    rcases hok : litOk y.mem Tb x b e
    · -- not compatible: step the odometer to `e'`
      have hc₁ : ¬(Cond.eq sat one).Holds z₁ := by
        simp [Cond.holds_eq, hz₁s, hok, hz₁f.one_eq]
      obtain ⟨z₂, hz₂, hz₂f, hz₂m, hz₂s, -⟩ := incE_spec t e z₁ hz₁f ht
        (by rw [hz₁m]; exact ht') (by rw [hz₁m]; exact he) he'
      have hn : nextSection (t.map (litAddrs C φ)) e = some e' := by simpa using hen.head
      obtain ⟨hc₂, he₂⟩ := hz₂s e' hn
      have ht₂ : HoldsList Db t z₂.mem :=
        ht'.frame fun a _ ha => by rw [hz₂m a (by rw [htlen] at ha; omega), hz₁m]
      obtain ⟨z₃, hz₃, hz₃f, hz₃m, hz₃s⟩ := ih e' z₂ hz₂f ht₂ he₂ hc₂ hen.tail
        fun e'' h => hmem e'' (List.mem_cons_of_mem _ h)
      have hm₃ : ∀ a < Db, z₂.mem a = y.mem a := fun a ha => by rw [hz₂m a (by omega), hz₁m]
      refine ⟨z₃, (ExecWithin.loop_iter hcond (hz₁.seq (ExecWithin.branch_neg
        (pos := ram[ contI ← zero ]) hc₁ hz₂)) hz₃).mono
        (by simp only [innerIter, List.length_cons]; ring_nf; omega), hz₃f,
        fun a ha => by rw [hz₃m a ha, hz₂m a ha, hz₁m], ?_⟩
      rw [hz₃s, show (e :: e' :: xs).any (litOk y.mem Tb x b) =
        (e' :: xs).any (litOk y.mem Tb x b) by rw [List.any_cons, hok, Bool.false_or]]
      congr 1
      exact any_congr_of_mem fun e'' h =>
        hstable y z₂ hf hm₃ e'' (hmem e'' (List.mem_cons_of_mem _ h))
    · -- compatible: stop
      have hc₁ : (Cond.eq sat one).Holds z₁ := by
        simp [Cond.holds_eq, hz₁s, hok, hz₁f.one_eq]
      have hcp := ExecWithin.copy (B := .standard) (w := w) (d := contI) (s := zero) (x := z₁)
      rw [hz₁f.zero_eq] at hcp
      have hcz : ¬(Cond.lt zero contI).Holds (z₁.set contI 0) := by
        simp +decide [Cond.holds_lt, hz₁f.zero_eq]
      refine ⟨z₁.set contI 0, (ExecWithin.loop_iter hcond (hz₁.seq (ExecWithin.branch_pos
        (neg := ram[ ⟪incE⟫ ]) hc₁ hcp)) (ExecWithin.loop_exit hcz)).mono
        (by simp only [innerIter, List.length_cons]; ring_nf; omega), hz₁f.set (by decide) _,
        fun a _ => by rw [Data.set_mem, hz₁m], ?_⟩
      simp +decide [hz₁s, hok]

end Inner

section Inner2

variable {w : ℕ} {φ : CNF (Fin n)} {τ : Fin n → Option Bool} {x : Fin n} {b : Bool}
  {C Tb s Db : ℕ}

/-- The test of the literal search reads only memory below `Db`. -/
theorem litOk_congr {t : List ℕ} (ht : t ∈ (List.replicate s (clauseAddrs C φ)).sections)
    {m₁ m₂ : ℕ → ℕ} (hcl : HoldsList C (encodeClauses φ) m₁)
    (hle : C + (encodeClauses φ).length ≤ Db) (hTb : Tb + n ≤ Db) (hm : ∀ a < Db, m₂ a = m₁ a)
    {e : List ℕ} (he : e ∈ (t.map (litAddrs C φ)).sections) :
    litOk m₂ Tb x b e = litOk m₁ Tb x b e := by
  obtain ⟨-, htA⟩ := mem_sections_replicate.mp ht
  have hchoice : ∀ p ∈ e, ∃ a ∈ t, p ∈ litAddrs C φ a := by
    intro p hp
    have h2 := List.mem_sections.mp he
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    have hlen2 := h2.length_eq
    have := (List.forall₂_iff_get.mp h2).2 i hi (by simpa [← hlen2] using hi)
    simp only [List.get_eq_getElem, List.getElem_map] at this
    exact ⟨_, List.getElem_mem _, this⟩
  have hlt : ∀ p ∈ e, p < Db := fun p hp => by
    obtain ⟨a, ha, hpa⟩ := hchoice p hp
    have := lt_of_mem_litAddrs (htA a ha) hpa
    omega
  refine compatCodes_congr (n := n) (fun p hp => hm p (hlt p hp)) (fun p hp => ?_)
    (fun v hv => hm _ (by omega))
  rw [hm p (hlt p hp)]
  obtain ⟨a, ha, hpa⟩ := hchoice p hp
  exact mem_litAddr_lt hcl (htA a ha) hpa

/-- **The literal search** on a choice `t` of `s` clause addresses in `D`: `sat = 1` exactly when
some choice of one literal address from each clause is compatible, within `innerTime s E`
instructions, where `E` is the length of the encoding of the clauses. The memory outside `E` is
unchanged. -/
theorem innerSearch_spec (t : List ℕ) (ht : t ∈ (List.replicate s (clauseAddrs C φ)).sections)
    (y : Data 32) (hf : ImpFrame w φ τ x b C Tb s Db y) (hl : HoldsList Db t y.mem) :
    ∃ z, ExecWithin w innerSearch y z (innerTime s (encodeClauses φ).length) ∧
      ImpFrame w φ τ x b C Tb s Db z ∧
      (∀ a, a < Db + s ∨ Db + 2 * s ≤ a → z.mem a = y.mem a) ∧
      z.regs sat = ((t.map (litAddrs C φ)).sections.any (litOk y.mem Tb x b)).toNat := by
  obtain ⟨htlen, htA⟩ := mem_sections_replicate.mp ht
  obtain ⟨z₁, hz₁, hz₁f, hz₁m, hz₁e, hz₁s⟩ := initE_spec t y hf ht hl
  have hm₁ : ∀ a < Db, z₁.mem a = y.mem a := fun a ha => hz₁m a (by omega)
  have hcount : (t.map (litAddrs C φ)).sections.length ≤ (encodeClauses φ).length ^ s := by
    have := length_sections_le (m := (encodeClauses φ).length) (L := t.map (litAddrs C φ))
      (by
        intro l hl'
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hl'
        exact length_litAddrs_le (htA a ha))
    simpa [htlen] using this
  rcases hall : t.all fun a => (clauseOf C φ a).length != 0
  · -- an empty clause: no choice of literals
    obtain ⟨a, ha, ha0⟩ : ∃ a ∈ t, (clauseOf C φ a).length = 0 := by
      simpa using hall
    have hnil : (t.map (litAddrs C φ)).sections = [] :=
      sections_eq_nil_of_nil_mem (List.mem_map.mpr ⟨a, ha, by simp [litAddrs, ha0]⟩)
    have hc : ¬(Cond.eq sat one).Holds z₁ := by
      simp [Cond.holds_eq, hz₁s, hall, hz₁f.one_eq]
    have hcp := ExecWithin.copy (B := .standard) (w := w) (d := sat) (s := sat) (x := z₁)
    refine ⟨_, (hz₁.seq (ExecWithin.branch_neg (pos := ram[ contI ← one; ⟪innerLoop⟫ ]) hc
      hcp)).mono (by simp only [innerTime]; nlinarith), hz₁f.set (by decide) _,
      fun a ha => by rw [Data.set_mem, hz₁m a ha], ?_⟩
    simp [hz₁s, hall, hnil]
  · -- every clause has a literal: run the search from the first choice
    have hne : ∀ l ∈ t.map (litAddrs C φ), l ≠ [] := by
      intro l hl'
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hl'
      have := List.all_eq_true.mp hall a ha
      simp only [bne_iff_ne, ne_eq] at this
      simp [litAddrs, this]
    obtain ⟨xs, hxs⟩ := sections_eq_cons_headD 0 hne
    have hhead : (t.map (litAddrs C φ)).map (·.headD 0) = t.map (· + 1) := by
      simp only [List.map_map]
      refine List.map_congr_left fun a ha => ?_
      have := List.all_eq_true.mp hall a ha
      simp only [bne_iff_ne, ne_eq] at this
      simp only [Function.comp_apply, litAddrs]
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero this
      rw [hk, List.range'_succ]
      rfl
    rw [hhead] at hxs
    have hc : (Cond.eq sat one).Holds z₁ := by
      simp [Cond.holds_eq, hz₁s, hall, hz₁f.one_eq]
    have hcp := ExecWithin.copy (B := .standard) (w := w) (d := contI) (s := one) (x := z₁)
    rw [hz₁f.one_eq] at hcp
    have hen : Enumerates (t.map (litAddrs C φ)) (t.map (· + 1) :: xs) := by
      rw [← hxs]
      exact nextSection_sections fun l hl' => by
        obtain ⟨a, -, rfl⟩ := List.mem_map.mp hl'
        exact litAddrs_nodup C φ a
    obtain ⟨z, hz, hzf, hzm, hzs⟩ := innerLoop_spec t ht xs (t.map (· + 1)) (z₁.set contI 1)
      (hz₁f.set (by decide) 1)
      (by simpa using hl.frame fun a _ ha => hz₁m a (Or.inl (by rw [htlen] at ha; omega)))
      (by simpa using hz₁e) (by simp) hen (by rw [← hxs]; exact fun _ h => h)
    have hlen' : xs.length + 1 ≤ (encodeClauses φ).length ^ s := by
      have := congrArg List.length hxs
      simp only [List.length_cons] at this
      omega
    refine ⟨z, (hz₁.seq (ExecWithin.branch_pos (neg := ram[ sat ← sat ]) hc (hcp.seq hz))).mono
      ?_, hzf, fun a ha => by rw [hzm a ha, Data.set_mem, hz₁m a ha], ?_⟩
    · have := Nat.mul_le_mul_right (innerIter s) hlen'
      simp only [innerTime]
      omega
    · rw [hzs, ← hxs]
      congr 1
      exact any_congr_of_mem fun e he =>
        litOk_congr ht hf.clauses hf.clauses_le hf.stored_le hm₁ he

end Inner2

/-! ### The search over choices of clauses -/

/-- One step of the clause search: search the choices of literals, and stop if none is
compatible; otherwise step the odometer. -/
def outerBody : Code .standard 32 := ram[
  ⟪innerSearch⟫; if sat = zero then [ contO ← zero ] else [ ⟪incD⟫ ] ]

/-- The clause search from the current choice on. -/
def outerLoop : Code .standard 32 := .loop (.lt zero contO) outerBody

/-- **The clause search**: `sat = 0` exactly when some choice of `s` clause addresses has no
compatible choice of literals. -/
def outerSearch : Code .standard 32 := ram[ ⟪initD⟫; contO ← one; ⟪outerLoop⟫ ]

/-- The time of one step of the clause search. -/
def outerIter (s E : ℕ) : ℕ := innerTime s E + 12 * s + 8

/-- The time of the clause search, with at most `E ^ s` choices of clauses. -/
def outerTime (s E : ℕ) : ℕ := 5 * s + 6 + E ^ s * outerIter s E

section Outer

variable {w : ℕ} {φ : CNF (Fin n)} {τ : Fin n → Option Bool} {x : Fin n} {b : Bool}
  {C Tb s Db : ℕ}

/-- The test of the clause search: no compatible choice of literals, on the memory `m`. -/
def clauseOk (m : ℕ → ℕ) (C Tb : ℕ) (φ : CNF (Fin n)) (x : Fin n) (b : Bool) (t : List ℕ) :
    Bool :=
  (t.map (litAddrs C φ)).sections.any (litOk m Tb x b)

/-- **The loop of the clause search**, from the choice `t` in `D`, followed by the choices `xs`:
`sat = 1` exactly when each of them has a compatible choice of literals. The memory outside `D`
and `E` is unchanged. -/
theorem outerLoop_spec : ∀ (xs : List (List ℕ)) (t : List ℕ) (y : Data 32),
    ImpFrame w φ τ x b C Tb s Db y → HoldsList Db t y.mem → y.regs contO = 1 →
    Enumerates (List.replicate s (clauseAddrs C φ)) (t :: xs) →
    (∀ t' ∈ t :: xs, t' ∈ (List.replicate s (clauseAddrs C φ)).sections) →
    ∃ z, ExecWithin w outerLoop y z
        ((xs.length + 1) * outerIter s (encodeClauses φ).length + 2) ∧
      ImpFrame w φ τ x b C Tb s Db z ∧
      (∀ a, a < Db ∨ Db + 2 * s ≤ a → z.mem a = y.mem a) ∧
      z.regs sat = ((t :: xs).all (clauseOk y.mem C Tb φ x b)).toNat := by
  intro xs
  induction xs with
  | nil =>
    intro t y hf hl hc hen hmem
    have ht := hmem t (by simp)
    have hcond : (Cond.lt zero contO).Holds y := by simp [Cond.holds_lt, hf.zero_eq, hc]
    obtain ⟨z₁, hz₁, hz₁f, hz₁m, hz₁s⟩ := innerSearch_spec t ht y hf hl
    replace hz₁s : z₁.regs sat = (clauseOk y.mem C Tb φ x b t).toNat := hz₁s
    rcases hok : clauseOk y.mem C Tb φ x b t
    · have hc₁ : (Cond.eq sat zero).Holds z₁ := by
        simp [Cond.holds_eq, hz₁s, hok, hz₁f.zero_eq]
      have hcp := ExecWithin.copy (B := .standard) (w := w) (d := contO) (s := zero) (x := z₁)
      rw [hz₁f.zero_eq] at hcp
      have hcz : ¬(Cond.lt zero contO).Holds (z₁.set contO 0) := by
        simp +decide [Cond.holds_lt, hz₁f.zero_eq]
      refine ⟨z₁.set contO 0, (ExecWithin.loop_iter hcond (hz₁.seq (ExecWithin.branch_pos
        (neg := ram[ ⟪incD⟫ ]) hc₁ hcp)) (ExecWithin.loop_exit hcz)).mono
        (by simp only [outerIter, List.length_nil]; omega), hz₁f.set (by decide) _,
        fun a ha => by rw [Data.set_mem, hz₁m a (by omega)], ?_⟩
      simp +decide [hz₁s, hok]
    · have hc₁ : ¬(Cond.eq sat zero).Holds z₁ := by
        simp [Cond.holds_eq, hz₁s, hok, hz₁f.zero_eq]
      have hl₁ : HoldsList Db t z₁.mem := hl.frame fun a _ ha => hz₁m a (by
        rw [(mem_sections_replicate.mp ht).1] at ha; omega)
      obtain ⟨z₂, hz₂, hz₂f, hz₂m, -, hz₂n⟩ := incD_spec t z₁ hz₁f ht hl₁
      have hn : nextSection (List.replicate s (clauseAddrs C φ)) t = none := by
        simpa using hen.head
      have hcz : ¬(Cond.lt zero contO).Holds z₂ := by
        simp [Cond.holds_lt, hz₂f.zero_eq, hz₂n hn]
      have hsz : z₂.regs sat = 1 := by
        rw [hz₂.regs_eq (by decide), hz₁s, hok]; rfl
      refine ⟨z₂, (ExecWithin.loop_iter hcond (hz₁.seq (ExecWithin.branch_neg
        (pos := ram[ contO ← zero ]) hc₁ hz₂)) (ExecWithin.loop_exit hcz)).mono
        (by simp only [outerIter, List.length_nil]; omega), hz₂f,
        fun a ha => by
          rcases ha with ha | ha
          · rw [hz₂m a (Or.inl ha), hz₁m a (by omega)]
          · rw [hz₂m a (Or.inr (by omega)), hz₁m a (Or.inr ha)], ?_⟩
      simp [hsz, hok]
  | cons t' xs ih =>
    intro t y hf hl hc hen hmem
    have ht := hmem t (by simp)
    have hcond : (Cond.lt zero contO).Holds y := by simp [Cond.holds_lt, hf.zero_eq, hc]
    obtain ⟨z₁, hz₁, hz₁f, hz₁m, hz₁s⟩ := innerSearch_spec t ht y hf hl
    replace hz₁s : z₁.regs sat = (clauseOk y.mem C Tb φ x b t).toNat := hz₁s
    rcases hok : clauseOk y.mem C Tb φ x b t
    · have hc₁ : (Cond.eq sat zero).Holds z₁ := by
        simp [Cond.holds_eq, hz₁s, hok, hz₁f.zero_eq]
      have hcp := ExecWithin.copy (B := .standard) (w := w) (d := contO) (s := zero) (x := z₁)
      rw [hz₁f.zero_eq] at hcp
      have hcz : ¬(Cond.lt zero contO).Holds (z₁.set contO 0) := by
        simp +decide [Cond.holds_lt, hz₁f.zero_eq]
      refine ⟨z₁.set contO 0, (ExecWithin.loop_iter hcond (hz₁.seq (ExecWithin.branch_pos
        (neg := ram[ ⟪incD⟫ ]) hc₁ hcp)) (ExecWithin.loop_exit hcz)).mono
        (by simp only [outerIter, List.length_cons]; ring_nf; omega), hz₁f.set (by decide) _,
        fun a ha => by rw [Data.set_mem, hz₁m a (by omega)], ?_⟩
      simp +decide [hz₁s, hok]
    · have hc₁ : ¬(Cond.eq sat zero).Holds z₁ := by
        simp [Cond.holds_eq, hz₁s, hok, hz₁f.zero_eq]
      have hl₁ : HoldsList Db t z₁.mem := hl.frame fun a _ ha => hz₁m a (by
        rw [(mem_sections_replicate.mp ht).1] at ha; omega)
      obtain ⟨z₂, hz₂, hz₂f, hz₂m, hz₂s, -⟩ := incD_spec t z₁ hz₁f ht hl₁
      have hn : nextSection (List.replicate s (clauseAddrs C φ)) t = some t' := by
        simpa using hen.head
      obtain ⟨hc₂, hl₂⟩ := hz₂s t' hn
      obtain ⟨z₃, hz₃, hz₃f, hz₃m, hz₃s⟩ := ih t' z₂ hz₂f hl₂ hc₂ hen.tail
        fun t'' h => hmem t'' (List.mem_cons_of_mem _ h)
      have hm₂ : ∀ a < Db, z₂.mem a = y.mem a := fun a ha => by
        rw [hz₂m a (Or.inl ha), hz₁m a (by omega)]
      refine ⟨z₃, (ExecWithin.loop_iter hcond (hz₁.seq (ExecWithin.branch_neg
        (pos := ram[ contO ← zero ]) hc₁ hz₂)) hz₃).mono
        (by simp only [outerIter, List.length_cons]; ring_nf; omega), hz₃f,
        fun a ha => by
          rw [hz₃m a ha]
          rcases ha with ha | ha
          · rw [hz₂m a (Or.inl ha), hz₁m a (by omega)]
          · rw [hz₂m a (Or.inr (by omega)), hz₁m a (Or.inr ha)], ?_⟩
      rw [hz₃s, show (t :: t' :: xs).all (clauseOk y.mem C Tb φ x b) =
        (t' :: xs).all (clauseOk y.mem C Tb φ x b) by rw [List.all_cons, hok, Bool.true_and]]
      congr 1
      refine all_congr_of_mem fun t'' h => ?_
      have ht'' := hmem t'' (List.mem_cons_of_mem _ h)
      exact any_congr_of_mem fun e he =>
        litOk_congr ht'' hf.clauses hf.clauses_le hf.stored_le hm₂ he

/-- **The clause search**, on a nonempty formula: `sat = 1` exactly when every choice of `s`
clause addresses has a compatible choice of literals, within `outerTime s E` instructions. The
memory outside `D` and `E` is unchanged. -/
theorem outerSearch_spec (hφ : φ ≠ []) (y : Data 32) (hf : ImpFrame w φ τ x b C Tb s Db y) :
    ∃ z, ExecWithin w outerSearch y z (outerTime s (encodeClauses φ).length) ∧
      ImpFrame w φ τ x b C Tb s Db z ∧
      (∀ a, a < Db ∨ Db + 2 * s ≤ a → z.mem a = y.mem a) ∧
      z.regs sat = ((List.replicate s (clauseAddrs C φ)).sections.all
        (clauseOk y.mem C Tb φ x b)).toNat := by
  obtain ⟨z₁, hz₁, hz₁f, hz₁l, hz₁m⟩ := initD_spec y hf
  have hA : clauseAddrs C φ ≠ [] := by
    rcases φ with _ | ⟨c, φ⟩
    · exact absurd rfl hφ
    · simp [clauseAddrs]
  obtain ⟨xs, hxs⟩ := sections_eq_cons_headD 0 (L := List.replicate s (clauseAddrs C φ))
    fun l hl => by rw [List.eq_of_mem_replicate hl]; exact hA
  rw [List.map_replicate, headD_clauseAddrs hφ] at hxs
  have hcp := ExecWithin.copy (B := .standard) (w := w) (d := contO) (s := one) (x := z₁)
  rw [hz₁f.one_eq] at hcp
  have hen : Enumerates (List.replicate s (clauseAddrs C φ)) (List.replicate s C :: xs) := by
    rw [← hxs]
    exact nextSection_sections fun l hl => by
      rw [List.eq_of_mem_replicate hl]; exact clauseAddrs_nodup C φ
  obtain ⟨z, hz, hzf, hzm, hzs⟩ := outerLoop_spec xs (List.replicate s C) (z₁.set contO 1)
    (hz₁f.set (by decide) 1) (by simpa using hz₁l) (by simp) hen
    (by rw [← hxs]; exact fun _ h => h)
  have hcount : xs.length + 1 ≤ (encodeClauses φ).length ^ s := by
    have := length_sections_le (m := (encodeClauses φ).length)
      (L := List.replicate s (clauseAddrs C φ))
      (fun l hl => by rw [List.eq_of_mem_replicate hl]; exact length_clauseAddrs_le C φ)
    rw [hxs] at this
    simpa using this
  have hm₁ : ∀ a < Db, z₁.mem a = y.mem a := fun a ha => hz₁m a (Or.inl ha)
  refine ⟨z, (hz₁.seq (hcp.seq hz)).mono ?_, hzf, fun a ha => by
    rw [hzm a ha, Data.set_mem, hz₁m a (by omega)], ?_⟩
  · have := Nat.mul_le_mul_right (outerIter s (encodeClauses φ).length) hcount
    simp only [outerTime]
    omega
  · rw [hzs, ← hxs]
    congr 1
    refine all_congr_of_mem fun t ht => ?_
    exact any_congr_of_mem fun e he =>
      litOk_congr ht hf.clauses hf.clauses_le hf.stored_le hm₁ he

end Outer

/-! ### Deciding w-implication -/

/-- Load the word of `x` in the partial assignment. -/
def impLoad : Code .standard 32 := ram[ adr ← tBase + xReg; lenR ← *adr ]

/-- **The w-implication search** for `x = b`: `sat = 0` exactly when the partial assignment sets
`x` to `b`, or some choice of `s` clauses has no compatible choice of literals with `x` set to
`!b`. -/
def impScan : Code .standard 32 := ram[
  ⟪impLoad⟫;
  if lenR = bReg then [ sat ← zero ]
  else [ if cBeg < cEnd then [ ⟪outerSearch⟫ ] else [ sat ← one ] ] ]

/-- The time of the w-implication search. -/
def impScanTime (s E : ℕ) : ℕ := outerTime s E + 6

section Scan

variable {w : ℕ} {φ : CNF (Fin n)} {τ : Fin n → Option Bool} {x : Fin n} {b : Bool}
  {C Tb s Db : ℕ}

/-- **The w-implication search decides w-implication**: `sat = 0` exactly when `x = b` is
`s`-implied under `τ` (through `Cslib.Complexity.PPSZ.impliedTest`), within `impScanTime s E`
instructions. The memory outside `D` and `E` is unchanged. -/
theorem impScan_spec (y : Data 32) (hf : ImpFrame w φ τ x b C Tb s Db y) :
    ∃ z, ExecWithin w impScan y z (impScanTime s (encodeClauses φ).length) ∧
      ImpFrame w φ τ x b C Tb s Db z ∧
      (∀ a, a < Db ∨ Db + 2 * s ≤ a → z.mem a = y.mem a) ∧
      z.regs sat = (!impliedTest φ s τ x b).toNat := by
  have hTx : y.mem (Tb + x) = optCode (τ x) := hf.stored x
  have hf1 : Fits w (Tb + x) := hf.fits_le (by have := hf.stored_le; omega)
  let y₁ := (y.set adr (Tb + x)).set lenR (optCode (τ x))
  have h₁ : ExecWithin w impLoad y y₁ 2 := by
    ram_eval [y₁, impLoad, hf.tBase_eq, hf.x_eq, hTx, hf1]
  have hy₁ : ImpFrame w φ τ x b C Tb s Db y₁ := (hf.set (by decide) _).set (by decide) _
  have htest := addrTest_eq (s := s) (x := x) (b := b) hf.clauses hf.stored
  rw [← htest]
  -- seq association: `impScan` is the two loads followed by the conditional
  have hseq : ∀ {c : Code .standard 32} {z : Data 32} {T : ℕ}, ExecWithin w c y₁ z T →
      c = (ram[ if lenR = bReg then [ sat ← zero ]
        else [ if cBeg < cEnd then [ ⟪outerSearch⟫ ] else [ sat ← one ] ] ] :
          Code .standard 32) →
      ExecWithin w impScan y z (T + 2) := by
    intro c z T h hc
    subst hc
    exact (h₁.seq h).mono (by omega)
  by_cases hτx : optCode (τ x) = b.toNat
  · -- already set
    have hc : (Cond.eq lenR bReg).Holds y₁ := by simp +decide [Cond.holds_eq, y₁, hf.b_eq, hτx]
    have hcp := ExecWithin.copy (B := .standard) (w := w) (d := sat) (s := zero) (x := y₁)
    rw [hy₁.zero_eq] at hcp
    refine ⟨_, (hseq (ExecWithin.branch_pos hc hcp) rfl).mono
      (by simp only [impScanTime, outerTime]; omega),
      hy₁.set (by decide) _, fun a _ => rfl, ?_⟩
    simp [addrTest, hTx, hτx]
  · have hc : ¬(Cond.eq lenR bReg).Holds y₁ := by
      simp +decide [Cond.holds_eq, y₁, hf.b_eq, hτx]
    have hfirst : (y.mem (Tb + x) == b.toNat) = false := by simp [hTx, hτx]
    rcases φ with _ | ⟨c₀, φ'⟩
    · -- no clauses
      have hc' : ¬(Cond.lt cBeg cEnd).Holds y₁ := by
        simp +decide [Cond.holds_lt, y₁, hf.cBeg_eq, hf.cEnd_eq]
      have hcp := ExecWithin.copy (B := .standard) (w := w) (d := sat) (s := one) (x := y₁)
      rw [hy₁.one_eq] at hcp
      refine ⟨_, (hseq (ExecWithin.branch_neg hc (ExecWithin.branch_neg hc' hcp)) rfl).mono
        (by simp only [impScanTime, outerTime]; omega), hy₁.set (by decide) _, fun a _ => rfl, ?_⟩
      have hnone : ((List.replicate s (clauseAddrs C ([] : CNF (Fin n)))).sections.any fun D =>
          !(D.map fun p => List.range' (p + 1) (y.mem p)).sections.any fun E =>
            compatCodes (fun v => y.mem (Tb + v)) x b.toNat (E.map y.mem)) = false := by
        rcases s with _ | s
        · simp [compatCodes]
        · rw [show clauseAddrs C ([] : CNF (Fin n)) = [] from rfl,
            sections_eq_nil_of_nil_mem (List.mem_replicate.mpr ⟨by omega, rfl⟩)]
          rfl
      simp [addrTest, hfirst, hnone]
    · -- some clause: the clause search
      have hlt : C < C + (encodeClauses (c₀ :: φ')).length := by
        simp only [encodeClauses_cons, List.length_append, length_encodeClause]; omega
      have hc' : (Cond.lt cBeg cEnd).Holds y₁ := by
        simp +decide [Cond.holds_lt, y₁, hf.cBeg_eq, hf.cEnd_eq]
      obtain ⟨z, hz, hzf, hzm, hzs⟩ := outerSearch_spec (List.cons_ne_nil c₀ φ') y₁ hy₁
      refine ⟨z, (hseq (ExecWithin.branch_neg hc (ExecWithin.branch_pos hc' hz)) rfl).mono
        (by simp only [impScanTime, outerTime]; omega), hzf, fun a ha => hzm a ha, ?_⟩
      rw [hzs]
      simp only [y₁, Data.set_mem, addrTest, hfirst, Bool.false_or]
      congr 1
      rw [Bool.eq_iff_iff]
      simp only [List.all_eq_true, Bool.not_eq_true', List.any_eq_false]
      refine forall₂_congr fun D hD => ?_
      have hD' := (mem_sections_replicate.mp hD).2
      have hmap : (D.map fun p => List.range' (p + 1) (y.mem p)) =
          D.map (litAddrs C (c₀ :: φ')) :=
        List.map_congr_left fun p hp => by
          rw [litAddrs, mem_clauseAddr hf.clauses (hD' p hp)]
      rw [hmap, clauseOk, List.any_eq_true]
      simp only [litOk, not_forall, not_not, exists_prop]

end Scan

/-! ### The implied value -/

/-- Set `D` and `E` back to zero. -/
def zeroBody : Code .standard 32 := ram[ adr ← dBase + jR; *adr ← zero; jR ← jR + one ]

/-- Set the words `jR, …, 2 s - 1` after `dBase` to zero. -/
def zeroLoop : Code .standard 32 := .loop (.lt jR stop) zeroBody

/-- **Clear the scratch memory** of `D` and `E`. -/
def zeroScratch : Code .standard 32 := ram[ jR ← zero; stop ← sReg + sReg; ⟪zeroLoop⟫ ]

/-- Read the bound `s` from the word at `tBase + 2 n`, set the addresses of `D` and `E` just after
it, and start with the polarity `true`. -/
def impSetup : Code .standard 32 := ram[
  dBase ← tBase + nReg; dBase ← dBase + nReg; sReg ← *dBase; dBase ← dBase + one;
  eBase ← dBase + sReg; bReg ← one ]

/-- **The value w-implied on `xReg`**, stored in `res` as `optCode (implied φ s τ x)`. The bound
`s` is read from the word at `tBase + 2 n`, and the arrays `D` and `E` take the `2 s` words after
it, which are cleared at the end. -/
def impliedCode : Code .standard 32 := ram[
  ⟪impSetup⟫; ⟪impScan⟫;
  if sat = zero then [ res ← one ]
  else [ bReg ← zero; ⟪impScan⟫; if sat = zero then [ res ← zero ] else [ res ← two ] ];
  ⟪zeroScratch⟫ ]

/-- **The instruction bound of `impliedCode`** for the bound `s` and a clause encoding of length
`E`: two searches over at most `E ^ s` choices of clauses, each with at most `E ^ s` choices of
literals. -/
def impliedTime (s E : ℕ) : ℕ := 2 * impScanTime s E + 10 * s + 16

/-- **The instruction bound in closed form**: `impliedTime s E ≤ 140 (s + 1)² (E + 1)^(2 s)`. -/
theorem impliedTime_le (s E : ℕ) :
    impliedTime s E ≤ 140 * (s + 1) ^ 2 * (E + 1) ^ (2 * s) := by
  have hP : E ^ s ≤ (E + 1) ^ s := Nat.pow_le_pow_left (Nat.le_succ E) s
  have hF : 1 ≤ (E + 1) ^ s := Nat.one_le_pow _ _ (Nat.succ_pos E)
  rw [show 2 * s = s * 2 by ring, pow_mul]
  simp only [impliedTime, impScanTime, outerTime, outerIter, innerTime, innerIter, goodTime]
  generalize E ^ s = P at *
  generalize (E + 1) ^ s = F at *
  have hFF : 1 ≤ F * F := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hA : P * (48 * s + 32) ≤ F * F * (48 * s + 32) :=
    Nat.mul_le_mul_right _ (hP.trans (Nat.le_mul_self F))
  have hB : P * P * (18 * s ^ 2 + 72 * s + 26) ≤ F * F * (18 * s ^ 2 + 72 * s + 26) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul hP hP)
  have hC : 20 * s + 40 ≤ F * F * (20 * s + 40) := Nat.le_mul_of_pos_left _ hFF
  have hD : F * F * (18 * s ^ 2 + 140 * s + 98) ≤ F * F * (140 * s ^ 2 + 280 * s + 140) :=
    Nat.mul_le_mul_left _ (by nlinarith)
  calc 2 * (5 * s + 6 + P * (12 * s + 8 + P * (s * (9 * s + 22) + 4 + 14 * s + 9) + 12 * s + 8)
        + 6) + 10 * s + 16
      = 20 * s + 40 + P * (48 * s + 32) + P * P * (18 * s ^ 2 + 72 * s + 26) := by ring
    _ ≤ F * F * (20 * s + 40) + F * F * (48 * s + 32) + F * F * (18 * s ^ 2 + 72 * s + 26) := by
        omega
    _ = F * F * (18 * s ^ 2 + 140 * s + 98) := by ring
    _ ≤ F * F * (140 * s ^ 2 + 280 * s + 140) := hD
    _ = 140 * (s + 1) ^ 2 * F ^ 2 := by ring

section ImpliedCode

variable {w : ℕ} {φ : CNF (Fin n)} {τ : Fin n → Option Bool} {x : Fin n} {b : Bool}
  {C Tb s Db : ℕ}

/-- The frame with another polarity. -/
theorem ImpFrame.setB {y : Data 32} (h : ImpFrame w φ τ x b C Tb s Db y) (b' : Bool) :
    ImpFrame w φ τ x b' C Tb s Db (y.set bReg b'.toNat) :=
  { (h.set (i := sat) (by decide) 0) with
    zero_eq := by simp +decide [h.zero_eq]
    one_eq := by simp +decide [h.one_eq]
    x_eq := by simp +decide [h.x_eq]
    b_eq := by simp
    cBeg_eq := by simp +decide [h.cBeg_eq]
    cEnd_eq := by simp +decide [h.cEnd_eq]
    tBase_eq := by simp +decide [h.tBase_eq]
    s_eq := by simp +decide [h.s_eq]
    dBase_eq := by simp +decide [h.dBase_eq]
    eBase_eq := by simp +decide [h.eBase_eq]
    clauses := h.clauses
    stored := h.stored }

/-- **The clearing loop** from word `j`: the words `j, …, 2 s - 1` after `Db` become zero, and
the other memory is unchanged. -/
theorem zeroLoop_spec : ∀ (d : ℕ) (y : Data 32), ImpFrame w φ τ x b C Tb s Db y →
    y.regs stop = 2 * s → y.regs jR + d = 2 * s →
    ∃ z, ExecWithin w zeroLoop y z (5 * d + 2) ∧ ImpFrame w φ τ x b C Tb s Db z ∧
      (∀ i, y.regs jR ≤ i → i < 2 * s → z.mem (Db + i) = 0) ∧
      ∀ a, a < Db + y.regs jR ∨ Db + 2 * s ≤ a → z.mem a = y.mem a
  | 0, y, hf, hst, hd => by
    have hc : ¬(Cond.lt jR stop).Holds y := by simp [Cond.holds_lt, hst]; omega
    exact ⟨y, (ExecWithin.loop_exit hc).mono (by omega), hf, fun i h1 h2 => by omega,
      fun _ _ => rfl⟩
  | d + 1, y, hf, hst, hd => by
    obtain ⟨j, hj⟩ : ∃ j, y.regs jR = j := ⟨_, rfl⟩
    rw [hj] at hd ⊢
    have hc : (Cond.lt jR stop).Holds y := by simp [Cond.holds_lt, hst, hj]; omega
    have hf1 : Fits w (Db + j) := hf.fits_le (by omega)
    have hf2 : Fits w (j + 1) := hf.fits_le (by omega)
    let y₁ := ((y.set adr (Db + j)).write (Db + j) 0).set jR (j + 1)
    have hrun : ExecWithin w zeroBody y y₁ 3 := by
      ram_eval [y₁, zeroBody, hf.dBase_eq, hj, hf.zero_eq, hf.one_eq, hf1, hf2]
    have hy₁ : ImpFrame w φ τ x b C Tb s Db y₁ :=
      ((hf.set (by decide) _).write (by omega) _).set (by decide) _
    obtain ⟨z, hz, hzf, hz0, hzm⟩ := zeroLoop_spec d y₁ hy₁ (by simp +decide [y₁, hst])
      (by simp [y₁]; omega)
    have hj₁ : y₁.regs jR = j + 1 := by simp [y₁]
    rw [hj₁] at hz0 hzm
    refine ⟨z, (ExecWithin.loop_iter hc hrun hz).mono (by omega), hzf, fun i h1 h2 => ?_,
      fun a ha => ?_⟩
    · rcases Nat.lt_or_ge i (j + 1) with hi | hi
      · have hij : i = j := by omega
        subst hij
        rw [hzm _ (by omega)]
        simp [y₁]
      · exact hz0 i hi h2
    · rw [hzm a (by omega)]
      simp only [y₁, Data.set_mem, Data.write_mem]
      rw [Function.update_of_ne (by omega)]

/-- **Clear the scratch memory**: the `2 s` words of `D` and `E` become zero, and the other memory
is unchanged, within `10 s + 4` instructions. -/
theorem zeroScratch_spec (y : Data 32) (hf : ImpFrame w φ τ x b C Tb s Db y) :
    ∃ z, ExecWithin w zeroScratch y z (10 * s + 4) ∧ ImpFrame w φ τ x b C Tb s Db z ∧
      (∀ i < 2 * s, z.mem (Db + i) = 0) ∧ ∀ a, a < Db ∨ Db + 2 * s ≤ a → z.mem a = y.mem a := by
  have hf1 : Fits w (s + s) := hf.fits_le (by omega)
  let y₁ := (y.set jR 0).set stop (s + s)
  have h₁ : ExecWithin w (ram[ jR ← zero; stop ← sReg + sReg ] : Code .standard 32) y y₁ 2 := by
    ram_eval [y₁, hf.zero_eq, hf.s_eq, hf1]
  have hy₁ : ImpFrame w φ τ x b C Tb s Db y₁ := (hf.set (by decide) _).set (by decide) _
  obtain ⟨z, hz, hzf, hz0, hzm⟩ := zeroLoop_spec (2 * s) y₁ hy₁ (by simp [y₁]; omega)
    (by simp +decide [y₁])
  have hj : y₁.regs jR = 0 := by simp +decide [y₁]
  rw [hj] at hz0 hzm
  have hseq : ExecWithin w zeroScratch y z (2 + (5 * (2 * s) + 2)) :=
    ExecWithin.seq_assoc.mp (h₁.seq hz)
  exact ⟨z, hseq.mono (by omega), hzf, fun i hi => hz0 i (Nat.zero_le _) hi,
    fun a ha => by rw [hzm a (by omega)]; rfl⟩

/-- **The value w-implied on `x`.** From the clauses of `φ` stored in `[cBeg, cEnd)` below the
partial assignment `τ` stored at `tBase = Tb`, the bound `s` stored at `Tb + 2 n` and `2 s` zero
words after it, `impliedCode` stores `optCode (implied φ s τ x)` in `res` within
`impliedTime s E` instructions, where `E` is the length of the encoding of the clauses, and leaves
memory unchanged. -/
theorem impliedCode_spec (φ : CNF (Fin n)) (τ : Fin n → Option Bool) (x : Fin n) (s : ℕ)
    {C Tb : ℕ} (y : Data 32) (hz : y.regs zero = 0) (ho : y.regs one = 1)
    (htwo : y.regs two = 2) (hx : y.regs xReg = x) (hC : y.regs cBeg = C)
    (hCe : y.regs cEnd = C + (encodeClauses φ).length) (hTb : y.regs tBase = Tb)
    (hn : y.regs nReg = n) (hcl : HoldsList C (encodeClauses φ) y.mem)
    (hτ : PartialAt y.mem Tb τ) (hle : C + (encodeClauses φ).length ≤ Tb)
    (hs : y.mem (Tb + 2 * n) = s) (hzero : ∀ i < 2 * s, y.mem (Tb + 2 * n + 1 + i) = 0)
    (hw : Fits w (Tb + 2 * n + 2 * s + 2)) :
    ∃ z, ExecWithin w impliedCode y z (impliedTime s (encodeClauses φ).length) ∧
      z.mem = y.mem ∧ z.regs res = optCode (implied φ s τ x) := by
  set Db := Tb + 2 * n + 1 with hDb
  have hf1 : Fits w (Tb + n) := hw.of_le (by omega)
  have hf2 : Fits w (Tb + n + n) := hw.of_le (by omega)
  have hf3 : Fits w (Tb + n + n + 1) := hw.of_le (by omega)
  have hf4 : Fits w (Tb + n + n + 1 + s) := hw.of_le (by omega)
  have hs' : y.mem (Tb + n + n) = s := by rw [← hs]; congr 1; omega
  let y₁ := (((((y.set dBase (Tb + n)).set dBase (Tb + n + n)).set sReg s).set dBase
    (Tb + n + n + 1)).set eBase (Tb + n + n + 1 + s)).set bReg 1
  have h₁ : ExecWithin w impSetup y y₁ 6 := by
    ram_eval [y₁, impSetup, hTb, hn, hs', ho, hf1, hf2, hf3, hf4]
  have hy₁ : ImpFrame w φ τ x true C Tb s Db y₁ :=
    { zero_eq := by simp +decide [y₁, hz]
      one_eq := by simp +decide [y₁, ho]
      x_eq := by simp +decide [y₁, hx]
      b_eq := by simp +decide [y₁]
      cBeg_eq := by simp +decide [y₁, hC]
      cEnd_eq := by simp +decide [y₁, hCe]
      tBase_eq := by simp +decide [y₁, hTb]
      s_eq := by simp +decide [y₁]
      dBase_eq := by simp +decide [y₁, hDb]; omega
      eBase_eq := by simp +decide [y₁, hDb]; omega
      clauses := hcl
      stored := hτ
      clauses_le := by omega
      stored_le := by omega
      codes_le := by omega
      fits := hw.of_le (by omega) }
  -- the polarity `true`
  obtain ⟨z₁, hz₁, hz₁f, hz₁m, hz₁s⟩ := impScan_spec y₁ hy₁
  -- the end: clear the scratch memory
  have hend : ∀ (b' : Bool) (z : Data 32), ImpFrame w φ τ x b' C Tb s Db z →
      (∀ a, a < Db ∨ Db + 2 * s ≤ a → z.mem a = y.mem a) →
      ∃ z', ExecWithin w zeroScratch z z' (10 * s + 4) ∧ z'.mem = y.mem ∧
        z'.regs res = z.regs res := by
    intro b' z hfz hzm
    obtain ⟨z', hz', -, hz'0, hz'm⟩ := zeroScratch_spec z hfz
    refine ⟨z', hz', funext fun a => ?_, hz'.regs_eq (by decide)⟩
    by_cases ha : a < Db ∨ Db + 2 * s ≤ a
    · rw [hz'm a ha, hzm a ha]
    · obtain ⟨i, hi, rfl⟩ : ∃ i < 2 * s, a = Db + i := ⟨a - Db, by omega, by omega⟩
      rw [hz'0 i hi, hDb, hzero i hi]
  rw [implied_eq_test]
  have hseq : ∀ {c : Code .standard 32} {z₂ z₃ : Data 32} {T T' : ℕ},
      ExecWithin w c z₁ z₂ T → ExecWithin w zeroScratch z₂ z₃ T' →
      c = (ram[ if sat = zero then [ res ← one ]
        else [ bReg ← zero; ⟪impScan⟫; if sat = zero then [ res ← zero ] else [ res ← two ] ] ] :
          Code .standard 32) →
      ExecWithin w impliedCode y z₃ (6 + impScanTime s (encodeClauses φ).length + T + T') := by
    intro c z₂ z₃ T T' h h' hc
    subst hc
    exact (h₁.seq (hz₁.seq (h.seq h'))).mono (by omega)
  rcases ht : impliedTest φ s τ x true
  · -- not implied `true`: the polarity `false`
    have hc : ¬(Cond.eq sat zero).Holds z₁ := by
      simp [Cond.holds_eq, hz₁s, ht, hz₁f.zero_eq]
    have hb₀ := ExecWithin.copy (B := .standard) (w := w) (d := bReg) (s := zero) (x := z₁)
    rw [hz₁f.zero_eq] at hb₀
    have hz₁f' : ImpFrame w φ τ x false C Tb s Db (z₁.set bReg 0) := hz₁f.setB false
    obtain ⟨z₂, hz₂, hz₂f, hz₂m, hz₂s⟩ := impScan_spec (z₁.set bReg 0) hz₁f'
    have hm₂ : ∀ a, a < Db ∨ Db + 2 * s ≤ a → z₂.mem a = y.mem a := fun a ha => by
      rw [hz₂m a ha, Data.set_mem, hz₁m a ha]; rfl
    rcases hf' : impliedTest φ s τ x false
    · have hc' : ¬(Cond.eq sat zero).Holds z₂ := by
        simp [Cond.holds_eq, hz₂s, hf', hz₂f.zero_eq]
      have hr := ExecWithin.copy (B := .standard) (w := w) (d := res) (s := two) (x := z₂)
      have htwo₂ : z₂.regs two = 2 := by
        rw [hz₂.regs_eq (by decide), Data.set_regs, Function.update_of_ne (by decide),
          hz₁.regs_eq (by decide)]
        simp +decide [y₁, htwo]
      rw [htwo₂] at hr
      obtain ⟨z', hz', hz'm, hz'r⟩ := hend false (z₂.set res 2) (hz₂f.set (by decide) _)
        fun a ha => by rw [Data.set_mem, hm₂ a ha]
      refine ⟨z', (hseq (ExecWithin.branch_neg hc (hb₀.seq (hz₂.seq
        (ExecWithin.branch_neg hc' hr)))) hz' rfl).mono (by simp only [impliedTime]; omega),
        hz'm, ?_⟩
      rw [hz'r]; simp [optCode]
    · have hc' : (Cond.eq sat zero).Holds z₂ := by
        simp [Cond.holds_eq, hz₂s, hf', hz₂f.zero_eq]
      have hr := ExecWithin.copy (B := .standard) (w := w) (d := res) (s := zero) (x := z₂)
      rw [hz₂f.zero_eq] at hr
      obtain ⟨z', hz', hz'm, hz'r⟩ := hend false (z₂.set res 0) (hz₂f.set (by decide) _)
        fun a ha => by rw [Data.set_mem, hm₂ a ha]
      refine ⟨z', (hseq (ExecWithin.branch_neg hc (hb₀.seq (hz₂.seq
        (ExecWithin.branch_pos hc' hr)))) hz' rfl).mono (by simp only [impliedTime]; omega),
        hz'm, ?_⟩
      rw [hz'r]; simp [optCode]
  · -- implied `true`
    have hc : (Cond.eq sat zero).Holds z₁ := by
      simp [Cond.holds_eq, hz₁s, ht, hz₁f.zero_eq]
    have hr := ExecWithin.copy (B := .standard) (w := w) (d := res) (s := one) (x := z₁)
    rw [hz₁f.one_eq] at hr
    obtain ⟨z', hz', hz'm, hz'r⟩ := hend true (z₁.set res 1) (hz₁f.set (by decide) _)
      fun a ha => by rw [Data.set_mem, hz₁m a ha]; rfl
    refine ⟨z', (hseq (ExecWithin.branch_pos hc hr) hz' rfl).mono
      (by simp only [impliedTime]; omega), hz'm, ?_⟩
    rw [hz'r]; simp [optCode]

end ImpliedCode

end Cslib.Algorithms.WordRAM.PPSZ
