/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORNative
public import CslibFrontier.Computability.WordRAM.Allocation

/-!
# Iterative native Add/XNOR dynamic programming

The native table sweep is reused by a fixed loop reading the actual operands
from a caller-supplied memory interval. Source and destination buffers exchange
roles at each layer; no table history or operator-string enumeration is stored.
The semantic invariant uses the already proved full-width `WordTable` program.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native

open Cslib.WordRAM

/-- Next operand address. -/
abbrev cursor : Fin 18 := 12
/-- End of the operand interval. -/
abbrev limit : Fin 18 := 13
/-- Temporary for buffer exchange and the constant increment. -/
abbrev temporary : Fin 18 := 14
/-- Initial word. -/
abbrev initial : Fin 18 := 15
/-- Target word. -/
abbrev target : Fin 18 := 16
/-- Returned Boolean flag. -/
abbrev answer : Fin 18 := 17

/-- One operand load, one actual sweep, then exchange the reusable buffers. -/
@[expose] def iteration : Code .standard 18 :=
  .seq (.op (.load operand cursor)) (.seq sweep
    (ram[ temporary ← source; source ← destination; destination ← temporary;
      temporary ← #1; cursor ← cursor + temporary ]))

/-- Fixed native loop over the supplied operands. -/
@[expose] def layers : Code .standard 18 := .loop (.lt cursor limit) iteration

/-- The two reusable buffer intervals. -/
@[expose] def InBuffers (b c N z : ℕ) : Prop :=
  (b ≤ z ∧ z < b + N) ∨ (c ≤ z ∧ z < c + N)

/-- The native loop refines every layer of the unrestricted word semantics.
The input table is an explicit prerequisite here; initialization is separate.
All operand reads, buffer exchanges and outer loop tests are charged. -/
theorem layers_exec {W m b c p : ℕ} (as : List (BitVec m)) (x : Data 18)
    (table : WordTable Bool m)
    (hb : x.regs source = b) (hc : x.regs destination = c)
    (hn : x.regs modulus = 2 ^ m) (hp : x.regs cursor = p)
    (hl : x.regs limit = p + as.length)
    (hinput : ∀ j (hj : j < as.length), x.mem (p + j) = as[j].toNat)
    (hout : ∀ j < as.length, ¬InBuffers b c (2 ^ m) (p + j))
    (hdisjoint : b + 2 ^ m ≤ c ∨ c + 2 ^ m ≤ b)
    (hrep : Represents x.mem b table)
    (hfit : Fits W (b + c + 2 * 2 ^ m + 2)) (hinputfit : Fits W (p + as.length)) :
    ∃ y, ExecWithin W layers x y (as.length * (14 * 2 ^ m + 14) + 2) ∧
      Represents y.mem (y.regs source) (WordTable.run (as.map stateKey) table).ret ∧
      ((y.regs source = b ∧ y.regs destination = c) ∨
        (y.regs source = c ∧ y.regs destination = b)) ∧
      y.regs modulus = 2 ^ m ∧ y.regs cursor = p + as.length ∧
      y.regs limit = p + as.length ∧
      (∀ z, ¬InBuffers b c (2 ^ m) z → y.mem z = x.mem z) := by
  induction as generalizing x table b c p with
  | nil =>
    refine ⟨x, ?_, ?_, Or.inl ⟨hb, hc⟩, hn, ?_, ?_, fun _ _ => rfl⟩
    · simp only [List.length_nil, Nat.zero_mul, Nat.zero_add, layers]
      exact ExecWithin.loop_exit (by simp [Cond.holds_lt, hp, hl])
    · simpa only [List.map_nil, WordTable.run, hb] using hrep
    · simpa using hp
    · simpa using hl
  | cons a as ih =>
    have h0 : 0 < (a :: as).length := by simp
    have hfirst : x.mem p = a.toNat := by simpa using hinput 0 h0
    let loaded := x.set operand a.toNat
    have heLoad : ExecWithin (B := .standard) W (.op (.load operand cursor)) x loaded 1 := by
      simpa only [Op.eval_load, hp, hfirst, loaded] using
        (ExecWithin.load (B := .standard) (w := W) (d := operand) (a := cursor) (x := x))
    have lb : loaded.regs source = b := by simpa +decide [loaded, source, operand] using hb
    have lc : loaded.regs destination = c := by
      simpa +decide [loaded, destination, operand] using hc
    have ln : loaded.regs modulus = 2 ^ m := by
      simpa +decide [loaded, modulus, operand] using hn
    obtain ⟨z, heSweep, zrep, zmem, zb, zc, zn, za⟩ :=
      advance_exec loaded a table lb lc ln (by simp [loaded]) hdisjoint hrep hfit
    have zp : z.regs cursor = p := by
      rw [heSweep.regs_eq (by decide)]
      simpa +decide [loaded, cursor, operand] using hp
    have zl : z.regs limit = p + (a :: as).length := by
      rw [heSweep.regs_eq (by decide)]
      simpa +decide [loaded, limit, operand] using hl
    have h1 : Fits W 1 := hfit.of_le (by omega)
    have hfp : Fits W (p + 1) := hinputfit.of_le (by simp only [List.length_cons]; omega)
    let next := ((((z.set temporary b).set source c).set destination b).set temporary 1).set
      cursor (p + 1)
    have heSwap : ExecWithin (B := .standard) W
        (ram[ temporary ← source; source ← destination; destination ← temporary;
          temporary ← #1; cursor ← cursor + temporary ]) z next 5 := by
      ram_eval [next, zb, zc, zp, h1, hfp,
        temporary, source, destination, cursor, Fin.mk.injEq]
    have nb : next.regs source = c := by simp +decide [next, source, destination, temporary, cursor]
    have nc : next.regs destination = b := by
      simp +decide [next, source, destination, temporary, cursor]
    have nn : next.regs modulus = 2 ^ m := by
      simpa +decide [next, source, destination, temporary, cursor, modulus] using zn
    have np : next.regs cursor = p + 1 := by simp [next]
    have nl : next.regs limit = (p + 1) + as.length := by
      simpa +decide [next, source, destination, temporary, cursor, limit, List.length_cons,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using zl
    have nmem : next.mem = updatePrefix x.mem b c (2 ^ m) a.toNat (2 ^ m) := by
      simpa only [next, Data.set_mem, loaded] using zmem
    have frame (j : ℕ) (hj : ¬InBuffers b c (2 ^ m) j) : next.mem j = x.mem j := by
      rw [nmem, updatePrefix_outside]
      simp only [InBuffers, not_or] at hj
      exact hj.2
    have ninput : ∀ j (hj : j < as.length), next.mem (p + 1 + j) = as[j].toNat := by
      intro j hj
      rw [frame _ (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (hout (j + 1) (by simp only [List.length_cons]; omega)))]
      have hget : x.mem (p + (j + 1)) = as[j].toNat :=
        hinput (j + 1) (by simp only [List.length_cons]; omega)
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hget
    have nout : ∀ j < as.length, ¬InBuffers c b (2 ^ m) (p + 1 + j) := by
      intro j hj
      have h := hout (j + 1) (by simp; omega)
      simpa only [InBuffers, or_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    have nrep : Represents next.mem c (WordTable.advance (stateKey a) table).ret := by
      simpa only [next, Data.set_mem] using zrep
    obtain ⟨y, heTail, yrep, ybases, yn, yp, yl, yframe⟩ := ih next
      (WordTable.advance (stateKey a) table).ret nb nc nn np nl ninput nout
      (by omega) nrep (by simpa only [Nat.add_comm] using hfit)
      (by simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using hinputfit)
    refine ⟨y, ?_, ?_, ?_, yn, ?_, ?_, ?_⟩
    · have heStep := heLoad.seq (heSweep.seq heSwap)
      have he := ExecWithin.loop_iter (cond := .lt cursor limit)
        (by simp [Cond.holds_lt, hp, hl]) heStep heTail
      apply he.mono
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
    · simpa only [List.map_cons, WordTable.run, Cslib.Algorithms.Lean.TimeM.ret_bind,
        Cslib.Algorithms.Lean.TimeM.ret_pure] using yrep
    · exact ybases.elim Or.inr Or.inl
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using yp
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using yl
    · intro j hj
      rw [yframe j (by simpa only [InBuffers, or_comm] using hj), frame j hj]

/-- Charged initialization: zero the source buffer, then set the initial flag. -/
@[expose] def initializeTable : Code .standard 18 :=
  .seq (ram[ one ← #1; left ← #0; address ← source; right ← source + modulus ])
    (.seq (zeroFill address right left one)
      (ram[ address ← source + initial; *address ← one ]))

/-- The initializer constructs the actual singleton table from dirty memory. -/
theorem initialize_exec {W m b : ℕ} (x : Data 18) (s : BitVec m)
    (hb : x.regs source = b) (hn : x.regs modulus = 2 ^ m)
    (hs : x.regs initial = s.toNat) (hfit : Fits W (b + 2 ^ m + 2)) :
    ∃ y, ExecWithin W initializeTable x y (4 * 2 ^ m + 8) ∧
      Represents y.mem b (WordTable.point m (stateKey s)).ret ∧
      y.mem = Function.update (clear x.mem b (2 ^ m)) (b + s.toNat) 1 := by
  have h0 : Fits W 0 := fits_zero _
  have h1 : Fits W 1 := hfit.of_le (by omega)
  have hstop : Fits W (b + 2 ^ m) := hfit.of_le (by omega)
  have haddr : Fits W (b + s.toNat) := hfit.of_le (by have := s.isLt; omega)
  let start := (((x.set one 1).set left 0).set address b).set right (b + 2 ^ m)
  have heStart : ExecWithin (B := .standard) W
      (ram[ one ← #1; left ← #0; address ← source; right ← source + modulus ]) x start 4 := by
    ram_eval [start, hb, hn, h0, h1, hstop, one, left, address, right, source, modulus,
      Fin.mk.injEq]
  have heClear := zeroFill_exec (w := W) (cur := address) (stop := right) (zero := left)
    (one := one) (x := start) (by decide) (by decide) (by decide)
    (by simp +decide [start, left, right, address, one])
    (by simp +decide [start, left, right, address, one])
    (by simp +decide [start, left, right, address, one])
    (by simpa +decide [start, left, right, address, one] using hstop)
  let zeroed : Data 18 := ⟨Function.update start.regs address (b + 2 ^ m),
    clear x.mem b (2 ^ m)⟩
  have heZero : ExecWithin W (zeroFill address right left one) start zeroed
      (4 * 2 ^ m + 2) := by
    refine ⟨_, le_rfl, ?_⟩
    simpa +decide [zeroed, start, left, right, address, one] using heClear
  let y := (zeroed.set address (b + s.toNat)).write (b + s.toNat) 1
  have hePoint : ExecWithin (B := .standard) W
      (ram[ address ← source + initial; *address ← one ]) zeroed y 2 := by
    ram_eval [zeroed, start, y, hb, hs, haddr, one, left, address, right, source, initial,
      Fin.mk.injEq]
  refine ⟨y, ?_, ?_, rfl⟩
  · exact (heStart.seq (heZero.seq hePoint)).mono (by omega)
  · intro t
    simp only [y, Data.write_mem, Data.set_mem, zeroed, WordTable.point_read]
    by_cases ht : t = s
    · subst t; simp
    · have hne : b + t.toNat ≠ b + s.toNat := by
        intro h
        exact ht (BitVec.eq_of_toNat_eq (by omega))
      rw [Function.update_of_ne hne, clear_of_owns (by
        change b ≤ b + t.toNat ∧ b + t.toNat < b + 2 ^ m
        exact ⟨by omega, by have := t.isLt; omega⟩)]
      simp [Ne.symm ht]

/-- Complete fixed native decision program, including singleton construction and lookup. -/
@[expose] def decide : Code .standard 18 :=
  .seq initializeTable (.seq layers (ram[ address ← source + target; answer ← *address ]))

/-- Actual decision for arbitrary operands, initial word and target. Both buffers
are overwritten as needed; the operand interval and all outside memory survive.
The runtime is a consequence of instruction execution, not a prescribed cost. -/
theorem decide_exec {W m b c p : ℕ} (as : List (BitVec m)) (s t : BitVec m) (x : Data 18)
    (hb : x.regs source = b) (hc : x.regs destination = c)
    (hn : x.regs modulus = 2 ^ m) (hp : x.regs cursor = p)
    (hl : x.regs limit = p + as.length)
    (hs : x.regs initial = s.toNat) (ht : x.regs target = t.toNat)
    (hinput : ∀ j (hj : j < as.length), x.mem (p + j) = as[j].toNat)
    (hout : ∀ j < as.length, ¬InBuffers b c (2 ^ m) (p + j))
    (hdisjoint : b + 2 ^ m ≤ c ∨ c + 2 ^ m ≤ b)
    (hfit : Fits W (b + c + 2 * 2 ^ m + 2)) (hinputfit : Fits W (p + as.length)) :
    ∃ y, ExecWithin W decide x y (4 * 2 ^ m + as.length * (14 * 2 ^ m + 14) + 12) ∧
      (y.regs answer = 1 ↔ Solvable as s t) ∧ y.regs answer < 2 ∧
      (∀ z, ¬InBuffers b c (2 ^ m) z → y.mem z = x.mem z) := by
  obtain ⟨z, heInit, zrep, zmem⟩ := initialize_exec x s hb hn hs (hfit.of_le (by omega))
  have preserved (i : Fin 18) (hi : initializeTable.Preserves i) : z.regs i = x.regs i :=
    heInit.regs_eq hi
  have zframe (j : ℕ) (hj : ¬InBuffers b c (2 ^ m) j) : z.mem j = x.mem j := by
    have hnot : ¬(b ≤ j ∧ j < b + 2 ^ m) := fun h => hj (Or.inl h)
    have hne : j ≠ b + s.toNat := by
      intro he
      subst j
      exact hnot ⟨by omega, by have := s.isLt; omega⟩
    rw [zmem, Function.update_of_ne hne, clear_of_not_owns hnot]
  obtain ⟨v, heLayers, vrep, vbases, vn, vp, vl, vframe⟩ := layers_exec as z
    (WordTable.point m (stateKey s)).ret
    ((preserved source (by decide)).trans hb) ((preserved destination (by decide)).trans hc)
    ((preserved modulus (by decide)).trans hn) ((preserved cursor (by decide)).trans hp)
    ((preserved limit (by decide)).trans hl)
    (fun j hj => (zframe (p + j) (hout j hj)).trans (hinput j hj))
    hout hdisjoint zrep hfit hinputfit
  have vt : v.regs target = t.toNat := by
    rw [heLayers.regs_eq (by decide), preserved target (by decide), ht]
  have haddr : Fits W (v.regs source + t.toNat) := hfit.of_le (by
    have htN := t.isLt
    rcases vbases with hv | hv <;> rw [hv.1] <;> omega)
  let y := (v.set address (v.regs source + t.toNat)).set answer
    (v.mem (v.regs source + t.toNat))
  have heLookup : ExecWithin (B := .standard) W
      (ram[ address ← source + target; answer ← *address ]) v y 2 := by
    ram_eval [y, vt, haddr, address, source, target, answer, Fin.mk.injEq]
  have hvalue : y.regs answer =
      ((WordTable.run (as.map stateKey)
        (WordTable.point m (stateKey s)).ret).ret.read t).toNat := by
    simpa only [y, Data.set_regs, Function.update_self] using vrep t
  refine ⟨y, (heInit.seq (heLayers.seq heLookup)).mono (by omega), ?_, ?_, ?_⟩
  · rw [hvalue, Bool.toNat_eq_one]
    simpa only [WordTable.decide, Cslib.Algorithms.Lean.TimeM.ret_bind,
      WordTable.lookup_ret, WordTable.read] using (WordTable.decide_correct as s t)
  · rw [hvalue]
    cases (WordTable.run (as.map stateKey)
      (WordTable.point m (stateKey s)).ret).ret.read t <;> decide
  · intro j hj
    exact (vframe j hj).trans (zframe j hj)

end Cslib.Cryptanalysis.AddXNOR.Native
