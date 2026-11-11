/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORNativeCounters

/-!
# Native projection and reversal for counter preprocessing

The low-bit instance in [WangLvShenZhang2027], Lemma 8, PDF pp. 21–22,
is constructed by native reads, remainders and stores. Backward preprocessing
uses reversed operands and complement conjugacy, reusing the forward counter
kernel. This module charges construction rather than installing a projected
instance as free input. It does not certify the class enumerator or dissection.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Counters

open Cslib.WordRAM

/-- Copy one projected operand, optionally reading the input in reverse order. -/
@[expose] def projectBody (back : Bool) : Code .standard 18 :=
  .seq (if back then ram[ address ← limit - cursor; address ← address - one;
      address ← address + negative ] else ram[ address ← cursor + negative ])
    (ram[ operand ← *address; operand ← operand % modulus;
      address ← destination + cursor; *address ← operand; cursor ← cursor + one ])

/-- A single loop constructs a disjoint projected operand array. -/
@[expose] def projectOperands (back : Bool) : Code .standard 18 :=
  .seq (ram[ cursor ← #0; one ← #1; negative ← #5 ])
    (.loop (.lt cursor limit) (projectBody back))

/-- Mathematical description of the cells actually written by projection. -/
def projectedPrefix {p : ℕ} (mem : ℕ → ℕ) (b : ℕ)
    (as : List (BitVec p)) (k : ℕ) : ℕ → ℕ :=
  fun z => if b ≤ z ∧ z < b + k then (as[z - b]!).toNat else mem z

private theorem projectedPrefix_zero {p : ℕ} (mem : ℕ → ℕ) (b : ℕ)
    (as : List (BitVec p)) : projectedPrefix mem b as 0 = mem := by
  funext z
  simp [projectedPrefix]

private theorem projectedPrefix_succ {p : ℕ} (mem : ℕ → ℕ) (b : ℕ)
    (as : List (BitVec p)) (k : ℕ) :
    projectedPrefix mem b as (k + 1) =
      Function.update (projectedPrefix mem b as k) (b + k) as[k]!.toNat := by
  funext z
  by_cases hz : z = b + k
  · subst z; simp [projectedPrefix]
  · simp only [projectedPrefix, Function.update_of_ne hz]
    have he : (b ≤ z ∧ z < b + (k + 1)) ↔ (b ≤ z ∧ z < b + k) := by omega
    simp only [he]

/-- Every source read, remainder, store, loop test and initialization is charged.
The source is disjoint from the destination, so even reverse reads cannot consume
an operand already overwritten by the copy. Other cells and the initial-state
register are preserved. The destination may contain arbitrary old data. -/
theorem projectOperands_exec {W p b : ℕ} (back : Bool) (as : List (BitVec p))
    (x : Data 18) (hn : x.regs modulus = 2 ^ p)
    (hb : x.regs destination = b) (hq : x.regs limit = as.length)
    (hsep : 5 + as.length ≤ b)
    (hinput : ∀ j (hj : j < as.length),
      x.mem (5 + if back then as.length - 1 - j else j) % 2 ^ p = as[j].toNat)
    (hfit : Fits W (b + as.length + 2 ^ p + 6)) :
    ∃ y, ExecWithin W (projectOperands back) x y (10 * as.length + 5) ∧
      y.mem = projectedPrefix x.mem b as as.length ∧
      y.regs modulus = 2 ^ p ∧ y.regs destination = b ∧
      y.regs limit = as.length ∧ y.regs cursor = as.length ∧
      y.regs initial = x.regs initial ∧ y.regs one = 1 := by
  have hN := Nat.two_pow_pos p
  have h0 : Fits W 0 := fits_zero _
  have h1 : Fits W 1 := hfit.of_le (by omega)
  have h5 : Fits W 5 := hfit.of_le (by omega)
  let start := ((x.set cursor 0).set one 1).set negative 5
  have hs : ExecWithin (B := .standard) W
      (ram[ cursor ← #0; one ← #1; negative ← #5 ]) x start 3 := by
    ram_eval [start, h0, h1, h5, cursor, one, negative, Fin.mk.injEq]
  let I (y : Data 18) : Prop :=
    y.regs modulus = 2 ^ p ∧ y.regs destination = b ∧
    y.regs limit = as.length ∧ y.regs one = 1 ∧ y.regs negative = 5 ∧
    y.regs cursor ≤ as.length ∧
    y.mem = projectedPrefix x.mem b as (y.regs cursor) ∧
    y.regs initial = x.regs initial
  have hi : I start := by
    simp [I, start, projectedPrefix_zero, hn, hb, hq,
      modulus, destination, limit, one, negative, cursor, initial]
  have step (y : Data 18) (hy : I y) (ht : (Cond.lt cursor limit).Holds y) :
      ∃ z, ExecWithin W (projectBody back) y z 8 ∧ I z ∧
        as.length - z.regs cursor < as.length - y.regs cursor := by
    obtain ⟨yn, yb, yq, yo, yg, yj, ym, yi⟩ := hy
    have hj : y.regs cursor < as.length := by simpa only [Cond.holds_lt, yq] using ht
    let j := y.regs cursor
    let r := if back then as.length - 1 - j else j
    have hr : r < as.length := by dsimp [r]; split <;> omega
    have hread : y.mem (5 + r) % 2 ^ p = as[j]!.toNat := by
      rw [ym]
      have hout : ¬(b ≤ 5 + r ∧ 5 + r < b + y.regs cursor) := by omega
      simp only [projectedPrefix, hout, ↓reduceIte]
      simpa only [r, j, getElem!_pos as j hj] using hinput j hj
    have haddr : Fits W (5 + r) := hfit.of_le (by omega)
    have hdest : Fits W (b + j) := hfit.of_le (by omega)
    have hnext : Fits W (j + 1) := hfit.of_le (by omega)
    have hvalue : Fits W as[j]!.toNat := hfit.of_le (by have := as[j]!.isLt; omega)
    let loaded := y.set address (5 + r)
    have heRead : ExecWithin (B := .standard) W
        (if back then ram[ address ← limit - cursor; address ← address - one;
          address ← address + negative ] else ram[ address ← cursor + negative ])
        y loaded 3 := by
      cases back
      · have he : 5 + r = y.regs cursor + 5 := by simp [r, j, Nat.add_comm]
        have hf : Fits W (y.regs cursor + 5) := he ▸ haddr
        have hrun : ExecWithin (B := .standard) W
            (ram[ address ← cursor + negative ]) y loaded 1 := by
          ram_eval [loaded, yo, yg, hf, he, address, cursor, negative, Fin.mk.injEq]
        exact hrun.mono (by omega)
      · have hr' : r = as.length - y.regs cursor - 1 := by dsimp [r, j]; omega
        have hf : Fits W (as.length - y.regs cursor) := hfit.of_le (by omega)
        have hf' : Fits W (as.length - y.regs cursor - 1) := hfit.of_le (by omega)
        have hf'' : Fits W (as.length - y.regs cursor - 1 + 5) := by
          simpa only [hr', Nat.add_comm] using haddr
        have hrun : ExecWithin (B := .standard) W
            (ram[ address ← limit - cursor; address ← address - one;
              address ← address + negative ]) y
            (y.set address (as.length - y.regs cursor)
              |>.set address (as.length - y.regs cursor - 1)
              |>.set address (as.length - y.regs cursor - 1 + 5)) 3 := by
          ram_eval [yq, yo, yg, hf, hf', hf'', address, limit, cursor, one,
            negative, Fin.mk.injEq]
        simpa [loaded, hr', Nat.add_comm, Data.set] using hrun
    let z := loaded.set operand (y.mem (5 + r))
      |>.set operand as[j]!.toNat |>.set address (b + j)
      |>.write (b + j) as[j]!.toNat |>.set cursor (j + 1)
    have heWrite : ExecWithin (B := .standard) W
        (ram[ operand ← *address; operand ← operand % modulus;
          address ← destination + cursor; *address ← operand; cursor ← cursor + one ])
        loaded z 5 := by
      ram_eval [z, loaded, hread, yn, yb, yo, hvalue, hdest, hnext,
        address, operand, modulus, destination, cursor, one, j, Fin.mk.injEq]
    refine ⟨z, heRead.seq heWrite, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals simp +decide only [z, loaded, Data.set_regs, Data.set_mem,
        Data.write_regs, Data.write_mem, Function.update_apply,
        modulus, destination, limit, one, negative, cursor, initial, address, operand,
        ↓reduceIte]
      · exact yn
      · exact yb
      · exact yq
      · exact yo
      · exact yg
      · exact Nat.succ_le_iff.mpr hj
      · simpa only [j, ym] using (projectedPrefix_succ x.mem b as (y.regs cursor)).symm
      · exact yi
    · simp only [z, Data.set_regs, Function.update_self, j]
      omega
  obtain ⟨y, he, hy, ht⟩ := ExecWithin.loop_invariant I
    (fun y => as.length - y.regs cursor) step hi
  have hj : y.regs cursor = as.length := by
    have := hy.2.2.2.2.2.1
    simp only [Cond.holds_lt, hy.2.2.1] at ht
    omega
  refine ⟨y, ?_, ?_, hy.1, hy.2.1, hy.2.2.1, hj, hy.2.2.2.2.2.2.2, hy.2.2.2.1⟩
  · apply (hs.seq he).mono
    have hz : start.regs cursor = 0 := by simp [start, cursor, one, negative]
    rw [hz]
    omega
  · simpa only [hj] using hy.2.2.2.2.2.2.1

/-- Seed and buffer setup after the projected operands have been written. -/
@[expose] def prepareProjected (back : Bool) : Code .standard 18 :=
  .seq (.op (.bin .mod initial initial modulus))
    (.seq (if back then ram[ mask ← modulus - one; initial ← initial ^^^ mask ]
      else ram[ initial ← initial ])
      (ram[ source ← destination + limit; cursor ← destination;
        limit ← source; destination ← source + modulus ]))

/-- Projection/reversal, initialization and every counter layer form one native program. -/
@[expose] def projectedPreprocess (back : Bool) : Code .standard 18 :=
  .seq (projectOperands back) (.seq (prepareProjected back) preprocess)

/-- The combined program reads full-width operands and constructs its projected
input itself. Its initial-state register holds the full-width start (forward)
or target (backward); the caller supplies the projection modulus and disjoint
workspace. No projected table or operand array is a premise. -/
theorem projectedPreprocess_exec {W m p b : ℕ} (back : Bool)
    (as : List (BitVec p)) (seed : BitVec m) (x : Data 18)
    (hn : x.regs modulus = 2 ^ p) (hb : x.regs destination = b)
    (hq : x.regs limit = as.length) (hs : x.regs initial = seed.toNat)
    (hsep : 5 + as.length ≤ b)
    (hinput : ∀ j (hj : j < as.length),
      x.mem (5 + if back then as.length - 1 - j else j) % 2 ^ p = as[j].toNat)
    (hfit : Fits W (2 * (b + as.length) + 3 * 2 ^ p + 2 * 2 ^ as.length + 6)) :
    ∃ y, ExecWithin W (projectedPreprocess back) x y
        (4 * 2 ^ p + as.length * (14 * 2 ^ p + 24) + 23) ∧
      Represents y.mem (y.regs source)
        (WordTable.classCounters as (if back then ~~~(seed.setWidth p) else seed.setWidth p)) ∧
      (∀ z, z < b → y.mem z = x.mem z) := by
  obtain ⟨z, heCopy, zm, zn, zb, zq, zj, zs, zo⟩ :=
    projectOperands_exec back as x hn hb hq hsep hinput (hfit.of_le (by omega))
  have hseed : seed.toNat % 2 ^ p = (seed.setWidth p).toNat := by
    simp [BitVec.toNat_setWidth]
  have hlow : Fits W (seed.setWidth p).toNat :=
    hfit.of_le (by have := (seed.setWidth p).isLt; omega)
  have hmask : Fits W (2 ^ p - 1) := hfit.of_le (by omega)
  have hnot : Fits W (~~~(seed.setWidth p)).toNat :=
    hfit.of_le (by have := (~~~(seed.setWidth p)).isLt; omega)
  have hbase : Fits W (b + as.length) := hfit.of_le (by omega)
  have hdest : Fits W (b + as.length + 2 ^ p) := hfit.of_le (by omega)
  let low := z.set initial (seed.setWidth p).toNat
  have heLow : ExecWithin (B := .standard) W (.op (.bin .mod initial initial modulus)) z low 1 := by
    ram_eval [low, zs, hs, zn, hseed, hlow, initial, modulus, Fin.mk.injEq]
  let complemented := if back then
    (low.set mask (2 ^ p - 1)).set initial (~~~(seed.setWidth p)).toNat else low
  have heNot : ExecWithin (B := .standard) W
      (if back then ram[ mask ← modulus - one; initial ← initial ^^^ mask ]
      else ram[ initial ← initial ])
      low complemented 2 := by
    cases back
    · have he : ExecWithin (B := .standard) W (ram[ initial ← initial ]) low low 1 := by
        ram_eval [Data.set, Function.update_eq_self]
      exact he.mono (by omega)
    · have hx : (seed.setWidth p).toNat ^^^ (2 ^ p - 1) =
          (~~~(seed.setWidth p)).toNat := by
        simpa only [BitVec.toNat_xor, BitVec.toNat_allOnes] using
          congrArg BitVec.toNat (BitVec.xor_allOnes (x := seed.setWidth p))
      ram_eval [complemented, low, zn, zo, hmask, hnot, hx,
        initial, modulus, mask, one, Fin.mk.injEq]
  let ready := complemented.set source (b + as.length) |>.set cursor b
    |>.set limit (b + as.length) |>.set destination (b + as.length + 2 ^ p)
  have hePointers : ExecWithin (B := .standard) W
      (ram[ source ← destination + limit; cursor ← destination;
        limit ← source; destination ← source + modulus ]) complemented ready 4 := by
    have cb : complemented.regs destination = b := by
      cases back <;> simpa +decide [complemented, low, destination, initial, mask] using zb
    have cq : complemented.regs limit = as.length := by
      cases back <;> simpa +decide [complemented, low, limit, initial, mask] using zq
    have cn : complemented.regs modulus = 2 ^ p := by
      cases back <;> simpa +decide [complemented, low, modulus, initial, mask] using zn
    have hbfit : Fits W b := hfit.of_le (by omega)
    ram_eval [ready, cb, cq, cn, hbase, hdest, hbfit,
      source, destination, cursor, limit, modulus, Fin.mk.injEq]
  have rb : ready.regs source = b + as.length := by
    simp +decide [ready, source, cursor, limit, destination]
  have rc : ready.regs destination = b + as.length + 2 ^ p := by simp [ready]
  have rn : ready.regs modulus = 2 ^ p := by
    cases back <;> simpa +decide [ready, complemented, low, source, destination, cursor,
      limit, initial, mask, modulus] using zn
  have rp : ready.regs cursor = b := by simp +decide [ready, cursor, limit, destination]
  have rl : ready.regs limit = b + as.length := by simp +decide [ready, limit, destination]
  have rs : ready.regs initial =
      (if back then ~~~(seed.setWidth p) else seed.setWidth p).toNat := by
    cases back <;> simp +decide [ready, complemented, low, source, destination, cursor,
      limit, initial, mask]
  have rmem : ready.mem = projectedPrefix x.mem b as as.length := by
    cases back <;> simpa [ready, complemented, low] using zm
  have rinput (j : ℕ) (hj : j < as.length) : ready.mem (b + j) = as[j].toNat := by
    rw [rmem]
    simp [projectedPrefix, hj]
  obtain ⟨y, heCount, yr, _, _, _, _, yf⟩ := preprocess_exec as
    (if back then ~~~(seed.setWidth p) else seed.setWidth p) ready rb rc rn rp rl rs
    rinput (by intro j hj; simp only [InBuffers]; omega) (Or.inl (by omega))
    (hfit.of_le (by omega)) (hfit.of_le (by omega))
  refine ⟨y, (heCopy.seq ((heLow.seq (heNot.seq hePointers)).seq heCount)).mono (by nlinarith),
    yr, ?_⟩
  intro j hj
  rw [yf j (by simp only [InBuffers]; omega), rmem]
  simp [projectedPrefix, show ¬(b ≤ j ∧ j < b + as.length) by omega]

/-- Standard instance followed by the requested projection width. The original
width and all full-width operands remain present in the input. -/
@[expose] def encodeProjected {m : ℕ} (p : ℕ) (as : List (BitVec m))
    (s t : BitVec m) : List ℕ := encodeInput as s t ++ [p]

/-- Read the projection width and seed from the original input, reserving a
separate operand-copy interval after its last word. -/
@[expose] def setupProjected (back : Bool) : Code .standard 18 :=
  ram[ address ← #4; limit ← *address; cursor ← #5;
    address ← limit + cursor; modulus ← *address; one ← #1;
    modulus ← one <<< modulus; address ← #(if back then 3 else 2);
    initial ← *address; destination ← limit + cursor;
    destination ← destination + one ]

/-- A fixed native program, with no projected-input or backward-counter oracle. -/
@[expose] def projectedEntry (back : Bool) : Code .standard 18 :=
  .seq (setupProjected back) (projectedPreprocess back)

/-- Full-width inputs, counters and addresses all fit this word width. In
particular counters require up to `q+1` bits even when the projection is empty. -/
@[expose] def projectedWordWidth (m p q : ℕ) : ℕ :=
  (3 * 2 ^ p + 2 * 2 ^ q + 4 * q + 2 ^ m + 30).log2 + 1

/-- Original-input projection and both counter directions, including native
operand reversal, initialization and every counter addition. The backward
array is read at complemented low-bit addresses. -/
theorem projectedEntry_exec {m p : ℕ} (back : Bool)
    (as : List (BitVec m)) (s t : BitVec m) (x : Data 18)
    (hs : x.mem 2 = s.toNat) (ht : x.mem 3 = t.toNat)
    (hq : x.mem 4 = as.length) (hpInput : x.mem (as.length + 5) = p)
    (hinput : ∀ j (hj : j < as.length), x.mem (5 + j) = as[j].toNat) :
    ∃ y, ExecWithin (projectedWordWidth m p as.length) (projectedEntry back) x y
        (4 * 2 ^ p + as.length * (14 * 2 ^ p + 24) + 34) ∧
      (∀ g : BitVec p, y.mem (y.regs source +
          (if back then ~~~g else g).toNat) =
        (if back then WordTable.backwardCounters (as.map (BitVec.setWidth p)) (t.setWidth p)
          else WordTable.classCounters (as.map (BitVec.setWidth p)) (s.setWidth p)).read g) ∧
      (∀ z, z < as.length + 6 → y.mem z = x.mem z) := by
  let W := projectedWordWidth m p as.length
  have hfit : Fits W (3 * 2 ^ p + 2 * 2 ^ as.length + 4 * as.length + 2 ^ m + 30) :=
    Nat.lt_log2_self
  have h1 : Fits W 1 := hfit.of_le (by omega)
  have h2 : Fits W 2 := hfit.of_le (by omega)
  have h3 : Fits W 3 := hfit.of_le (by omega)
  have h4 : Fits W 4 := hfit.of_le (by omega)
  have h5 : Fits W 5 := hfit.of_le (by omega)
  have hN : Fits W (2 ^ p) := hfit.of_le (by omega)
  have haddr : Fits W (as.length + 5) := hfit.of_le (by omega)
  have hb : Fits W (as.length + 6) := hfit.of_le (by omega)
  let seed := if back then t else s
  let operands := (if back then as.reverse else as).map (BitVec.setWidth p)
  have hlen : operands.length = as.length := by cases back <;> simp [operands]
  let z := x.set address 4 |>.set limit as.length |>.set cursor 5
    |>.set address (as.length + 5) |>.set modulus p |>.set one 1
    |>.set modulus (2 ^ p) |>.set address (if back then 3 else 2)
    |>.set initial seed.toNat |>.set destination (as.length + 5)
    |>.set destination (as.length + 6)
  have heSetup : ExecWithin W (setupProjected back) x z 11 := by
    cases back <;> ram_eval [setupProjected, z, seed, hs, ht, hq, hpInput,
      h1, h2, h3, h4, h5, hN, haddr, hb, Nat.shiftLeft_eq, one_mul,
      address, modulus, one, initial, limit, cursor, destination, Fin.mk.injEq]
  have zn : z.regs modulus = 2 ^ p := by
    simp +decide [z, address, modulus, one, initial, limit, cursor, destination]
  have zb : z.regs destination = as.length + 6 := by simp [z]
  have zq : z.regs limit = operands.length := by
    simp +decide [z, hlen, address, modulus, one, initial, limit, cursor, destination]
  have zs : z.regs initial = seed.toNat := by simp +decide [z, initial, destination]
  have zinput (j : ℕ) (hj : j < operands.length) :
      z.mem (5 + if back then operands.length - 1 - j else j) % 2 ^ p = operands[j].toNat := by
    have hj' : j < as.length := by simpa only [hlen] using hj
    cases back
    · simpa [z, operands, BitVec.toNat_setWidth] using
        congrArg (fun n => n % 2 ^ p) (hinput j hj')
    · have hi : as.length - 1 - j < as.length := by omega
      have hr := congrArg (fun n => n % 2 ^ p) (hinput (as.length - 1 - j) hi)
      simpa [z, operands, BitVec.toNat_setWidth, List.getElem_reverse,
        Nat.sub_sub] using hr
  obtain ⟨y, he, yr, yf⟩ := projectedPreprocess_exec back operands seed z zn zb zq zs
    (by rw [hlen]; omega) zinput (hfit.of_le (by
      rw [hlen]
      have := Nat.two_pow_pos m
      omega))
  refine ⟨y, (heSetup.seq he).mono (by rw [hlen]; omega), ?_, ?_⟩
  · intro g
    cases back
    · simpa [Represents, operands, seed] using yr g
    · have hr := yr (~~~g)
      simpa [Represents, operands, seed, List.map_reverse,
        WordTable.backwardCounters_conjugate] using hr
  · intro j hj
    exact yf j (by simpa only [hlen] using hj)

/-- The full-width original input, appended projection width, length word,
all counters and all layout addresses fit the selected physical words. -/
theorem encodeProjected_fits {m p : ℕ} (hp : p ≤ m)
    (as : List (BitVec m)) (s t : BitVec m) :
    InputFits (projectedWordWidth m p as.length) (encodeProjected p as s t) := by
  have hfit : Fits (projectedWordWidth m p as.length)
      (3 * 2 ^ p + 2 * 2 ^ as.length + 4 * as.length + 2 ^ m + 30) := Nat.lt_log2_self
  have hlen : (encodeProjected p as s t).length = as.length + 5 := by
    simp [encodeProjected, encodeInput]
  refine ⟨hfit.of_le (by
    rw [hlen]
    calc
      as.length + 5 ≤ 4 * as.length + 30 := by omega
      _ ≤ (3 * 2 ^ p + 2 * 2 ^ as.length + 2 ^ m) + (4 * as.length + 30) :=
        Nat.le_add_left _ _
      _ = _ := by ac_rfl), ?_⟩
  intro v hv
  simp only [encodeProjected, encodeInput, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_map] at hv
  have hmN := Nat.lt_two_pow_self (n := m)
  rcases hv with ((rfl | rfl | rfl | rfl) | ⟨a, _, rfl⟩) | rfl
  · exact hfit.of_le (by omega)
  · exact hfit.of_le (by have := s.isLt; omega)
  · exact hfit.of_le (by have := t.isLt; omega)
  · exact hfit.of_le (by omega)
  · exact hfit.of_le (by have := a.isLt; omega)
  · exact hfit.of_le (by omega)

/-- Input-to-halt resources for original-width inputs and either low-bit count
direction. The memory certificate counts accessed cells and all registers, not
the word's address span. It conservatively bounds simultaneous occupancy by the
union of all accessed cells; input installation follows `Data.init` conventions.
This is preprocessing, not an integrated dissection space theorem. -/
theorem encoded_projected_resources {m p q : ℕ} (back : Bool) (hp : p ≤ m)
    (as : Fin q → BitVec m) (s t : BitVec m) :
    ∃ y n ts,
      n + 1 ≤ 77 * (q + 1) * 2 ^ p ∧
      TraceExec (projectedWordWidth m p q) (projectedEntry back)
        (Data.init (encodeProjected p (List.ofFn as) s t)) y n ts ∧
      Executes (projectedWordWidth m p q) ((projectedEntry back).program source)
        (State.init (encodeProjected p (List.ofFn as) s t)) (y.regs source) (n + 1) ∧
      (∀ g : BitVec p, y.mem (y.regs source + (if back then ~~~g else g).toNat) =
        if back then backwardClassCount p as t g else forwardClassCount p as s g) ∧
      ((Probe.reads ts ∪ Probe.writes ts).card + 18) * projectedWordWidth m p q ≤
        (77 * (q + 1) * 2 ^ p + 18) * projectedWordWidth m p q ∧
      (∀ k u, Runs (projectedWordWidth m p q) ((projectedEntry back).program source)
        (State.init (encodeProjected p (List.ofFn as) s t)) u k → k ≤ n →
        u.data.Bounded (projectedWordWidth m p q) ∧ ∃ live : Finset ℕ,
          (∀ a, u.data.mem a ≠ 0 → a ∈ live) ∧
          (live.card + 18) * projectedWordWidth m p q ≤
            (77 * (q + 1) * 2 ^ p + q + 24) * projectedWordWidth m p q) := by
  let input := encodeProjected p (List.ofFn as) s t
  have h2 : (Data.init input : Data 18).mem 2 = s.toNat := by
    simp [input, Data.init_mem_succ, encodeProjected, encodeInput,
      List.getD_eq_getElem?_getD]
  have h3 : (Data.init input : Data 18).mem 3 = t.toNat := by
    simp [input, Data.init_mem_succ, encodeProjected, encodeInput,
      List.getD_eq_getElem?_getD]
  have h4 : (Data.init input : Data 18).mem 4 = (List.ofFn as).length := by
    simp [input, Data.init_mem_succ, encodeProjected, encodeInput,
      List.getD_eq_getElem?_getD]
  have hpInput : (Data.init input : Data 18).mem ((List.ofFn as).length + 5) = p := by
    rw [show (List.ofFn as).length + 5 = ((List.ofFn as).length + 4) + 1 by omega,
      Data.init_mem_succ]
    simp [input, encodeProjected, encodeInput, List.getD_eq_getElem?_getD]
  have operands (j : ℕ) (hj : j < (List.ofFn as).length) :
      (Data.init input : Data 18).mem (5 + j) = (List.ofFn as)[j].toNat := by
    rw [show 5 + j = (j + 4) + 1 by omega, Data.init_mem_succ]
    simp only [List.length_ofFn] at hj
    simp [input, encodeProjected, encodeInput, List.getD_eq_getElem?_getD,
      List.getElem?_append, hj]
  obtain ⟨y, he, hr, _⟩ := projectedEntry_exec back (List.ofFn as) s t (Data.init input)
    h2 h3 h4 hpInput operands
  obtain ⟨n, hn, he⟩ := he
  obtain ⟨ts, ht⟩ := he.exists_trace
  have hb : n + 1 ≤ 77 * (q + 1) * 2 ^ p := by
    simp only [List.length_ofFn] at hn
    have hN : 1 ≤ 2 ^ p := Nat.one_le_two_pow
    have := Nat.mul_le_mul_left q hN
    nlinarith
  refine ⟨y, n, ts, hb, by simpa only [List.length_ofFn] using ht,
    by simpa only [State.init, List.length_ofFn] using he.executes source, ?_, ?_, ?_⟩
  · intro g
    have h := hr g
    cases back
    · simpa only [Bool.false_eq_true, ↓reduceIte, List.map_ofFn, Function.comp_def,
        WordTable.projected_classCounters hp] using h
    · simpa only [Bool.true_eq, ↓reduceIte, List.map_ofFn, Function.comp_def,
        WordTable.projected_backwardCounters hp] using h
  · exact Nat.mul_le_mul_right _ (by have := ht.footprint_le; omega)
  · intro k u hu hk
    refine ⟨hu.bounded_init (by simpa only [List.length_ofFn] using
      (encodeProjected_fits hp (List.ofFn as) s t)), ?_⟩
    have inputSupport (a : ℕ) (ha : (State.init input : State 18).data.mem a ≠ 0) :
        a ∈ Finset.range (q + 6) := by
      apply Finset.mem_range.mpr
      by_contra hn
      have hlen : input.length = q + 5 := by simp [input, encodeProjected, encodeInput]
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show a ≠ 0 by omega)
      have hj : input.length ≤ j := by omega
      simp only [State.init, Data.init_mem_succ, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none_iff.mpr hj, Option.getD_none, ne_eq, not_true_eq_false] at ha
    obtain ⟨live, hcard, hlive⟩ := hu.exists_memorySupport (Finset.range (q + 6)) inputSupport
    refine ⟨live, hlive, Nat.mul_le_mul_right _ ?_⟩
    simp only [Finset.card_range] at hcard
    omega

end Cslib.Cryptanalysis.AddXNOR.Native.Counters
