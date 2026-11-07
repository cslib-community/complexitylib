/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORNativeResources
public import Complexity.Cryptanalysis.AddXNORClasses

/-!
# Native low-bit counter sweeps

The counting refinement of the native reachable-state sweep adds both predecessor
counters, including when the two inverse addresses coincide. Every read, addition,
store and loop test is a standard-basis WordRAM instruction. The fit hypothesis
charges room for the sum of two bounded counters as well as addresses.

The complete forward counter preprocessing for [WangLvShenZhang2027],
Lemma 8, PDF pp. 21–22, is certified from encoded input through halt. Its
transcript bounds accessed storage. `AddXNORNativeProjection` reuses this kernel
for original-input projection and both counter directions. The complete native
streaming dissection remains unproved.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Counters

open Cslib.WordRAM

/-- One table entry: address arithmetic, two loads, counter addition and one store. -/
@[expose] def body : Code .standard 18 := ram[
  left ← negative + index; left ← left % modulus;
  address ← source + left; left ← *address;
  right ← index ^^^ mask; right ← right ^^^ operand;
  address ← source + right; right ← *address;
  value ← left + right; address ← destination + index;
  *address ← value; index ← index + one ]

/-- A single fixed program sweeps all states at every supplied width. -/
@[expose] def sweep : Code .standard 18 :=
  .seq (ram[ index ← #0; one ← #1; mask ← modulus - one;
    negative ← modulus - operand ]) (.loop (.lt index modulus) body)

/-- Mathematical specification of a partially filled destination array;
not an executable primitive. -/
def updatePrefix (mem : ℕ → ℕ) (b c N a k : ℕ) : ℕ → ℕ :=
  fun z => if c ≤ z ∧ z < c + k then
    mem (b + ((N - a + (z - c)) % N)) +
      mem (b + (((z - c) ^^^ (N - 1)) ^^^ a)) else mem z

private theorem updatePrefix_zero (mem : ℕ → ℕ) (b c N a : ℕ) :
    updatePrefix mem b c N a 0 = mem := by
  funext z
  simp [updatePrefix]

private theorem updatePrefix_succ (mem : ℕ → ℕ) (b c N a k : ℕ) :
    updatePrefix mem b c N a (k + 1) = Function.update (updatePrefix mem b c N a k) (c + k)
      (mem (b + ((N - a + k) % N)) + mem (b + ((k ^^^ (N - 1)) ^^^ a))) := by
  funext z
  by_cases hz : z = c + k
  · subst z; simp [updatePrefix]
  · simp only [updatePrefix, Function.update_of_ne hz]
    have h : (c ≤ z ∧ z < c + (k + 1)) ↔ (c ≤ z ∧ z < c + k) := by omega
    simp only [h]

/-- Every initialized output cell contains the sum of both predecessor counters. -/
theorem updatePrefix_read (mem : ℕ → ℕ) (b c N a k j : ℕ) (hj : j < k) :
    updatePrefix mem b c N a k (c + j) =
      mem (b + ((N - a + j) % N)) + mem (b + ((j ^^^ (N - 1)) ^^^ a)) := by
  simp [updatePrefix, hj]

/-- No store outside the destination prefix is hidden by the specification. -/
theorem updatePrefix_outside (mem : ℕ → ℕ) (b c N a k z : ℕ)
    (hz : ¬(c ≤ z ∧ z < c + k)) : updatePrefix mem b c N a k z = mem z := by
  simp [updatePrefix, hz]

/-- Native full-array execution, including initialization of scratch registers and
all loop control. Only the destination buffer changes. Dirty destination memory
is permitted. A supplied counter source table is required, not presumed free. -/
theorem sweep_exec {W m b c a C : ℕ} (x : Data 18)
    (hb : x.regs source = b) (hc : x.regs destination = c)
    (hn : x.regs modulus = 2 ^ m) (ha : x.regs operand = a)
    (haN : a < 2 ^ m) (hdisjoint : b + 2 ^ m ≤ c ∨ c + 2 ^ m ≤ b)
    (hflags : ∀ j < 2 ^ m, x.mem (b + j) ≤ C)
    (hfit : Fits W (b + c + 2 * 2 ^ m + 2 * C + 2)) :
    ∃ y, ExecWithin W sweep x y (14 * 2 ^ m + 6) ∧
      y.mem = updatePrefix x.mem b c (2 ^ m) a (2 ^ m) ∧
      y.regs source = b ∧ y.regs destination = c ∧
      y.regs modulus = 2 ^ m ∧ y.regs operand = a := by
  have hN : 0 < 2 ^ m := Nat.two_pow_pos m
  have h0 : Fits W 0 := fits_zero _
  have h1 : Fits W 1 := hfit.of_le (by omega)
  have hmask : Fits W (2 ^ m - 1) := hfit.of_le (by omega)
  have hneg : Fits W (2 ^ m - a) := hfit.of_le (by omega)
  let start := (((x.set index 0).set one 1).set mask (2 ^ m - 1)).set negative (2 ^ m - a)
  have hs : ExecWithin (B := .standard) W
      (ram[ index ← #0; one ← #1; mask ← modulus - one; negative ← modulus - operand ])
      x start 4 := by
    ram_eval [start, hb, hc, hn, ha, h0, h1, hmask, hneg,
      source, destination, modulus, operand, index, one, mask, negative, Fin.mk.injEq]
  let I (y : Data 18) : Prop :=
    y.regs source = b ∧ y.regs destination = c ∧ y.regs modulus = 2 ^ m ∧
    y.regs operand = a ∧ y.regs one = 1 ∧ y.regs mask = 2 ^ m - 1 ∧
    y.regs negative = 2 ^ m - a ∧ y.regs index ≤ 2 ^ m ∧
    y.mem = updatePrefix x.mem b c (2 ^ m) a (y.regs index)
  have hi : I start := by
    simp [I, start, updatePrefix_zero, hb, hc, hn, ha,
      source, destination, modulus, operand, index, one, mask, negative]
  have step (y : Data 18) (hy : I y) (ht : (Cond.lt index modulus).Holds y) :
      ∃ z, ExecWithin W body y z 12 ∧ I z ∧
        2 ^ m - z.regs index < 2 ^ m - y.regs index := by
    obtain ⟨yb, yc, yn, ya, yo, ym, yg, yi, ymem⟩ := hy
    have hj : y.regs index < 2 ^ m := by simpa only [Cond.holds_lt, yn] using ht
    have hx1 := Nat.xor_lt_two_pow hj (show 2 ^ m - 1 < 2 ^ m by omega)
    have hx2 := Nat.xor_lt_two_pow hx1 haN
    have hadd : Fits W (2 ^ m - a + y.regs index) := hfit.of_le (by omega)
    have hmod : Fits W ((2 ^ m - a + y.regs index) % 2 ^ m) :=
      hfit.of_le (by have := Nat.mod_lt (2 ^ m - a + y.regs index) hN; omega)
    have hxor1 : Fits W (y.regs index ^^^ (2 ^ m - 1)) := hfit.of_le (by omega)
    have hxor2 : Fits W ((y.regs index ^^^ (2 ^ m - 1)) ^^^ a) := hfit.of_le (by omega)
    have haddr1 : Fits W (b + ((2 ^ m - a + y.regs index) % 2 ^ m)) :=
      hfit.of_le (by have := Nat.mod_lt (2 ^ m - a + y.regs index) hN; omega)
    have haddr2 : Fits W (b + ((y.regs index ^^^ (2 ^ m - 1)) ^^^ a)) :=
      hfit.of_le (by omega)
    have haddr3 : Fits W (c + y.regs index) := hfit.of_le (by omega)
    have hnext : Fits W (y.regs index + 1) := hfit.of_le (by omega)
    have hread (j : ℕ) (hj : j < 2 ^ m) : y.mem (b + j) = x.mem (b + j) := by
      rw [ymem, updatePrefix_outside]
      rcases hdisjoint with hd | hd <;> omega
    let l := x.mem (b + ((2 ^ m - a + y.regs index) % 2 ^ m))
    let r := x.mem (b + ((y.regs index ^^^ (2 ^ m - 1)) ^^^ a))
    have hl : l ≤ C := hflags _ (Nat.mod_lt _ hN)
    have hr : r ≤ C := hflags _ hx2
    have hv : Fits W (l + r) := by
      exact hfit.of_le (by omega)
    let z := y.set left (2 ^ m - a + y.regs index)
      |>.set left ((2 ^ m - a + y.regs index) % 2 ^ m)
      |>.set address (b + ((2 ^ m - a + y.regs index) % 2 ^ m))
      |>.set left l
      |>.set right (y.regs index ^^^ (2 ^ m - 1))
      |>.set right ((y.regs index ^^^ (2 ^ m - 1)) ^^^ a)
      |>.set address (b + ((y.regs index ^^^ (2 ^ m - 1)) ^^^ a))
      |>.set right r
      |>.set value (l + r)
      |>.set address (c + y.regs index)
      |>.write (c + y.regs index) (l + r)
      |>.set index (y.regs index + 1)
    have he : ExecWithin W body y z 12 := by
      ram_eval [body, z, l, r, yb, yc, yn, ya, yo, ym, yg,
        hread _ (Nat.mod_lt _ hN), hread _ hx2, hadd, hmod, hxor1, hxor2,
        haddr1, haddr2, haddr3, hnext, hv, source, destination, modulus,
        operand, index, one, address, left, right, mask, negative, value, Fin.mk.injEq]
    refine ⟨z, he, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals simp +decide only [z, Data.set_regs, Data.set_mem,
        Data.write_regs, Data.write_mem, Function.update_apply, source, destination,
        modulus, operand, index, one, address, left, right, mask, negative, value,
        ↓reduceIte]
      · exact yb
      · exact yc
      · exact yn
      · exact ya
      · exact yo
      · exact ym
      · exact yg
      · simpa only [index] using (Nat.succ_le_iff.mpr hj)
      · simpa only [l, r, ymem] using (updatePrefix_succ x.mem b c (2 ^ m) a (y.regs index)).symm
    · simp only [z, Data.set_regs, Function.update_self]
      omega
  obtain ⟨y, he, hy, ht⟩ := ExecWithin.loop_invariant I (fun y => 2 ^ m - y.regs index) step hi
  have hj : y.regs index = 2 ^ m := by
    have := hy.2.2.2.2.2.2.2.1
    simp only [Cond.holds_lt, hy.2.2.1] at ht
    omega
  refine ⟨y, ?_, ?_, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1⟩
  · apply (hs.seq he).mono
    have hstart : start.regs index = 0 := by simp [start, index, one, mask, negative]
    rw [hstart]
    omega
  · simpa only [hj] using hy.2.2.2.2.2.2.2.2

/-- A native array stores actual natural counters, rather than Boolean flags. -/
@[expose] def Represents {m : ℕ} (mem : ℕ → ℕ) (b : ℕ)
    (table : WordTable ℕ m) : Prop :=
  ∀ s : BitVec m, mem (b + s.toNat) = table.read s

/-- The physical counter sweep implements the existing multiplicity-preserving
recurrence. In particular a coincident predecessor contributes twice. -/
theorem updatePrefix_represents {m : ℕ} (mem : ℕ → ℕ) (b c : ℕ)
    (a : BitVec m) (table : WordTable ℕ m) (h : Represents mem b table) :
    Represents (updatePrefix mem b c (2 ^ m) a.toNat (2 ^ m)) c
      (WordTable.countAdvance (stateKey a) table).ret := by
  intro s
  rw [updatePrefix_read _ _ _ _ _ _ _ s.isLt, WordTable.countAdvance_read]
  have hadd := h (s - a)
  have hxor := h (s ^^^ (~~~a))
  rw [BitVec.toNat_sub] at hadd
  rw [BitVec.toNat_xor, BitVec.toNat_not] at hxor
  have hmask : (s.toNat ^^^ (2 ^ m - 1)) ^^^ a.toNat =
      s.toNat ^^^ (2 ^ m - 1 - a.toNat) := by
    have he := congrArg BitVec.toNat
      (show s ^^^ BitVec.allOnes m ^^^ a = s ^^^ (~~~a) by
        rw [BitVec.xor_assoc, BitVec.allOnes_xor])
    simpa only [BitVec.toNat_xor, BitVec.toNat_not, Nat.xor_comm,
      Nat.xor_assoc, BitVec.toNat_allOnes] using he
  rw [hmask, hadd, hxor]
  simp [unstep, BitVec.not_xor_right]

/-- A complete native counter layer, including all scratch initialization and loop
control, accepts dirty destination storage and preserves every other cell. -/
theorem advance_exec {W m b c C : ℕ} (x : Data 18) (a : BitVec m)
    (table : WordTable ℕ m) (hb : x.regs source = b) (hc : x.regs destination = c)
    (hn : x.regs modulus = 2 ^ m) (ha : x.regs operand = a.toNat)
    (hdisjoint : b + 2 ^ m ≤ c ∨ c + 2 ^ m ≤ b)
    (hrep : Represents x.mem b table) (hcount : ∀ s, table.read s ≤ C)
    (hfit : Fits W (b + c + 2 * 2 ^ m + 2 * C + 2)) :
    ∃ y, ExecWithin W sweep x y (14 * 2 ^ m + 6) ∧
      Represents y.mem c (WordTable.countAdvance (stateKey a) table).ret ∧
      y.mem = updatePrefix x.mem b c (2 ^ m) a.toNat (2 ^ m) ∧
      y.regs source = b ∧ y.regs destination = c ∧
      y.regs modulus = 2 ^ m ∧ y.regs operand = a.toNat := by
  have hflags (j : ℕ) (hj : j < 2 ^ m) : x.mem (b + j) ≤ C := by
    have hr := hrep (BitVec.ofNat m j)
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj] at hr
    rw [hr]
    exact hcount _
  obtain ⟨y, he, hm, hr⟩ := sweep_exec x hb hc hn ha a.isLt hdisjoint hflags hfit
  exact ⟨y, he, hm ▸ updatePrefix_represents x.mem b c a table hrep, hm, hr⟩

/-- One operand load, one actual sweep, then exchange the reusable buffers. -/
@[expose] def iteration : Code .standard 18 :=
  .seq (.op (.load operand cursor)) (.seq sweep
    (ram[ temporary ← source; source ← destination; destination ← temporary;
      temporary ← #1; cursor ← cursor + temporary ]))

/-- Fixed native loop over the supplied operands. -/
@[expose] def layers : Code .standard 18 := .loop (.lt cursor limit) iteration

/-- The native loop refines every layer of the unrestricted word semantics.
The input table is an explicit prerequisite here; initialization is separate.
All operand reads, buffer exchanges and outer loop tests are charged. -/
theorem layers_exec {W m b c p C : ℕ} (as : List (BitVec m)) (x : Data 18)
    (table : WordTable ℕ m)
    (hb : x.regs source = b) (hc : x.regs destination = c)
    (hn : x.regs modulus = 2 ^ m) (hp : x.regs cursor = p)
    (hl : x.regs limit = p + as.length)
    (hinput : ∀ j (hj : j < as.length), x.mem (p + j) = as[j].toNat)
    (hout : ∀ j < as.length, ¬InBuffers b c (2 ^ m) (p + j))
    (hdisjoint : b + 2 ^ m ≤ c ∨ c + 2 ^ m ≤ b)
    (hrep : Represents x.mem b table)
    (hcount : ∀ s, table.read s ≤ C)
    (hfit : Fits W (b + c + 2 * 2 ^ m + 2 * C * 2 ^ as.length + 2))
    (hinputfit : Fits W (p + as.length)) :
    ∃ y, ExecWithin W layers x y (as.length * (14 * 2 ^ m + 14) + 2) ∧
      Represents y.mem (y.regs source) (WordTable.countRun (as.map stateKey) table).ret ∧
      ((y.regs source = b ∧ y.regs destination = c) ∨
        (y.regs source = c ∧ y.regs destination = b)) ∧
      y.regs modulus = 2 ^ m ∧ y.regs cursor = p + as.length ∧
      y.regs limit = p + as.length ∧
      (∀ z, ¬InBuffers b c (2 ^ m) z → y.mem z = x.mem z) := by
  induction as generalizing x table b c p C with
  | nil =>
    refine ⟨x, ?_, ?_, Or.inl ⟨hb, hc⟩, hn, ?_, ?_, fun _ _ => rfl⟩
    · simp only [List.length_nil, Nat.zero_mul, Nat.zero_add, layers]
      exact ExecWithin.loop_exit (by simp [Cond.holds_lt, hp, hl])
    · simpa only [List.map_nil, WordTable.countRun, hb] using hrep
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
      advance_exec loaded a table lb lc ln (by simp [loaded]) hdisjoint hrep hcount (hfit.of_le (by
        have hp : 1 ≤ 2 ^ (a :: as).length := Nat.one_le_two_pow
        have := Nat.mul_le_mul_left (2 * C) hp
        omega))
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
    have nrep : Represents next.mem c (WordTable.countAdvance (stateKey a) table).ret := by
      simpa only [next, Data.set_mem] using zrep
    have nextCount (s : BitVec m) :
        (WordTable.countAdvance (stateKey a) table).ret.read s ≤ 2 * C := by
      rw [WordTable.countAdvance_read]
      have := hcount (unstep false s a)
      have := hcount (unstep true s a)
      omega
    obtain ⟨y, heTail, yrep, ybases, yn, yp, yl, yframe⟩ := ih next
      (WordTable.countAdvance (stateKey a) table).ret nb nc nn np nl ninput nout
      (by omega) nrep nextCount (by
        apply hfit.of_le
        simp only [List.length_cons, pow_succ]
        nlinarith [Nat.mul_assoc (2 * C) 2 (2 ^ as.length)])
      (by simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using hinputfit)
    refine ⟨y, ?_, ?_, ?_, yn, ?_, ?_, ?_⟩
    · have heStep := heLoad.seq (heSweep.seq heSwap)
      have he := ExecWithin.loop_iter (cond := .lt cursor limit)
        (by simp [Cond.holds_lt, hp, hl]) heStep heTail
      apply he.mono
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
    · simpa only [List.map_cons, WordTable.countRun, Cslib.Algorithms.Lean.TimeM.ret_bind,
        Cslib.Algorithms.Lean.TimeM.ret_pure] using yrep
    · exact ybases.elim Or.inr Or.inl
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using yp
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using yl
    · intro j hj
      rw [yframe j (by simpa only [InBuffers, or_comm] using hj), frame j hj]


/-- Initialize the zero/one counter table with the already certified native
zero-fill and singleton store. No host table is installed. -/
theorem initialize_exec {W m b : ℕ} (x : Data 18) (s : BitVec m)
    (hb : x.regs source = b) (hn : x.regs modulus = 2 ^ m)
    (hs : x.regs initial = s.toNat) (hfit : Fits W (b + 2 ^ m + 2)) :
    ∃ y, ExecWithin W initializeTable x y (4 * 2 ^ m + 8) ∧
      Represents y.mem b (WordTable.indicators (WordTable.point m (stateKey s)).ret) ∧
      y.mem = Function.update (clear x.mem b (2 ^ m)) (b + s.toNat) 1 := by
  obtain ⟨y, he, hr, hm⟩ := Native.initialize_exec x s hb hn hs hfit
  refine ⟨y, he, ?_, hm⟩
  intro t
  rw [WordTable.indicators_read, hr]
  cases (WordTable.point m (stateKey s)).ret.read t <;> rfl

/-- Complete forward counter preprocessing: native initialization and all layers.
The final table, its current buffer, and the unchanged input interval are certified.
The source and destination buffers can be reused by subsequent class processing. -/
@[expose] def preprocess : Code .standard 18 := .seq initializeTable layers

theorem preprocess_exec {W m b c p : ℕ} (as : List (BitVec m))
    (s : BitVec m) (x : Data 18)
    (hb : x.regs source = b) (hc : x.regs destination = c)
    (hn : x.regs modulus = 2 ^ m) (hp : x.regs cursor = p)
    (hl : x.regs limit = p + as.length) (hs : x.regs initial = s.toNat)
    (hinput : ∀ j (hj : j < as.length), x.mem (p + j) = as[j].toNat)
    (hout : ∀ j < as.length, ¬InBuffers b c (2 ^ m) (p + j))
    (hdisjoint : b + 2 ^ m ≤ c ∨ c + 2 ^ m ≤ b)
    (hfit : Fits W (b + c + 2 * 2 ^ m + 2 * 2 ^ as.length + 2))
    (hinputfit : Fits W (p + as.length)) :
    ∃ y, ExecWithin W preprocess x y
        (4 * 2 ^ m + as.length * (14 * 2 ^ m + 14) + 10) ∧
      Represents y.mem (y.regs source) (WordTable.classCounters as s) ∧
      ((y.regs source = b ∧ y.regs destination = c) ∨
        (y.regs source = c ∧ y.regs destination = b)) ∧
      y.regs modulus = 2 ^ m ∧ y.regs cursor = p + as.length ∧
      y.regs limit = p + as.length ∧
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
    (WordTable.indicators (WordTable.point m (stateKey s)).ret)
    ((preserved source (by decide)).trans hb) ((preserved destination (by decide)).trans hc)
    ((preserved modulus (by decide)).trans hn) ((preserved cursor (by decide)).trans hp)
    ((preserved limit (by decide)).trans hl)
    (fun j hj => (zframe (p + j) (hout j hj)).trans (hinput j hj))
    hout hdisjoint zrep
    (C := 1) (by intro t; rw [WordTable.indicators_read]; split <;> omega)
    (by simpa only [mul_one] using hfit) hinputfit
  refine ⟨v, (heInit.seq heLayers).mono (by omega), vrep, vbases, vn, vp, vl, ?_⟩
  intro j hj
  exact (vframe j hj).trans (zframe j hj)

/-- Counter preprocessing uses the native header reader and two alternating arrays. -/
@[expose] def entry : Code .standard 18 := .seq setup preprocess

/-- Physical words fit counters as well as memory addresses. Counter width is
linear in the number of operands; it is not suppressed in storage claims. -/
@[expose] def wordWidth (m q : ℕ) : ℕ :=
  (3 * 2 ^ m + 2 * q + 2 * 2 ^ q + 12).log2 + 1

/-- All intermediate addresses and counter sums fit the chosen width. -/
theorem layout_fits (m q : ℕ) :
    Fits (wordWidth m q) (3 * 2 ^ m + 2 * q + 2 * 2 ^ q + 12) := Nat.lt_log2_self

/-- The header and every counter layer are executed from the actual encoded
input. All input cells survive, and the returned pointer identifies the final table. -/
theorem entry_exec {m : ℕ} (as : List (BitVec m)) (s t : BitVec m) (x : Data 18)
    (hm : x.mem 1 = m) (hs : x.mem 2 = s.toNat) (ht : x.mem 3 = t.toNat)
    (hq : x.mem 4 = as.length)
    (hinput : ∀ j (hj : j < as.length), x.mem (5 + j) = as[j].toNat) :
    ∃ y, ExecWithin (wordWidth m as.length) entry x y
        (4 * 2 ^ m + as.length * (14 * 2 ^ m + 14) + 24) ∧
      Represents y.mem (y.regs source) (WordTable.classCounters as s) ∧
      (∀ z, z < as.length + 5 → y.mem z = x.mem z) := by
  have hfit := layout_fits m as.length
  have h1 : Fits (wordWidth m as.length) 1 := hfit.of_le (by omega)
  have h2 : Fits (wordWidth m as.length) 2 := hfit.of_le (by omega)
  have h3 : Fits (wordWidth m as.length) 3 := hfit.of_le (by omega)
  have h4 : Fits (wordWidth m as.length) 4 := hfit.of_le (by omega)
  have h5 : Fits (wordWidth m as.length) 5 := hfit.of_le (by omega)
  have hN : Fits (wordWidth m as.length) (2 ^ m) := hfit.of_le (by omega)
  have hend : Fits (wordWidth m as.length) (as.length + 5) := hfit.of_le (by omega)
  have hbuffer : Fits (wordWidth m as.length) (as.length + 5 + 2 ^ m) := hfit.of_le (by omega)
  let z := x.set address 1
    |>.set modulus m |>.set one 1 |>.set modulus (2 ^ m)
    |>.set address 2 |>.set initial s.toNat
    |>.set address 3 |>.set target t.toNat
    |>.set address 4 |>.set limit as.length |>.set cursor 5
    |>.set limit (as.length + 5) |>.set source (as.length + 5)
    |>.set destination (as.length + 5 + 2 ^ m)
  have heSetup : ExecWithin (wordWidth m as.length) setup x z 14 := by
    ram_eval [setup, z, hm, hs, ht, hq, h1, h2, h3, h4, h5, hN, hend, hbuffer,
      Nat.shiftLeft_eq, one_mul, address, modulus, one, initial, target, limit, cursor,
      source, destination, Fin.mk.injEq]
  have zb : z.regs source = as.length + 5 := by
    simp +decide [z, source, destination]
  have zc : z.regs destination = as.length + 5 + 2 ^ m := by simp [z]
  have zn : z.regs modulus = 2 ^ m := by
    simp +decide [z, address, modulus, one, initial, target, limit, cursor, source, destination]
  have zp : z.regs cursor = 5 := by
    simp +decide [z, address, modulus, one, initial, target, limit, cursor, source, destination]
  have zl : z.regs limit = 5 + as.length := by
    simp +decide [z, address, modulus, one, initial, target, limit, cursor, source, destination,
      Nat.add_comm]
  have zs : z.regs initial = s.toNat := by
    simp +decide [z, address, modulus, one, initial, target, limit, cursor, source, destination]
  obtain ⟨y, heDecide, hy, _, _, _, _, hframe⟩ := preprocess_exec as s z zb zc zn zp zl zs
    hinput (by intro j hj; simp only [InBuffers]; omega) (Or.inl (by omega))
    (hfit.of_le (by omega)) (hfit.of_le (by omega))
  refine ⟨y, (heSetup.seq heDecide).mono (by omega), hy, ?_⟩
  intro j hj
  exact hframe j (by simp only [InBuffers]; omega)

/-- The complete preprocessing program is fixed, deterministic and width-oblivious. -/
theorem entry_fixed : entry.IsRandFree ∧ ¬entry.ReadsWidth := by decide

/-- All standard input words, including the header, fit the counter word width. -/
theorem encodeInput_fits {m : ℕ} (as : List (BitVec m)) (s t : BitVec m) :
    InputFits (wordWidth m as.length) (encodeInput as s t) := by
  have hfit := layout_fits m as.length
  refine ⟨hfit.of_le (by simp [encodeInput]; omega), ?_⟩
  intro v hv
  simp only [encodeInput, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map] at hv
  have hmN := Nat.lt_two_pow_self (n := m)
  rcases hv with (rfl | rfl | rfl | rfl) | ⟨a, _, rfl⟩
  · exact hfit.of_le (by omega)
  · exact hfit.of_le (by have := s.isLt; omega)
  · exact hfit.of_le (by have := t.isLt; omega)
  · exact hfit.of_le (by omega)
  · exact hfit.of_le (by have := a.isLt; omega)

/-- Standard input-to-halt execution returns the actual counter-array pointer.
Reading any cell of that array gives the existing indexed solution count.
Initialization, headers, all counter additions and halt are charged. -/
theorem encoded_counts {m q : ℕ} (as : Fin q → BitVec m) (s t : BitVec m) :
    ∃ y n ts,
      n ≤ 4 * 2 ^ m + q * (14 * 2 ^ m + 14) + 24 ∧
      TraceExec (wordWidth m q) entry (Data.init (encodeInput (List.ofFn as) s t)) y n ts ∧
      Executes (wordWidth m q) (entry.program source)
        (State.init (encodeInput (List.ofFn as) s t)) (y.regs source) (n + 1) ∧
      (∀ g : BitVec m, y.mem (y.regs source + g.toNat) = solutionCount as s g) ∧
      ts.length ≤ n := by
  have operand (j : ℕ) (hj : j < (List.ofFn as).length) :
      (Data.init (encodeInput (List.ofFn as) s t) : Data 18).mem (5 + j) =
        (List.ofFn as)[j].toNat := by
    rw [show 5 + j = (j + 4) + 1 by omega, Data.init_mem_succ,
      List.getD_eq_getElem?_getD]
    rw [encodeInput, List.getElem?_append_right (by change 4 ≤ j + 4; omega)]
    simp only [List.length_ofFn] at hj
    simp [hj]
  obtain ⟨y, he, hr, _⟩ :=
    entry_exec (List.ofFn as) s t (Data.init (encodeInput (List.ofFn as) s t))
    (by simp [Data.init_mem_succ, encodeInput, List.getD_eq_getElem?_getD])
    (by simp [Data.init_mem_succ, encodeInput, List.getD_eq_getElem?_getD])
    (by simp [Data.init_mem_succ, encodeInput, List.getD_eq_getElem?_getD])
    (by simp [Data.init_mem_succ, encodeInput, List.getD_eq_getElem?_getD]) operand
  obtain ⟨n, hn, he⟩ := he
  obtain ⟨ts, ht⟩ := he.exists_trace
  refine ⟨y, n, ts, by simpa using hn, by simpa using ht,
    by simpa only [State.init, List.length_ofFn] using he.executes source, ?_, ht.length_le⟩
  intro g
  rw [hr g, WordTable.classCounters_read]

/-- Native preprocessing has a complete time and accessed-storage certificate.
The footprint includes every prefix's accessed cells, and the register bank is
included in the bit bound. The bound by time is deliberately conservative; it
avoids equating the counter word's entire address capacity with allocated space. -/
theorem encoded_resources {m q : ℕ} (as : Fin q → BitVec m) (s t : BitVec m) :
    ∃ y n ts,
      n + 1 ≤ 43 * (q + 1) * 2 ^ m ∧
      TraceExec (wordWidth m q) entry (Data.init (encodeInput (List.ofFn as) s t)) y n ts ∧
      Executes (wordWidth m q) (entry.program source)
        (State.init (encodeInput (List.ofFn as) s t)) (y.regs source) (n + 1) ∧
      (∀ g : BitVec m, y.mem (y.regs source + g.toNat) = solutionCount as s g) ∧
      ((Probe.reads ts ∪ Probe.writes ts).card + 18) * wordWidth m q ≤
        (43 * (q + 1) * 2 ^ m + 18) * wordWidth m q := by
  obtain ⟨y, n, ts, hn, ht, he, hr, _⟩ := encoded_counts as s t
  have hb : n + 1 ≤ 43 * (q + 1) * 2 ^ m := by
    have hp : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    have hq := Nat.mul_le_mul_left q hp
    nlinarith
  refine ⟨y, n, ts, hb, ht, he, hr, ?_⟩
  exact Nat.mul_le_mul_right _ (by have := ht.footprint_le; omega)

end Cslib.Cryptanalysis.AddXNOR.Native.Counters
