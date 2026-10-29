/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Notation

/-!
# Charged in-place normalization of an array

`ArrayNormalize.program` replaces each word of a supplied interval by its remainder modulo a
supplied positive modulus. It executes actual loads, remainders and stores; the untouched
memory need not already be normalized. This small topic module avoids adding an application
specific transformation to the allocation API.
-/

public section

namespace Cslib.WordRAM.ArrayNormalize

/-- First address to normalize. -/
abbrev base : Fin 7 := 0
/-- Number of words. -/
abbrev length : Fin 7 := 1
/-- Positive normalization modulus. -/
abbrev modulus : Fin 7 := 2
/-- Current index. -/
abbrev index : Fin 7 := 3
/-- Temporary absolute address. -/
abbrev address : Fin 7 := 4
/-- Loaded and normalized word. -/
abbrev value : Fin 7 := 5
/-- Constant one. -/
abbrev one : Fin 7 := 6

/-- Normalize one cell with five actual native instructions. -/
@[expose] def body : Code .standard 7 := ram[
  address ← base + index; value ← *address; value ← value % modulus;
  *address ← value; index ← index + one ]

/-- Fixed code for in-place normalization of an interval supplied in registers. -/
@[expose] def program : Code .standard 7 :=
  .seq (ram[ index ← #0; one ← #1 ]) (.loop (.lt index length) body)

/-- Mathematical memory after normalizing a prefix; this is not a machine operation. -/
def normalizePrefix (mem : ℕ → ℕ) (b M k : ℕ) : ℕ → ℕ :=
  fun a => if b ≤ a ∧ a < b + k then mem a % M else mem a

/-- Every cell in the normalized interval contains its original remainder. -/
theorem normalizePrefix_read (mem : ℕ → ℕ) (b M n j : ℕ) (hj : j < n) :
    normalizePrefix mem b M n (b + j) = mem (b + j) % M := by
  simp [normalizePrefix, hj]

/-- Normalizing an interval leaves all outside memory unchanged. -/
theorem normalizePrefix_outside (mem : ℕ → ℕ) (b M n a : ℕ)
    (ha : ¬(b ≤ a ∧ a < b + n)) : normalizePrefix mem b M n a = mem a := by
  simp [normalizePrefix, ha]

private theorem normalizePrefix_succ (mem : ℕ → ℕ) (b M k : ℕ) :
    normalizePrefix mem b M (k + 1) =
      Function.update (normalizePrefix mem b M k) (b + k) (mem (b + k) % M) := by
  funext a
  by_cases ha : a = b + k
  · subst a; simp [normalizePrefix]
  · simp only [normalizePrefix, Function.update_of_ne ha]
    have h : (b ≤ a ∧ a < b + (k + 1)) ↔ (b ≤ a ∧ a < b + k) := by omega
    simp only [h]

private theorem normalizePrefix_zero (mem : ℕ → ℕ) (b M : ℕ) :
    normalizePrefix mem b M 0 = mem := by
  funext a
  simp [normalizePrefix]

/-- In-place normalization costs at most `7n+4` native instructions, including every indexed
load/store and loop decision. The input arguments and all outside memory are preserved. -/
theorem exec {W b M n : ℕ} (x : Data 7) (hb : x.regs base = b)
    (hn : x.regs length = n) (hm : x.regs modulus = M) (hM : 0 < M)
    (hfit : Fits W (b + n + M + 2)) :
    ∃ y, ExecWithin W program x y (7 * n + 4) ∧ y.mem = normalizePrefix x.mem b M n ∧
      y.regs base = b ∧ y.regs length = n ∧ y.regs modulus = M := by
  have h0 : Fits W 0 := fits_zero _
  have h1 : Fits W 1 := hfit.of_le (by omega)
  let start := (x.set index 0).set one 1
  have hs : ExecWithin (B := .standard) W (ram[ index ← #0; one ← #1 ]) x start 2 := by
    ram_eval [start, h0, h1]
  let I (y : Data 7) : Prop := y.regs base = b ∧ y.regs length = n ∧
    y.regs modulus = M ∧ y.regs one = 1 ∧ y.regs index ≤ n ∧
    y.mem = normalizePrefix x.mem b M (y.regs index)
  have hi : I start := by
    simp [I, start, normalizePrefix_zero, hb, hn, hm, base, length, modulus, index, one]
  have step (y : Data 7) (hy : I y) (hc : (Cond.lt index length).Holds y) :
      ∃ z, ExecWithin W body y z 5 ∧ I z ∧ n - z.regs index < n - y.regs index := by
    obtain ⟨yb, yn, ym, yo, yi, ymem⟩ := hy
    have hlt : y.regs index < n := by simpa only [Cond.holds_lt, yn] using hc
    have ha : Fits W (b + y.regs index) := hfit.of_le (by omega)
    have hv : Fits W (x.mem (b + y.regs index) % M) :=
      hfit.of_le ((Nat.mod_lt _ hM).le.trans (by omega))
    have hj : Fits W (y.regs index + 1) := hfit.of_le (by omega)
    have hread : y.mem (b + y.regs index) = x.mem (b + y.regs index) := by
      rw [ymem]
      simp [normalizePrefix]
    let z := ((((y.set address (b + y.regs index)).set value
      (x.mem (b + y.regs index))).set value
      (x.mem (b + y.regs index) % M)).write (b + y.regs index)
        (x.mem (b + y.regs index) % M)).set index (y.regs index + 1)
    have he : ExecWithin W body y z 5 := by
      ram_eval [body, z, yb, ym, yo, hread, ha, hv, hj,
        base, length, modulus, index, address, value, one, Fin.mk.injEq]
    refine ⟨z, he, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa +decide [z, Function.update_apply] using yb
      · simpa +decide [z, Function.update_apply] using yn
      · simpa +decide [z, Function.update_apply] using ym
      · simpa +decide [z, Function.update_apply] using yo
      · simpa +decide [z, Function.update_apply] using (show y.regs index + 1 ≤ n by omega)
      · simpa +decide only [z, Data.set_regs, Data.set_mem, Data.write_regs, Data.write_mem,
          Function.update_apply, ymem, index, address, value, one, Fin.reduceEq, ↓reduceIte] using
          (normalizePrefix_succ x.mem b M (y.regs index)).symm
    · simp only [z, Data.set_regs, Function.update_self]
      omega
  obtain ⟨y, he, hy, hc⟩ := ExecWithin.loop_invariant I (fun y => n - y.regs index) step hi
  have hj : y.regs index = n := by
    have := hy.2.2.2.2.1
    simp only [Cond.holds_lt, hy.2.1] at hc
    omega
  refine ⟨y, ?_, ?_, hy.1, hy.2.1, hy.2.2.1⟩
  · apply (hs.seq he).mono
    have hstart : start.regs index = 0 := by simp [start, index, one]
    rw [hstart]
    omega
  · simpa only [hj] using hy.2.2.2.2.2

end Cslib.WordRAM.ArrayNormalize
