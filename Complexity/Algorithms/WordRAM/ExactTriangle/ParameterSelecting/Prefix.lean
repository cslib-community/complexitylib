/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.Flat
public import Complexity.Computability.WordRAM.Width
import Complexity.Foundations.Data.Nat.Log

/-!
# Original-data bounds for every assembled-solver prefix

The actual complete execution at minimum admission controls every prefix at every wider
word size. Caller admission includes the original raw-word bound before dirty loads. This
extra hypothesis is confined to numerical resource results; semantic execution on arbitrary
old data still uses `exec_at`. No comparison run is supplied by the caller.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting

open Cslib.WordRAM

/-- Resource admission includes the original caller's raw words, before normalization. -/
@[expose] def admissionWidth (n F b ap bp cp P : ℕ) (values : List ℤ) : ℕ :=
  Nat.clog 2 (envelope n F b ap bp cp values + P + 1) + 3

/-- A physical-width-independent numerical bound for all words and newly written addresses. -/
@[expose] def wordBound (n F b ap bp cp P : ℕ) (values : List ℤ) : ℕ :=
  16 * (envelope n F b ap bp cp values + P + 1)

/-- Caller resource admission is positive, including empty inputs and zero bounds. -/
theorem admissionWidth_pos (n F b ap bp cp P : ℕ) (values : List ℤ) :
    0 < admissionWidth n F b ap bp cp P values := by unfold admissionWidth; omega

/-- Resource admission implies the weaker semantic execution admission. -/
theorem executionWidth_le_admissionWidth (n F b ap bp cp P : ℕ) (values : List ℤ) :
    executionWidth n F b ap bp cp values ≤ admissionWidth n F b ap bp cp P values := by
  unfold executionWidth admissionWidth
  exact Nat.add_le_add_right (Nat.clog_mono_right 2 (by omega)) 3

/-- Powers of the resource threshold stay within the original-data envelope. -/
theorem pow_admissionWidth_le (n F b ap bp cp P : ℕ) (values : List ℤ) :
    2 ^ admissionWidth n F b ap bp cp P values ≤ wordBound n F b ap bp cp P values := by
  let E := envelope n F b ap bp cp values + P + 1
  have hp := Nat.pow_clog_le_mul (by decide : 1 < (2 : ℕ)) (by dsimp only [E]; omega : E ≠ 0)
  change 2 ^ (Nat.clog 2 E + 3) ≤ 16 * E
  rw [pow_add]
  norm_num only [Nat.reducePow]
  omega

/-- Raw caller data fit at the resource threshold, before any actual remainder instruction. -/
theorem original_bounded {W n F b ap bp cp P : ℕ} (values : List ℤ) (x : Data 640)
    (hregs : ∀ i, x.regs i ≤ P) (hmem : ∀ q, x.mem q ≤ P)
    (hW : admissionWidth n F b ap bp cp P values ≤ W) : x.Bounded W := by
  have hp : P < 2 ^ W := by
    have hle := Nat.le_pow_clog (by decide : 1 < (2 : ℕ))
      (envelope n F b ap bp cp values + P + 1)
    have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ))
      (show Nat.clog 2 (envelope n F b ap bp cp values + P + 1) ≤ W by
        unfold admissionWidth at hW; omega)
    omega
  exact ⟨fun i => (hregs i).trans_lt hp, fun q => (hmem q).trans_lt hp⟩

/-- Every actual caller prefix has a width-independent bound. The semantic solver proves
the comparison run itself; arbitrary unused old words are bounded only in this theorem. -/
theorem bounded_reachable_caller {W n F ap bp cp b P k : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hv : ∀ z ∈ values, z.natAbs ≤ F)
    (x : Data 640) (xn : x.regs Reg.side = n) (xF : x.regs Reg.bound = F)
    (xap : x.regs Reg.ab = ap) (xbp : x.regs Reg.bc = bp)
    (xcp : x.regs Reg.ac = cp) (xb : x.regs Reg.free = b)
    (hab : ap + n * n ≤ b) (hbc : bp + n * n ≤ b) (hac : cp + n * n ≤ b)
    (vab : ∀ q < n * n, x.mem (ap + q) = Signed.encode (values.getD q 0))
    (vbc : ∀ q < n * n, x.mem (bp + q) = Signed.encode (values.getD (n * n + q) 0))
    (vac : ∀ q < n * n, x.mem (cp + q) = Signed.encode (values.getD (2 * (n * n) + q) 0))
    (hregs : ∀ i, x.regs i ≤ P) (hmem : ∀ q, x.mem q ≤ P)
    (hW : admissionWidth n F b ap bp cp P values ≤ W)
    {s : State 640} (hr : Runs W (program.program Reg.result) ⟨0, x⟩ s k) :
    (∀ i, s.data.regs i < wordBound n F b ap bp cp P values) ∧
      (∀ q, s.data.mem q < wordBound n F b ap bp cp P values) ∧
      ∀ q, wordBound n F b ap bp cp P values ≤ q → s.data.mem q = x.mem q := by
  let w := admissionWidth n F b ap bp cp P values
  have hx : x.Bounded w := original_bounded values x hregs hmem le_rfl
  obtain ⟨p, mem, y, he, _⟩ := exec_at values hlen hv x xn xF xap xbp xcp xb
    hab hbc hac vab vbc vac (executionWidth_le_admissionWidth n F b ap bp cp P values)
  obtain ⟨t, ht, hex⟩ := he
  have hlow := Runs.prefix_at_smaller_width program_fixed.2 hW hr (hex.executes Reg.result)
  have hs := hlow.bounded hx
  have hpow := pow_admissionWidth_le n F b ap bp cp P values
  refine ⟨fun i => (hs.1 i).trans_le hpow, fun q => (hs.2 q).trans_le hpow, ?_⟩
  exact fun q hq => hlow.mem_above hx (hpow.trans hq)

/-- The initialized program has no physical-width-dependent word or address support. -/
theorem bounded_reachable_input {W n F k : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hv : ∀ z ∈ values, z.natAbs ≤ F)
    (hW : inputWidth n F values ≤ W) {s : State 640}
    (hr : Runs W (entryProgram.program Reg.result)
      (State.init (CountPrime.inputWords n F values)) s k) :
    let E := envelope n F (3 + 3 * (n * n)) 3 (3 + n * n) (3 + 2 * (n * n)) values
    (∀ i, s.data.regs i < 16 * E) ∧ (∀ q, s.data.mem q < 16 * E) ∧
      ∀ q, 16 * E ≤ q → s.data.mem q = 0 := by
  obtain ⟨hi, p, mem, y, t, ht, hpref, he, _⟩ := runs_input values hlen hv le_rfl
  have hlow := Runs.prefix_at_smaller_width entryProgram_fixed.2 hW hr he
  have hx := Data.Bounded.init (r := 640) hi
  have hs := hlow.bounded hx
  let E := envelope n F (3 + 3 * (n * n)) 3 (3 + n * n) (3 + 2 * (n * n)) values
  have hpow : 2 ^ inputWidth n F values ≤ 16 * E := by
    have hp := Nat.pow_clog_le_mul (by decide : 1 < (2 : ℕ))
      (by dsimp only [E, envelope]; omega : E ≠ 0)
    change 2 ^ (Nat.clog 2 E + 3) ≤ 16 * E
    rw [pow_add]
    norm_num only [Nat.reducePow]
    omega
  refine ⟨fun i => (hs.1 i).trans_le hpow, fun q => (hs.2 q).trans_le hpow, ?_⟩
  intro q hq
  have hq' : 2 ^ inputWidth n F values ≤ q := hpow.trans hq
  rw [hlow.mem_above hx hq']
  cases q with
  | zero => have := Nat.two_pow_pos (inputWidth n F values); omega
  | succ q =>
    change (CountPrime.inputWords n F values).getD q 0 = 0
    apply List.getD_eq_default
    have hlen := hi.1
    dsimp only [Fits] at hlen
    omega

end Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting
