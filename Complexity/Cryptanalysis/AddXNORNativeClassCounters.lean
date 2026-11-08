/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORNativeQuarterProjection
public import Complexity.Cryptanalysis.AddXNORNativeBalance
import all Complexity.Cryptanalysis.AddXNORNativeQuarterProjection
import all Complexity.Cryptanalysis.AddXNORNativeCounters
import all Complexity.Cryptanalysis.AddXNORNativeProjection

/-!
# Native projected class counters at configurable addresses

Construct projected operands from original arrays and execute the existing native
multiplicity-preserving counter kernel. Forward halves use their ordinary order
and seed; backward halves use reversed operands and the complemented target.
This makes both counter tables available before any full class is retained, as
required by [WangLvShenZhang2027], Lemma 8/Theorem 7, PDF pp. 21–22.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Quarter

open Cslib.WordRAM

/-- Native counter layout transfer, including both reusable buffers. -/
@[expose] def countSetup (q B n N seed : ℕ) : Code .standard 18 :=
  ram[ source ← #B; destination ← #(B + N); Native.modulus ← #N;
    cursor ← #q; limit ← #(q + n); Native.initial ← #seed ]

/-- Project an original array and count every indexed operator word natively. -/
@[expose] def countHalf (a q B n N seed : ℕ) : Code .standard 32 :=
  .seq (projectQuarter a q n N false)
    ((Code.seq (countSetup q B n N seed) Counters.preprocess).rename counterRegs)

/-- Actual counter values, buffer address and outside-memory frame from raw
original operands. Neither projected operands nor counter contents are premises. -/
theorem countHalf_exec {W m p a q B : ℕ} (as : List (BitVec m)) (s : BitVec m)
    (x : Data 32) (hinput : ∀ i (hi : i < as.length), x.mem (a + i) = as[i].toNat)
    (hsource : a + as.length ≤ q) (hproject : q + as.length ≤ B)
    (hfit : Fits W (a + q + 2 * B + as.length + 4 * 2 ^ p +
      2 * 2 ^ as.length + 2 ^ m + 12)) :
    ∃ y, ExecWithin W (countHalf a q B as.length (2 ^ p) (s.setWidth p).toNat) x y
        ((10 * as.length + 8) + (6 +
          (4 * 2 ^ p + as.length * (14 * 2 ^ p + 14) + 10))) ∧
      Counters.Represents y.mem (y.regs (counterRegs source))
        (WordTable.classCounters (as.map (BitVec.setWidth p)) (s.setWidth p)) ∧
      (y.regs (counterRegs source) = B ∨ y.regs (counterRegs source) = B + 2 ^ p) ∧
      (∀ z, z < q ∨ B + 2 * 2 ^ p ≤ z → y.mem z = x.mem z) := by
  have na := Nat.zero_le a
  have nb := Nat.zero_le B
  have nq := Nat.zero_le q
  have nl := Nat.zero_le (as.length)
  have np := Nat.zero_le (2 ^ p)
  have ne := Nat.zero_le (2 ^ as.length)
  have nm := Nat.zero_le (2 ^ m)
  obtain ⟨z, hz, zm, zframe⟩ := projectQuarter_exec (p := p) false as x hinput hsource
    (hfit.of_le (by omega))
  let u := (z.comap counterRegs).set source B |>.set destination (B + 2 ^ p)
    |>.set Native.modulus (2 ^ p) |>.set cursor q |>.set limit (q + as.length)
    |>.set Native.initial (s.setWidth p).toNat
  have setup : ExecWithin W (countSetup q B as.length (2 ^ p) (s.setWidth p).toNat)
      (z.comap counterRegs) u 6 := by
    have hb : Fits W B := hfit.of_le (by omega)
    have hc : Fits W (B + 2 ^ p) := hfit.of_le (by omega)
    have hn : Fits W (2 ^ p) := hfit.of_le (by omega)
    have hq : Fits W q := hfit.of_le (by omega)
    have hl : Fits W (q + as.length) := hfit.of_le (by omega)
    have hs : Fits W (s.setWidth p).toNat :=
      hfit.of_le (by have := (s.setWidth p).isLt; omega)
    ram_eval [countSetup, u, hb, hc, hn, hq, hl, hs, source, destination, Native.modulus,
      cursor, limit, Native.initial, Fin.mk.injEq]
  obtain ⟨y, hy, yr, yp, _, _, _, yf⟩  := Counters.preprocess_exec
    (b := B) (c := B + 2 ^ p) (p := q)
    (as.map (BitVec.setWidth p)) (s.setWidth p) u
    (by simp +decide [u, source, destination, Native.modulus, cursor, limit, Native.initial])
    (by simp +decide [u, destination, Native.modulus, cursor, limit, Native.initial])
    (by simp +decide [u, Native.modulus, cursor, limit, Native.initial])
    (by simp +decide [u, cursor, limit, Native.initial])
    (by simp +decide [u, limit, Native.initial]) (by simp [u])
    (by
      intro i hi
      change z.mem _ = _
      rw [zm]
      have hi' : i < as.length := by simpa using hi
      simp [Counters.projectedPrefix, hi'])
    (by intro i hi; simp only [InBuffers, List.length_map] at *; omega)
    (Or.inl (by omega))
    (hfit.of_le (by simp only [List.length_map]; omega))
    (hfit.of_le (by simp only [List.length_map]; omega))
  refine ⟨y.extend counterRegs z, ?_, ?_, ?_, ?_⟩
  · simpa only [countHalf, List.length_map] using
      hz.seq ((setup.seq hy).rename counterRegs_injective)
  · simpa only [Data.extend, counterRegs_injective.extend_apply] using yr
  · simp only [Data.extend, counterRegs_injective.extend_apply]
    exact yp.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  · intro v hv
    change y.mem v = x.mem v
    rw [yf v (by simp only [InBuffers]; omega)]
    exact zframe v (by omega)

end Cslib.Cryptanalysis.AddXNOR.Native.Quarter
