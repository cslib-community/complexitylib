/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORNativeProjectFrom
public import CslibFrontier.Cryptanalysis.AddXNORNativeEnumeration
import all CslibFrontier.Cryptanalysis.AddXNORNativeProjection

/-!
# Projecting original quarters in the native enumeration register file

The configurable projection loop is reused by register renaming, with all setup
charged. Its input is an original full-width operand array, and its conclusion
constructs the exact projected array in either order while framing other memory.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Quarter

open Cslib.WordRAM

/-- Embed the existing eighteen-register projection kernel into this register file. -/
abbrev counterRegs (r : Fin 18) : Fin 32 := r.castLE (by decide)

private theorem counterRegs_injective : Function.Injective counterRegs := by
  intro i j hij
  exact Fin.ext (congrArg (fun r : Fin 32 => r.val) hij)

/-- Projection-kernel modulus register in the enumeration register file. -/
abbrev projMod := counterRegs Native.modulus
/-- Projection-kernel destination register. -/
abbrev projDest := counterRegs Native.destination
/-- Projection-kernel operand count register. -/
abbrev projCount := counterRegs Native.limit

/-- Native projection/reversal with three charged layout transfers. -/
@[expose] def projectQuarter (a b n N : ℕ) (back : Bool) : Code .standard 32 :=
  .seq (ram[ projMod ← #N;
    projDest ← #b; projCount ← #n ])
    ((Counters.projectFrom a back).rename counterRegs)

/-- Exact projected array constructed from original operands, in either order. -/
theorem projectQuarter_exec {W m p a b : ℕ} (back : Bool) (as : List (BitVec m))
    (x : Data 32) (hinput : ∀ i (hi : i < as.length), x.mem (a + i) = as[i].toNat)
    (hsep : a + as.length ≤ b) (hfit : Fits W (b + as.length + 2 ^ p + 6)) :
    ∃ y, ExecWithin W (projectQuarter a b as.length (2 ^ p) back) x y
        (10 * as.length + 8) ∧
      y.mem = Counters.projectedPrefix x.mem b
        ((if back then as.reverse else as).map (BitVec.setWidth p)) as.length ∧
      (∀ z, ¬(b ≤ z ∧ z < b + as.length) → y.mem z = x.mem z) := by
  have hpos := Nat.two_pow_pos p
  let ps := (if back then as.reverse else as).map (BitVec.setWidth p)
  have hlen : ps.length = as.length := by cases back <;> simp [ps]
  let z := x.set (counterRegs Native.modulus) (2 ^ p)
    |>.set (counterRegs Native.destination) b |>.set (counterRegs Native.limit) as.length
  have setup : ExecWithin (B := .standard) W
      (ram[ projMod ← #(2 ^ p);
        projDest ← #b; projCount ← #as.length ]) x z 3 := by
    have hN : Fits W (2 ^ p) := hfit.of_le (by omega)
    have hb : Fits W b := hfit.of_le (by omega)
    have hn : Fits W as.length := hfit.of_le (by omega)
    ram_eval [z, hN, hb, hn, projMod, projDest, projCount, counterRegs,
      Native.modulus, Native.destination, Native.limit,
      Fin.mk.injEq]
  obtain ⟨y, he, ym, _, _, _, _, _, _⟩ := Counters.projectFrom_exec
    (a := a) (b := b) back ps (z.comap counterRegs)
    (by simp +decide [z, counterRegs, Native.modulus, Native.destination, Native.limit])
    (by simp +decide [z, counterRegs, Native.destination, Native.limit])
    (by simp [z, hlen]) (by simpa only [hlen] using hsep)
    (by
      intro i hi
      have hi' : i < as.length := by simpa only [hlen] using hi
      cases back
      · simpa [ps, z, BitVec.toNat_setWidth] using
          congrArg (fun n => n % 2 ^ p) (hinput i hi')
      · have hr := congrArg (fun n => n % 2 ^ p)
          (hinput (as.length - 1 - i) (by omega))
        simpa [ps, z, BitVec.toNat_setWidth, List.getElem_reverse, Nat.sub_sub] using hr)
    (by simpa only [hlen] using hfit)
  refine ⟨y.extend counterRegs z, ?_, ?_, ?_⟩
  · exact (setup.seq (he.rename counterRegs_injective)).mono (by rw [hlen]; omega)
  · change y.mem = _
    simpa only [Data.comap_mem, z, Data.set_mem, hlen, ps] using ym
  · intro q hq
    change y.mem q = x.mem q
    rw [ym]
    simp only [Counters.projectedPrefix, hlen, hq, ↓reduceIte, Data.comap_mem, z, Data.set_mem]

end Cslib.Cryptanalysis.AddXNOR.Native.Quarter
