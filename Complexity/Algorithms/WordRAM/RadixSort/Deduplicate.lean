/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.RadixSort.Program
public import Complexity.Algorithms.WordRAM.Deduplicate.Program
public import Complexity.Computability.WordRAM.Signed.Encoding

/-!
# Native radix sorting followed by unique-key/multiplicity array construction

This composes the complete native sorter and adjacent-run builder. Two length-`n` sorting
buffers are followed by length-`n` key and count output buffers. All four blocks lie in one
explicit frame. The returned keys are in unsigned encoding order; decoding signed keys does
not turn that order into signed integer order.

## Main definitions

* `deduplicateCode`: fixed 16-register sorting and multiplicity program.
* `deduplicateTime`: complete structured instruction bound.

## Main results

* `deduplicate_exec`: exact set enumeration and full multiplicities, with no sorting premise.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.RadixSort

open Cslib.WordRAM

/-- Original base retained while radix sorting swaps its two pointers. -/
abbrev origin : Fin 16 := 14

/-- Install the two output pointers after the two sorting buffers. -/
def outputLayout : Code .standard 16 := ram[
  Deduplicate.keys ← len + len; Deduplicate.keys ← Deduplicate.keys + origin;
  Deduplicate.counts ← Deduplicate.keys + len ]

/-- Complete sorting and deduplication; `Deduplicate.out` returns the number of unique words. -/
def deduplicateCode : Code .standard 16 :=
  .seq (ram[ origin ← src ]) (.seq code (.seq outputLayout Deduplicate.code))

/-- All instructions, including pointer construction and both complete algorithms, excluding
only the final halt. For positive `n` and key-bit bound this is `O(n * keyBits)`. -/
def deduplicateTime (n keyBits : ℕ) : ℕ := keyBits * (22 * n + 15) + 29 * n + 14

/-- Complete fixed-code radix sorting and adjacent deduplication, with full multiplicities.
Keys below `2^keyBits` may repeat arbitrarily. Only the four length-`n` buffers change. The
conditions constrain arithmetic/address fit, not sorting or deduplication behavior. -/
theorem deduplicate_exec {w base keyBits : ℕ} (xs : List ℕ) (x : Data 16)
    (hn : x.regs len = xs.length) (hs : x.regs src = base)
    (hd : x.regs dst = base + xs.length) (hb : x.regs bits = keyBits)
    (hmem : Block.HoldsList base xs x.mem)
    (hkeys : ∀ v ∈ xs, v < 2 ^ keyBits) (hwords : ∀ v ∈ xs, Fits w v)
    (hfit : Fits w (base + 4 * xs.length)) (hbits : Fits w keyBits) (h2 : Fits w 2) :
    ∃ (y : Data 16) (rs : List (ℕ × ℕ)),
      ExecWithin w deduplicateCode x y (deduplicateTime xs.length keyBits) ∧
      y.regs Deduplicate.out = rs.length ∧
      Block.HoldsList (base + 2 * xs.length) (rs.map Prod.fst) y.mem ∧
      Block.HoldsList (base + 3 * xs.length) (rs.map Prod.snd) y.mem ∧
      (rs.map Prod.fst).Nodup ∧
      (rs.map Prod.fst).Pairwise (· < ·) ∧
      (∀ k, k ∈ rs.map Prod.fst ↔ k ∈ xs) ∧
      (∀ p ∈ rs, 0 < p.2 ∧ xs.count p.1 = p.2) ∧
      Modifies (Block.mk base (4 * xs.length)).footprint x.mem y.mem := by
  let x₀ := x.set origin base
  have hinit : ExecWithin (B := .standard) w (ram[ origin ← src ]) x x₀ 1 := by ram_eval [x₀, hs]
  obtain ⟨u, hu, hum, hp, hsorted, hptr, huf⟩ := exec xs x₀
    (by simpa +decide [x₀] using hn) (by simpa +decide [x₀] using hs)
    (by simpa +decide [x₀] using hd) (by simpa +decide [x₀] using hb)
    hmem hkeys hwords (hfit.of_le (by omega)) hbits h2
  have hun : u.regs len = xs.length := by
    simpa +decide [x₀] using (hu.regs_eq (i := len) (by decide)).trans
      (show x₀.regs len = xs.length by simpa +decide [x₀] using hn)
  have huo : u.regs origin = base := by
    simpa only [x₀, Data.set_regs, Function.update_self] using hu.regs_eq (i := origin) (by decide)
  have htwice : Fits w (u.regs len + u.regs len) := hfit.of_le (by rw [hun]; omega)
  have hkeyaddr : Fits w (u.regs len + u.regs len + base) := hfit.of_le (by rw [hun]; omega)
  have hcntaddr : Fits w (u.regs len + u.regs len + base + u.regs len) :=
    hfit.of_le (by rw [hun]; omega)
  let v := ((u.set Deduplicate.keys (u.regs len + u.regs len)).set
    Deduplicate.keys (u.regs len + u.regs len + base)).set
    Deduplicate.counts (u.regs len + u.regs len + base + u.regs len)
  have hl : ExecWithin w outputLayout u v 3 := by
    ram_eval [v, outputLayout, huo, htwice, hkeyaddr, hcntaddr]
  have hvl : v.regs Deduplicate.len = (passes keyBits xs).length := by
    change u.regs len = (passes keyBits xs).length
    rw [hun, hp.length_eq]
  have hvs : v.regs Deduplicate.src = u.regs src := rfl
  have hvk : v.regs Deduplicate.keys = base + 2 * xs.length := by
    change u.regs len + u.regs len + base = base + 2 * xs.length
    omega
  have hvc : v.regs Deduplicate.counts = base + 3 * xs.length := by
    change u.regs len + u.regs len + base + u.regs len = base + 3 * xs.length
    omega
  have hlen : (passes keyBits xs).length = xs.length := hp.length_eq
  obtain ⟨y, rs, hy, hrs, hyout, hyrk, hyrc, _, hyf⟩ := Deduplicate.exec (passes keyBits xs) v
    hvl hvs hvk (by rw [hvc, hlen]; omega) hum hsorted
    (by rw [hlen]; rcases hptr with hptr | hptr <;> omega)
    (by rw [hlen]; exact hfit.of_le (by omega)) (h2.of_le (by omega))
  have heq : base + 2 * xs.length + xs.length = base + 3 * xs.length := by omega
  refine ⟨y, rs, ?_, hyout, hyrk, by simpa only [hlen, heq] using hyrc,
    hrs.keys_nodup, List.pairwise_map.mpr hrs.ordered, ?_, ?_, ?_⟩
  · have hall := hinit.seq (hu.seq (hl.seq hy))
    apply hall.mono
    simp only [deduplicateTime, timeBound, hlen]
    omega
  · intro k
    exact (hrs.mem_iff k).trans hp.mem_iff
  · intro p hp'
    exact ⟨hrs.positive p hp', (hp.count_eq p.1).symm.trans (hrs.multiplicity hp')⟩
  · intro a hnot
    have hnotSort : a ∉ (Block.mk base (2 * xs.length)).footprint := by
      intro ha
      apply hnot
      rw [Block.mem_footprint] at ha ⊢
      dsimp only [Block.Owns] at ha ⊢
      omega
    have hnotOut : a ∉ (Block.mk (base + 2 * xs.length)
        (2 * (passes keyBits xs).length)).footprint := by
      intro ha
      apply hnot
      rw [Block.mem_footprint] at ha ⊢
      dsimp only [Block.Owns] at ha ⊢
      rw [hlen] at ha
      omega
    exact (hyf a hnotOut).trans (huf a hnotSort)

end Cslib.Algorithms.WordRAM.RadixSort
