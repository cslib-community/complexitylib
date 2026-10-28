/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.RadixSort.Deduplicate
public import Complexity.Computability.WordRAM.Time

/-!
# Fixed-code native sorting and multiplicity construction from machine input

The input is the ordinary native list of unsigned words. The code reads its length and the
physical word width, and uses that width as an explicit key-bit bound. The lower-level
`deduplicateCode` accepts a smaller caller-supplied bit bound when known.
The standard-input wrapper's charged bound is `O(n * w)` for positive `n` and `w`.

The key array starts at `1+2n`, the count array at `1+3n`; the return value is their common
logical length. The two sorting buffers occupy `[1,1+2n)`. The implementation accepts repeated
keys, zero keys and canonical signed integer encodings. Its order is unsigned encoding order.

## Main definitions

* `inputCode`, `program`: the complete structured and flat native programs.
* `layoutWidth`: a logarithmic width sufficient for all four array blocks.

## Main results

* `input_exec`: charged execution from ordinary native input, with exact key/count output.
* `layout_fits`: logarithmic-width layout fit, including empty input.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.RadixSort

open Cslib.WordRAM

/-- Read the native input header and width, then sort and construct both output arrays. -/
def inputCode : Code .standard 16 :=
  .seq (ram[ addr ← #0; len ← *addr; src ← #1; dst ← src + len; bits ← width% ])
    deduplicateCode

/-- The fixed native instruction list, returning the number of unique keys. -/
def program : Program .standard 16 := inputCode.program Deduplicate.out

/-- A logarithmic layout-width schedule; the key magnitude bound is independent. -/
def layoutWidth (n : ℕ) : ℕ := logWidth 3 (n + 1)

/-- Four array blocks and both initialization constants fit at the layout-width threshold.
This does not by itself bound input key magnitudes. -/
theorem layout_fits (n : ℕ) : Fits (layoutWidth n) (1 + 4 * n) ∧ Fits (layoutWidth n) 2 := by
  have hs : 4 ≤ (n + 2) ^ 2 := Nat.pow_le_pow_left (show 2 ≤ n + 2 by omega) 2
  have hm := Nat.mul_le_mul_right (n + 2) hs
  have hp : 4 * (n + 2) ≤ (n + 2) ^ 3 := by simpa only [Nat.pow_succ] using hm
  constructor
  · apply fits_of_lt_pow
    have he : n + 1 + 1 = n + 2 := by omega
    rw [he]
    omega
  · apply fits_of_lt_pow
    have he : n + 1 + 1 = n + 2 := by omega
    rw [he]
    omega

/-- Execute the complete finite native program on the standard input convention. The bound
includes the final halt and every setup/address/control instruction. Input fit and the explicit
`4n+1` layout fit are independent requirements. Empty and singleton inputs need no exceptions.
The output words enumerate exactly the input set and each stored count is its full multiplicity. -/
theorem input_exec {w : ℕ} (xs : List ℕ) (hinput : InputFits w xs)
    (hfit : Fits w (1 + 4 * xs.length)) (h2 : Fits w 2) :
    ∃ (y : Data 16) (rs : List (ℕ × ℕ)) (steps : ℕ),
      Exec w inputCode (Data.init xs) y steps ∧
      Executes w program (State.init xs) rs.length (steps + 1) ∧
      steps + 1 ≤ deduplicateTime xs.length w + 6 ∧
      Block.HoldsList (1 + 2 * xs.length) (rs.map Prod.fst) y.mem ∧
      Block.HoldsList (1 + 3 * xs.length) (rs.map Prod.snd) y.mem ∧
      (rs.map Prod.fst).Nodup ∧
      (rs.map Prod.fst).Pairwise (· < ·) ∧
      (∀ k, k ∈ rs.map Prod.fst ↔ k ∈ xs) ∧
      (∀ p ∈ rs, 0 < p.2 ∧ xs.count p.1 = p.2) ∧
      Modifies (Block.mk 1 (4 * xs.length)).footprint (Data.init xs : Data 16).mem y.mem := by
  let x := Data.init xs (r := 16)
  have h1 := h2.of_le (show 1 ≤ 2 by omega)
  have had : Fits w (1 + xs.length) := hfit.of_le (by omega)
  let u := ((((x.set addr 0).set len xs.length).set src 1).set dst (1 + xs.length)).set bits w
  have hi : ExecWithin w
      (ram[ addr ← #0; len ← *addr; src ← #1; dst ← src + len; bits ← width% ]) x u 5 := by
    ram_eval [u, x, Data.init_mem_zero, h1, had]
  have hn : u.regs len = xs.length := by simp +decide [u]
  have hs : u.regs src = 1 := by simp +decide [u]
  have hd : u.regs dst = 1 + xs.length := by simp +decide [u]
  have hb : u.regs bits = w := by simp [u]
  have hm : Block.HoldsList 1 xs u.mem := by
    intro i
    change (Data.init xs : Data 16).mem (1 + i.val) = xs[i.val]
    rw [Nat.add_comm, Data.init_mem_succ]
    simp only [List.getD, List.getElem?_eq_getElem i.isLt, Option.getD_some]
  obtain ⟨y, rs, he, hyout, hyrk, hyrc, hnodup, hordered, hset, hcount, hframe⟩ :=
    deduplicate_exec xs u hn hs hd hb hm hinput.2 hinput.2 hfit (fits_self w) h2
  obtain ⟨steps, hsteps, hexec⟩ := hi.seq he
  refine ⟨y, rs, steps, hexec, ?_, by omega, hyrk, hyrc, hnodup, hordered, hset, hcount, hframe⟩
  simpa only [program, inputCode, hyout, State.init, x] using hexec.executes Deduplicate.out

end Cslib.Algorithms.WordRAM.RadixSort
