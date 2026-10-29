/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.NodeExec

/-!
# Exact output contract for complete native Chan–He node construction

The output uses the existing mathematical heavy subsets and `Node.oneArray`. A heavy array
contains each selected integer once, preceded by its exact cardinality. The
packed array has `4N` cells, including every sentinel and padded cell. Memory outside the
explicit allocation and caller registers 46–55 are preserved.

## Main results

* `NodePacking.exec_spec`: complete native execution and exact semantic readback.
* `NodePacking.Output.packed_square`: exact native readback at the common `8m²` length.
* `NodePacking.abs_oneArray_le`: the node magnitude bound is `60U+40`.

These programs and composition proofs are original. The mathematical comparator is the
existing Chan–He development; no host-level output is substituted for native execution.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.NodePacking

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Exact semantic readback from the concrete native allocation. -/
structure Output (L : Layout) (values : Fin 3 → ℕ → ℤ) (before after : ℕ → ℕ) : Prop where
  /-- Each compact list enumerates precisely the existing heavy set, without duplicates. -/
  heavy : ∀ j, ∃ zs : List ℤ, zs.Nodup ∧
    zs.toFinset = Cslib.Algorithms.ThreeSum.ChanHe.heavy
      ((Finset.range (L.n j)).image (values j)) L.M ∧
    after (L.descriptor j) = zs.length ∧
    ∀ k (hk : k < zs.length), after (L.heavy j + k) = encode zs[k]
  /-- Every packed cell equals the existing mathematical node array. -/
  packed : ∀ u < 4 * L.N, after (L.packed + u) = encode ((node L values).oneArray L.U u)
  /-- All memory outside the fresh allocation retains its old contents. -/
  frame : ∀ a, a < L.base ∨ L.endpoint ≤ a → after a = before a

/-- Exact readback of the fully composed memory theorem. -/
theorem memory_output (L : Layout) (values : Fin 3 → ℕ → ℤ) (mem : ℕ → ℕ)
    (hM : 0 < L.M) (hN : 2 * L.M ≤ L.N)
    (hinj : ∀ j, Set.InjOn (values j) (↑(Finset.range (L.n j)) : Set ℕ)) :
    Output L values mem (memory L values mem) := by
  refine ⟨?_, fun _ hu => memory_oneArray L values mem hM hinj hu,
    fun _ ha => memory_outside L values mem hM hN ha⟩
  intro j
  obtain ⟨hc, hd⟩ := memory_heavy L values mem hM hN j
  exact ⟨Place.heavyList (values j) (L.n j) L.M (L.n j),
    Place.heavyList_nodup _ _ _ (hinj j), Place.heavyList_toFinset _ _ hM (hinj j), hc, hd⟩

/-- The native descriptor is the cardinality of the existing heavy set. -/
theorem Output.heavy_card {L : Layout} {values : Fin 3 → ℕ → ℤ}
    {before after : ℕ → ℕ} (h : Output L values before after) (j : Fin 3) :
    after (L.descriptor j) = (Cslib.Algorithms.ThreeSum.ChanHe.heavy
      ((Finset.range (L.n j)).image (values j)) L.M).card := by
  obtain ⟨zs, hnd, hs, hc, _⟩ := h.heavy j
  rw [hc, ← hs]
  exact (List.toFinset_card_of_nodup hnd).symm

/-- The complete fixed native program constructs all three exact heavy outputs and the exact
packed node array, charging setup, clearing, padding, signed tags, every address and count store,
and every actual residue/histogram call. Initial output and scratch contents are arbitrary. -/
theorem exec_spec {w : ℕ} (x : Data 64) (values : Fin 3 → ℕ → ℤ)
    (hM : 0 < (layout x).M) (hN : 2 * (layout x).M ≤ (layout x).N)
    (hwidth : GenericRAM.Signed.Fits w ((layout x).budget : ℤ))
    (hsrc : ∀ j, x.regs (source j) + (layout x).n j ≤ (layout x).base)
    (hbdd : ∀ j i, i < (layout x).n j → (values j i).natAbs ≤ (layout x).U)
    (hinput : ∀ j i, i < (layout x).n j →
      x.mem (x.regs (source j) + i) = encode (values j i))
    (hinj : ∀ j, Set.InjOn (values j) (↑(Finset.range ((layout x).n j)) : Set ℕ)) :
    ∃ y, ExecWithin (w + 2) program x y
        (256 * ((layout x).total + (layout x).M + (layout x).N + 1)) ∧
      Output (layout x) values x.mem y.mem ∧ Parameters x y := by
  obtain ⟨y, hy, hm, hp⟩ := exec x values hM hN hwidth hsrc hbdd hinput hinj
  refine ⟨y, hy.mono (time_le_linear _), ?_, hp⟩
  rw [hm]
  exact memory_output _ _ _ hM hN hinj

/-- The supplied magnitude bound transfers to the existing finite-set notion. -/
theorem bdd_image (L : Layout) (values : Fin 3 → ℕ → ℤ)
    (hbdd : ∀ j i, i < L.n j → (values j i).natAbs ≤ L.U) (j : Fin 3) :
    Cslib.Algorithms.ThreeSum.Bdd L.U ((Finset.range (L.n j)).image (values j)) := by
  intro z hz
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
  have h := hbdd j i (Finset.mem_range.mp hi)
  rw [← Int.natCast_natAbs]
  exact_mod_cast h

/-- The existing mathematical output bound applies to every native packed value. -/
theorem abs_oneArray_le (L : Layout) (values : Fin 3 → ℕ → ℤ)
    (hbdd : ∀ j i, i < L.n j → (values j i).natAbs ≤ L.U) (u : ℕ) :
    |(node L values).oneArray L.U u| ≤ 60 * (L.U : ℤ) + 40 :=
  Cslib.Algorithms.ThreeSum.ChanHe.Node.abs_oneArray_le
    (bdd_image L values hbdd 0) (bdd_image L values hbdd 1) (bdd_image L values hbdd 2) u

/-- Exact readback at the full preprocessing's common length, with no extra padding assumption. -/
theorem Output.packed_square {L : Layout} {values : Fin 3 → ℕ → ℤ}
    {before after : ℕ → ℕ} (h : Output L values before after)
    {m : ℕ} (hN : L.N = 2 * m ^ 2) {u : ℕ} (hu : u < 8 * m ^ 2) :
    after (L.packed + u) = encode ((node L values).oneArray L.U u) :=
  h.packed u (by rw [hN]; omega)

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.NodePacking
