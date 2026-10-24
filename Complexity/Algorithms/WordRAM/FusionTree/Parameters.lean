/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.FusionTree.Compression
public import Complexity.Algorithms.Lean.FusionTree.Sketch
public import Complexity.Algorithms.Lean.FusionTree.Capacity
public import Complexity.Algorithms.WordRAM.FusionTree.Compress
public import Complexity.Algorithms.WordRAM.FusionTree.LowerRank
import Mathlib.Tactic.FinCases

/-!
# Concrete fusion-node preprocessing parameters

Static preprocessing chooses collision-free shifts and three half-word multiplier digits.
All other stored constants are explicit arithmetic expressions in these witnesses and the
stored keys. The choices have no preprocessing-time certificate. Arithmetic compression
agrees with perfect-sketch comparisons on all inputs; full-key query correction and the
complete fusion-tree query remain separate.

## Main definitions

* `NodeParameters`: actual compression witnesses for a node.
* `NodeParameters.words`: fifteen physical parameter words, independent of the node header.

## Main results

* `NodeParameters.exists_parameters`: witnesses for every large-width bounded sorted node.
* `NodeParameters.compressed_lt_iff`: comparison agreement for arbitrary inputs.
* `NodeParameters.words_fit`: every stored parameter fits the physical word.

## References

* [Fredman and Willard, *Surpassing the information theoretic bound
  with fusion trees*][FredmanWillard1993].
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.FusionTree

open Cslib.BitString Cslib.WordRAM
open Lean.FusionTree

/-- Number of selected source positions. -/
def relevantCount {n : ℕ} (w : ℕ) (keys : Fin n → ℕ) : ℕ :=
  (relevantBits w keys).card

/-- Source positions enumerated in increasing significance order. -/
def sourcePositions {n : ℕ} (w : ℕ) (keys : Fin n → ℕ) :
    Fin (relevantCount w keys) ↪o ℕ :=
  (relevantBits w keys).orderEmbOfFin rfl

/-- The source-position list is exactly the list defining the perfect sketch. -/
private theorem sourcePositions_list {n : ℕ} (w : ℕ) (keys : Fin n → ℕ) :
    List.ofFn (sourcePositions w keys) = (relevantBits w keys).sort (· ≤ ·) := by
  rw [List.ofFn_eq_map]
  exact Finset.listMap_orderEmbOfFin_finRange _ rfl

/-- Explicit compression witnesses. Correctness and word bounds below are derived from the
collision, ordering and span properties supplied by the constructive shift theorem. -/
structure NodeParameters (w : ℕ) {n : ℕ} (keys : Fin n → ℕ) where
  /-- Collision-free shift positions. -/
  shifts : Fin (relevantCount w keys) → ℕ
  /-- Distinct cross terms prevent carries. -/
  cross_injective : Function.Injective
    (fun p : Fin (relevantCount w keys) × Fin (relevantCount w keys) =>
      sourcePositions w keys p.1 + shifts p.2)
  /-- Retained terms occur in significance order. -/
  diagonal_strictMono : StrictMono (fun i => sourcePositions w keys i + shifts i)
  /-- All retained terms lie in the short window. -/
  span : ∀ i, w < sourcePositions w keys i + shifts i ∧
    sourcePositions w keys i + shifts i < w + 2 * relevantCount w keys ^ 4
  /-- The three little-endian half-word digits of the multiplier. -/
  digits : Fin 3 → ℕ
  /-- Each multiplier digit fits the multiplication radix. -/
  digits_lt : ∀ i, digits i < Multiword.radix w
  /-- The digits represent the actual shift mask. -/
  digits_value : Nat.ofDigits (Multiword.radix w) (List.ofFn digits) = positionMask shifts

namespace NodeParameters

variable {w n : ℕ} {keys : Fin n → ℕ}

/-- Selected-bit count, at most one per adjacent pair. -/
abbrev r (_p : NodeParameters w keys) : ℕ := relevantCount w keys
/-- Compressed payload width. -/
def b (p : NodeParameters w keys) : ℕ := 2 * p.r ^ 4
/-- Input position mask. -/
def C (_p : NodeParameters w keys) : ℕ := positionMask (sourcePositions w keys)
/-- Full multiplier, represented in storage by three digits. -/
def M (p : NodeParameters w keys) : ℕ := positionMask p.shifts
/-- Retained output mask. -/
def D (p : NodeParameters w keys) : ℕ :=
  positionMask (fun i => sourcePositions w keys i + p.shifts i - w)
/-- Arithmetic compressed sketch, for any natural input. -/
def compressed (p : NodeParameters w keys) (x : ℕ) : ℕ :=
  approximateSketch w (sourcePositions w keys) p.shifts x
/-- Stored sketches, extended by the sketch of zero outside the node. -/
def sketches (p : NodeParameters w keys) (i : ℕ) : ℕ :=
  p.compressed (if hi : i < n then keys ⟨i, hi⟩ else 0)
/-- Query replication multiplier. -/
def copies (p : NodeParameters w keys) : ℕ := queryMultiplier p.b n
/-- Guarded original sketches. -/
def packed (p : NodeParameters w keys) : ℕ := packedNode p.b n p.sketches
/-- Guarded complemented sketches. -/
def packedComplement (p : NodeParameters w keys) : ℕ :=
  packedNode p.b n (fun i => 2 ^ p.b - 1 - p.sketches i)
/-- Guard mask for packed comparisons. -/
def guards (p : NodeParameters w keys) : ℕ := guardMask p.b n
/-- Divisor selecting the middle count digit. -/
def middle (p : NodeParameters w keys) : ℕ := 2 ^ ((p.b + 1) * (n - 1))
/-- Packed-field radix, distinct from the half-word multiplication radix. -/
def radix (p : NodeParameters w keys) : ℕ := 2 ^ (p.b + 1)
/-- Largest compressed payload. -/
def maximum (p : NodeParameters w keys) : ℕ := 2 ^ p.b - 1

private theorem r_le (p : NodeParameters w keys) : p.r ≤ n - 1 := relevantBits_card_le w keys

private theorem diagonal_strictMono_sub (p : NodeParameters w keys) :
    StrictMono (fun i => sourcePositions w keys i + p.shifts i - w) := by
  intro i j hij
  have := p.diagonal_strictMono hij
  have := (p.span i).1
  have := (p.span j).1
  dsimp only at *
  omega

theorem D_lt (p : NodeParameters w keys) : p.D < 2 ^ p.b := by
  apply positionMask_lt _ p.diagonal_strictMono_sub.injective
  intro i
  have := p.span i
  change sourcePositions w keys i + p.shifts i - w < 2 * relevantCount w keys ^ 4
  omega

/-- The entire multiplier may exceed one word but fits in `w + b` bits. -/
theorem M_lt (p : NodeParameters w keys) : p.M < 2 ^ (w + p.b) := by
  have hm : Function.Injective p.shifts := by
    intro i j he
    exact congrArg Prod.snd (p.cross_injective (show
      sourcePositions w keys (i, i).1 + p.shifts (i, i).2 =
        sourcePositions w keys (i, j).1 + p.shifts (i, j).2 by dsimp only; rw [he]))
  exact positionMask_lt _ hm
    (fun i => lt_of_le_of_lt (Nat.le_add_left _ _) (p.span i).2)

theorem compressed_lt (p : NodeParameters w keys) (x : ℕ) :
    p.compressed x < 2 ^ p.b := Nat.and_le_right.trans_lt p.D_lt

/-- The arithmetic sketch and the perfect sketch compare identically for all inputs,
including inputs outside the stored key set and outside the physical word range. -/
theorem compressed_lt_iff (p : NodeParameters w keys) (x y : ℕ) :
    p.compressed x < p.compressed y ↔
      sketch (relevantBits w keys) x < sketch (relevantBits w keys) y := by
  simpa only [compressed, sourcePositions_list, sketch] using
    approximateSketch_lt_iff_projectBits (sourcePositions w keys) p.shifts
      p.cross_injective (sourcePositions w keys).injective (fun i => (p.span i).1.le)
      p.diagonal_strictMono_sub x y

/-- Weak comparisons agree too, including equality queries. -/
theorem compressed_le_iff (p : NodeParameters w keys) (x y : ℕ) :
    p.compressed x ≤ p.compressed y ↔
      sketch (relevantBits w keys) x ≤ sketch (relevantBits w keys) y := by
  simpa only [not_lt] using not_congr (p.compressed_lt_iff y x)

/-- The concrete stored arithmetic sketches remain strictly increasing. -/
theorem strictMono_compressed (p : NodeParameters w keys) (hsorted : StrictMono keys)
    (hbound : ∀ i, keys i < 2 ^ w) : StrictMono (fun i => p.compressed (keys i)) := by
  intro i j hij
  exact (p.compressed_lt_iff _ _).mpr (strictMono_sketch hsorted hbound hij)

/-- Capacity supplies the full packed-count multiplication bound. -/
theorem packed_width (p : NodeParameters w keys) (hnB : n ≤ branching w)
    (hw : 9 ≤ Nat.log 2 w) : 2 * ((p.b + 1) * n) ≤ w :=
  packed_width_le hw hnB (p.r_le.trans (by omega))

/-- Capacity also supplies the odd-width-aware half-word extraction bound. -/
theorem window (p : NodeParameters w keys) (hn : 0 < n) (hnB : n ≤ branching w)
    (hw : 9 ≤ Nat.log 2 w) : p.b + (w - 2 * (w / 2)) ≤ w / 2 :=
  compression_window_le hw hn hnB (p.r_le.trans (by omega))

private theorem C_fit (p : NodeParameters w keys) (hsorted : StrictMono keys)
    (hbound : ∀ i, keys i < 2 ^ w) : Fits w p.C := by
  apply positionMask_lt _ (sourcePositions w keys).injective
  intro i
  exact Finset.mem_range.mp (relevantBits_subset_range hsorted hbound
    (Finset.orderEmbOfFin_mem _ rfl i))

theorem sketches_lt (p : NodeParameters w keys) (i : ℕ) : p.sketches i < 2 ^ p.b :=
  p.compressed_lt _

/-- Distinct perfect sketches give a numerical bound on the number of stored keys. -/
theorem count_lt_radix (p : NodeParameters w keys) (hsorted : StrictMono keys)
    (hbound : ∀ i, keys i < 2 ^ w) : n < 2 ^ (p.b + 1) := by
  let f : Fin n → Fin (2 ^ p.r) := fun i =>
    ⟨sketch (relevantBits w keys) (keys i), sketch_lt_two_pow _ _⟩
  have hf : Function.Injective f := by
    intro i j he
    exact sketch_injective hsorted hbound (congrArg Fin.val he)
  have hc : n ≤ 2 ^ p.r := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf
  have hrb : p.r < p.b + 1 := by
    have hp : p.r ≤ p.r ^ 4 := Nat.le_self_pow (by decide) _
    dsimp only [b]
    omega
  exact hc.trans_lt (Nat.pow_lt_pow_right (by decide) hrb)

/-- In particular the separately stored occupancy is a physical word. -/
theorem count_fit (p : NodeParameters w keys) (hn : 0 < n)
    (hsorted : StrictMono keys) (hbound : ∀ i, keys i < 2 ^ w)
    (hnB : n ≤ branching w) (hw : 9 ≤ Nat.log 2 w) : Fits w n := by
  have hfield := Nat.le_mul_of_pos_right (p.b + 1) hn
  have hpack := p.packed_width hnB hw
  exact (p.count_lt_radix hsorted hbound).trans_le
    (Nat.pow_le_pow_right (by decide) (by omega))

/-- The inclusive arithmetic rank counts perfect sketches at or below every query.
This is a sketch rank, not the predecessor rank of the original keys. -/
theorem upperRank_eq (p : NodeParameters w keys) (hn : 0 < n)
    (hsorted : StrictMono keys) (hbound : ∀ i, keys i < 2 ^ w) (q : ℕ) :
    upperRankExpr p.b n p.sketches (p.compressed q) =
      ((Finset.range n).filter (fun i =>
        sketch (relevantBits w keys) (if hi : i < n then keys ⟨i, hi⟩ else 0) ≤
          sketch (relevantBits w keys) q)).card := by
  rw [upperRankExpr_eq_card _ hn (p.count_lt_radix hsorted hbound)
    (fun i _ => p.sketches_lt i) (p.compressed_lt q)]
  congr 1
  apply Finset.filter_congr
  intro i _
  exact p.compressed_le_iff _ q

/-- Strict arithmetic rank agrees with the perfect-sketch strict rank for every query,
including zero and queries with the same sketch as a stored key. -/
theorem lowerRank_eq (p : NodeParameters w keys) (hn : 0 < n)
    (hsorted : StrictMono keys) (hbound : ∀ i, keys i < 2 ^ w) (q : ℕ) :
    n - countGuards p.b n p.sketches (p.compressed q) =
      ((Finset.range n).filter (fun i =>
        sketch (relevantBits w keys) (if hi : i < n then keys ⟨i, hi⟩ else 0) <
          sketch (relevantBits w keys) q)).card := by
  rw [LowerRankProgram.countGuards_complement _ hn (p.count_lt_radix hsorted hbound)
    (fun i _ => p.sketches_lt i) (p.compressed_lt q)]
  congr 1
  apply Finset.filter_congr
  intro i _
  exact p.compressed_lt_iff _ q

/-- Slot order: input mask, three multiplier digits, retained mask, copies,
complemented packed sketches, original packed sketches, guards, payload width,
middle divisor, field radix, maximum payload, odd-width offset, selected-bit count. The node tag,
occupancy and minimum belong to the separate three-word header. -/
def words (p : NodeParameters w keys) : Fin 15 → ℕ := ![
  p.C, p.digits 0, p.digits 1, p.digits 2, p.D, p.copies, p.packedComplement,
  p.packed, p.guards, p.b, p.middle, p.radix, p.maximum, w - 2 * (w / 2), p.r]

/-- Every actual stored parameter is a physical word. The full multiplier is stored only
as three digits, because its unbounded numeric value may exceed a physical word. -/
theorem words_fit (p : NodeParameters w keys) (hn : 2 ≤ n)
    (hsorted : StrictMono keys) (hbound : ∀ i, keys i < 2 ^ w)
    (hnB : n ≤ branching w) (hw : 9 ≤ Nat.log 2 w) : ∀ i, Fits w (p.words i) := by
  have hpack := p.packed_width hnB hw
  have hn0 : 0 < n := by omega
  have hfield : p.b + 1 ≤ (p.b + 1) * n := by
    exact Nat.le_mul_of_pos_right _ hn0
  have hbw : p.b + 1 < w := by omega
  have hwidth : (p.b + 1) * n ≤ w := by omega
  have hbfit : Fits w p.b := (Nat.lt_two_pow_self).trans_le
    (Nat.pow_le_pow_right (by decide) (by omega : p.b ≤ w))
  have hDfit : Fits w p.D := p.D_lt.trans_le
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hdigits (i : Fin 3) : Fits w (p.digits i) := (p.digits_lt i).trans
    (Multiword.radix_fits (by omega))
  have hcopies : Fits w p.copies := (queryMultiplier_lt p.b n).trans_le
    (Nat.pow_le_pow_right (by decide) hwidth)
  have hpacked : Fits w p.packed := (packedNode_lt _ (fun i _ => p.sketches_lt i)).trans_le
    (Nat.pow_le_pow_right (by decide) hwidth)
  have hcomp : Fits w p.packedComplement := (packedNode_lt _ (fun i _ =>
      show 2 ^ p.b - 1 - p.sketches i < 2 ^ p.b by have := Nat.two_pow_pos p.b; omega)).trans_le
    (Nat.pow_le_pow_right (by decide) hwidth)
  have hguards : Fits w p.guards := (packedNode_lt (fun _ => 0)
    (fun _ _ => Nat.two_pow_pos _)).trans_le (Nat.pow_le_pow_right (by decide) hwidth)
  have hmidexp : (p.b + 1) * (n - 1) < w := by
    have hlt := Nat.mul_lt_mul_of_pos_left (show n - 1 < n by omega)
      (show 0 < p.b + 1 by omega)
    omega
  have hmiddle : Fits w p.middle := Nat.pow_lt_pow_right (by decide) hmidexp
  have hradix : Fits w p.radix := Nat.pow_lt_pow_right (by decide) hbw
  have hmax : Fits w p.maximum := (show 2 ^ p.b - 1 < 2 ^ p.b by
    have := Nat.two_pow_pos p.b; omega).trans_le
      (Nat.pow_le_pow_right (by decide) (by omega))
  have hrfit : Fits w p.r := (p.r_le.trans (by omega : n - 1 ≤ n)).trans_lt
    ((p.count_lt_radix hsorted hbound).trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
  have hoffset : Fits w (w - 2 * (w / 2)) :=
    (Nat.sub_le _ _).trans_lt Nat.lt_two_pow_self
  intro i
  fin_cases i <;> first
    | assumption
    | exact p.C_fit hsorted hbound
    | exact hdigits 0
    | exact hdigits 1
    | exact hdigits 2

/-- Real preprocessing witnesses exist; no correctness or timing oracle is assumed. -/
theorem exists_parameters (hn : 2 ≤ n) (hsorted : StrictMono keys)
    (hbound : ∀ i, keys i < 2 ^ w) (hnB : n ≤ branching w)
    (hw : 9 ≤ Nat.log 2 w) : Nonempty (NodeParameters w keys) := by
  have hr : 0 < relevantCount w keys := by
    apply Finset.card_pos.mpr
    exact ⟨_, Finset.mem_image.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _, rfl⟩⟩
  have hsource (i : Fin (relevantCount w keys)) : sourcePositions w keys i < w :=
    Finset.mem_range.mp (relevantBits_subset_range hsorted hbound
      (Finset.orderEmbOfFin_mem _ rfl i))
  obtain ⟨m, hc, hm, hs⟩ := exists_spread_shifts hr (sourcePositions w keys)
    (sourcePositions w keys).injective (fun i => (hsource i).le)
  have hmi : Function.Injective m := by
    intro i j he
    let k : Fin (relevantCount w keys) := ⟨0, hr⟩
    exact congrArg Prod.snd (hc (show sourcePositions w keys (k, i).1 + m (k, i).2 =
      sourcePositions w keys (k, j).1 + m (k, j).2 by dsimp only; rw [he]))
  have hM : positionMask m < 2 ^ (w + 2 * relevantCount w keys ^ 4) :=
    positionMask_lt m hmi (fun i => lt_of_le_of_lt (Nat.le_add_left _ _) (hs i).2)
  have hwindow := compression_window_le hw (by omega : 0 < n) hnB
    ((relevantBits_card_le w keys).trans (by omega : n - 1 ≤ branching w))
  obtain ⟨digits, hd, hv⟩ := CompressProgram.exists_multiplier_digits hwindow hM
  exact ⟨⟨m, hc, hm, hs, digits, hd, hv⟩⟩

/-- Static preprocessing explicitly uses classical choice; no preprocessing-time bound. -/
noncomputable def choose (hn : 2 ≤ n) (hsorted : StrictMono keys)
    (hbound : ∀ i, keys i < 2 ^ w) (hnB : n ≤ branching w)
    (hw : 9 ≤ Nat.log 2 w) : NodeParameters w keys :=
  (exists_parameters hn hsorted hbound hnB hw).some

end NodeParameters

end Cslib.Algorithms.WordRAM.FusionTree
