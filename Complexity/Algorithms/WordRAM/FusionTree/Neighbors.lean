/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Notation
public import Complexity.Algorithms.Lean.FusionTree.XorCorrection

/-!
# Loading and selecting sketch neighbors

An inclusive sketch cut has at most two neighboring full keys. Clamp the two indices to a
nonempty array, load both keys, and compare their exclusive or with the query. Clamping
allows the same bounded program to handle cuts at either end of the array.

## Main definitions

* `NeighborProgram.query`, `NeighborProgram.cut`, `NeighborProgram.count`,
  `NeighborProgram.base`, `NeighborProgram.stride`, `NeighborProgram.one`,
  `NeighborProgram.leftIndex`, `NeighborProgram.rightIndex`, `NeighborProgram.excess`,
  `NeighborProgram.address`, `NeighborProgram.leftKey`, `NeighborProgram.rightKey`,
  `NeighborProgram.leftXor`, `NeighborProgram.rightXor`, `NeighborProgram.chosen`,
  `NeighborProgram.divergence`, `NeighborProgram.index`: register assignments for loading and
  comparing sketch neighbors.
* `NeighborProgram.left`, `NeighborProgram.right`: clamped predecessor and successor indices.
* `NeighborProgram.code`: load two full keys and choose the smaller exclusive or.
* `NeighborProgram.loaded`, `NeighborProgram.result`: register and memory states after loading
  both keys and after selecting the neighbor.

## Main results

* `NeighborProgram.exec`: checked execution in at most eighteen instructions.

## References

* [Fredman and Willard, *Surpassing the information theoretic bound
  with fusion trees*][FredmanWillard1993].
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.FusionTree.NeighborProgram

open Cslib.WordRAM
open Cslib.Algorithms.Lean.FusionTree

/-- Query word, preserved. -/
abbrev query : Fin 17 := 0
/-- Inclusive sketch cut, preserved. -/
abbrev cut : Fin 17 := 1
/-- Nonzero node occupancy, preserved. -/
abbrev count : Fin 17 := 2
/-- Address of the first full key, preserved. -/
abbrev base : Fin 17 := 3
/-- Distance between full keys, preserved. -/
abbrev stride : Fin 17 := 4
/-- Constant one. -/
abbrev one : Fin 17 := 5
/-- Clamped predecessor index. -/
abbrev leftIndex : Fin 17 := 6
/-- Clamped successor index. -/
abbrev rightIndex : Fin 17 := 7
/-- Clamping scratch. -/
abbrev excess : Fin 17 := 8
/-- Memory address scratch. -/
abbrev address : Fin 17 := 9
/-- First candidate key. -/
abbrev leftKey : Fin 17 := 10
/-- Second candidate key. -/
abbrev rightKey : Fin 17 := 11
/-- First candidate's exclusive or with the query. -/
abbrev leftXor : Fin 17 := 12
/-- Second candidate's exclusive or with the query. -/
abbrev rightXor : Fin 17 := 13
/-- Selected key. -/
abbrev chosen : Fin 17 := 14
/-- Selected key's exclusive or with the query. -/
abbrev divergence : Fin 17 := 15
/-- Selected array index. -/
abbrev index : Fin 17 := 16

/-- Clamped predecessor position. -/
def left (t : ℕ) : ℕ := t - 1
/-- Clamped successor position, expressed using two saturating subtractions. -/
def right (n t : ℕ) : ℕ := t - (t - (n - 1))

private theorem indices_lt {n t : ℕ} (hn : 0 < n) (ht : t ≤ n) :
    left t < n ∧ right n t < n := by
  dsimp only [left, right]
  omega

/-- Exactly one of the two optional sketch neighbors is repeated at an end cut. -/
private theorem indices_neighbors {n t : ℕ} (hn : 0 < n) (ht : t ≤ n) :
    (left t + 1 = t ∨ left t = t) ∧ (right n t + 1 = t ∨ right n t = t) := by
  dsimp only [left, right]
  omega

/-- Index selected by the comparison in `code`. -/
private def selectIndex (score : ℕ → ℕ) (n t : ℕ) : ℕ :=
  if score (right n t) < score (left t) then right n t else left t

/-- The clamped comparison chooses a valid neighbor of minimum score among all neighbors
of the cut. At either end the repeated candidate causes no exception. -/
private theorem selectIndex_spec (score : ℕ → ℕ) {n t : ℕ} (hn : 0 < n) (ht : t ≤ n) :
    selectIndex score n t < n ∧
      (selectIndex score n t + 1 = t ∨ selectIndex score n t = t) ∧
      ∀ i < n, (i + 1 = t ∨ i = t) → score (selectIndex score n t) ≤ score i := by
  have hi := indices_lt hn ht
  have hneighbor := indices_neighbors hn ht
  have hcover (i : ℕ) (hi : i < n) (hc : i + 1 = t ∨ i = t) :
      i = left t ∨ i = right n t := by
    dsimp only [left, right]
    omega
  unfold selectIndex
  split
  · rename_i hs
    refine ⟨hi.2, hneighbor.2, ?_⟩
    intro i hi hc
    rcases hcover i hi hc with rfl | rfl
    · exact hs.le
    · exact le_rfl
  · rename_i hs
    refine ⟨hi.1, hneighbor.1, ?_⟩
    intro i hi hc
    rcases hcover i hi hc with rfl | rfl
    · exact le_rfl
    · omega

/-- Thirteen instructions load the candidates. Selection adds four or five instructions,
including control flow, and prefers the left candidate when exclusive-or values tie. -/
def code : Code .standard 17 := ram[
  one ← #1;
  leftIndex ← cut - one;
  rightIndex ← count - one;
  excess ← cut - rightIndex;
  rightIndex ← cut - excess;
  address ← leftIndex * stride;
  address ← base + address;
  leftKey ← *address;
  leftXor ← leftKey ^^^ query;
  address ← rightIndex * stride;
  address ← base + address;
  rightKey ← *address;
  rightXor ← rightKey ^^^ query;
  if rightXor < leftXor then [
    chosen ← rightKey; divergence ← rightXor; index ← rightIndex
  ] else [
    chosen ← leftKey; divergence ← leftXor; index ← leftIndex
  ] ]

/-- State after loading, before the one comparison selecting a candidate. -/
def loaded (x : Data 17) (q n t a d : ℕ) : Data 17 :=
  let l := left t
  let r := right n t
  let kl := x.mem (a + l * d)
  let kr := x.mem (a + r * d)
  (((((((((((((x.set one 1).set leftIndex l).set rightIndex (n - 1)).set excess
    (t - (n - 1))).set rightIndex r).set address (l * d)).set address
    (a + l * d)).set leftKey kl).set leftXor (kl ^^^ q)).set address
    (r * d)).set address (a + r * d)).set rightKey kr).set rightXor (kr ^^^ q))

/-- Final state, choosing the smaller full-word exclusive or. -/
def result (x : Data 17) (q n t a d : ℕ) : Data 17 :=
  let z := loaded x q n t a d
  if x.mem (a + right n t * d) ^^^ q < x.mem (a + left t * d) ^^^ q then
    ((z.set chosen (x.mem (a + right n t * d))).set divergence
      (x.mem (a + right n t * d) ^^^ q)).set index (right n t)
  else
    ((z.set chosen (x.mem (a + left t * d))).set divergence
      (x.mem (a + left t * d) ^^^ q)).set index (left t)

/-- The returned key, exclusive-or value, and index describe the same selected array entry. -/
private theorem result_spec (x : Data 17) (q n t a d : ℕ) :
    let j := selectIndex (fun i => x.mem (a + i * d) ^^^ q) n t
    (result x q n t a d).regs index = j ∧
      (result x q n t a d).regs chosen = x.mem (a + j * d) ∧
      (result x q n t a d).regs divergence = x.mem (a + j * d) ^^^ q := by
  dsimp only
  unfold result selectIndex
  split <;> simp +decide [loaded, index, chosen, divergence, one, leftIndex,
    rightIndex, excess, address, leftKey, rightKey, leftXor, rightXor]

/-- With an actual sketch cut and an encoded full-key array, the output identifies a sketch
neighbor with minimum exclusive-or value among the neighbors. No full-key scan supplies the
answer. The statement is separate from the checked execution and can be composed with it. -/
theorem result_sketchNeighbor {w n q a d : ℕ} (x : Data 17) (keys : Fin n → ℕ)
    (hn : 0 < n) (hkeys : ∀ i : Fin n, x.mem (a + i.val * d) = keys i) :
    ∃ j : Fin n,
      (result x q n (sketchRank w keys q) a d).regs index = j.val ∧
      (result x q n (sketchRank w keys q) a d).regs chosen = keys j ∧
      (result x q n (sketchRank w keys q) a d).regs divergence = keys j ^^^ q ∧
      IsSketchNeighbor w keys q j ∧
      ∀ i, IsSketchNeighbor w keys q i → keys j ^^^ q ≤ keys i ^^^ q := by
  let t := sketchRank w keys q
  let score := fun i => x.mem (a + i * d) ^^^ q
  have ht : t ≤ n := upperRank_le _ _
  have hs := selectIndex_spec score hn ht
  let j : Fin n := ⟨selectIndex score n t, hs.1⟩
  have hout := result_spec x q n t a d
  refine ⟨j, hout.1, ?_, ?_, ?_, ?_⟩
  · exact hout.2.1.trans (hkeys j)
  · exact hout.2.2.trans (congrArg (fun k => k ^^^ q) (hkeys j))
  · exact hs.2.1
  · intro i hi
    have hscore := hs.2.2 i i.isLt hi
    change score j.val ≤ score i.val at hscore
    simpa only [score, hkeys] using hscore

/-- Loading two clamped neighbors and selecting one takes at most eighteen actual checked
instructions. The address premise covers the last array key; every accessed address and
intermediate product lies below it. The query, cut, occupancy, base, stride, and memory are
preserved. Constant preparation and the sketch cut itself are separate. -/
theorem exec {w q n t a d : ℕ} (x : Data 17) (hn : 0 < n) (ht : t ≤ n)
    (hq : Fits w q) (hnfit : Fits w n) (ha : Fits w (a + (n - 1) * d))
    (hkeys : ∀ i < n, Fits w (x.mem (a + i * d)))
    (hxq : x.regs query = q) (hxt : x.regs cut = t) (hxn : x.regs count = n)
    (hxa : x.regs base = a) (hxd : x.regs stride = d) :
    ExecWithin w code x (result x q n t a d) 18 ∧
      (result x q n t a d).mem = x.mem := by
  have hi := indices_lt hn ht
  have h1 : Fits w 1 := hnfit.of_le hn
  have hl : Fits w (left t) := hnfit.of_le hi.1.le
  have hnm : Fits w (n - 1) := hnfit.of_le (Nat.sub_le _ _)
  have he : Fits w (t - (n - 1)) := hnfit.of_le (by omega)
  have hr : Fits w (right n t) := hnfit.of_le hi.2.le
  have hla : Fits w (a + left t * d) := ha.of_le (by
    have hm := Nat.mul_le_mul_right d (show left t ≤ n - 1 by omega)
    omega)
  have hra : Fits w (a + right n t * d) := ha.of_le (by
    have hm := Nat.mul_le_mul_right d (show right n t ≤ n - 1 by omega)
    omega)
  have hlm : Fits w (left t * d) := hla.of_le (Nat.le_add_left _ _)
  have hrm : Fits w (right n t * d) := hra.of_le (Nat.le_add_left _ _)
  have hlx : Fits w (x.mem (a + left t * d) ^^^ q) :=
    Nat.xor_lt_two_pow (hkeys _ hi.1) hq
  have hrx : Fits w (x.mem (a + right n t * d) ^^^ q) :=
    Nat.xor_lt_two_pow (hkeys _ hi.2) hq
  have hleft : Fits w (t - 1) := hl
  have hright : Fits w (t - (t - (n - 1))) := hr
  simp only [left, right] at hla hra hlm hrm hlx hrx
  by_cases hc : x.mem (a + right n t * d) ^^^ q < x.mem (a + left t * d) ^^^ q
  · simp only [left, right] at hc
    refine ⟨⟨17, by omega, ?_⟩, ?_⟩
    · ram_eval [code, result, loaded, hxq, hxt, hxn, hxa, hxd,
        h1, hleft, hnm, he, hright, hlm, hrm, hla, hra, hlx, hrx, hc, left, right]
    · simp [result, left, right, hc, loaded]
  · simp only [left, right] at hc
    refine ⟨⟨18, le_rfl, ?_⟩, ?_⟩
    · ram_eval [code, result, loaded, hxq, hxt, hxn, hxa, hxd,
        h1, hleft, hnm, he, hright, hlm, hrm, hla, hra, hlx, hrx, hc, left, right]
    · simp [result, left, right, hc, loaded]

end Cslib.Algorithms.WordRAM.FusionTree.NeighborProgram
