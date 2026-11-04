/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.DataStructure.FusionTree.Multiplier
public import Complexity.Foundations.Data.Nat.Bitwise.Projection

/-!
# Comparing multiplication-based and perfect fusion sketches

The gaps between the bits of an approximate sketch do not change comparisons.
This holds for arbitrary queries as well as stored keys, and is separate from the
subsequent correction needed to recover full-key predecessor ranks.

## Main results

* `approximateSketch_lt_iff_projectBits`: approximate and perfect sketches give the
  same strict comparisons on every pair of inputs.
* `exists_compression`: existence of collision-free compression parameters preserving
  all comparisons.

## References

* [Fredman and Willard, *Surpassing the information theoretic bound
  with fusion trees*][FredmanWillard1993].
-/

@[expose] public section

namespace Cslib.DataStructure.FusionTree

open Cslib.BitString

/-- A collision-free multiplier with increasingly placed diagonal bits preserves every
comparison made by the perfect sketch. The inputs need not belong to the stored key set. -/
theorem approximateSketch_lt_iff_projectBits {r w : ℕ} (b m : Fin r → ℕ)
    (h : Function.Injective (fun p : Fin r × Fin r => b p.1 + m p.2))
    (hb : Function.Injective b) (hw : ∀ i, w ≤ b i + m i)
    (hs : StrictMono (fun i => b i + m i - w)) (x y : ℕ) :
    approximateSketch w b m x < approximateSketch w b m y ↔
      projectBits (List.ofFn b) x < projectBits (List.ofFn b) y := by
  rw [approximateSketch_eq b m h hb hw, approximateSketch_eq b m h hb hw,
    projectBits_ofFn_eq_sum, projectBits_ofFn_eq_sum]
  exact Nat.sum_strictMono_lt_iff _ _ hs (fun _ _ hi => hi) _ _

/-- Collision-free compression parameters exist for every nonempty set of distinct positions.
The multiplier occupies at most `w + 2r⁴` bits, and every compressed word at most `2r⁴`.
The construction preserves comparisons for all inputs. Preprocessing and multiword execution
remain separate from this arithmetic existence theorem. -/
theorem exists_compression {r w : ℕ} (hr : 0 < r) (b : Fin r → ℕ)
    (hb : Function.Injective b) (hw : ∀ i, b i ≤ w) :
    ∃ m : Fin r → ℕ,
      Function.Injective (fun p : Fin r × Fin r => b p.1 + m p.2) ∧
      positionMask m < 2 ^ (w + 2 * r ^ 4) ∧
      (∀ x, approximateSketch w b m x < 2 ^ (2 * r ^ 4)) ∧
      (∀ x y, approximateSketch w b m x < approximateSketch w b m y ↔
        projectBits (List.ofFn b) x < projectBits (List.ofFn b) y) := by
  obtain ⟨m, hcross, hmono, hspan⟩ := exists_spread_shifts hr b hb hw
  have hlow (i : Fin r) : w ≤ b i + m i := (hspan i).1.le
  have hdiag : StrictMono (fun i => b i + m i - w) := by
    intro i j hij
    have hi := hlow i
    have hj := hlow j
    have hlt := hmono hij
    change b i + m i < b j + m j at hlt
    change b i + m i - w < b j + m j - w
    omega
  have hminj : Function.Injective m := by
    intro i j he
    let k : Fin r := ⟨0, hr⟩
    exact congrArg Prod.snd (hcross (show b (k, i).1 + m (k, i).2 =
      b (k, j).1 + m (k, j).2 by dsimp only; rw [he]))
  refine ⟨m, hcross, ?_, ?_, fun x y =>
    approximateSketch_lt_iff_projectBits b m hcross hb hlow hdiag x y⟩
  · exact positionMask_lt m hminj (fun i => lt_of_le_of_lt (Nat.le_add_left _ _) (hspan i).2)
  · intro x
    apply Nat.and_le_right.trans_lt
    apply positionMask_lt _ hdiag.injective
    intro i
    have hi := hspan i
    change b i + m i - w < 2 * r ^ 4
    omega

end Cslib.DataStructure.FusionTree
