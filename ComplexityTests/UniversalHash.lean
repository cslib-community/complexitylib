/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Probability.HashFamily.Polynomial
import Complexity.Probability.HashIsolation
import Mathlib.Algebra.Field.ZMod

/-! Public-seed extraction, nonuniform seeds, empty digests and preimage isolation. -/

namespace ComplexityTests.UniversalHash

open Cslib.Probability Cslib.Probability.PMF
open scoped ENNReal

private def xorHash (seed value : Bool) : Bool := value ^^ seed

-- The seed distribution need not be uniform: every individual hash here is injective.
private theorem xor_twoUniversal (seed : PMF Bool) : IsTwoUniversal seed xorHash := by
  intro x y hxy
  have hempty : {s | xorHash s x = xorHash s y} = ∅ := by
    ext s
    cases x <;> cases y <;> cases s <;> simp_all [xorHash]
  simp [hempty]

example : IsTwoUniversal (PMF.pure false) xorHash := xor_twoUniversal _

-- Choosing one of two coordinates is not injective; its collision bound can be tight.
private theorem coord_twoUniversal :
    IsTwoUniversal (PMF.uniformOfFintype Bool)
      (fun key (input : Bool × Bool) => if key then input.1 else input.2) :=
  isTwoUniversal_iff_sum_ite_le.mpr <| by
    rintro ⟨a, b⟩ ⟨c, d⟩ hne
    cases a <;> cases b <;> cases c <;> cases d <;>
      norm_num [Fintype.sum_bool, PMF.uniformOfFintype_apply] at *

example : IsTwoUniversal (PMF.uniformOfFintype Bool)
    (fun key (input : Bool × Bool) => if key then input.1 else input.2) :=
  coord_twoUniversal

open scoped BigOperators in
example : (𝔼 key : Bool,
    if (if key then (false, false).1 else (false, false).2) =
        (if key then (true, false).1 else (true, false).2)
      then (1 : ℝ) else 0) ≤ (Fintype.card Bool : ℝ)⁻¹ :=
  coord_twoUniversal.expect_boole_le (by decide)

example : (∑ key : Bool,
    if (if key then (false, false).1 else (false, false).2) =
        (if key then (true, false).1 else (true, false).2)
      then (PMF.uniformOfFintype Bool key).toReal else 0) = (1 / 2 : ℝ) := by
  norm_num [Fintype.sum_bool, PMF.uniformOfFintype_apply]

-- A uniform source remains exactly uniform even with this maximally biased public seed.
example : seededHash (PMF.pure false) (PMF.uniformOfFintype Bool) xorHash =
    (PMF.pure false).bind (fun s => (PMF.uniformOfFintype Bool).map (s, ·)) := by
  simp [seededHash, xorHash]

-- The digest alone is uniform for a fixed source, but it equals the public seed.
example : (seededHash (PMF.uniformOfFintype Bool) (PMF.pure false) xorHash).map Prod.snd =
    PMF.uniformOfFintype Bool := by
  simp [seededHash, xorHash, PMF.map_bind, PMF.bind_pure]

-- Keeping that seed distinguishes the actual joint law from an independent uniform digest.
example : dist (seededHash (PMF.uniformOfFintype Bool) (PMF.pure false) xorHash)
    ((PMF.uniformOfFintype Bool).bind
      (fun s => (PMF.uniformOfFintype Bool).map (s, ·))) = 1 / 2 := by
  norm_num [dist_eq, seededHash, PMF.bind_apply, PMF.map_apply, PMF.pure_apply,
    PMF.uniformOfFintype_apply, tsum_fintype, Fintype.sum_prod_type, Fintype.sum_bool, xorHash]

-- A zero-bit digest is exactly uniform, even for a source on an infinite ambient type.
example (source : PMF (List Bool)) :
    seededHash (PMF.pure true) source (fun _ _ => fun i : Fin 0 => i.elim0) =
      (PMF.pure true).bind (fun s =>
        (PMF.uniformOfFintype (Fin 0 → Bool)).map (s, ·)) :=
  seededHash_eq_uniform_of_subsingleton _ _ _

-- Revealing an injective function image leaves no entropy in any seed-dependent predicate.
example (seed source : PMF Bool) :
    conditionalEntropy (seed.bind (fun s => source.map
      (fun x => ((s, x, xorHash s x), xorHash s x)))) = 0 := by
  apply le_antisymm _ (conditionalEntropy_nonneg _)
  simpa using (xor_twoUniversal seed).conditionalEntropy_hash_le source id xorHash

-- Conditional extraction retains both the correlated side information and the public seed.
example (side : PMF Bool) (source : Bool → PMF Bool) :
    4 * dist
      (side.bind (fun info => (seededHash (PMF.pure false) (source info) xorHash).map (info, ·)))
      (side.bind (fun info => ((PMF.pure false).bind
        (fun s => (PMF.uniformOfFintype Bool).map (s, ·))).map (info, ·))) ^ 2 ≤
      2 * ∑ info, (side info).toReal * collisionProbability (source info) := by
  simpa using (xor_twoUniversal (PMF.pure false)).leftover_hash_conditional_sq side source

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- Leftover hash lemma for an ε-universal family with ε = 2 / 5 ≠ 1 / |ZMod 5|:
-- two-block polynomial hashing over ZMod 5.
example (source : PMF (ZMod 5 × ZMod 5)) :
    dist (seededHash (PMF.uniformOfFintype (ZMod 5)) source (fun k p => polyHash k [p.1, p.2]))
      ((PMF.uniformOfFintype (ZMod 5)).bind
        (fun k => (PMF.uniformOfFintype (ZMod 5)).map (k, ·))) ≤
      Real.sqrt (5 * (collisionProbability source + 2 / 5) - 1) / 2 := by
  have hpoly : IsUniversalHash (PMF.uniformOfFintype (ZMod 5))
      (fun k (p : ZMod 5 × ZMod 5) => polyHash k [p.1, p.2]) (2 / 5) := by
    have h2 : IsUniversalHash (PMF.uniformOfFintype (ZMod 5))
        (fun k (m : {m : List (ZMod 5) // m.length ≤ 2}) => polyHash k m) (2 / 5) := by
      simpa using isUniversalHash_polyHash (F := ZMod 5) 2
    exact h2.precompose (encode := fun p : ZMod 5 × ZMod 5 => ⟨[p.1, p.2], by simp⟩)
      (fun p q h => by
        have h' := congrArg Subtype.val h
        simp only [List.cons.injEq, and_true] at h'
        exact Prod.ext h'.1 h'.2)
  have hne : (2 / 5 : ℝ≥0∞) ≠ ⊤ := ENNReal.div_ne_top (by norm_num) (by norm_num)
  simpa [ENNReal.toReal_div] using hpoly.leftover_hash hne source

/--
info: 'Cslib.Probability.IsDeltaUniversalHash.isTwoUniversal' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsDeltaUniversalHash.isTwoUniversal

/--
info: 'Cslib.Probability.isTwoUniversal_uniformOfFintype_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isTwoUniversal_uniformOfFintype_iff

/--
info: 'Cslib.Probability.IsTwoUniversal.expect_boole_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsTwoUniversal.expect_boole_le

/--
info: 'Cslib.Probability.IsUniversalHash.collision_with_set_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsUniversalHash.collision_with_set_le

/--
info: 'Cslib.Probability.IsUniversalHash.leftover_hash_sq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsUniversalHash.leftover_hash_sq

/--
info: 'Cslib.Probability.IsUniversalHash.leftover_hash' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms IsUniversalHash.leftover_hash

end ComplexityTests.UniversalHash
