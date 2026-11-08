/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.Minimap
public meta import CslibFrontier.Foundations.Data.BitString.Combination
public meta import CslibFrontier.DataStructure.Dictionary.Spillover
public meta import CslibFrontier.DataStructure.Dictionary.DynamicMatching
public meta import CslibFrontier.DataStructure.Dictionary.Minimap
public meta import Mathlib.Data.Finset.Insert

/-!
# Subconstant-Redundancy Dictionary Primitives Tests (`Spillover`, `DynamicMatching`, `Minimap`)

Exercises:
1. `Cslib.DataStructure.Dictionary.Spillover` (`Lemma 3.8`):
   - concrete evaluations across `X ≤ r_sp`, exact power-of-two multiples `X = r_sp * 2 ^ M`, and
     general non-power-of-two `X`, round-trip `encode`/`decode?`, out-of-range rejection, and
     logarithmic / ceiling-log bit-redundancy theorems;
2. `Cslib.DataStructure.Dictionary.DynamicMatching` (`Lemma 3.2`, `Claims 3.3–3.4`):
   - concrete multi-round cyclic matching on `U' = 6, n' = 3` requiring `2` rounds due to round-`0`
     ball-before-bin collisions, relocation distance `relocDist` under insertion, deletion, and
     atomic replacement, and instantiations of expected round / relocation bounds;
3. `Cslib.BitString` (`rankCombination`, `subsetEquiv`) &
   `Cslib.DataStructure.Dictionary.Minimap` (`Lemma 3.7` at `r = 1` & `Section 5.2`):
   - concrete `BitString.rankCombination` / `BitString.subsetEquiv` round-trips, comparison of
     `bitWidth` (`28` bits) against `infoBits` (`27` bits) and naive per-key ceiling
     `Dynamic.optBits` (`31` bits) on `(U', n', X) = (8, 4, 33)`, end-to-end `#eval` trace of
     `BoundedEncoded` (`empty`, `insert`, in-place overwrite, `query`, `delete`) and `FixedEncoded`
     (`replace`, `lookupHeader`, `slotDiff`), and instantiations of `bitWidth_le_infoBits_add_two`,
     `queryTableSize_le`, `slotDiff_replace_le`, and `expect_slotDiff_replace_encode_le`.
-/

public section

namespace CslibFrontierTests.SubconstantMinimap

open Cslib.DataStructure
open Cslib.DataStructure.Dictionary
open scoped BigOperators Finset

/-! ## 1. Power-of-Two Spillover (`Spillover`, Lemma 3.8) -/

-- Footnote 4 regime (`X ≤ r_sp`): `M = 0`, `K = X`, zero redundancy.
example : Spillover.memBits 3 5 = 0 := by decide
example : Spillover.spillUniv 3 5 = 3 := by decide

-- Exact power-of-two multiple (`X = 16, r_sp = 4`): `M = 2`, `K = 4 = r_sp`.
example : Spillover.memBits 16 4 = 2 := by decide
example : Spillover.spillUniv 16 4 = 4 := by decide

-- Non-power-of-two payload (`X = 100, r_sp = 6`): `M = 4`, `K = 7 ∈ (6, 12]`.
example : Spillover.memBits 100 6 = 4 := by decide
example : Spillover.spillUniv 100 6 = 7 := by decide

/-- info: ((0, 0), (0, 15), (1, 0), 6, 3) -/
#guard_msgs in
#eval
  let enc (x : Fin 100) :=
    let km := Spillover.encode 6 x
    (km.1.val, km.2.val)
  (enc ⟨0, by decide⟩, enc ⟨15, by decide⟩, enc ⟨16, by decide⟩, enc ⟨99, by decide⟩)

/-- info: (some 99, none) -/
#guard_msgs in
#eval
  let ok := (Spillover.decode? (X := 100) 6 (Spillover.encode 6 ⟨99, by decide⟩)).map Fin.val
  let oob := (Spillover.decode? (X := 100) 6 (⟨6, by decide⟩, ⟨15, by decide⟩)).map Fin.val
  (ok, oob)

theorem spillover_bounds_100_6 :
    6 < Spillover.spillUniv 100 6 ∧ Spillover.spillUniv 100 6 ≤ 2 * 6 ∧
      (Spillover.memBits 100 6 : ℝ) + Real.logb 2 (Spillover.spillUniv 100 6) ≤
        Real.logb 2 100 + 2 / (6 : ℝ) ∧
      Nat.clog 2 (15 * (Spillover.spillUniv 100 6) ^ 6) + 6 * Spillover.memBits 100 6 ≤
        Nat.clog 2 (15 * 100 ^ 6) + 2 := by
  refine ⟨Spillover.lt_spillUniv_of_mul_two_pow_lt (by decide),
    Spillover.spillUniv_le_two_mul (by decide),
    Spillover.memBits_add_logb_spillUniv_le (by decide) (by decide),
    Spillover.clog_mul_spillUniv_pow_add_le (by decide) (by decide) (by decide)⟩

/-! ## 2. Multi-Round Unit-Circle Dynamic Matching (`DynamicMatching`, Lemma 3.2) -/

/-- Concrete deterministic scheme on `U' = 6, n' = 3` (`U' + n' = 9`):
in round `0`, identity order puts balls `0, 1, 2, 3, 4, 5` before bins `6, 7, 8`, so among active
balls `{0, 2, 5}` only ball `5` precedes bin `6` (`round 0`), while balls `0` and `2` remain for
subsequent rounds under the transpositions `swap 1 7` (round 1) and `swap 3 8` (later rounds). -/
meta def sampleSchemeMeta : DynamicMatching.Scheme 6 3 := fun r =>
  if r.val = 0 then Equiv.refl (Fin 9)
  else if r.val = 1 then
    -- Interleave remaining balls and bins by swapping `1` with bin `7`.
    Equiv.swap (⟨1, by decide⟩ : Fin 9) ⟨7, by decide⟩
  else
    Equiv.swap (⟨3, by decide⟩ : Fin 9) ⟨8, by decide⟩

/-- info: (2, [some 1, none, some 2, none, none, some 0]) -/
#guard_msgs in
#eval
  let A : Finset (Fin 6) := {⟨0, by decide⟩, ⟨2, by decide⟩, ⟨5, by decide⟩}
  let r := DynamicMatching.rounds sampleSchemeMeta A
  let m :=
    (List.finRange 6).map fun a => (DynamicMatching.matchOpt sampleSchemeMeta A a).map Fin.val
  (r, m)

/-- info: (1, 2, 3) -/
#guard_msgs in
#eval
  let A2 : Finset (Fin 6) := {⟨0, by decide⟩, ⟨5, by decide⟩}
  let A3 : Finset (Fin 6) := insert ⟨2, by decide⟩ A2
  let A3' : Finset (Fin 6) := insert ⟨4, by decide⟩ (A3.erase ⟨0, by decide⟩)
  let dIns := DynamicMatching.relocDist
    (DynamicMatching.matchOpt sampleSchemeMeta A2) (DynamicMatching.matchOpt sampleSchemeMeta A3)
  let dDel := DynamicMatching.relocDist
    (DynamicMatching.matchOpt sampleSchemeMeta A3)
    (DynamicMatching.matchOpt sampleSchemeMeta (A3.erase ⟨5, by decide⟩))
  let dRep := DynamicMatching.relocDist
    (DynamicMatching.matchOpt sampleSchemeMeta A3) (DynamicMatching.matchOpt sampleSchemeMeta A3')
  (dIns, dDel, dRep)

theorem sample_matching_bounds (A : Finset (Fin 6)) (hA : A.card ≤ 3)
    (x y : Fin 6) (hrep : (insert y (A.erase x)).card ≤ 3) :
    DynamicMatching.schemePMF 6 3 =
      Cslib.Probability.PMF.uniformOfFintype (DynamicMatching.Scheme 6 3) ∧
    (∑ h : DynamicMatching.Scheme 6 3,
      (DynamicMatching.schemePMF 6 3 h).toReal * (DynamicMatching.rounds h A : ℝ)) ≤
      3 * (Nat.clog 2 (max A.card 2) : ℝ) ∧
    (∑ h : DynamicMatching.Scheme 6 3,
      (DynamicMatching.schemePMF 6 3 h).toReal *
        (DynamicMatching.relocDist (DynamicMatching.matchOpt h A)
          (DynamicMatching.matchOpt h (insert y (A.erase x))) : ℝ)) ≤
      18 * (Nat.clog 2 (max A.card 2) : ℝ) :=
  ⟨rfl, DynamicMatching.expect_rounds_le hA,
    DynamicMatching.expect_relocDist_replace_le x y hA hrep⟩

/-! ## 3. Fixed-Capacity Leaf Minimap (`Minimap`, Lemma 3.7 & Section 5.2) -/

-- Subconstant leaf bit budget on `(U', n', X) = (8, 4, 33)`:
-- `infoBits = 27`, `bitWidth = 28` (`+1` wasted bit total across 4 keys), whereas per-key ceiling
-- `Dynamic.optBits 8 33 4 = 31` wastes `4` bits.
example : Minimap.infoBits 8 4 33 = 27 := by decide
example : Minimap.bitWidth 8 4 33 = 28 := by decide
example : Dynamic.optBits 8 33 4 = 31 := by decide
example : Minimap.bitWidth 8 4 33 ≤ Minimap.infoBits 8 4 33 + 2 :=
  Minimap.bitWidth_le_infoBits_add_two (by decide) (by decide) (by decide)
example : 8 * Minimap.headerUniv 8 4 33 4 ≤ 8 * (8).choose 4 * (2 * 4) ^ 4 :=
  Minimap.queryTableSize_le (by decide)

-- Concrete `BitString.rankCombination` and `BitString.subsetEquiv` round-trip checks on `Fin 6`.
example : Cslib.BitString.rankCombination (Cslib.BitString.unrankCombination 6 3 11) = 11 := by
  decide

/-- info: (true, true) -/
#guard_msgs in
#eval
  let S : { S : Finset (Fin 6) // S.card = 3 } := ⟨{(0 : Fin 6), 2, 5}, by decide⟩
  let r := Cslib.BitString.subsetEquiv 6 3 S
  let S' := (Cslib.BitString.subsetEquiv 6 3).symm r
  (decide (S' = S), decide (Cslib.BitString.subsetEquiv 6 3 S' = r))

-- End-to-end concrete evaluation of `BoundedEncoded` (`empty`, `insert`, overwrite, `query`,
-- `delete`, and fresh `insert` after `delete` from full capacity) on `U' = 6, n' = 3, X = 50`.
/-- info: ([41, 99, 17, 99, 99, 49], [99, 99, 33, 99, 12, 49]) -/
#guard_msgs in
#eval
  let b0 := Minimap.BoundedEncoded.empty 6 3 50
  have he0 : Minimap.activeSet b0.encoded = ∅ := Minimap.BoundedEncoded.activeSet_empty 6 3 50
  have hs0 : b0.size.val = 0 := Minimap.BoundedEncoded.size_empty 6 3 50
  let b1 := Minimap.BoundedEncoded.insert sampleSchemeMeta b0 ⟨0, by decide⟩ 41 (by decide)
    (.inl (by omega))
  have hs1 : b1.size.val = 1 := by
    have h := Minimap.BoundedEncoded.size_insert_of_notMem sampleSchemeMeta b0 ⟨0, by decide⟩ 41
      (by decide) (.inl (by omega)) (by rw [he0]; simp)
    dsimp only [b1]; omega
  have he1 : Minimap.activeSet b1.encoded = {⟨0, by decide⟩} := by
    dsimp only [b1]
    rw [Minimap.BoundedEncoded.activeSet_insert, he0]; rfl
  let b2 := Minimap.BoundedEncoded.insert sampleSchemeMeta b1 ⟨2, by decide⟩ 17 (by decide)
    (.inl (by omega))
  have hs2 : b2.size.val = 2 := by
    have h := Minimap.BoundedEncoded.size_insert_of_notMem sampleSchemeMeta b1 ⟨2, by decide⟩ 17
      (by decide) (.inl (by omega)) (by rw [he1]; decide)
    dsimp only [b2]; omega
  have he2 : Minimap.activeSet b2.encoded = {⟨2, by decide⟩, ⟨0, by decide⟩} := by
    dsimp only [b2]
    rw [Minimap.BoundedEncoded.activeSet_insert, he1]
  let b3 := Minimap.BoundedEncoded.insert sampleSchemeMeta b2 ⟨5, by decide⟩ 49 (by decide)
    (.inl (by omega))
  have hs3 : b3.size.val = 3 := by
    have h := Minimap.BoundedEncoded.size_insert_of_notMem sampleSchemeMeta b2 ⟨5, by decide⟩ 49
      (by decide) (.inl (by omega)) (by rw [he2]; decide)
    dsimp only [b3]; omega
  have he3 : Minimap.activeSet b3.encoded = {⟨5, by decide⟩, ⟨2, by decide⟩, ⟨0, by decide⟩} := by
    dsimp only [b3]
    rw [Minimap.BoundedEncoded.activeSet_insert, he2]
  let snap1 :=
    (List.finRange 6).map fun u => (Minimap.BoundedEncoded.query sampleSchemeMeta b3 u).getD 99
  let b4 := Minimap.BoundedEncoded.insert sampleSchemeMeta b3 ⟨2, by decide⟩ 33 (by decide)
    (.inr (by rw [he3]; decide))
  have hs4 : b4.size.val = 3 := by
    have h := Minimap.BoundedEncoded.size_insert_of_mem sampleSchemeMeta b3 ⟨2, by decide⟩ 33
      (by decide) (.inr (by rw [he3]; decide)) (by rw [he3]; decide)
    dsimp only [b4]; omega
  have he4 : Minimap.activeSet b4.encoded = {⟨5, by decide⟩, ⟨2, by decide⟩, ⟨0, by decide⟩} := by
    dsimp only [b4]
    rw [Minimap.BoundedEncoded.activeSet_insert, he3]; decide
  let b5 := Minimap.BoundedEncoded.delete sampleSchemeMeta b4 ⟨0, by decide⟩
  have hs5 : b5.size.val = 2 := by
    have h := Minimap.BoundedEncoded.size_delete_of_mem sampleSchemeMeta b4 ⟨0, by decide⟩
      (by rw [he4]; decide)
    dsimp only [b5]; omega
  let b6 := Minimap.BoundedEncoded.insert sampleSchemeMeta b5 ⟨4, by decide⟩ 12 (by decide)
    (.inl (by omega))
  let snap2 :=
    (List.finRange 6).map fun u => (Minimap.BoundedEncoded.query sampleSchemeMeta b6 u).getD 99
  (snap1, snap2)

-- Concrete fixed-capacity leaf `FixedEncoded` (`m = n' = 3`) evaluation of `lookupHeader`,
-- `replace`, `query`, `slotDiff`, and history independence (`eRep == eDirect`).
/-- info: (true, [none, none, some 17, none, some 28, some 49], true, true) -/
#guard_msgs in
#eval
  let e0 := Minimap.empty 6 3 50
  let e1 := Minimap.insertNew (by decide) sampleSchemeMeta e0 ⟨0, by decide⟩ 41
    (by decide) (by simp [e0])
  let e2 := Minimap.insertNew (by decide) sampleSchemeMeta e1 ⟨2, by decide⟩ 17
    (by decide) (by simp [e1, e0])
  let e3 : Minimap.FixedEncoded 6 3 50 :=
    Minimap.insertNew (by decide) sampleSchemeMeta e2 ⟨5, by decide⟩ 49
      (by decide) (by simp [e2, e1, e0])
  let hdrHit := (Minimap.lookupHeader sampleSchemeMeta e3.header ⟨2, by decide⟩).isSome
  let eRep := Minimap.replace sampleSchemeMeta e3 ⟨0, by decide⟩ ⟨4, by decide⟩ 28
    (by decide) (by simp [e3, e2, e1, e0]) (by simp [e3, e2, e1, e0])
  let d1 := Minimap.insertNew (by decide) sampleSchemeMeta e0 ⟨5, by decide⟩ 49
    (by decide) (by simp [e0])
  let d2 := Minimap.insertNew (by decide) sampleSchemeMeta d1 ⟨4, by decide⟩ 28
    (by decide) (by simp [d1, e0])
  let eDirect : Minimap.FixedEncoded 6 3 50 :=
    Minimap.insertNew (by decide) sampleSchemeMeta d2 ⟨2, by decide⟩ 17
      (by decide) (by simp [d2, d1, e0])
  let snap := (List.finRange 6).map (Minimap.query sampleSchemeMeta eRep)
  let diffOk := decide (Minimap.slotDiff e3 eRep ≤
    8 * DynamicMatching.rounds sampleSchemeMeta (Minimap.activeSet e3) + 14)
  (hdrHit, snap, diffOk, decide (eRep = eDirect))

theorem sample_leaf_canonical (h : DynamicMatching.Scheme 6 3)
    {e₁ e₂ : Minimap.FixedEncoded 6 3 50}
    (hwf₁ : Minimap.WellFormed le_rfl h e₁)
    (hwf₂ : Minimap.WellFormed le_rfl h e₂)
    (hq : Minimap.query h e₁ = Minimap.query h e₂) :
    e₁ = e₂ :=
  Minimap.eq_of_query_eq_fixed h hwf₁ hwf₂ hq

theorem sample_leaf_replace_bounds (s : Dictionary.State 6)
    (hb : Dictionary.ValuesBounded 50 s) (hs : (Dictionary.dom s).card = 3)
    (x_old x_new : Fin 6) (v_new : ℕ) (hv : v_new < 50)
    (hx_old : x_old ∈ Dictionary.dom s) (hx_new : x_new ∉ (Dictionary.dom s).erase x_old) :
    (∀ h, Minimap.slotDiff (Minimap.encode le_rfl h s hb hs)
      (Minimap.replace h (Minimap.encode le_rfl h s hb hs) x_old x_new v_new hv
        (by rwa [Minimap.activeSet_encode]) (by rwa [Minimap.activeSet_encode])) ≤
      8 * DynamicMatching.rounds h (Dictionary.dom s) + 14) ∧
    (∑ h : DynamicMatching.Scheme 6 3,
      (DynamicMatching.schemePMF 6 3 h).toReal *
        (Minimap.slotDiff (Minimap.encode le_rfl h s hb hs)
          (Minimap.replace h (Minimap.encode le_rfl h s hb hs) x_old x_new v_new hv
            (by rwa [Minimap.activeSet_encode]) (by rwa [Minimap.activeSet_encode])) : ℝ)) ≤
      38 * (Nat.clog 2 (max 3 2) : ℝ) :=
  ⟨fun h => by
      simpa using Minimap.slotDiff_replace_le h (Minimap.encode le_rfl h s hb hs)
        x_old x_new v_new hv (by rwa [Minimap.activeSet_encode])
        (by rwa [Minimap.activeSet_encode]),
    Minimap.expect_slotDiff_replace_encode_le s hb hs x_old x_new v_new hv hx_old hx_new⟩

end CslibFrontierTests.SubconstantMinimap
