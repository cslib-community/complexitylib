/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

import Complexity.Computability.GenericRAM.Native.SubsetPairFold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-!
# Concrete tests for combinatorial subset-pair unranking and streaming folds

Kernel-checked boundary, completeness, Möbius cancellation/reconstruction, `fun_prop`, and
streaming `ComputableInO` tests for `Cslib.GenericRAM.SubsetPairFold`.
-/

open Cslib.GenericRAM Turing.MultiTapeTM Cslib.GenericRAM.SubsetPairFold

-- 1. Pascal DP table values and `(n + 1)`-bit entry bounds (`n = 0` and `n = 4`).
example : pascalTable 0 = [[1]] ∧
    pascalTable 4 =
      [[1, 0, 0, 0, 0], [1, 1, 0, 0, 0], [1, 2, 1, 0, 0], [1, 3, 3, 1, 0], [1, 4, 6, 4, 1]] ∧
    (pascalTable 4).all (fun row => row.all fun x => (encNat x).length ≤ 5) = true := by decide

-- 2. Boundary cases `n = 0` (`q = 0`, `q = 3`) and `q = 0` (`n = 4, q = 0`): `C_q = 1`.
example : subsetPairCount 0 0 = 1 ∧ subsetPairCount 0 3 = 1 ∧ subsetPairCount 4 0 = 1 ∧
    (List.range (subsetPairCount 0 3)).map (unrankSubsetPair 0 3) = [([], [], false)] ∧
    (List.range (subsetPairCount 4 0)).map (unrankSubsetPair 4 0) =
      [([false, false, false, false], [false, false, false, false], false)] := by decide

-- 3. `n = 3, q = 2`: `1 + 6 + 12 = 19` valid `(E, U)` pairs, duplicate-free and exhaustive.
private def boolWords3 : List (List Bool) :=
  let b := [false, true]
  b.flatMap fun x0 => b.flatMap fun x1 => b.map fun x2 => [x0, x1, x2]

private def expectedValid3_2 : List DecodedPair :=
  boolWords3.flatMap fun e => if e.count true ≤ 2 then
    (boolWords3.filter fun u => (List.range 3).all fun i => !u.getD i false || e.getD i false).map
      fun u => (e, u, (e.count true - u.count true) % 2 == 1) else []

example : subsetPairCount 3 0 = 1 ∧ subsetPairCount 3 1 = 7 ∧ subsetPairCount 3 2 = 19 ∧
    expectedValid3_2.length = 19 ∧
    let s := (List.range (subsetPairCount 3 2)).map (unrankSubsetPair 3 2)
    s.length = 19 ∧ expectedValid3_2.all (fun p => s.count p == 1) = true ∧
      s.all (fun p => p ∈ expectedValid3_2) = true := by decide

-- 4. `q > n` (`n = 3, q = 5`): `subsetPairCount 3 5 = 3 ^ 3 = 27`, concrete refinement with
-- `Cslib.subsetPairCount`, and out-of-range fallback.
example : subsetPairCount 3 5 = 27 ∧ Cslib.subsetPairCount 3 5 = 27 ∧
    subsetPairCount 3 2 = Cslib.subsetPairCount 3 2 ∧
    ((List.range (subsetPairCount 3 5)).map (unrankSubsetPair 3 5)).Nodup ∧
    unrankSubsetPair 3 2 19 = ([false, false, false], [false, false, false], false) ∧
    unrankSubsetPair 3 2 100 = ([false, false, false], [false, false, false], false) :=
  ⟨by rw [subsetPairCount_eq]; decide, by decide, subsetPairCount_eq 3 2,
    by decide, by decide, by decide⟩

-- 5. Möbius alternating sum cancellation and degree-2 cube sum reconstruction via `run`.
private def testPoly3 (w : List Bool) : ℤ :=
  let x (i : ℕ) : ℤ := if w.getD i false then 1 else 0
  3 - 2 * x 0 + 5 * x 0 * x 2 + 7 * x 1 * x 2

private def innerCubeCount (e : List Bool) : ℤ :=
  (boolWords3.filter fun x => (List.range 3).all fun i => !e.getD i false || x.getD i false).length

private def mobiusStep3 (p : DecodedPair × ℤ) : ℤ :=
  let t := innerCubeCount p.1.1 * testPoly3 p.1.2.1
  if p.1.2.2 then p.2 - t else p.2 + t

example :
    SubsetPairFold.run (fun p : DecodedPair × ℤ => if p.1.2.2 then p.2 - 1 else p.2 + 1) 3 2 0 = 1 ∧
    (boolWords3.map testPoly3).sum = 40 ∧
    SubsetPairFold.run mobiusStep3 3 2 0 = 40 ∧
    SubsetPairFold.run mobiusStep3 3 1 0 = 16 := by decide

-- 6. Composite `fun_prop` synthesis for `pascalTable`, `subsetPairCount`, and `unrankSubsetPair`.
example : ComputableInPolyTime
    (fun p : ℕ × ℕ => subsetPairCount (p.1 + 1) p.2 + (pascalTable p.1).length)
    encParams encNat := by unfold encParams; fun_prop

example : ComputableInPolyTime
    (fun p : (ℕ × ℕ) × ℕ => let d := unrankSubsetPair p.1.1 p.1.2 p.2; d.1.zipWith Bool.xor d.2.1)
    (encPair encParams encNat) encBits := by
  have hunr : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => unrankSubsetPair p.1.1 p.1.2 p.2)
      (encPair encParams encNat) encDecodedPair := by fun_prop
  exact ComputableInPolyTime.bitsZipWithInput Bool.xor
    ((ComputableInPolyTime.fst encBits (encPair encBits encBool)).comp hunr)
    ((ComputableInPolyTime.fst encBits encBool).comp
      ((ComputableInPolyTime.snd encBits (encPair encBits encBool)).comp hunr))

-- 7. Concrete `SubsetPairFold.computableInO` and polynomial live-workspace instantiation.
private noncomputable def parityCallbackCert :
    NativeCertificate (fun p : DecodedPair × Bool => Bool.xor p.1.2.2 p.2)
      (encPair encDecodedPair encBool) encBool :=
  NativeCertificate.ofPolyTime (by unfold encDecodedPair; fun_prop)

example : ∃ T S, ComputableInO (fun p : ℕ × ℕ =>
      SubsetPairFold.run (fun x : DecodedPair × Bool => Bool.xor x.1.2.2 x.2) p.1 p.2 false)
      encParams encBool T S ∧ PolyBounded (fun p : ℕ × ℕ => (encParams p).length) S := by
  let cn := NativeCertificate.linear (ComputableInO.fst encUnary encUnary)
  let cq := NativeCertificate.linear (ComputableInO.snd encUnary encUnary)
  let ci : NativeCertificate (fun _ : ℕ × ℕ => false) encParams encBool := .const false
  have hcb_poly : parityCallbackCert.IsPolynomial := NativeCertificate.ofPolyTime_isPolynomial _
  obtain ⟨ct, dt, hct⟩ := hcb_poly.1.exists_le; obtain ⟨cs, ds, hcs⟩ := hcb_poly.2.exists_le
  let boundIn (p : ℕ × ℕ) : ℕ := 8 * p.1 + 8
  have hlen_in : ∀ (p : ℕ × ℕ) (j : ℕ) (acc : Bool),
      (encPair encDecodedPair encBool (unrankSubsetPair p.1 p.2 j, acc)).length ≤ boundIn p := by
    intro p j acc
    simp only [encDecodedPair, length_encPair, encBits_apply, length_fst_unrankSubsetPair,
      length_snd_unrankSubsetPair, encBool_apply, List.length_singleton, boundIn]; omega
  refine ⟨_, _, SubsetPairFold.computableInO cn cq ci parityCallbackCert
    (fun p => ct * (boundIn p + 1) ^ dt) (fun p => cs * (boundIn p + 1) ^ ds) (fun _ => 1)
    (fun p j _ => (hct _).trans (Nat.mul_le_mul_left ct
      (Nat.pow_le_pow_left (Nat.add_le_add_right (hlen_in p j _) 1) dt)))
    (fun p j _ => (hcs _).trans (Nat.mul_le_mul_left cs
      (Nat.pow_le_pow_left (Nat.add_le_add_right (hlen_in p j _) 1) ds)))
    (fun _ _ _ => by simp [encBool_apply]), ?_⟩
  have hp1 : PolyBounded (fun p : ℕ × ℕ => (encParams p).length) Prod.fst :=
    PolyBounded.self.mono fun p => by
      simp only [encParams, length_encPair, encUnary_apply, List.length_replicate]; omega
  have hboundIn : PolyBounded (fun p : ℕ × ℕ => (encParams p).length) boundIn :=
    ((PolyBounded.const 8).mul hp1).add (.const 8)
  exact SubsetPairFold.polyBounded_space_of_polyBounded cn cq ci
    (NativeCertificate.linear_isPolynomial _) (NativeCertificate.linear_isPolynomial _)
    (NativeCertificate.const_isPolynomial false) (.const 1)
    (NativeCertificate.polyBounded_pow_of_polyBounded hboundIn cs ds)
