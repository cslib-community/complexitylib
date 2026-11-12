/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Probabilistic.AffineHash
import CslibFrontier.Probability.BitString.LinearHash.Collisions
import CslibFrontier.Tactic.PPT

/-! Matrix and affine hashing through ordinary functional programs and public-output tests. -/

namespace CslibFrontierTests.LinearHash

open Cslib Cslib.BitString Cslib.BitString.LinearHash Cslib.Probability
open Cslib.Probability.PMF Turing.MultiTapeTM

-- A partial final matrix row is padded with false, rather than discarded.
example : wordHash 2 [true, false, true] [true, true] = [true, true] := by decide

-- Empty inputs retain the requested number of zero-width rows and output bits.
example : wordHash 3 [true, true] [] = [false, false, false] := by decide

example : ProbComp.eval (extract 3 []) = PMF.pure [false, false, false] := by
  simp [extract, wordHash, listRows, listRow]

-- Zero digest bits require no matrix bits, whatever the source length.
example (input : List Bool) : ProbComp.eval (extract 0 input) = PMF.pure [] := by
  simp [extract, wordHash, listRows]

-- The digest marginal can be uniform while the complete output repeats its public seed.
example : ProbComp.eval (extract 1 [true]) =
    (PMF.uniformOfFintype Bool).map (fun bit => [bit, bit]) := by
  simp [extract, sampleList, wordHash, listRows, listRow]

-- The hash count and both words can be computed from an alternatively encoded caller.
example : ComputableInPolyTime
    (fun p : List Bool × ℕ => wordHash (p.2 + 1) (p.1 ++ [true]) p.1)
    (encPair (encList encBool) encUnary) encBits := by fun_prop

-- A nested second projection uses the same conversion rule, independent of hashing.
example : ComputableInPolyTime
    (fun p : ℕ × (Bool × List Bool) => p.2.2)
    (encPair encUnary (encPair encBool (encList encBool))) encBits := by fun_prop

-- Encoding conversion also works in the other direction when its certificate is available.
example : ComputableInPolyTime (fun p : ℕ × List Bool => p.2)
    (encPair encUnary encBits) (encList encBool) := by fun_prop

example : IsPPTOn (encPair encBits encUnary) encBits
    (fun p : List Bool × ℕ => extract (p.2 + 1) (p.1 ++ [false])) := by ppt

example : IsPPTOn (encPair (encList encBool) encUnary) encBits
    (fun p : List Bool × ℕ => extract (p.2 + 1) (p.1 ++ [false])) := by ppt

-- The same sampler written with explicit binds certifies without a syntax-specific rule.
example : IsPPTOn (encPair (encList encBool) encUnary) encBits
    (fun p : List Bool × ℕ =>
      sampleList ((p.2 + 1) * (p.1 ++ [false]).length) >>= fun seed =>
        pure (seed ++ wordHash (p.2 + 1) seed (p.1 ++ [false]))) := by ppt

-- Tests may randomize based on the entire output; for `m = 2` digest bits and a uniform 2-bit
-- source, `extract_dist_bind_le` gives a concrete distance bound of `1 / 2`.
example (test : List Bool → PMF Bool) :
    dist ((((PMF.uniformOfFintype (BitString 2)).map List.ofFn).bind
      (fun input => ProbComp.eval (extract 2 input))).bind test)
        ((uniformList 6).bind test) ≤ 1 / 2 := by
  apply (extract_dist_bind_le (m := 2) (PMF.uniformOfFintype (BitString 2)) test).trans
  rw [collisionProbability_uniform]
  norm_num [BitString]

-- The finite matrix maps in the collision theorem are linear over the Boolean ring.
example {n m : ℕ} (rows : Fin m → BitString n) (x y : BitString n) :
    hash rows (x + y) = hash rows x + hash rows y := by
  ext i
  simp [Cslib.BitString.LinearHash.hash, dotProduct_add]

-- Three inputs need at most two digest bits, independently of the ambient input width.
example {n : ℕ} (S : Finset (BitString n)) (hS : S.card ≤ 3) :
    ∃ rows : Fin 2 → BitString n, Set.InjOn (hash rows) S :=
  exists_injOn S ((Nat.choose_le_choose 2 hS).trans_lt (by decide))

-- The zero-bit output case applies to the singleton zero-width input space.
example : ∃ rows : Fin 0 → BitString 0,
    Set.InjOn (hash rows) (Finset.univ : Finset (BitString 0)) :=
  exists_injOn Finset.univ (by decide)

-- It does not make a zero-bit digest injective on a two-element set.
example : ¬ ∃ rows : Fin 0 → BitString 1,
    Set.InjOn (hash rows) (Finset.univ : Finset (BitString 1)) := by decide

-- Independently search all four one-row matrices for every subset of the two-bit cube.
-- This counts ordered distinct pairs; the general theorem also permits one orientation only.
/-- info: true -/
#guard_msgs in
#eval decide (∀ S : Finset (BitString 2), ∃ rows : Fin 1 → BitString 2,
  2 * (S.offDiag.filter fun p => hash rows p.1 = hash rows p.2).card ≤ S.offDiag.card)

/-! ### Word-level affine seeds, affine hashes, and zero tests -/

-- Identity matrix with shift `(1, 1)` sends `(1, 1)` to `(0, 0)` and `(1, 0)` to `(0, 1)`.
example :
    wordAffineHash 2 [true, false, false, true, true, true] [true, true] = [false, false] ∧
    hashZero 2 2 [true, false, false, true, true, true] [true, true] = true ∧
    wordAffineHash 2 [true, false, false, true, true, true] [true, false] = [false, true] ∧
    hashZero 2 2 [true, false, false, true, true, true] [true, false] = false := by decide

-- `hashZero k n` pads short inputs with `false` to width `n` before reading the `k * n` matrix
-- bits and `k` shift bits, ignores extra input bits past `n`, and pads short seeds with `false`.
example :
    hashZero 1 2 [false, true, true] [true] = false ∧
    hashZero 1 2 [true, false, true] [true] = true ∧
    hashZero 1 2 [true, false, true] [true, false, true] = true ∧
    hashZero 1 2 [true] [false, true] = true ∧
    hashZero 1 2 [true] [true, true] = false := by decide

-- Exhaustive check on `k = 2, n = 2` (64 seeds, 4 inputs): `packAffineSeed` and `affineSeedEquiv`
-- round-trip, `hashZero` agrees with the kernel of `affineHash`, and every input hits zero on
-- exactly `64 / 4 = 16` seeds.
example :
    (∀ r : BitString 6, packAffineSeed (affineSeedEquiv 2 2 r) = List.ofFn r) ∧
    (∀ (r : BitString 6) (x : BitString 2),
      hashZero 2 2 (List.ofFn r) (List.ofFn x) =
        decide (LinearHash.affineHash (affineSeedEquiv 2 2 r) x = 0)) ∧
    (∀ x : BitString 2,
      (Finset.univ.filter fun r : BitString 6 =>
        hashZero 2 2 (List.ofFn r) (List.ofFn x) = true).card = 16) := by decide

-- `fun_prop` synthesizes plain polynomial-time certificates for `wordAffineHash` and `hashZero`,
-- and `ppt` certifies uniform seed sampling followed by `hashZero`.
example : ComputableInPolyTime
    (fun p : List Bool × ℕ => wordAffineHash (p.2 + 1) (p.1 ++ [true]) p.1)
    (encPair (encList encBool) encUnary) encBits := by fun_prop

example : ComputableInPolyTime
    (fun p : List Bool × (ℕ × ℕ) => hashZero (p.2.1 + 1) p.2.2 (p.1 ++ [true]) p.1)
    (encPair (encList encBool) (encPair encUnary encUnary)) encBool := by fun_prop

example : IsPPTOn (encPair encBits (encPair encUnary encUnary)) encBool
    (fun p : List Bool × (ℕ × ℕ) => do
      let seed ← sampleList (p.2.1 * p.2.2 + p.2.1)
      return hashZero p.2.1 p.2.2 seed p.1) := by ppt

end CslibFrontierTests.LinearHash

-- Plain callbacks share the entire captured input; no sampler or raw certificate is required.
example {α : Type} {encode : α ↪ List Bool}
    {count : α → ℕ} {seed input : α → List Bool}
    (hcount : Turing.MultiTapeTM.ComputableInPolyTime count encode Turing.MultiTapeTM.encUnary)
    (hseed : Turing.MultiTapeTM.ComputableInPolyTime seed encode Turing.MultiTapeTM.encBits)
    (hinput : Turing.MultiTapeTM.ComputableInPolyTime input encode Turing.MultiTapeTM.encBits) :
    Turing.MultiTapeTM.ComputableInPolyTime
      (fun a => Cslib.BitString.LinearHash.wordHash (count a) (seed a) (input a))
      encode Turing.MultiTapeTM.encBits := by
  fun_prop
