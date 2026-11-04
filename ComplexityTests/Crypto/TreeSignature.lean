/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.TreeSignature
import Complexity.Tactic.PolyTime
import Complexity.Tactic.PPT

/-!
# Tests for stateless tree signatures

A toy indexed scheme `echo` whose signature on `(u, msg)` is the word `encPair encUnary encBits
(u, msg)` itself, with empty keys: insecure, but deterministic, so its seeded algorithms are
concrete. The tree scheme over `echo` with all-`false` coins, depth `n + 1`, is run at `n = 2` on
the leaf `[true, false, true]`: the signature has two certificates and verifies; a message, leaf
or depth mismatch is rejected. The generic seeded algorithms `IndexedSignatureScheme.seeded` and the
packaged `TreeSignature.scheme` are instantiated.
-/

namespace ComplexityTests.Crypto.TreeSignature

open Cslib Cslib.Crypto Cslib.Crypto.TreeSignature Cslib.Probability Turing.MultiTapeTM

/-- A toy indexed scheme with empty keys whose signatures are the signed pairs themselves. -/
noncomputable def echo : IndexedSignatureScheme where
  capacity _ := 2
  keyGen _ := pure ([], [])
  sign _ u msg := pure (encPair encUnary encBits (u, msg))
  verify _ u msg sig := sig == encPair encUnary encBits (u, msg)
  capacity_polyTime := ComputableInPolyTime.const _
  keyGen_ppt := (ComputableInPolyTime.const _).isPPTOn
  sign_ppt := by
    apply ComputableInPolyTime.isPPTOn
    polytime
  verify_polyTime := by polytime
  verify_sign _ _ _ _ _ _ sig hsig := by
    simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hsig
    simp [hsig]

/-- The concrete seeded algorithms of `echo`: no coins are needed. -/
noncomputable def echoSeeded : echo.Seeded where
  keyGenWith _ _ := ([], [])
  keyGenBudget _ := 0
  signWith _ u msg _ := encPair encUnary encBits (u, msg)
  signBudget _ _ _ := 0
  keyGenWith_polyTime := ComputableInPolyTime.const _
  keyGenBudget_polyTime := ComputableInPolyTime.const _
  keyGenWith_mem_support _ _ := by simp [echo]
  eval_keyGen _ _ _ := by
    simp only [echo, ProbComp.eval_pure]
    exact (PMF.map_const (BitString.uniformList _) ([], [])).symm
  signWith_polyTime := by polytime
  signBudget_polyTime := ComputableInPolyTime.const _
  signWith_mem_support _ _ _ _ := by simp [echo]
  eval_sign _ _ _ _ _ := by
    simp only [echo, ProbComp.eval_pure]
    exact (PMF.map_const (BitString.uniformList _) _).symm

/-- All-`false` coins of the requested length. -/
def zeroCoins (_ _ : List Bool) (L : ℕ) : List Bool := List.replicate L false

theorem computableInPolyTime_zeroCoins :
    ComputableInPolyTime (fun p : List Bool × List Bool × ℕ => zeroCoins p.1 p.2.1 p.2.2)
      (encPair encBits (encPair encBits encUnary)) encBits := by
  unfold zeroCoins
  polytime

/-- The tree scheme over `echo`, with secrets of length `n` and depth `n + 1`. -/
noncomputable abbrev echoTree : SignatureScheme :=
  scheme echo echoSeeded zeroCoins id (· + 1) computableInPolyTime_zeroCoins
    ComputableInPolyTime.id' (by polytime) (fun _ => le_rfl) (fun _ => Nat.succ_pos _)

/-! ### A run at `n = 2` -/

def key : List Bool := [true, false]
def leaf : List Bool := [true, false, true]
def msg : List Bool := [true, true]

/-- The public key: the parameter and the root's (empty) public key. -/
def pk : List Bool := encPair encUnary encBits (2, [])

-- The certification chain visits the nodes `[true]` and `[true, false]`, each certified by its
-- parent at the matching index.
example : (certify echo echoSeeded zeroCoins 2 key [true, false]).2.2 =
    [([], encPair encUnary encBits (1, [])), ([], encPair encUnary encBits (0, []))] := by
  decide +kernel

-- The honest signature at the leaf verifies.
example : verify echo (· + 1) pk msg (signWithLeaf echo echoSeeded zeroCoins 2 key leaf msg) =
    true := by
  decide +kernel

-- Another message is rejected.
example : verify echo (· + 1) pk [false, true]
    (signWithLeaf echo echoSeeded zeroCoins 2 key leaf msg) = false := by
  decide +kernel

-- A leaf of the wrong depth is rejected, even though its chain verifies.
example : verify echo (· + 1) pk msg
    (signWithLeaf echo echoSeeded zeroCoins 2 key [true, false] msg) = false := by
  decide +kernel

-- Replaying an internal certificate as the final signature is rejected by the depth check.
example : verify echo (· + 1) pk []
    (encodeSignature [true] [] (encPair encUnary encBits (1, []))) = false := by
  decide +kernel

-- Completeness and the packaged scheme, as instances.
example : echoTree.verify pk msg (signWithLeaf echo echoSeeded zeroCoins 2 key leaf msg) =
    true := by
  decide +kernel

noncomputable example (S : IndexedSignatureScheme) : S.Seeded := S.seeded

end ComplexityTests.Crypto.TreeSignature
