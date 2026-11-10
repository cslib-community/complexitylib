/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Crypto.Computational.HashAndSign

/-!
# Tests for the Collision-Resistant Hash-and-Sign Paradigm

Provides concrete instantiations of `HashAndSign.scheme`, `HashAndSign.collisionFinder`,
`HashAndSign.baseForger`, and `HashAndSign.fixedCollisionForger` on explicit fixed-length
signature and compression schemes, verifies compact signature evaluation and verification on
arbitrary-length bit strings via Merkle–Damgård hashing, checks collision extraction from forgery
logs, and demonstrates necessity of collision resistance against a constant hash family.
-/

namespace CslibFrontierTests.Crypto.HashAndSign

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

/-- Concrete fixed-length signature scheme that echoes the `n`-bit message as its signature and
verifies equality `sig == msg`. -/
def echoSignatureScheme : SignatureScheme where
  keyGen _ := pure ([], [])
  sign _ msg := pure msg
  verify _ msg sig := sig == msg
  keyGen_ppt := by ppt
  sign_ppt := by ppt
  verify_polyTime := by polytime
  verify_sign := by
    intro _ _ _ msg _ sig hsig
    simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hsig
    subst hsig
    exact beq_self_eq_true _

theorem sig_length_le_echoSignatureScheme (n : ℕ) (keys : List Bool × List Bool)
    (_ : keys ∈ (ProbComp.eval (echoSignatureScheme.keyGen n)).support)
    (msg : List Bool) (hmsg : msg.length = n) (sig : List Bool)
    (hsig : sig ∈ (ProbComp.eval (echoSignatureScheme.sign keys.2 msg)).support) :
    sig.length ≤ id n := by
  change sig ∈ (ProbComp.eval (pure msg)).support at hsig
  rw [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hsig
  subst hsig
  exact hmsg.le

/-- Concrete `2n → n` XOR compression function: split `x` into two `k.length`-bit halves
(normalized via `padOrTake k.length`) and XOR them bitwise. -/
def xorCompress (k x : List Bool) : List Bool :=
  (padOrTake k.length (x.take k.length)).zipWith Bool.xor
    (padOrTake k.length (x.drop k.length))

theorem length_xorCompress (k x : List Bool) : (xorCompress k x).length = k.length := by
  simp [xorCompress]

theorem computableInPolyTime_xorCompress :
    ComputableInPolyTime (fun p : List Bool × List Bool => xorCompress p.1 p.2)
      (encPair encBits encBits) encBits := by
  unfold xorCompress padOrTake
  polytime

theorem computableInPolyTime_mdXor :
    ComputableInPolyTime
      (fun p : List Bool × List Bool => merkleDamgard xorCompress p.1 p.2)
      (encPair encBits encBits) encBits :=
  computableInPolyTime_merkleDamgard computableInPolyTime_xorCompress
    (fun k x _ => length_xorCompress k x)

theorem length_mdXor (s msg : List Bool) :
    (merkleDamgard xorCompress s msg).length = s.length :=
  length_merkleDamgard (fun x _ => length_xorCompress s x)

/-- Concrete `WordSignatureScheme` obtained by applying `HashAndSign.scheme` to
`echoSignatureScheme` and `merkleDamgard xorCompress`. -/
noncomputable def mdEchoWordScheme : WordSignatureScheme :=
  HashAndSign.scheme echoSignatureScheme (merkleDamgard xorCompress)
    computableInPolyTime_mdXor length_mdXor

-- Signing an arbitrary-length message under a packed key `(sk₀, s)` produces a raw 2-bit digest
-- signature with no per-signature hash-key overhead:
example : HashAndSign.sign echoSignatureScheme (merkleDamgard xorCompress)
      (encPair encBits encBits ([], [false, false])) [false, true] =
    pure [false, true] := by
  rw [HashAndSign.sign_encPair]
  rfl

-- Verification accepts the matching signature on `[false, true]` and rejects a modified message:
example : HashAndSign.verify echoSignatureScheme (merkleDamgard xorCompress)
      (encPair encBits encBits ([], [false, false])) [false, true] [false, true] = true := by
  rw [HashAndSign.verify_encPair]
  decide

example : HashAndSign.verify echoSignatureScheme (merkleDamgard xorCompress)
      (encPair encBits encBits ([], [false, false])) [] [false, true] = false := by
  rw [HashAndSign.verify_encPair]
  decide

-- Collision extraction from a forgery log: `[false, false]` and `[]` collide under
-- `merkleDamgard xorCompress [false, false]`, so `collisionOf` extracts `([false, false], [])`.
example : HashAndSign.collisionOf (merkleDamgard xorCompress) [false, false]
      (([false, false], [false, false]), [[false, true], []]) =
    ([false, false], []) := rfl

example : isCollision (merkleDamgard xorCompress) (fun _ _ => true) 2 [false, false]
      (HashAndSign.collisionOf (merkleDamgard xorCompress) [false, false]
        (([false, false], [false, false]), [[false, true], []])).1
      (HashAndSign.collisionOf (merkleDamgard xorCompress) [false, false]
        (([false, false], [false, false]), [[false, true], []])).2 = true :=
  HashAndSign.isCollision_collisionOf_of_isSome (merkleDamgard xorCompress)
    (by decide) (by decide)

/-- Concrete one-query collision forger with identity signature-length bound `bound n = n`. -/
abbrev idCollisionForger : Forger :=
  HashAndSign.fixedCollisionForger id [] [true]

theorem isOraclePPT_idCollisionForger :
    IsOraclePPT (encPair encBits encBits) idCollisionForger :=
  HashAndSign.isOraclePPT_fixedCollisionForger .id' [] [true]

-- Plain PPT and OraclePPT certificates for the two reduction adversaries of Theorem 13.4:
example : IsPPT (encPair encBits encBits)
    (HashAndSign.collisionFinder echoSignatureScheme (merkleDamgard xorCompress)
      computableInPolyTime_mdXor length_mdXor idCollisionForger) :=
  HashAndSign.isPPT_collisionFinder echoSignatureScheme (merkleDamgard xorCompress)
    computableInPolyTime_mdXor length_mdXor isOraclePPT_idCollisionForger

example : IsOraclePPT (encPair encBits encBits)
    (HashAndSign.baseForger (merkleDamgard xorCompress) id idCollisionForger) :=
  HashAndSign.isOraclePPT_baseForger (merkleDamgard xorCompress)
    computableInPolyTime_mdXor .id' isOraclePPT_idCollisionForger

-- Pointwise reduction inequality for `mdEchoWordScheme` against `idCollisionForger`:
example (n : ℕ) :
    Game.succProbability (ProbComp.eval (mdEchoWordScheme.eufCmaGame idCollisionForger n)) ≤
      Game.succProbability
        (ProbComp.eval (echoSignatureScheme.eufCmaGame
          (HashAndSign.baseForger (merkleDamgard xorCompress) id idCollisionForger) n)) +
      Game.succProbability
        (ProbComp.eval (collisionGame (merkleDamgard xorCompress) (fun _ _ => true)
          (HashAndSign.collisionFinder echoSignatureScheme (merkleDamgard xorCompress)
            computableInPolyTime_mdXor length_mdXor idCollisionForger) n)) :=
  HashAndSign.succProbability_eufCmaGame_le echoSignatureScheme (merkleDamgard xorCompress)
    computableInPolyTime_mdXor length_mdXor sig_length_le_echoSignatureScheme
    idCollisionForger n

/-- Trivial length-preserving hash family that ignores the message and returns the key `s`. -/
def constHash (s _ : List Bool) : List Bool := s

theorem computableInPolyTime_constHash :
    ComputableInPolyTime (fun p : List Bool × List Bool => constHash p.1 p.2)
      (encPair encBits encBits) encBits :=
  ComputableInPolyTime.fst encBits encBits

theorem length_constHash (s msg : List Bool) : (constHash s msg).length = s.length := rfl

-- Under `constHash`, `idCollisionForger` queries `[]` and forges on `[true]` with probability 1:
example (n : ℕ) :
    Game.succProbability
      (ProbComp.eval
        ((HashAndSign.scheme echoSignatureScheme constHash
            computableInPolyTime_constHash length_constHash).eufCmaGame
          idCollisionForger n)) = 1 :=
  HashAndSign.succProbability_eufCmaGame_fixedCollisionForger echoSignatureScheme constHash
    computableInPolyTime_constHash length_constHash sig_length_le_echoSignatureScheme
    (List.cons_ne_nil true []) (fun _ => rfl) n

/-- Instantiating Construction 13.3 with `constHash` is never `EUFCMA`-secure for any base
`SignatureScheme` `S`. -/
theorem not_eufCMA_constHash (S : SignatureScheme) :
    ¬ (HashAndSign.scheme S constHash computableInPolyTime_constHash length_constHash).EUFCMA :=
  HashAndSign.not_eufCMA_scheme_of_collision S constHash
    computableInPolyTime_constHash length_constHash (m₀ := []) (m₁ := [true])
    (List.cons_ne_nil true []) (fun _ => rfl)

end CslibFrontierTests.Crypto.HashAndSign
