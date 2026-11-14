/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.SchnorrSignature.ForkPass
import CslibFrontier.Crypto.Computational.DiscreteLog.SchnorrGroup
import Mathlib.Tactic.NormNum.Prime

/-!
# Native Schnorr forking pass regressions

Check that one native step consumes a transcript on every call, programs and logs signing points,
answers repeated hash points from the table without using an answer, records distinct junk points
as own queries, and becomes a no-op on a new point once the answers run out. Check that the final
check names the own query of a fresh winning forgery and names nothing for a signed message.
-/

namespace CslibFrontierTests.Crypto.SchnorrForkPass

open Cslib Cslib.Crypto Cslib.Crypto.PrimeOrderGroupFamily Turing.MultiTapeTM

private def banks : SchnorrForkBanks :=
  ([([true], [false, true], [true, true]), ([false], [true, true], [false])],
    [[true, false], [false, false]])

private def empty : SchnorrForkState := ([], [], 0, 0)

-- A signing call returns `(t, z)`, programs `(msg, t)` with `c` (tag `0`) and logs `msg`.
example : schnorrForkStep banks (false, [true]) empty =
    (encPair encBits encBits ([true], [true, true]),
      ([(encPair encBits encBits ([true], [true]), [false, true], 0)], [[true]], 0, 1)) := by
  decide

-- A new hash point takes the next answer and becomes own query `0` (tag `1`).
example : schnorrForkStep banks (true, [false]) empty =
    ([true, false], ([([false], [true, false], 1)], [], 1, 1)) := by
  decide

-- A repeated hash point is answered from the table, uses no answer, but consumes a transcript.
example : schnorrForkStep banks (true, [false]) ([([false], [true, false], 1)], [], 1, 1) =
    ([true, false], ([([false], [true, false], 1)], [], 1, 2)) := by
  decide

-- A distinct junk point is a second own query (tag `2`).
example :
    schnorrForkStep banks (true, [true, true, true]) ([([false], [true, false], 1)], [], 1, 1) =
    ([false, false], ([([true, true, true], [false, false], 2), ([false], [true, false], 1)],
      [], 2, 2)) := by
  decide

-- Once the answers run out, a new point gets the empty reply and changes only the call count.
example : schnorrForkStep banks (true, [true]) ([], [], 2, 5) = ([], ([], [], 2, 5 + 1)) := by
  decide

/-- A forgery whose commitment is the recovered commitment for challenge `c`. -/
private def forgery (F : PrimeOrderGroupFamily) (d : F.Desc) (pk msg c z : List Bool) :
    List Bool × List Bool :=
  (msg, encPair encBits encBits (F.schnorrRecoverCommitBits (d, pk, c, z), z))

-- A fresh accepting forgery at a new point names that point as own query `0` (code `1`).
example (F : PrimeOrderGroupFamily) (d : F.Desc) (pk msg c z : List Bool) :
    F.schnorrForkFinish d pk [c] (forgery F d pk msg c z, ([], [], 0, 0)) = (1, c, z) := by
  have hdec := (Decoder.bits.pair Decoder.bits).decode_enc
    (F.schnorrRecoverCommitBits (d, pk, c, z), z)
  simp only [forgery, schnorrForkFinish, hdec]
  simp [schnorrSigVerifyBits_eq_decide_recover]

-- The same forgery on a signed message names nothing.
example (F : PrimeOrderGroupFamily) (d : F.Desc) (pk msg c z : List Bool) :
    F.schnorrForkFinish d pk [c] (forgery F d pk msg c z, ([], [msg], 0, 0)) = (0, c, z) := by
  have hdec := (Decoder.bits.pair Decoder.bits).decode_enc
    (F.schnorrRecoverCommitBits (d, pk, c, z), z)
  simp only [forgery, schnorrForkFinish, hdec]
  simp [schnorrSigVerifyBits_eq_decide_recover]

-- An accepting forgery at a point programmed by a signing call (tag `0`) names nothing.
example (F : PrimeOrderGroupFamily) (d : F.Desc) (pk msg c z : List Bool) :
    F.schnorrForkFinish d pk [c]
      (forgery F d pk msg c z,
        ([(encPair encBits encBits (msg, F.schnorrRecoverCommitBits (d, pk, c, z)), c, 0)],
          [], 0, 1)) = (0, c, z) := by
  have hdec := (Decoder.bits.pair Decoder.bits).decode_enc
    (F.schnorrRecoverCommitBits (d, pk, c, z), z)
  simp only [forgery, schnorrForkFinish, hdec]
  simp [schnorrSigVerifyBits_eq_decide_recover]

end CslibFrontierTests.Crypto.SchnorrForkPass
