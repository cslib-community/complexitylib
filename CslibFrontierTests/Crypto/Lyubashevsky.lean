/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.SIS.Basic
import CslibFrontier.Crypto.Protocols.SigmaProtocol.Lyubashevsky
import CslibFrontier.Crypto.Protocols.SigmaProtocol.Lyubashevsky.Efficient
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF

/-!
# Tests for SIS, box rejection sampling and Lyubashevsky identification

Short integer solutions, the exact box rejection-sampling law, and a
run of Lyubashevsky's protocol over `ZMod 7` with `n = 1`, `m = 2`, `k = 1`, `γ = 2`, `β = 1` and
witness entries bounded by `η = 1`. The block checks honest answers and an abort, runs the
extractor on two conversations with a common commitment, and evaluates the simulator's law.
-/

namespace CslibFrontierTests.Crypto.Lyubashevsky

open Cslib Cslib.Crypto Cslib.Probability Cslib.Probability.PMF Cslib.Crypto.Protocols
  SigmaProtocol Turing.MultiTapeTM
open scoped ENNReal

/-! ### Short integer solutions -/

/-- `(1, 1, -1)` is a short solution for the row `(1, 2, 3)` modulo `7`. -/
example : SIS.IsSolution !![(1 : ZMod 7), 2, 3] 1 ![1, 1, -1] := by decide

/-- The zero vector is never a solution, and the bound is enforced. -/
example : ¬SIS.IsSolution !![(1 : ZMod 7), 2, 3] 1 0 := by decide
example : ¬SIS.IsSolution !![(1 : ZMod 7), 2, 3] 1 ![2, -1, 0] := by decide
example : SIS.IsSolution !![(1 : ZMod 7), 2, 3] 2 ![2, -1, 0] := by decide

/-! ### Lyubashevsky's protocol

The statement is `A = (1, 2)` and `T = A S = (6)` for the witness `S = (1, -1)ᵀ`. With the
commitment randomness `y = (0, 1)` the commitment is `w = A y = 2`. The challenge `0` gets the
answer `y = (0, 1)` and the challenge `1` gets `y + S = (1, 0)`; both lie in the inner box
`[-1, 1]²`. -/

/-- The public matrix. -/
abbrev A : Matrix (Fin 1) (Fin 2) (ZMod 7) := !![1, 2]

/-- The witness. -/
abbrev S : Matrix (Fin 2) (Fin 1) ℤ := !![1; -1]

/-- The image `T = A S`. -/
abbrev T : Matrix (Fin 1) (Fin 1) (ZMod 7) := !![6]

/-- The protocol with `γ = 2` and `β = 1`. -/
noncomputable abbrev P := lyubashevsky 1 2 1 7 2 1

example : lyubashevskyRelation 1 S (A, T) := by decide

/-- The honest prover's answers to both challenges, for the randomness `(0, 1)`. -/
example : P.respond S (A, T) ![0, 1] ![false] = some ![0, 1] := by decide
example : P.respond S (A, T) ![0, 1] ![true] = some ![1, 0] := by decide

/-- For the randomness `(1, 0)` the challenge `1` would give `(2, -1)`, so the prover aborts. -/
example : P.respond S (A, T) ![1, 0] ![true] = none := by decide

/-- The commitment `2` for the randomness `(0, 1)` is a possible honest commitment. -/
example : ((![2] : Fin 1 → ZMod 7), (![0, 1] : Fin 2 → ℤ)) ∈ (P.commit S (A, T)).support :=
  (PMF.mem_support_map_iff _ _ _).mpr
    ⟨![0, 1], (mem_support_uniformOfFinset_iff _ _).mpr (by decide), by decide⟩

example : P.Accepts (A, T) ![2] ![false] (some ![0, 1]) := by decide
example : P.Accepts (A, T) ![2] ![true] (some ![1, 0]) := by decide
example : ¬P.Accepts (A, T) ![2] ![true] (some ![0, 1]) := by decide
example : ¬P.Accepts (A, T) ![2] ![true] none := by decide

/-- The extractor returns `(-1, 1, 1)`, and `[A | T] (-1, 1, 1) = -1 + 2 + 6 = 0` modulo `7`. -/
example : lyubashevskyExtract 1 2 1 7 (A, T) ![2] ![false] (some ![0, 1]) ![true]
    (some ![1, 0]) = Sum.elim ![-1, 1] ![1] := by
  decide

example : SIS.IsSolution (Matrix.fromCols A T) 2
    (lyubashevskyExtract 1 2 1 7 (A, T) ![2] ![false] (some ![0, 1]) ![true] (some ![1, 0])) :=
  lyubashevsky_specialSoundness (γ := 2) (β := 1) _ _ _ _ _ _ (by decide) (by decide) (by decide)

/-- At the challenge `1`, the prover aborts with probability `1 - (3 / 5) ^ 2 = 16 / 25`. -/
example : P.acceptedTranscript S (A, T) ![true] none = 1 - (3 / 5) ^ 2 := by
  rw [lyubashevsky_acceptedTranscript_none (η := 1) (by norm_num) (by norm_num) (by decide)]
  norm_num

/-- The simulator and the honest prover publish `(w, z) = (2, (1, 0))` at the challenge `1` with
probability `1 / 25`: the answer `(1, 0)` comes from one of the `25` points of `[-2, 2]²`. -/
theorem simulate_apply :
    lyubashevskySimulate 1 2 1 7 2 1 (A, T) ![true] (some (![2], ![1, 0])) = 25⁻¹ := by
  rw [lyubashevskySimulate, PMF.map_apply, tsum_eq_single (some ![1, 0])]
  · rw [ite_eq_left (by decide), boxReject, shiftReject_apply_some (fun _ hz => by
      rw [sub_zero]
      exact intBox_mono (by norm_num) hz), card_intBox, ite_eq_left (by decide)]
    norm_num
  · rintro (_ | z) hz
    · simp
    · rw [ite_eq_right]
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, not_and]
      exact fun _ h => hz (congrArg some h.symm)

example : P.acceptedTranscript S (A, T) ![true] (some (![2], ![1, 0])) = 25⁻¹ := by
  have h := (lyubashevsky_nonAbortSpecialHVZK (n := 1) (m := 2) (k := 1) (q := 7) (γ := 2)
    (β := 1) (η := 1) (by norm_num) (by norm_num)).acceptedTranscript_eq S (A, T) (by decide)
    ![true]
  rw [← h]
  exact simulate_apply

/-! ### Strict-PPT integer-box samplers and Lyubashevsky efficiency certificates -/

/-- `sampleIntBoxCoins` maps fair coin bits into `[-B, B]`. -/
example : sampleIntBoxCoins 2 [] = -2 := by decide
example : sampleIntBoxCoins 2 [true, true] = 1 := by decide
example : |sampleIntBoxCoins 2 [true, true, false, false]| ≤ (2 : ℤ) :=
  abs_sampleIntBoxCoins_le 2 [true, true, false, false]

/-- Dyadic centered box sampler maps `3` coin bits into `[-4, 3]`. -/
example : sampleDyadicIntBoxCoins 3 [] = -4 := by decide
example : sampleDyadicIntBoxCoins 3 [true, true, true] = 3 := by decide

/-- Runtime parameters `(n, m, k, width) = (1, 2, 1, 4)` and `(q, γ, β) = (7, 2, 1)`. -/
abbrev params : LyubashevskyParams :=
  { n := 1, m := 2, k := 1, width := 4, q := 7, γ := 2, β := 1 }

/-- `(S, (A, T))` satisfies `lyubashevskyFamilyRelation (fun _ => 1) params` (`β ≤ γ` and
`k * 1 ≤ β`). -/
example : lyubashevskyFamilyRelation (fun _ => 1) params S (A, T) := by decide

/-- The serialized verifier accepts the encoded accepting conversation `((A, T), ![2], ![true],
some ![1, 0])` and rejects `none`. -/
example :
    lyubashevskyVerifyWord
      (params,
        lyubashevskyEncoding.statement params (A, T),
        lyubashevskyEncoding.commitment params ![2],
        lyubashevskyEncoding.challenge params ![true],
        lyubashevskyEncoding.response params (some ![1, 0])) = true := by
  rw [verifierRealizedBy_lyubashevskyVerifyWord]
  decide

example :
    lyubashevskyVerifyWord
      (params,
        lyubashevskyEncoding.statement params (A, T),
        lyubashevskyEncoding.commitment params ![2],
        lyubashevskyEncoding.challenge params ![true],
        lyubashevskyEncoding.response params none) = false := by
  rw [verifierRealizedBy_lyubashevskyVerifyWord]
  decide

/-- On coin bits `[false, false, true, true] ++ [false, false, true, false]` (which decode via
`sampleIntBoxListCoins 2 2 4` to `z = [1, 0] ∈ [-1, 1]²`), `lyubashevskySimulateCoins` outputs the
encoded accepting transcript `(w, some z) = (![2], some ![1, 0])` for challenge `![true]`. -/
example :
    lyubashevskySimulateCoins
      ((params,
        lyubashevskyEncoding.statement params (A, T),
        lyubashevskyEncoding.challenge params ![true]),
        [false, false, true, true, false, false, true, false]) =
      some (lyubashevskyEncoding.commitment params ![2],
        lyubashevskyEncoding.response params (some ![1, 0])) := by
  have hcoins :
      sampleIntBoxListCoins params.γ params.m params.width
        [false, false, true, true, false, false, true, false] =
      List.ofFn (![1, 0] : Fin params.m → ℤ) := by decide
  rw [lyubashevskySimulateCoins, hcoins, lyubashevskySimulatePostprocess_ofFn,
    ite_eq_left (by decide)]
  congr 2

/-- On all-false coin bits (which decode to `z = [-2, -2] ∉ [-1, 1]²`), `lyubashevskySimulateCoins`
aborts with `none`. -/
example :
    lyubashevskySimulateCoins
      ((params,
        lyubashevskyEncoding.statement params (A, T),
        lyubashevskyEncoding.challenge params ![true]),
        List.replicate 8 false) = none := by
  decide

/-- Unconditional `EfficientNonAbortSpecialHVZK` certificate instantiated at `η = fun _ => 1`, and
its concrete statistical distance bound `2 * (5 / 16)` on `params` between the strict-PPT simulator
and the honest prover's encoded `acceptedTranscript`. -/
example :
    EfficientNonAbortSpecialHVZK lyubashevskyFamily
      (lyubashevskyFamilyRelation (fun _ => 1))
      lyubashevskyEncoding
      (fun p => lyubashevskySimulate p.n p.m p.k p.q p.γ p.β)
      (fun p => (p.m : ℝ≥0∞) * ((2 * p.γ + 1 : ℝ≥0∞) / 2 ^ p.width)) :=
  efficientNonAbortSpecialHVZK_lyubashevsky (fun _ => 1)

example (c : BitString params.k) :
    CloseTo
      (((lyubashevskyFamily params).acceptedTranscript S (A, T) c).map
        (Option.map fun tz =>
          (lyubashevskyEncoding.commitment params tz.1,
            lyubashevskyEncoding.response params (some tz.2))))
      (ProbComp.eval (lyubashevskySimulateWord
        (params,
          lyubashevskyEncoding.statement params (A, T),
          lyubashevskyEncoding.challenge params c)))
      ((params.m : ℝ≥0∞) * ((2 * params.γ + 1 : ℝ≥0∞) / 2 ^ params.width)) :=
  nonAbortSimulatorRealizedBy_lyubashevskySimulateWord.closeTo_acceptedTranscript
    (lyubashevskyFamily_nonAbortSpecialHVZK (fun _ => 1))
    (by decide : lyubashevskyFamilyRelation (fun _ => 1) params S (A, T)) c

example {p q : LyubashevskyParams} (hn : p.n = q.n) (hm : p.m = q.m) (hk : p.k = q.k)
    (hw : p.width = q.width) (hq : p.q = q.q) (hγ : p.γ = q.γ) (hβ : p.β = q.β) : p = q := by
  ext <;> assumption

section PolyTimeOpened

open ComputableInPolyTime

example : ComputableInPolyTime LyubashevskyParams.n encLyubashevskyParams encUnary := by
  fun_prop

example : ComputableInPolyTime LyubashevskyParams.m encLyubashevskyParams encUnary := by
  fun_prop

example : ComputableInPolyTime LyubashevskyParams.k encLyubashevskyParams encUnary := by
  fun_prop

example : ComputableInPolyTime LyubashevskyParams.width encLyubashevskyParams encUnary := by
  fun_prop

example : ComputableInPolyTime LyubashevskyParams.q encLyubashevskyParams encNat := by
  fun_prop

example : ComputableInPolyTime LyubashevskyParams.γ encLyubashevskyParams encNat := by
  fun_prop

example : ComputableInPolyTime LyubashevskyParams.β encLyubashevskyParams encNat := by
  fun_prop

example : ComputableInPolyTime
    (fun x : ℕ × ℕ =>
      ({ n := x.1, m := x.1, k := x.1, width := x.1, q := x.2, γ := x.2, β := x.2 } :
        LyubashevskyParams))
    (encPair encUnary encNat) encLyubashevskyParams := by
  fun_prop

end PolyTimeOpened

end CslibFrontierTests.Crypto.Lyubashevsky

namespace CslibFrontierTests.Crypto.LyubashevskyUnopened

open Cslib.Crypto.Protocols.SigmaProtocol (LyubashevskyParams encLyubashevskyParams)
open Turing.MultiTapeTM (ComputableInPolyTime encNat encPair encUnary)

example : ComputableInPolyTime LyubashevskyParams.n encLyubashevskyParams encUnary := by
  fun_prop

example : ComputableInPolyTime LyubashevskyParams.m encLyubashevskyParams encUnary := by
  fun_prop

example : ComputableInPolyTime LyubashevskyParams.q encLyubashevskyParams encNat := by
  fun_prop

example : ComputableInPolyTime
    (fun p : LyubashevskyParams =>
      ({ n := p.n, m := p.m, k := p.k, width := p.width, q := p.q, γ := p.γ, β := p.β } :
        LyubashevskyParams))
    encLyubashevskyParams encLyubashevskyParams := by
  fun_prop

end CslibFrontierTests.Crypto.LyubashevskyUnopened
