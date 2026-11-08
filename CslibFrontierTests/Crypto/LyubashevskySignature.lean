/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Protocols.SigmaProtocol.Lyubashevsky.Signature
import CslibFrontier.Probability.PMF

/-!
# Tests for Lyubashevsky Fiat–Shamir-with-aborts signatures and SIS reductions

Concrete checks over `ZMod 7` with `n = 1`, `m = 2`, `k = 1`, `γ = 2`, `β = 1`, and `η = 1`:
1. Scalar-challenge and unit-challenge SIS collision reductions (`isSISSolution_sub_secret`,
   `isSISSolution_sub_smul_secret`).
2. Homogeneous SIS extraction (`extractSISFromTwoTranscripts`, `lyubashevskyForkToSIS`) from two
   accepting transcripts whose response difference differs from the honest secret key's shift.
3. Single-attempt and bounded `K`-attempt Fiat–Shamir-with-aborts signing (`fsAbortSignStep`,
   `lyubashevskySignAttempt`, `lyubashevskySignBounded`), signature verification
   (`lyubashevskyVerifySig`), exact multi-attempt abort probability `(1 - (3 / 5) ^ 2) ^ 2`,
   and signature forking extraction into both relaxed `[A | T]` and homogeneous `A` SIS solutions.
-/

namespace ComplexityTests.Crypto.LyubashevskySignature

open Cslib Cslib.Crypto Cslib.Probability Cslib.Probability.PMF Cslib.Crypto.Protocols
  SigmaProtocol
open scoped ENNReal

/-- Public matrix `A = (1, 2)` over `ZMod 7`. -/
abbrev A : Matrix (Fin 1) (Fin 2) (ZMod 7) := !![1, 2]

/-- Honest secret witness `S = (1, -1)ᵀ` with entries in `[-1, 1]`. -/
abbrev S : Matrix (Fin 2) (Fin 1) ℤ := !![1; -1]

/-- Public image `T = A S = (6)` modulo `7`. -/
abbrev T : Matrix (Fin 1) (Fin 1) (ZMod 7) := !![6]

/-- Lyubashevsky protocol instance with `γ = 2` and `β = 1`. -/
noncomputable abbrev P := lyubashevsky 1 2 1 7 2 1

/-! ### 1. Scalar-challenge SIS collision reductions -/

/-- Two distinct short vectors `v = (-1, 0)` and `s = (1, -1)` with `A v = A s = (6)` yield the
short kernel vector `v - s = (-2, 1)` of `A` with bound `1 + 1 = 2`. -/
example : SIS.IsSolution A 2 (![-1, 0] - ![1, -1]) :=
  isSISSolution_sub_secret (B := 1) (η := 1) (t := ![6])
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Scalar challenge difference `Δc = 2`: `v = (-2, 0)` satisfies `A v = 2 • (6) = (5)` and
`v ≠ 2 • s`, so `v - 2 • s = (-4, 2)` is a short integer solution for `A` with bound `2 + 2 = 4`. -/
example : SIS.IsSolution A (2 + (2 : ℤ).natAbs * 1) (![-2, 0] - (2 : ℤ) • ![1, -1]) :=
  isSISSolution_sub_smul_secret (B := 2) (η := 1) (t := ![6]) (Δc := 2)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-! ### 2. Homogeneous SIS extraction from two transcripts -/

/-- At commitment `w = (1)`, both `(c₁ = [true], z₁ = (0, 0))` and `(c₂ = [false], z₂ = (1, 0))`
are accepting conversations for `(A, T)`, and their response difference `(-1, 0)` differs from
`S (ĉ₁ - ĉ₂) = (1, -1)`. Folding through `S` extracts `(-2, 1)`, a short integer solution for `A`
with bound `2 (γ - β) + k η = 3`. -/
example : extractSISFromTwoTranscripts S ![true] (some ![0, 0]) ![false] (some ![1, 0]) =
    ![-2, 1] := by
  decide

example : SIS.IsSolution A 3
    (extractSISFromTwoTranscripts S ![true] (some ![0, 0]) ![false] (some ![1, 0])) :=
  lyubashevskyForkToSIS (n := 1) (m := 2) (k := 1) (q := 7) (γ := 2) (β := 1) (η := 1)
    (y := (A, T)) (w := ![1]) (by decide) (by decide) (by decide) (by decide)

/-! ### 3. Fiat–Shamir with aborts: signing, verification, retry law, and forking -/

/-- Constant hash oracle returning challenge `[true]`. -/
def hTrue : Bool × (Fin 1 → ZMod 7) → BitString 1 := fun _ => ![true]

/-- Constant hash oracle returning challenge `[false]`. -/
def hFalse : Bool × (Fin 1 → ZMod 7) → BitString 1 := fun _ => ![false]

/-- For commitment randomness `r = (0, 1)` (commitment `w = (2)`), the deterministic signing step
succeeds with signature `((2), (1, 0))`; for `r = (1, 0)` it aborts (`none`). -/
example : fsAbortSignStep P hTrue S (A, T) true (![2], ![0, 1]) = some (![2], ![1, 0]) := by
  decide

example : fsAbortSignStep P hTrue S (A, T) true (![1], ![1, 0]) = none := by
  decide

/-- The produced signature `((2), (1, 0))` is in the support of both single-attempt and 2-attempt
signing, and passes `lyubashevskyVerifySig`. -/
theorem mem_support_signAttempt_example :
    some ((![2] : Fin 1 → ZMod 7), (![1, 0] : Fin 2 → ℤ)) ∈
      (lyubashevskySignAttempt 1 2 1 7 2 1 hTrue S (A, T) true).support := by
  have hcomm : ((![2] : Fin 1 → ZMod 7), (![0, 1] : Fin 2 → ℤ)) ∈ (P.commit S (A, T)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr
      ⟨![0, 1], (mem_support_uniformOfFinset_iff _ _).mpr (by decide), by decide⟩
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨(![2], ![0, 1]), hcomm, by decide⟩

example : lyubashevskyVerifySig 1 2 1 7 2 1 hTrue (A, T) true (![2], ![1, 0]) = true :=
  lyubashevskyVerifySig_of_lyubashevskySignAttempt_eq_some (S := S) hTrue (by decide)
    mem_support_signAttempt_example

example : lyubashevskyVerifySig 1 2 1 7 2 1 hTrue (A, T) true (![2], ![1, 0]) = true := by
  refine lyubashevskyVerifySig_of_lyubashevskySignBounded_eq_some (S := S) (K := 2) hTrue
    (by decide) ?_
  simp only [lyubashevskySignBounded, fsAbortSignBounded, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff]
  exact ⟨some (![2], ![1, 0]), mem_support_signAttempt_example, by simp⟩

/-- With constant challenge `[true]`, a single signing attempt has the exact abort probability
`1 - (3 / 5) ^ 2` of `acceptedTranscript`, so 2 independent attempts abort with probability
`(1 - (3 / 5) ^ 2) ^ 2`. -/
example : lyubashevskySignBounded 1 2 1 7 2 1 hTrue 2 S (A, T) true none =
    (1 - (3 / 5) ^ 2) ^ 2 := by
  rw [lyubashevskySignBounded_apply_none]
  have hattempt : lyubashevskySignAttempt 1 2 1 7 2 1 hTrue S (A, T) true =
      P.acceptedTranscript S (A, T) ![true] := by
    simp only [lyubashevskySignAttempt, fsAbortSignAttempt, acceptedTranscript,
      transcript, PMF.map_comp]
    rfl
  rw [hattempt,
    lyubashevsky_acceptedTranscript_none (η := 1) (by norm_num) (by norm_num) (by decide)]
  norm_num

/-- Two valid signatures `((1), (0, 0))` under `hTrue` and `((1), (1, 0))` under `hFalse` share
commitment `w = (1)` at distinct challenges and yield both a relaxed `[A | T]` solution and a
homogeneous `A` solution via `lyubashevskySignatureForkToRelaxedSIS` and
`lyubashevskySignatureForkToSIS`. -/
example : SIS.IsSolution (Matrix.fromCols A T) 2
    (lyubashevskyExtract 1 2 1 7 (A, T) ![1] (hTrue (true, ![1])) (some ![0, 0])
      (hFalse (true, ![1])) (some ![1, 0])) :=
  lyubashevskySignatureForkToRelaxedSIS (γ := 2) (β := 1) (y := (A, T))
    (by decide) (by decide) (by decide)

example : SIS.IsSolution A 3
    (extractSISFromTwoTranscripts S (hTrue (true, ![1])) (some ![0, 0])
      (hFalse (true, ![1])) (some ![1, 0])) :=
  lyubashevskySignatureForkToSIS (γ := 2) (β := 1) (η := 1) (y := (A, T))
    (by decide) (by decide) (by decide) (by decide)

end ComplexityTests.Crypto.LyubashevskySignature
