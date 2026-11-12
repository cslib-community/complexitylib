/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.IKNP
public import CslibFrontier.Foundations.Data.BitString.Flip
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool

/-!
# Malicious-Receiver Selective-Failure Attack on Unchecked IKNP OT Extension

This module formalizes the selective-failure attack of [IshaiKilianNissimPetrank2003], Section 3,
against the IKNP oblivious-transfer extension protocol `Cslib.Crypto.Protocols.MPC.iknpProtocol`
when the sender does not check that the receiver's base-OT columns have consistent row differences.

In `iknpProtocol`, party `1` (the extension receiver) chooses `m` bits `r : Fin m → Bool` and is
supposed to submit column pairs `(tⁱ, tⁱ + r)` to `batchOTSpec κ (BitString m)` for a uniform
matrix `T : Fin m → BitString κ`, while party `0` (the sender) queries with `s : BitString κ` and
replies with `Y j b = X j b + H j (qⱼ + b • s)`. Without a consistency check:

1. **Single-bit selective failure (`iknpSelectiveFailureColumns`):** flipping a single bit
   `(i₀, j₀)` in the `true`-column of base coordinate `i₀` leaves every row `j ≠ j₀` intact, while
   on row `j₀` the honest receiver's unmasked message equals `X j₀ (r j₀)` when `s i₀ = false`
   `X j₀ (r j₀) + (H j₀ (BitString.flipOn {i₀} (T j₀)) - H j₀ (T j₀))` when `s i₀ = true`. Thus
   failure depends on the sender's secret bit `s i₀`. When `X j₀ false` is known (fixed) and `H j₀`
   distinguishes `T j₀` from `BitString.flipOn {i₀} (T j₀)`, a single execution recovers `s i₀`
   with probability `1`, whereas any ideal-OT simulator against `batchOTFunctionality` guesses
   `s i₀` with probability `1 / 2` (`iknpSelectiveFailureSBit_advantage`).
2. **Full-key extraction and simultaneous recovery (`iknpFullAttackColumns`):** over `m = κ + 1`
   transfers where `κ` probe coordinates carry fixed known probe pairs `probe : Fin κ → Bool → L`
   and target coordinate `Fin.last κ` carries independent uniform `(m₀, m₁) ← L × L`, placing a
   diagonal single-bit probe on rows `0, …, κ - 1` and `(t_κ, t_κ + 1)` on row `κ` lets the
   malicious receiver recover every bit `s i` from rows `0, …, κ - 1` and decrypt **both**
   `(m₀, m₁)` on row `κ` with probability `1`. Any ideal-OT simulator that queries one choice vector
   `r' : Fin (κ + 1) → Bool` and sees only `(fun j => X j (r' j))` predicts `(m₀, m₁)` with
   probability at most `(Fintype.card L : ℝ)⁻¹`, yielding distinguishing advantage at least
   `1 - (Fintype.card L : ℝ)⁻¹` (`iknpFullAttack_malicious_receiver_advantage`).

## Main definitions

* `Cslib.Crypto.Protocols.MPC.iknpSenderReplyOf`: the sender's masked output in an IKNP-schedule
  protocol when a malicious receiver submits arbitrary base-OT column pairs `U`.
* `Cslib.Crypto.Protocols.MPC.iknpSelectiveFailureColumns`: malicious base-OT column pairs flipping
  one bit `(i₀, j₀)` of column `true` at base index `i₀`.
* `Cslib.Crypto.Protocols.MPC.iknpSelectiveFailureSBitRealGame`,
  `Cslib.Crypto.Protocols.MPC.iknpSelectiveFailureSBitIdealGame`: real and ideal games for
  recovering one bit `s i₀` of the sender's base-OT choice vector given a known probe value.
* `Cslib.Crypto.Protocols.MPC.iknpFullAttackColumns`,
  `Cslib.Crypto.Protocols.MPC.iknpFullAttackRecover`: `κ + 1`-transfer diagonal probing and
  simultaneous two-message extraction.
* `Cslib.Crypto.Protocols.MPC.iknpFullAttackRealGame`,
  `Cslib.Crypto.Protocols.MPC.iknpFullAttackIdealGame`: real and ideal games for simultaneous
  extraction of uniform `(m₀, m₁)` on transfer `κ` from `κ` known probe transfers.

## Main results

* `Cslib.Crypto.Protocols.MPC.iknpMasked_selectiveFailure_ne`: for any `j ≠ j₀`,
  `iknpSelectiveFailureColumns` behaves identically to honest `iknpColumns`.
* `Cslib.Crypto.Protocols.MPC.iknpMasked_selectiveFailure_sub`: at row `j₀`, honest unmasking
  recovers `X j₀ (r j₀)` when `s i₀ = false` and incurs shift
  `H j₀ (BitString.flipOn {i₀} (T j₀)) - H j₀ (T j₀)` when `s i₀ = true`.
* `Cslib.Crypto.Protocols.MPC.iknpSelectiveFailureSBit_advantage`: at least `1 / 2` distinguishing
  advantage against every ideal-OT simulator for predicting `s i₀`.
* `Cslib.Crypto.Protocols.MPC.iknpFullAttackRecover_eq`: deterministic recovery of `(m₀, m₁)` in a
  single run.
* `Cslib.Crypto.Protocols.MPC.iknpFullAttack_malicious_receiver_advantage`: at least
  `1 - (Fintype.card L : ℝ)⁻¹` distinguishing advantage against every ideal-OT simulator for
  simultaneous recovery of `(m₀, m₁)`.

## References

* [Y. Ishai, J. Kilian, K. Nissim, E. Petrank, *Extending Oblivious Transfers
  Efficiently*][IshaiKilianNissimPetrank2003], Section 3.
-/

public section

namespace Cslib.Crypto.Protocols.MPC

open Probability

/-! ### Sender reply map and algebraic selective-failure identities -/

/-- The honest sender's second-round masked reply in a protocol along `iknpSchedule κ m L`, on
sender input `X` and base-OT choice vector `s`, when a malicious receiver submits arbitrary column
pairs `U : Fin κ → Bool → BitString m` to the base `batchOTSpec` oracle. -/
@[expose] def iknpSenderReplyOf {κ m : ℕ} {L : Type}
    (proto : Protocol 2 (batchOTSpec κ (BitString m)) (iknpSchedule κ m L)
      ((batchOTSpec m L).Query ()) (IKNPCoins κ m) ((batchOTSpec m L).Answer ()))
    (X : Fin m → Bool → L) (s : BitString κ) (U : Fin κ → Bool → BitString m) :
    Fin m → Bool → L :=
  match proto.steps with
  | .oracle _ (.message send _) =>
    send ((X, s), fun sl hsl =>
      Fin.cases (motive := fun sl =>
          iknpRoleReversal sl = 0 → (batchOTSpec κ (BitString m)).Answer () sl)
        (fun h => absurd h (by decide))
        (fun _ _ i => U i (s i))
        sl hsl)

/-- The sender reply of `iknpProtocol H` on arbitrary base-OT columns `U` is `iknpMasked` on
`fun i => U i (s i)`. -/
@[simp] theorem iknpSenderReplyOf_iknpProtocol {κ m : ℕ} {L : Type} [AddCommGroup L]
    (H : Fin m → BitString κ → L) (X : Fin m → Bool → L) (s : BitString κ)
    (U : Fin κ → Bool → BitString m) :
    iknpSenderReplyOf (iknpProtocol H) X s U = iknpMasked H X s (fun i => U i (s i)) :=
  rfl

/-- Malicious base-OT column pairs that match `iknpColumns r T` everywhere except flipping bit
`(i₀, j₀)` of the `true`-column at base coordinate `i₀`. -/
@[expose] def iknpSelectiveFailureColumns {κ m : ℕ} (r : Fin m → Bool)
    (T : Fin m → BitString κ) (i₀ : Fin κ) (j₀ : Fin m) :
    Fin κ → Bool → BitString m :=
  fun i b j =>
    if i = i₀ ∧ b = true ∧ j = j₀ then !(iknpColumns r T i b j) else iknpColumns r T i b j

private theorem bitString_flipOn_singleton_add {κ : ℕ} (i₀ : Fin κ) (v s : BitString κ) :
    BitString.flipOn {i₀} v + s = BitString.flipOn {i₀} (v + s) := by
  funext i
  by_cases hi : i = i₀
  · subst hi
    simp only [BitString.flipOn_singleton_self, Pi.add_apply]
    cases v i <;> cases s i <;> rfl
  · simp only [BitString.flipOn_singleton_of_ne hi, Pi.add_apply]

/-- On every row `j ≠ j₀`, `iknpSelectiveFailureColumns r T i₀ j₀` leaves the sender's received
row unchanged and therefore preserves `iknpMasked`. -/
theorem iknpMasked_selectiveFailure_ne {κ m : ℕ} {L : Type} [AddCommGroup L]
    (H : Fin m → BitString κ → L) (X : Fin m → Bool → L)
    (r : Fin m → Bool) (T : Fin m → BitString κ) (s : BitString κ)
    (i₀ : Fin κ) {j₀ j : Fin m} (hj : j ≠ j₀) (b : Bool) :
    iknpMasked H X s (fun i => iknpSelectiveFailureColumns r T i₀ j₀ i (s i)) j b =
      X j b + H j (if b = r j then T j else T j + s) := by
  have hrow :
      iknpRows (fun i => iknpSelectiveFailureColumns r T i₀ j₀ i (s i)) j =
        iknpRows (fun i => iknpColumns r T i (s i)) j := by
    funext i
    simp [iknpRows, iknpSelectiveFailureColumns, hj]
  dsimp only [iknpMasked]
  rw [hrow, iknp_mask_input]

/-- On the probed row `j₀`, `iknpSelectiveFailureColumns r T i₀ j₀` shifts the hash input by
flipping bit `i₀` if and only if `s i₀ = true`. -/
theorem iknpMasked_selectiveFailure_at {κ m : ℕ} {L : Type} [AddCommGroup L]
    (H : Fin m → BitString κ → L) (X : Fin m → Bool → L)
    (r : Fin m → Bool) (T : Fin m → BitString κ) (s : BitString κ)
    (i₀ : Fin κ) (j₀ : Fin m) (b : Bool) :
    iknpMasked H X s (fun i => iknpSelectiveFailureColumns r T i₀ j₀ i (s i)) j₀ b =
      X j₀ b + H j₀ (if s i₀ then
        BitString.flipOn {i₀} (if b = r j₀ then T j₀ else T j₀ + s)
      else
        if b = r j₀ then T j₀ else T j₀ + s) := by
  have hrow :
      iknpRows (fun i => iknpSelectiveFailureColumns r T i₀ j₀ i (s i)) j₀ =
        if s i₀ then BitString.flipOn {i₀} (iknpRows (fun i => iknpColumns r T i (s i)) j₀)
        else iknpRows (fun i => iknpColumns r T i (s i)) j₀ := by
    funext i
    by_cases hi : i = i₀
    · subst hi
      cases hs : s i <;>
        simp [iknpRows, iknpSelectiveFailureColumns, BitString.flipOn_singleton_self, hs]
    · cases hs : s i₀ <;>
        simp [iknpRows, iknpSelectiveFailureColumns, hi, BitString.flipOn_singleton_of_ne hi]
  dsimp only [iknpMasked]
  rw [hrow]
  cases hs : s i₀
  · simp [iknp_mask_input]
  · simp only [↓reduceIte]
    cases b
    · rw [← iknp_mask_input r T s j₀ false]
      simp
    · rw [bitString_flipOn_singleton_add, ← iknp_mask_input r T s j₀ true]
      simp

/-- **Algebraic selective-failure identity**: honestly unmasking `Y j₀ (r j₀)` recovers
`X j₀ (r j₀)` when `s i₀ = false`, and produces an additive error
`H j₀ (BitString.flipOn {i₀} (T j₀)) - H j₀ (T j₀)` when `s i₀ = true`. -/
theorem iknpMasked_selectiveFailure_sub {κ m : ℕ} {L : Type} [AddCommGroup L]
    (H : Fin m → BitString κ → L) (X : Fin m → Bool → L)
    (r : Fin m → Bool) (T : Fin m → BitString κ) (s : BitString κ)
    (i₀ : Fin κ) (j₀ : Fin m) :
    iknpMasked H X s (fun i => iknpSelectiveFailureColumns r T i₀ j₀ i (s i)) j₀ (r j₀) -
        H j₀ (T j₀) =
      if s i₀ then
        X j₀ (r j₀) + (H j₀ (BitString.flipOn {i₀} (T j₀)) - H j₀ (T j₀))
      else
        X j₀ (r j₀) := by
  rw [iknpMasked_selectiveFailure_at]
  cases hs : s i₀
  · simp
  · simp only [↓reduceIte]
    abel

/-! ### Single-bit leakage of `s i₀` via selective failure -/

/-- Real game for recovering the sender's secret bit `s i₀`: the sender draws coins `s` via
`(iknpProtocol H).sampleCoins 0` on input `X` and replies to the selective-failure columns
`iknpSelectiveFailureColumns (fun _ => false) T i₀ j₀`. The malicious receiver checks whether
honest unmasking at `(j₀, false)` fails to recover `X j₀ false`. -/
@[expose] noncomputable def iknpSelectiveFailureSBitRealGame {κ m : ℕ} {L : Type}
    [AddCommGroup L] [DecidableEq L]
    (H : Fin m → BitString κ → L) (T : Fin m → BitString κ) (i₀ : Fin κ) (j₀ : Fin m)
    (X : Fin m → Bool → L) : ProbComp Bool := do
  let s ← (iknpProtocol H).sampleCoins 0
  let Y := iknpSenderReplyOf (iknpProtocol H) X s
    (iknpSelectiveFailureColumns (fun _ => false) T i₀ j₀)
  return decide (decide (Y j₀ false - H j₀ (T j₀) ≠ X j₀ false) = s i₀)

/-- Ideal game for predicting `s i₀` against `batchOTFunctionality m L`: the ideal functionality
never depends on `s`, so an ideal simulator `S` picks a choice vector `r'`, receives
`fun j => X j (r' j)`, and outputs a Boolean guess tested against an independent uniform `s i₀`. -/
@[expose] noncomputable def iknpSelectiveFailureSBitIdealGame (κ m : ℕ) (L : Type)
    (X : Fin m → Bool → L) (i₀ : Fin κ)
    (S : ProbComp ((Fin m → Bool) × ((Fin m → L) → ProbComp Bool))) : ProbComp Bool := do
  let s ← ProbComp.uniform (BitString κ)
  let sim ← S
  let guess ← sim.2 (fun j => X j (sim.1 j))
  return decide (guess = s i₀)

/-- Whenever `H j₀ (BitString.flipOn {i₀} (T j₀)) ≠ H j₀ (T j₀)`, the selective-failure attack
predicts `s i₀` with probability `1` in `iknpSelectiveFailureSBitRealGame`. -/
theorem succProbability_iknpSelectiveFailureSBitRealGame {κ m : ℕ} {L : Type}
    [AddCommGroup L] [DecidableEq L]
    (H : Fin m → BitString κ → L) (T : Fin m → BitString κ) (i₀ : Fin κ) (j₀ : Fin m)
    (X : Fin m → Bool → L)
    (hsep : H j₀ (BitString.flipOn {i₀} (T j₀)) ≠ H j₀ (T j₀)) :
    (Game.succProbability
      (ProbComp.eval (iknpSelectiveFailureSBitRealGame H T i₀ j₀ X)) : ℝ) = 1 := by
  have hcheck : ∀ s : BitString κ,
      decide (iknpSenderReplyOf (iknpProtocol H) X s
        (iknpSelectiveFailureColumns (fun _ => false) T i₀ j₀) j₀ false -
          H j₀ (T j₀) ≠ X j₀ false) = s i₀ := by
    intro s
    rw [iknpSenderReplyOf_iknpProtocol]
    have hsub := iknpMasked_selectiveFailure_sub H X (fun _ => false) T s i₀ j₀
    rw [hsub]
    cases hs : s i₀
    · simp
    · simp only [↓reduceIte, ne_eq, add_eq_left, sub_eq_zero, hsep, not_false_eq_true,
        decide_true]
  rw [Game.coe_succProbability]
  have hfun :
      (fun s : BitString κ =>
        PMF.pure (decide (decide (iknpSenderReplyOf (iknpProtocol H) X s
          (iknpSelectiveFailureColumns (fun _ => false) T i₀ j₀) j₀ false -
            H j₀ (T j₀) ≠ X j₀ false) = s i₀))) =
      fun _ : BitString κ => PMF.pure true := by
    funext s
    rw [hcheck s, decide_eq_true rfl]
  have hreal :
      ProbComp.eval (iknpSelectiveFailureSBitRealGame H T i₀ j₀ X) =
        (ProbComp.eval (ProbComp.uniform (BitString κ))).bind fun s =>
          PMF.pure (decide (decide (iknpSenderReplyOf (iknpProtocol H) X s
            (iknpSelectiveFailureColumns (fun _ => false) T i₀ j₀) j₀ false -
              H j₀ (T j₀) ≠ X j₀ false) = s i₀)) := by
    simp only [iknpSelectiveFailureSBitRealGame, ProbComp.eval_bind, ProbComp.eval_pure]
    rfl
  rw [hreal, hfun]
  simp

/-- Every ideal-OT simulator predicts `s i₀` with probability `1 / 2`. -/
theorem succProbability_iknpSelectiveFailureSBitIdealGame (κ m : ℕ) (L : Type)
    (X : Fin m → Bool → L) (i₀ : Fin κ)
    (S : ProbComp ((Fin m → Bool) × ((Fin m → L) → ProbComp Bool))) :
    (Game.succProbability
      (ProbComp.eval (iknpSelectiveFailureSBitIdealGame κ m L X i₀ S)) : ℝ) = 1 / 2 := by
  have hguess (b : Bool) :
      ((PMF.uniformOfFintype (BitString κ)).bind fun s =>
        PMF.pure (decide (b = s i₀))) true = (1 / 2 : ENNReal) := by
    let e : BitString κ ≃ BitString κ :=
      Equiv.ofBijective (BitString.flipOn {i₀}) (BitString.flipOn_involutive {i₀}).bijective
    have hsymm :
        ((PMF.uniformOfFintype (BitString κ)).bind fun s =>
          PMF.pure (decide (b = s i₀))) true =
        ((PMF.uniformOfFintype (BitString κ)).bind fun s =>
          PMF.pure (decide (b = s i₀))) false := by
      conv_lhs => rw [← PMF.uniformOfFintype_map_equiv e, PMF.bind_map]
      simp only [PMF.bind_apply, Function.comp_apply, e, Equiv.ofBijective_apply,
        BitString.flipOn_singleton_self, PMF.pure_apply]
      refine tsum_congr fun s => ?_
      cases b <;> cases s i₀ <;> simp
    have hsum :
        ((PMF.uniformOfFintype (BitString κ)).bind fun s =>
          PMF.pure (decide (b = s i₀))) true +
        ((PMF.uniformOfFintype (BitString κ)).bind fun s =>
          PMF.pure (decide (b = s i₀))) false = 1 := by
      have ht := ((PMF.uniformOfFintype (BitString κ)).bind fun s =>
        PMF.pure (decide (b = s i₀))).tsum_coe
      rw [tsum_bool, add_comm] at ht
      exact ht
    rw [← hsymm, ← two_mul] at hsum
    calc
      ((PMF.uniformOfFintype (BitString κ)).bind fun s =>
          PMF.pure (decide (b = s i₀))) true
        = (1 / 2 : ENNReal) * (2 * ((PMF.uniformOfFintype (BitString κ)).bind fun s =>
            PMF.pure (decide (b = s i₀))) true) := by
          rw [← mul_assoc, one_div, ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]
      _ = 1 / 2 := by rw [hsum, mul_one]
  have hinner (sim : (Fin m → Bool) × ((Fin m → L) → ProbComp Bool)) :
      ((ProbComp.eval (sim.2 fun j => X j (sim.1 j))).bind fun guess =>
        (PMF.uniformOfFintype (BitString κ)).bind fun s =>
          PMF.pure (decide (guess = s i₀))) true = (1 / 2 : ENNReal) := by
    rw [PMF.bind_apply]
    simp_rw [hguess, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  have hprob :
      ProbComp.eval (iknpSelectiveFailureSBitIdealGame κ m L X i₀ S) true =
        (1 / 2 : ENNReal) := by
    simp only [iknpSelectiveFailureSBitIdealGame, ProbComp.eval_bind, ProbComp.eval_pure,
      ProbComp.eval_uniform]
    rw [PMF.bind_comm]
    calc
      ((ProbComp.eval S).bind fun sim =>
          (PMF.uniformOfFintype (BitString κ)).bind fun s =>
            (ProbComp.eval (sim.2 fun j => X j (sim.1 j))).bind fun guess =>
              PMF.pure (decide (guess = s i₀))) true
        = ((ProbComp.eval S).bind fun sim =>
            (ProbComp.eval (sim.2 fun j => X j (sim.1 j))).bind fun guess =>
              (PMF.uniformOfFintype (BitString κ)).bind fun s =>
                PMF.pure (decide (guess = s i₀))) true := by
          refine congrArg (fun f => (PMF.bind (ProbComp.eval S) f) true) (funext fun sim => ?_)
          exact PMF.bind_comm _ _ _
      _ = 1 / 2 := by
          rw [PMF.bind_apply]
          simp_rw [hinner, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  rw [Game.coe_succProbability, hprob]
  norm_num

/-- **Selective-failure bit-leakage separation**: whenever
`H j₀ (BitString.flipOn {i₀} (T j₀)) ≠ H j₀ (T j₀)`, the distinguishing advantage between
`iknpSelectiveFailureSBitRealGame` and `iknpSelectiveFailureSBitIdealGame` is at least `1 / 2` for
every ideal-OT simulator `S`. -/
theorem iknpSelectiveFailureSBit_advantage {κ m : ℕ} {L : Type}
    [AddCommGroup L] [DecidableEq L]
    (H : Fin m → BitString κ → L) (T : Fin m → BitString κ) (i₀ : Fin κ) (j₀ : Fin m)
    (X : Fin m → Bool → L)
    (hsep : H j₀ (BitString.flipOn {i₀} (T j₀)) ≠ H j₀ (T j₀))
    (S : ProbComp ((Fin m → Bool) × ((Fin m → L) → ProbComp Bool))) :
    (1 / 2 : ℝ) ≤
      (Game.advantage
        (ProbComp.eval (iknpSelectiveFailureSBitRealGame H T i₀ j₀ X))
        (ProbComp.eval (iknpSelectiveFailureSBitIdealGame κ m L X i₀ S)) : ℝ) := by
  rw [Game.coe_advantage, succProbability_iknpSelectiveFailureSBitRealGame H T i₀ j₀ X hsep,
    succProbability_iknpSelectiveFailureSBitIdealGame]
  norm_num [le_abs_self]

/-! ### Full `s`-extraction and simultaneous recovery of both target messages -/

/-- Malicious base-OT column pairs for `m = κ + 1`: base OT `i` flips bit `i.castSucc` and target
bit `Fin.last κ` in its `true`-column relative to `T`, leaving all other entries equal to `T`. -/
@[expose] def iknpFullAttackColumns {κ : ℕ} (T : Fin (κ + 1) → BitString κ) :
    Fin κ → Bool → BitString (κ + 1) :=
  fun i b j =>
    if j = i.castSucc ∨ j = Fin.last κ then T j i + b else T j i

/-- Extract every bit `s k` from the selective failure on probe row `k.castSucc`, then decrypt both
messages `(m₀, m₁)` on row `Fin.last κ`. -/
@[expose] def iknpFullAttackRecover {κ : ℕ} {L : Type} [AddCommGroup L] [DecidableEq L]
    (H : Fin (κ + 1) → BitString κ → L) (T : Fin (κ + 1) → BitString κ)
    (probe : Fin κ → Bool → L) (Y : Fin (κ + 1) → Bool → L) : L × L :=
  let s' : BitString κ := fun k =>
    decide (Y k.castSucc false - H k.castSucc (T k.castSucc) ≠ probe k false)
  (Y (Fin.last κ) false - H (Fin.last κ) (T (Fin.last κ) + s'),
   Y (Fin.last κ) true - H (Fin.last κ) (T (Fin.last κ)))

/-- **Simultaneous recovery on `m = κ + 1` transfers**: when each probe row `k.castSucc` carries
known `probe k` and `H k.castSucc` separates `T k.castSucc` from its single-bit flip at `k`,
`iknpFullAttackRecover` deterministically recovers both target messages `(m₀, m₁)` on row
`Fin.last κ`. -/
theorem iknpFullAttackRecover_eq {κ : ℕ} {L : Type} [AddCommGroup L] [DecidableEq L]
    (H : Fin (κ + 1) → BitString κ → L) (T : Fin (κ + 1) → BitString κ)
    (probe : Fin κ → Bool → L) (m₀ m₁ : L) (s : BitString κ)
    (hsep : ∀ k : Fin κ,
      H k.castSucc (BitString.flipOn {k} (T k.castSucc)) ≠ H k.castSucc (T k.castSucc)) :
    let X : Fin (κ + 1) → Bool → L := Fin.snoc probe (fun b => if b then m₁ else m₀)
    iknpFullAttackRecover H T probe (iknpMasked H X s (fun i => iknpFullAttackColumns T i (s i))) =
      (m₀, m₁) := by
  intro X
  have hprobeRow (k : Fin κ) :
      iknpRows (fun i => iknpFullAttackColumns T i (s i)) k.castSucc =
        if s k then BitString.flipOn {k} (T k.castSucc) else T k.castSucc := by
    funext i
    have hne : k.castSucc ≠ Fin.last κ := Fin.castSucc_ne_last k
    have hfalse : ∀ a : Bool, a + false = a := by decide
    have htrue : ∀ a : Bool, a + true = !a := by decide
    by_cases hik : i = k
    · subst i
      simp only [iknpRows, iknpFullAttackColumns, hne, or_false, ↓reduceIte]
      cases hs : s k
      · simp [hfalse]
      · simp [htrue, BitString.flipOn_singleton_self]
    · have hcast : k.castSucc ≠ i.castSucc := Fin.castSucc_injective κ |>.ne (Ne.symm hik)
      simp only [iknpRows, iknpFullAttackColumns, hne, hcast, or_self, ↓reduceIte]
      cases s k <;> simp [BitString.flipOn_singleton_of_ne hik]
  have hs' :
      (fun k : Fin κ =>
        decide (iknpMasked H X s (fun i => iknpFullAttackColumns T i (s i)) k.castSucc false -
          H k.castSucc (T k.castSucc) ≠ probe k false)) = s := by
    funext k
    have hxk : X k.castSucc false = probe k false := by
      simp [X]
    dsimp only [iknpMasked]
    simp_rw [hprobeRow k, hxk]
    cases hs : s k
    · simp
    · simp only [Bool.false_eq_true, ↓reduceIte, ne_eq, add_sub_assoc, add_eq_left, sub_eq_zero,
        hsep k, not_false_eq_true, decide_true]
  have hlastRow :
      iknpRows (fun i => iknpFullAttackColumns T i (s i)) (Fin.last κ) = T (Fin.last κ) + s := by
    funext i
    simp [iknpRows, iknpFullAttackColumns]
  have hcancel : (T (Fin.last κ) + s) + s = T (Fin.last κ) := by
    have hbool : ∀ a b : Bool, (a + b) + b = a := by decide
    funext i
    exact hbool (T (Fin.last κ) i) (s i)
  dsimp only [iknpFullAttackRecover]
  rw [hs']
  dsimp only [iknpMasked]
  rw [hlastRow]
  have hx0 : X (Fin.last κ) false = m₀ := by simp [X]
  have hx1 : X (Fin.last κ) true = m₁ := by simp [X]
  simp only [Bool.false_eq_true, ↓reduceIte, hx0, hx1, hcancel, add_sub_cancel_right]

/-- Real game for simultaneous recovery in unchecked IKNP over `m = κ + 1` transfers: the first `κ`
transfers hold known `probe` values, the last transfer holds independent uniform `(m₀, m₁) ← L × L`,
and the malicious receiver outputs `iknpFullAttackRecover`. -/
@[expose] noncomputable def iknpFullAttackRealGame {κ : ℕ} {L : Type}
    [AddCommGroup L] [DecidableEq L] [Fintype L] [Nonempty L]
    (H : Fin (κ + 1) → BitString κ → L) (T : Fin (κ + 1) → BitString κ)
    (probe : Fin κ → Bool → L) : ProbComp Bool := do
  let m₀ ← ProbComp.uniform L
  let m₁ ← ProbComp.uniform L
  let X : Fin (κ + 1) → Bool → L := Fin.snoc probe (fun b => if b then m₁ else m₀)
  let s ← (iknpProtocol H).sampleCoins 0
  let Y := iknpSenderReplyOf (iknpProtocol H) X s (iknpFullAttackColumns T)
  return decide (iknpFullAttackRecover H T probe Y = (m₀, m₁))

/-- Ideal game for simultaneous recovery against `batchOTFunctionality (κ + 1) L`: the simulator `S`
chooses one query vector `r' : Fin (κ + 1) → Bool`, learns only `fun j => X j (r' j)`, and wins if
its guess equals `(m₀, m₁)`. -/
@[expose] noncomputable def iknpFullAttackIdealGame {κ : ℕ} {L : Type}
    [DecidableEq L] [Fintype L] [Nonempty L] (probe : Fin κ → Bool → L)
    (S : ProbComp ((Fin (κ + 1) → Bool) × ((Fin (κ + 1) → L) → ProbComp (L × L)))) :
    ProbComp Bool := do
  let sim ← S
  let m₀ ← ProbComp.uniform L
  let m₁ ← ProbComp.uniform L
  let X : Fin (κ + 1) → Bool → L := Fin.snoc probe (fun b => if b then m₁ else m₀)
  let pair ← sim.2 (fun j => X j (sim.1 j))
  return decide (pair = (m₀, m₁))

/-- Under `hsep`, the malicious receiver wins `iknpFullAttackRealGame` with probability `1`. -/
theorem succProbability_iknpFullAttackRealGame {κ : ℕ} {L : Type}
    [AddCommGroup L] [DecidableEq L] [Fintype L] [Nonempty L]
    (H : Fin (κ + 1) → BitString κ → L) (T : Fin (κ + 1) → BitString κ)
    (probe : Fin κ → Bool → L)
    (hsep : ∀ k : Fin κ,
      H k.castSucc (BitString.flipOn {k} (T k.castSucc)) ≠ H k.castSucc (T k.castSucc)) :
    (Game.succProbability (ProbComp.eval (iknpFullAttackRealGame H T probe)) : ℝ) = 1 := by
  have hrec (m₀ m₁ : L) (s : BitString κ) :
      iknpFullAttackRecover H T probe
        (iknpSenderReplyOf (iknpProtocol H)
          (Fin.snoc probe (fun b => if b then m₁ else m₀)) s
          (iknpFullAttackColumns T)) = (m₀, m₁) := by
    rw [iknpSenderReplyOf_iknpProtocol]
    exact iknpFullAttackRecover_eq H T probe m₀ m₁ s hsep
  have hreal :
      ProbComp.eval (iknpFullAttackRealGame H T probe) =
        (ProbComp.eval (ProbComp.uniform L)).bind fun m₀ =>
          (ProbComp.eval (ProbComp.uniform L)).bind fun m₁ =>
            (ProbComp.eval (ProbComp.uniform (BitString κ))).bind fun s =>
              PMF.pure (decide (iknpFullAttackRecover H T probe
                (iknpSenderReplyOf (iknpProtocol H)
                  (Fin.snoc probe (fun b => if b then m₁ else m₀)) s
                  (iknpFullAttackColumns T)) = (m₀, m₁))) := by
    simp only [iknpFullAttackRealGame, ProbComp.eval_bind, ProbComp.eval_pure]
    rfl
  rw [Game.coe_succProbability, hreal]
  simp_rw [hrec, decide_true]
  simp

/-- In `iknpFullAttackIdealGame`, every simulator `S` outputs `(m₀, m₁)` with probability at most
`(Fintype.card L : ℝ)⁻¹`. -/
theorem succProbability_iknpFullAttackIdealGame_le {κ : ℕ} {L : Type}
    [DecidableEq L] [Fintype L] [Nonempty L] (probe : Fin κ → Bool → L)
    (S : ProbComp ((Fin (κ + 1) → Bool) × ((Fin (κ + 1) → L) → ProbComp (L × L)))) :
    (Game.succProbability (ProbComp.eval (iknpFullAttackIdealGame probe S)) : ℝ) ≤
      (Fintype.card L : ℝ)⁻¹ := by
  have hunit : ∀ x : L,
      ((PMF.uniformOfFintype L).bind (fun y => PMF.pure (decide (x = y)))) true =
        (Fintype.card L : ENNReal)⁻¹ := fun x => by
    simp only [PMF.bind_apply, PMF.uniformOfFintype_apply, PMF.pure_apply]
    rw [tsum_eq_single x]
    · simp
    · intro y hy
      simp [decide_eq_false hy.symm]
  have hguess : ∀ (x : L) (E : L → Bool), (∀ y, E y = true → x = y) →
      ((PMF.uniformOfFintype L).bind fun y => PMF.pure (E y)) true ≤
        (Fintype.card L : ENNReal)⁻¹ := fun x E hE => by
    rw [← hunit x]
    exact PMF.map_true_mono _ fun y _ h => decide_eq_true (hE y h)
  have hview (r' : Fin (κ + 1) → Bool) (m₀ m₁ : L) :
      (fun j =>
        (Fin.snoc (α := fun _ => Bool → L) probe
          (fun b => if b then m₁ else m₀) j) (r' j)) =
        Fin.snoc (fun i : Fin κ => probe i (r' i.castSucc))
          (if r' (Fin.last κ) then m₁ else m₀) := by
    funext j
    exact Fin.lastCases (by simp) (fun i => by simp) j
  have h_ennreal :
      ProbComp.eval (iknpFullAttackIdealGame probe S) true ≤ (Fintype.card L : ENNReal)⁻¹ := by
    simp only [iknpFullAttackIdealGame, ProbComp.eval_bind, ProbComp.eval_pure,
      ProbComp.eval_uniform]
    refine PMF.bind_apply_le_on_support _ fun sim _ => ?_
    obtain ⟨r', guess⟩ := sim
    cases hr : r' (Fin.last κ)
    · simp_rw [hview r', hr]
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine PMF.bind_apply_le_on_support _ fun m₀ _ => ?_
      rw [PMF.bind_comm]
      refine PMF.bind_apply_le_on_support _ fun pair _ => ?_
      refine hguess pair.2 _ fun y h => ?_
      exact congrArg Prod.snd (of_decide_eq_true h)
    · simp_rw [hview r', hr]
      simp only [↓reduceIte]
      rw [PMF.bind_comm]
      refine PMF.bind_apply_le_on_support _ fun m₁ _ => ?_
      rw [PMF.bind_comm]
      refine PMF.bind_apply_le_on_support _ fun pair _ => ?_
      refine hguess pair.1 _ fun y h => ?_
      exact congrArg Prod.fst (of_decide_eq_true h)
  rw [Game.coe_succProbability, ← ENNReal.toReal_natCast, ← ENNReal.toReal_inv]
  exact ENNReal.toReal_mono (by simp) h_ennreal

/-- **Malicious-receiver simultaneous-recovery separation on unchecked IKNP**: for every ideal-OT
simulator `S`, the distinguishing advantage between `iknpFullAttackRealGame` and
`iknpFullAttackIdealGame probe S` is at least `1 - (Fintype.card L : ℝ)⁻¹`. -/
theorem iknpFullAttack_malicious_receiver_advantage {κ : ℕ} {L : Type}
    [AddCommGroup L] [DecidableEq L] [Fintype L] [Nonempty L]
    (H : Fin (κ + 1) → BitString κ → L) (T : Fin (κ + 1) → BitString κ)
    (probe : Fin κ → Bool → L)
    (hsep : ∀ k : Fin κ,
      H k.castSucc (BitString.flipOn {k} (T k.castSucc)) ≠ H k.castSucc (T k.castSucc))
    (S : ProbComp ((Fin (κ + 1) → Bool) × ((Fin (κ + 1) → L) → ProbComp (L × L)))) :
    1 - (Fintype.card L : ℝ)⁻¹ ≤
      (Game.advantage
        (ProbComp.eval (iknpFullAttackRealGame H T probe))
        (ProbComp.eval (iknpFullAttackIdealGame probe S)) : ℝ) := by
  rw [Game.coe_advantage, succProbability_iknpFullAttackRealGame H T probe hsep]
  exact (sub_le_sub_left (succProbability_iknpFullAttackIdealGame_le probe S) 1).trans
    (le_abs_self _)

end Cslib.Crypto.Protocols.MPC
