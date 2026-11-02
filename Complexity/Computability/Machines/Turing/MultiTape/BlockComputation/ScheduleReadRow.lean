/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleReadSpace
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Pi
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite
import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinarySizeFacts

/-!
# Native schedule direction rows

A schedule suffix is obtained by repeatedly dividing by the fixed row radix. A fixed column
then yields one direction, and the fixed family of input/work heads yields the complete row.
The schedule and interval are binary runtime inputs: neither the interval list nor a power with
runtime exponent is allocated. The supplied row agrees with `scheduleOfNat`.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.ScheduleRead

open MultiTapeTM MultiTapeTM.ComputableInSpace MultiTapeNTM.ChoiceTable

/-- Discard a binary-counted number of schedule rows using fixed-radix division. -/
@[expose] def suffix (k : ℕ) (a : ℕ × ℕ) : ℕ :=
  (fun n : ℕ => n / 3 ^ (k + 1))^[a.2] a.1

/-- The streamed suffix has the existing digit-position meaning. The power is a specification,
not an operation performed by the native reader. -/
theorem suffix_eq (k σ i : ℕ) :
    suffix k (σ, i) = σ / 3 ^ ((k + 1) * i) := by
  change (fun n : ℕ => n / 3 ^ (k + 1))^[i] σ = _
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    rw [ih, Nat.div_div_eq_div_mul, ← pow_add, Nat.mul_succ]

/-- Discarding rows cannot enlarge the stored schedule. -/
theorem suffix_le (k σ i : ℕ) : suffix k (σ, i) ≤ σ := by
  rw [suffix_eq]
  exact Nat.div_le_self _ _

/-- Native suffix extraction uses space linear in actual binary schedule and interval storage. -/
theorem suffix_inSpace (k : ℕ) :
    ComputableInSpace (suffix k) encState encNat (fun a => (encState a).length) := by
  have hid : ComputableInSpace (fun n : ℕ => n) encNat encNat
      (fun n => (encNat n).length) :=
    of_inO (ComputableInO.of_eq (f := id) fun _ => rfl)
  have hnext := budget_natDiv hid
    (budget_const (encB := encNat) (3 ^ (k + 1)) (.refl _))
  have hstates (a : ℕ × ℕ) (j : ℕ) (_hj : j ≤ a.2) :
      (encNat ((fun n : ℕ => n / 3 ^ (k + 1))^[j] a.1)).length ≤
        (encState a).length := by
    have hmono := ComputableTidilyInO.length_encNat_mono (suffix_le k a.1 j)
    change (encNat (suffix k (a.1, j))).length ≤ _
    simp only [encState, length_encPair]
    omega
  exact (budget_iterate (snd encNat encNat) (fst encNat encNat) hnext hstates
    (.refl _)).of_enc_eq fun _ => rfl

/-- Read one fixed head column of the actual runtime schedule row. -/
@[expose] def row (k c : ℕ) (a : ℕ × ℕ) : SignType :=
  signEquiv.symm ⟨suffix k a / 3 ^ c % 3, Nat.mod_lt _ (by decide)⟩

/-- A fixed-column direction reader is native and charges actual binary input storage. -/
theorem row_inSpace (k c : ℕ) :
    ComputableInSpace (row k c) encState (encFinite SignType)
      (fun a => (encState a).length) := by
  have hquot := budget_natDiv (suffix_inSpace k)
    (budget_const (encB := encNat) (3 ^ c) (.refl _))
  have hfin := budget_finMod (by decide : 0 < 3) hquot (.refl _)
  exact (budget_finite (encC := encFinite SignType) signEquiv.symm hfin).of_enc_eq
    fun _ => rfl

/-- The complete direction row, with the input head in column zero. -/
@[expose] def fullrow (k : ℕ) (a : ℕ × ℕ) : Option (Fin k) → SignType :=
  fun head => row k ((finSuccEquiv k).symm head) a

/-- The finite head family is fixed by the simulated machine, so its native space constant
is independent of the runtime schedule and interval. -/
theorem fullrow_inSpace (k : ℕ) :
    ComputableInSpace (fullrow k) encState (encPi (encFinite SignType))
      (fun a => (encState a).length) :=
  pi_linear fun head => row_inSpace k ((finSuccEquiv k).symm head)

/-- The native direction family is exactly the existing functional schedule's row. -/
theorem fullrow_eq_scheduleOfNat {k q : ℕ} (σ : ℕ) (i : Fin q) :
    fullrow k (σ, i) = scheduleOfNat k q σ i := by
  funext head
  change signEquiv.symm _ = signEquiv.symm _
  apply congrArg signEquiv.symm
  apply Fin.ext
  change suffix k (σ, i) / 3 ^ (((finSuccEquiv k).symm head : Fin (k + 1)) : ℕ) % 3 = _
  rw [suffix_eq, Nat.div_div_eq_div_mul, ← pow_add,
    Nat.add_comm ((k + 1) * i.val) (((finSuccEquiv k).symm head : Fin (k + 1)) : ℕ)]

end Turing.MultiTapePTM.BlockComputation.ScheduleRead
