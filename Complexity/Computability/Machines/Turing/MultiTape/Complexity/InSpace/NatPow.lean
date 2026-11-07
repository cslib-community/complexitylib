/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
public import Complexity.Foundations.Data.Nat.BinarySize

/-!
# Binary natural powers with a runtime exponent

The base and exponent are binary naturals. Repeated multiplication keeps the immutable base and
one accumulator; the iteration counter is binary. The space bound charges the possible output
length, proportional to the exponent times the binary length of the base, and the binary length
of the exponent. No unary charge for the base is introduced.

## Main results

* `Turing.MultiTapeTM.ComputableInSpace.natPow`: power with both arguments supplied at runtime.
* `Turing.MultiTapeTM.ComputableInSpace.budget_natPow_variable`: compute a power within a
  caller's budget that covers this output-length bound.
-/

public section

namespace Turing.MultiTapeTM.ComputableInSpace

private def powStep (q : ℕ × ℕ) : ℕ × ℕ := (q.1, q.2 * q.1)

private theorem iterate_powStep (a n : ℕ) : powStep^[n] (a, 1) = (a, a ^ n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]; rfl

private theorem powStep_inSpace :
    ComputableInSpace powStep (encPair encNat encNat) (encPair encNat encNat)
      fun q => (encPair encNat encNat q).length := by
  have hbase := fst encNat encNat
  have hacc := snd encNat encNat
  exact (budget_prod hbase (budget_natMul hacc hbase)).of_enc_eq fun _ => rfl

/-- A runtime exponent is evaluated by repeated multiplication within the possible output
length plus the binary counter length. The bound is valid also at base or exponent zero. -/
theorem natPow :
    ComputableInSpace (fun q : ℕ × ℕ => q.1 ^ q.2) (encPair encNat encNat) encNat
      fun q => (q.2 + 1) * (encNat q.1).length + (encNat q.2).length + 1 := by
  let B (q : ℕ × ℕ) := (q.2 + 1) * (encNat q.1).length + (encNat q.2).length + 1
  have hin : (fun q : ℕ × ℕ => (encPair encNat encNat q).length) ≼ B :=
    .of_le_linear 2 0 fun q => by
      dsimp only [B]
      rw [length_encPair]
      nlinarith
  have hbase := (fst encNat encNat).weaken hin
  have hn := (snd encNat encNat).weaken hin
  have hinit := budget_prod hbase (budget_const (encB := encNat) 1 hin)
  have hstates (q : ℕ × ℕ) (j : ℕ) (hj : j ≤ q.2) :
      (encPair encNat encNat (powStep^[j] (q.1, 1))).length ≤ 2 * B q := by
    rw [iterate_powStep, length_encPair]
    have hp := Nat.size_pow_le q.1 j
    have hmul := Nat.mul_le_mul_right q.1.size hj
    simp only [length_encNat_eq_size, B] at *
    nlinarith
  have hrun := budget_iterate hn hinit powStep_inSpace hstates
    (.of_le_linear 2 0 fun _ => le_rfl)
  exact (snd' hrun).of_enc_eq fun q => by rw [iterate_powStep]

/-- A power with a computed exponent stays within a budget covering both arguments and the
possible output length. Unlike `budget_natPow`, the exponent here is an input-dependent value. -/
theorem budget_natPow_variable {α : Type} {encIn : α ↪ List Bool} {Bs : α → ℕ}
    {a n : α → ℕ} (ha : ComputableInSpace a encIn encNat Bs)
    (hn : ComputableInSpace n encIn encNat Bs)
    (hbound : (fun x => (n x + 1) * (encNat (a x)).length + (encNat (n x)).length + 1) ≼ Bs) :
    ComputableInSpace (fun x => a x ^ n x) encIn encNat Bs :=
  budget_comp natPow (budget_prod ha hn) hbound

end Turing.MultiTapeTM.ComputableInSpace
