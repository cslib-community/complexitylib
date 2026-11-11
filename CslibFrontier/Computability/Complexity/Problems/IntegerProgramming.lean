/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SubsetSum
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Zero-one integer programming

`ZeroOneIP` is the feasibility problem of zero-one integer programming in equality form: a system
of linear equations `∑ j, a j * x j = t` with natural coefficients and right-hand sides, encoded in
binary, has a solution with every `x j ∈ {0, 1}`. Each equation `c : ZeroOneIP.Equation` stores the
coefficients `c.coeffs` of the variables `0, 1, …` (with missing coefficients zero) and the
right-hand side `c.rhs`.

Karp states zero-one integer programming with integer coefficients and inequalities
[Karp1972]; the equality form with natural coefficients is the special case used here, and it is
already `NP`-complete. A subset sum instance is a single equation, so `SubsetSum` reduces to
`ZeroOneIP`, and composing with Sipser's digit construction reduces `ThreeSAT` to `ZeroOneIP`.

## Main definitions

* `Cslib.Complexity.ZeroOneIP.Equation`, `Cslib.Complexity.ZeroOneIP.encEquation`: equality
  constraints and their binary encoding.
* `Cslib.Complexity.ZeroOneIP`, `Cslib.Complexity.encZeroOneIP`.
* `Cslib.Complexity.ZeroOneIP.verifier`.
* `Cslib.Complexity.SubsetSum.toZeroOneIP`.

## Main results

* `Cslib.Complexity.sum_maskSelect`: the masked sum is the scalar product with the mask.
* `Cslib.Complexity.ZeroOneIP.mem_NP`: `ZeroOneIP ∈ NP encZeroOneIP`.
* `Cslib.Complexity.polyTimeReducible_SubsetSum_ZeroOneIP`,
  `Cslib.Complexity.polyTimeReducible_ThreeSAT_ZeroOneIP`, `Cslib.Complexity.ZeroOneIP_npHard`,
  `Cslib.Complexity.ZeroOneIP_npComplete`: `ZeroOneIP` is `NP`-complete.

## References

* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
-/

public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM ComputableInPolyTime

namespace ZeroOneIP

/-- A linear equality constraint `∑ j, coeffs[j] * x j = rhs` in a zero-one integer program, with
missing coefficients treated as zero. -/
structure Equation where
  /-- The coefficients of variables `0, 1, …`. -/
  coeffs : List ℕ
  /-- The right-hand side target. -/
  rhs : ℕ
  deriving DecidableEq, Repr

/-- Binary encoding of a zero-one linear equation as `(coeffs, rhs)`. -/
enc_structure encEquation : Equation where
  coeffs : (encList encNat), rhs : encNat

end ZeroOneIP

/-- The systems of linear equations with natural coefficients that have a zero-one solution, the
equality form of Karp's zero-one integer programming [Karp1972]. An equation `c` asks for
`∑ j < c.coeffs.length, c.coeffs[j] * x j = c.rhs`. -/
@[expose] def ZeroOneIP : Set (List ZeroOneIP.Equation) :=
  {C | ∃ x : ℕ → Bool,
    ∀ c ∈ C, ∑ j ∈ range c.coeffs.length, c.coeffs.getD j 0 * (x j).toNat = c.rhs}

/-- Instances of `ZeroOneIP`: the equations `(coeffs, rhs)`, each framed, an equation being its
list `coeffs` of coefficients, framed, each coefficient framed, then its right-hand side `rhs`;
all numbers in binary. -/
abbrev encZeroOneIP : List ZeroOneIP.Equation ↪ List Bool := encList ZeroOneIP.encEquation

/-- The numbers selected by a mask sum to the scalar product with the mask. -/
theorem sum_maskSelect (a : List ℕ) (w : List Bool) :
    (maskSelect a w).sum = ∑ j ∈ range a.length, a.getD j 0 * (w.getD j false).toNat := by
  induction a generalizing w with
  | nil => simp
  | cons n a ih =>
    rw [maskSelect_cons, List.sum_append, ih, List.length_cons, sum_range_succ']
    cases w with
    | nil => simp
    | cons b w => cases b <;> simp [Nat.add_comm]

namespace ZeroOneIP

/-- The verifier for `ZeroOneIP`: the certificate, read as the values of the variables, satisfies
every equation. -/
@[expose] def verifier (x : List Equation × List Bool) : Bool :=
  x.1.all fun c => decide ((maskSelect c.coeffs x.2).sum = c.rhs)

/-- `ZeroOneIP.verifier` verifies `ZeroOneIP` with certificates as long as the encoded system. -/
theorem isVerifier :
    IsVerifier encZeroOneIP Polynomial.X verifier ZeroOneIP := by
  intro C
  simp only [ZeroOneIP, Set.mem_ofPred_eq, Polynomial.eval_X, verifier, List.all_eq_true,
    decide_eq_true_eq, sum_maskSelect]
  set n := (encZeroOneIP C).length
  have hlen : ∀ c ∈ C, c.coeffs.length ≤ n := by
    intro c hc
    have hc_len : c.coeffs.length ≤ (encEquation c).length := by
      rw [encEquation_apply]
      exact length_le_length_encPair encNat encNat (c.coeffs, c.rhs)
    exact hc_len.trans (length_le_encList_of_mem _ hc)
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨(List.range n).map x, by simp, fun c hc => ?_⟩
    rw [← hx c hc]
    refine sum_congr rfl fun j hj => ?_
    have hj' : j < n := (mem_range.1 hj).trans_le (hlen c hc)
    simp [List.getD_eq_getElem?_getD, hj']
  · rintro ⟨w, -, hw⟩
    exact ⟨fun j => w.getD j false, hw⟩

/-- The `ZeroOneIP` verifier is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair encZeroOneIP encBits) encBool := by
  have hmask := computableInPolyTime_maskSelect encNat
  unfold verifier
  apply allWithInput (by fun_prop)
  fun_prop

/-- `ZeroOneIP` belongs to `NP`. -/
theorem mem_NP : ZeroOneIP ∈ NP encZeroOneIP :=
  ⟨Polynomial.X, verifier, computableInPolyTime_verifier, isVerifier⟩

end ZeroOneIP

namespace SubsetSum

/-- A subset sum instance as a single equation. -/
@[expose] def toZeroOneIP (x : List ℕ × ℕ) : List ZeroOneIP.Equation := [⟨x.1, x.2⟩]

/-- **Correctness of the reduction to `ZeroOneIP`.** -/
theorem toZeroOneIP_mem_iff (x : List ℕ × ℕ) : toZeroOneIP x ∈ ZeroOneIP ↔ x ∈ SubsetSum := by
  simp only [ZeroOneIP, toZeroOneIP, Set.mem_ofPred_eq, List.mem_singleton, forall_eq,
    mem_SubsetSum]
  rw [exists_le_iff_exists_maskSelect le_rfl (fun s => s.sum = x.2)]
  simp only [Multiset.sum_coe, sum_maskSelect]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(List.range x.1.length).map y, by simp, ?_⟩
    rw [← hy]
    exact sum_congr rfl fun j hj => by simp [List.getD_eq_getElem?_getD, mem_range.1 hj]
  · rintro ⟨w, -, hw⟩
    exact ⟨fun j => w.getD j false, hw⟩

open scoped ZeroOneIP in
/-- The reduction to `ZeroOneIP` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_toZeroOneIP :
    ComputableInPolyTime toZeroOneIP encSubsetSum encZeroOneIP := by
  unfold toZeroOneIP
  fun_prop

end SubsetSum

/-- `SubsetSum` reduces to `ZeroOneIP` in polynomial time. -/
theorem polyTimeReducible_SubsetSum_ZeroOneIP :
    PolyTimeReducible encSubsetSum encZeroOneIP SubsetSum ZeroOneIP :=
  ⟨SubsetSum.toZeroOneIP, SubsetSum.computableInPolyTime_toZeroOneIP,
    fun x => (SubsetSum.toZeroOneIP_mem_iff x).symm⟩

/-- `ThreeSAT` reduces to `ZeroOneIP` in polynomial time, through Sipser's digit construction. -/
theorem polyTimeReducible_ThreeSAT_ZeroOneIP :
    PolyTimeReducible encCNF encZeroOneIP ThreeSAT ZeroOneIP :=
  polyTimeReducible_ThreeSAT_SubsetSum.trans polyTimeReducible_SubsetSum_ZeroOneIP

/-- `ZeroOneIP` is `NP`-hard. -/
theorem ZeroOneIP_npHard : NPHard encZeroOneIP ZeroOneIP :=
  ThreeSAT_npHard.trans polyTimeReducible_ThreeSAT_ZeroOneIP

/-- **Zero-one integer programming is NP-complete**, in equality form with natural coefficients
in binary [Karp1972]. -/
theorem ZeroOneIP_npComplete : NPComplete encZeroOneIP ZeroOneIP :=
  ⟨ZeroOneIP.mem_NP, ZeroOneIP_npHard⟩

end Cslib.Complexity
