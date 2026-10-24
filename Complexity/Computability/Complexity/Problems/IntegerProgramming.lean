/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SubsetSum
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Zero-one integer programming

`ZeroOneIP` is the feasibility problem of zero-one integer programming in equality form: a system
of linear equations `∑ j, a j * x j = t` with natural coefficients and right-hand sides, encoded in
binary, has a solution with every `x j ∈ {0, 1}`. Each constraint is a pair `(a, t)`, with `a`
listing the coefficients of the variables `0, 1, …`; missing coefficients are zero.

Karp states zero-one integer programming with integer coefficients and inequalities
[Karp1972]; the equality form with natural coefficients is the special case used here, and it is
already `NP`-complete. A subset sum instance is a single equation, so `SubsetSum` reduces to
`ZeroOneIP`, and composing with Sipser's digit construction reduces `ThreeSAT` to `ZeroOneIP`.

## Main definitions

* `Cslib.Complexity.ZeroOneIP`.
* `Cslib.Complexity.ZeroOneIP.verifier`.
* `Cslib.Complexity.SubsetSum.toZeroOneIP`.

## Main results

* `Cslib.Complexity.sum_maskSelect`: the masked sum is the scalar product with the mask.
* `Cslib.Complexity.ZeroOneIP.mem_NP`: `ZeroOneIP ∈ NP (encList (encPair (encList encNat) encNat))`.
* `Cslib.Complexity.polyTimeReducible_SubsetSum_ZeroOneIP`,
  `Cslib.Complexity.polyTimeReducible_ThreeSAT_ZeroOneIP`, `Cslib.Complexity.ZeroOneIP_npHard`,
  `Cslib.Complexity.ZeroOneIP_npComplete`: `ZeroOneIP` is `NP`-complete.

## References

* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
-/

@[expose] public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM ComputableTidilyInPolyTime

/-- The systems of linear equations with natural coefficients that have a zero-one solution, the
equality form of Karp's zero-one integer programming [Karp1972]. A constraint `(a, t)` asks for
`∑ j < a.length, a[j] * x j = t`. -/
def ZeroOneIP : Set (List (List ℕ × ℕ)) :=
  {C | ∃ x : ℕ → Bool, ∀ c ∈ C, ∑ j ∈ range c.1.length, c.1.getD j 0 * (x j).toNat = c.2}

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
def verifier (x : List (List ℕ × ℕ) × List Bool) : Bool :=
  x.1.all fun c => decide ((maskSelect c.1 x.2).sum = c.2)

/-- `ZeroOneIP.verifier` verifies `ZeroOneIP` with certificates as long as the encoded system. -/
theorem isVerifier :
    IsVerifier (encList (encPair (encList encNat) encNat)) Polynomial.X verifier ZeroOneIP := by
  intro C
  simp only [ZeroOneIP, Set.mem_ofPred_eq, Polynomial.eval_X, verifier, List.all_eq_true,
    decide_eq_true_eq, sum_maskSelect]
  set n := (encList (encPair (encList encNat) encNat) C).length
  have hlen : ∀ c ∈ C, c.1.length ≤ n := fun c hc =>
    (length_le_length_encPair encNat encNat c).trans (length_le_encList_of_mem _ hc)
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
    ComputableInPolyTime verifier
      (encPair (encList (encPair (encList encNat) encNat)) encBits) encBool := by
  have hmask := (computableInPolyTime_maskSelect encNat).tidy
  refine .of_tidy ?_
  unfold verifier
  apply allWithInput (by fun_prop)
  fun_prop

/-- `ZeroOneIP` belongs to `NP`. -/
theorem mem_NP : ZeroOneIP ∈ NP (encList (encPair (encList encNat) encNat)) :=
  ⟨Polynomial.X, verifier, computableInPolyTime_verifier, isVerifier⟩

end ZeroOneIP

namespace SubsetSum

/-- A subset sum instance as a single equation. -/
def toZeroOneIP (x : List ℕ × ℕ) : List (List ℕ × ℕ) := [x]

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

/-- The reduction to `ZeroOneIP` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_toZeroOneIP :
    ComputableInPolyTime toZeroOneIP (encPair (encList encNat) encNat)
      (encList (encPair (encList encNat) encNat)) := by
  unfold toZeroOneIP
  fun_prop

end SubsetSum

/-- `SubsetSum` reduces to `ZeroOneIP` in polynomial time. -/
theorem polyTimeReducible_SubsetSum_ZeroOneIP :
    PolyTimeReducible (encPair (encList encNat) encNat)
      (encList (encPair (encList encNat) encNat)) SubsetSum ZeroOneIP :=
  ⟨SubsetSum.toZeroOneIP, SubsetSum.computableInPolyTime_toZeroOneIP,
    fun x => (SubsetSum.toZeroOneIP_mem_iff x).symm⟩

/-- `ThreeSAT` reduces to `ZeroOneIP` in polynomial time, through Sipser's digit construction. -/
theorem polyTimeReducible_ThreeSAT_ZeroOneIP :
    PolyTimeReducible encCNF (encList (encPair (encList encNat) encNat)) ThreeSAT ZeroOneIP :=
  polyTimeReducible_ThreeSAT_SubsetSum.trans polyTimeReducible_SubsetSum_ZeroOneIP

/-- `ZeroOneIP` is `NP`-hard. -/
theorem ZeroOneIP_npHard : NPHard (encList (encPair (encList encNat) encNat)) ZeroOneIP :=
  ThreeSAT_npHard.trans polyTimeReducible_ThreeSAT_ZeroOneIP

/-- **Zero-one integer programming is NP-complete**, in equality form with natural coefficients
in binary [Karp1972]. -/
theorem ZeroOneIP_npComplete : NPComplete (encList (encPair (encList encNat) encNat)) ZeroOneIP :=
  ⟨ZeroOneIP.mem_NP, ZeroOneIP_npHard⟩

end Cslib.Complexity
