/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.RP
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! Error reduction for `BPP` and `RP` and `RP ⊆ BPP`, with concrete repeated deciders whose error
is genuinely reduced. -/

namespace ComplexityTests.ResourceClasses3

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM

/-! ### Repeated deciders on concrete random strings -/

/-- Accept when the random string is the single bit `true`. -/
def acceptsTrue (x : List Bool × List Bool) : Bool := x.2 == [true]

/-- Two rows of one bit, `[false]` and `[true]`: some row is accepted. -/
example : repeatAny encBits 2 1 acceptsTrue ([], [false, true]) = true := by
  simp only [repeatAny, Polynomial.eval_ofNat, Polynomial.eval_one]
  decide

/-- Two rows of one bit, both `[false]`: no row is accepted. -/
example : repeatAny encBits 2 1 acceptsTrue ([], [false, false]) = false := by
  simp only [repeatAny, Polynomial.eval_ofNat, Polynomial.eval_one]
  decide

/-- A short random string is padded with `false`. -/
example : repeatAny encBits 2 1 acceptsTrue ([], [false]) = false := by
  simp only [repeatAny, Polynomial.eval_ofNat, Polynomial.eval_one]
  decide

/-- Two votes of one bit each, one accepting: no strict majority. -/
example : repeatMajority encBits 1 1 acceptsTrue ([], [true, false]) = false := by
  simp only [repeatMajority, Polynomial.eval_one]
  decide

/-- Two votes of one bit each, both accepting: a strict majority. -/
example : repeatMajority encBits 1 1 acceptsTrue ([], [true, true]) = true := by
  simp only [repeatMajority, Polynomial.eval_one]
  decide

/-! ### Non-vacuity: the error is genuinely reduced -/

/-- Accepting on the first random bit decides every problem containing all instances with
one-sided error: half of the random strings are accepted. -/
theorem decidesWithOneSidedError_head :
    DecidesWithOneSidedError encBits 1 (fun x => x.2.headD false) Set.univ := fun a => by
  refine ⟨fun _ => ?_, fun h => absurd (Set.mem_univ a) h⟩
  have key (n : ℕ) (hn : n = 1) : 2 ^ n ≤ 2 * (Finset.univ.filter fun r : Fin n → Bool =>
      (List.ofFn r).headD false = true).card := by
    subst hn
    decide
  exact key _ Polynomial.eval_one

/-- Repeating the first-bit decider on `2` blocks reduces one-sided error to at most `1 / 4`,
which in turn satisfies one-sided error. -/
example :
    DecidesWithOneSidedError encBits (2 * 1)
      (repeatAny encBits 2 1 fun x => x.2.headD false) Set.univ :=
  (decidesWithOneSidedError_head.repeatAny 2).solvesWithOneSidedError fun _ => by simp

/-- Accepting when one of the first two random bits is `true` decides every problem containing
all instances with bounded error: three quarters of the random strings are accepted. -/
theorem decidesWithBoundedError_or :
    DecidesWithBoundedError encBits 2 (fun x => x.2.headD false || x.2.getD 1 false)
      Set.univ := fun a => by
  refine ⟨fun _ => ?_, fun h => absurd (Set.mem_univ a) h⟩
  have key (n : ℕ) (hn : n = 2) : 2 * 2 ^ n ≤ 3 * (Finset.univ.filter fun r : Fin n → Bool =>
      ((List.ofFn r).headD false || (List.ofFn r).getD 1 false) = true).card := by
    subst hn
    decide
  exact key _ (Polynomial.eval_ofNat 2 _)

/-- Majority votes of `24` runs reduce error to at most `1 / 4`, which in turn satisfies bounded
error. -/
example :
    DecidesWithBoundedError encBits (12 * 2 * 2)
      (repeatMajority encBits (6 * 2) 2 fun x => x.2.headD false || x.2.getD 1 false)
      Set.univ :=
  (decidesWithBoundedError_or.repeatMajority 2).solvesWithBoundedError fun _ => by simp

/-! ### Class-level error reduction -/

private theorem univ_mem_RP : (Set.univ : Set (List Bool)) ∈ RP encBits :=
  ⟨1, fun x => x.2.headD false, by fun_prop, decidesWithOneSidedError_head⟩

private theorem empty_mem_coRP : (∅ : Set (List Bool)) ∈ coRP encBits := by
  rw [mem_coRP, Set.compl_empty]
  exact univ_mem_RP

example : (Set.univ : Set (List Bool)) ∈ BPP encBits ∧ (∅ : Set (List Bool)) ∈ BPP encBits := by
  have hsub : RP encBits ∪ coRP encBits ⊆ BPP encBits :=
    Set.union_subset RP_subset_BPP coRP_subset_BPP
  exact ⟨hsub (Or.inl univ_mem_RP), hsub (Or.inr empty_mem_coRP)⟩

/-- Problems in `BPP` are decided with error below `2 ^ (-(n + 1))` on instances of length `n`, as
needed for Adleman's theorem. -/
example :
    ∃ (p : Polynomial ℕ) (V : List Bool × List Bool → Bool),
      ComputableInPolyTime V (encPair encBits encBits) encBool ∧
        DecidesWithErrorExponent encBits (Polynomial.X + 1) p V Set.univ :=
  mem_BPP_iff_forall_decidesWithErrorExponent.1 (RP_subset_BPP univ_mem_RP) (Polynomial.X + 1)

/-- Problems in `RP` are decided with one-sided error below `2 ^ (-(n + 1))`. -/
example :
    ∃ (p : Polynomial ℕ) (V : List Bool × List Bool → Bool),
      ComputableInPolyTime V (encPair encBits encBits) encBool ∧
        DecidesWithOneSidedErrorExponent encBits (Polynomial.X + 1) p V Set.univ :=
  mem_RP_iff_forall_decidesWithOneSidedErrorExponent.1 univ_mem_RP (Polynomial.X + 1)

end ComplexityTests.ResourceClasses3
