/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.RP

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

/-- Repeating the first-bit decider on `q(n)` blocks errs with probability at most
`2 ^ (-q(n))`. -/
example (q : Polynomial ℕ) :
    DecidesWithOneSidedErrorExponent encBits q (q * 1)
      (repeatAny encBits q 1 fun x => x.2.headD false) Set.univ :=
  decidesWithOneSidedError_head.repeatAny q

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

/-- Majority votes of `12 q(n)` runs err with probability at most `2 ^ (-q(n))`. -/
example (q : Polynomial ℕ) :
    DecidesWithErrorExponent encBits q (12 * q * 2)
      (repeatMajority encBits (6 * q) 2 fun x => x.2.headD false || x.2.getD 1 false)
      Set.univ :=
  decidesWithBoundedError_or.repeatMajority q

/-- Error at most `1 / 4` is bounded error. -/
example {α : Type} {enc : α ↪ List Bool} {p : Polynomial ℕ} {V : α × List Bool → Bool}
    {A : Set α} (h : DecidesWithErrorExponent enc 2 p V A) : DecidesWithBoundedError enc p V A :=
  h.decidesWithBoundedError fun _ => by simp

/-! ### Class-level error reduction -/

example {α : Type} (enc : α ↪ List Bool) (A : Set α) :
    A ∈ BPP enc ↔ ∀ q : Polynomial ℕ, ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableInPolyTime V (encPair enc encBits) encBool ∧
        DecidesWithErrorExponent enc q p V A :=
  mem_BPP_iff_forall_decidesWithErrorExponent

example {α : Type} (enc : α ↪ List Bool) (A : Set α) :
    A ∈ RP enc ↔ ∀ q : Polynomial ℕ, ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableInPolyTime V (encPair enc encBits) encBool ∧
        DecidesWithOneSidedErrorExponent enc q p V A :=
  mem_RP_iff_forall_decidesWithOneSidedErrorExponent

/-- Problems in `BPP` are decided with error below `2 ^ (-n)` on instances of length `n`, as
needed for Adleman's theorem. -/
example {α : Type} (enc : α ↪ List Bool) (A : Set α) (hA : A ∈ BPP enc) :
    ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableInPolyTime V (encPair enc encBits) encBool ∧
        DecidesWithErrorExponent enc (.X + 1) p V A :=
  mem_BPP_iff_forall_decidesWithErrorExponent.1 hA _

example {α : Type} (enc : α ↪ List Bool) : RP enc ∪ coRP enc ⊆ BPP enc :=
  Set.union_subset RP_subset_BPP coRP_subset_BPP

/-! ### Axioms -/

/--
info: 'Cslib.Complexity.DecidesWithBoundedError.repeatMajority' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.DecidesWithBoundedError.repeatMajority

/--
info: 'Cslib.Complexity.computableInPolyTime_repeatMajority' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.computableInPolyTime_repeatMajority

/--
info: 'Cslib.Complexity.mem_BPP_iff_forall_decidesWithErrorExponent' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_BPP_iff_forall_decidesWithErrorExponent

/--
info: 'Cslib.Complexity.DecidesWithOneSidedError.repeatAny' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.DecidesWithOneSidedError.repeatAny

/--
info: 'Cslib.Complexity.computableInPolyTime_repeatAny' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.computableInPolyTime_repeatAny

/--
info: 'Cslib.Complexity.mem_RP_iff_forall_decidesWithOneSidedErrorExponent' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_RP_iff_forall_decidesWithOneSidedErrorExponent

/--
info: 'Cslib.Complexity.RP_subset_BPP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.RP_subset_BPP

/--
info: 'Cslib.Complexity.coRP_subset_BPP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.coRP_subset_BPP

end ComplexityTests.ResourceClasses3
