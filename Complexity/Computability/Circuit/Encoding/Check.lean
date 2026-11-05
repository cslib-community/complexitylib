/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Encoding
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Checking circuit gate codes

The existing `Program.IsCodeFrom` predicate has one Boolean checker for arbitrary signatures.
Its native certificate charges the operator's supplied encoding and a certified binary arity
function. Only actual argument lists are traversed; neither arity nor wire numbers drive an
allocation. The input count is unary and wire numbers are binary. Output-wire validity and
output-count agreement are separate checks.

## Main definitions

* `Cslib.Circuits.codeCheck`: arity and backward-reference validation.

## Main results

* `Cslib.Circuits.codeCheck_eq_true_iff`: exact agreement with `Program.IsCodeFrom`.
* `Cslib.Circuits.computableInPolyTime_codeCheck`: uniform validation given certified binary arity.
-/

@[expose] public section

namespace Cslib.Circuits

open Turing.MultiTapeTM

/-! ### Checking codes -/

/-- Whether a list of gates is the code of a program on `n` inputs (`Program.IsCodeFrom`), as a
Boolean test: every entry has the arity of its operation and reads only inputs and earlier
gates. -/
def codeCheck (σ : Signature) (n : ℕ) (gates : List (σ.Op × List ℕ)) : Bool :=
  gates.zipIdx.all fun g =>
    decide (g.1.2.length = σ.Arity g.1.1) && g.1.2.all (· < n + g.2)

private theorem all_zipIdx_eq_true_iff {σ : Signature} {n : ℕ} (k : ℕ)
    (gates : List (σ.Op × List ℕ)) :
    ((gates.zipIdx k).all fun g =>
      decide (g.1.2.length = σ.Arity g.1.1) && g.1.2.all (· < n + g.2)) = true ↔
      Program.IsCodeFrom σ n k gates := by
  induction gates generalizing k with
  | nil => simp [Program.IsCodeFrom]
  | cons g gates ih =>
    rw [List.zipIdx_cons, List.all_cons, Bool.and_eq_true, ih, Program.isCodeFrom_cons]
    simp

/-- `codeCheck σ n gates` returns `true` iff `gates` is a valid program code on `n` inputs. -/
theorem codeCheck_eq_true_iff {σ : Signature} {n : ℕ} {gates : List (σ.Op × List ℕ)} :
    codeCheck σ n gates = true ↔ Program.IsCodeFrom σ n 0 gates :=
  all_zipIdx_eq_true_iff 0 gates

open ComputableInPolyTime

/-- Gate validation is polynomial-time in the full encoded input, for unary input count and
binary wire indices, when computing an operation's binary arity is polynomial-time. No bound
on the numeric arity is required: comparison uses the actual argument-list length. -/
theorem computableInPolyTime_codeCheck {σ : Signature} {eOp : σ.Op ↪ List Bool}
    (harity : ComputableInPolyTime σ.Arity eOp encNat)
    {γ : Type} {encIn : γ ↪ List Bool} {n : γ → ℕ} {gates : γ → List (σ.Op × List ℕ)}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hgates : ComputableInPolyTime gates encIn (encList (Circuit.encGate eOp))) :
    ComputableInPolyTime (fun a => codeCheck σ (n a) (gates a)) encIn encBool := by
  have hbound : ComputableInPolyTime (fun p : (γ × ((σ.Op × List ℕ) × ℕ)) × ℕ =>
      decide (p.2 < n p.1.1 + p.1.2.2))
      (encPair (encPair encIn (encPair (Circuit.encGate eOp) encUnary)) encNat) encBool :=
    binary_lt' (snd _ _) (unary_to_binary.comp (by fun_prop))
  have hzip : ComputableInPolyTime (fun a => (gates a).zipIdx)
      encIn (encList (encPair (Circuit.encGate eOp) encUnary)) := by fun_prop
  unfold codeCheck
  exact allWithInput hzip (bool_and'
    (decide_eq' (unary_to_binary.comp (by fun_prop)) (harity.comp (by fun_prop)))
    (allWithInput (by fun_prop) hbound))

end Cslib.Circuits
