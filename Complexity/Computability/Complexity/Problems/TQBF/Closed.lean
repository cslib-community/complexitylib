/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Space.TQBF.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives

/-!
# Closedness of a quantified Boolean formula in polynomial time

The free variables of a formula are computed by one scan of its tokens from right to left, with a
stack holding the free variables of the subformulas read so far
(`Cslib.Logic.PL.QBF.freeVarStep`): a variable pushes itself, a constant pushes nothing, a binary
connective joins the two lists on top of the stack, and a quantifier removes its variable from the
list on top. On the tokens of a formula the scan ends with the list of its free variables
(`Cslib.Logic.PL.QBF.foldl_freeVarStep_tokens`), so a formula is closed exactly when that list is
empty (`Cslib.Logic.PL.QBF.isClosed_tokens`), and closedness is decided in polynomial time
(`Cslib.Complexity.TQBF.computableInPolyTime_decide_closed`).

## Main definitions

* `Cslib.Logic.PL.QBF.freeVarList`: the free variables of a formula, with multiplicity.
* `Cslib.Logic.PL.QBF.freeVarStep`, `Cslib.Logic.PL.QBF.isClosed`: the scan of the tokens.

## Main results

* `Cslib.Logic.PL.QBF.mem_freeVarList`: the list has the free variables as elements.
* `Cslib.Logic.PL.QBF.isClosed_tokens`: the scan decides closedness.
* `Cslib.Complexity.TQBF.computableInPolyTime_decide_closed`: in polynomial time.
-/

@[expose] public section

namespace Cslib.Logic.PL.QBF

/-! ### Free variables by a scan of the tokens -/

/-- The free variables of a formula, with multiplicity. -/
def freeVarList : QBF ℕ → List ℕ
  | .var v => [v]
  | .top => []
  | .bot => []
  | .not φ => freeVarList φ
  | .and φ ψ => freeVarList φ ++ freeVarList ψ
  | .or φ ψ => freeVarList φ ++ freeVarList ψ
  | .ex v φ => (freeVarList φ).filter (· != v)
  | .all v φ => (freeVarList φ).filter (· != v)

/-- The elements of `freeVarList φ` are the free variables of `φ`. -/
theorem mem_freeVarList {φ : QBF ℕ} {x : ℕ} : x ∈ φ.freeVarList ↔ x ∈ φ.freeVars := by
  induction φ with
  | var v => simp [freeVarList]
  | top => simp [freeVarList]
  | bot => simp [freeVarList]
  | not φ ih => exact ih
  | and φ ψ ihφ ihψ => simp [freeVarList, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp [freeVarList, ihφ, ihψ]
  | ex v φ ih => simp [freeVarList, ih, and_comm]
  | all v φ ih => simp [freeVarList, ih, and_comm]

/-- A formula is closed exactly when its list of free variables is empty. -/
theorem closed_iff_freeVarList_eq_nil {φ : QBF ℕ} : φ.Closed ↔ φ.freeVarList = [] := by
  rw [Closed, Finset.eq_empty_iff_forall_notMem, List.eq_nil_iff_forall_not_mem]
  exact forall_congr' fun x => not_congr mem_freeVarList.symm

/-- One step of the scan of the tokens from right to left, for a token of kind `k` and variable
`v`, on the stack of the lists of free variables of the subformulas read so far. -/
def freeVarStepAt : Kind → ℕ → List (List ℕ) → List (List ℕ)
  | .var, v, stack => [v] :: stack
  | .top, _, stack => [] :: stack
  | .bot, _, stack => [] :: stack
  | .not, _, stack => stack
  | .and, _, stack => (stack.headD [] ++ stack.tail.headD []) :: stack.tail.tail
  | .or, _, stack => (stack.headD [] ++ stack.tail.headD []) :: stack.tail.tail
  | .ex, v, stack => (stack.headD []).filter (fun x => !decide (x = v)) :: stack.tail
  | .all, v, stack => (stack.headD []).filter (fun x => !decide (x = v)) :: stack.tail

/-- One step of the scan of the tokens from right to left. -/
def freeVarStep (stack : List (List ℕ)) (t : Kind × ℕ) : List (List ℕ) :=
  freeVarStepAt t.1 t.2 stack

/-- **The scan of the tokens** of a formula pushes the list of its free variables. -/
theorem foldl_freeVarStep_tokens (φ : QBF ℕ) (stack : List (List ℕ)) :
    φ.tokens.reverse.foldl freeVarStep stack = φ.freeVarList :: stack := by
  induction φ generalizing stack with
  | var v => rfl
  | top => rfl
  | bot => rfl
  | not φ ih =>
    simp only [tokens, List.reverse_cons, List.foldl_append, ih, List.foldl_cons,
      List.foldl_nil]
    rfl
  | and φ ψ ihφ ihψ =>
    simp only [tokens, List.reverse_cons, List.reverse_append, List.foldl_append, ihψ, ihφ,
      List.foldl_cons, List.foldl_nil]
    rfl
  | or φ ψ ihφ ihψ =>
    simp only [tokens, List.reverse_cons, List.reverse_append, List.foldl_append, ihψ, ihφ,
      List.foldl_cons, List.foldl_nil]
    rfl
  | ex v φ ih =>
    simp only [tokens, List.reverse_cons, List.foldl_append, ih, List.foldl_cons,
      List.foldl_nil]
    rfl
  | all v φ ih =>
    simp only [tokens, List.reverse_cons, List.foldl_append, ih, List.foldl_cons,
      List.foldl_nil]
    rfl

/-- Whether the scan of a list of tokens finds no free variable. -/
def isClosed (tokens : List (Kind × ℕ)) : Bool :=
  ((tokens.reverse.foldl freeVarStep []).headD []).isEmpty

/-- **The scan decides closedness.** -/
theorem isClosed_tokens (φ : QBF ℕ) : isClosed φ.tokens = decide φ.Closed := by
  rw [isClosed, foldl_freeVarStep_tokens, List.headD_cons]
  by_cases h : φ.Closed
  · rw [decide_eq_true h, List.isEmpty_iff.2 (closed_iff_freeVarList_eq_nil.1 h)]
  · rw [decide_eq_false h, Bool.eq_false_iff]
    intro h'
    exact h (closed_iff_freeVarList_eq_nil.2 (List.isEmpty_iff.1 h'))

end Cslib.Logic.PL.QBF

namespace Cslib.Complexity.TQBF

open _root_.Turing _root_.Turing.MultiTapeTM Cslib.Logic.PL ComputableInPolyTime

/-- A step of the scan for a fixed kind of token is polynomial-time. -/
private theorem freeVarStepAt_pt (k : QBF.Kind) :
    ComputableInPolyTime (fun p : List (List ℕ) × (QBF.Kind × ℕ) =>
      QBF.freeVarStepAt k p.2.2 p.1) (encPair (encList (encList encNat)) encToken)
      (encList (encList encNat)) := by
  cases k <;> simp only [QBF.freeVarStepAt] <;> fun_prop

/-- A step of the scan is polynomial-time. -/
private theorem freeVarStep_pt :
    ComputableInPolyTime (fun p : List (List ℕ) × (QBF.Kind × ℕ) =>
      QBF.freeVarStep p.1 p.2) (encPair (encList (encList encNat)) encToken)
      (encList (encList encNat)) :=
  finite_cases (tagEncoding := encKind) (tag := fun p : List (List ℕ) × (QBF.Kind × ℕ) => p.2.1)
    (branch := fun k p => QBF.freeVarStepAt k p.2.2 p.1) (by fun_prop) freeVarStepAt_pt

/-- Keeping some elements of a list does not lengthen its encoding. -/
private theorem length_encList_filter_le {α : Type} (enc : α ↪ List Bool) (l : List α)
    (f : α → Bool) : (encList enc (l.filter f)).length ≤ (encList enc l).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.filter_cons]
    split_ifs
    · simp only [encList_cons, List.length_append]
      omega
    · simp only [encList_cons, List.length_append]
      omega

/-- One step of the scan adds at most the encoding of its token, up to a constant. -/
private theorem length_freeVarStep_le (stack : List (List ℕ)) (t : QBF.Kind × ℕ) :
    (encList (encList encNat) (QBF.freeVarStep stack t)).length ≤
      (encList (encList encNat) stack).length + 4 * (encToken t).length + 3 := by
  obtain ⟨k, v⟩ := t
  have htok : (encNat v).length ≤ (encToken (k, v)).length := by
    simp only [encToken, encPair_apply, List.length_append, length_frame]
    omega
  simp only [QBF.freeVarStep]
  cases k <;> simp only [QBF.freeVarStepAt]
  · simp only [encList_cons, List.length_append, length_frame, encList_nil, List.length_nil]
    omega
  · simp only [encList_cons, List.length_append, length_frame, encList_nil, List.length_nil]
    omega
  · simp only [encList_cons, List.length_append, length_frame, encList_nil, List.length_nil]
    omega
  · omega
  · rcases stack with _ | ⟨a, _ | ⟨b, stack⟩⟩ <;>
      simp only [encList_cons, List.length_append, length_frame, encList_nil, List.length_nil,
        List.headD_nil, List.headD_cons, List.tail_nil, List.tail_cons, encList_append,
        List.append_nil] <;> omega
  · rcases stack with _ | ⟨a, _ | ⟨b, stack⟩⟩ <;>
      simp only [encList_cons, List.length_append, length_frame, encList_nil, List.length_nil,
        List.headD_nil, List.headD_cons, List.tail_nil, List.tail_cons, encList_append,
        List.append_nil] <;> omega
  · rcases stack with _ | ⟨a, stack⟩
    · simp
    · have := length_encList_filter_le encNat a (fun x => !decide (x = v))
      simp only [encList_cons, List.length_append, length_frame, List.headD_cons,
        List.tail_cons]
      omega
  · rcases stack with _ | ⟨a, stack⟩
    · simp
    · have := length_encList_filter_le encNat a (fun x => !decide (x = v))
      simp only [encList_cons, List.length_append, length_frame, List.headD_cons,
        List.tail_cons]
      omega

/-- **Closedness is decided in polynomial time.** -/
theorem computableInPolyTime_decide_closed :
    Turing.MultiTapeTM.ComputableInPolyTime (fun φ : QBF ℕ => decide φ.Closed) encQBF encBool := by
  simp only [← QBF.isClosed_tokens]
  unfold QBF.isClosed
  have hfold : ComputableInPolyTime (fun φ : QBF ℕ =>
      φ.tokens.reverse.foldl QBF.freeVarStep []) encQBF (encList (encList encNat)) := by
    refine foldlWith_of_bounded_growth (encA := encToken) (encL := encList encToken)
      (encP := encBool)
      (step := fun (_ : Bool) => QBF.freeVarStep)
      (par := fun _ => false) (const false) (by fun_prop) (const []) ?_
      (growth := fun φ => 4 * (encQBF φ).length + 3)
      (PolyBounded.of_forall_le 4 1 fun φ => by rw [pow_one]; omega) ?_
    · exact freeVarStep_pt.comp ((fst (encPair encBool _) encToken).snd'.prod (snd _ _))
    · intro φ stack t ht
      refine (length_freeVarStep_le stack t).trans (Nat.add_le_add_right
        (Nat.add_le_add_left (Nat.mul_le_mul_left 4 ?_) _) 3)
      rw [List.mem_reverse] at ht
      rw [encQBF_apply, length_encList]
      exact (Nat.le_succ_of_le (Nat.le_mul_of_pos_left _ two_pos)).trans
        (List.le_sum_of_mem (List.mem_map_of_mem ht))
  fun_prop

end Cslib.Complexity.TQBF
