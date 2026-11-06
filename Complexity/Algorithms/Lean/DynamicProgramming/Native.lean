/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.DynamicProgramming.RoundedProduct
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Unary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Tactic.PolyTime
import Mathlib.Tactic

/-!
# Binary-machine implementation of minimum-product table operations

Table keys are unary because the rounded-key budget is polynomial in item count
and inverse tolerance; probabilities remain binary rationals. Witness elements
use an arbitrary supplied encoding. Native certificates charge copying, framing,
comparisons and exact rational normalization through the multitape calculus.

## Main results

* `computable_insert`: actual early-exit insertion on binary-rational tables.
* `computable_prune`: the original minimum-product pruning pass.
-/

public section
namespace Cslib.Algorithms.Lean.DynamicProgramming.MinProduct
open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableInPolyTime

variable {ι : Type} (enc : ι ↪ List Bool)

/-- A unary rounded key, binary rational product and explicit encoded witness. -/
@[expose] def encEntry : Entry ι ↪ List Bool :=
  (⟨fun e => (e.rounded,e.product,e.selected), fun a b h => by
    have hk := congrArg Prod.fst h
    have hp := congrArg (Prod.fst ∘ Prod.snd) h
    have hs := congrArg (Prod.snd ∘ Prod.snd) h
    cases a; cases b
    simp_all⟩ : Entry ι ↪ ℕ × ℚ × List ι).trans
      (encPair encUnary (encPair encRatBin (encList enc)))

private theorem entry_fields : ComputableInPolyTime
    (fun e : Entry ι => (e.rounded,e.product,e.selected)) (encEntry enc)
    (encPair encUnary (encPair encRatBin (encList enc))) := .of_eq fun _ => rfl

private theorem entry_rounded : ComputableInPolyTime (Entry.rounded (ι := ι))
    (encEntry enc) encUnary := (entry_fields enc).fst'

private theorem entry_product : ComputableInPolyTime (Entry.product (ι := ι))
    (encEntry enc) encRatBin := (entry_fields enc).snd'.fst'

private def insertionStep (x y : Entry ι) (state : List (Entry ι) × List (Entry ι)) :=
  let (original,inserted) := state
  (y :: original, if x.rounded = y.rounded then
    (if x.product ≤ y.product then x else y) :: original else y :: inserted)

private theorem insertion_fold (x : Entry ι) (xs : List (Entry ι)) :
    xs.reverse.foldl (fun state y => insertionStep x y state) ([],[x]) =
      (xs,insert Entry.rounded Entry.product x xs) := by
  rw [← List.foldr_eq_foldl_reverse]
  induction xs with
  | nil => rfl
  | cons y ys ih => simp only [List.foldr_cons, ih, insertionStep, insert]

private theorem insertion_step_computable : ComputableInPolyTime
    (fun p : (Entry ι × (List (Entry ι) × List (Entry ι))) × Entry ι =>
      let ((x,state),y) := p
      insertionStep x y state)
    (encPair (encPair (encEntry enc)
      (encPair (encList (encEntry enc)) (encList (encEntry enc)))) (encEntry enc))
    (encPair (encList (encEntry enc)) (encList (encEntry enc))) := by
  have hk := entry_rounded enc
  have hp := entry_product enc
  let input := encPair (encPair (encEntry enc)
    (encPair (encList (encEntry enc)) (encList (encEntry enc)))) (encEntry enc)
  have hx : ComputableInPolyTime (fun p : (Entry ι ×
      (List (Entry ι) × List (Entry ι))) × Entry ι => p.1.1) input (encEntry enc) := by
    exact (fst _ _).comp (fst _ _)
  have hy : ComputableInPolyTime (fun p : (Entry ι ×
      (List (Entry ι) × List (Entry ι))) × Entry ι => p.2) input (encEntry enc) := snd _ _
  have hle := ratBin_le.comp ((hp.comp hx).prod (hp.comp hy))
  have horig : ComputableInPolyTime (fun p : (Entry ι ×
      (List (Entry ι) × List (Entry ι))) × Entry ι => p.1.2.1) input
      (encList (encEntry enc)) := by exact (fst _ _).comp ((snd _ _).comp (fst _ _))
  have hins : ComputableInPolyTime (fun p : (Entry ι ×
      (List (Entry ι) × List (Entry ι))) × Entry ι => p.1.2.2) input
      (encList (encEntry enc)) := by exact (snd _ _).comp ((snd _ _).comp (fst _ _))
  unfold insertionStep
  fun_prop (config := { maxSteps := 256 })

/-- The exact insertion function, including its early-exit behavior, has a
uniform native binary-machine polynomial-time implementation. The table may
have arbitrarily large rational magnitudes and arbitrary encoded witnesses. -/
theorem computable_insert : ComputableInPolyTime
    (fun p : Entry ι × List (Entry ι) => insert Entry.rounded Entry.product p.1 p.2)
    (encPair (encEntry enc) (encList (encEntry enc))) (encList (encEntry enc)) := by
  let input := encPair (encEntry enc) (encList (encEntry enc))
  let stateEnc := encPair (encList (encEntry enc)) (encList (encEntry enc))
  have hf := ComputableTidilyInPolyTime.foldlWith_spec
    (encP := encEntry enc) (encA := encEntry enc) (encL := encList (encEntry enc))
    (encB := stateEnc) (encIn := input)
    (par := Prod.fst) (list := fun p : Entry ι × List (Entry ι) => p.2.reverse)
    (init := fun p => ([],[p.1]))
    (step := fun x state y => insertionStep x y state)
    (ComputableTidilyInPolyTime.fst _ _) (by fun_prop) (by fun_prop)
    (insertion_step_computable enc).tidy
    (fun p consumed state => state =
      (consumed.reverse,insert Entry.rounded Entry.product p.1 consumed.reverse))
    (by intro p; rfl) (by
      intro p consumed state y _ hs
      subst state
      simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
        insertionStep, insert])
    (size := fun p => 3 * ((input p).length + 1) * (2 * (input p).length + 1) + 1)
    (by exact (((PolyBounded.const 3).mul ((PolyBounded.self).add (.const 1))).mul
      (((PolyBounded.const 2).mul .self).add (.const 1))).add (.const 1)) ?_
  · have h := hf.1.snd'
    refine of_tidy (h.of_enc_eq ?_)
    intro p
    simp only [insertion_fold]
  · intro p consumed state hprefix hstate
    subst state
    let N := (input p).length
    have hx : (encEntry enc p.1).length ≤ N := length_le_encPair_left _ _ p
    have hxs : (encList (encEntry enc) p.2).length ≤ N := length_le_encPair_right _ _ p
    have hn : consumed.reverse.length ≤ N := by
      have hc := hprefix.length_le
      have hl := SizedListEncoding.length_le (encA := encEntry enc)
        (encL := encList (encEntry enc)) p.2
      simp only [List.length_reverse] at *
      omega
    have he (e : Entry ι) (he : e ∈ consumed.reverse) : (encEntry enc e).length ≤ N := by
      have hm : e ∈ p.2 := List.mem_reverse.mp
        (hprefix.subset (List.mem_reverse.mp he))
      exact (SizedListEncoding.length_elem_le (encA := encEntry enc)
        (encL := encList (encEntry enc)) p.2 e hm).trans hxs
    have h₀ := length_encList_le (encEntry enc) consumed.reverse he
    have h₁ := length_encList_le (encEntry enc)
      (insert Entry.rounded Entry.product p.1 consumed.reverse) (by
        intro e he'
        rcases mem_insert Entry.rounded Entry.product he' with rfl | he'
        · exact hx
        · exact he e he')
    have hl := insert_length_le Entry.rounded Entry.product p.1 consumed.reverse
    dsimp only [stateEnc]
    rw [length_encPair]
    change 2 * (encList (encEntry enc) consumed.reverse).length + 1 +
      (encList (encEntry enc) (insert Entry.rounded Entry.product p.1
        consumed.reverse)).length ≤ _
    change _ ≤ 3 * (N + 1) * (2 * N + 1) + 1
    nlinarith

private theorem prune_fold (xs : List (Entry ι)) :
    xs.reverse.foldl (fun table x => insert Entry.rounded Entry.product x table) [] =
      prune Entry.rounded Entry.product xs := by
  rw [← List.foldr_eq_foldl_reverse]
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.foldr_cons, ih, prune]

/-- The full minimum-product pruning pass has a uniform native binary-machine
polynomial-time implementation, including all insertion scans and exact rational
comparisons. The result is the original list-valued implementation. -/
theorem computable_prune : ComputableInPolyTime
    (prune (Entry.rounded (ι := ι)) Entry.product)
    (encList (encEntry enc)) (encList (encEntry enc)) := by
  have hstep : ComputableTidilyInPolyTime
      (fun p : List (Entry ι) × Entry ι => insert Entry.rounded Entry.product p.2 p.1)
      (encPair (encList (encEntry enc)) (encEntry enc)) (encList (encEntry enc)) :=
    ((computable_insert enc).comp ((snd _ _).prod (fst _ _))).tidy
  have hf := ComputableTidilyInPolyTime.foldl_spec
    (encA := encEntry enc) (encL := encList (encEntry enc))
    (encB := encList (encEntry enc)) (encIn := encList (encEntry enc))
    (list := List.reverse) (init := fun _ => [])
    (step := fun table x => insert Entry.rounded Entry.product x table)
    (by fun_prop) (ComputableTidilyInPolyTime.const []) hstep
    (fun _ consumed table => table = prune Entry.rounded Entry.product consumed.reverse)
    (by intro _; rfl) (by
      intro xs consumed table x _ ht
      subst table
      simp only [List.reverse_append, List.reverse_singleton, List.singleton_append, prune])
    (size := fun xs => (encList (encEntry enc) xs).length *
      (2 * (encList (encEntry enc) xs).length + 1))
    (PolyBounded.self.mul (((PolyBounded.const 2).mul .self).add (.const 1))) ?_
  · refine of_tidy (hf.1.of_enc_eq ?_)
    intro xs
    rw [prune_fold]
  · intro xs consumed table hprefix ht
    subst table
    have hsub : consumed.reverse.Sublist xs := by
      simpa only [List.reverse_reverse] using hprefix.sublist.reverse
    have hn := (prune_length_le_input Entry.rounded Entry.product consumed.reverse).trans
      hsub.length_le
    have hlen := SizedListEncoding.length_le (encA := encEntry enc)
      (encL := encList (encEntry enc)) xs
    have hb := length_encList_le (encEntry enc)
      (prune Entry.rounded Entry.product consumed.reverse) (by
        intro e he
        exact SizedListEncoding.length_elem_le (encA := encEntry enc)
          (encL := encList (encEntry enc)) xs e
          (hsub.subset (prune_sound Entry.rounded Entry.product he)))
    exact hb.trans (Nat.mul_le_mul_right _ (hn.trans hlen))

end Cslib.Algorithms.Lean.DynamicProgramming.MinProduct
