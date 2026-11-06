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
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
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
* `computable_run`: uniform compilation of the complete recurrence with runtime field access.
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

/-- Read the three fields without converting their encodings. -/
theorem computable_entry_fields : ComputableInPolyTime
    (fun e : Entry ι => (e.rounded,e.product,e.selected)) (encEntry enc)
    (encPair encUnary (encPair encRatBin (encList enc))) := .of_eq fun _ => rfl

private theorem entry_rounded : ComputableInPolyTime (Entry.rounded (ι := ι))
    (encEntry enc) encUnary := (computable_entry_fields enc).fst'

private theorem entry_product : ComputableInPolyTime (Entry.product (ι := ι))
    (encEntry enc) encRatBin := (computable_entry_fields enc).snd'.fst'

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

/-- Construct an entry from its encoded key, product and witness. -/
theorem computable_entry : ComputableInPolyTime
    (fun p : ℕ × ℚ × List ι => let (z,q,selected) := p; (⟨z,q,selected⟩ : Entry ι))
    (encPair encUnary (encPair encRatBin (encList enc))) (encEntry enc) :=
  .of_eq fun _ => rfl

private theorem computable_extend : ComputableInPolyTime
    (fun p : ((ι × ℕ) × ℚ) × List (Entry ι) =>
      let (((i,z),q),table) := p
      extend i z q table)
    (encPair (encPair (encPair enc encUnary) encRatBin) (encList (encEntry enc)))
    (encList (encEntry enc)) := by
  have hk := entry_rounded enc
  have hp := entry_product enc
  have hs := (computable_entry_fields enc).snd'.snd'
  have hm := computable_entry enc
  have hskip : ComputableInPolyTime
      (fun p : ℚ × Entry ι => p.2.skip p.1)
      (encPair encRatBin (encEntry enc)) (encEntry enc) := by
    have h : ComputableInPolyTime
        (fun p : ℚ × Entry ι => (p.2.rounded,p.1 * p.2.product,p.2.selected))
        (encPair encRatBin (encEntry enc))
        (encPair encUnary (encPair encRatBin (encList enc))) := by fun_prop
    exact hm.comp h
  have htake : ComputableInPolyTime
      (fun p : (ι × ℕ) × Entry ι => p.2.take p.1.1 p.1.2)
      (encPair (encPair enc encUnary) (encEntry enc)) (encEntry enc) := by
    have h : ComputableInPolyTime
        (fun p : (ι × ℕ) × Entry ι => (p.2.rounded + p.1.2,p.2.product,p.1.1 :: p.2.selected))
        (encPair (encPair enc encUnary) (encEntry enc))
        (encPair encUnary (encPair encRatBin (encList enc))) := by fun_prop
    exact hm.comp h
  have hl : ComputableInPolyTime
      (fun p : ((ι × ℕ) × ℚ) × List (Entry ι) => p.2.map (Entry.skip p.1.2))
      (encPair (encPair (encPair enc encUnary) encRatBin) (encList (encEntry enc)))
      (encList (encEntry enc)) := by
    apply ComputableInPolyTime.mapWithInput (snd _ _)
    exact hskip.comp (((snd _ _).comp ((fst _ _).comp (fst _ _))).prod (snd _ _))
  have hr : ComputableInPolyTime
      (fun p : ((ι × ℕ) × ℚ) × List (Entry ι) => p.2.map (Entry.take p.1.1.1 p.1.1.2))
      (encPair (encPair (encPair enc encUnary) encRatBin) (encList (encEntry enc)))
      (encList (encEntry enc)) := by
    apply ComputableInPolyTime.mapWithInput (snd _ _)
    exact htake.comp (((fst _ _).comp ((fst _ _).comp (fst _ _))).prod (snd _ _))
  exact hl.listAppend' hr

/-- Compile the entire select/omit/prune recurrence, with the population,
initial table witness, keys and probabilities all computed from the runtime
input. Unary keys pay their numerical sizes; probabilities and products remain
binary. The hypotheses are certificates for input preparation and individual
field access, not a certificate or resource bound for the desired recurrence.
All table traversals, witness copying and normalized rational operations are
charged by the native fold/list compiler. -/
theorem computable_run {γ : Type} {encIn : γ ↪ List Bool}
    {items : γ → List ι} {initial : γ → Entry ι}
    {z : γ → ι → ℕ} {q : γ → ι → ℚ}
    (hitems : ComputableInPolyTime items encIn (encList enc))
    (hinitial : ComputableInPolyTime initial encIn (encEntry enc))
    (hz : ComputableInPolyTime (fun p : γ × ι => z p.1 p.2)
      (encPair encIn enc) encUnary)
    (hq : ComputableInPolyTime (fun p : γ × ι => q p.1 p.2)
      (encPair encIn enc) encRatBin) :
    ComputableInPolyTime (fun x => run (z x) (q x) (initial x) (items x))
      encIn (encList (encEntry enc)) := by
  have hzlist : ComputableTidilyInPolyTime (fun x => (items x).map (z x))
      encIn (encList encUnary) :=
    ComputableTidilyInPolyTime.mapWithInput hitems.tidy hz.tidy
  have hqlist : ComputableTidilyInPolyTime (fun x => (items x).map (q x))
      encIn (encList encRatBin) :=
    ComputableTidilyInPolyTime.mapWithInput hitems.tidy hq.tidy
  let S := fun x => (encEntry enc (initial x)).length + (encList enc (items x)).length +
    (encList encUnary ((items x).map (z x))).length +
    (encList encRatBin ((items x).map (q x))).length
  have hS : PolyBounded (fun x => (encIn x).length) S :=
    ((hinitial.tidy.polyBounded_length.add hitems.tidy.polyBounded_length).add
      hzlist.polyBounded_length).add hqlist.polyBounded_length
  have hstep : ComputableTidilyInPolyTime
      (fun p : (γ × List (Entry ι)) × ι =>
        let ((x,table),i) := p
        prune Entry.rounded Entry.product (extend i (z x i) (q x i) table))
      (encPair (encPair encIn (encList (encEntry enc))) enc)
      (encList (encEntry enc)) := by
    have he := computable_extend enc
    have hp := computable_prune enc
    have harg : ComputableInPolyTime
        (fun p : (γ × List (Entry ι)) × ι => (((p.2,z p.1.1 p.2),q p.1.1 p.2),p.1.2))
        (encPair (encPair encIn (encList (encEntry enc))) enc)
        (encPair (encPair (encPair enc encUnary) encRatBin) (encList (encEntry enc))) := by
      have hinput : ComputableInPolyTime
          (fun p : (γ × List (Entry ι)) × ι => (p.1.1,p.2))
          (encPair (encPair encIn (encList (encEntry enc))) enc) (encPair encIn enc) := by
        fun_prop
      have hz' := hz.comp hinput
      have hq' := hq.comp hinput
      fun_prop
    exact (hp.comp (he.comp harg)).tidy
  have hf := ComputableTidilyInPolyTime.foldlWith_spec
    (encP := encIn) (encA := enc) (encL := encList enc)
    (encB := encList (encEntry enc)) (encIn := encIn)
    (par := id) (list := fun x => (items x).reverse) (init := fun x => [initial x])
    (step := fun x table i =>
      prune Entry.rounded Entry.product (extend i (z x i) (q x i) table))
    ComputableTidilyInPolyTime.id'
    ((ComputableTidilyInPolyTime.listReverse enc).comp hitems.tidy)
    (hinitial.tidy.cons' (ComputableTidilyInPolyTime.const [])) hstep
    (fun x consumed table => table = run (z x) (q x) (initial x) consumed.reverse)
    (by intro x; rfl) (by
      intro x consumed table i _ ht
      subst table
      simp only [List.reverse_append, List.reverse_singleton, List.singleton_append, run, id_eq])
    (size := fun x => (S x + 1) * (16 * S x + 17))
    ((hS.add (.const 1)).mul (((PolyBounded.const 16).mul hS).add (.const 17))) ?_
  · refine of_tidy (hf.1.of_enc_eq ?_)
    intro x
    simp only [id_eq]
    rw [← List.foldr_eq_foldl_reverse]
    have hfold : ∀ xs : List ι,
        xs.foldr (fun i table =>
          prune Entry.rounded Entry.product (extend i (z x i) (q x i) table)) [initial x] =
          run (z x) (q x) (initial x) xs := by
      intro xs
      induction xs with
      | nil => rfl
      | cons i xs ih => simp only [List.foldr_cons, ih, run]
    rw [hfold]
  · intro x consumed table hprefix ht
    subst table
    have hsub : consumed.reverse.Sublist (items x) := by
      simpa only [List.reverse_reverse] using hprefix.sublist.reverse
    have hzsum : ((items x).map (z x)).sum ≤
        (encList encUnary ((items x).map (z x))).length := by
      simpa only [encUnary_apply, List.length_replicate, List.map_map, Function.comp_def] using
        sum_length_le_length_encList encUnary ((items x).map (z x))
    have hqsum : ((items x).map (fun i => (q x i).binaryWidth)).sum ≤
        (encList encRatBin ((items x).map (q x))).length := by
      apply (List.sum_le_sum (fun i (_ : i ∈ items x) =>
        binaryWidth_le_length_encRatBin (q x i))).trans
      simpa only [List.map_map, Function.comp_def] using
        sum_length_le_length_encList encRatBin ((items x).map (q x))
    have hzsub := List.Sublist.sum_le_sum (hsub.map (z x))
      (by intro a _; exact Nat.zero_le a)
    have hqsub := List.Sublist.sum_le_sum (hsub.map (fun i => (q x i).binaryWidth))
      (by intro a _; exact Nat.zero_le a)
    have hfields :
        (encEntry enc (initial x)).length =
          2 * (initial x).rounded + 1 + 2 * (encRatBin (initial x).product).length + 1 +
            (encList enc (initial x).selected).length := by
      change (encPair encUnary (encPair encRatBin (encList enc))
        ((initial x).rounded,(initial x).product,(initial x).selected)).length = _
      simp only [length_encPair, encUnary_apply, List.length_replicate]
      omega
    have hiw := binaryWidth_le_length_encRatBin (initial x).product
    have hlen := run_length_le (z x) (q x) (initial x) consumed.reverse
    have hkey : (initial x).rounded + (consumed.reverse.map (z x)).sum ≤ S x := by
      dsimp [S]
      omega
    have hbound (e : Entry ι)
        (he : e ∈ run (z x) (q x) (initial x) consumed.reverse) :
        (encEntry enc e).length ≤ 8 * S x + 8 := by
      have hchoices := run_sound (z x) (q x) (initial x) consumed.reverse he
      have hk := choices_rounded_le (z x) (q x) (initial x) consumed.reverse hchoices
      have hp := run_product_binaryWidth_le (z x) (q x) (initial x) consumed.reverse he
      have hs := choices_selected_sublist (z x) (q x) (initial x) consumed.reverse hchoices
      have heSel := length_encList_sublist enc
        (hs.trans (hsub.append (List.Sublist.refl (initial x).selected)))
      have heProd := length_encRatBin_le e.product
      have heLen : (encEntry enc e).length =
          2 * e.rounded + 1 + 2 * (encRatBin e.product).length + 1 +
            (encList enc e.selected).length := by
        change (encPair encUnary (encPair encRatBin (encList enc))
          (e.rounded,e.product,e.selected)).length = _
        simp only [length_encPair, encUnary_apply, List.length_replicate]
        omega
      rw [encList_append, List.length_append] at heSel
      dsimp [S] at ⊢
      omega
    have hb := length_encList_le (encEntry enc) _ hbound
    apply hb.trans
    convert Nat.mul_le_mul_right (16 * S x + 17)
      (hlen.trans (Nat.add_le_add_right hkey 1)) using 1
    ring

end Cslib.Algorithms.Lean.DynamicProgramming.MinProduct
