/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import Complexity.Crypto.Computational.GGM.Evaluation
import Mathlib.Tactic.Linarith

/-!
# Quantitative certificate clients

Resource bounds survive composition, ordinary functional spellings and streaming folds.
-/

open Turing.MultiTapeTM

namespace ComplexityTests.Quantitative

-- Quadratic computation with linear output feeds a cubic consumer without a degree-six bound.
example (f g : List Bool → List Bool)
    (hg : ComputableTidilyInDegree g encBits encBits 2 1)
    (hf : ComputableTidilyInDegree f encBits encBits 3 1) :
    ComputableTidilyInDegree (fun x => f (g x)) encBits encBits 3 1 := by
  fail_if_success (clear hg; fun_prop (disch := lia))
  fail_if_success (clear hf; fun_prop (disch := lia))
  fail_if_success
    have : ComputableTidilyInDegree (fun x => f (g x)) encBits encBits 3 0 := by
      fun_prop (disch := lia)
  fun_prop (disch := lia)

example (f g : List Bool → List Bool)
    (hg : ComputableTidilyInDegree g encBits encBits 2 1)
    (hf : ComputableTidilyInDegree f encBits encBits 3 1) :
    ComputableTidilyInDegree (f ∘ g) encBits encBits 3 1 := by
  fun_prop (disch := lia)

-- An alternative intermediate encoding and let spelling retain the same degrees.
example (f g : List Bool → List Bool)
    (hg : ComputableTidilyInDegree g encBits (encFramed encBits) 2 1)
    (hf : ComputableTidilyInDegree f (encFramed encBits) encBits 3 1) :
    ComputableTidilyInDegree (fun x => let y := g x; f y) encBits encBits 3 1 := by
  fun_prop (disch := lia)

-- Pairing preserves linear output even when the components take longer to compute.
example (f g : List Bool → List Bool)
    (hf : ComputableTidilyInDegree f encBits encBits 2 1)
    (hg : ComputableTidilyInDegree g encBits encBits 3 1) :
    ComputableTidilyInDegree (fun x => (f x, g x)) encBits (encPair encBits encBits) 3 1 := by
  fun_prop (disch := lia)

example (f g : List Bool → List Bool) (h : List Bool × List Bool → List Bool)
    (hf : ComputableTidilyInDegree f encBits encBits 2 1)
    (hg : ComputableTidilyInDegree g encBits encBits 2 1)
    (hh : ComputableTidilyInDegree h (encPair encBits encBits) encBits 3 1) :
    ComputableTidilyInDegree (fun x => h (f x, g x)) encBits encBits 3 1 := by
  fun_prop (disch := lia)

-- Reusing a let-bound value and expanding the binding must give the same resource bound.
example (f g : List Bool → List Bool)
    (hg : ComputableTidilyInDegree g encBits encBits 2 1)
    (hf : ComputableTidilyInDegree f encBits encBits 3 1) :
    ComputableTidilyInDegree (fun x => let y := g x; (f y, y)) encBits
      (encPair encBits encBits) 3 1 := by
  fun_prop (disch := lia)

example (f g : List Bool → List Bool)
    (hg : ComputableTidilyInDegree g encBits encBits 2 1)
    (hf : ComputableTidilyInDegree f encBits encBits 3 1) :
    ComputableTidilyInDegree (fun x => (f (g x), g x)) encBits
      (encPair encBits encBits) 3 1 := by
  fun_prop (disch := lia)

-- Sharing also works when the intermediate encoding differs from the input encoding.
example (f g : List Bool → List Bool)
    (hg : ComputableTidilyInDegree g encBits (encFramed encBits) 2 1)
    (hf : ComputableTidilyInDegree f (encFramed encBits) encBits 3 1) :
    ComputableTidilyInDegree (fun x => let y := g x; (f y, y)) encBits
      (encPair encBits (encFramed encBits)) 3 1 := by
  fun_prop (disch := lia)

-- Constructors, nested projections and branching infer their payload encodings. The element
-- encoding is arbitrary: this also covers framed and nonstandard representations.
example {α : Type} (enc : α ↪ List Bool) (fallback : α) :
    ComputableTidilyInDegree (fun q : Bool × List α =>
      if q.1 then q.2.headD fallback :: q.2.tail else q.2)
      (encPair encBool (encList enc)) (encList enc) 1 1 := by
  fun_prop (disch := first | apply le_refl | lia)

example {α : Type} (enc : α ↪ List Bool) (fallback : α) :
    ComputableTidilyInDegree (fun q : Bool × List α =>
      let word := q.2
      if q.1 then List.cons (List.headD word fallback) (List.tail word) else word)
      (encPair encBool (encList enc)) (encList enc) 1 1 := by
  fun_prop (disch := first | apply le_refl | lia)

-- A costly producer with linear output still gives degree three after testing and projecting.
example (f : List Bool → ℕ × Option ℕ × Bool)
    (hf : ComputableTidilyInDegree f encBits
      (encPair encUnary (encPair (encOption encUnary) encBool)) 3 1) :
    ComputableTidilyInDegree (fun x =>
      if (f x).2.1.isSome then (f x).2.1.getD 0 else (f x).1) encBits encUnary 3 1 := by
  fail_if_success
    have : ComputableTidilyInDegree (fun x =>
        if (f x).2.1.isSome then (f x).2.1.getD 0 else (f x).1) encBits encUnary 3 0 := by
      fun_prop (disch := first | apply le_refl | lia)
  fun_prop (disch := first | apply le_refl | lia)

-- The same certificates still imply ordinary polynomial time when requested.
example (f g : List Bool → List Bool)
    (hg : ComputableTidilyInDegree g encBits encBits 2 1)
    (hf : ComputableTidilyInDegree f encBits encBits 3 1) :
    ComputableTidilyInPolyTime (fun x => f (g x)) encBits encBits :=
  (show ComputableTidilyInDegree (fun x => f (g x)) encBits encBits 3 1 by
    fun_prop (disch := lia)).computableTidilyInPolyTime

-- A recognizably functional scan gets linear time and constant workspace, and emitting each
-- mapped bit uses no work-tape cells even though the output grows.
example {σ : Type} [Finite σ] (enc : σ ↪ List Bool) (step : σ → Bool → σ) (init : σ)
    (f : Bool → Bool) :
    ComputableTidilyInO (fun l : List Bool => l.foldl (· ^^ ·) false)
      encBits encBool List.length (fun _ => 0) ∧
    ComputableTidilyInO (List.foldl (fun state bit => state ^^ bit) false)
      encBits (encFramed encBool) (fun l => l.length) (fun _ => 0) ∧
    ComputableTidilyInO (fun l => l.foldl step init) encBits enc List.length (fun _ => 0) ∧
    ComputableTidilyInTimeAndSpace (fun l : List Bool => l.map f) encBits encBits
      (fun l => 4 * l.length + 8) (fun _ => 0) ∧
    ComputableTidilyInTimeAndSpace (fun l : List Bool =>
      l.foldl (fun acc b => acc ++ [f b]) []) encBits encBits
      (fun l => 4 * l.length + 8) (fun _ => 0) := by
  refine ⟨by fun_prop, by fun_prop, by fun_prop, by fun_prop, ?_⟩
  simpa only [List.foldl_append_eq_append, List.nil_append, ← List.flatMap_def,
    ← List.map_eq_flatMap] using ComputableTidilyInTimeAndSpace.map_bits f

-- The numerical loop contract also handles a genuinely growing stored accumulator.
-- Its invariant is one stored bit per consumed input bit. The cost at index i uses i, not the
-- final input length; summing it accounts for the cumulative copying of growing prefixes.
example : (∃ c, ComputableTidilyInTimeAndSpace (fun l : List Bool =>
      l.foldl (fun acc b => acc ++ [b]) []) encBits encBits
      (fun l => c * (l.length + 1) ^ 2) (fun l => c * (l.length + 1))) ∧
      ∀ l : List Bool, (l.foldl (fun acc b => acc ++ [b]) []).length = l.length := by
  have hfst : ComputableTidilyInLinearTimeAndSpace Prod.fst
      (encPair encBits encBool) encBits := Internal.NormalForm.linear (PairEncoding.fst encBool)
  have hsnd : ComputableTidilyInLinearTimeAndSpace Prod.snd
      (encPair encBits encBool) encBool := Internal.NormalForm.linear (PairEncoding.snd encBits)
  have hstep : ComputableTidilyInLinearTimeAndSpace
      (fun p : List Bool × Bool => p.1 ++ [p.2]) (encPair encBits encBool) encBits :=
    hfst.append
      hsnd (fun _ => rfl)
  obtain ⟨k, hk⟩ := hstep
  obtain ⟨⟨c, h⟩, hpost⟩ := hk.foldl_bits_stream_sum_spec (step := fun acc b => acc ++ [b]) []
    (fun _ i state => state.length = i) (by simp)
    (by intro l i hi state hs; simpa using hs)
    (R := fun _ i => k * (2 * i + 3) + 2 * i + 2)
    (Q := fun l => k * (2 * l.length + 3))
    (B := List.length)
    (by
      intro l i hi state hs
      simp only [length_encPair, encBits_apply, encBool_apply, List.length_singleton,
        List.length_append, hs]
      exact ⟨by lia, Nat.mul_le_mul_left k (by lia)⟩)
    (by intro l i hi state hs; simpa [hs] using hi)
  refine ⟨⟨c * (3 * k + 3), h.mono (fun l => ?_) (fun l => ?_)⟩, hpost⟩
  · have hsum (n : ℕ) : (∑ i ∈ Finset.range n, (k * (2 * i + 3) + 2 * i + 2)) =
        (k + 1) * n ^ 2 + (2 * k + 1) * n := by
      induction n with
      | zero => simp
      | succ n ih => rw [Finset.sum_range_succ]; nlinarith
    rw [hsum, Nat.mul_assoc]
    apply Nat.mul_le_mul_left c
    nlinarith
  · rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left c
    nlinarith


-- Resetting an accumulator charges only the prefixes actually retained between resets.
-- Long runs cost more; short runs need not pay the largest state's cost on every round.
private def resetStep (state : List Bool) (bit : Bool) : List Bool :=
  if bit then [] else state ++ [false]

example : ∃ c, ComputableTidilyInTimeAndSpace (fun l => l.foldl resetStep []) encBits encBits
    (fun l => c * ((∑ i ∈ Finset.range l.length,
      (((l.take i).foldl resetStep []).length + 1)) + 1))
    (fun l => c * (l.length + 1)) := by
  have hgrowth (state : List Bool) (bit : Bool) :
      (resetStep state bit).length ≤ state.length + 1 := by cases bit <;> simp [resetStep]
  have hlength (l state : List Bool) :
      (l.foldl resetStep state).length ≤ state.length + l.length := by
    induction l generalizing state with
    | nil => simp
    | cons b l ih =>
      have h := ih (resetStep state b)
      have hg := hgrowth state b
      simpa only [List.foldl_cons, List.length_cons] using (show
        (l.foldl resetStep (resetStep state b)).length ≤ state.length + (l.length + 1) by lia)
  have hfst : ComputableTidilyInLinearTimeAndSpace Prod.fst
      (encPair encBits encBool) encBits := Internal.NormalForm.linear (PairEncoding.fst encBool)
  have hsnd : ComputableTidilyInLinearTimeAndSpace Prod.snd
      (encPair encBits encBool) encBool := Internal.NormalForm.linear (PairEncoding.snd encBits)
  have happend : ComputableTidilyInLinearTimeAndSpace
      (fun p : List Bool × Bool => p.1 ++ [false]) (encPair encBits encBool) encBits :=
    hfst.append
      (ComputableTidilyInLinearTimeAndSpace.const (encMid := encBool) false) (fun _ => rfl)
  have hstep : ComputableTidilyInLinearTimeAndSpace
      (fun p : List Bool × Bool => resetStep p.1 p.2) (encPair encBits encBool) encBits :=
    hsnd.ite
      (ComputableTidilyInLinearTimeAndSpace.const []) (happend.restrict _)
  obtain ⟨k, hk⟩ := hstep
  obtain ⟨c, h⟩ := hk.foldl_bits_stream_sum (step := resetStep) []
    (R := fun l i => (3 * k + 2) * (((l.take i).foldl resetStep []).length + 1))
    (Q := fun l => k * (2 * l.length + 3)) (B := List.length)
    (fun l i hi => by
      have hg := hgrowth ((l.take i).foldl resetStep []) l[i]
      simp only [length_encPair, encBits_apply, encBool_apply, List.length_singleton,
        List.take_succ_eq_append_getElem hi, List.foldl_append, List.foldl_cons, List.foldl_nil]
      nlinarith)
    (fun l i hi => by
      have hl := hlength (l.take i) []
      simp only [List.length_nil, Nat.zero_add, List.length_take] at hl
      apply Nat.mul_le_mul_left k
      simp only [length_encPair, encBits_apply, encBool_apply, List.length_singleton]
      lia)
    (fun l i hi => by
      have hl := hlength (l.take i) []
      simpa only [encBits_apply, List.length_nil, Nat.zero_add, List.length_take] using
        hl.trans (by simp))
  have hn (l : List Bool) : l.length ≤ ∑ i ∈ Finset.range l.length,
      (((l.take i).foldl resetStep []).length + 1) := by
    simpa using (Finset.sum_le_sum (s := Finset.range l.length)
      (f := fun _ => 1) (g := fun i => ((l.take i).foldl resetStep []).length + 1)
      (fun _ _ => Nat.le_add_left 1 _))
  refine ⟨c * (3 * k + 3), h.mono (fun l => ?_) (fun l => ?_)⟩
  · rw [← Finset.mul_sum, Nat.mul_assoc]
    apply Nat.mul_le_mul_left c
    have hl := hn l
    nlinarith
  · rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left c
    nlinarith

-- Empty input retains and emits the nonempty initial state; one-bit input charges successor state;
-- reversal, dropLast, and getLast have linear time and zero workspace.
example :
    ¬ (∀ l : List Bool, ∀ i ≤ l.length,
      (encBits ((l.take i).foldl (fun state _ => state) [true])).length ≤ 0) ∧
    ¬ (∀ l : List Bool, ∀ i ≤ l.length,
      (encBits ((l.take i).foldl (fun state bit => state ++ [bit]) [])).length ≤ 0) ∧
    ComputableTidilyInTimeAndSpace (List.reverse (α := Bool)) encBits encBits
      (fun l => 2 * l.length + 2) (fun _ => 0) ∧
    ComputableTidilyInTimeAndSpace (List.dropLast (α := Bool)) encBits encBits
      (fun l => 4 * l.length + 8) (fun _ => 0) ∧
    ComputableTidilyInTimeAndSpace (fun l : List Bool => l.getLast?.toList) encBits encBits
      (fun l => 4 * l.length + 8) (fun _ => 0) := by
  refine ⟨fun h => ?_, fun h => ?_, by fun_prop, by fun_prop, by fun_prop⟩
  · have := h [] 0 (by simp)
    simp at this
  · have := h [true] 1 (by simp)
    simp at this

example (f : List Bool → List Bool) (hf : ComputableTidilyInDegree f encBits encBits 2 1) :
    ComputableTidilyInDegree (fun x => (f x).dropLast.reverse) encBits encBits 2 1 := by
  fail_if_success
    have : ComputableTidilyInDegree (fun x => (f x).dropLast.reverse) encBits encBits 2 0 := by
      fun_prop (disch := lia)
  fun_prop (disch := lia)

-- Because `getLast?.toList` has output degree 0, a high-degree consumer still runs in constant
-- time on its 0-or-1-bit output.
example (f g : List Bool → List Bool)
    (hf : ComputableTidilyInDegree f encBits encBits 2 1)
    (hg : ComputableTidilyInDegree g encBits encBits 5 1) :
    ComputableTidilyInDegree (fun x => g (f x).getLast?.toList) encBits encBits 2 0 := by
  fun_prop (disch := lia)

-- Second quantitative client of `streamFold_pair_sum` (via `foldl_bits_pair_stream_sum_spec`):
-- GGM tree evaluation streams the query bits from the second component of `(seed, query)` while
-- keeping only the current `n`-bit node label in the state, so workspace is
-- `O(Q + seed.length + 1)` independent of the query depth `query.length`.
theorem ggm_eval_quantitative {generator : List Bool → List Bool}
    {tChild sChild : List Bool × Bool → ℕ}
    (hchild : ComputableTidilyInTimeAndSpace
      (fun p : List Bool × Bool => Cslib.Crypto.GGM.child generator p.1 p.2)
      (encPair encBits encBool) encBits tChild sChild)
    {Q : List Bool × List Bool → ℕ}
    (hspace : ∀ p : List Bool × List Bool, ∀ i < p.2.length,
      sChild (Cslib.Crypto.GGM.eval generator p.1 (p.2.take i), p.2[i]?.getD false) ≤ Q p) :
    (∃ c, ComputableTidilyInTimeAndSpace
      (fun p : List Bool × List Bool => Cslib.Crypto.GGM.eval generator p.1 p.2)
      (encPair encBits encBits) encBits
      (fun p => c * (p.1.length + p.2.length +
        (∑ i ∈ Finset.range p.2.length,
          (tChild (Cslib.Crypto.GGM.eval generator p.1 (p.2.take i), p.2[i]?.getD false) +
            p.1.length + 1)) + 1))
      (fun p => c * (Q p + p.1.length + 1))) ∧
      ∀ p : List Bool × List Bool,
        (Cslib.Crypto.GGM.eval generator p.1 p.2).length ≤ p.1.length := by
  obtain ⟨⟨c, h⟩, hpost⟩ := hchild.foldl_bits_pair_stream_sum_spec
    (invariant := fun p i state =>
      state = Cslib.Crypto.GGM.eval generator p.1 (p.2.take i) ∧ state.length ≤ p.1.length)
    (fun _ => ⟨rfl, le_rfl⟩)
    (fun p i hi state ⟨heq, hle⟩ => by
      refine ⟨?_, (Cslib.Crypto.GGM.length_child_le generator state p.2[i]).trans hle⟩
      rw [List.take_succ_eq_append_getElem hi, Cslib.Crypto.GGM.eval_append,
        Cslib.Crypto.GGM.eval_cons, Cslib.Crypto.GGM.eval_nil, ← heq])
    (R := fun p i =>
      3 * (tChild (Cslib.Crypto.GGM.eval generator p.1 (p.2.take i), p.2[i]?.getD false) +
        p.1.length + 1))
    (Q := Q)
    (B := fun p => p.1.length)
    (fun p i hi state ⟨heq, hle⟩ => by
      have hnext_le : (Cslib.Crypto.GGM.child generator state p.2[i]).length ≤ p.1.length :=
        (Cslib.Crypto.GGM.length_child_le generator state p.2[i]).trans hle
      subst heq
      have hsp := hspace p i hi
      simp only [encBits_apply, List.getElem?_eq_getElem hi, Option.getD_some] at hsp ⊢
      exact ⟨by omega, hsp⟩)
    (fun _ _ _ _ ⟨_, hle⟩ => by simpa using hle)
  refine ⟨⟨3 * c, h.mono (fun p => ?_) (fun p => ?_)⟩, fun p => (hpost p).2⟩
  · have hsum_nonneg : 0 ≤ ∑ i ∈ Finset.range p.2.length,
        (tChild (Cslib.Crypto.GGM.eval generator p.1 (p.2.take i), p.2[i]?.getD false) +
          p.1.length + 1) := Nat.zero_le _
    simp only [← Finset.mul_sum]
    nlinarith
  · nlinarith

-- Concrete boundary evaluations of `GGM.eval` (empty query, empty seed, multi-bit path).
example :
    Cslib.Crypto.GGM.eval (fun s => s ++ s.map (!·)) [true, false] [] = [true, false] ∧
    Cslib.Crypto.GGM.eval (fun s => s ++ s.map (!·)) [] [true, false, true] = [] ∧
    Cslib.Crypto.GGM.eval (fun s => s ++ s.map (!·)) [true, false] [false, true] =
      [false, true] := by decide

/-- info: 'Turing.MultiTapeTM.read_rawFrameReader' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Turing.MultiTapeTM.read_rawFrameReader

end ComplexityTests.Quantitative
