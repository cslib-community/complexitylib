/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Tactic.PolyTime

/-!
# Encoding inference and input-dependent loop contracts

Fixed scans need no encoding of their indices. Runtime scans retain joint certificates, while
loop bounds charge the full framed state on every reachable iteration.
-/

namespace ComplexityTests.PolyTimeContracts

open Turing.MultiTapeTM

-- The size adapter has exactly the original pointwise polynomial contract.
example {α : Type*} (size cost : α → ℕ) :
    PolyBounded size cost ↔ ∃ c d, ∀ a, cost a ≤ c * (size a + 1) ^ d :=
  ⟨PolyBounded.exists_le, fun ⟨c, d, h⟩ => .of_forall_le c d h⟩

example (cost : ℕ → ℕ) : PolyBounded id cost ↔ Cslib.PolynomiallyBounded cost :=
  ⟨PolyBounded.polynomiallyBounded, PolyBounded.of_polynomiallyBounded id⟩

-- Costs can depend on more than size; composing a nonmonotone upstream bound still works.
example : PolyBounded (fun p : ℕ × ℕ => p.1)
    (fun p => if min p.1 p.2 = 0 then 7 else min p.1 p.2) := by
  have hbound : Cslib.PolynomiallyBounded (fun n => if n = 0 then 7 else n) := by fun_prop
  exact (PolyBounded.of_polynomiallyBounded id hbound).comp
    (PolyBounded.self.mono fun p => Nat.min_le_left p.1 p.2)

-- A constant size cannot hide costs unbounded within that size, even at size zero.
example : ¬ PolyBounded (fun _ : ℕ => 0) id := by
  intro h
  obtain ⟨c, d, h⟩ := h.exists_le
  have hbad := h (c + 1)
  simp only [id_eq, zero_add, one_pow, Nat.mul_one] at hbad
  lia

-- Fixed lists may contain higher-universe objects for which no bit encoding is supplied.
example {ι : Type 1} (indices : List ι) (test : List Bool → ι → Bool)
    (htest : ∀ i ∈ indices,
      ComputableTidilyInPolyTime (fun word => test word i) encBits encBool) :
    ComputableTidilyInPolyTime (fun word => indices.all (test word)) encBits encBool := by
  fun_prop

example {ι : Type 1} (indices : List ι) (test : List Bool → ι → Bool)
    (htest : ∀ i ∈ indices,
      ComputableTidilyInPolyTime (fun word => test word i) encBits encBool) :
    ComputableTidilyInPolyTime (fun word => indices.any fun i => test word i)
      encBits encBool := by
  polytime

-- No callback certificate is needed when there are no indices.
example (test : List Bool → Fin 0 → Bool) :
    ComputableTidilyInPolyTime (fun word => ([] : List (Fin 0)).all (test word))
      encBits encBool := by
  exact ComputableTidilyInPolyTime.allConst [] (by simp)

-- The same runtime scan supports unrelated element representations.
example {α β : Type} (input : α ↪ List Bool) (element : β ↪ List Bool)
    (values : α → List β) (test : α × β → Bool)
    (hvalues : ComputableTidilyInPolyTime values input (encList element))
    (htest : ComputableTidilyInPolyTime test (encPair input element) encBool) :
    ComputableTidilyInPolyTime
      (fun x => let entries := values x; entries.all fun value => test (x, value))
      input encBool := by
  fail_if_success (clear hvalues; polytime)
  fail_if_success (clear htest; polytime)
  polytime

example {α β : Type} (input : α ↪ List Bool) (element : β ↪ List Bool)
    (values : α → List β) (test : α × β → Bool)
    (hvalues : ComputableTidilyInPolyTime values input (encList element))
    (htest : ComputableTidilyInPolyTime test (encPair input element) encBool) :
    ComputableTidilyInPolyTime (fun x => (values x).any fun value => test (x, value))
      input encBool := by
  polytime

-- Raw and framed Boolean words use their existing list interfaces.
example : ComputableTidilyInPolyTime
    (fun p : List Bool × Bool => p.1.all fun bit => bit == p.2)
    (encPair encBits encBool) encBool := by polytime

example : ComputableTidilyInPolyTime
    (fun p : List Bool × Bool => p.1.all (fun bit => bit == p.2))
    (encPair (encList encBool) encBool) encBool := by polytime

example : ComputableTidilyInPolyTime
    (fun p : List ℕ × ℕ => p.1.any fun n => n == p.2)
    (encPair (encList encNat) encNat) encBool := by polytime

example : ComputableTidilyInPolyTime
    (fun p : List ℕ × ℕ => p.1.any fun n => n == p.2)
    (encPair (encList encUnary) encUnary) encBool := by polytime

-- Separate certificates at each fixed index give no uniform runtime-index certificate.
example (test : List Bool → ℕ → Bool)
    (_hfixed : ∀ n, ComputableTidilyInPolyTime (fun word => test word n) encBits encBool) :
    True := by
  fail_if_success
    have : ComputableTidilyInPolyTime
        (fun word => (List.range word.length).all (test word)) encBits encBool := by polytime
  trivial

-- An arbitrary mathematical bound need not have a computation certificate.
example {α β : Type} {input : α ↪ List Bool} {stateEncoding : β ↪ List Bool}
    {initial : α → β} {step : β → β} {count bound : α → ℕ}
    (hcount : ComputableTidilyInPolyTime count input encUnary)
    (hinitial : ComputableTidilyInPolyTime initial input stateEncoding)
    (hstep : ComputableTidilyInPolyTime step stateEncoding stateEncoding)
    (invariant : α → ℕ → β → Prop)
    (hbase : ∀ x, invariant x 0 (initial x))
    (hpreserve : ∀ x i state, i < count x → invariant x i state →
      invariant x (i + 1) (step state))
    (hsize : PolyBounded (fun x => (input x).length) bound)
    (hbound : ∀ x i state, i ≤ count x → invariant x i state →
      (stateEncoding state).length ≤ bound x) :
    ComputableTidilyInPolyTime (fun x => step^[count x] (initial x)) input stateEncoding := by
  exact (ComputableTidilyInPolyTime.iterate_spec hcount hinitial hstep invariant
    hbase hpreserve hsize hbound).1

-- Accumulating rows charges each copied row and every outer list frame.
private def repeatRows (p : List Bool × ℕ) : List (List Bool) :=
  (fun rows => p.1 :: rows)^[p.2] []

private theorem repeatRows_spec :
    ComputableTidilyInPolyTime repeatRows (encPair encBits encUnary) (encList encBits) ∧
      ∀ p, (repeatRows p).length = p.2 ∧ ∀ row ∈ repeatRows p, row = p.1 := by
  unfold repeatRows
  refine ComputableTidilyInPolyTime.iterateWith_spec (par := Prod.fst)
    (count := Prod.snd) (init := fun _ => []) (step := List.cons)
    (by polytime) (by polytime) (by polytime) (by polytime)
    (invariant := fun p i rows => rows.length = i ∧ ∀ row ∈ rows, row = p.1)
    (by simp) ?_ (size := fun p => p.2 * (2 * p.1.length + 1)) ?_ ?_
  · intro p i rows _ h
    simpa only [List.length_cons, h.1, List.mem_cons, forall_eq_or_imp, true_and]
      using h.2
  · exact ComputableTidilyInPolyTime.polyBounded (by polytime)
  · intro p i rows hi h
    calc
      (encList encBits rows).length ≤ rows.length * (2 * p.1.length + 1) :=
        length_encList_le encBits rows fun row hrow => by simp [h.2 row hrow]
      _ ≤ _ := by simpa only [h.1] using Nat.mul_le_mul_right (2 * p.1.length + 1) hi

-- A nested loop composes the row certificate; no intermediate representation is supplied here.
example : ComputableTidilyInPolyTime (fun p : List Bool × ℕ =>
    (List.range p.2).flatMap fun n => repeatRows (p.1, n))
    (encPair encBits encUnary) (encList encBits) := by
  have h := repeatRows_spec.1
  polytime

example : repeatRows ([true, false], 0) = [] := rfl
example : (encList encBits (repeatRows ([true, false], 3))).length = 15 := by decide

private abbrev TaggedRowsInput := (List (List Bool) × List Bool) × List (List Bool)
private abbrev taggedRowsInputEncoding :=
  encPair (encPair (encList encBits) encBits) (encList encBits)

private def tagRows (p : TaggedRowsInput) : List (List Bool) :=
  p.1.1.foldl (fun rows row => (row ++ p.1.2) :: rows) p.2

-- Each copied row is bounded by the actual source list, including with an arbitrary initial state.
-- No fixed additive bound would hold for all possible rows outside that list.
private theorem tagRows_polytime :
    ComputableTidilyInPolyTime tagRows taggedRowsInputEncoding (encList encBits) := by
  unfold tagRows taggedRowsInputEncoding
  refine ComputableTidilyInPolyTime.foldlWith_of_bounded_growth (encA := encBits)
    (par := fun p : TaggedRowsInput => p.1.2)
    (step := fun tag rows row => (row ++ tag) :: rows)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (growth := fun p => 2 * ((encList encBits p.1.1).length + p.1.2.length) + 1)
    (ComputableTidilyInPolyTime.polyBounded (by fun_prop)) ?_
  intro p state row hrow
  have hsize := SizedListEncoding.length_elem_le
    (encA := encBits) (encL := encList encBits) p.1.1 row hrow
  simp only [encList_cons, List.length_append, length_frame, encBits_apply] at hsize ⊢
  lia

-- A downstream traversal consumes the accumulated rows through the ordinary list API.
example : ComputableTidilyInPolyTime (fun p => (tagRows p).map List.reverse)
    taggedRowsInputEncoding (encList encBits) := by
  have h := tagRows_polytime
  polytime

example : tagRows (([], [true]), [[false]]) = [[false]] := rfl
example : tagRows (([[false], [false]], [true]), [[true]]) =
    [[false, true], [false, true], [true]] := by decide

private def skipCopies (p : (Bool × ℕ) × List Bool) : List Bool :=
  (List.replicate p.1.2 p.1.1).foldl
    (fun state bit => if bit = p.1.1 then state else state ++ state) p.2

-- Prefix membership, rather than a global growth claim, rules out the doubling branch.
private theorem skipCopies_spec :
    ComputableTidilyInPolyTime skipCopies (encPair (encPair encBool encUnary) encBits) encBits ∧
      ∀ p, skipCopies p = p.2 := by
  unfold skipCopies
  refine ComputableTidilyInPolyTime.foldlWith_spec (encA := encBool) (encL := encList encBool)
    (par := fun p : (Bool × ℕ) × List Bool => p.1.1)
    (step := fun tag state bit => if bit = tag then state else state ++ state)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (fun p _ state => state = p.2) (by simp) ?_
    (size := fun p => p.2.length) (ComputableTidilyInPolyTime.polyBounded (by fun_prop)) ?_
  · intro p consumed state bit hprefix hstate
    have hbit : bit = p.1.1 := List.eq_of_mem_replicate (hprefix.subset (by simp))
    simp [hbit, hstate]
  · intro p consumed state _ hstate
    simp [hstate]

example : skipCopies ((true, 3), [true, false]) = [true, false] := skipCopies_spec.2 _

-- A standard outer operation leaves the fold's meaningful step and growth contracts usable.
example (step : List Bool → Bool → List Bool) (growth : ℕ)
    (hstep : ComputableTidilyInPolyTime (fun pair : List Bool × Bool => step pair.1 pair.2)
      (encPair encBits encBool) encBits)
    (hgrowth : ∀ word bit, (step word bit).length ≤ word.length + growth) :
    ComputableTidilyInPolyTime (fun word : List Bool => (word.foldl step []).reverse)
      encBits encBits := by
  fail_if_success (clear hstep; polytime)
  fail_if_success (clear hgrowth; polytime)
  polytime

-- Framed input and state elements may have unrelated encodings; let notation needs no annotation.
example {α β : Type} (item : α ↪ List Bool) (stateElement : β ↪ List Bool)
    (step : List β → α → List β) (growth : ℕ)
    (hstep : ComputableTidilyInPolyTime (fun pair : List β × α => step pair.1 pair.2)
      (encPair (encList stateElement) item) (encList stateElement))
    (hgrowth : ∀ state value, (encList stateElement (step state value)).length ≤
      (encList stateElement state).length + growth) :
    ComputableTidilyInPolyTime
      (fun list : List α => let accumulated := list.foldl step []; accumulated.reverse)
      (encList item) (encList stateElement) := by polytime

-- Growth outside the reachable invariant does not matter; the step still has a uniform certificate.
example : ComputableTidilyInPolyTime
    (fun n : ℕ => (fun word : List Bool => if word.isEmpty then [] else word ++ word)^[n] [])
    encUnary encBits := by
  refine (ComputableTidilyInPolyTime.iterate_spec (by polytime) (by polytime) (by polytime)
    (fun _ _ word => word = []) (by simp) ?_ (.const 0) ?_).1
  · intros
    simp_all
  · intros
    simp_all

-- A small final projection supplies no bound on a loop's intermediate storage.
example : True := by
  fail_if_success
    have : ComputableTidilyInPolyTime (fun n : ℕ =>
        ((fun p : ℕ × List Bool =>
          if p.1 = 0 then (0, []) else (p.1 - 1, p.2 ++ p.2))^[n + 1] (n, [true])).2)
        encUnary encBits := by polytime
  trivial

section CapturedFold

variable {γ α β : Type} (input : γ ↪ List Bool) (element : α ↪ List Bool)
    (stateEncoding : β ↪ List Bool) (listEncoding : List α ↪ List Bool)
    [hencoding : ListEncoding element listEncoding]
    [hsize : SizedListEncoding element listEncoding]
    (list : γ → List α) (initial : γ → β) (step : γ → β → α → β)
    (hlist : ComputableTidilyInPolyTime list input listEncoding)
    (hinitial : ComputableTidilyInPolyTime initial input stateEncoding)
    (hstep : ComputableTidilyInPolyTime (fun p : (γ × β) × α => step p.1.1 p.1.2 p.2)
      (encPair (encPair input stateEncoding) element) stateEncoding)
    (growth : γ → ℕ) (hpoly : PolyBounded (fun x => (input x).length) growth)
    (hgrowth : ∀ x state value, value ∈ list x →
      (stateEncoding (step x state value)).length ≤ (stateEncoding state).length + growth x)

include hlist hinitial hstep hpoly hgrowth

-- Each part of the contract is needed. The growth bound need not itself be computable.
example : ComputableTidilyInPolyTime (fun x => (list x).foldl (step x) (initial x))
    input stateEncoding := by
  fail_if_success (clear hlist; polytime)
  fail_if_success (clear hinitial; polytime)
  fail_if_success (clear hstep; polytime)
  fail_if_success (clear hpoly; polytime)
  fail_if_success (clear hgrowth; polytime)
  fail_if_success (clear hencoding; polytime)
  fail_if_success (clear hsize; polytime)
  polytime

-- Joint inference chooses compatible list, callback and encoding evidence. Competing encodings,
-- polynomial bounds and growth inequalities must not commit to an incompatible choice.
example (otherElement : α ↪ List Bool) (otherListEncoding : List α ↪ List Bool)
    [ListEncoding otherElement otherListEncoding]
    [SizedListEncoding otherElement otherListEncoding]
    (_hotherList : ComputableTidilyInPolyTime list input otherListEncoding)
    (otherGrowth looseGrowth : γ → ℕ)
    (_hother : PolyBounded (fun x => (input x).length) otherGrowth)
    (_hloose : ∀ x state value, value ∈ list x →
      (stateEncoding (step x state value)).length ≤ (stateEncoding state).length + looseGrowth x) :
    ComputableTidilyInPolyTime (fun x => (list x).foldl (step x) (initial x))
      input stateEncoding := by
  revert hlist hpoly hgrowth
  intro hlist hpoly hgrowth
  have : ComputableTidilyInPolyTime
      (fun x => let entries := list x; entries.foldl (fun state value => step x state value)
        (initial x)) input stateEncoding := by polytime
  clear this
  revert _hotherList _hother _hloose
  intro _hotherList _hother _hloose
  polytime

omit hlist
variable {otherListEncoding₁ otherListEncoding₂ : List α ↪ List Bool}
    {otherElement₁ otherElement₂ otherCallbackElement : α ↪ List Bool}
    [hencoding₁ : ListEncoding otherElement₁ otherListEncoding₁]
    [hsize₁ : SizedListEncoding otherElement₁ otherListEncoding₁]
    [hencoding₂ : ListEncoding otherElement₂ otherListEncoding₂]
    [hsize₂ : SizedListEncoding otherElement₂ otherListEncoding₂]
    (_hotherStep : ComputableTidilyInPolyTime
      (fun p : (γ × β) × α => step p.1.1 p.1.2 p.2)
      (encPair (encPair input stateEncoding) otherCallbackElement) stateEncoding)

include hencoding₁ hsize₁ hencoding₂ hsize₂ _hotherStep

-- All six certificate orders must work, including when the compatible choice is in the middle.
-- Every list representation has interfaces, but only one callback certificate is compatible.
example (hgood : ComputableTidilyInPolyTime list input listEncoding)
    (_hother₁ : ComputableTidilyInPolyTime list input otherListEncoding₁)
    (_hother₂ : ComputableTidilyInPolyTime list input otherListEncoding₂) :
    ComputableTidilyInPolyTime (fun x => (list x).foldl (step x) (initial x))
      input stateEncoding := by polytime

example (hgood : ComputableTidilyInPolyTime list input listEncoding)
    (_hother₂ : ComputableTidilyInPolyTime list input otherListEncoding₂)
    (_hother₁ : ComputableTidilyInPolyTime list input otherListEncoding₁) :
    ComputableTidilyInPolyTime
      (fun x => (list x).foldl (fun state value => step x state value) (initial x))
      input stateEncoding := by
  revert hstep
  intro hstep
  polytime

example (_hother₁ : ComputableTidilyInPolyTime list input otherListEncoding₁)
    (hgood : ComputableTidilyInPolyTime list input listEncoding)
    (_hother₂ : ComputableTidilyInPolyTime list input otherListEncoding₂) :
    ComputableTidilyInPolyTime
      (fun x => let entries := list x;
        entries.foldl (fun state value => step x state value) (initial x))
      input stateEncoding := by polytime

example (_hother₂ : ComputableTidilyInPolyTime list input otherListEncoding₂)
    (hgood : ComputableTidilyInPolyTime list input listEncoding)
    (_hother₁ : ComputableTidilyInPolyTime list input otherListEncoding₁) :
    ComputableTidilyInPolyTime (fun x => (list x).foldl (step x) (initial x))
      input stateEncoding := by
  revert hstep
  intro hstep
  polytime

example (_hother₁ : ComputableTidilyInPolyTime list input otherListEncoding₁)
    (_hother₂ : ComputableTidilyInPolyTime list input otherListEncoding₂)
    (hgood : ComputableTidilyInPolyTime list input listEncoding) :
    ComputableTidilyInPolyTime
      (fun x => (list x).foldl (fun state value => step x state value) (initial x))
      input stateEncoding := by polytime

example (_hother₂ : ComputableTidilyInPolyTime list input otherListEncoding₂)
    (_hother₁ : ComputableTidilyInPolyTime list input otherListEncoding₁)
    (hgood : ComputableTidilyInPolyTime list input listEncoding) :
    ComputableTidilyInPolyTime
      (fun x => let entries := list x;
        entries.foldl (fun state value => step x state value) (initial x))
      input stateEncoding := by
  revert hstep
  intro hstep
  polytime

end CapturedFold

private def taggedBits (p : List Bool × List Bool) : List Bool :=
  p.2.foldl (fun state bit => p.1 ++ bit :: state) []

private theorem taggedBits_growth (p : List Bool × List Bool) (state : List Bool) (bit : Bool) :
    (p.1 ++ bit :: state).length ≤ state.length + (p.1.length + 1) := by
  simp [Nat.add_left_comm]

-- Both raw and framed source words infer the callback encoding from ordinary constructors.
example : ComputableTidilyInPolyTime taggedBits (encPair encBits encBits) encBits := by
  have hpoly : PolyBounded (fun p : List Bool × List Bool =>
      (encPair encBits encBits p).length) (fun p => p.1.length + 1) :=
    ComputableTidilyInPolyTime.polyBounded (by fun_prop)
  have hgrowth := taggedBits_growth
  unfold taggedBits
  polytime

example : ComputableTidilyInPolyTime
    (fun p : List Bool × List Bool => let tag := p.1;
      p.2.foldl (fun state bit => tag ++ bit :: state) [])
    (encPair encBits (encList encBool)) encBits := by
  have hpoly : PolyBounded (fun p : List Bool × List Bool =>
      (encPair encBits (encList encBool) p).length) (fun p => p.1.length + 1) :=
    ComputableTidilyInPolyTime.polyBounded (by fun_prop)
  have hgrowth := taggedBits_growth
  polytime

example : taggedBits ([true], [false, false]) = [true, false, true, false] := by decide

section CapturedIteration

variable {α β : Type} (input : α ↪ List Bool) (stateEncoding : β ↪ List Bool)
    (count : α → ℕ) (initial : α → β) (step : α → β → β)
    (hcount : ComputableTidilyInPolyTime count input encUnary)
    (hinitial : ComputableTidilyInPolyTime initial input stateEncoding)
    (hstep : ComputableTidilyInPolyTime (fun p : α × β => step p.1 p.2)
      (encPair input stateEncoding) stateEncoding)
    (growth : α → ℕ) (hpoly : PolyBounded (fun x => (input x).length) growth)
    (hgrowth : ∀ x state, (stateEncoding (step x state)).length ≤
      (stateEncoding state).length + growth x)

include hcount hinitial hstep hpoly hgrowth

-- A captured loop still needs a unary count, uniform step and polynomial state-growth bound.
example : ComputableTidilyInPolyTime (fun x => (step x)^[count x] (initial x))
    input stateEncoding := by
  fail_if_success (clear hcount; polytime)
  fail_if_success (clear hinitial; polytime)
  fail_if_success (clear hstep; polytime)
  fail_if_success (clear hpoly; polytime)
  fail_if_success (clear hgrowth; polytime)
  polytime

-- Bounds are selected jointly, independently of hypothesis order and callback spelling.
example (otherGrowth looseGrowth : α → ℕ)
    (_hother : PolyBounded (fun x => (input x).length) otherGrowth)
    (_hloose : ∀ x state, (stateEncoding (step x state)).length ≤
      (stateEncoding state).length + looseGrowth x) :
    ComputableTidilyInPolyTime (fun x => (step x)^[count x] (initial x))
      input stateEncoding := by
  revert hpoly hgrowth
  intro hpoly hgrowth
  have : ComputableTidilyInPolyTime
      (fun x => let update := fun state => step x state; update^[count x] (initial x))
      input stateEncoding := by polytime
  clear this
  revert _hother _hloose
  intro _hother _hloose
  polytime

end CapturedIteration

-- Accumulating captured rows infers the framed state and pays for each copied row.
example : ComputableTidilyInPolyTime
    (fun p : List Bool × ℕ => (fun rows => p.1 :: rows)^[p.2] [])
    (encPair encBits encUnary) (encList encBits) := by
  have hpoly : PolyBounded (fun p : List Bool × ℕ => (encPair encBits encUnary p).length)
      (fun p => 2 * p.1.length + 1) :=
    ComputableTidilyInPolyTime.polyBounded (by polytime)
  have hgrowth (p : List Bool × ℕ) (rows : List (List Bool)) :
      (encList encBits (p.1 :: rows)).length ≤
        (encList encBits rows).length + (2 * p.1.length + 1) := by
    simp [Nat.add_comm]
  polytime

end ComplexityTests.PolyTimeContracts
