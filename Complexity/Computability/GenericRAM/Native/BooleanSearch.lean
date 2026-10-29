/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.GenericRAM.Native.BooleanFold
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Lists
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-!
# Streaming first-match search on Boolean words

The width is a runtime unary natural. The test receives the retained context and one Boolean
word, and the search retains at most one matching word. The implementation uses `BooleanFold`;
the list of all words occurs only in the correctness specification.

This supplies the unrestricted representative scan of [OpenAI2026ETH], Lemma 3.2, printed p. 23.
In that application the test checks measurements, without the fixed-bit restriction used in the
second scan. This module does not implement that second scan or the counting algorithm.

## Main definitions

* `Cslib.GenericRAM.BooleanSearch.run`: first matching word, or `none`.
* `Cslib.GenericRAM.BooleanSearch.runPrefix`: the complete state after a prefix of the traversal.
* `Cslib.GenericRAM.BooleanSearch.certificate`: native search from a supplied native test.

## Main results

* `Cslib.GenericRAM.BooleanSearch.run_eq_find?`: equality with the existing enumeration's search.
* `Cslib.GenericRAM.BooleanSearch.run_eq_none_iff`,
  `Cslib.GenericRAM.BooleanSearch.run_some`: completeness and soundness.
* `Cslib.GenericRAM.BooleanSearch.length_prefix_le`: complete live-state bound at every prefix.
* `Cslib.GenericRAM.BooleanSearch.exists_computableInO`: traversal-proportional time and
  polynomial workspace when the test has polynomial resource bounds.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Lemma 3.2, pp. 22–23.
-/

public section

namespace Cslib.GenericRAM.BooleanSearch

open Turing.MultiTapeTM Cslib.BitString

variable {C : Type}

/-- Retain the context and the first match, using the existing list-search step. -/
@[expose] def step (test : C × List Bool → Bool)
    (p : (ℕ × List Bool) × (C × Option (List Bool))) : C × Option (List Bool) :=
  (p.2.1, if p.2.2.isSome then p.2.2 else if test (p.2.1, p.1.2) then some p.1.2 else none)

/-- Prefix state: binary index, unary width, context and at most one matching word. -/
@[expose] def runPrefix (test : C × List Bool → Bool) (p : C × ℕ) (j : ℕ) :
    ℕ × (ℕ × (C × Option (List Bool))) :=
  BooleanFold.runPrefix (step test) p.2 j (p.1, none)

/-- Stream all words of the runtime width and return the first match in enumeration order.
After finding a match the traversal retains it and makes no further calls to the test. -/
@[expose] def run (test : C × List Bool → Bool) (p : C × ℕ) : Option (List Bool) :=
  (runPrefix test p (2 ^ p.2)).2.2.2

private theorem foldl_step (test : C × List Bool → Bool) (ctx : C)
    (words : List (List Bool)) (acc : Option (List Bool)) :
    words.foldl
        (fun (s : C × Option (List Bool)) w =>
          (s.1, if s.2.isSome then s.2 else if test (s.1, w) then some w else none))
        (ctx, acc) =
      (ctx, acc.or (words.find? fun w => test (ctx, w))) := by
  induction words generalizing acc with
  | nil => simp
  | cons w words ih =>
    rw [List.foldl_cons, ih]
    cases acc with
    | some v => simp
    | none => cases h : test (ctx, w) <;> simp [h]

/-- Every prefix retains the original context and the first match among the visited words.
The list on the right is specification-only, not a stored traversal history. -/
theorem prefix_accumulator (test : C × List Bool → Bool) (p : C × ℕ) (j : ℕ) :
    (runPrefix test p j).2.2 =
      (p.1, ((List.range j).map (lowBits p.2)).find? fun w => test (p.1, w)) := by
  rw [runPrefix, BooleanFold.prefix_accumulator]
  change (List.range j).foldl
    (fun (s : C × Option (List Bool)) i =>
      (s.1, if s.2.isSome then s.2
        else if test (s.1, lowBits p.2 i) then some (lowBits p.2 i) else none))
      (p.1, none) = _
  have hm := List.foldl_map (f := lowBits p.2)
    (g := fun (s : C × Option (List Bool)) w =>
      (s.1, if s.2.isSome then s.2 else if test (s.1, w) then some w else none))
    (l := List.range j) (init := (p.1, none))
  rw [← hm, foldl_step, Option.none_or]

/-- The streaming result has exactly the first-match semantics of the existing enumeration. -/
theorem run_eq_find? (test : C × List Bool → Bool) (p : C × ℕ) :
    run test p = (enumList p.2).find? fun w => test (p.1, w) := by
  unfold run
  rw [prefix_accumulator, BooleanFold.decoded_range_eq_enumList]

/-- A returned word passes the test and every earlier word in enumeration order fails it. -/
theorem run_eq_some_iff (test : C × List Bool → Bool) (p : C × ℕ) (word : List Bool) :
    run test p = some word ↔ test (p.1, word) = true ∧
      ∃ before after, enumList p.2 = before ++ word :: after ∧
        ∀ w ∈ before, test (p.1, w) = false := by
  rw [run_eq_find?, List.find?_eq_some_iff_append]
  simp

/-- A match retained at any prefix has the requested width and passes the test. -/
theorem prefix_some (test : C × List Bool → Bool) (p : C × ℕ) (j : ℕ)
    {word : List Bool} (h : (runPrefix test p j).2.2.2 = some word) :
    word.length = p.2 ∧ test (p.1, word) = true := by
  rw [prefix_accumulator] at h
  have hm := List.mem_of_find?_eq_some h
  obtain ⟨i, _, hi⟩ := List.mem_map.mp hm
  refine ⟨?_, List.find?_some (p := fun w => test (p.1, w)) h⟩
  rw [← hi, length_lowBits]

/-- Every returned word has the requested width and passes the test. -/
theorem run_some (test : C × List Bool → Bool) (p : C × ℕ)
    {word : List Bool} (h : run test p = some word) :
    word.length = p.2 ∧ test (p.1, word) = true :=
  prefix_some test p _ h

/-- Failure means that no word of the requested width passes the test. -/
theorem run_eq_none_iff (test : C × List Bool → Bool) (p : C × ℕ) :
    run test p = none ↔ ∀ word : List Bool, word.length = p.2 → test (p.1, word) = false := by
  rw [run_eq_find?, List.find?_eq_none]
  simp only [mem_enumList, Bool.not_eq_true]

/-- A word satisfying the test exists exactly when the streaming search returns a word. -/
theorem run_ne_none_iff (test : C × List Bool → Bool) (p : C × ℕ) :
    run test p ≠ none ↔ ∃ word : List Bool, word.length = p.2 ∧ test (p.1, word) = true := by
  rw [ne_eq, run_eq_none_iff]
  simp only [not_forall, exists_prop, Bool.not_eq_false]

variable {encC : C ↪ List Bool}

private theorem length_enc_words (word : List Bool) :
    (encList encBool word).length = 3 * word.length := by
  induction word with
  | nil => rfl
  | cons b word ih =>
    simp only [encList_cons, List.length_append, length_frame, encBool_apply,
      List.length_cons, List.length_nil, ih]
    omega

/-- A prefix stores at most one width-sized result, including the option tag and list framing. -/
theorem length_prefix_result_le (test : C × List Bool → Bool) (p : C × ℕ) (j : ℕ) :
    (encOption (encList encBool) (runPrefix test p j).2.2.2).length ≤ 3 * p.2 + 1 := by
  cases h : (runPrefix test p j).2.2.2 with
  | none => simp
  | some word =>
    have hw := (prefix_some test p j h).1
    simp only [encOption_some, List.length_cons, length_enc_words, hw]
    omega

/-- The complete captured accumulator has polynomial size at every prefix, independently of
the number of visited assignments. -/
theorem length_prefix_accumulator_le (test : C × List Bool → Bool) (p : C × ℕ) (j : ℕ) :
    (encPair encC (encOption (encList encBool)) (runPrefix test p j).2.2).length ≤
      2 * (encC p.1).length + 3 * p.2 + 2 := by
  rw [length_encPair]
  have hc : (runPrefix test p j).2.2.1 = p.1 := by rw [prefix_accumulator]
  rw [hc]
  have := length_prefix_result_le test p j
  omega

/-- The full index/width/context/result state stays polynomial even at the terminal prefix. -/
theorem length_prefix_le (test : C × List Bool → Bool) (p : C × ℕ) (j : ℕ)
    (hj : j ≤ 2 ^ p.2) :
    (encPair encNat (encPair encUnary (encPair encC (encOption (encList encBool))))
      (runPrefix test p j)).length ≤ 2 * (encC p.1).length + 7 * p.2 + 6 := by
  exact (BooleanFold.length_prefix_le (step test) p.2 j _ (p.1, none) hj
    (length_prefix_accumulator_le test p j)).trans (by omega)

private abbrev encAccumulator (encC : C ↪ List Bool) :=
  encPair encC (encOption (encList encBool))

private abbrev encCallback (encC : C ↪ List Bool) :=
  encPair (encPair encUnary encBits) (encAccumulator encC)

private def contextCertificate :
    NativeCertificate (fun p : (ℕ × List Bool) × (C × Option (List Bool)) => p.2.1)
      (encCallback encC) encC :=
  NativeCertificate.linear ((ComputableInO.fst encC (encOption (encList encBool))).comp_linear
    (ComputableInO.snd (encPair encUnary encBits) (encAccumulator encC)))

private def resultCertificate :
    NativeCertificate (fun p : (ℕ × List Bool) × (C × Option (List Bool)) => p.2.2)
      (encCallback encC) (encOption (encList encBool)) :=
  NativeCertificate.linear
    ((ComputableInO.snd encC (encOption (encList encBool))).comp_linear
      (ComputableInO.snd (encPair encUnary encBits) (encAccumulator encC)))

private theorem word_polyTime :
    ComputableInPolyTime (fun p : (ℕ × List Bool) × (C × Option (List Bool)) => p.1.2)
      (encCallback encC) (encList encBool) :=
  ComputableInPolyTime.bitsToList.comp
    ((ComputableInPolyTime.snd encUnary encBits).comp
      (ComputableInPolyTime.fst (encPair encUnary encBits) (encAccumulator encC)))

private noncomputable def wordCertificate :
    NativeCertificate (fun p : (ℕ × List Bool) × (C × Option (List Bool)) => p.1.2)
      (encCallback encC) (encList encBool) :=
  NativeCertificate.ofPolyTime word_polyTime

/-- Certify the captured search step with an arbitrary native test. The outer branch skips the
test when a word has already been found; the decoder's bit word is converted to the agreed list
encoding before invoking the test. -/
noncomputable def stepCertificate {test : C × List Bool → Bool}
    (ct : NativeCertificate test (encPair encC (encList encBool)) encBool) :
    NativeCertificate (step test)
      (encPair (encPair encUnary encBits) (encPair encC (encOption (encList encBool))))
      (encPair encC (encOption (encList encBool))) := by
  exact (contextCertificate.prod
    (NativeCertificate.branch
      (resultCertificate.post (ComputableInDegree.isSome (encList encBool)).inO_one)
      resultCertificate
      (NativeCertificate.branch (ct.comp (contextCertificate.prod wordCertificate))
        wordCertificate.some (NativeCertificate.const none)))).congr (fun _ => rfl)

/-- A polynomial native test gives a polynomial step in the complete captured input encoding.
This does not assert polynomial time for the exponential traversal. -/
theorem stepCertificate_isPolynomial {test : C × List Bool → Bool}
    (ct : NativeCertificate test (encPair encC (encList encBool)) encBool)
    (hct : ct.IsPolynomial) : (stepCertificate ct).IsPolynomial := by
  unfold stepCertificate
  apply NativeCertificate.congr_isPolynomial
  apply NativeCertificate.prod_isPolynomial
  · exact NativeCertificate.linear_isPolynomial _
  · apply NativeCertificate.branch_isPolynomial
    · apply NativeCertificate.post_isPolynomial
      exact NativeCertificate.linear_isPolynomial _
    · exact NativeCertificate.linear_isPolynomial _
    · apply NativeCertificate.branch_isPolynomial
      · apply NativeCertificate.comp_isPolynomial _ _ hct
        apply NativeCertificate.prod_isPolynomial
        · exact NativeCertificate.linear_isPolynomial _
        · exact NativeCertificate.ofPolyTime_isPolynomial _
      · apply NativeCertificate.some_isPolynomial
        exact NativeCertificate.ofPolyTime_isPolynomial _
      · exact NativeCertificate.const_isPolynomial _

/-- One fixed native machine searches all runtime widths and contexts. Its independently
charged time and space bounds are those of the binary streaming iterator, including count
preparation, initialization, decoding, the selected test calls and output projection. -/
noncomputable def certificate {test : C × List Bool → Bool}
    (ct : NativeCertificate test (encPair encC (encList encBool)) encBool) :
    NativeCertificate (run test) (encPair encC encUnary) (encOption (encList encBool)) :=
  ((BooleanFold.certificate
    (NativeCertificate.linear (ComputableInO.snd encC encUnary))
    ((NativeCertificate.linear (ComputableInO.fst encC encUnary)).prod
      (NativeCertificate.const none)) (stepCertificate ct)).snd.snd.snd).congr (fun _ => rfl)

/-- With a polynomial test, search takes the traversal count times polynomial overhead and
only polynomial charged workspace. The two polynomials and the realizing machine are fixed
before the runtime context and width. In particular, the traversal count does not enter space. -/
theorem exists_computableInO {test : C × List Bool → Bool}
    (ct : NativeCertificate test (encPair encC (encList encBool)) encBool)
    (hct : ct.IsPolynomial) :
    ∃ overhead workspace : C × ℕ → ℕ,
      PolyBounded (fun p => (encPair encC encUnary p).length) overhead ∧
      PolyBounded (fun p => (encPair encC encUnary p).length) workspace ∧
      ComputableInO (run test) (encPair encC encUnary) (encOption (encList encBool))
        (fun p => (2 ^ p.2 + 1) * overhead p) workspace := by
  let size := fun p : C × ℕ => (encPair encC encUnary p).length
  let cn := BooleanFold.clock.comp
    (NativeCertificate.linear (ComputableInO.snd encC encUnary))
  let ci := (NativeCertificate.linear (ComputableInO.snd encC encUnary)).prod
    ((NativeCertificate.linear (ComputableInO.fst encC encUnary)).prod
      (NativeCertificate.const (em := encOption (encList encBool)) none))
  let cv := BooleanFold.visitCertificate (stepCertificate ct)
  have hcv := BooleanFold.visitCertificate_isPolynomial (stepCertificate ct)
    (stepCertificate_isPolynomial ct hct)
  obtain ⟨a, b, ht⟩ := hcv.1.exists_le
  obtain ⟨c, d, hs⟩ := hcv.2.exists_le
  let B := fun p : C × ℕ => 10 * (size p + 1)
  let R := fun p : C × ℕ => a * (B p + 1) ^ b
  let Q := fun p : C × ℕ => c * (B p + 1) ^ d
  have hstate (p : C × ℕ) (j : ℕ) (hj : j ≤ 2 ^ p.2) :
      (encPair encNat (encPair encUnary (encPair encC (encOption (encList encBool))))
        (runPrefix test p j)).length ≤ B p := by
    have h := length_prefix_le (encC := encC) test p j hj
    apply h.trans
    simp only [B, size, length_encPair, encUnary_apply, List.length_replicate]
    omega
  have hrun := IndexFold.computableInO cn ci cv R Q B
    (fun p j hj => (ht (runPrefix test p j)).trans
      (Nat.mul_le_mul_left a (Nat.pow_le_pow_left (by
        have := hstate p j hj
        omega) b)))
    (fun p j hj => (hs (runPrefix test p j)).trans
      (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by
        have := hstate p j hj
        omega) d)))
    (fun p j hj => by
      have h := hstate p j hj
      rw [length_encPair] at h
      exact le_trans (Nat.le_add_left _ _) h)
  have hfinal := (ComputableInO.snd encC (encOption (encList encBool))).comp_linear
    ((ComputableInO.snd encUnary (encAccumulator encC)).comp_linear
      ((ComputableInO.snd encNat (encPair encUnary (encAccumulator encC))).comp_linear hrun))
  let stateSize := fun p : C × ℕ => 2 * (p.2 + 1) + 1 + B p
  let overhead := fun p : C × ℕ => cn.time p + (size p + ci.time p) +
    (stateSize p + (p.2 + 2) ^ 2 + R p) + stateSize p + (p.2 + 2) ^ 2
  let workspace := fun p : C × ℕ => cn.space p + (size p + ci.space p) +
    (stateSize p + (p.2 + 2) + Q p) + stateSize p + (p.2 + 1)
  have hn : PolyBounded size (fun p : C × ℕ => p.2) := PolyBounded.self.mono fun p => by
    simp only [size, length_encPair, encUnary_apply, List.length_replicate]
    omega
  have hB : PolyBounded size B := (PolyBounded.const 10).mul
    (PolyBounded.self.add (PolyBounded.const 1))
  have hR : PolyBounded size R := NativeCertificate.polyBounded_pow_of_polyBounded hB a b
  have hQ : PolyBounded size Q := NativeCertificate.polyBounded_pow_of_polyBounded hB c d
  have hci : ci.IsPolynomial := NativeCertificate.prod_isPolynomial _ _
    (NativeCertificate.linear_isPolynomial _)
    (NativeCertificate.prod_isPolynomial _ _ (NativeCertificate.linear_isPolynomial _)
      (NativeCertificate.const_isPolynomial _))
  have hcn : cn.IsPolynomial := by
    change (BooleanFold.clock.comp _).IsPolynomial
    apply NativeCertificate.comp_isPolynomial
    · exact ⟨PolyBounded.self, PolyBounded.self⟩
    · exact NativeCertificate.linear_isPolynomial _
  have hstateSize : PolyBounded size stateSize :=
    (((PolyBounded.const 2).mul (hn.add (PolyBounded.const 1))).add
      (PolyBounded.const 1)).add hB
  have hsq : PolyBounded size (fun p : C × ℕ => (p.2 + 2) ^ 2) := by
    simpa only [one_mul, Nat.add_assoc] using
      NativeCertificate.polyBounded_pow_of_polyBounded (hn.add (PolyBounded.const 1)) 1 2
  refine ⟨overhead, workspace,
    ((((hcn.1.add (PolyBounded.self.add hci.1)).add
      ((hstateSize.add hsq).add hR)).add hstateSize).add hsq),
    ((((hcn.2.add (PolyBounded.self.add hci.2)).add
      ((hstateSize.add (hn.add (PolyBounded.const 2))).add hQ)).add hstateSize).add
      (hn.add (PolyBounded.const 1))), ?_⟩
  apply hfinal.mono_le
  · intro p
    simp only [Function.comp_apply, BooleanFold.length_clock]
    dsimp only [overhead, stateSize]
    have hcount : (1 : ℕ) ≤ 2 ^ p.2 + 1 := Nat.le_add_left 1 _
    nlinarith
  · intro p
    simp only [Function.comp_apply, BooleanFold.length_clock]
    exact le_rfl

end Cslib.GenericRAM.BooleanSearch
