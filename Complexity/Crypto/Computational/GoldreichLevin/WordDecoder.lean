/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.GoldreichLevin.Parameters
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import Complexity.Probability.BitString.List
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial-time word algorithms for Goldreich–Levin decoding

The decoder is ordinary functional code: maps, filtering, folds and first-match search.
Its deterministic certificates use the shared tidy TM calculus. A fixed precision degree keeps
both the number of guesses and their complete encoded size polynomially bounded. Exact
representation laws preserve candidate order, duplicates, the fallback and every mask tape.

The predictor may capture public data and saved coins. Its certificate must be uniform jointly
in that environment and its query. Sampling and uniform PPT adversaries are connected in the
subsequent reduction; this module certifies the deterministic decoder.

## Main definitions

* `wordCandidate`, `wordCandidates`: corrected majority voting for each parity guess.
* `wordCheckCandidates`: select the first preimage, with a zero-word fallback.
* `wordDecode`: decode and check all guesses from one mask tape.

## Main results

* `polyTime_wordDecode`: uniform deterministic polynomial time for any efficient captured predictor.
* `wordDecode_eq_ofFn`, `uniform_wordDecode`: exact finite-algorithm and distributional agreement.
* `wordDecode_success_ge_half`: correlated prediction gives a valid preimage with probability
  at least one half.

## References

* [O. Goldreich, L. Levin, *A Hard-Core Predicate for All One-Way Functions*][GoldreichLevin1989]
* [L. Trevisan, *CS276 Lecture 12: Goldreich–Levin*][Trevisan2009GL]

Adapted from Crypto/Computational/GoldreichLevin/WordDecoder.lean on the cslib `crypto` branch
at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib.Crypto.GoldreichLevin

open Probability BitString Turing.MultiTapeTM

/-- A fixed precision degree is computable from a unary security parameter. -/
@[fun_prop]
theorem polyTime_precision {α : Type} {input : α ↪ List Bool} {parameter : α → ℕ}
    (hparameter : ComputableInPolyTime parameter input encUnary) (degree : ℕ) :
    ComputableInPolyTime (fun a => precision degree (parameter a)) input encUnary := by
  unfold precision
  fun_prop

/-- Computing the logarithmic mask count includes the unary precision arithmetic. -/
@[fun_prop]
theorem polyTime_maskCount {α : Type} {input : α ↪ List Bool} {dimension precision : α → ℕ}
    (hdimension : ComputableInPolyTime dimension input encUnary)
    (hprecision : ComputableInPolyTime precision input encUnary) :
    ComputableInPolyTime (fun a => maskCount (dimension a) (precision a)) input encUnary := by
  unfold maskCount
  fun_prop

/-- The selectors for nonempty subsets of the base masks. -/
def nonzeroSelectors (count : ℕ) : List (List Bool) :=
  (enumList count).filter (fun word => word.any id)

private def selectorEquiv (count : ℕ) : BitString count ≃ Finset (Fin count) where
  toFun guess := Finset.univ.filter (fun i => guess i)
  invFun subset i := decide (i ∈ subset)
  left_inv guess := by funext i; simp
  right_inv subset := by ext; simp

/-- The word selectors enumerate exactly the finite decoder's voting subsets, once each. -/
theorem listStrictMajority_nonzeroSelectors (count : ℕ) (vote : List Bool → Bool) :
    listStrictMajority ((nonzeroSelectors count).map vote) =
      strictMajorityOn (nonemptySubsets count)
        (fun s => vote (List.ofFn (fun i => decide (i ∈ s)))) := by
  let indices :=
    ((BitString.enum count).map (selectorEquiv count)).filter (fun s => decide s.Nonempty)
  have hnodup : indices.Nodup :=
    ((BitString.nodup_enum count).map (selectorEquiv count).injective).filter _
  have hall : ∀ s, s ∈ (BitString.enum count).map (selectorEquiv count) := by
    intro s
    exact List.mem_map.mpr ⟨(selectorEquiv count).symm s, BitString.mem_enum _ _, by simp⟩
  have hset : indices.toFinset = nonemptySubsets count := by
    ext s
    simp [indices, hall]
  have heq : nonzeroSelectors count =
      indices.map (fun s => List.ofFn (fun i => decide (i ∈ s))) := by
    simp only [nonzeroSelectors, enumList, indices, List.filter_map, List.map_map,
      Function.comp_def, selectorEquiv, Equiv.coe_fn_mk, Finset.mem_filter,
      Finset.mem_univ, true_and, Bool.decide_coe]
    congr 2
    funext guess
    apply Bool.eq_iff_iff.mpr
    simp [Finset.Nonempty]
  rw [heq, List.map_map, listStrictMajority_map _ hnodup, hset]
  rfl

/-- At fixed precision, the complete encoded guess list has polynomial size. -/
theorem enumList_size_polynomial (degree : ℕ) :
    PolynomiallyBounded (fun n =>
      (encList encBits (enumList (maskCount n (precision degree n)))).length) := by
  simp only [length_encList_enumList]
  have := guessCount_polynomial degree
  have := maskCount_polynomial degree
  fun_prop

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- Enumerating at a fixed precision degree includes the cost of computing the mask count. -/
@[fun_prop]
theorem polyTime_enumList_maskCount {α : Type} {input : α ↪ List Bool} {parameter : α → ℕ}
    (hparameter : ComputableInPolyTime parameter input encUnary) (degree : ℕ) :
    ComputableInPolyTime
      (fun a => enumList (maskCount (parameter a) (precision degree (parameter a))))
      input (encList encBits) := by
  have hparameter := hparameter.tidy
  refine .of_tidy ?_
  have h : ComputableTidilyInPolyTime (fun n => enumList (maskCount n (precision degree n)))
      encUnary (encList encBits) := by
    refine ComputableTidilyInPolyTime.bitsEnumList (by fun_prop)
      (enumList_size_polynomial degree) ?_
    intro n
    simp only [encUnary_apply, List.length_replicate,
      length_encList_enumList, le_refl]
  exact h.comp hparameter

/-- Decode one parity guess by mapping a corrected majority vote over the coordinates. -/
def wordCandidate (predictor : List Bool → Bool) (dimension : ℕ) (rows selectors : List (List Bool))
    (guess : List Bool) : List Bool :=
  (listSingles dimension).map (fun coordinate => listStrictMajority (selectors.map (fun selector =>
    predictor (coordinate.zipWith Bool.xor (listXorSelected dimension selector rows)) ^^
      (guess.zipWith Bool.and selector).foldl Bool.xor false)))

/-- Nested maps compose with any predictor certified jointly in its input and query. -/
@[fun_prop]
theorem polyTime_wordCandidate {α : Type} {input : α ↪ List Bool}
    {predictor : α → List Bool → Bool} {dimension : α → ℕ}
    {rows selectors : α → List (List Bool)} {guess : α → List Bool}
    (hpredictor : ComputableInPolyTime (fun p : α × List Bool => predictor p.1 p.2)
      (encPair input encBits) encBool)
    (hdimension : ComputableInPolyTime dimension input encUnary)
    (hrows : ComputableInPolyTime rows input (encList encBits))
    (hselectors : ComputableInPolyTime selectors input (encList encBits))
    (hguess : ComputableInPolyTime guess input encBits) :
    ComputableInPolyTime (fun a => wordCandidate (predictor a) (dimension a)
      (rows a) (selectors a) (guess a)) input encBits := by
  have hpredictor := hpredictor.tidy
  have hdimension := hdimension.tidy
  have hrows := hrows.tidy
  have hselectors := hselectors.tidy
  have hguess := hguess.tidy
  refine .of_tidy ?_
  unfold wordCandidate
  fun_prop

/-- The word program computes exactly the finite decoder's candidate for the same guess. -/
theorem wordCandidate_eq_ofFn {n k : ℕ} (predictor : List Bool → Bool)
    (masks : Fin k → BitString n) (guess : BitString k) :
    wordCandidate predictor n (List.ofFn (fun i => List.ofFn (masks i)))
        (nonzeroSelectors k) (List.ofFn guess) =
      List.ofFn (candidate (fun query => predictor (List.ofFn query)) masks guess) := by
  simp only [wordCandidate, listSingles_eq_ofFn, List.map_ofFn, Function.comp_def]
  congr 1
  funext i
  rw [listStrictMajority_nonzeroSelectors]
  unfold candidate
  congr 1
  funext subset
  simp only [listXorSelected_eq_ofFn_sum_subset, ← ofFn_add, ← dotProduct_eq_foldl, vote,
    Bool.one_eq_true]
  congr 1
  have h (j : Fin k) : guess j * decide (j ∈ subset) = if j ∈ subset then guess j else 0 := by
    by_cases hj : j ∈ subset <;> simp [hj, Bool.mul_eq_and, Bool.zero_eq_false]
  simp only [dotProduct, h, Finset.sum_ite_mem, Finset.univ_inter]

/-- Generate a candidate for every guess, reusing the nonzero selectors across candidates. -/
def wordCandidates (predictor : List Bool → Bool) (dimension : ℕ)
    (rows guesses : List (List Bool)) : List (List Bool) :=
  guesses.map (wordCandidate predictor dimension rows (guesses.filter (fun word => word.any id)))

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- The guess-list certificate accounts for the number and size of candidate words. -/
@[fun_prop]
theorem polyTime_wordCandidates {α : Type} {input : α ↪ List Bool}
    {predictor : α → List Bool → Bool} {dimension : α → ℕ} {rows guesses : α → List (List Bool)}
    (hpredictor : ComputableInPolyTime (fun p : α × List Bool => predictor p.1 p.2)
      (encPair input encBits) encBool)
    (hdimension : ComputableInPolyTime dimension input encUnary)
    (hrows : ComputableInPolyTime rows input (encList encBits))
    (hguesses : ComputableInPolyTime guesses input (encList encBits)) :
    ComputableInPolyTime (fun a => wordCandidates (predictor a) (dimension a)
      (rows a) (guesses a)) input (encList encBits) := by
  have hpredictor := hpredictor.tidy
  have hdimension := hdimension.tidy
  have hrows := hrows.tidy
  have hguesses := hguesses.tidy
  refine .of_tidy ?_
  unfold wordCandidates
  apply ComputableTidilyInPolyTime.mapWithInput hguesses
  apply ComputableInPolyTime.tidy
  apply polyTime_wordCandidate <;> exact .of_tidy (by fun_prop)

/-- Candidate generation preserves the finite decoder's order and duplicates. -/
theorem wordCandidates_eq_map {n k : ℕ} (predictor : List Bool → Bool)
    (masks : Fin k → BitString n) :
    wordCandidates predictor n (List.ofFn (fun i => List.ofFn (masks i))) (enumList k) =
      (candidateList (fun query => predictor (List.ofFn query)) masks).map List.ofFn := by
  rw [wordCandidates, ← nonzeroSelectors]
  simp only [enumList, candidateList, List.map_map, Function.comp_def, wordCandidate_eq_ofFn]

/-- Return the first matching candidate, defaulting to a zero word of the input dimension. -/
def wordCheckCandidates (f : List Bool → List Bool) (dimension : ℕ) (image : List Bool)
    (candidates : List (List Bool)) : List Bool :=
  (candidates.find? (fun candidate => f candidate == image)).getD
    (List.replicate dimension false)

/-- Candidate checking composes evaluation, equality, captured search and a runtime fallback. -/
@[fun_prop]
theorem polyTime_wordCheckCandidates {α : Type} {input : α ↪ List Bool}
    {f : List Bool → List Bool} {dimension : α → ℕ} {image : α → List Bool}
    {candidates : α → List (List Bool)}
    (hf : ComputableInPolyTime f encBits encBits)
    (hdimension : ComputableInPolyTime dimension input encUnary)
    (himage : ComputableInPolyTime image input encBits)
    (hcandidates : ComputableInPolyTime candidates input (encList encBits)) :
    ComputableInPolyTime
      (fun a => wordCheckCandidates f (dimension a) (image a) (candidates a)) input encBits := by
  have hf := hf.tidy
  have hdimension := hdimension.tidy
  have himage := himage.tidy
  have hcandidates := hcandidates.tidy
  refine .of_tidy ?_
  unfold wordCheckCandidates
  fun_prop

/-- Searching the word representation preserves the finite decoder's first-match behavior. -/
theorem wordCheckCandidates_eq_ofFn {n : ℕ} (f : List Bool → List Bool)
    (image : List Bool) (candidates : List (BitString n)) :
    wordCheckCandidates f n image (candidates.map List.ofFn) =
      List.ofFn (checkCandidates (fun bits => f (List.ofFn bits)) image candidates) := by
  have hzero : List.ofFn (0 : BitString n) = List.replicate n false := by
    change List.ofFn (fun _ : Fin n => false) = _
    simp
  simp only [wordCheckCandidates, checkCandidates, List.find?_map, ← hzero, Option.getD_map,
    Function.comp_def, beq_eq_decide]

/-- Decode a predictor using one mask tape, then check the candidates against the image.
The predictor may capture arbitrary public data and saved coins independently of that image. -/
def wordDecode (f : List Bool → List Bool) (predictor : List Bool → Bool) (degree dimension : ℕ)
    (image masks : List Bool) : List Bool :=
  wordCheckCandidates f dimension image (wordCandidates predictor dimension
    (listRows (maskCount dimension (precision degree dimension)) dimension masks)
    (enumList (maskCount dimension (precision degree dimension))))

/-- The complete decoder is polynomial-time for each fixed precision degree. -/
@[fun_prop]
theorem polyTime_wordDecode {α : Type} {input : α ↪ List Bool} {f : List Bool → List Bool}
    {predictor : α → List Bool → Bool} {dimension : α → ℕ} {image masks : α → List Bool}
    (degree : ℕ) (hf : ComputableInPolyTime f encBits encBits)
    (hpredictor : ComputableInPolyTime (fun p : α × List Bool => predictor p.1 p.2)
      (encPair input encBits) encBool)
    (hdimension : ComputableInPolyTime dimension input encUnary)
    (himage : ComputableInPolyTime image input encBits)
    (hmasks : ComputableInPolyTime masks input encBits) :
    ComputableInPolyTime (fun a => wordDecode f (predictor a) degree (dimension a)
      (image a) (masks a)) input encBits := by
  unfold wordDecode
  fun_prop

/-- The full word decoder agrees with its finite mathematical algorithm for every predictor
and mask tape. No assumption about how the predictor obtains its auxiliary data is required. -/
theorem wordDecode_eq_ofFn (f : List Bool → List Bool) (predictor : List Bool → Bool)
    (degree dimension : ℕ) (image masks : List Bool) :
    wordDecode f predictor degree dimension image masks =
      List.ofFn (checkCandidates (fun bits => f (List.ofFn bits)) image
        (candidateList (fun query => predictor (List.ofFn query))
          (block (ofList (maskCount dimension (precision degree dimension) * dimension)
            masks)))) := by
  simp only [wordDecode, listRows_eq_ofFn, wordCandidates_eq_map]
  exact wordCheckCandidates_eq_ofFn f image _

/-- Uniform mask bits give exactly the finite inversion experiment for a captured predictor. -/
theorem uniform_wordDecode (f : List Bool → List Bool) (predictor : List Bool → Bool)
    (degree dimension : ℕ) (image : List Bool) :
    (uniformList (maskCount dimension (precision degree dimension) * dimension)).map
        (wordDecode f predictor degree dimension image) =
      (invertFixed (n := dimension) (fun bits => f (List.ofFn bits))
        (fun query => predictor (List.ofFn query))
        (maskCount dimension (precision degree dimension)) image).map List.ofFn := by
  rw [invertFixed, ← uniformList_blocks]
  simp only [PMF.map_comp, Function.comp_def]
  congr 1
  funext masks
  exact wordDecode_eq_ofFn f predictor degree dimension image masks

/-- A sufficiently correlated word predictor yields a valid preimage with probability at least
one half. Auxiliary data stay captured in `predictor`; the recovered preimage need not be `x`. -/
theorem wordDecode_success_ge_half (f : List Bool → List Bool) (predictor : List Bool → Bool)
    (degree : ℕ) {n : ℕ} (x : BitString n)
    (h : 1 / 2 + (1 / (precision degree n : ℝ)) / 2 ≤
      agreement (fun query => predictor (List.ofFn query)) x) :
    1 / 2 ≤ (((uniformList (maskCount n (precision degree n) * n)).map
      (fun masks => f (wordDecode f predictor degree n (f (List.ofFn x)) masks) ==
        f (List.ofFn x))) true).toReal := by
  have hsuccess := invertFixed_success_ge_half (fun bits => f (List.ofFn bits))
    (fun query => predictor (List.ofFn query)) x ((1 / (precision degree n : ℝ)) / 2)
    (by have := precision_pos degree n; positivity) (maskCount_pos _ _) h
    (maskCount_sufficient n _ (precision_pos degree n))
  have hlaw := congrArg (fun p : PMF (List Bool) =>
    ((p.map (fun candidate => f candidate == f (List.ofFn x))) true).toReal)
      (uniform_wordDecode f predictor degree n (f (List.ofFn x)))
  simp only [PMF.map_comp, Function.comp_def, beq_eq_decide] at hlaw ⊢
  rw [hlaw]
  simpa only [beq_eq_decide] using hsuccess

end Cslib.Crypto.GoldreichLevin
