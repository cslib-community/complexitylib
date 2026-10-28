/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.MatrixMultiplication.Schonhage.Pruned
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Meaning

/-!
# Numerical query codes for native pruned evaluation

The output variables use the existing term numbering through their private terms: the nine
outer outputs have digits zero through eight and the inner output has digit nine. The first
coordinate is the least significant digit, exactly as for the encoded leaf arrays.

## Main definitions

* `PrunedQuery.queryIndex`: the flat code of an output string.
* `PrunedQuery.childCodes`: the child request set, computed by digit tests and division.

## Main results

* `PrunedQuery.queryIndex_privateLeaf`: agreement with the existing leaf-array indexing.
* `PrunedQuery.queryIndex_cons`: the numerical first-digit decomposition.

## References

The child-set definition is adapted from [AlmanWilliams2026, Section 2.4.2] and Anthropic's
formal source at revision `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`,
[pinned source](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec2/Lemma10.lean). These are finite coding identities, not native run claims.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Output digits follow their private terms in the existing encoder's numbering. -/
def outputDigits : Fin 10 ≃ OutVar where
  toFun t := match Encoding.termAt t with
    | .P i j => .z i j
    | .P0 => .z0
  invFun z := Encoding.termDigits.symm z.privateTerm
  left_inv := by decide
  right_inv := by decide

/-- The least-significant-first flat code of an output string. -/
def queryIndex {L : ℕ} (w : OutStr L) : Fin (10 ^ L) :=
  Encoding.leafIndex (privateLeaf w)

/-- Decode a supplied finite query code with the existing executable digit enumeration. -/
def queryAt {L : ℕ} (q : Fin (10 ^ L)) : OutStr L :=
  fun i => outputDigits ((finFunctionFinEquiv.symm q) i)

/-- Encoding a decoded query returns the actual supplied code. -/
@[simp]
theorem queryIndex_queryAt {L : ℕ} (q : Fin (10 ^ L)) : queryIndex (queryAt q) = q := by
  change (finFunctionFinEquiv fun i =>
    outputDigits.symm (outputDigits (finFunctionFinEquiv.symm q i))) = q
  simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]

/-- Decoding a query's code returns every output coordinate unchanged. -/
@[simp]
theorem queryAt_queryIndex {L : ℕ} (w : OutStr L) : queryAt (queryIndex w) = w := by
  funext i
  change outputDigits ((finFunctionFinEquiv.symm
    (finFunctionFinEquiv fun j => outputDigits.symm (w j))) i) = w i
  simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]

/-- The requested output set is computed from the ordinary initialized list of query codes.
Repeated list entries are allowed and will be reported in their original order. -/
def requested {L : ℕ} (qs : List (Fin (10 ^ L))) : Finset (OutStr L) :=
  qs.toFinset.image queryAt

/-- The request set's numerical image is precisely the set of supplied numerical codes. -/
theorem image_queryIndex_requested {L : ℕ} (qs : List (Fin (10 ^ L))) :
    (requested qs).image (fun w => (queryIndex w).val) = qs.toFinset.image Fin.val := by
  simp only [requested, Finset.image_image, Function.comp_def, queryIndex_queryAt]

/-- Every supplied list entry is one of the requested mathematical outputs. -/
theorem queryAt_mem_requested {L : ℕ} {qs : List (Fin (10 ^ L))} {q : Fin (10 ^ L)}
    (hq : q ∈ qs) : queryAt q ∈ requested qs :=
  Finset.mem_image.mpr ⟨q, List.mem_toFinset.mpr hq, rfl⟩

/-- A query's code is the leaf-array address of its private leaf. -/
theorem queryIndex_privateLeaf {L : ℕ} (w : OutStr L) :
    queryIndex w = Encoding.leafIndex (privateLeaf w) := rfl

/-- Every flat code denotes exactly one output string. -/
theorem queryIndex_bijective (L : ℕ) : Function.Bijective (queryIndex (L := L)) :=
  finFunctionFinEquiv.bijective.comp
    (Equiv.piCongrRight fun _ : Fin L => outputDigits.symm).bijective

/-- Replacing output strings by their numerical codes preserves a request-set cardinality. -/
theorem card_image_queryIndex {L : ℕ} (S : Finset (OutStr L)) :
    (S.image (fun w => (queryIndex w).val)).card = S.card :=
  Finset.card_image_of_injective S (fun _ _ he =>
    (queryIndex_bijective L).injective (Fin.ext he))

/-- The first query digit is its output-variable digit; the suffix is shifted by one place. -/
theorem queryIndex_cons {L : ℕ} (z : OutVar) (w : OutStr L) :
    (queryIndex (Fin.cons z w) : ℕ) = (outputDigits.symm z).val + 10 * (queryIndex w).val := by
  simp only [queryIndex, Encoding.leafIndex, privateLeaf, finFunctionFinEquiv_apply,
    Fin.sum_univ_succ, Fin.cons_zero,
    Fin.cons_succ, Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Taking the first numerical digit recovers the first output variable. -/
theorem queryIndex_mod {L : ℕ} (w : OutStr (L + 1)) :
    (queryIndex w).val % 10 = (outputDigits.symm (w 0)).val := by
  have he := queryIndex_cons (w 0) (Fin.tail w)
  rw [Fin.cons_self_tail] at he
  rw [he]
  have h := (outputDigits.symm (w 0)).isLt
  omega

/-- Integer division discards the first output coordinate. -/
theorem queryIndex_div {L : ℕ} (w : OutStr (L + 1)) :
    (queryIndex w).val / 10 = (queryIndex (Fin.tail w)).val := by
  have he := queryIndex_cons (w 0) (Fin.tail w)
  rw [Fin.cons_self_tail] at he
  rw [he]
  have h := (outputDigits.symm (w 0)).isLt
  omega

/-- A term contributes to the inner digit or to its own outer digit. -/
theorem contributes_iff_digit (t : Fin 10) (z : OutVar) :
    (Encoding.termDigits t).Contributes z ↔
      (outputDigits.symm z).val = 9 ∨ (outputDigits.symm z).val = t.val := by
  decide +revert

/-- Numerical child requests are selected by the actual digit tests, then shortened by division.
The finite-set image removes repeated suffixes. Native code will implement that deduplication.
-/
def childCodes (S : Finset ℕ) (term : ℕ) : Finset ℕ :=
  (S.filter fun q => q % 10 = 9 ∨ q % 10 = term).image fun q => q / 10

/-- Child suffixes stay within the smaller numerical query space. -/
theorem childCodes_bounded {n : ℕ} {S : Finset ℕ} (term : ℕ)
    (hS : ∀ q ∈ S, q < 10 ^ (n + 1)) :
    ∀ q ∈ childCodes S term, q < 10 ^ n := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
  have h := hS p (Finset.mem_filter.mp hp).1
  apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 10)).mpr
  simpa only [pow_succ] using h

/-- The numerical child requests agree exactly with the existing finite pruning definition. -/
theorem mem_childCodes {L : ℕ} (S : Finset (OutStr (L + 1))) (t : Fin 10) (w : OutStr L) :
    (queryIndex w).val ∈ childCodes (S.image fun v => (queryIndex v).val) t.val ↔
      w ∈ childSet S (Encoding.termDigits t) := by
  constructor
  · intro h
    obtain ⟨q, hq, htail⟩ := Finset.mem_image.mp h
    obtain ⟨hparent, hmatch⟩ := Finset.mem_filter.mp hq
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hparent
    rw [queryIndex_div] at htail
    have htw : Fin.tail v = w := (queryIndex_bijective L).injective (Fin.ext htail)
    have hc : (Encoding.termDigits t).Contributes (v 0) := by
      rw [contributes_iff_digit]
      simpa only [queryIndex_mod] using hmatch
    rw [mem_childSet]
    exact ⟨v, hv, hc, htw⟩
  · intro h
    obtain ⟨v, hv, hc, htail⟩ := mem_childSet.mp h
    apply Finset.mem_image.mpr
    refine ⟨(queryIndex v).val, Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
    · rw [queryIndex_mod]
      exact (contributes_iff_digit t (v 0)).mp hc
    · rw [queryIndex_div, htail]

/-- The whole native child-set specification is the numerical image of the existing child set. -/
theorem childCodes_eq_image {L : ℕ} (S : Finset (OutStr (L + 1))) (t : Fin 10) :
    childCodes (S.image fun w => (queryIndex w).val) t.val =
      (childSet S (Encoding.termDigits t)).image (fun w => (queryIndex w).val) := by
  ext q
  constructor
  · intro hq
    have hbound := childCodes_bounded t.val (S := S.image fun w => (queryIndex w).val)
      (fun p hp => by
        obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hp
        exact (queryIndex v).isLt) q hq
    obtain ⟨w, hw⟩ := (queryIndex_bijective L).surjective ⟨q, hbound⟩
    have he : (queryIndex w).val = q := congrArg Fin.val hw
    exact Finset.mem_image.mpr ⟨w, (mem_childCodes S t w).mp (he.symm ▸ hq), he⟩
  · intro hq
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
    exact (mem_childCodes S t w).mpr hw

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
