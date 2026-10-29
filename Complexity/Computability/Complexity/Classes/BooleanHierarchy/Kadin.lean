/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.BooleanHierarchy.PH
public import Complexity.Computability.Complexity.Classes.PH.Collapse
public import Complexity.Computability.Complexity.Problems.SATUNSAT
import Complexity.Computability.Complexity.Classes.NP.Witness
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Kadin's Theorem

If the Boolean hierarchy over `NP` collapses at any finite level `k` (`coBH k ⊆ BH k`, or
equivalently `BH (k + 1) = BH k`), then the polynomial hierarchy collapses to its third level
`Σ₃ᴾ ∩ Π₃ᴾ` (`PH = Σ₃ᴾ`) [Kadin][Kadin1988]. In particular, if `DP = coDP` (or `SATUNSAT ∈ coDP`),
then `PH = Σ₃ᴾ`.

## Proof overview

To place a language `A ∈ Π₃ᴾ` in `Σ₃ᴾ`, peel off its first two quantifier blocks of lengths `p₁`
and `p₂`; the negated inner quantifier defines a language `E ∈ NP (encPair enc encBits)` such that
`a ∈ A ↔ ∀ u₁ (|u₁| = p₁(n)), ∃ u₂ (|u₂| = p₂(n)), (a, u₁ ++ u₂) ∉ E`, where every queried word
`u₁ ++ u₂` has fixed length `m(n) = (p₁ + p₂)(n)`.

For each `r ≤ k`, an `r`-tuple of words of length `m(n)` is represented as a single concatenated
bit string `s` of length `r * m(n)` paired with `a` under `encPair enc encBits`. The canonical
alternating languages `kadinChain enc m E r ∈ BH (encPair enc encBits) r` satisfy
`(a, s ++ y) ∈ kadinChain enc m E (r + 1) ↔ (a, y) ∈ E ∧ (a, s) ∉ kadinChain enc m E r` whenever
`|s| = r * m(n)`. Assuming `coBH (encPair enc encBits) k ⊆ BH (encPair enc encBits) k`, the
complement `(kadinChain enc m E k)ᶜ` lies in `BH (encPair enc encBits) k`. Stepping down the nested
difference representation of `(kadinChain enc m E k)ᶜ` from `r = k` to `r = 0` yields at each level
either a hard prefix `s` of length `r * m(n)` that reduces `(a, y) ∉ E` on words of length `m(n)`
to an existential check over `NP`, or completeness for the next level down. Taking the union of
these `k` hard-prefix branches places `A` in `Σ₃ᴾ`.

## Main definitions

* `Cslib.Complexity.kadinChain`: the canonical `BH r` language on concatenated `r`-tuples of fixed
  polynomial word length.
* `Cslib.Complexity.allWordsIn`: the `NP` language checking that `d` concatenated words of fixed
  polynomial length all belong to a given language.

## Main results

* `Cslib.Complexity.exists_mem_BH_encBits_and_polyTimeReducible`: every language in `BH enc r`
  polynomial-time many-one reduces to a language in `BH encBits r`.
* `Cslib.Complexity.coBH_subset_BH_of_coBH_encBits_subset_BH_encBits` and
  `Cslib.Complexity.BH_succ_eq_of_BH_encBits_succ_eq`: Boolean-hierarchy collapse on the canonical
  bit-string encoding `encBits` transfers to every instance encoding `enc`.
* `Cslib.Complexity.PiP_three_subset_SigmaP_three_of_coBH_subset_BH`:
  `coBH (encPair enc encBits) k ⊆ BH (encPair enc encBits) k → PiP 3 enc ⊆ SigmaP 3 enc`.
* `Cslib.Complexity.SigmaP_three_eq_PiP_three_of_coBH_subset_BH`:
  `coBH (encPair enc encBits) k ⊆ BH (encPair enc encBits) k → SigmaP 3 enc = PiP 3 enc`.
* `Cslib.Complexity.PH_eq_SigmaP_three_of_coBH_subset_BH`: Kadin's theorem for
  `coBH encBits k ⊆ BH encBits k`.
* `Cslib.Complexity.PH_eq_SigmaP_three_of_BH_succ_eq`: Kadin's theorem for
  `BH encBits (k + 1) = BH encBits k`.
* `Cslib.Complexity.PH_eq_SigmaP_three_of_DP_eq_coDP`: Kadin's theorem for
  `DP encBits = coDP encBits`.
* `Cslib.Complexity.DPComplete.PH_eq_SigmaP_three_of_mem_coDP` and
  `Cslib.Complexity.PH_eq_SigmaP_three_of_SATUNSAT_mem_coDP`: collapse from a single `DP`-complete
  language in `coDP`.

## References

* [J. Kadin, *The Polynomial Time Hierarchy Collapses if the Boolean Hierarchy
  Collapses*][Kadin1988]
* [J.-Y. Cai et al., *The Boolean Hierarchy I: Structural Properties*][CaiEtAl1988]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime Polynomial

variable {α β : Type} {enc : α ↪ List Bool}

/-! ### Alternating verifiers on fixed-length bit-string slices -/

/-- The encoded length of `(a, s)` under `encPair enc encBits` when `s` has length `q |enc a|`. -/
private noncomputable def pairPoly (q : Polynomial ℕ) : Polynomial ℕ := 2 * X + 1 + q

private theorem length_encPair_eq_eval_pairPoly {q : Polynomial ℕ} {a : α} {s : List Bool}
    (hs : s.length = q.eval (enc a).length) :
    (encPair enc encBits (a, s)).length = (pairPoly q).eval (enc a).length := by
  simp [pairPoly, hs]

/-- Shift the first `p |enc a|` certificate bits from the quantifier stream onto the accumulated
bit-string prefix `s`. -/
private def shiftVerifier (enc : α ↪ List Bool) (p : Polynomial ℕ)
    (V : (α × List Bool) × List Bool → Bool) (x : (α × List Bool) × List Bool) : Bool :=
  let n := p.eval (enc x.1.1).length
  V ((x.1.1, x.1.2 ++ x.2.take n), x.2.drop n)

@[simp]
private theorem shiftVerifier_append {p : Polynomial ℕ} {V : (α × List Bool) × List Bool → Bool}
    {a : α} {s u v : List Bool} (hu : u.length = p.eval (enc a).length) :
    shiftVerifier enc p V ((a, s), u ++ v) = V ((a, s ++ u), v) := by
  simp [shiftVerifier, ← hu]

private theorem computableInPolyTime_shiftVerifier (p : Polynomial ℕ)
    {V : (α × List Bool) × List Bool → Bool}
    (hV : ComputableInPolyTime V (encPair (encPair enc encBits) encBits) encBool) :
    ComputableInPolyTime (shiftVerifier enc p V)
      (encPair (encPair enc encBits) encBits) encBool := by
  have hn : ComputableInPolyTime
      (fun x : (α × List Bool) × List Bool => p.eval (enc x.1.1).length)
      (encPair (encPair enc encBits) encBits) encUnary :=
    (unary_eval p).comp ((encoding_length enc).comp (fst _ _).fst')
  exact hV.comp (((fst _ _).fst'.prod
    (bitsAppend (fst _ _).snd' (bitsTakeWithInput (snd _ _) hn))).prod
    (bitsDropWithInput (snd _ _) hn))

/-- `R : α → List Bool → Prop` is verified at `(b, k)` on prefixes `s` of length `q |enc a|` by a
polynomial-time alternating verifier whose certificate block lengths are polynomials in
`|enc a|`. -/
private def OnSliceAlt (enc : α ↪ List Bool) (b : Bool) (k : ℕ) (q : Polynomial ℕ)
    (R : α → List Bool → Prop) : Prop :=
  ∃ (ps : List (Polynomial ℕ)) (V : (α × List Bool) × List Bool → Bool),
    ps.length = k ∧
    ComputableInPolyTime V (encPair (encPair enc encBits) encBits) encBool ∧
    ∀ a : α, ∀ s : List Bool, s.length = q.eval (enc a).length →
      (R a s ↔ Alternation b (ps.map fun p => p.eval (enc a).length) fun v => V ((a, s), v) = true)

namespace OnSliceAlt

variable {b : Bool} {k : ℕ} {p q : Polynomial ℕ} {R R₁ R₂ : α → List Bool → Prop}

private theorem congr (h : OnSliceAlt enc b k q R₁)
    (hR : ∀ a s, s.length = q.eval (enc a).length → (R₁ a s ↔ R₂ a s)) :
    OnSliceAlt enc b k q R₂ := by
  obtain ⟨ps, V, hk, hV, hA⟩ := h
  exact ⟨ps, V, hk, hV, fun a s hs => (hR a s hs).symm.trans (hA a s hs)⟩

private theorem congr_poly (h : OnSliceAlt enc b k q R) {q' : Polynomial ℕ}
    (hq : ∀ n, q.eval n = q'.eval n) :
    OnSliceAlt enc b k q' R := by
  obtain ⟨ps, V, hk, hV, hA⟩ := h
  exact ⟨ps, V, hk, hV, fun a s hs => hA a s (hs.trans (hq _).symm)⟩

/-- At slice length `0`, an existential `OnSliceAlt` relation defines a `SigmaP k` language on
`α`. -/
private theorem mem_SigmaP (h : OnSliceAlt enc true k 0 R) : {a | R a []} ∈ SigmaP k enc := by
  obtain ⟨ps, V, hk, hV, hR⟩ := h
  refine Complexity.mem_SigmaP.mpr ⟨ps, fun x => V ((x.1, []), x.2), hk, ?_, fun a => ?_⟩
  · exact hV.comp (((fst enc encBits).prod (.const [])).prod (snd enc encBits))
  · exact hR a [] (by simp)

/-- Negating the verifier swaps quantifier polarities. -/
private theorem not (h : OnSliceAlt enc b k q R) : OnSliceAlt enc (!b) k q (fun a s => ¬R a s) := by
  obtain ⟨ps, V, hk, hV, hR⟩ := h
  refine ⟨ps, fun x => !V x, hk, by fun_prop, fun a s hs => ?_⟩
  dsimp only
  rw [hR a s hs, not_alternation]
  exact alternation_congr fun v => by simp

/-- Prepending a length-zero block flips the leading quantifier polarity and increments the
level. -/
private theorem zero_cons (h : OnSliceAlt enc b k q R) : OnSliceAlt enc (!b) (k + 1) q R := by
  obtain ⟨ps, V, hk, hV, hR⟩ := h
  refine ⟨0 :: ps, V, by simp [hk], hV, fun a s hs => ?_⟩
  rw [hR a s hs, List.map_cons, Polynomial.eval_zero, alternation_zero_cons, Bool.not_not]

/-- Appending a length-zero block increments the level without changing the leading polarity. -/
private theorem append_zero (h : OnSliceAlt enc b k q R) : OnSliceAlt enc b (k + 1) q R := by
  obtain ⟨ps, V, hk, hV, hR⟩ := h
  refine ⟨ps ++ [0], V, by simp [hk], hV, fun a s hs => ?_⟩
  rw [hR a s hs, List.map_append, List.map_singleton, Polynomial.eval_zero, alternation_append_zero]

/-- Conjoining two `OnSliceAlt` relations at the same polarity and level. -/
private theorem and (h₁ : OnSliceAlt enc b k q R₁) (h₂ : OnSliceAlt enc b k q R₂) :
    OnSliceAlt enc b k q (fun a s => R₁ a s ∧ R₂ a s) := by
  obtain ⟨ps, V, hp, hV, hR₁⟩ := h₁
  obtain ⟨qs, W, hq, hW, hR₂⟩ := h₂
  have hlen : ps.length = qs.length := hp.trans hq.symm
  let pqs := ps.zip qs
  refine ⟨pqs.map fun pq => pq.1 + pq.2,
    fun x =>
      let w := splitAlternatingBlocks
        (pqs.map fun pq => (pq.1.eval (enc x.1.1).length, pq.2.eval (enc x.1.1).length)) x.2
      V (x.1, w.1) && W (x.1, w.2),
    by simp [pqs, hp, hq], ?_, fun a s hs => ?_⟩
  · have hn : ComputableInPolyTime
        (fun x : (α × List Bool) × List Bool => (enc x.1.1).length)
        (encPair (encPair enc encBits) encBits) encUnary :=
      (encoding_length enc).comp (fst _ _).fst'
    have hs := computableInPolyTime_splitAlternatingBlocks pqs hn (.snd _ _)
    have h := bool_and.comp ((hV.comp ((fst _ _).prod hs.fst')).prod
      (hW.comp ((fst _ _).prod hs.snd')))
    exact h
  · dsimp only
    rw [hR₁ a s hs, hR₂ a s hs]
    have hfst : pqs.map Prod.fst = ps := List.map_fst_zip hlen.le
    have hsnd : pqs.map Prod.snd = qs := List.map_snd_zip hlen.ge
    rw [← hfst, ← hsnd]
    simp only [List.map_map, Function.comp_def, Polynomial.eval_add, Bool.and_eq_true]
    simpa only [List.map_map, Function.comp_def] using (alternation_splitAlternatingBlocks
      (pqs.map fun pq => (pq.1.eval (enc a).length, pq.2.eval (enc a).length)) b
      (fun v => V ((a, s), v) = true) (fun v => W ((a, s), v) = true)).symm

/-- Disjoining two `OnSliceAlt` relations at the same polarity and level. -/
private theorem or (h₁ : OnSliceAlt enc b k q R₁) (h₂ : OnSliceAlt enc b k q R₂) :
    OnSliceAlt enc b k q (fun a s => R₁ a s ∨ R₂ a s) := by
  have h : OnSliceAlt enc (!!b) k q (fun a s => ¬(¬R₁ a s ∧ ¬R₂ a s)) := (h₁.not.and h₂.not).not
  rw [Bool.not_not] at h
  exact h.congr fun a s _ => by tauto

/-- Implication from a negated `OnSliceAlt` relation to a positive one at the same polarity. -/
private theorem imp (h₁ : OnSliceAlt enc (!b) k q R₁) (h₂ : OnSliceAlt enc b k q R₂) :
    OnSliceAlt enc b k q (fun a s => R₁ a s → R₂ a s) := by
  have h₁' : OnSliceAlt enc b k q (fun a s => ¬R₁ a s) := by
    simpa using h₁.not
  refine (h₁'.or h₂).congr fun a s _ => ?_
  tauto

/-- Embed a `SigmaP k (encPair enc encBits)` language at any slice polynomial `q`. -/
private theorem of_mem_SigmaP {C : Set (α × List Bool)} (hC : C ∈ SigmaP k (encPair enc encBits))
    (q : Polynomial ℕ) :
    OnSliceAlt enc true k q (fun a s => (a, s) ∈ C) := by
  obtain ⟨ps, V, hk, hV, hA⟩ := hC
  refine ⟨ps.map fun p => p.comp (pairPoly q), V, by simp [hk], hV, fun a s hs => ?_⟩
  dsimp only
  rw [hA (a, s), length_encPair_eq_eval_pairPoly hs]
  simp [List.map_map, Function.comp_def, Polynomial.eval_comp]

/-- Embed a `PiP k (encPair enc encBits)` language at any slice polynomial `q`. -/
private theorem of_mem_PiP {C : Set (α × List Bool)} (hC : C ∈ PiP k (encPair enc encBits))
    (q : Polynomial ℕ) :
    OnSliceAlt enc false k q (fun a s => (a, s) ∈ C) := by
  obtain ⟨ps, V, hk, hV, hA⟩ := hC
  refine ⟨ps.map fun p => p.comp (pairPoly q), V, by simp [hk], hV, fun a s hs => ?_⟩
  dsimp only
  rw [hA (a, s), length_encPair_eq_eval_pairPoly hs]
  simp [List.map_map, Function.comp_def, Polynomial.eval_comp]

/-- Drop the first `p |enc a|` bits of the slice prefix before evaluating `R`. -/
private theorem drop (p : Polynomial ℕ) (h : OnSliceAlt enc b k q R) :
    OnSliceAlt enc b k (p + q) (fun a s => R a (s.drop (p.eval (enc a).length))) := by
  obtain ⟨ps, V, hk, hV, hR⟩ := h
  refine ⟨ps, fun x => V ((x.1.1, x.1.2.drop (p.eval (enc x.1.1).length)), x.2), hk, ?_,
    fun a s hs => ?_⟩
  · have hn : ComputableInPolyTime
        (fun x : (α × List Bool) × List Bool => p.eval (enc x.1.1).length)
        (encPair (encPair enc encBits) encBits) encUnary :=
      (unary_eval p).comp ((encoding_length enc).comp (fst _ _).fst')
    exact hV.comp (((fst _ _).fst'.prod
      (bitsDropWithInput (fst _ _).snd' hn)).prod (snd _ _))
  · refine hR a (s.drop (p.eval (enc a).length)) ?_
    simp [hs]

/-- Prepend an existential quantifier over words of length `p |enc a|` to a universal relation. -/
private theorem exists_append_flip (p : Polynomial ℕ) (h : OnSliceAlt enc false k (q + p) R) :
    OnSliceAlt enc true (k + 1) q
      (fun a s => ∃ u : List Bool, u.length = p.eval (enc a).length ∧ R a (s ++ u)) := by
  obtain ⟨ps, V, hk, hV, hR⟩ := h
  refine ⟨p :: ps, shiftVerifier enc p V, by simp [hk],
    computableInPolyTime_shiftVerifier p hV, fun a s hs => ?_⟩
  simp only [List.map_cons, alternation_true_cons]
  refine exists_congr fun u => and_congr_right fun hu => ?_
  have hsu : (s ++ u).length = (q + p).eval (enc a).length := by
    simp [hs, hu]
  rw [hR a (s ++ u) hsu]
  exact alternation_congr fun v => by rw [shiftVerifier_append hu]

/-- Prepend a universal quantifier over words of length `p |enc a|` to an existential relation. -/
private theorem forall_append_flip (p : Polynomial ℕ) (h : OnSliceAlt enc true k (q + p) R) :
    OnSliceAlt enc false (k + 1) q
      (fun a s => ∀ u : List Bool, u.length = p.eval (enc a).length → R a (s ++ u)) := by
  obtain ⟨ps, V, hk, hV, hR⟩ := h
  refine ⟨p :: ps, shiftVerifier enc p V, by simp [hk],
    computableInPolyTime_shiftVerifier p hV, fun a s hs => ?_⟩
  simp only [List.map_cons, alternation_false_cons]
  refine forall_congr' fun u => imp_congr_right fun hu => ?_
  have hsu : (s ++ u).length = (q + p).eval (enc a).length := by
    simp [hs, hu]
  rw [hR a (s ++ u) hsu]
  exact alternation_congr fun v => by rw [shiftVerifier_append hu]

/-- Merge an existential quantifier over words of length `p |enc a|` into the leading existential
block. -/
private theorem exists_append_same (p : Polynomial ℕ) (h : OnSliceAlt enc true (k + 1) (q + p) R) :
    OnSliceAlt enc true (k + 1) q
      (fun a s => ∃ u : List Bool, u.length = p.eval (enc a).length ∧ R a (s ++ u)) := by
  obtain ⟨ps, V, hk, hV, hR⟩ := h
  rcases ps with _ | ⟨p₁, ps⟩
  · cases hk
  refine ⟨(p + p₁) :: ps, shiftVerifier enc p V, by simpa using hk,
    computableInPolyTime_shiftVerifier p hV, fun a s hs => ?_⟩
  simp only [List.map_cons, Polynomial.eval_add, alternation_true_cons]
  constructor
  · rintro ⟨u, hu, hRu⟩
    have hsu : (s ++ u).length = (q + p).eval (enc a).length := by simp [hs, hu]
    obtain ⟨w₁, hw₁, hA⟩ := (hR a (s ++ u) hsu).1 hRu
    refine ⟨u ++ w₁, by simp [hu, hw₁], ?_⟩
    refine hA.mono fun v hv => ?_
    simpa only [List.append_assoc, shiftVerifier_append hu] using hv
  · rintro ⟨w, hw, hA⟩
    let n := p.eval (enc a).length
    have hu : (w.take n).length = n := by simp [n, hw]
    have hw₁ : (w.drop n).length = p₁.eval (enc a).length := by simp [n, hw]
    have hsu : (s ++ w.take n).length = (q + p).eval (enc a).length := by simp [hs, hu, n]
    refine ⟨w.take n, hu, (hR a (s ++ w.take n) hsu).2 ⟨w.drop n, hw₁, ?_⟩⟩
    refine hA.mono fun v hv => ?_
    have htake : (w.take n ++ (w.drop n ++ v)) = w ++ v := by
      rw [← List.append_assoc, List.take_append_drop]
    rw [← htake, shiftVerifier_append hu] at hv
    exact hv

/-- Merge a universal quantifier over words of length `p |enc a|` into the leading universal
block. -/
private theorem forall_append_same (p : Polynomial ℕ) (h : OnSliceAlt enc false (k + 1) (q + p) R) :
    OnSliceAlt enc false (k + 1) q
      (fun a s => ∀ u : List Bool, u.length = p.eval (enc a).length → R a (s ++ u)) := by
  have hnot : OnSliceAlt enc (!!false) (k + 1) q
      (fun a s => ¬∃ u : List Bool, u.length = p.eval (enc a).length ∧ ¬R a (s ++ u)) :=
    (h.not.exists_append_same p).not
  exact hnot.congr fun a s _ => by simp

end OnSliceAlt

/-! ### Kadin's alternating tuple chain and word-tuple predicates -/

/-- The canonical `BH r` language on concatenated `r`-tuples of words of length `m |enc a|`:
`(a, s ++ y)` belongs to `kadinChain enc m E (r + 1)` when `(a, y) ∈ E` and
`(a, s) ∉ kadinChain enc m E r`. -/
def kadinChain (enc : α ↪ List Bool) (m : Polynomial ℕ) (E : Set (α × List Bool)) :
    ℕ → Set (α × List Bool)
  | 0 => ∅
  | r + 1 =>
    {x : α × List Bool | (x.1, x.2.drop ((r • m).eval (enc x.1).length)) ∈ E} \
      {x : α × List Bool | (x.1, x.2.take ((r • m).eval (enc x.1).length)) ∈ kadinChain enc m E r}

@[simp]
theorem kadinChain_zero (m : Polynomial ℕ) (E : Set (α × List Bool)) :
    kadinChain enc m E 0 = ∅ := rfl

theorem mem_kadinChain_succ_append {m : Polynomial ℕ} {E : Set (α × List Bool)} {r : ℕ}
    {a : α} {s y : List Bool} (hs : s.length = (r • m).eval (enc a).length) :
    (a, s ++ y) ∈ kadinChain enc m E (r + 1) ↔
      (a, y) ∈ E ∧ (a, s) ∉ kadinChain enc m E r := by
  have hs' : s.length = r * m.eval (enc a).length := by simpa using hs
  simp [kadinChain, ← hs']

theorem kadinChain_mem_BH {m : Polynomial ℕ} {E : Set (α × List Bool)}
    (hE : E ∈ NP (encPair enc encBits)) (r : ℕ) :
    kadinChain enc m E r ∈ BH (encPair enc encBits) r := by
  induction r with
  | zero => simp [kadinChain]
  | succ r ih =>
    have hn : ComputableInPolyTime
        (fun x : α × List Bool => (r • m).eval (enc x.1).length)
        (encPair enc encBits) encUnary :=
      (unary_eval (r • m)).comp ((encoding_length enc).comp (fst _ _))
    have hdrop : PolyTimeReducible (encPair enc encBits) (encPair enc encBits)
        {x : α × List Bool | (x.1, x.2.drop ((r • m).eval (enc x.1).length)) ∈ E} E :=
      ⟨fun x => (x.1, x.2.drop ((r • m).eval (enc x.1).length)),
        (fst _ _).prod (bitsDropWithInput (snd _ _) hn), fun _ => Iff.rfl⟩
    have htake : PolyTimeReducible (encPair enc encBits) (encPair enc encBits)
        {x : α × List Bool |
          (x.1, x.2.take ((r • m).eval (enc x.1).length)) ∈ kadinChain enc m E r}
        (kadinChain enc m E r) :=
      ⟨fun x => (x.1, x.2.take ((r • m).eval (enc x.1).length)),
        (fst _ _).prod (bitsTakeWithInput (snd _ _) hn), fun _ => Iff.rfl⟩
    exact ⟨_, hdrop.mem_NP hE, _, htake.mem_BH ih, rfl⟩

/-- The `NP` language checking that each of the first `d` consecutive blocks of length `m |enc a|`
in `z` belongs to `E`. -/
def allWordsIn (enc : α ↪ List Bool) (m : Polynomial ℕ) (E : Set (α × List Bool)) :
    ℕ → Set (α × List Bool)
  | 0 => Set.univ
  | d + 1 =>
    {x : α × List Bool | (x.1, x.2.take (m.eval (enc x.1).length)) ∈ E} ∩
      {x : α × List Bool | (x.1, x.2.drop (m.eval (enc x.1).length)) ∈ allWordsIn enc m E d}

@[simp]
theorem allWordsIn_zero (m : Polynomial ℕ) (E : Set (α × List Bool)) :
    allWordsIn enc m E 0 = Set.univ := rfl

theorem mem_allWordsIn_succ_append {m : Polynomial ℕ} {E : Set (α × List Bool)} {d : ℕ}
    {a : α} {y z : List Bool} (hy : y.length = m.eval (enc a).length) :
    (a, y ++ z) ∈ allWordsIn enc m E (d + 1) ↔
      (a, y) ∈ E ∧ (a, z) ∈ allWordsIn enc m E d := by
  simp [allWordsIn, ← hy]

theorem allWordsIn_mem_NP {m : Polynomial ℕ} {E : Set (α × List Bool)}
    (hE : E ∈ NP (encPair enc encBits)) (d : ℕ) :
    allWordsIn enc m E d ∈ NP (encPair enc encBits) := by
  induction d with
  | zero => exact ⟨0, fun _ => true, .const _, by simp [IsVerifier]⟩
  | succ d ih =>
    have hn : ComputableInPolyTime
        (fun x : α × List Bool => m.eval (enc x.1).length)
        (encPair enc encBits) encUnary :=
      (unary_eval m).comp ((encoding_length enc).comp (fst _ _))
    have htake : PolyTimeReducible (encPair enc encBits) (encPair enc encBits)
        {x : α × List Bool | (x.1, x.2.take (m.eval (enc x.1).length)) ∈ E} E :=
      ⟨fun x => (x.1, x.2.take (m.eval (enc x.1).length)),
        (fst _ _).prod (bitsTakeWithInput (snd _ _) hn), fun _ => Iff.rfl⟩
    have hdrop : PolyTimeReducible (encPair enc encBits) (encPair enc encBits)
        {x : α × List Bool | (x.1, x.2.drop (m.eval (enc x.1).length)) ∈ allWordsIn enc m E d}
        (allWordsIn enc m E d) :=
      ⟨fun x => (x.1, x.2.drop (m.eval (enc x.1).length)),
        (fst _ _).prod (bitsDropWithInput (snd _ _) hn), fun _ => Iff.rfl⟩
    exact inter_mem_NP (htake.mem_NP hE) (hdrop.mem_NP ih)

/-- Unpack a `BH (r + 1)` language `D ⊆ U` (where `U ∈ NP`) into `D = B \ D₁` with
`D₁ ⊆ B ⊆ U`, so that `D₁ = B \ D ⊆ U \ D`. -/
private theorem mem_BH_succ_subset {γ : Type} {encγ : γ ↪ List Bool} {r : ℕ}
    {U D : Set γ} (hU : U ∈ NP encγ) (hD : D ∈ BH encγ (r + 1)) (hDU : D ⊆ U) :
    ∃ B ∈ NP encγ, ∃ D₁ ∈ BH encγ r,
      B ⊆ U ∧ D₁ ⊆ B ∧ D = B \ D₁ ∧ D₁ ⊆ U \ D := by
  obtain ⟨B', hB', D', hD', rfl⟩ := hD
  refine ⟨B' ∩ U, inter_mem_NP hB' hU, D' ∩ (B' ∩ U),
    inter_mem_BH_of_mem_NP hD' (inter_mem_NP hB' hU),
    Set.inter_subset_right, Set.inter_subset_right, ?_, ?_⟩
  · ext x
    have hxU : x ∈ B' \ D' → x ∈ U := fun h => hDU h
    simp only [Set.mem_sdiff, Set.mem_inter_iff] at hxU ⊢
    tauto
  · intro x hx
    simp only [Set.mem_inter_iff, Set.mem_sdiff] at hx ⊢
    tauto

/-! ### Hard-prefix branch at level `r` -/

/-- A prefix `s` of `r` words of length `m |enc a|` is `r`-hard for `D₁` on instance `a` if
`(a, s) ∉ kadinChain enc m E r` and no extension by `y` (of length `m |enc a|`) and `z` (of `d`
words in `E` of length `m |enc a|`) places `(a, s ++ y ++ z)` in `D₁`. -/
private def kadinIsHard (enc : α ↪ List Bool) (m : Polynomial ℕ) (E : Set (α × List Bool))
    (r d : ℕ) (D₁ : Set (α × List Bool)) (a : α) (s : List Bool) : Prop :=
  (a, s) ∉ kadinChain enc m E r ∧
    ∀ w : List Bool, w.length = ((1 + d) • m).eval (enc a).length →
      (a, w.drop (m.eval (enc a).length)) ∈ allWordsIn enc m E d →
      (a, s ++ w) ∉ D₁

/-- Given a hard prefix `s`, the main `Π₂` check for `a ∈ A`: for every `u₁` of length `p₁ |enc a|`,
there exist `u₂` of length `p₂ |enc a|` and `z` of `d` words in `E` (packed as `w = u₂ ++ z` of
length `(p₂ + d • m) |enc a|`) such that `(a, s ++ u₁ ++ w) ∈ B`. -/
private def kadinMain (enc : α ↪ List Bool) (p₁ p₂ m : Polynomial ℕ) (E : Set (α × List Bool))
    (d : ℕ) (B : Set (α × List Bool)) (a : α) (s : List Bool) : Prop :=
  ∀ u₁ : List Bool, u₁.length = p₁.eval (enc a).length →
    ∃ w : List Bool, w.length = (p₂ + d • m).eval (enc a).length ∧
      (a, w.drop (p₂.eval (enc a).length)) ∈ allWordsIn enc m E d ∧
      (a, s ++ u₁ ++ w) ∈ B

/-- The level-`r` hard-prefix branch of Kadin's `Σ₃ᴾ` simulation. -/
private def kadinHardBranch (enc : α ↪ List Bool) (p₁ p₂ m : Polynomial ℕ) (E : Set (α × List Bool))
    (r d : ℕ) (D₁ B : Set (α × List Bool)) : Set α :=
  {a | ∃ s : List Bool, s.length = (r • m).eval (enc a).length ∧
    kadinIsHard enc m E r d D₁ a s ∧
    kadinMain enc p₁ p₂ m E d B a s}

/-- `kadinIsHard` is an `OnSliceAlt enc false 2 (r • m)` slice predicate. -/
private theorem onSliceAlt_kadinIsHard {m : Polynomial ℕ} {E : Set (α × List Bool)}
    (hE : E ∈ NP (encPair enc encBits)) (r d : ℕ) {D₁ : Set (α × List Bool)}
    (hD₁ : D₁ ∈ BH (encPair enc encBits) r) :
    OnSliceAlt enc false 2 (r • m) (kadinIsHard enc m E r d D₁) := by
  -- `kadinIsHard` is `OnSliceAlt enc false 2 (r • m)`
  have hLr_compl : (kadinChain enc m E r)ᶜ ∈ PiP 2 (encPair enc encBits) :=
    (BooleanHierarchy_subset_SigmaP_two_inter_PiP_two
      (compl_mem_BooleanHierarchy
        (BH_subset_BooleanHierarchy r (kadinChain_mem_BH hE r)))).2
  have hD₁_compl : D₁ᶜ ∈ PiP 2 (encPair enc encBits) :=
    (BooleanHierarchy_subset_SigmaP_two_inter_PiP_two
      (compl_mem_BooleanHierarchy (BH_subset_BooleanHierarchy r hD₁))).2
  have hAll : allWordsIn enc m E d ∈ SigmaP 1 (encPair enc encBits) :=
    SigmaP_one (enc := encPair enc encBits) ▸ allWordsIn_mem_NP hE d
  have hHard1 : OnSliceAlt enc false 2 (r • m) (fun a s => (a, s) ∉ kadinChain enc m E r) :=
    OnSliceAlt.of_mem_PiP hLr_compl (r • m)
  have hAll_drop1 : OnSliceAlt enc true 2 ((r • m + m) + d • m)
      (fun a sw => (a, sw.drop ((r • m + m).eval (enc a).length)) ∈ allWordsIn enc m E d) :=
    ((OnSliceAlt.of_mem_SigmaP hAll (d • m)).append_zero).drop (r • m + m)
  have hAll_drop1' : OnSliceAlt enc (!false) 2 (r • m + (1 + d) • m)
      (fun a sw => (a, sw.drop ((r • m + m).eval (enc a).length)) ∈ allWordsIn enc m E d) :=
    hAll_drop1.congr_poly fun n => by simp [add_smul, one_smul, add_assoc]
  have hD₁_slice : OnSliceAlt enc false 2 (r • m + (1 + d) • m) (fun a sw => (a, sw) ∉ D₁) :=
    OnSliceAlt.of_mem_PiP hD₁_compl (r • m + (1 + d) • m)
  have hHard2 : OnSliceAlt enc false 2 (r • m)
      (fun a s => ∀ w : List Bool, w.length = ((1 + d) • m).eval (enc a).length →
        (a, w.drop (m.eval (enc a).length)) ∈ allWordsIn enc m E d →
        (a, s ++ w) ∉ D₁) := by
    refine ((hAll_drop1'.imp hD₁_slice).forall_append_same ((1 + d) • m)).congr fun a s hs => ?_
    refine forall_congr' fun w => imp_congr_right fun _ => ?_
    have hlen : (r • m + m).eval (enc a).length = s.length + m.eval (enc a).length := by
      rw [Polynomial.eval_add, hs]
    rw [hlen, ← List.drop_drop, List.drop_left]
  exact hHard1.and hHard2

/-- `kadinMain` is an `OnSliceAlt enc false 2 (r • m)` slice predicate. -/
private theorem onSliceAlt_kadinMain {p₁ p₂ m : Polynomial ℕ} {E : Set (α × List Bool)}
    (hE : E ∈ NP (encPair enc encBits)) (r d : ℕ) {B : Set (α × List Bool)}
    (hB : B ∈ NP (encPair enc encBits)) :
    OnSliceAlt enc false 2 (r • m) (kadinMain enc p₁ p₂ m E d B) := by
  -- `kadinMain` is `OnSliceAlt enc false 2 (r • m)`
  have hAll : allWordsIn enc m E d ∈ SigmaP 1 (encPair enc encBits) :=
    SigmaP_one (enc := encPair enc encBits) ▸ allWordsIn_mem_NP hE d
  have hB' : B ∈ SigmaP 1 (encPair enc encBits) :=
    SigmaP_one (enc := encPair enc encBits) ▸ hB
  have hAll_drop2 : OnSliceAlt enc true 1 ((r • m + p₁ + p₂) + d • m)
      (fun a suw =>
        (a, suw.drop ((r • m + p₁ + p₂).eval (enc a).length)) ∈ allWordsIn enc m E d) :=
    (OnSliceAlt.of_mem_SigmaP hAll (d • m)).drop (r • m + p₁ + p₂)
  have hAll_drop2' : OnSliceAlt enc true 1 ((r • m + p₁) + (p₂ + d • m))
      (fun a suw =>
        (a, suw.drop ((r • m + p₁ + p₂).eval (enc a).length)) ∈ allWordsIn enc m E d) :=
    hAll_drop2.congr_poly fun n => by simp [add_assoc]
  have hB_slice : OnSliceAlt enc true 1 ((r • m + p₁) + (p₂ + d • m))
      (fun a suw => (a, suw) ∈ B) :=
    OnSliceAlt.of_mem_SigmaP hB' ((r • m + p₁) + (p₂ + d • m))
  have hMain_exists : OnSliceAlt enc true 1 (r • m + p₁)
      (fun a su₁ => ∃ w : List Bool, w.length = (p₂ + d • m).eval (enc a).length ∧
        (a, (su₁ ++ w).drop ((r • m + p₁ + p₂).eval (enc a).length)) ∈ allWordsIn enc m E d ∧
        (a, su₁ ++ w) ∈ B) :=
    (hAll_drop2'.and hB_slice).exists_append_same (p₂ + d • m)
  refine (hMain_exists.forall_append_flip p₁).congr fun a s hs => ?_
  refine forall_congr' fun u₁ => imp_congr_right fun hu₁ => ?_
  refine exists_congr fun w => and_congr_right fun _ => ?_
  have hsu₁ : (r • m + p₁ + p₂).eval (enc a).length =
      (s ++ u₁).length + p₂.eval (enc a).length := by
    simp [hs, hu₁]
  rw [hsu₁, ← List.drop_drop, List.drop_left]

private theorem kadinHardBranch_mem_SigmaP_three {p₁ p₂ m : Polynomial ℕ}
    {E : Set (α × List Bool)} (hE : E ∈ NP (encPair enc encBits)) (r d : ℕ)
    {D₁ B : Set (α × List Bool)} (hD₁ : D₁ ∈ BH (encPair enc encBits) r)
    (hB : B ∈ NP (encPair enc encBits)) :
    kadinHardBranch enc p₁ p₂ m E r d D₁ B ∈ SigmaP 3 enc := by
  -- `kadinIsHard` is `OnSliceAlt enc false 2 (r • m)`
  have hIsHard := onSliceAlt_kadinIsHard (m := m) hE r d hD₁
  have hMain := onSliceAlt_kadinMain (p₁ := p₁) (p₂ := p₂) (m := m) hE r d hB
  -- Combine `kadinIsHard` and `kadinMain`, then existentially quantify over `s`
  have hBoth : OnSliceAlt enc false 2 (0 + r • m)
      (fun a s => kadinIsHard enc m E r d D₁ a s ∧ kadinMain enc p₁ p₂ m E d B a s) :=
    (hIsHard.and hMain).congr_poly fun n => by simp
  have hBranch : OnSliceAlt enc true 3 0
      (fun a s => ∃ u : List Bool, u.length = (r • m).eval (enc a).length ∧
        kadinIsHard enc m E r d D₁ a (s ++ u) ∧ kadinMain enc p₁ p₂ m E d B a (s ++ u)) :=
    hBoth.exists_append_flip (r • m)
  exact hBranch.mem_SigmaP

/-! ### Downward induction along the Boolean hierarchy -/

section KadinInduction

variable (enc) (p₁ p₂ m : Polynomial ℕ) (E : Set (α × List Bool))

private def kadinTarget : Set α :=
  {a | ∀ u₁ : List Bool, u₁.length = p₁.eval (enc a).length →
    ∃ u₂ : List Bool, u₂.length = p₂.eval (enc a).length ∧ (a, u₁ ++ u₂) ∉ E}

private def kadinSoundD (r d : ℕ) (D : Set (α × List Bool)) : Prop :=
  ∀ a : α, ∀ s z : List Bool,
    s.length = (r • m).eval (enc a).length →
    z.length = (d • m).eval (enc a).length →
    (a, z) ∈ allWordsIn enc m E d →
    (a, s ++ z) ∈ D →
    (a, s) ∉ kadinChain enc m E r

private def kadinSoundDiff (r d : ℕ) (U D : Set (α × List Bool)) : Prop :=
  ∀ a : α, ∀ s z : List Bool,
    s.length = (r • m).eval (enc a).length →
    z.length = (d • m).eval (enc a).length →
    (a, z) ∈ allWordsIn enc m E d →
    (a, s ++ z) ∈ U \ D →
    (a, s) ∈ kadinChain enc m E r

private def kadinComp (r d : ℕ) (D : Set (α × List Bool)) (a : α) : Prop :=
  ∀ s : List Bool,
    s.length = (r • m).eval (enc a).length →
    (a, s) ∉ kadinChain enc m E r →
    ∃ z : List Bool,
      z.length = (d • m).eval (enc a).length ∧
      (a, z) ∈ allWordsIn enc m E d ∧
      (a, s ++ z) ∈ D

/-- Strong soundness of `D₁`: `(a, s ++ (y ++ z)) ∈ D₁` implies
`(a, y) ∈ E ∧ (a, s) ∉ kadinChain enc m E r`. -/
private theorem kadinStrongSoundD₁ {r d : ℕ} {U D D₁ : Set (α × List Bool)}
    (hD₁UD : D₁ ⊆ U \ D) (hSoundDiff : kadinSoundDiff enc m E (r + 1) d U D)
    (a : α) (s y z : List Bool) (hs : s.length = (r • m).eval (enc a).length)
    (hy : y.length = m.eval (enc a).length) (hz : z.length = (d • m).eval (enc a).length)
    (hzE : (a, z) ∈ allWordsIn enc m E d) (hmem : (a, s ++ (y ++ z)) ∈ D₁) :
    (a, y) ∈ E ∧ (a, s) ∉ kadinChain enc m E r := by
  -- Strong soundness of `D₁`: `(a, s ++ y ++ z) ∈ D₁` implies `(a, y) ∈ E ∧ (a, s) ∉ L r`
  have hsy_len : (s ++ y).length = ((r + 1) • m).eval (enc a).length := by
    simp [hs, hy, add_smul, one_smul]
  have hmem' : (a, (s ++ y) ++ z) ∈ U \ D := by
    rw [List.append_assoc]
    exact hD₁UD hmem
  have hL : (a, s ++ y) ∈ kadinChain enc m E (r + 1) :=
    hSoundDiff a (s ++ y) z hsy_len hz hzE hmem'
  exact (mem_kadinChain_succ_append hs).1 hL

/-- `kadinSoundD` steps down from `(r + 1, d, U \ D)` to `(r, d + 1, D₁)`. -/
private theorem kadinSoundD_succ {r d : ℕ} {U D D₁ : Set (α × List Bool)}
    (hD₁UD : D₁ ⊆ U \ D) (hSoundDiff : kadinSoundDiff enc m E (r + 1) d U D) :
    kadinSoundD enc m E r (d + 1) D₁ := by
  intro a s w hs hw hwE hmem
  have hw' : w.length = m.eval (enc a).length + (d • m).eval (enc a).length := by
    simpa [add_smul, one_smul, Nat.add_comm] using hw
  let y := w.take (m.eval (enc a).length)
  let z := w.drop (m.eval (enc a).length)
  have hy : y.length = m.eval (enc a).length := by simp [y, hw']
  have hz : z.length = (d • m).eval (enc a).length := by simp [z, hw']
  have hsplit : y ++ z = w := List.take_append_drop _ _
  rw [← hsplit] at hwE hmem
  obtain ⟨_, hzE⟩ := (mem_allWordsIn_succ_append hy).1 hwE
  exact (kadinStrongSoundD₁ enc m E hD₁UD hSoundDiff a s y z hs hy hz hzE hmem).2

/-- `kadinSoundDiff` steps down from `(r + 1, d, D)` to `(r, d + 1, B, D₁)` when `D = B \ D₁`. -/
private theorem kadinSoundDiff_succ {r d : ℕ} {D B D₁ : Set (α × List Bool)}
    (hDB : D = B \ D₁) (hSoundD : kadinSoundD enc m E (r + 1) d D) :
    kadinSoundDiff enc m E r (d + 1) B D₁ := by
  intro a s w hs hw hwE hmem
  have hw' : w.length = m.eval (enc a).length + (d • m).eval (enc a).length := by
    simpa [add_smul, one_smul, Nat.add_comm] using hw
  let y := w.take (m.eval (enc a).length)
  let z := w.drop (m.eval (enc a).length)
  have hy : y.length = m.eval (enc a).length := by simp [y, hw']
  have hz : z.length = (d • m).eval (enc a).length := by simp [z, hw']
  have hsplit : y ++ z = w := List.take_append_drop _ _
  rw [← hsplit] at hwE hmem
  obtain ⟨hyE, hzE⟩ := (mem_allWordsIn_succ_append hy).1 hwE
  have hsy_len : (s ++ y).length = ((r + 1) • m).eval (enc a).length := by
    simp [hs, hy, add_smul, one_smul]
  have hmemD : (a, (s ++ y) ++ z) ∈ D := by
    rw [List.append_assoc, hDB]
    exact hmem
  have hnotL : (a, s ++ y) ∉ kadinChain enc m E (r + 1) :=
    hSoundD a (s ++ y) z hsy_len hz hzE hmemD
  rw [mem_kadinChain_succ_append hs, not_and, not_not] at hnotL
  exact hnotL hyE

/-- Soundness of the hard-prefix branch: every instance in `kadinHardBranch` is in
`kadinTarget`. -/
private theorem kadinHardBranch_subset_kadinTarget (hm : m = p₁ + p₂) {r d : ℕ}
    {D B D₁ : Set (α × List Bool)} (hDB : D = B \ D₁)
    (hSoundD : kadinSoundD enc m E (r + 1) d D) :
    kadinHardBranch enc p₁ p₂ m E r d D₁ B ⊆ kadinTarget enc p₁ p₂ E := by
  rintro a ⟨s, hs, ⟨hs_notL, hs_hard⟩, hmain⟩ u₁ hu₁
  obtain ⟨w, hw, hwE, hBw⟩ := hmain u₁ hu₁
  let u₂ := w.take (p₂.eval (enc a).length)
  let z := w.drop (p₂.eval (enc a).length)
  have hu₂ : u₂.length = p₂.eval (enc a).length := by simp [u₂, hw]
  have hz : z.length = (d • m).eval (enc a).length := by simp [z, hw]
  have hw_eq : u₂ ++ z = w := List.take_append_drop _ _
  let y := u₁ ++ u₂
  have hy : y.length = m.eval (enc a).length := by simp [y, hm, hu₁, hu₂]
  have hyz_len : (y ++ z).length = ((1 + d) • m).eval (enc a).length := by
    simp [hy, hz, add_smul, one_smul]
  have hyz_drop : (y ++ z).drop (m.eval (enc a).length) = z := by simp [← hy]
  have hnotD₁ : (a, s ++ (y ++ z)) ∉ D₁ := hs_hard (y ++ z) hyz_len (by rwa [hyz_drop])
  have hsuw_eq : s ++ u₁ ++ w = (s ++ y) ++ z := by simp [y, ← hw_eq, List.append_assoc]
  have hmemD : (a, (s ++ y) ++ z) ∈ D := by
    rw [hDB]
    exact ⟨by rwa [← hsuw_eq], by simpa [List.append_assoc] using hnotD₁⟩
  have hsy_len : (s ++ y).length = ((r + 1) • m).eval (enc a).length := by
    simp [hs, hy, add_smul, one_smul]
  have hnotL_succ : (a, s ++ y) ∉ kadinChain enc m E (r + 1) :=
    hSoundD a (s ++ y) z hsy_len hz hwE hmemD
  rw [mem_kadinChain_succ_append hs] at hnotL_succ
  exact ⟨u₂, hu₂, fun hyE => hnotL_succ ⟨hyE, hs_notL⟩⟩

/-- When no hard prefix exists at level `r`, `kadinComp` holds at `(r, d + 1, D₁)`. -/
private theorem kadinComp_of_not_exists_kadinIsHard {r d : ℕ} {U D D₁ : Set (α × List Bool)}
    (hD₁UD : D₁ ⊆ U \ D) (hSoundDiff : kadinSoundDiff enc m E (r + 1) d U D) {a : α}
    (hEx : ¬∃ s : List Bool, s.length = (r • m).eval (enc a).length ∧
      kadinIsHard enc m E r d D₁ a s) :
    kadinComp enc m E r (d + 1) D₁ a := by
  intro s hs hs_notL
  have hnotHard : ¬kadinIsHard enc m E r d D₁ a s := fun h => hEx ⟨s, hs, h⟩
  simp only [kadinIsHard, hs_notL, not_false_eq_true, true_and, not_forall, not_not] at hnotHard
  obtain ⟨w, hw, hwE, hmemD₁⟩ := hnotHard
  have hw' : w.length = m.eval (enc a).length + (d • m).eval (enc a).length := by
    simpa [add_smul, one_smul] using hw
  let y := w.take (m.eval (enc a).length)
  let z := w.drop (m.eval (enc a).length)
  have hy : y.length = m.eval (enc a).length := by simp [y, hw']
  have hz : z.length = (d • m).eval (enc a).length := by simp [z, hw']
  have hsplit : y ++ z = w := List.take_append_drop _ _
  rw [← hsplit] at hmemD₁
  have hyE : (a, y) ∈ E := (kadinStrongSoundD₁ enc m E hD₁UD hSoundDiff a s y z hs hy hz hwE
    hmemD₁).1
  refine ⟨w, by simpa [add_smul, one_smul, Nat.add_comm] using hw, ?_, by rwa [← hsplit]⟩
  rw [← hsplit, mem_allWordsIn_succ_append hy]
  exact ⟨hyE, hwE⟩

private theorem exists_kadin_sigmaP_three (hm : m = p₁ + p₂)
    (hE : E ∈ NP (encPair enc encBits)) :
    ∀ (r d : ℕ) {U D : Set (α × List Bool)},
      U ∈ NP (encPair enc encBits) →
      D ∈ BH (encPair enc encBits) r →
      D ⊆ U →
      kadinSoundD enc m E r d D →
      kadinSoundDiff enc m E r d U D →
      ∃ H ∈ SigmaP 3 enc,
        H ⊆ kadinTarget enc p₁ p₂ E ∧
        ∀ a ∈ kadinTarget enc p₁ p₂ E, kadinComp enc m E r d D a → a ∈ H
  | 0, d, U, D, _, hD, _, _, _ => by
    have hD0 : D = ∅ := hD
    subst hD0
    have hempty : (∅ : Set α) ∈ SigmaP 3 enc :=
      SigmaP_subset_SigmaP_succ 2 (SigmaP_subset_SigmaP_succ 1
        (SigmaP_one (enc := enc) ▸ ⟨0, fun _ => false, .const _, by simp [IsVerifier]⟩))
    refine ⟨∅, hempty, Set.empty_subset _, fun a _ hComp => ?_⟩
    obtain ⟨z, _, _, hz⟩ := hComp [] (by simp) (by simp [kadinChain])
    exact hz
  | r + 1, d, U, D, hU, hD, hDU, hSoundD, hSoundDiff => by
    obtain ⟨B, hB, D₁, hD₁, hBU, hD₁B, hDB, hD₁UD⟩ := mem_BH_succ_subset hU hD hDU
    obtain ⟨H_r, hH_r_mem, hH_r_sub, hH_r_comp⟩ :=
      exists_kadin_sigmaP_three hm hE r (d + 1) hB hD₁ hD₁B
        (kadinSoundD_succ enc m E hD₁UD hSoundDiff) (kadinSoundDiff_succ enc m E hDB hSoundD)
    let Hard := kadinHardBranch enc p₁ p₂ m E r d D₁ B
    refine ⟨Hard ∪ H_r, union_mem_SigmaP (kadinHardBranch_mem_SigmaP_three hE r d hD₁ hB)
      hH_r_mem, Set.union_subset (kadinHardBranch_subset_kadinTarget enc p₁ p₂ m E hm hDB hSoundD)
        hH_r_sub, fun a ha hComp => ?_⟩
    by_cases hEx : ∃ s : List Bool, s.length = (r • m).eval (enc a).length ∧
        kadinIsHard enc m E r d D₁ a s
    · left
      obtain ⟨s, hs, hHard_s⟩ := hEx
      refine ⟨s, hs, hHard_s, fun u₁ hu₁ => ?_⟩
      obtain ⟨u₂, hu₂, hnotE⟩ := ha u₁ hu₁
      let y := u₁ ++ u₂
      have hy : y.length = m.eval (enc a).length := by simp [y, hm, hu₁, hu₂]
      have hsy_len : (s ++ y).length = ((r + 1) • m).eval (enc a).length := by
        simp [hs, hy, add_smul, one_smul]
      have hnotL_succ : (a, s ++ y) ∉ kadinChain enc m E (r + 1) := by
        rw [mem_kadinChain_succ_append hs]
        exact fun ⟨hyE, _⟩ => hnotE hyE
      obtain ⟨z, hz, hzE, hmemD⟩ := hComp (s ++ y) hsy_len hnotL_succ
      rw [hDB] at hmemD
      refine ⟨u₂ ++ z, by simp [hu₂, hz], by simpa [← hu₂] using hzE,
        by simpa [y, List.append_assoc] using hmemD.1⟩
    · exact Or.inr (hH_r_comp a ha (kadinComp_of_not_exists_kadinIsHard enc m E hD₁UD hSoundDiff
        hEx))

end KadinInduction

/-! ### Reduction to the canonical bit-string Boolean hierarchy -/

/-- Every language in `BH enc r` polynomial-time many-one reduces to a language in the canonical
bit-string Boolean hierarchy `BH encBits r`. -/
theorem exists_mem_BH_encBits_and_polyTimeReducible {r : ℕ} {A : Set α} (hA : A ∈ BH enc r) :
    ∃ B ∈ BH encBits r, PolyTimeReducible enc encBits A B := by
  induction r generalizing A with
  | zero =>
    have hA0 : A = ∅ := hA
    subst hA0
    exact ⟨∅, rfl, ⟨fun _ => [], .const [], fun _ => Iff.rfl⟩⟩
  | succ r ih =>
    obtain ⟨E, hE, D₁, hD₁, rfl⟩ := hA
    obtain ⟨f₀, hf₀, hiff₀⟩ := CookLevin.SAT_npHard enc E hE
    obtain ⟨B₁, hB₁, f₁, hf₁, hiff₁⟩ := ih hD₁
    let B₀ : Set (List Bool) := {w | cnfDecoder.decode w ∈ SAT}
    have hB₀ : B₀ ∈ NP encBits :=
      PolyTimeReducible.mem_NP
        ⟨cnfDecoder.decode, cnfDecoder.computableInPolyTime, fun _ => Iff.rfl⟩
        SAT.mem_NP
    have hunframe : PolyTimeReducible encBits encBits {w | unframe w ∈ B₀} B₀ :=
      ⟨unframe, ComputableInPolyTime.unframe, fun _ => Iff.rfl⟩
    have hdrop : PolyTimeReducible encBits encBits {w | dropFrame w ∈ B₁} B₁ :=
      ⟨dropFrame, ComputableInPolyTime.dropFrame, fun _ => Iff.rfl⟩
    refine ⟨{w | unframe w ∈ B₀} \ {w | dropFrame w ∈ B₁},
      ⟨_, hunframe.mem_NP hB₀, _, hdrop.mem_BH hB₁, rfl⟩,
      fun a => encPair encBits encBits (encCNF (f₀ a), f₁ a),
      (hf₀.encoding_comp.prod hf₁).encoding_comp,
      fun a => ?_⟩
    simp [B₀, unframe_frame_append, dropFrame_frame_append, cnfDecoder.decode_enc, hiff₀ a,
      hiff₁ a]

/-- Collapse of the canonical bit-string Boolean hierarchy `coBH encBits k ⊆ BH encBits k`
transfers to every instance encoding `enc`. -/
theorem coBH_subset_BH_of_coBH_encBits_subset_BH_encBits {k : ℕ}
    (h : coBH encBits k ⊆ BH encBits k) :
    coBH enc k ⊆ BH enc k := by
  intro A hA
  obtain ⟨B, hB, hred⟩ := exists_mem_BH_encBits_and_polyTimeReducible hA
  have hBc : Bᶜ ∈ BH encBits k := h (compl_mem_coBH_iff.mpr hB)
  have hred' : PolyTimeReducible enc encBits A Bᶜ := by
    simpa only [compl_compl] using hred.compl
  exact hred'.mem_BH hBc

/-- Consecutive-level collapse of the canonical bit-string Boolean hierarchy
`BH encBits (k + 1) = BH encBits k` transfers to every instance encoding `enc`. -/
theorem BH_succ_eq_of_BH_encBits_succ_eq {k : ℕ}
    (h : BH encBits (k + 1) = BH encBits k) :
    BH enc (k + 1) = BH enc k :=
  BH_succ_eq_iff_coBH_subset.mpr
    (coBH_subset_BH_of_coBH_encBits_subset_BH_encBits (BH_succ_eq_iff_coBH_subset.mp h))

/-! ### Kadin's collapse theorems -/

/-- **Kadin's theorem at level `3`** [Kadin][Kadin1988]: if `coBH k ⊆ BH k` holds for the pair
encoding `encPair enc encBits`, then `PiP 3 enc ⊆ SigmaP 3 enc`. -/
theorem PiP_three_subset_SigmaP_three_of_coBH_subset_BH {k : ℕ}
    (h : coBH (encPair enc encBits) k ⊆ BH (encPair enc encBits) k) :
    PiP 3 enc ⊆ SigmaP 3 enc := by
  rintro A ⟨ps, V, hps, hV, hAV⟩
  rcases ps with _ | ⟨p₁, _ | ⟨p₂, _ | ⟨p₃, _ | _⟩⟩⟩ <;> try cases hps
  let E : Set (α × List Bool) :=
    {y | ∃ u₃ : List Bool, u₃.length = p₃.eval (enc y.1).length ∧ (!V (y.1, y.2 ++ u₃)) = true}
  have hE : E ∈ NP (encPair enc encBits) :=
    mem_NP_setOf_exists_append (V := fun x => !V x)
      (ComputableInPolyTime.bool_not.comp hV) p₃
  let m := p₁ + p₂
  have hLk_compl : (kadinChain enc m E k)ᶜ ∈ BH (encPair enc encBits) k :=
    h (compl_mem_coBH_iff.mpr (kadinChain_mem_BH hE k))
  have hU : (Set.univ : Set (α × List Bool)) ∈ NP (encPair enc encBits) :=
    ⟨0, fun _ => true, .const _, by simp [IsVerifier]⟩
  have hSoundD : kadinSoundD enc m E k 0 (kadinChain enc m E k)ᶜ := by
    intro a s z hs hz _ hmem
    have hz0 : z = [] := List.length_eq_zero_iff.1 (by simpa using hz)
    subst hz0
    simpa using hmem
  have hSoundDiff : kadinSoundDiff enc m E k 0 Set.univ (kadinChain enc m E k)ᶜ := by
    intro a s z hs hz _ hmem
    have hz0 : z = [] := List.length_eq_zero_iff.1 (by simpa using hz)
    subst hz0
    simpa using hmem
  obtain ⟨H, hH_mem, hH_sub, hH_comp⟩ :=
    exists_kadin_sigmaP_three enc p₁ p₂ m E rfl hE k 0 hU hLk_compl (Set.subset_univ _)
      hSoundD hSoundDiff
  have hA_eq : A = kadinTarget enc p₁ p₂ E := by
    ext a
    rw [hAV a]
    simp only [kadinTarget, Set.mem_ofPred_eq, List.map_cons, List.map_nil,
      alternation_false_cons, alternation_true_cons, alternation_nil]
    refine forall_congr' fun u₁ => imp_congr_right fun _ => ?_
    refine exists_congr fun u₂ => and_congr_right fun _ => ?_
    simp [E, List.append_assoc]
  have hH_eq : A = H := by
    rw [hA_eq]
    refine Set.Subset.antisymm (fun a ha => hH_comp a ha fun s _ hs => ?_) hH_sub
    exact ⟨[], by simp, trivial, by simpa using hs⟩
  rwa [hH_eq]

/-- **Kadin's theorem at level `3`** [Kadin][Kadin1988]: if `coBH k ⊆ BH k` holds for the pair
encoding `encPair enc encBits`, then `SigmaP 3 enc = PiP 3 enc`. -/
theorem SigmaP_three_eq_PiP_three_of_coBH_subset_BH {k : ℕ}
    (h : coBH (encPair enc encBits) k ⊆ BH (encPair enc encBits) k) :
    SigmaP 3 enc = PiP 3 enc := by
  have hsub := PiP_three_subset_SigmaP_three_of_coBH_subset_BH h
  refine Set.Subset.antisymm (fun A hA => ?_) hsub
  simpa using compl_mem_PiP_of_mem_SigmaP (hsub (compl_mem_PiP_of_mem_SigmaP hA))

/-- **Kadin's theorem** [Kadin][Kadin1988]: if `coBH encBits k ⊆ BH encBits k`, the polynomial
hierarchy collapses to `Σ₃ᴾ`. -/
theorem PH_eq_SigmaP_three_of_coBH_subset_BH {k : ℕ}
    (h : coBH encBits k ⊆ BH encBits k) :
    PH enc = SigmaP 3 enc :=
  PH_eq_SigmaP_of_PiP_subset_SigmaP (by decide) fun _ =>
    PiP_three_subset_SigmaP_three_of_coBH_subset_BH
      (coBH_subset_BH_of_coBH_encBits_subset_BH_encBits h)

/-- **Kadin's theorem** [Kadin][Kadin1988]: if `coBH encBits k ⊆ BH encBits k`, the polynomial
hierarchy collapses to `Σ₃ᴾ ∩ Π₃ᴾ`. -/
theorem PH_eq_SigmaP_three_inter_PiP_three_of_coBH_subset_BH {k : ℕ}
    (h : coBH encBits k ⊆ BH encBits k) :
    PH enc = SigmaP 3 enc ∩ PiP 3 enc := by
  rw [PH_eq_SigmaP_three_of_coBH_subset_BH h,
    ← SigmaP_three_eq_PiP_three_of_coBH_subset_BH
      (coBH_subset_BH_of_coBH_encBits_subset_BH_encBits h),
    Set.inter_self]

/-- **Kadin's theorem from `BH (k + 1) = BH k`** [Kadin][Kadin1988]: if two consecutive levels of
the Boolean hierarchy coincide on `encBits`, then `PH = Σ₃ᴾ`. -/
theorem PH_eq_SigmaP_three_of_BH_succ_eq {k : ℕ}
    (h : BH encBits (k + 1) = BH encBits k) :
    PH enc = SigmaP 3 enc :=
  PH_eq_SigmaP_three_of_coBH_subset_BH (BH_succ_eq_iff_coBH_subset.mp h)

/-- **Kadin's theorem for `DP`** [Kadin][Kadin1988]: if `coDP (encPair enc encBits) ⊆
DP (encPair enc encBits)`, then `PiP 3 enc ⊆ SigmaP 3 enc`. -/
theorem PiP_three_subset_SigmaP_three_of_coDP_subset_DP
    (h : coDP (encPair enc encBits) ⊆ DP (encPair enc encBits)) :
    PiP 3 enc ⊆ SigmaP 3 enc := by
  rw [← coBH_two, ← BH_two] at h
  exact PiP_three_subset_SigmaP_three_of_coBH_subset_BH h

/-- **Kadin's theorem for `DP`** [Kadin][Kadin1988]: if `coDP (encPair enc encBits) ⊆
DP (encPair enc encBits)`, then `SigmaP 3 enc = PiP 3 enc`. -/
theorem SigmaP_three_eq_PiP_three_of_coDP_subset_DP
    (h : coDP (encPair enc encBits) ⊆ DP (encPair enc encBits)) :
    SigmaP 3 enc = PiP 3 enc := by
  rw [← coBH_two, ← BH_two] at h
  exact SigmaP_three_eq_PiP_three_of_coBH_subset_BH h

/-- **Kadin's theorem for `coDP ⊆ DP`** [Kadin][Kadin1988]: if `coDP encBits ⊆ DP encBits`,
then `PH = Σ₃ᴾ`. -/
theorem PH_eq_SigmaP_three_of_coDP_subset_DP
    (h : coDP encBits ⊆ DP encBits) :
    PH enc = SigmaP 3 enc := by
  rw [← coBH_two, ← BH_two] at h
  exact PH_eq_SigmaP_three_of_coBH_subset_BH h

/-- **Kadin's theorem for `DP = coDP`** [Kadin][Kadin1988]: if `DP encBits = coDP encBits`,
then `PH = Σ₃ᴾ`. -/
theorem PH_eq_SigmaP_three_of_DP_eq_coDP
    (h : DP encBits = coDP encBits) :
    PH enc = SigmaP 3 enc :=
  PH_eq_SigmaP_three_of_coDP_subset_DP h.symm.subset

/-! ### Collapse from a single `DP`-complete problem in `coDP` -/

/-- If a `DP`-complete problem belongs to `coDP`, then `coDP ⊆ DP` for every instance encoding. -/
theorem DPComplete.coDP_subset_DP_of_mem_coDP {encB : β ↪ List Bool} {B : Set β}
    (hB : DPComplete encB B) (h : B ∈ coDP encB) (enc : α ↪ List Bool) :
    coDP enc ⊆ DP enc := by
  intro A hA
  have hred : PolyTimeReducible enc encB A Bᶜ := by
    simpa only [compl_compl] using (hB.2 enc Aᶜ hA).compl
  exact hred.mem_DP h

/-- If a `DP`-complete problem belongs to `coDP`, then `DP = coDP` for every instance encoding. -/
theorem DPComplete.DP_eq_coDP_of_mem_coDP {encB : β ↪ List Bool} {B : Set β}
    (hB : DPComplete encB B) (h : B ∈ coDP encB) (enc : α ↪ List Bool) :
    DP enc = coDP enc := by
  have hsub := hB.coDP_subset_DP_of_mem_coDP h enc
  exact Set.Subset.antisymm (fun A hA => hsub (by simpa [coDP] using hA)) hsub

/-- **Kadin's theorem for a `DP`-complete problem** [Kadin][Kadin1988]: if a `DP`-complete problem
belongs to `coDP`, then `PH = Σ₃ᴾ`. -/
theorem DPComplete.PH_eq_SigmaP_three_of_mem_coDP {encB : β ↪ List Bool} {B : Set β}
    (hB : DPComplete encB B) (h : B ∈ coDP encB) :
    PH enc = SigmaP 3 enc :=
  PH_eq_SigmaP_three_of_coDP_subset_DP (hB.coDP_subset_DP_of_mem_coDP h encBits)

/-- **Kadin's theorem for `SATUNSAT`** [Kadin][Kadin1988]: if `SATUNSAT ∈ coDP`, the polynomial
hierarchy collapses to `Σ₃ᴾ`. -/
theorem PH_eq_SigmaP_three_of_SATUNSAT_mem_coDP
    (h : SATUNSAT ∈ coDP (encPair encCNF encCNF)) :
    PH enc = SigmaP 3 enc :=
  SATUNSAT_dpComplete.PH_eq_SigmaP_three_of_mem_coDP h

end Cslib.Complexity
