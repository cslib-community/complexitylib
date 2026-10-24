/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Reduction
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder
public import Complexity.Foundations.Data.List.SelectDistinct
public import Mathlib.Data.Finset.Card
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Cslib.Foundations.Data.Polynomial.Monotone
import Mathlib.Data.List.GetD

/-!
# NP membership from witness relations

Membership in `Cslib.Complexity.NP` asks for a verifier whose certificates have length exactly
`p (enc a).length`. Problems are usually given by a witness relation instead: `a` belongs to the
problem when some witness `b` with `R a b` exists, the witnesses of a member can be chosen of
polynomial length, and `R` is decidable in polynomial time
[Papadimitriou, Proposition 9.1][Papadimitriou94]. This file turns such relations into membership
in `NP`, handling the exact-length convention in one place.

A certificate is a witness prefix padded with `false` to the required length, and the verifier
ignores the padding (`Cslib.Complexity.IsVerifier.of_padding`). Three kinds of witnesses are
supported:

* witnesses `b : β` with an encoding `encW` that has a decoder `Turing.MultiTapeTM.Decoder`
  (`Cslib.Complexity.mem_NP_of_witness`): the certificate is `frame (encW b)` followed by padding.
  The verifier `Cslib.Complexity.witnessVerifier` decodes the framed prefix of the certificate,
  re-encodes the decoded witness to reject malformed certificates, and checks the witness
  (`Cslib.Complexity.witnessVerifier_eq_true_iff`). The decoder is what makes the parsing
  polynomial-time: a check that is polynomial-time on encoded witnesses says nothing about words
  that encode no witness;
* sets of candidates from a list computed from the instance
  (`Cslib.Complexity.mem_NP_of_subsetWitness`): bit `i` of the certificate selects the `i`-th
  candidate at its first occurrence (`Cslib.Complexity.selectDistinct`), missing bits are `false`,
  and bits beyond the candidates are ignored;
* bit strings read with default `false`, directly through `IsVerifier.of_padding`, as for the
  assignments of `SAT`.

`NP` is also closed under polynomial-time reductions (`Cslib.Complexity.PolyTimeReducible.mem_NP`,
the unrelativized counterpart of `Cslib.Complexity.PolyTimeReducible.mem_NPWithOracle`).
Certificates for the original instance have a length polynomial in its own length, while the
verifier of the target expects a length determined by the reduced instance, so the verifier reads
only that prefix of the certificate, and `IsVerifier.of_padding` handles the rest.

For verifiers on concatenated strings, `Cslib.Complexity.mem_NP_setOf_exists_append` places the
pairs `(a, u)` admitting an accepted suffix of length `q (enc a).length` in `NP`. This is the
inner existential quantifier used in the Karp–Lipton argument.

## Main definitions

* `Cslib.Complexity.witnessVerifier`: the verifier of a witness relation, parsing certificates
  with a decoder.
* `Cslib.Complexity.subsetVerifier`: the verifier of a subset problem, selecting candidates by a
  mask (`Cslib.Complexity.selectDistinct`).

## Main results

* `Cslib.Complexity.witnessVerifier_eq_true_iff`: the witness verifier accepts exactly a framed
  encoded witness that passes the check, followed by any bits.
* `Cslib.Complexity.isVerifier_witnessVerifier`, `Cslib.Complexity.mem_NP_of_witness`: a relation
  with polynomially short witnesses decided in polynomial time defines a problem in `NP`.
* `Cslib.Complexity.isVerifier_subsetVerifier`, `Cslib.Complexity.mem_NP_of_subsetWitness`:
  subset problems over polynomial-time candidate lists with polynomial-time checks are in `NP`.
* `Cslib.Complexity.PolyTimeReducible.mem_NP`: `NP` is closed under polynomial-time reductions.
* `Cslib.Complexity.mem_NP_setOf_exists_append`: a polynomially bounded suffix accepted by a
  polynomial-time verifier defines a problem in `NP` on pairs.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [C. H. Papadimitriou, *Computational Complexity*][Papadimitriou94]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableTidilyInPolyTime

variable {α β γ : Type} {enc : α ↪ List Bool} {p : Polynomial ℕ} {V : α × List Bool → Bool}
  {A : Set α}

/-! ### Witnesses parsed by a decoder -/

section Witness

variable {encW : β ↪ List Bool}

/-- The verifier of the witness relation decided by `check`. It decodes the framed prefix of the
certificate with `D`, rejects the certificate unless it starts with the framed encoding of the
decoded witness, and checks that witness. -/
def witnessVerifier (D : Decoder encW) (check : α × β → Bool) (x : α × List Bool) : Bool :=
  decide (frame (encW (D.decode (unframe x.2))) ++ dropFrame x.2 = x.2) &&
    check (x.1, D.decode (unframe x.2))

/-- **Malformed certificates are rejected.** `witnessVerifier D check` accepts exactly the
certificates that consist of the framed encoding of a witness accepted by `check`, followed by any
bits. -/
theorem witnessVerifier_eq_true_iff {D : Decoder encW} {check : α × β → Bool} {a : α}
    {w : List Bool} :
    witnessVerifier D check (a, w) = true ↔
      ∃ b v, w = frame (encW b) ++ v ∧ check (a, b) = true := by
  simp only [witnessVerifier, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hw, hcheck⟩
    exact ⟨_, _, hw.symm, hcheck⟩
  · rintro ⟨b, v, rfl, hcheck⟩
    simpa [D.decode_enc] using hcheck

/-- A certificate framing the encoding of a witness, followed by any bits, is checked as that
witness. -/
@[simp]
theorem witnessVerifier_frame_append (D : Decoder encW) (check : α × β → Bool) (a : α) (b : β)
    (v : List Bool) : witnessVerifier D check (a, frame (encW b) ++ v) = check (a, b) := by
  simp [witnessVerifier, D.decode_enc]

/-- **Witness relations.** If `check` decides `R` and every member has a witness whose encoding has
length at most `p (enc a).length`, then `witnessVerifier D check` verifies `{a | ∃ b, R a b}` with
certificates of length `2 * p + 1`: a framed encoded witness, followed by padding. -/
theorem isVerifier_witnessVerifier (D : Decoder encW) {check : α × β → Bool} {R : α → β → Prop}
    (hR : ∀ a b, check (a, b) = true ↔ R a b)
    (hp : ∀ a b, R a b → ∃ b', R a b' ∧ (encW b').length ≤ p.eval (enc a).length) :
    IsVerifier enc (2 * p + 1) (witnessVerifier D check) {a | ∃ b, R a b} := by
  refine IsVerifier.of_padding (fun a w _ h => ?_) fun a ⟨b, hb⟩ => ?_
  · obtain ⟨b, -, -, hcheck⟩ := witnessVerifier_eq_true_iff.1 h
    exact ⟨b, (hR a b).1 hcheck⟩
  obtain ⟨b', hb', hlen⟩ := hp a b hb
  refine ⟨frame (encW b'), ?_, fun k => ?_⟩
  · simp only [length_frame, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_one]
    omega
  · rw [witnessVerifier_frame_append]
    exact (hR a b').2 hb'

/-- The verifier of a witness relation is polynomial-time when its check is. -/
@[fun_prop]
theorem computableInPolyTime_witnessVerifier (D : Decoder encW) {check : α × β → Bool}
    (hcheck : ComputableInPolyTime check (encPair enc encW) encBool) :
    ComputableInPolyTime (witnessVerifier D check) (encPair enc encBits) encBool := by
  have hcheck := hcheck.tidy
  refine .of_tidy ?_
  obtain ⟨_, _, hD⟩ := D.computable
  have hdecode : ComputableTidilyInPolyTime (fun x : α × List Bool => D.decode (unframe x.2))
      (encPair enc encBits) encW :=
    hD.computableTidilyInPolyTime.comp (unframe.comp (snd enc encBits))
  exact bool_and' (decide_eq' (bitsAppend ((bitsFrame encW).comp hdecode)
    (dropFrame.comp (snd enc encBits))) (snd enc encBits))
    (hcheck.comp ((fst enc encBits).prod hdecode))

/-- **NP membership from a witness relation** [Papadimitriou, Proposition 9.1][Papadimitriou94].
If `check` decides the relation `R` in polynomial time, the witness encoding has a decoder, and
every member has a witness whose encoding has length at most `p (enc a).length`, then
`{a | ∃ b, R a b}` is in `NP`. -/
theorem mem_NP_of_witness (D : Decoder encW) {check : α × β → Bool} {R : α → β → Prop}
    (hcheck : ComputableInPolyTime check (encPair enc encW) encBool)
    (hR : ∀ a b, check (a, b) = true ↔ R a b)
    (hp : ∀ a b, R a b → ∃ b', R a b' ∧ (encW b').length ≤ p.eval (enc a).length) :
    {a | ∃ b, R a b} ∈ NP enc := by
  have hcheck := hcheck.tidy
  exact mem_NP.mpr
    ⟨_, _, computableInPolyTime_witnessVerifier D (.of_tidy hcheck),
      isVerifier_witnessVerifier D hR hp⟩

end Witness

/-! ### Subset witnesses -/

section Subset

variable [DecidableEq γ]

/-- The entries of `l` selected by the mask of a set `S` of entries of `l`, followed by any bits,
are the elements of `S`. -/
private theorem toFinset_selectDistinct_map_append {l : List γ} {S : Finset γ} (hS : ∀ v ∈ S, v ∈ l)
    (u : List Bool) : (selectDistinct l (l.map (fun v => decide (v ∈ S)) ++ u)).toFinset = S := by
  have hget : ∀ v ∈ l,
      (l.map (fun v => decide (v ∈ S)) ++ u).getD (l.idxOf v) false = decide (v ∈ S) := by
    intro v hv
    have hlt : l.idxOf v < l.length := List.idxOf_lt_length_iff.2 hv
    rw [List.getD_append _ _ _ _ (by simpa using hlt),
      List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_map, List.getElem_idxOf hlt]
  ext v
  rw [List.mem_toFinset, mem_selectDistinct]
  exact ⟨fun ⟨hv, h⟩ => of_decide_eq_true ((hget v hv).symm.trans h),
    fun hv => ⟨hS v hv, (hget v (hS v hv)).trans (decide_eq_true hv)⟩⟩

/-- Selecting the entries of a list from a mask is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_selectDistinct (encγ : γ ↪ List Bool) :
    ComputableInPolyTime (fun x : List γ × List Bool => selectDistinct x.1 x.2)
      (encPair (encList encγ) encBits) (encList encγ) := by
  unfold selectDistinct
  fun_prop

/-- The verifier of a subset problem over the candidates `vs a`: select candidates by the
certificate mask (`selectDistinct`) and check the selected list. -/
def subsetVerifier (vs : α → List γ) (check : α × List γ → Bool) (x : α × List Bool) : Bool :=
  check (x.1, selectDistinct (vs x.1) x.2)

/-- **Subset witnesses.** Let the candidates `vs a` be at most `p (enc a).length` many, and let
`check` decide `P a` on the duplicate-free lists of candidates. Then `subsetVerifier vs check`
verifies the problem of having a set `S` of candidates with `P a S`, with certificates of length
`p`: the mask of `S`, followed by padding. -/
theorem isVerifier_subsetVerifier {vs : α → List γ}
    (hvs : ∀ a, (vs a).length ≤ p.eval (enc a).length) {check : α × List γ → Bool}
    {P : α → Finset γ → Prop}
    (hP : ∀ a l, l.Nodup → (∀ v ∈ l, v ∈ vs a) → (check (a, l) = true ↔ P a l.toFinset)) :
    IsVerifier enc p (subsetVerifier vs check)
      {a | ∃ S : Finset γ, (∀ v ∈ S, v ∈ vs a) ∧ P a S} := by
  have hsub (a : α) (w : List Bool) : ∀ v ∈ selectDistinct (vs a) w, v ∈ vs a :=
    fun _ hv => (mem_selectDistinct.1 hv).1
  refine IsVerifier.of_padding (fun a w _ h => ?_) fun a ⟨S, hS, hPS⟩ => ?_
  · exact ⟨_, fun v hv => hsub a w v (List.mem_toFinset.1 hv),
      (hP a _ (nodup_selectDistinct _ _) (hsub a w)).1 h⟩
  · refine ⟨(vs a).map (fun v => decide (v ∈ S)), by simpa using hvs a, fun k => ?_⟩
    refine (hP a _ (nodup_selectDistinct _ _) (hsub a _)).2 ?_
    rwa [toFinset_selectDistinct_map_append hS]

/-- The verifier of a subset problem is polynomial-time when the candidates and the check are. -/
@[fun_prop]
theorem computableInPolyTime_subsetVerifier {encγ : γ ↪ List Bool} {vs : α → List γ}
    (hvs : ComputableInPolyTime vs enc (encList encγ)) {check : α × List γ → Bool}
    (hcheck : ComputableInPolyTime check (encPair enc (encList encγ)) encBool) :
    ComputableInPolyTime (subsetVerifier vs check) (encPair enc encBits) encBool :=
  hcheck.comp
    ((ComputableInPolyTime.fst enc encBits).prod ((computableInPolyTime_selectDistinct encγ).comp
    ((hvs.comp (ComputableInPolyTime.fst enc encBits)).prod
      (ComputableInPolyTime.snd enc encBits))))

/-- **NP membership of subset problems.** If the candidates `vs a` and the check of the selected
candidates are polynomial-time, and `check` decides `P a` on duplicate-free lists of candidates,
then having a set `S` of candidates with `P a S` is in `NP`. -/
theorem mem_NP_of_subsetWitness {encγ : γ ↪ List Bool} {vs : α → List γ}
    (hvs : ComputableInPolyTime vs enc (encList encγ)) {check : α × List γ → Bool}
    (hcheck : ComputableInPolyTime check (encPair enc (encList encγ)) encBool)
    {P : α → Finset γ → Prop}
    (hP : ∀ a l, l.Nodup → (∀ v ∈ l, v ∈ vs a) → (check (a, l) = true ↔ P a l.toFinset)) :
    {a | ∃ S : Finset γ, (∀ v ∈ S, v ∈ vs a) ∧ P a S} ∈ NP enc := by
  have hvs := hvs.tidy
  have hcheck := hcheck.tidy
  obtain ⟨p, hle⟩ := hvs.polyBounded_length.exists_polynomial
  refine mem_NP.mpr ⟨p, _,
    computableInPolyTime_subsetVerifier (.of_tidy hvs) (.of_tidy hcheck),
    isVerifier_subsetVerifier (fun a => ?_) hP⟩
  exact (length_le_length_encList encγ (vs a)).trans (hle a)

end Subset

/-! ### Closure under reductions -/

/-- **`NP` is closed under polynomial-time reductions.** The verifier of `A` runs the verifier of
`B` on the reduced instance and on the prefix of the certificate whose length the verifier of `B`
expects. For the oracle classes, see `Cslib.Complexity.PolyTimeReducible.mem_NPWithOracle`. -/
theorem PolyTimeReducible.mem_NP {encB : β ↪ List Bool} {B : Set β}
    (h : PolyTimeReducible enc encB A B) (hB : B ∈ NP encB) : A ∈ NP enc := by
  obtain ⟨f, hf, hAB⟩ := h
  obtain ⟨q, W, hW, hWB⟩ := Complexity.mem_NP.mp hB
  have hf := hf.tidy
  have hlen : ComputableTidilyInPolyTime (fun a => q.eval (encB (f a)).length) enc encUnary :=
    (unary_eval q).comp ((encoding_length encB).comp hf)
  obtain ⟨p, hle⟩ := hlen.polyBounded.exists_polynomial
  refine Complexity.mem_NP.mpr ⟨p,
    fun x => W (f x.1, x.2.take (q.eval (encB (f x.1)).length)), ?_,
    IsVerifier.of_padding (fun a w hw h => ?_) fun a ha => ?_⟩
  · exact .of_tidy <| hW.tidy.comp ((hf.comp (fst enc encBits)).prod
      (bitsTakeWithInput (snd enc encBits) (hlen.comp (fst enc encBits))))
  · refine (hAB a).2 ((hWB (f a)).2 ⟨_, List.length_take_of_le ?_, h⟩)
    rw [hw]
    exact hle a
  · obtain ⟨u, hu, hWu⟩ := (hWB (f a)).1 ((hAB a).1 ha)
    refine ⟨u, by rw [hu]; exact hle a, fun k => ?_⟩
    simpa only [List.take_left' hu] using hWu

/-- `coNP` is closed under polynomial-time reductions. -/
theorem PolyTimeReducible.mem_coNP {encB : β ↪ List Bool} {B : Set β}
    (h : PolyTimeReducible enc encB A B) (hB : B ∈ coNP encB) : A ∈ coNP enc :=
  h.mem_compl PolyTimeReducible.mem_NP hB

/-! ### The inner quantifier -/

/-- **The inner quantifier of a `Π₂` verifier is in `NP`.** For a polynomial-time `V`, the pairs
`(a, u)` for which `V` accepts `(a, u ++ v)` for some `v` of length `q (enc a).length` form a
problem in `NP`, for the encoding of pairs. -/
theorem mem_NP_setOf_exists_append {V : α × List Bool → Bool}
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool) (q : Polynomial ℕ) :
    {y : α × List Bool | ∃ v : List Bool, v.length = q.eval (enc y.1).length ∧
      V (y.1, y.2 ++ v) = true} ∈ NP (encPair enc encBits) := by
  have hV := hV.tidy
  refine mem_NP.mpr
    ⟨q, fun z => V (z.1.1, z.1.2 ++ z.2.take (q.eval (enc z.1.1).length)), ?_, fun y => ?_⟩
  · exact .of_tidy <| hV.comp ((fst _ _).fst'.prod (bitsAppend (fst _ _).snd'
      (bitsTakeWithInput (snd _ _) ((unary_eval q).comp ((encoding_length enc).comp
        (fst _ _).fst')))))
  · have hle : q.eval (enc y.1).length ≤ q.eval (encPair enc encBits y).length :=
      q.eval_mono (length_le_encPair_left _ _ _)
    constructor
    · rintro ⟨v, hv, hV⟩
      refine ⟨v ++ List.replicate (q.eval (encPair enc encBits y).length - v.length) false,
        by simp only [List.length_append, List.length_replicate, hv]; omega, ?_⟩
      dsimp only
      rwa [← hv, List.take_left]
    · rintro ⟨w, hw, hV⟩
      exact ⟨_, by rw [List.length_take, hw, Nat.min_eq_left hle], hV⟩

end Cslib.Complexity
