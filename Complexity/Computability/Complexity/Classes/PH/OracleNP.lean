/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Oracle.BoundedQuery
public import Complexity.Computability.Complexity.Classes.PH
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.Oracle
import Complexity.Computability.Complexity.Classes.NP.Witness
import Complexity.Computability.Complexity.Classes.Oracle.Deterministic
import Complexity.Computability.Complexity.Classes.Oracle.Lowness
import Complexity.Computability.Complexity.Classes.PH.Closure
import Complexity.Computability.Complexity.Classes.PH.Collapse
import Complexity.Computability.Complexity.Classes.SharpP
import Complexity.Computability.Complexity.Classes.SharpP.PolyTime
import Complexity.Computability.Complexity.Classes.SharpP.Products
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import Cslib.Foundations.Data.Polynomial.Monotone

/-!
# `P^NP ⊆ Σ₂ ∩ Π₂`

A polynomial-time computation with an oracle `A ∈ NP` is simulated in `Σ₂` by guessing its
transcript of oracle replies (`Turing.MultiTapePTM.oracleReplies`). A guessed transcript is the
canonical one exactly when every `true` reply answers a query in `A`, an `NP` condition
(`Cslib.Complexity.oracleTranscriptYes_mem_NP`), and every `false` reply answers a query outside
`A`, a `coNP` condition (`Cslib.Complexity.oracleTranscriptNo_mem_coNP`)
(`Cslib.Complexity.mem_oracleTranscriptYes_inter_oracleTranscriptNo`). The pairs of an instance
and an accepted canonical transcript therefore form a problem in `Σ₂`, and so does its projection
(`Cslib.Complexity.mem_SigmaP_of_exists`). Since `P^A` is closed under complement, it also lies in
`Π₂`. This is the inclusion `Δ₂ᵖ ⊆ Σ₂ᵖ ∩ Π₂ᵖ` of the polynomial hierarchy
[Stockmeyer][Stockmeyer1976].

In particular `P^{NP[O(log n)]} ⊆ Σ₂ ∩ Π₂ ⊆ PH`
(`Cslib.Complexity.PNPLog_subset_SigmaP_two_inter_PiP_two`), the inclusion `Θ₂ᵖ ⊆ Σ₂ᵖ` used by
[Hemaspaandra and Ogihara, Theorem 1.14][HemaspaandraOgihara2002] in the proof of Kadin's theorem.

## Main definitions

* `Cslib.Complexity.oracleTranscriptYes`, `Cslib.Complexity.oracleTranscriptNo`: the transcripts
  whose `true`, respectively `false`, query replies are correct for the oracle.

## Main results

* `Cslib.Complexity.ComputableInPolyTimeWithOracle.encoded_mem_SigmaP_two`: a polynomial-time
  predicate of an `FP^NP` output defines a problem in `Σ₂`.
* `Cslib.Complexity.PWithOracle_subset_SigmaP_two_inter_PiP_two`: `P^A ⊆ Σ₂ ∩ Π₂` for `A ∈ NP`.
* `Cslib.Complexity.PNPLog_subset_SigmaP_two_inter_PiP_two`, `Cslib.Complexity.PNPLog_subset_PH`:
  `P^{NP[O(log n)]} ⊆ Σ₂ ∩ Π₂ ⊆ PH`.

## References

* [L. J. Stockmeyer, *The polynomial-time hierarchy*][Stockmeyer1976]
* [L. A. Hemaspaandra, M. Ogihara, *The Complexity Theory Companion*][HemaspaandraOgihara2002]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-! ### Transcript certificates -/

section Transcript

open _root_.Turing _root_.Turing.MultiTapePTM _root_.Turing.MultiTapeMachine

variable {k : ℕ} {Control Operation : Type} [DecidableEq Operation]

/-- Every `true` bit of the transcript answers a pending query in `A`. -/
def oracleTranscriptYes (machine : MultiTapePTM k Bool Control Operation) (enc : α ↪ List Bool)
    (A : Set (List Bool)) : Set (α × List Bool) :=
  {x | ∀ i < x.2.length, x.2.getD i false = true →
    (machine.pendingQuery (machine.replayPrefix (enc x.1) x.2 i)).isSome ∧
      machine.pendingRequest (machine.replayPrefix (enc x.1) x.2 i) ∈ A}

/-- Every `false` bit of a pending query answers a query outside `A`. -/
def oracleTranscriptNo (machine : MultiTapePTM k Bool Control Operation) (enc : α ↪ List Bool)
    (A : Set (List Bool)) : Set (α × List Bool) :=
  {x | ∀ i < x.2.length, x.2.getD i false = false →
    (machine.pendingQuery (machine.replayPrefix (enc x.1) x.2 i)).isSome →
      machine.pendingRequest (machine.replayPrefix (enc x.1) x.2 i) ∉ A}

theorem mem_oracleTranscriptYes {machine : MultiTapePTM k Bool Control Operation}
    {A : Set (List Bool)} {x : α × List Bool} :
    x ∈ oracleTranscriptYes machine enc A ↔ ∀ i < x.2.length, x.2.getD i false = true →
      (machine.pendingQuery (machine.replayPrefix (enc x.1) x.2 i)).isSome ∧
        machine.pendingRequest (machine.replayPrefix (enc x.1) x.2 i) ∈ A :=
  Iff.rfl

theorem mem_oracleTranscriptNo {machine : MultiTapePTM k Bool Control Operation}
    {A : Set (List Bool)} {x : α × List Bool} :
    x ∈ oracleTranscriptNo machine enc A ↔ ∀ i < x.2.length, x.2.getD i false = false →
      (machine.pendingQuery (machine.replayPrefix (enc x.1) x.2 i)).isSome →
        machine.pendingRequest (machine.replayPrefix (enc x.1) x.2 i) ∉ A :=
  Iff.rfl

variable {machine : MultiTapePTM k Bool Control Operation} {A : Set (List Bool)}

open Classical in
/-- A transcript is certified by both `oracleTranscriptYes` and `oracleTranscriptNo` exactly when
it is the canonical transcript of oracle replies for `A` of its own length. -/
theorem mem_oracleTranscriptYes_inter_oracleTranscriptNo {x : α × List Bool} :
    x ∈ oracleTranscriptYes machine enc A ∩ oracleTranscriptNo machine enc A ↔
      x.2 = machine.oracleReplies (fun q => decide (q ∈ A)) x.2.length (enc x.1) := by
  rw [machine.eq_oracleReplies_iff]
  simp only [Set.mem_inter_iff, mem_oracleTranscriptYes, mem_oracleTranscriptNo]
  constructor
  · rintro ⟨hY, hN⟩ i hi
    cases hb : x.2.getD i false
    · cases hq : (machine.pendingQuery (machine.replayPrefix (enc x.1) x.2 i)).isSome
      · simp
      · simp [hN i hi hb hq]
    · obtain ⟨hq, hA⟩ := hY i hi hb
      simp [hq, hA]
  · intro h
    refine ⟨fun i hi hb => ?_, fun i hi hb hq => ?_⟩
    · rw [h i hi] at hb
      split_ifs at hb with hq
      · exact ⟨hq, of_decide_eq_true hb⟩
    · rw [h i hi] at hb
      simpa only [hq, ↓reduceIte, decide_eq_false_iff_not] using hb

open Classical in
/-- The transcripts whose `true` bits are certified form a problem in `NP`: the certificate lists
an `NP` certificate for every such bit, through a `#P` product. -/
theorem oracleTranscriptYes_mem_NP [Finite Control] [Finite Operation] (hA : A ∈ NP encBits) :
    oracleTranscriptYes machine enc A ∈ NP (encPair enc encBits) := by
  let _ := Fintype.ofFinite Operation
  obtain ⟨fA, hfA, hA⟩ := mem_NP_iff_exists_SharpP.mp hA
  have hinput : ComputableInPolyTime (fun a : α => enc a) enc encBits := ComputableInPolyTime.id'
  let cfg : (α × List Bool) × ℕ → FiniteConfig k Bool Control Operation :=
    fun y => machine.replayPrefix (enc y.1.1) y.1.2 y.2
  have hcfg : ComputableInPolyTime cfg (encPair (encPair enc encBits) encUnary)
      encFiniteConfig :=
    machine.computableInPolyTime_replayPrefix.comp (g := fun y : (α × List Bool) × ℕ =>
      ((enc y.1.1, y.1.2), y.2)) (by fun_prop)
  have hquery : ComputableInPolyTime (fun y => (machine.pendingQuery (cfg y)).isSome)
      (encPair (encPair enc encBits) encUnary) encBool :=
    (ComputableInPolyTime.of_finite Option.isSome).comp (machine.pendingQuery_pt.comp hcfg)
  have hreq : ComputableInPolyTime (fun y => machine.pendingRequest (cfg y))
      (encPair (encPair enc encBits) encUnary) encBits :=
    machine.pendingRequest_pt.comp hcfg
  have hbit : ComputableInPolyTime (fun y : (α × List Bool) × ℕ => y.1.2.getD y.2 false)
      (encPair (encPair enc encBits) encUnary) encBool := by fun_prop
  let factor : (α × List Bool) × ℕ → ℕ := fun y =>
    if y.1.2.getD y.2 false then
      (if (machine.pendingQuery (cfg y)).isSome then fA (machine.pendingRequest (cfg y)) else 0)
    else 1
  have hfactor : factor ∈ SharpP (encPair (encPair enc encBits) encUnary) :=
    SharpP.ite_mem hbit (SharpP.ite_mem hquery (SharpP.comp_mem hfA hreq) SharpP.zero_mem)
      SharpP.one_mem
  refine mem_NP_iff_exists_SharpP.mpr ⟨fun x => ∏ i ∈ Finset.range x.2.length, factor (x, i),
    SharpP.prod_range_mem hfactor (by fun_prop), fun x => ?_⟩
  rw [CanonicallyOrderedAdd.prod_pos]
  simp only [mem_oracleTranscriptYes, Finset.mem_range]
  refine forall₂_congr fun i _ => ?_
  simp only [factor, cfg]
  cases x.2.getD i false
  · simp
  · cases (machine.pendingQuery (machine.replayPrefix (enc x.1) x.2 i)).isSome
    · simp
    · simp [hA]

open Classical in
/-- The transcripts whose `false` bits at queries are certified form a problem in `coNP`: a
witness against it is the index of a `false` bit together with an `NP` certificate that its query
lies in `A`. -/
theorem oracleTranscriptNo_mem_coNP [Finite Control] [Finite Operation] (hA : A ∈ NP encBits) :
    oracleTranscriptNo machine enc A ∈ coNP (encPair enc encBits) := by
  let _ := Fintype.ofFinite Operation
  obtain ⟨pA, VA, hVA, hA⟩ := mem_NP.mp hA
  have hinput : ComputableInPolyTime (fun a : α => enc a) enc encBits := ComputableInPolyTime.id'
  let req : (α × List Bool) × ℕ → List Bool :=
    fun y => machine.pendingRequest (machine.replayPrefix (enc y.1.1) y.1.2 y.2)
  let isQ : (α × List Bool) × ℕ → Bool :=
    fun y => (machine.pendingQuery (machine.replayPrefix (enc y.1.1) y.1.2 y.2)).isSome
  have hreq : ComputableInPolyTime req (encPair (encPair enc encBits) encUnary) encBits :=
    machine.replayPrefix_pendingRequest_pt.comp (g := fun y : (α × List Bool) × ℕ =>
      ((enc y.1.1, y.1.2), y.2)) (by fun_prop)
  have hisQ : ComputableInPolyTime isQ (encPair (encPair enc encBits) encUnary) encBool :=
    machine.replayPrefix_isQuery_pt.comp (g := fun y : (α × List Bool) × ℕ =>
      ((enc y.1.1, y.1.2), y.2)) (by fun_prop)
  -- the relation: `w.1` is a live index with bit `false` at a query, and `w.2` certifies its query
  let R : α × List Bool → ℕ × List Bool → Prop := fun x w =>
    w.1 < x.2.length ∧ x.2.getD w.1 false = false ∧ isQ (x, w.1) = true ∧
      w.2.length = pA.eval (req (x, w.1)).length ∧ VA (req (x, w.1), w.2) = true
  let check : (α × List Bool) × (ℕ × List Bool) → Bool := fun z =>
    decide (z.2.1 < z.1.2.length) && !z.1.2.getD z.2.1 false && isQ (z.1, z.2.1) &&
      decide (z.2.2.length = pA.eval (req (z.1, z.2.1)).length) && VA (req (z.1, z.2.1), z.2.2)
  have hcheck : ComputableInPolyTime check
      (encPair (encPair enc encBits) (encPair encUnary encBits)) encBool := by
    have hidx : ComputableInPolyTime
        (fun z : (α × List Bool) × (ℕ × List Bool) => (z.1, z.2.1))
        (encPair (encPair enc encBits) (encPair encUnary encBits))
        (encPair (encPair enc encBits) encUnary) := by fun_prop
    have hreq' := hreq.comp hidx
    have hisQ' := hisQ.comp hidx
    have hV' : ComputableInPolyTime
        (fun z : (α × List Bool) × (ℕ × List Bool) => VA (req (z.1, z.2.1), z.2.2))
        (encPair (encPair enc encBits) (encPair encUnary encBits)) encBool :=
      hVA.comp (hreq'.prod (by fun_prop))
    have hlen' : ComputableInPolyTime
        (fun z : (α × List Bool) × (ℕ × List Bool) => pA.eval (req (z.1, z.2.1)).length)
        (encPair (encPair enc encBits) (encPair encUnary encBits)) encUnary :=
      (ComputableInPolyTime.unary_eval pA).comp
        ((ComputableInPolyTime.encoding_length _).comp hreq')
    simp only [check]
    fun_prop
  have hR : ∀ x w, check (x, w) = true ↔ R x w := by
    intro x w
    simp only [check, R, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', and_assoc]
  have hset : (oracleTranscriptNo machine enc A)ᶜ = {x | ∃ w, R x w} := by
    ext x
    constructor
    · intro hx
      by_contra hne
      refine hx fun i hi hb hq hmem => ?_
      obtain ⟨w, hw, hV⟩ := (hA _).mp hmem
      exact hne ⟨(i, w), hi, hb, hq, hw, hV⟩
    · rintro ⟨⟨i, w⟩, hi, hb, hq, hw, hV⟩ hx
      exact hx i hi hb hq ((hA _).mpr ⟨w, hw, hV⟩)
  rw [mem_coNP, hset]
  refine mem_NP_of_witness (p := 2 * Polynomial.X + 1 + pA)
    (Decoder.pair Decoder.unary Decoder.bits)
    hcheck hR fun x w hw => ⟨w, hw, ?_⟩
  obtain ⟨hi, -, -, hlen, -⟩ := hw
  have hx2 : x.2.length ≤ (encPair enc encBits x).length := by
    rw [length_encPair, encBits_apply]
    omega
  have hreq_le : (req (x, w.1)).length ≤ (encPair enc encBits x).length :=
    ((machine.length_pendingRequest_replayPrefix_le _ _ _).trans (Nat.min_le_right _ _)).trans hx2
  have hi' : w.1 ≤ (encPair enc encBits x).length := hi.le.trans hx2
  have hpA := Polynomial.eval_mono (p := pA) hreq_le
  simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X,
    Polynomial.eval_one] at hpA hi' hlen ⊢
  omega

end Transcript

/-! ### `P^NP ⊆ Σ₂ ∩ Π₂` -/

section PNP

open _root_.Turing _root_.Turing.MultiTapePTM

variable {β : Type} {output : β ↪ List Bool} {A : Set (List Bool)}

open Classical in
/-- **Polynomial-time predicates of `FP^NP` outputs lie in `Σ₂`.** If `A ∈ NP`, `f` is computable
in polynomial time relative to `A`, and `P` is a polynomial-time predicate of an instance and an
encoded output, then `{a | P (a, output (f a)) = true} ∈ Σ₂`. Guess the transcript of oracle
replies: its `true` bits are certified existentially and its `false` bits universally. -/
theorem ComputableInPolyTimeWithOracle.encoded_mem_SigmaP_two {f : α → β}
    {P : α × List Bool → Bool} (hA : A ∈ NP encBits)
    (hf : ComputableInPolyTimeWithOracle A f enc output)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBool) :
    {a | P (a, output (f a)) = true} ∈ SigmaP 2 enc := by
  obtain ⟨program, hcert, hprogram⟩ := hf
  obtain ⟨k, m, machine, c, d, hrun⟩ := hcert.exists_fin_run_pure_false
  let T : Polynomial ℕ := Polynomial.C c * (Polynomial.X + 1) ^ d
  have hT (a : α) : T.eval (enc a).length = c * ((enc a).length + 1) ^ d := by simp [T]
  -- the replayed output of a transcript satisfies `P`
  let good : Set (α × List Bool) :=
    {x | P (x.1, machine.replayOutput (enc x.1) x.2) = true}
  have hgood : good ∈ SigmaP 2 (encPair enc encBits) := by
    have hinput : ComputableInPolyTime (fun a : α => enc a) enc encBits := ComputableInPolyTime.id'
    have hgoodP : good ∈ Complexity.P (encPair enc encBits) :=
      ⟨fun x => P (x.1, machine.replayOutput (enc x.1) x.2), hP.comp
        ((ComputableInPolyTime.fst _ _).prod
          (machine.computableInPolyTime_replayOutput.comp
            (g := fun x : α × List Bool => (enc x.1, x.2)) (by fun_prop))), fun _ => Iff.rfl⟩
    rw [← SigmaP_zero] at hgoodP
    exact SigmaP_mono (show 0 ≤ 2 by omega) hgoodP
  have hYes : oracleTranscriptYes machine enc A ∈ SigmaP 2 (encPair enc encBits) :=
    SigmaP_subset_SigmaP_succ 1 (SigmaP_one ▸ oracleTranscriptYes_mem_NP hA)
  have hNo : oracleTranscriptNo machine enc A ∈ SigmaP 2 (encPair enc encBits) :=
    PiP_subset_SigmaP_succ 1 (PiP_one_eq_coNP ▸ oracleTranscriptNo_mem_coNP hA)
  have hB := inter_mem_SigmaP hgood (inter_mem_SigmaP hYes hNo)
  convert mem_SigmaP_of_exists (by omega) hB T using 1
  ext a
  simp only [Set.mem_ofPred_eq, hT]
  let g : List Bool → Bool := fun q => decide (q ∈ A)
  have hout : machine.replayOutput (enc a)
      (machine.oracleReplies g (c * ((enc a).length + 1) ^ d) (enc a)) = output (f a) := by
    rw [machine.replayOutput_oracleReplies]
    exact (hrun a (languageOracle A)).trans (congrArg output (hprogram a))
  constructor
  · intro h
    refine ⟨machine.oracleReplies g (c * ((enc a).length + 1) ^ d) (enc a),
      machine.length_oracleReplies _ _ _, ?_,
      mem_oracleTranscriptYes_inter_oracleTranscriptNo.mpr ?_⟩
    · change P (a, _) = true
      rwa [hout]
    · rw [machine.length_oracleReplies]
  · rintro ⟨t, ht, hP', hYN⟩
    have heq : t = machine.oracleReplies g t.length (enc a) :=
      mem_oracleTranscriptYes_inter_oracleTranscriptNo.mp hYN
    change P (a, machine.replayOutput (enc a) t) = true at hP'
    rwa [heq, ht, hout] at hP'

/-- **`P^A ⊆ Σ₂` for `A ∈ NP`.** -/
theorem PWithOracle_subset_SigmaP_two (hA : A ∈ NP encBits) :
    PWithOracle A enc ⊆ SigmaP 2 enc := by
  rintro L ⟨f, hf, hL⟩
  have hP : ComputableInPolyTime (fun x : α × List Bool => decide (x.2 = [true]))
      (encPair enc encBits) encBool := by fun_prop
  convert hf.encoded_mem_SigmaP_two hA hP using 1
  ext a
  simp [hL a, encBool_apply]

/-- **`P^A ⊆ Π₂` for `A ∈ NP`**: `P^A` is closed under complement. -/
theorem PWithOracle_subset_PiP_two (hA : A ∈ NP encBits) :
    PWithOracle A enc ⊆ PiP 2 enc := fun L hL => by
  simpa only [compl_compl] using
    compl_mem_PiP_of_mem_SigmaP (PWithOracle_subset_SigmaP_two hA (compl_mem_PWithOracle hL))

/-- **`P^NP ⊆ Σ₂ ∩ Π₂`** [Stockmeyer][Stockmeyer1976]. -/
theorem PWithOracle_subset_SigmaP_two_inter_PiP_two (hA : A ∈ NP encBits) :
    PWithOracle A enc ⊆ SigmaP 2 enc ∩ PiP 2 enc :=
  Set.subset_inter (PWithOracle_subset_SigmaP_two hA) (PWithOracle_subset_PiP_two hA)

/-- **`P^{NP[O(log n)]} ⊆ Σ₂ ∩ Π₂`.** -/
theorem PNPLog_subset_SigmaP_two_inter_PiP_two (enc : α ↪ List Bool) :
    PNPLog enc ⊆ SigmaP 2 enc ∩ PiP 2 enc := fun L hL => by
  obtain ⟨A, hA, hLA⟩ := Set.mem_iUnion₂.mp (PNPLog_subset_PWithOracle enc hL)
  exact PWithOracle_subset_SigmaP_two_inter_PiP_two hA hLA

/-- **`P^{NP[O(log n)]} ⊆ PH`.** -/
theorem PNPLog_subset_PH (enc : α ↪ List Bool) : PNPLog enc ⊆ PH enc := fun _ hL =>
  SigmaP_subset_PH 2 (PNPLog_subset_SigmaP_two_inter_PiP_two enc hL).1

end PNP

end Cslib.Complexity
