/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Oracle.Closure
public import CslibFrontier.Computability.Complexity.Classes.Oracle.PolyTime
public import CslibFrontier.Computability.Complexity.Classes.UP
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.Oracle
import CslibFrontier.Computability.Complexity.Classes.Oracle.CanonicalReplay
import CslibFrontier.Computability.Complexity.Classes.P.Complement
import CslibFrontier.Computability.Complexity.Classes.SharpP.Aggregation
import CslibFrontier.Computability.Complexity.Classes.SharpP.PolyTime
import CslibFrontier.Computability.Complexity.Classes.SharpP.OracleReplay
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Mathlib.Data.List.OfFn

/-!
# Oracle lowness of `NP ∩ coNP` and `UP ∩ coUP`

An oracle language `A ∈ NP ∩ coNP` adds nothing to nondeterministic polynomial time:
`NP^A = NP` and `P^A ⊆ NP ∩ coNP`, and conversely any language `A` with `NP^A = NP` lies in
`NP ∩ coNP` [Schöning][Schoening1989] [Arora and Barak, Chapter 3][AroraBarak09]. When `A` is in
`UP ∩ coUP`, every `P^A` predicate has at most one accepting replay certificate, giving
`P^A ⊆ UP ∩ coUP`.

The proof combines deterministic instruction-indexed oracle replay
(`Turing.MultiTapePTM.replayPrefix`, `Turing.MultiTapePTM.replayOutput`,
`Turing.MultiTapePTM.oracleReplies`) with uniform `#P` products and Boolean sums
(`Cslib.Complexity.SharpP.prod_range_mem`, `Cslib.Complexity.SharpP.sum_bits_mem`):

1. Given `#P` functions `fYes` and `fNo` whose supports are `A` and `Aᶜ`, each replayed step `i`
   contributes `fYes q_i` when step `i` submits query `q_i` and the guessed reply bit is `true`,
   `fNo q_i` when step `i` submits `q_i` and the guessed reply bit is `false`, and `1` (for bit
   `false`) or `0` (for bit `true`) at local and halted instructions.
2. Multiplying these step factors over `i < |answers|` produces a `#P` path count
   (`Cslib.Complexity.replayPathCount`) that is positive if and only if `answers` equals the
   canonical transcript `machine.oracleReplies`. When `fYes` and `fNo` are bounded by `1`
   (`A ∈ UP ∩ coUP`), the path count is `1` on the canonical transcript and `0` on every other
   transcript.
3. Summing over all transcript words of the polynomial clock length
   (`Cslib.Complexity.replayWeightedSum`) therefore certifies any
   polynomial-time predicate of `(a, output (f a))` in `NP` (or `UP`). Applying this to the output
   bits of a `P^A` decider yields `P^A ⊆ NP ∩ coNP` (and `P^A ⊆ UP ∩ coUP`), and applying it to an
   `NP^A` verifier on `encPair enc encBits` yields `NP^A = NP`.

## Main results

* `Cslib.Complexity.compl_mem_PWithOracle`, `Cslib.Complexity.inter_mem_PWithOracle`,
  `Cslib.Complexity.union_mem_PWithOracle`, `Cslib.Complexity.mem_PWithOracle_compl_self`: Boolean
  closure of `P^A`.
* `Cslib.Complexity.ComputableInPolyTimeWithOracle.encoded_mem_NP`,
  `Cslib.Complexity.ComputableInPolyTimeWithOracle.mem_NP`,
  `Cslib.Complexity.ComputableInPolyTimeWithOracle.encoded_mem_UP`,
  `Cslib.Complexity.ComputableInPolyTimeWithOracle.mem_UP`: polynomial-time predicates of `FP^A`
  functions lie in `NP` (for `A ∈ NP ∩ coNP`) and `UP` (for `A ∈ UP ∩ coUP`).
* `Cslib.Complexity.PWithOracle_subset_NP`, `Cslib.Complexity.PWithOracle_subset_coNP`,
  `Cslib.Complexity.PWithOracle_subset_NP_inter_coNP`,
  `Cslib.Complexity.PWithOracle_subset_NP_inter_coNP_iff`,
  `Cslib.Complexity.iUnion_PWithOracle_NP_inter_coNP`,
  `Cslib.Complexity.P_eq_NP_inter_coNP_iff_forall_PWithOracle_eq_P`:
  `P^(NP ∩ coNP) = NP ∩ coNP`.
* `Cslib.Complexity.PWithOracle_subset_UP`, `Cslib.Complexity.PWithOracle_subset_coUP`,
  `Cslib.Complexity.PWithOracle_subset_UP_inter_coUP`,
  `Cslib.Complexity.PWithOracle_subset_UP_inter_coUP_iff`,
  `Cslib.Complexity.iUnion_PWithOracle_UP_inter_coUP`:
  `P^(UP ∩ coUP) = UP ∩ coUP`.
* `Cslib.Complexity.NPWithOracle_subset_NP_of_PWithOracle_subset_NP`,
  `Cslib.Complexity.NPWithOracle_eq_NP_of_mem_NP_of_mem_coNP`,
  `Cslib.Complexity.NPWithOracle_eq_NP_iff`,
  `Cslib.Complexity.forall_NPWithOracle_eq_NP_iff`,
  `Cslib.Complexity.iUnion_NPWithOracle_NP_inter_coNP`,
  `Cslib.Complexity.P_eq_NP_iff_forall_PWithOracle_eq_P`,
  `Cslib.Complexity.NP_eq_coNP_iff_forall_NPWithOracle_eq_NP`:
  `NP^A = NP` if and only if `A ∈ NP ∩ coNP`, and `NP = coNP` if and only if `NP^NP = NP`.

## References

* [U. Schöning, *Probabilistic Complexity Classes and Lowness*][Schoening1989]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeMachine
  _root_.Turing.MultiTapePTM Finset

variable {α β : Type} {enc : α ↪ List Bool} {output : β ↪ List Bool} {A : Set (List Bool)}

/-! ### Boolean closure of `PWithOracle` -/

/-- **`P` relative to an oracle is closed under complement**: negate the Boolean decider. -/
theorem compl_mem_PWithOracle {L : Set α} (hL : L ∈ PWithOracle A enc) :
    Lᶜ ∈ PWithOracle A enc := by
  obtain ⟨f, hf, hL⟩ := hL
  refine ⟨fun a => !f a, hf.map (by fun_prop), fun a => ?_⟩
  rw [Set.mem_compl_iff, hL a]
  cases h : f a <;> simp [h]

/-- **`P` relative to an oracle is closed under intersection.** -/
theorem inter_mem_PWithOracle {L₁ L₂ : Set α} (h₁ : L₁ ∈ PWithOracle A enc)
    (h₂ : L₂ ∈ PWithOracle A enc) : L₁ ∩ L₂ ∈ PWithOracle A enc := by
  obtain ⟨f₁, hf₁, hL₁⟩ := h₁
  obtain ⟨f₂, hf₂, hL₂⟩ := h₂
  refine ⟨fun a => f₁ a && f₂ a, (hf₁.prod hf₂).map (g := fun p => p.1 && p.2)
    (by fun_prop),
    fun a => ?_⟩
  rw [Set.mem_inter_iff, hL₁ a, hL₂ a, Bool.and_eq_true]

/-- **`P` relative to an oracle is closed under union.** -/
theorem union_mem_PWithOracle {L₁ L₂ : Set α} (h₁ : L₁ ∈ PWithOracle A enc)
    (h₂ : L₂ ∈ PWithOracle A enc) : L₁ ∪ L₂ ∈ PWithOracle A enc := by
  obtain ⟨f₁, hf₁, hL₁⟩ := h₁
  obtain ⟨f₂, hf₂, hL₂⟩ := h₂
  refine ⟨fun a => f₁ a || f₂ a, (hf₁.prod hf₂).map (g := fun p => p.1 || p.2)
    (by fun_prop),
    fun a => ?_⟩
  rw [Set.mem_union, hL₁ a, hL₂ a, Bool.or_eq_true]

/-- **`P` relative to `A` contains `Aᶜ`.** -/
theorem mem_PWithOracle_compl_self (A : Set (List Bool)) : Aᶜ ∈ PWithOracle A encBits :=
  compl_mem_PWithOracle (mem_PWithOracle_self A)

/-! ### Oracle lowness of `NP ∩ coNP` -/

open Classical in
/-- **Polynomial-time predicates of encoded `FP^(NP ∩ coNP)` outputs lie in `NP`.** If
`A ∈ NP ∩ coNP`, `f : α → β` is computable in polynomial time relative to `A`, and
`P : α × List Bool → Bool` is computable in polynomial time, then
`{a | P (a, output (f a)) = true} ∈ NP enc`. -/
theorem ComputableInPolyTimeWithOracle.encoded_mem_NP {f : α → β} {P : α × List Bool → Bool}
    (hA_np : A ∈ NP encBits) (hA_conp : A ∈ coNP encBits)
    (hf : ComputableInPolyTimeWithOracle A f enc output)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBool) :
    {a | P (a, output (f a)) = true} ∈ NP enc := by
  obtain ⟨fYes, hYes_mem, hYes⟩ := mem_NP_iff_exists_SharpP.mp hA_np
  obtain ⟨fNo, hNo_mem, hNo⟩ := mem_NP_iff_exists_SharpP.mp hA_conp
  obtain ⟨k, m, machine, p, hout⟩ := hf.exists_replayOutput
  have hYes' (q : List Bool) : decide (q ∈ A) = true ↔ 0 < fYes q := by
    simp only [decide_eq_true_eq, hYes q]
  have hNo' (q : List Bool) : decide (q ∈ A) = false ↔ 0 < fNo q := by
    simp only [decide_eq_false_iff_not, ← Set.mem_compl_iff, hNo q]
  let T : α → ℕ := fun a => p.eval (enc a).length
  have hT : ComputableInPolyTime T enc encUnary := by
    dsimp only [T]
    fun_prop
  have hinput : ComputableInPolyTime (fun a : α => enc a) enc encBits :=
    ComputableInPolyTime.id'
  -- weight each transcript by the indicator of `P` on its replayed output
  let F : α × List Bool → ℕ := fun x => if P x then 1 else 0
  have hF : F ∈ SharpP (encPair enc encBits) := SharpP.ite_mem hP SharpP.one_mem SharpP.zero_mem
  refine mem_NP_iff_exists_SharpP.mpr
    ⟨replayWeightedSum machine (fun a => enc a) T fYes fNo F,
      replayWeightedSum_mem_SharpP machine hinput hT hYes_mem hNo_mem hF, fun a => ?_⟩
  rw [replayWeightedSum_pos_iff machine (fun a => enc a) T hYes' hNo' F a, hout a]
  by_cases h : P (a, output (f a)) = true <;> simp [F, h]

/-- **Polynomial-time predicates of word-valued `FP^(NP ∩ coNP)` functions lie in `NP`.** -/
theorem ComputableInPolyTimeWithOracle.mem_NP {f : α → List Bool} {P : α × List Bool → Bool}
    (hA_np : A ∈ NP encBits) (hA_conp : A ∈ coNP encBits)
    (hf : ComputableInPolyTimeWithOracle A f enc encBits)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBool) :
    {a | P (a, f a) = true} ∈ NP enc :=
  hf.encoded_mem_NP hA_np hA_conp hP

/-- **`P^(NP ∩ coNP) ⊆ NP`** [Schöning][Schoening1989], [Arora and Barak, Chapter 3][AroraBarak09].
-/
theorem PWithOracle_subset_NP (hA_np : A ∈ NP encBits) (hA_conp : A ∈ coNP encBits) :
    PWithOracle A enc ⊆ NP enc := by
  rintro L ⟨f, hf, hL⟩
  have hP : ComputableInPolyTime (fun x : α × List Bool => decide (x.2 = [true]))
      (encPair enc encBits) encBool := by fun_prop
  have hmem := hf.encoded_mem_NP hA_np hA_conp hP
  convert hmem using 1
  ext a
  simp [hL a, encBool_apply]

/-- **`P^(NP ∩ coNP) ⊆ coNP`**: `P^A` is closed under complement. -/
theorem PWithOracle_subset_coNP (hA_np : A ∈ NP encBits) (hA_conp : A ∈ coNP encBits) :
    PWithOracle A enc ⊆ coNP enc :=
  fun _ hL => PWithOracle_subset_NP hA_np hA_conp (compl_mem_PWithOracle hL)

/-- **`P^(NP ∩ coNP) ⊆ NP ∩ coNP`.** -/
theorem PWithOracle_subset_NP_inter_coNP (hA_np : A ∈ NP encBits) (hA_conp : A ∈ coNP encBits) :
    PWithOracle A enc ⊆ NP enc ∩ coNP enc :=
  Set.subset_inter (PWithOracle_subset_NP hA_np hA_conp) (PWithOracle_subset_coNP hA_np hA_conp)

/-- **`P^A ⊆ NP ∩ coNP` on bit strings if and only if `A ∈ NP ∩ coNP`.** -/
theorem PWithOracle_subset_NP_inter_coNP_iff :
    PWithOracle A encBits ⊆ NP encBits ∩ coNP encBits ↔
      A ∈ NP encBits ∩ coNP encBits :=
  ⟨fun h => h (mem_PWithOracle_self A), fun h => PWithOracle_subset_NP_inter_coNP h.1 h.2⟩

/-- **The union of `P^A` over `A ∈ NP ∩ coNP` is `NP ∩ coNP`.** -/
theorem iUnion_PWithOracle_NP_inter_coNP :
    (⋃ A ∈ NP encBits ∩ coNP encBits, PWithOracle A encBits) =
      NP encBits ∩ coNP encBits := by
  apply Set.Subset.antisymm
  · exact Set.iUnion₂_subset fun A hA => PWithOracle_subset_NP_inter_coNP hA.1 hA.2
  · intro A hA
    exact Set.mem_iUnion₂.mpr ⟨A, hA, mem_PWithOracle_self A⟩

/-- **`P = NP ∩ coNP` if and only if every `NP ∩ coNP` oracle is low for `P`.** -/
theorem P_eq_NP_inter_coNP_iff_forall_PWithOracle_eq_P :
    P encBits = NP encBits ∩ coNP encBits ↔
      ∀ A ∈ NP encBits ∩ coNP encBits, PWithOracle A encBits = P encBits := by
  constructor
  · intro hP A hA
    exact PWithOracle_eq_P (hP.symm ▸ hA) encBits
  · intro h
    refine Set.Subset.antisymm (Set.subset_inter P_subset_NP P_subset_coNP) (fun A hA => ?_)
    rw [← h A hA]
    exact mem_PWithOracle_self A

/-- **General reduction from `NPWithOracle` collapse to `PWithOracle` on paired encodings.**
If `P^A ⊆ NP` on `encPair enc encBits`, then `NP^A ⊆ NP` on `enc`: an `NP^A` verifier is a `P^A`
language on `(instance, certificate)` pairs, and summing its `#P` witness count over certificates
of polynomial length gives an ordinary `#P` support for the original language. -/
theorem NPWithOracle_subset_NP_of_PWithOracle_subset_NP
    (h : PWithOracle A (encPair enc encBits) ⊆ NP (encPair enc encBits)) :
    NPWithOracle A enc ⊆ NP enc := by
  rintro L ⟨p, V, hV, hL⟩
  have hV_mem : {x : α × List Bool | V x = true} ∈ PWithOracle A (encPair enc encBits) :=
    ⟨V, hV, fun _ => Iff.rfl⟩
  obtain ⟨F, hF, hFV⟩ := mem_NP_iff_exists_SharpP.mp (h hV_mem)
  have hFV' (x : α × List Bool) : 0 < F x ↔ V x = true := (hFV x).symm
  have hr : ComputableInPolyTime (fun a : α => p.eval (enc a).length) enc encUnary := by
    fun_prop
  refine mem_NP_iff_exists_SharpP.mpr ⟨_, SharpP.sum_bits_mem hF hr, fun a => ?_⟩
  rw [Finset.sum_pos_iff, hL a]
  simp only [mem_univ, true_and, hFV']
  constructor
  · rintro ⟨w, hlen, hVw⟩
    have hw : List.ofFn (fun i : Fin (p.eval (enc a).length) => w[i.val]'(by omega)) = w :=
      (List.ofFn_congr hlen.symm _).trans List.ofFn_getElem
    refine ⟨fun i => w[i.val]'(by omega), ?_⟩
    simpa only [hw] using hVw
  · rintro ⟨w, hVw⟩
    exact ⟨List.ofFn w, List.length_ofFn, hVw⟩

/-- **`NP^(NP ∩ coNP) = NP`** [Schöning][Schoening1989], [Arora and Barak, Chapter 3][AroraBarak09]:
an oracle language in `NP ∩ coNP` adds nothing to `NP`, for every instance encoding `enc`. -/
theorem NPWithOracle_eq_NP_of_mem_NP_of_mem_coNP
    (hA_np : A ∈ NP encBits) (hA_conp : A ∈ coNP encBits) (enc : α ↪ List Bool) :
    NPWithOracle A enc = NP enc :=
  Set.Subset.antisymm
    (NPWithOracle_subset_NP_of_PWithOracle_subset_NP (PWithOracle_subset_NP hA_np hA_conp))
    (NP_subset_NPWithOracle A enc)

/-- **Characterization of the first low level `Low₁ = NP ∩ coNP`** [Schöning][Schoening1989]:
`NP^A = NP` on bit strings if and only if `A ∈ NP ∩ coNP`. -/
theorem NPWithOracle_eq_NP_iff :
    NPWithOracle A encBits = NP encBits ↔ A ∈ NP encBits ∩ coNP encBits := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [← h]
      exact PWithOracle_subset_NPWithOracle A encBits (mem_PWithOracle_self A)
    · rw [mem_coNP, ← h]
      exact PWithOracle_subset_NPWithOracle A encBits (mem_PWithOracle_compl_self A)
  · rintro ⟨hA_np, hA_conp⟩
    exact NPWithOracle_eq_NP_of_mem_NP_of_mem_coNP hA_np hA_conp encBits

/-- **`NP^A = NP` for all instance encodings if and only if `A ∈ NP ∩ coNP`.** -/
theorem forall_NPWithOracle_eq_NP_iff :
    (∀ {α : Type} (enc : α ↪ List Bool), NPWithOracle A enc = NP enc) ↔
      A ∈ NP encBits ∩ coNP encBits :=
  ⟨fun h => NPWithOracle_eq_NP_iff.mp (h encBits),
    fun ⟨hA_np, hA_conp⟩ _ enc => NPWithOracle_eq_NP_of_mem_NP_of_mem_coNP hA_np hA_conp enc⟩

/-- **The union of `NP^A` over `A ∈ NP ∩ coNP` is `NP`.** -/
theorem iUnion_NPWithOracle_NP_inter_coNP (enc : α ↪ List Bool) :
    (⋃ A ∈ NP encBits ∩ coNP encBits, NPWithOracle A enc) = NP enc :=
  (Set.iUnion₂_congr fun _ hA => NPWithOracle_eq_NP_of_mem_NP_of_mem_coNP hA.1 hA.2 enc).trans
    (Set.biUnion_const (s := NP encBits ∩ coNP encBits)
      ⟨∅, P_subset_NP empty_mem_P, P_subset_coNP empty_mem_P⟩ _)

/-- **`P = NP` if and only if every `NP` oracle is low for `P`.** -/
theorem P_eq_NP_iff_forall_PWithOracle_eq_P :
    P encBits = NP encBits ↔ ∀ A ∈ NP encBits, PWithOracle A encBits = P encBits := by
  constructor
  · intro hP A hA
    exact PWithOracle_eq_P (hP.symm ▸ hA) encBits
  · intro h
    refine Set.Subset.antisymm P_subset_NP (fun A hA => ?_)
    rw [← h A hA]
    exact mem_PWithOracle_self A

/-- **`NP = coNP` if and only if every `NP` oracle is low for `NP` (`NP^NP = NP`)**
[Arora and Barak, Chapter 3][AroraBarak09]. -/
theorem NP_eq_coNP_iff_forall_NPWithOracle_eq_NP :
    NP encBits = coNP encBits ↔ ∀ A ∈ NP encBits, NPWithOracle A encBits = NP encBits := by
  constructor
  · intro hNP A hA
    exact NPWithOracle_eq_NP_of_mem_NP_of_mem_coNP hA (hNP ▸ hA) encBits
  · intro h
    ext A
    constructor
    · intro hA
      exact (NPWithOracle_eq_NP_iff.mp (h A hA)).2
    · intro hA
      have hAc_conp : Aᶜ ∈ coNP encBits := (NPWithOracle_eq_NP_iff.mp (h Aᶜ hA)).2
      rwa [mem_coNP, compl_compl] at hAc_conp

/-! ### Oracle lowness of `UP ∩ coUP` for `P` -/

open Classical in
/-- **Polynomial-time predicates of encoded `FP^(UP ∩ coUP)` outputs lie in `UP`.** When `A` and
`Aᶜ` have unambiguous verifiers, the canonical oracle transcript is the unique transcript with a
valid step-by-step witness tuple, and its witness tuple is unique. -/
theorem ComputableInPolyTimeWithOracle.encoded_mem_UP {f : α → β} {P : α × List Bool → Bool}
    (hA_up : A ∈ UP encBits) (hA_coup : A ∈ coUP encBits)
    (hf : ComputableInPolyTimeWithOracle A f enc output)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBool) :
    {a | P (a, output (f a)) = true} ∈ UP enc := by
  obtain ⟨fYes, hYes_mem, hYes_le, hYes_iff⟩ := hA_up
  obtain ⟨fNo, hNo_mem, hNo_le, hNo_iff⟩ := hA_coup
  obtain ⟨k, m, machine, p, hout⟩ := hf.exists_replayOutput
  have hYes' (q : List Bool) : decide (q ∈ A) = true ↔ 0 < fYes q := by
    have hle := hYes_le q
    rw [show (0 < fYes q) ↔ fYes q = 1 by omega]
    simp only [decide_eq_true_eq, hYes_iff q]
  have hNo' (q : List Bool) : decide (q ∈ A) = false ↔ 0 < fNo q := by
    have hle := hNo_le q
    rw [show (0 < fNo q) ↔ fNo q = 1 by omega]
    simp only [decide_eq_false_iff_not, ← Set.mem_compl_iff, hNo_iff q]
  let T : α → ℕ := fun a => p.eval (enc a).length
  have hT : ComputableInPolyTime T enc encUnary := by
    dsimp only [T]
    fun_prop
  have hinput : ComputableInPolyTime (fun a : α => enc a) enc encBits :=
    ComputableInPolyTime.id'
  -- weight each transcript by the indicator of `P` on its replayed output
  let F : α × List Bool → ℕ := fun x => if P x then 1 else 0
  have hF : F ∈ SharpP (encPair enc encBits) := SharpP.ite_mem hP SharpP.one_mem SharpP.zero_mem
  have heval (a : α) : replayWeightedSum machine (fun a => enc a) T fYes fNo F a =
      if P (a, output (f a)) then 1 else 0 := by
    rw [replayWeightedSum_eq_of_le_one machine (fun a => enc a) T hYes_le hNo_le hYes' hNo' F a,
      hout a]
  refine ⟨replayWeightedSum machine (fun a => enc a) T fYes fNo F,
    replayWeightedSum_mem_SharpP machine hinput hT hYes_mem hNo_mem hF,
    fun a => ?_, fun a => ?_⟩
  · rw [heval a]
    split_ifs <;> omega
  · rw [heval a]
    by_cases h : P (a, output (f a)) = true <;> simp [h]

/-- **Polynomial-time predicates of word-valued `FP^(UP ∩ coUP)` functions lie in `UP`.** -/
theorem ComputableInPolyTimeWithOracle.mem_UP {f : α → List Bool} {P : α × List Bool → Bool}
    (hA_up : A ∈ UP encBits) (hA_coup : A ∈ coUP encBits)
    (hf : ComputableInPolyTimeWithOracle A f enc encBits)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBool) :
    {a | P (a, f a) = true} ∈ UP enc :=
  hf.encoded_mem_UP hA_up hA_coup hP

/-- **`P^(UP ∩ coUP) ⊆ UP`.** -/
theorem PWithOracle_subset_UP (hA_up : A ∈ UP encBits) (hA_coup : A ∈ coUP encBits) :
    PWithOracle A enc ⊆ UP enc := by
  rintro L ⟨f, hf, hL⟩
  have hP : ComputableInPolyTime (fun x : α × List Bool => decide (x.2 = [true]))
      (encPair enc encBits) encBool := by fun_prop
  have hmem := hf.encoded_mem_UP hA_up hA_coup hP
  convert hmem using 1
  ext a
  simp [hL a, encBool_apply]

/-- **`P^(UP ∩ coUP) ⊆ coUP`**: `P^A` is closed under complement. -/
theorem PWithOracle_subset_coUP (hA_up : A ∈ UP encBits) (hA_coup : A ∈ coUP encBits) :
    PWithOracle A enc ⊆ coUP enc :=
  fun _ hL => PWithOracle_subset_UP hA_up hA_coup (compl_mem_PWithOracle hL)

/-- **`P^(UP ∩ coUP) ⊆ UP ∩ coUP`.** -/
theorem PWithOracle_subset_UP_inter_coUP (hA_up : A ∈ UP encBits) (hA_coup : A ∈ coUP encBits) :
    PWithOracle A enc ⊆ UP enc ∩ coUP enc :=
  Set.subset_inter (PWithOracle_subset_UP hA_up hA_coup) (PWithOracle_subset_coUP hA_up hA_coup)

/-- **`P^A ⊆ UP ∩ coUP` on bit strings if and only if `A ∈ UP ∩ coUP`.** -/
theorem PWithOracle_subset_UP_inter_coUP_iff :
    PWithOracle A encBits ⊆ UP encBits ∩ coUP encBits ↔
      A ∈ UP encBits ∩ coUP encBits :=
  ⟨fun h => h (mem_PWithOracle_self A), fun h => PWithOracle_subset_UP_inter_coUP h.1 h.2⟩

/-- **The union of `P^A` over `A ∈ UP ∩ coUP` is `UP ∩ coUP`.** -/
theorem iUnion_PWithOracle_UP_inter_coUP :
    (⋃ A ∈ UP encBits ∩ coUP encBits, PWithOracle A encBits) =
      UP encBits ∩ coUP encBits := by
  apply Set.Subset.antisymm
  · exact Set.iUnion₂_subset fun A hA => PWithOracle_subset_UP_inter_coUP hA.1 hA.2
  · intro A hA
    exact Set.mem_iUnion₂.mpr ⟨A, hA, mem_PWithOracle_self A⟩

end Cslib.Complexity
