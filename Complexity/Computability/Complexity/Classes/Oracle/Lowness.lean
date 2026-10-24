/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Oracle.Closure
public import Complexity.Computability.Complexity.Classes.Oracle.PolyTime
public import Complexity.Computability.Complexity.Classes.UP
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.Oracle
import Complexity.Computability.Complexity.Classes.P.Complement
import Complexity.Computability.Complexity.Classes.SharpP.Aggregation
import Complexity.Computability.Complexity.Classes.SharpP.PolyTime
import Complexity.Computability.Complexity.Classes.SharpP.Products
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

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
2. Multiplying these step factors over `i < |answers|` produces a `#P` path count that is positive
   if and only if `answers` equals the canonical transcript `machine.oracleReplies`. When `fYes`
   and `fNo` are bounded by `1` (`A ∈ UP ∩ coUP`), the path count is `1` on the canonical
   transcript and `0` on every other transcript.
3. Summing over all transcript words of the polynomial clock length therefore certifies any
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
  refine ⟨fun a => !f a, hf.map (.of_tidy (by fun_prop)), fun a => ?_⟩
  rw [Set.mem_compl_iff, hL a]
  cases h : f a <;> simp [h]

/-- **`P` relative to an oracle is closed under intersection.** -/
theorem inter_mem_PWithOracle {L₁ L₂ : Set α} (h₁ : L₁ ∈ PWithOracle A enc)
    (h₂ : L₂ ∈ PWithOracle A enc) : L₁ ∩ L₂ ∈ PWithOracle A enc := by
  obtain ⟨f₁, hf₁, hL₁⟩ := h₁
  obtain ⟨f₂, hf₂, hL₂⟩ := h₂
  refine ⟨fun a => f₁ a && f₂ a, (hf₁.prod hf₂).map (g := fun p => p.1 && p.2)
    (.of_tidy (by fun_prop)),
    fun a => ?_⟩
  rw [Set.mem_inter_iff, hL₁ a, hL₂ a, Bool.and_eq_true]

/-- **`P` relative to an oracle is closed under union.** -/
theorem union_mem_PWithOracle {L₁ L₂ : Set α} (h₁ : L₁ ∈ PWithOracle A enc)
    (h₂ : L₂ ∈ PWithOracle A enc) : L₁ ∪ L₂ ∈ PWithOracle A enc := by
  obtain ⟨f₁, hf₁, hL₁⟩ := h₁
  obtain ⟨f₂, hf₂, hL₂⟩ := h₂
  refine ⟨fun a => f₁ a || f₂ a, (hf₁.prod hf₂).map (g := fun p => p.1 || p.2)
    (.of_tidy (by fun_prop)),
    fun a => ?_⟩
  rw [Set.mem_union, hL₁ a, hL₂ a, Bool.or_eq_true]

/-- **`P` relative to `A` contains `Aᶜ`.** -/
theorem mem_PWithOracle_compl_self (A : Set (List Bool)) : Aᶜ ∈ PWithOracle A encBits :=
  compl_mem_PWithOracle (mem_PWithOracle_self A)

/-! ### Step-certified oracle replay in `#P` -/

section Replay

variable {k : ℕ} {Control Operation : Type} [DecidableEq Operation]

private theorem ofFn_getElem_of_length_eq {n : ℕ} (L : List Bool) (h : L.length = n) :
    List.ofFn (fun i : Fin n => L[i.val]'(by omega)) = L :=
  List.ext_getElem (by simp [h]) fun i _ _ => by simp

private theorem nat_prod_pos_iff {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    0 < ∏ i ∈ s, f i ↔ ∀ i ∈ s, 0 < f i := by
  simp only [Nat.pos_iff_ne_zero, ne_eq, Finset.prod_eq_zero_iff, not_exists, not_and]

/-- The `#P` factor certifying instruction `x.2` of transcript `x.1.2` on instance `x.1.1`. -/
private def replayStepFactor (machine : MultiTapePTM k Bool Control Operation)
    (input : α → List Bool) (fYes fNo : List Bool → ℕ)
    (x : (α × List Bool) × ℕ) : ℕ :=
  let cfg := machine.replayPrefix (input x.1.1) x.1.2 x.2
  if (machine.pendingQuery cfg).isSome then
    let q := machine.pendingRequest cfg
    if x.1.2.getD x.2 false then fYes q else fNo q
  else
    if x.1.2.getD x.2 false then 0 else 1

/-- The `#P` product certifying all instructions of transcript `x.2` on instance `x.1`. -/
private def replayPathCount (machine : MultiTapePTM k Bool Control Operation)
    (input : α → List Bool) (fYes fNo : List Bool → ℕ)
    (x : α × List Bool) : ℕ :=
  ∏ i ∈ range x.2.length, replayStepFactor machine input fYes fNo (x, i)

/-- The `#P` sum over all transcripts of length `T a` whose replayed output satisfies `P`. -/
private def replayAcceptCount (machine : MultiTapePTM k Bool Control Operation)
    (input : α → List Bool) (T : α → ℕ) (fYes fNo : List Bool → ℕ)
    (P : α × List Bool → Bool) (a : α) : ℕ :=
  ∑ w : Fin (T a) → Bool,
    replayPathCount machine input fYes fNo (a, List.ofFn w) *
      if P (a, machine.replayOutput (input a) (List.ofFn w)) then 1 else 0

private theorem replayStepFactor_mem_SharpP [Finite Control] [Finite Operation]
    (machine : MultiTapePTM k Bool Control Operation) {input : α → List Bool}
    {fYes fNo : List Bool → ℕ}
    (hinput : ComputableTidilyInPolyTime input enc encBits)
    (hYes : fYes ∈ SharpP encBits) (hNo : fNo ∈ SharpP encBits) :
    replayStepFactor machine input fYes fNo ∈ SharpP (encPair (encPair enc encBits) encUnary) := by
  let _ := Fintype.ofFinite Operation
  let cfg : (α × List Bool) × ℕ → FiniteConfig k Bool Control Operation :=
    fun x => machine.replayPrefix (input x.1.1) x.1.2 x.2
  have hcfg : ComputableTidilyInPolyTime cfg
      (encPair (encPair enc encBits) encUnary) encFiniteConfig :=
    machine.replayPrefix_pt.comp (g := fun x : (α × List Bool) × ℕ =>
      ((input x.1.1, x.1.2), x.2)) (by fun_prop)
  have hquery : ComputableTidilyInPolyTime
      (fun x => (machine.pendingQuery (cfg x)).isSome)
      (encPair (encPair enc encBits) encUnary) encBool :=
    (ComputableTidilyInPolyTime.of_finite Option.isSome).comp
      (machine.pendingQuery_pt.comp hcfg)
  have hreq : ComputableTidilyInPolyTime
      (fun x => machine.pendingRequest (cfg x))
      (encPair (encPair enc encBits) encUnary) encBits :=
    machine.pendingRequest_pt.comp hcfg
  have hbit : ComputableTidilyInPolyTime
      (fun x : (α × List Bool) × ℕ => x.1.2.getD x.2 false)
      (encPair (encPair enc encBits) encUnary) encBool := by fun_prop
  exact SharpP.ite_mem (.of_tidy hquery)
    (SharpP.ite_mem (.of_tidy hbit) (SharpP.comp_mem hYes (.of_tidy hreq))
      (SharpP.comp_mem hNo (.of_tidy hreq)))
    (SharpP.ite_mem (.of_tidy hbit) SharpP.zero_mem SharpP.one_mem)

private theorem replayPathCount_mem_SharpP [Finite Control] [Finite Operation]
    (machine : MultiTapePTM k Bool Control Operation) {input : α → List Bool}
    {fYes fNo : List Bool → ℕ}
    (hinput : ComputableTidilyInPolyTime input enc encBits)
    (hYes : fYes ∈ SharpP encBits) (hNo : fNo ∈ SharpP encBits) :
    replayPathCount machine input fYes fNo ∈ SharpP (encPair enc encBits) :=
  SharpP.prod_range_mem (replayStepFactor_mem_SharpP machine hinput hYes hNo)
    (r := fun x : α × List Bool => x.2.length) (.of_tidy (by fun_prop))

private theorem replayAcceptCount_mem_SharpP [Finite Control] [Finite Operation]
    (machine : MultiTapePTM k Bool Control Operation) {input : α → List Bool}
    {T : α → ℕ} {fYes fNo : List Bool → ℕ} {P : α × List Bool → Bool}
    (hinput : ComputableTidilyInPolyTime input enc encBits)
    (hT : ComputableTidilyInPolyTime T enc encUnary)
    (hYes : fYes ∈ SharpP encBits) (hNo : fNo ∈ SharpP encBits)
    (hP : ComputableTidilyInPolyTime P (encPair enc encBits) encBool) :
    replayAcceptCount machine input T fYes fNo P ∈ SharpP enc := by
  have hpath := replayPathCount_mem_SharpP machine hinput hYes hNo
  have hout : ComputableTidilyInPolyTime
      (fun x : α × List Bool => P (x.1, machine.replayOutput (input x.1) x.2))
      (encPair enc encBits) encBool := by
    have hpair : ComputableTidilyInPolyTime
        (fun x : α × List Bool => (input x.1, x.2))
        (encPair enc encBits) (encPair encBits encBits) := by fun_prop
    exact hP.comp ((ComputableTidilyInPolyTime.fst enc encBits).prod
      (machine.replayOutput_pt.comp hpair))
  have hmask : (fun x : α × List Bool =>
      if P (x.1, machine.replayOutput (input x.1) x.2) then 1 else 0) ∈
      SharpP (encPair enc encBits) :=
    SharpP.ite_mem (.of_tidy hout) SharpP.one_mem SharpP.zero_mem
  exact SharpP.sum_bits_mem (SharpP.mul_mem hpath hmask) (.of_tidy hT)

private theorem replayStepFactor_pos_iff (machine : MultiTapePTM k Bool Control Operation)
    (input : α → List Bool) {fYes fNo : List Bool → ℕ} {g : List Bool → Bool}
    (hYes : ∀ q, g q = true ↔ 0 < fYes q) (hNo : ∀ q, g q = false ↔ 0 < fNo q)
    (a : α) (answers : List Bool) (i : ℕ) :
    0 < replayStepFactor machine input fYes fNo ((a, answers), i) ↔
      answers.getD i false =
        let cfg := machine.replayPrefix (input a) answers i
        if (machine.pendingQuery cfg).isSome then g (machine.pendingRequest cfg) else false := by
  unfold replayStepFactor
  dsimp only
  set cfg := machine.replayPrefix (input a) answers i
  cases hq : (machine.pendingQuery cfg).isSome
  · cases hb : answers.getD i false <;> simp
  · cases hb : answers.getD i false
    · simp [← hNo (machine.pendingRequest cfg)]
    · simp [← hYes (machine.pendingRequest cfg)]

private theorem take_eq_take_oracleReplies_of_forall_getD
    (machine : MultiTapePTM k Bool Control Operation) (g : List Bool → Bool)
    (input answers : List Bool)
    (h : ∀ i < answers.length, answers.getD i false =
      let cfg := machine.replayPrefix input answers i
      if (machine.pendingQuery cfg).isSome then g (machine.pendingRequest cfg) else false) :
    ∀ m ≤ answers.length,
      answers.take m = (machine.oracleReplies g answers.length input).take m := by
  set oracle := machine.oracleReplies g answers.length input
  have hlen_or : oracle.length = answers.length :=
    machine.length_oracleReplies g answers.length input
  intro m hm
  induction m with
  | zero => rfl
  | succ m ih =>
    have hm_lt : m < answers.length := Nat.lt_of_succ_le hm
    have hm_or : m < oracle.length := hlen_or ▸ hm_lt
    have ih_m : answers.take m = oracle.take m := ih hm_lt.le
    have hcfg : machine.replayPrefix input answers m =
        machine.replayPrefix input oracle m := by
      simp only [replayPrefix, ih_m]
    have hbit : answers[m] = oracle[m] := by
      rw [← List.getD_eq_getElem answers false hm_lt,
        ← List.getD_eq_getElem oracle false hm_or,
        h m hm_lt, machine.getD_oracleReplies g answers.length input m hm_lt, hcfg]
    calc
      answers.take (m + 1) = answers.take m ++ [answers[m]] :=
        List.take_succ_eq_append_getElem hm_lt
      _ = oracle.take m ++ [oracle[m]] := by rw [ih_m, hbit]
      _ = oracle.take (m + 1) := (List.take_succ_eq_append_getElem hm_or).symm

private theorem replayPathCount_pos_iff (machine : MultiTapePTM k Bool Control Operation)
    (input : α → List Bool) {fYes fNo : List Bool → ℕ} {g : List Bool → Bool}
    (hYes : ∀ q, g q = true ↔ 0 < fYes q) (hNo : ∀ q, g q = false ↔ 0 < fNo q)
    (a : α) (answers : List Bool) :
    0 < replayPathCount machine input fYes fNo (a, answers) ↔
      answers = machine.oracleReplies g answers.length (input a) := by
  unfold replayPathCount
  rw [nat_prod_pos_iff]
  simp only [mem_range,
    replayStepFactor_pos_iff machine input hYes hNo a answers]
  constructor
  · intro h
    have htake := take_eq_take_oracleReplies_of_forall_getD machine g (input a) answers h
      answers.length le_rfl
    have hlen : (machine.oracleReplies g answers.length (input a)).length = answers.length :=
      machine.length_oracleReplies g answers.length (input a)
    rwa [List.take_length, List.take_of_length_le hlen.le] at htake
  · intro h i hi
    have hstep := machine.getD_oracleReplies g answers.length (input a) i hi
    rwa [← h] at hstep

private theorem replayAcceptCount_pos_iff (machine : MultiTapePTM k Bool Control Operation)
    (input : α → List Bool) (T : α → ℕ) {fYes fNo : List Bool → ℕ} {g : List Bool → Bool}
    (hYes : ∀ q, g q = true ↔ 0 < fYes q) (hNo : ∀ q, g q = false ↔ 0 < fNo q)
    (P : α × List Bool → Bool) (a : α) :
    0 < replayAcceptCount machine input T fYes fNo P a ↔
      P (a, machine.replayOutput (input a) (machine.oracleReplies g (T a) (input a))) = true := by
  unfold replayAcceptCount
  rw [Finset.sum_pos_iff]
  simp only [mem_univ, true_and, CanonicallyOrderedAdd.mul_pos,
    replayPathCount_pos_iff machine input hYes hNo, List.length_ofFn]
  constructor
  · rintro ⟨w, hw, hP⟩
    rw [← hw]
    cases h : P (a, machine.replayOutput (input a) (List.ofFn w))
    · simp [h] at hP
    · rfl
  · intro hP
    have hlen : (machine.oracleReplies g (T a) (input a)).length = T a :=
      machine.length_oracleReplies g (T a) (input a)
    have hw₀ := ofFn_getElem_of_length_eq (machine.oracleReplies g (T a) (input a)) hlen
    refine ⟨fun i => (machine.oracleReplies g (T a) (input a))[i.val]'(by omega), hw₀, ?_⟩
    rw [hw₀, hP]
    decide

private theorem replayStepFactor_le_one (machine : MultiTapePTM k Bool Control Operation)
    (input : α → List Bool) {fYes fNo : List Bool → ℕ}
    (hYes_le : ∀ q, fYes q ≤ 1) (hNo_le : ∀ q, fNo q ≤ 1)
    (x : (α × List Bool) × ℕ) :
    replayStepFactor machine input fYes fNo x ≤ 1 := by
  unfold replayStepFactor
  dsimp only
  split_ifs <;> first | exact hYes_le _ | exact hNo_le _ | omega

private theorem replayPathCount_le_one (machine : MultiTapePTM k Bool Control Operation)
    (input : α → List Bool) {fYes fNo : List Bool → ℕ}
    (hYes_le : ∀ q, fYes q ≤ 1) (hNo_le : ∀ q, fNo q ≤ 1)
    (x : α × List Bool) :
    replayPathCount machine input fYes fNo x ≤ 1 :=
  Finset.prod_le_one fun i _ =>
    replayStepFactor_le_one machine input hYes_le hNo_le (x, i)

private theorem replayAcceptCount_eq_ite_of_le_one
    (machine : MultiTapePTM k Bool Control Operation)
    (input : α → List Bool) (T : α → ℕ) {fYes fNo : List Bool → ℕ} {g : List Bool → Bool}
    (hYes_le : ∀ q, fYes q ≤ 1) (hNo_le : ∀ q, fNo q ≤ 1)
    (hYes : ∀ q, g q = true ↔ 0 < fYes q) (hNo : ∀ q, g q = false ↔ 0 < fNo q)
    (P : α × List Bool → Bool) (a : α) :
    replayAcceptCount machine input T fYes fNo P a =
      if P (a, machine.replayOutput (input a) (machine.oracleReplies g (T a) (input a))) then 1
      else 0 := by
  have hlen : (machine.oracleReplies g (T a) (input a)).length = T a :=
    machine.length_oracleReplies g (T a) (input a)
  let w₀ : Fin (T a) → Bool :=
    fun i => (machine.oracleReplies g (T a) (input a))[i.val]'(by omega)
  have hw₀ : List.ofFn w₀ = machine.oracleReplies g (T a) (input a) :=
    ofFn_getElem_of_length_eq (machine.oracleReplies g (T a) (input a)) hlen
  unfold replayAcceptCount
  rw [Finset.sum_eq_single w₀]
  · have hpos : 0 < replayPathCount machine input fYes fNo (a, List.ofFn w₀) := by
      rw [replayPathCount_pos_iff machine input hYes hNo, List.length_ofFn]
      exact hw₀
    have hle := replayPathCount_le_one machine input hYes_le hNo_le (a, List.ofFn w₀)
    have heq : replayPathCount machine input fYes fNo (a, List.ofFn w₀) = 1 := by omega
    rw [heq, one_mul, hw₀]
  · intro w _ hw
    have hnot : ¬0 < replayPathCount machine input fYes fNo (a, List.ofFn w) := by
      rw [replayPathCount_pos_iff machine input hYes hNo, List.length_ofFn, ← hw₀]
      exact fun h => hw (List.ofFn_injective h)
    have hz : replayPathCount machine input fYes fNo (a, List.ofFn w) = 0 := by omega
    rw [hz, zero_mul]
  · intro hmem
    exact False.elim (hmem (mem_univ w₀))

end Replay

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
  obtain ⟨program, hcert, hprogram⟩ := hf
  obtain ⟨k, m, machine, c, d, hrun⟩ := hcert.exists_fin_run_pure_false
  let g : List Bool → Bool := fun q => decide (q ∈ A)
  have hYes' (q : List Bool) : g q = true ↔ 0 < fYes q := by
    simp only [g, decide_eq_true_eq, hYes q]
  have hNo' (q : List Bool) : g q = false ↔ 0 < fNo q := by
    simp only [g, decide_eq_false_iff_not, ← Set.mem_compl_iff, hNo q]
  let T : α → ℕ := fun a => c * ((enc a).length + 1) ^ d
  have hT : ComputableTidilyInPolyTime T enc encUnary :=
    ((ComputableTidilyInPolyTime.unary_eval (Polynomial.C c * (Polynomial.X + 1) ^ d)).comp
      (ComputableTidilyInPolyTime.encoding_length enc)).of_enc_eq fun a => by simp [T]
  have hinput : ComputableTidilyInPolyTime (fun a : α => enc a) enc encBits :=
    ComputableTidilyInPolyTime.id'
  refine mem_NP_iff_exists_SharpP.mpr
    ⟨replayAcceptCount machine (fun a => enc a) T fYes fNo P,
      replayAcceptCount_mem_SharpP machine hinput hT hYes_mem hNo_mem hP.tidy, fun a => ?_⟩
  rw [replayAcceptCount_pos_iff machine (fun a => enc a) T hYes' hNo' P a,
    machine.replayOutput_oracleReplies g (T a) (enc a)]
  have hrun_a := hrun a (languageOracle A)
  rw [hprogram a] at hrun_a
  change P (a, output (f a)) = true ↔ _
  rw [← hrun_a]
  rfl

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
      (encPair enc encBits) encBool := .of_tidy (by fun_prop)
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
  have hr : ComputableTidilyInPolyTime (fun a : α => p.eval (enc a).length) enc encUnary := by
    fun_prop
  refine mem_NP_iff_exists_SharpP.mpr ⟨_, SharpP.sum_bits_mem hF (.of_tidy hr), fun a => ?_⟩
  rw [Finset.sum_pos_iff, hL a]
  simp only [mem_univ, true_and, hFV']
  constructor
  · rintro ⟨w, hlen, hVw⟩
    have hw := ofFn_getElem_of_length_eq w hlen
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
    (⋃ A ∈ NP encBits ∩ coNP encBits, NPWithOracle A enc) = NP enc := by
  apply Set.Subset.antisymm
  · exact Set.iUnion₂_subset fun A hA =>
      (NPWithOracle_eq_NP_of_mem_NP_of_mem_coNP hA.1 hA.2 enc).le
  · intro L hL
    have hempty : (∅ : Set (List Bool)) ∈ P encBits :=
      ⟨fun _ => false, .const false, fun _ => by simp⟩
    refine Set.mem_iUnion₂.mpr ⟨∅, ⟨P_subset_NP hempty, P_subset_coNP hempty⟩, ?_⟩
    exact NP_subset_NPWithOracle ∅ enc hL

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
  obtain ⟨program, hcert, hprogram⟩ := hf
  obtain ⟨k, m, machine, c, d, hrun⟩ := hcert.exists_fin_run_pure_false
  let g : List Bool → Bool := fun q => decide (q ∈ A)
  have hYes' (q : List Bool) : g q = true ↔ 0 < fYes q := by
    have hle := hYes_le q
    rw [show (0 < fYes q) ↔ fYes q = 1 by omega]
    simp only [g, decide_eq_true_eq, hYes_iff q]
  have hNo' (q : List Bool) : g q = false ↔ 0 < fNo q := by
    have hle := hNo_le q
    rw [show (0 < fNo q) ↔ fNo q = 1 by omega]
    simp only [g, decide_eq_false_iff_not, ← Set.mem_compl_iff, hNo_iff q]
  let T : α → ℕ := fun a => c * ((enc a).length + 1) ^ d
  have hT : ComputableTidilyInPolyTime T enc encUnary :=
    ((ComputableTidilyInPolyTime.unary_eval (Polynomial.C c * (Polynomial.X + 1) ^ d)).comp
      (ComputableTidilyInPolyTime.encoding_length enc)).of_enc_eq fun a => by simp [T]
  have hinput : ComputableTidilyInPolyTime (fun a : α => enc a) enc encBits :=
    ComputableTidilyInPolyTime.id'
  refine ⟨replayAcceptCount machine (fun a => enc a) T fYes fNo P,
    replayAcceptCount_mem_SharpP machine hinput hT hYes_mem hNo_mem hP.tidy,
    fun a => ?_, fun a => ?_⟩
  · rw [replayAcceptCount_eq_ite_of_le_one machine (fun a => enc a) T hYes_le hNo_le hYes' hNo' P a]
    split_ifs <;> omega
  · rw [replayAcceptCount_eq_ite_of_le_one machine (fun a => enc a) T hYes_le hNo_le hYes' hNo' P a,
      machine.replayOutput_oracleReplies g (T a) (enc a)]
    have hrun_a := hrun a (languageOracle A)
    rw [hprogram a] at hrun_a
    change P (a, output (f a)) = true ↔ _
    rw [← hrun_a]
    change P (a, OracleComp.interpret (m := Id) (fun q => [g q.2])
      (machine.run (pure false) (fun op word => OracleComp.query (op, word)) (T a) (enc a))) =
        true ↔ _
    cases P (a, OracleComp.interpret (m := Id) (fun q => [g q.2])
      (machine.run (pure false) (fun op word => OracleComp.query (op, word)) (T a) (enc a))) <;>
      decide

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
      (encPair enc encBits) encBool := .of_tidy (by fun_prop)
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
