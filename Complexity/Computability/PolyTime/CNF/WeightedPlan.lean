/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.PolyTime.CNF.WeightedQuery
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import all Complexity.Logics.Propositional.CNF.WeightedExecution
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Foundations.Data.List.OfFn

/-!
# Complete binary weighted counting-plan construction

Tagged direct answers or two ordinary CNFs with their declared variable count,
for [ChenJiangZhu2027], Section 7.1, Theorem 7.1, PDF pp. 23–24.
The demand cap is fixed; declared width/indices are unary and all weights,
targets and direct counts are binary. The external counting-oracle runtime is
separate from polynomial-time/space construction of the complete output.
-/

public section

namespace Cslib.Logic.PL.WeightedRow.BinaryPlan

open Turing.MultiTapeTM
open scoped BigOperators
open BinaryQuery

/-- A binary direct count, or a declared variable count and the two ordinary CNFs. -/
abbrev Output := ℕ ⊕ (ℕ × (CNF ℕ × CNF ℕ))

/-- The tag and every declared variable/literal/count bit are included in the encoding. -/
@[expose] def encOutput : Output ↪ List Bool :=
  encSum encNat (encPair encUnary (encPair encCNF encCNF))

/-- Test one constant assignment directly on the original binary occurrences. -/
@[expose] def constantTest (rows : List BinaryNormalization.Input) (b : Bool) : Bool :=
  rows.all fun (es, target) =>
    (es.map fun (_, (s, w)) => if b = s then w else 0).sum == target

/-- At most two assignments are checked; zero variables have only one assignment. -/
@[expose] def smallAnswer (n : ℕ) (rows : List BinaryNormalization.Input) : ℕ :=
  if n = 0 then if constantTest rows false then 1 else 0
  else (if constantTest rows false then 1 else 0) + (if constantTest rows true then 1 else 0)

/-- Branch assembly from computed diagnostics; `compile` supplies these fields itself. -/
@[expose] def largeOutput (d n : ℕ) (rows : List BinaryNormalization.Input)
    (reject : Bool) (ids : List ℕ) (consistent boolean : Bool) : Output :=
  if reject then .inl 0
  else if (BinaryNormalization.materialize n rows).1.length = 0 then .inl (2 ^ n)
  else if consistent then
    if ids.length = n then .inl (if boolean then 1 else 0)
    else if ids.length = 0 then .inl (2 ^ n)
    else .inr (n + ids.length - 1,
      (selectedQuery d n rows false, selectedQuery d n rows true))
  else .inl 0

/-- Execute the whole all-cases plan from original occurrence records. No basis, rank,
answer or resource conclusion is supplied. No assignment enumeration occurs at large n. -/
@[expose] def compile (d n : ℕ) (rows : List BinaryNormalization.Input) : Output :=
  if n ≤ 1 then .inl (smallAnswer n rows)
  else
    let (reject, (ids, (consistent, boolean))) := BinaryNormalization.analyze n rows
    largeOutput d n rows reject ids consistent boolean

/-- The small-input scan includes every binary addition and comparison. -/
@[fun_prop] theorem constantTest_polytime :
    ComputableInPolyTime (fun p : List BinaryNormalization.Input × Bool => constantTest p.1 p.2)
      (encPair (encList BinaryNormalization.encInput) encBool) encBool := by
  unfold constantTest
  fun_prop

/-- The one/two-assignment direct branch is uniformly polynomial on explicit binary input. -/
@[fun_prop] theorem smallAnswer_polytime :
    ComputableInPolyTime (fun p : ℕ × List BinaryNormalization.Input => smallAnswer p.1 p.2)
      (encPair encUnary (encList BinaryNormalization.encInput)) encNat := by
  unfold smallAnswer
  fun_prop

private theorem largeOutput_polytime (d : ℕ) {α : Type} {enc : α ↪ List Bool}
    {n : α → ℕ} {rows : α → List BinaryNormalization.Input}
    {reject consistent boolean : α → Bool} {ids : α → List ℕ}
    (hn : ComputableInPolyTime n enc encUnary)
    (hr : ComputableInPolyTime rows enc (encList BinaryNormalization.encInput))
    (hre : ComputableInPolyTime reject enc encBool)
    (hi : ComputableInPolyTime ids enc (encList encUnary))
    (hc : ComputableInPolyTime consistent enc encBool)
    (hb : ComputableInPolyTime boolean enc encBool) :
    ComputableInPolyTime
      (fun x => largeOutput d (n x) (rows x) (reject x) (ids x) (consistent x) (boolean x))
      enc encOutput := by
  have hp : ComputableInPolyTime (fun x => (2 : ℕ) ^ n x) enc encNat :=
    (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.binary_pow).comp
      ((ComputableInPolyTime.const 2).prod hn)
  have hf := (selectedQuery_polytime d).comp ((hn.prod hr).prod (ComputableInPolyTime.const false))
  have ht := (selectedQuery_polytime d).comp ((hn.prod hr).prod (ComputableInPolyTime.const true))
  have hv : ComputableInPolyTime (fun x => n x + (ids x).length - 1) enc encUnary := by fun_prop
  have hquery := (ComputableInPolyTime.sumInr encNat
    (encPair encUnary (encPair encCNF encCNF))).comp (hv.prod (hf.prod ht))
  have hpow := (ComputableInPolyTime.sumInl encNat
    (encPair encUnary (encPair encCNF encCNF))).comp hp
  have hbool : ComputableInPolyTime (fun x => if boolean x then (1 : ℕ) else 0) enc encNat :=
    hb.ite' (ComputableInPolyTime.const 1) (ComputableInPolyTime.const 0)
  have hbtag := (ComputableInPolyTime.sumInl encNat
    (encPair encUnary (encPair encCNF encCNF))).comp hbool
  have hzero : ComputableInPolyTime (fun _ : α => (Sum.inl 0 : Output)) enc encOutput :=
    ComputableInPolyTime.const _
  have hm := BinaryNormalization.materialize_polytime.comp (hn.prod hr)
  have he : ComputableInPolyTime
      (fun x => decide ((BinaryNormalization.materialize (n x) (rows x)).1.length = 0))
      enc encBool := by fun_prop
  have hfull : ComputableInPolyTime (fun x => decide ((ids x).length = n x))
      enc encBool := by fun_prop
  have hz : ComputableInPolyTime (fun x => decide ((ids x).length = 0)) enc encBool := by fun_prop
  simpa only [largeOutput, Function.comp_def, decide_eq_true_eq] using
    hre.ite' hzero (he.ite' hpow (hc.ite' (hfull.ite' hbtag (hz.ite' hpow hquery)) hzero))

/-- Complete tagged-plan construction is polynomial binary time and independent polynomial
space for fixed d, including direct count bits, both query lists and declared-variable output. -/
@[fun_prop] theorem compile_polytime (d : ℕ) :
    ComputableInPolyTime (fun p : ℕ × List BinaryNormalization.Input => compile d p.1 p.2)
      (encPair encUnary (encList BinaryNormalization.encInput)) encOutput := by
  let encI := encPair encUnary (encList BinaryNormalization.encInput)
  have hn : ComputableInPolyTime (fun p : ℕ × List BinaryNormalization.Input => p.1)
      encI encUnary := by fun_prop
  have hr : ComputableInPolyTime (fun p : ℕ × List BinaryNormalization.Input => p.2)
      encI (encList BinaryNormalization.encInput) := by fun_prop
  have hd := BinaryNormalization.analyze_polytime
  have hl := largeOutput_polytime d hn hr hd.fst' hd.snd'.fst' hd.snd'.snd'.fst' hd.snd'.snd'.snd'
  have hs := (ComputableInPolyTime.sumInl encNat
    (encPair encUnary (encPair encCNF encCNF))).comp smallAnswer_polytime
  have hg : ComputableInPolyTime (fun p : ℕ × List BinaryNormalization.Input => decide (p.1 ≤ 1))
      encI encBool := by fun_prop
  apply (hg.ite' hs hl).of_enc_eq
  intro p
  simp only [compile, decide_eq_true_eq, Function.comp_def]
  split_ifs
  · rfl
  · rcases BinaryNormalization.analyze p.1 p.2 with ⟨reject, ids, consistent, boolean⟩
    rfl

/-- Serialize the reviewed finite plan, retaining every declared original/auxiliary variable. -/
@[expose] def serialize {n d : ℕ} : CountingPlan n d → Output
  | .direct a => .inl a
  | .queries k q _ _ _ => .inr (n + k,
      ((q false).relabel (flattenVar (n := n)), (q true).relabel (flattenVar (n := n))))

/-- Constant-assignment checking agrees pointwise with the original occurrence equations. -/
theorem constantTest_ofOccurrences {n m t : ℕ} (R : Fin t → Occurrences n m) (b : Bool) :
    constantTest ((List.finRange t).map fun j => BinaryNormalization.ofOccurrences (R j)) b = true ↔
      ∀ j, ((R j).value (fun _ => b) : ℤ) = (R j).target := by
  simp [constantTest, BinaryNormalization.ofOccurrences, List.sum_ofFn,
    Occurrences.value, Nat.cast_sum, Nat.cast_ite]

private theorem constantTest_normalized {n m t d : ℕ} (R : Fin t → Occurrences n m)
    (hd : ∀ j, (R j).demand ≤ d) (b : Bool) :
    constantTest ((List.finRange t).map fun j => BinaryNormalization.ofOccurrences (R j)) b =
      normalizedTest ((List.finRange t).map fun j => (R j).normalize d (hd j)) (fun _ => b) := by
  apply Bool.eq_iff_iff.mpr
  simp [constantTest_ofOccurrences, normalizedTest_iff, Occurrences.normalize_iff]

private theorem smallCount_zero {d : ℕ} (ns : List (Normalized 0 d)) :
    smallCount ns = if normalizedTest ns (fun _ => false) then 1 else 0 := by
  classical
  have he (σ : Fin 0 → Bool) : normalizedTest ns σ = normalizedTest ns (fun _ => false) :=
    congrArg (normalizedTest ns) (Subsingleton.elim _ _)
  simp only [smallCount, Finset.univ_unique, Finset.filter_singleton, he]
  split_ifs <;> simp

private theorem smallCount_one {d : ℕ} (ns : List (Normalized 1 d)) :
    smallCount ns = (if normalizedTest ns (fun _ => false) then 1 else 0) +
      (if normalizedTest ns (fun _ => true) then 1 else 0) := by
  classical
  rw [smallCount_correct]
  change Fintype.card {σ : Fin 1 → Bool // ∀ N ∈ ns, N.Holds σ} = _
  have hcard : Fintype.card {σ : Fin 1 → Bool // ∀ N ∈ ns, N.Holds σ} =
      Fintype.card {b : Bool // ∀ N ∈ ns, N.Holds (fun _ => b)} := by
    symm
    exact Fintype.card_congr (Equiv.subtypeEquiv (Equiv.funUnique (Fin 1) Bool).symm
      (fun _ => Iff.rfl))
  rw [hcard, Fintype.card_subtype]
  simp only [← normalizedTest_iff]
  have hu : (Finset.univ : Finset Bool) = {false, true} := by decide
  rw [hu]
  cases hf : normalizedTest ns (fun _ => false) <;>
    cases ht : normalizedTest ns (fun _ => true) <;>
      simp [Finset.filter_insert, Finset.filter_singleton, hf, ht]

/-- Exactly the reviewed direct count is emitted at n≤1, with no large Boolean cube. -/
theorem smallAnswer_ofOccurrences {n m t d : ℕ} (R : Fin t → Occurrences n m)
    (hd : ∀ j, (R j).demand ≤ d) (hn : n ≤ 1) :
    smallAnswer n ((List.finRange t).map fun j => BinaryNormalization.ofOccurrences (R j)) =
      smallCount ((List.finRange t).map fun j => (R j).normalize d (hd j)) := by
  interval_cases n
  · simp [smallAnswer, constantTest_normalized R hd, smallCount_zero]
  · simp [smallAnswer, constantTest_normalized R hd, smallCount_one]

/-- The actual tagged binary compiler equals serialization of the reviewed executable plan,
case by case, on original positive-weight occurrences with bounded computed demands. -/
theorem compile_ofOccurrences {n m t d : ℕ} (R : Fin t → Occurrences n m)
    (hd : ∀ j, (R j).demand ≤ d) :
    compile d n ((List.finRange t).map fun j => BinaryNormalization.ofOccurrences (R j)) =
      serialize (executableCountingPlan
        ((List.finRange t).map fun j => (R j).normalize d (hd j))).val := by
  let ns := (List.finRange t).map fun j => (R j).normalize d (hd j)
  change _ = serialize (executableCountingPlan ns).val
  by_cases small : n ≤ 1
  · simp only [compile, small, ite_true, executableCountingPlan, dite_true, serialize,
      smallAnswer_ofOccurrences R hd small]
    rfl
  rw [compile, ite_eq_right small, BinaryNormalization.analyze_ofOccurrences R hd]
  change largeOutput d n _ (rejected ns) (cappedBasis ns)
    (LinearSystem.rectangularConsistent n (cappedMatrix ns) (cappedRhs ns))
    (if (cappedBasis ns).length = n then
      LinearSystem.rectangularBoolean n (cappedMatrix ns) (cappedRhs ns) else false) = _
  unfold largeOutput executableCountingPlan
  simp only [small, dite_false]
  by_cases hr : rejected ns = true
  · simp [hr, serialize]
  simp only [hr, Bool.false_eq_true, ite_false, dite_false]
  rw [BinaryNormalization.materialize_ofOccurrences R hd]
  change (if (cappedMatrix ns).length = 0 then _ else _) = _
  have hlen : (cappedMatrix ns).length = (cappedRows ns).length := by simp [cappedMatrix]
  simp only [hlen]
  by_cases he : (cappedRows ns).length = 0
  · simp [he, serialize]
  simp only [he, ite_false, dite_false]
  by_cases hc : LinearSystem.rectangularConsistent n (cappedMatrix ns) (cappedRhs ns) = true
  · simp only [hc, ite_true, dite_true]
    by_cases hf : (cappedBasis ns).length = n
    · simp [hf, serialize]
    simp only [hf, ite_false, dite_false]
    by_cases hz : (cappedBasis ns).length = 0
    · simp [hz, serialize]
    simp only [hz, ite_false, dite_false]
    have hk : (cappedBasis ns).length - 1 + 1 = (cappedBasis ns).length := by omega
    rw [selectedQuery_ofOccurrences R hd hk false, selectedQuery_ofOccurrences R hd hk true]
    simp only [serialize]
    have hmeta : n + (cappedBasis ns).length - 1 = n + ((cappedBasis ns).length - 1) := by omega
    simp only [hmeta]
    rfl
  · simp [hc, serialize]

/-- The full original-input endpoint agrees with the exact reviewed all-cases output. -/
theorem compile_original {n m t d : ℕ} (R : Fin t → Occurrences n m)
    (hd : ∀ j, (R j).demand ≤ d) :
    compile d n ((List.finRange t).map fun j => BinaryNormalization.ofOccurrences (R j)) =
      serialize (executableOriginalCountingPlan R hd).val :=
  compile_ofOccurrences R hd

/-- Extend a declared finite assignment by false outside the declaration. -/
@[expose] def assignment {N : ℕ} (σ : Fin N → Bool) (i : ℕ) : Bool :=
  if hi : i < N then σ ⟨i, hi⟩ else false

open Classical in
/-- Ordinary CNF count over every declared variable, including unused variables. -/
noncomputable def queryCount (N : ℕ) (q : CNF ℕ) : ℕ :=
  Fintype.card {σ : Fin N → Bool // q.eval (assignment σ) = true}

/-- Interpret the actual tagged answer or the difference of the two ordinary counts. -/
noncomputable def Output.count : Output → ℕ
  | .inl a => a
  | .inr (N, (qfalse, qtrue)) => queryCount N qfalse - queryCount N qtrue

private theorem queryCount_relabel {n k : ℕ} (q : CNF (Fin n ⊕ Fin k)) :
    queryCount (n + k) (q.relabel (flattenVar (n := n))) =
      Fintype.card {σ : Fin n ⊕ Fin k → Bool // q.eval σ = true} := by
  classical
  let e : (Fin (n + k) → Bool) ≃ (Fin n ⊕ Fin k → Bool) :=
    (Equiv.arrowCongr finSumFinEquiv (Equiv.refl Bool)).symm
  apply Fintype.card_congr
  apply Equiv.subtypeEquiv e
  intro σ
  rw [CNF.eval_relabel]
  have he : assignment σ ∘ flattenVar = e σ := by
    funext v
    rw [Function.comp_apply, assignment, dite_eq_left (flattenVar_lt v)]
    change σ _ = σ (finSumFinEquiv v)
    congr 1
    apply Fin.ext
    cases v <;> rfl
  rw [he]

/-- Serialization preserves exact full-declared-variable query counting. -/
theorem serialize_count {n d : ℕ} (p : CountingPlan n d) :
    (serialize p).count = p.count := by
  cases p with
  | direct a => rfl
  | queries k q hv hw hc =>
    simp only [serialize, Output.count, CountingPlan.count, queryCount_relabel]

/-- End-to-end exact counting for the actual tagged output on original positive occurrences. -/
theorem compile_count {n m t d : ℕ} (R : Fin t → Occurrences n m)
    (hd : ∀ j, (R j).demand ≤ d) :
    (compile d n ((List.finRange t).map fun j => BinaryNormalization.ofOccurrences (R j))).count =
      Fintype.card {σ : Fin n → Bool // ∀ j, ((R j).value σ : ℤ) = (R j).target} := by
  rw [compile_original R hd, serialize_count]
  exact (executableOriginalCountingPlan R hd).property

/-- Query declarations, actual list budgets and all emitted indices satisfy the source bounds. -/
@[expose] def WithinBudget (n d : ℕ) : Output → Prop
  | .inl _ => True
  | .inr (N, (qfalse, qtrue)) =>
    N ≤ 2 * n - 2 ∧ ∀ q ∈ [qfalse, qtrue], q.length ≤ countingBudget n d ∧
      ∀ c ∈ q, c.length ≤ d + 2 ∧ ∀ l ∈ c, l.1 < N

/-- The serialized finite plan retains all variable, clause, literal and index guarantees. -/
theorem serialize_withinBudget {n d : ℕ} (p : CountingPlan n d) :
    WithinBudget n d (serialize p) := by
  cases p with
  | direct a => trivial
  | queries k q hv hw hc =>
    refine ⟨hv, ?_⟩
    intro Q hQ
    have hb (β : Bool) :
        ((q β).relabel (flattenVar (n := n))).length ≤ countingBudget n d ∧
          ∀ c ∈ (q β).relabel (flattenVar (n := n)), c.length ≤ d + 2 ∧
            ∀ l ∈ c, l.1 < n + k := by
      refine ⟨by simpa only [CNF.relabel, List.length_map] using hc β, ?_⟩
      intro c hcm
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hcm
      refine ⟨by simpa only [Clause.relabel, List.length_map] using hw β a ha, ?_⟩
      intro l hl
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hl
      exact flattenVar_lt v.1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
    rcases hQ with rfl | rfl
    · exact hb false
    · exact hb true

/-- End-to-end variable/width/clause/index bounds for the actual compiled output. -/
theorem compile_withinBudget {n m t d : ℕ} (R : Fin t → Occurrences n m)
    (hd : ∀ j, (R j).demand ≤ d) :
    WithinBudget n d
      (compile d n ((List.finRange t).map fun j => BinaryNormalization.ofOccurrences (R j))) := by
  rw [compile_original R hd]
  exact serialize_withinBudget _

/-- The complete interpreted output never counts more than all declared Boolean assignments. -/
theorem compile_count_le {n m t d : ℕ} (R : Fin t → Occurrences n m)
    (hd : ∀ j, (R j).demand ≤ d) :
    (compile d n ((List.finRange t).map fun j => BinaryNormalization.ofOccurrences (R j))).count ≤
      2 ^ n := by
  rw [compile_count R hd]
  classical
  have h := Fintype.card_le_of_injective
    (fun σ : {σ : Fin n → Bool // ∀ j, ((R j).value σ : ℤ) = (R j).target} => σ.val)
    Subtype.val_injective
  simpa using h

/-- A directly emitted answer has at most n+1 binary bits, even for the 2^n branch. -/
theorem compile_direct_bits {n m t d a : ℕ} (R : Fin t → Occurrences n m)
    (hd : ∀ j, (R j).demand ≤ d)
    (ha : compile d n ((List.finRange t).map fun j => BinaryNormalization.ofOccurrences (R j)) =
      .inl a) : (encNat a).length ≤ n + 1 := by
  have h := compile_count_le R hd
  rw [ha] at h
  change a ≤ 2 ^ n at h
  have hp : 0 < 2 ^ n := by positivity
  have hs : a.size ≤ n + 1 := Nat.size_le.mpr (by rw [Nat.pow_succ]; omega)
  change a.bits.length ≤ n + 1
  simpa only [Nat.size_eq_bits_len] using hs

/-- Complete encoded output storage is polynomial because the whole compiler is certified. -/
theorem compile_output_polyBounded (d : ℕ) :
    PolyBounded
      (fun p : ℕ × List BinaryNormalization.Input =>
        (encPair encUnary (encList BinaryNormalization.encInput) p).length)
      (fun p => (encOutput (compile d p.1 p.2)).length) :=
  ((ComputableInPolyTime.encoding_length _).comp (compile_polytime d)).polyBounded

end Cslib.Logic.PL.WeightedRow.BinaryPlan
