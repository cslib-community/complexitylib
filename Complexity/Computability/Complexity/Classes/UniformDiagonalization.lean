/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Ladner.PolyTime
public import Complexity.Computability.Complexity.Reduction
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Clocked
import Complexity.Computability.Complexity.Classes.Immune
import Complexity.Computability.Machines.Turing.MultiTape.Halting.Partrec
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.TwoPow
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import Mathlib.Data.Set.Finite.List

/-!
# Uniform diagonalization

Schöning's uniform diagonalization theorem [Schöning][Schoening1982]
(`Cslib.Complexity.exists_mem_P_ite_notMem`): let `C₁`, `C₂` be recursively presentable classes
of sets of bit words, both closed under finite variations, and let `A₁ ∉ C₁` and `A₂ ∉ C₂` be
decidable. Then some `G ∈ P` makes the set `G.ite A₁ A₂`, which agrees with `A₁` on `G` and with
`A₂` off `G`, belong to neither class. This set is decidable, reduces to the marked union of `A₁`
and `A₂`, and reduces to `A₂` when `A₁ ∈ P` and `A₂` is neither empty nor everything.

The proof is delayed diagonalization. Stage `k` separates the mixed set from the member of index
`k / 2` of the first family (even `k`) or the second family (odd `k`). The words of length `n` are
put on the side of the stage at `n`. The stage at `n` advances over the stage at `n - 1` when a
word of index below `n` separates the two sets, as seen by runs of `n` steps of both machines
(`Turing.MultiTapeTM.Universal.runBool`). This check takes polynomial time in `n`, so `G ∈ P`.
Since the sets of each side are infinitely different from the members of their family, every
stage is reached, and leaving stage `k` needs a separating word.

`P` itself meets the hypotheses: it is closed under finite variations
(`Cslib.Complexity.closedUnderFiniteVariation_P`), and it is recursively presentable by the
machines run within polynomial clocks (`Cslib.Complexity.recursivelyPresentable_P`).

## Main definitions

* `Cslib.Complexity.RecursivelyPresentable`: the class of the sets `{a | F (i, a) = true}` for a
  computable `F`, with the index `i` in unary.
* `Cslib.Complexity.ClosedUnderFiniteVariation`: closure under finite symmetric differences.
* `Cslib.Complexity.markedUnion`: `false :: x` for `x ∈ A₁` and `true :: x` for `x ∈ A₂`.

## Main results

* `Cslib.Complexity.exists_mem_P_ite_notMem`: Schöning's uniform diagonalization theorem.
* `Cslib.Complexity.exists_mem_P_forall_ite_ne`: the effective form, against two computable
  families of sets, each infinitely different from `A₁` or `A₂`.
* `Cslib.Complexity.isDecidable_ite`, `Cslib.Complexity.polyTimeReducible_ite_markedUnion`,
  `Cslib.Complexity.polyTimeReducible_ite_of_mem_P`: the mixed set is decidable and reduces to the
  marked union, and to `A₂` when `A₁ ∈ P`.
* `Cslib.Complexity.recursivelyPresentable_P`, `Cslib.Complexity.closedUnderFiniteVariation_P`:
  `P` meets the hypotheses.
* `Cslib.Complexity.exists_mem_P_ite_notMem_P`: the theorem with `C₁ = P`.

## Implementation notes

The classes are of sets of bit words (`encBits`), so the theorem is the binary-alphabet case of
the source statement. Decidable sets and presentations are computed by total native machines
(`Turing.MultiTapeTM.IsComputable`). The reduction to `A₂` takes a member and a non-member of
`A₂` in place of the hypothesis that `A₂` is neither empty nor everything.

Ladner's density theorem, the application to the polynomial-time degree of a decidable set
outside `P`, is not formalized here: it needs a recursive presentation of that degree.

## References

* [U. Schöning, *A uniform approach to obtain diagonal sets in complexity
  classes*][Schoening1982]
-/

public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal ComputableInPolyTime
open scoped symmDiff

namespace UniformDiagonalization

open Ladner (word index word_index index_word length_word_lt index_add_two_le)

/-! ### The construction -/

/-- The side of stage `k`: `true` (the first pair) at even stages, `false` at odd ones. -/
@[expose] def side (k : ℕ) : Bool := decide (k % 2 = 0)

variable (dA : Bool → Desc) (dF : Bool → Desc)

/-- The clocked answer, within `t` steps, for membership of `w` in the mixed set, where the side
is read from the table `T` at the length of `w`. -/
def approxA (T : List ℕ) (w : List Bool) (t : ℕ) : Option Bool :=
  runBool (dA (side (T.getD w.length 0))) w t

/-- The clocked answer, within `t` steps, for membership of `w` in the set diagonalized at stage
`k`. -/
def approxF (k : ℕ) (w : List Bool) (t : ℕ) : Option Bool :=
  runBool (dF (side k)) (encPair encUnary encBits (k / 2, w)) t

/-- Two clocked answers that are both present and differ. -/
def disagree (u v : Option Bool) : Bool :=
  u.isSome && v.isSome && !decide (u = v)

theorem disagree_iff {u v : Option Bool} :
    disagree u v = true ↔ ∃ b, u = some b ∧ v = some !b := by
  cases u with
  | none => simp [disagree]
  | some a => cases v with
    | none => simp [disagree]
    | some c => cases a <;> cases c <;> simp [disagree]

/-- Whether a word with index below `T.length` separates the mixed set from the set diagonalized at
stage `k`, as seen by runs of `T.length` steps. -/
def witness (T : List ℕ) (k : ℕ) : Bool :=
  (List.range T.length).any fun j =>
    disagree (approxA dA T (word j) T.length) (approxF dF k (word j) T.length)

/-- The stage after the table `T` of the earlier stages: the last stage, advanced by one if it has
a witness. -/
def stageStep (T : List ℕ) : ℕ :=
  if witness dA dF T (T.getD (T.length - 1) 0) then T.getD (T.length - 1) 0 + 1
  else T.getD (T.length - 1) 0

/-- The table of the first `n` stages. -/
def table : ℕ → List ℕ
  | 0 => []
  | n + 1 => table n ++ [stageStep dA dF (table n)]

/-- The stage at length `n`. -/
def stage (n : ℕ) : ℕ := stageStep dA dF (table dA dF n)

theorem table_eq (n : ℕ) : table dA dF n = (List.range n).map (stage dA dF) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [table, List.range_succ, List.map_append, ← ih]; rfl

@[simp]
theorem length_table (n : ℕ) : (table dA dF n).length = n := by
  simp [table_eq]

theorem getD_table {n m : ℕ} (h : m < n) : (table dA dF n).getD m 0 = stage dA dF m := by
  rw [table_eq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

theorem stage_zero : stage dA dF 0 = 0 := by
  simp [stage, stageStep, table, witness]

theorem stage_succ (n : ℕ) : stage dA dF (n + 1) =
    if witness dA dF (table dA dF (n + 1)) (stage dA dF n) then stage dA dF n + 1
    else stage dA dF n := by
  rw [stage, stageStep, length_table, Nat.add_sub_cancel, getD_table _ _ (Nat.lt_succ_self n)]

theorem stage_le_succ (n : ℕ) : stage dA dF n ≤ stage dA dF (n + 1) := by
  rw [stage_succ]
  split_ifs <;> omega

theorem stage_succ_le (n : ℕ) : stage dA dF (n + 1) ≤ stage dA dF n + 1 := by
  rw [stage_succ]
  split_ifs <;> omega

theorem stage_mono : Monotone (stage dA dF) :=
  monotone_nat_of_le_succ (stage_le_succ dA dF)

theorem stage_le_self (n : ℕ) : stage dA dF n ≤ n := by
  induction n with
  | zero => rw [stage_zero]
  | succ n ih => have := stage_succ_le dA dF n; omega

/-! ### Soundness and completeness of the witnesses -/

section Spec

variable {A : Bool → Set (List Bool)} {F : Bool → ℕ → Set (List Bool)}

/-- Clocked runs of `dA b` decide `A b`, and clocked runs of `dF b` decide the family `F b`, soundly
and eventually completely. -/
structure Spec (A : Bool → Set (List Bool)) (F : Bool → ℕ → Set (List Bool)) : Prop where
  soundA : ∀ b w t c, runBool (dA b) w t = some c → (c = true ↔ w ∈ A b)
  completeA : ∀ b w, ∃ T, ∀ t, T ≤ t → ∃ c, runBool (dA b) w t = some c
  soundF : ∀ b i w t c, runBool (dF b) (encPair encUnary encBits (i, w)) t = some c →
    (c = true ↔ w ∈ F b i)
  completeF : ∀ b i w, ∃ T, ∀ t, T ≤ t →
    ∃ c, runBool (dF b) (encPair encUnary encBits (i, w)) t = some c

/-- The mixed set: a word of length `n` is decided by the side of the stage at `n`. -/
def D (A : Bool → Set (List Bool)) : Set (List Bool) :=
  {w | w ∈ A (side (stage dA dF w.length))}

variable {dA dF}

/-- **A witness separates.** -/
theorem witness_sound (hS : Spec dA dF A F) {n k : ℕ} (h : witness dA dF (table dA dF n) k = true) :
    ∃ w, ¬(w ∈ D dA dF A ↔ w ∈ F (side k) (k / 2)) := by
  obtain ⟨j, hj, hd⟩ := List.any_eq_true.mp h
  rw [length_table, List.mem_range] at hj
  obtain ⟨c, hc₁, hc₂⟩ := disagree_iff.mp hd
  have hlen : (word j).length < n := (length_word_lt j).trans_le hj
  rw [approxA, getD_table _ _ hlen] at hc₁
  refine ⟨word j, fun hiff => ?_⟩
  have h₁ := hS.soundA _ _ _ _ hc₁
  have h₂ := hS.soundF _ _ _ _ _ hc₂
  rw [D, Set.mem_ofPred_eq] at hiff
  cases c <;> simp_all

/-- **A separating word is eventually a witness.** -/
theorem witness_complete (hS : Spec dA dF A F) {k : ℕ} {w : List Bool}
    (hw : ¬(w ∈ A (side k) ↔ w ∈ F (side k) (k / 2))) :
    ∃ N, ∀ n, N ≤ n → stage dA dF w.length = k →
      witness dA dF (table dA dF n) k = true := by
  obtain ⟨T₁, hT₁⟩ := hS.completeA (side k) w
  obtain ⟨T₂, hT₂⟩ := hS.completeF (side k) (k / 2) w
  refine ⟨max (index w + 1) (max T₁ T₂), fun n hn hk => ?_⟩
  refine List.any_eq_true.mpr ⟨index w, ?_, ?_⟩
  · rw [length_table, List.mem_range]
    omega
  · have hlen : w.length < n := by
      have := length_word_lt (index w)
      rw [word_index] at this
      omega
    obtain ⟨c₁, hc₁⟩ := hT₁ n (by omega)
    obtain ⟨c₂, hc₂⟩ := hT₂ n (by omega)
    have h₁ := hS.soundA _ _ _ _ hc₁
    have h₂ := hS.soundF _ _ _ _ _ hc₂
    rw [word_index, approxA, approxF, length_table, getD_table _ _ hlen, hk, hc₁, hc₂]
    refine disagree_iff.mpr ⟨c₁, rfl, ?_⟩
    cases c₁ <;> cases c₂ <;> simp_all

/-- **Every stage is reached** when each `A b` is infinitely different from every `F b i`: if the
stages stayed at `k`, the sets of the side of `k` would agree on all long words. -/
theorem exists_stage_eq (hS : Spec dA dF A F) (hinf : ∀ b i, (A b ∆ F b i).Infinite) (k : ℕ) :
    ∃ n, stage dA dF n = k := by
  induction k with
  | zero => exact ⟨0, stage_zero dA dF⟩
  | succ k ih =>
    obtain ⟨n, hn⟩ := ih
    by_contra hne
    simp only [not_exists] at hne
    -- the stages stay at `k` from `n` on
    have hstay : ∀ m, n ≤ m → stage dA dF m = k := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => exact hn
      | succ m _ ihm =>
        have h₁ := stage_le_succ dA dF m
        have h₂ := stage_succ_le dA dF m
        have h₃ := hne (m + 1)
        omega
    -- so the sets of the side of `k` agree on the words of length at least `n`
    refine hinf (side k) (k / 2) ((List.finite_length_lt Bool n).subset fun w hw => ?_)
    by_contra hlen
    rw [Set.mem_ofPred_eq, not_lt] at hlen
    have hsep : ¬(w ∈ A (side k) ↔ w ∈ F (side k) (k / 2)) := fun hiff =>
      (Set.mem_symmDiff.mp hw).elim (fun h => h.2 (hiff.mp h.1)) fun h => h.2 (hiff.mpr h.1)
    obtain ⟨N, hN⟩ := witness_complete hS hsep
    have hw := hN (max N n + 1) (by omega) (hstay _ hlen)
    have hs := stage_succ dA dF (max N n)
    rw [hstay (max N n) (le_max_right _ _), ite_eq_left hw] at hs
    exact hne _ hs

/-- **The mixed set differs from every diagonalized set.** -/
theorem D_ne (hS : Spec dA dF A F) (hinf : ∀ b i, (A b ∆ F b i).Infinite) (b : Bool) (i : ℕ) :
    D dA dF A ≠ F b i := by
  intro heq
  obtain ⟨k, hside, hhalf⟩ : ∃ k, side k = b ∧ k / 2 = i :=
    ⟨2 * i + cond b 0 1, by cases b <;> simp [side], by cases b <;> simp; omega⟩
  obtain ⟨n, hn⟩ := exists_stage_eq hS hinf (k + 1)
  have hex : ∃ m, k + 1 ≤ stage dA dF m := ⟨n, hn.ge⟩
  -- the first stage beyond `k` is reached from stage `k` through a witness
  obtain ⟨m, hm, hmin⟩ : ∃ m, k + 1 ≤ stage dA dF m ∧ ∀ m' < m, stage dA dF m' < k + 1 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m' hm' => not_le.mp (Nat.find_min hex hm')⟩
  cases m with
  | zero => rw [stage_zero] at hm; omega
  | succ m =>
    have h₁ := hmin m (Nat.lt_succ_self m)
    have h₂ := stage_succ_le dA dF m
    have hkm : stage dA dF m = k := by omega
    rw [stage_succ, hkm] at hm
    split_ifs at hm with hw
    · obtain ⟨w, hsep⟩ := witness_sound hS hw
      rw [hside, hhalf, ← heq] at hsep
      exact hsep Iff.rfl
    · omega

end Spec

/-! ### The stages in polynomial time -/

theorem computableInPolyTime_side : ComputableInPolyTime side encUnary encBool := by
  unfold side
  fun_prop

private theorem computableInPolyTime_disagree :
    ComputableInPolyTime (fun p : Option Bool × Option Bool => disagree p.1 p.2)
      (encPair (encOption encBool) (encOption encBool)) encBool := by
  unfold disagree
  fun_prop

private theorem computableInPolyTime_witnessAt :
    ComputableInPolyTime (fun p : (List ℕ × ℕ) × ℕ =>
        disagree (approxA dA p.1.1 (word p.2) p.1.1.length)
          (approxF dF p.1.2 (word p.2) p.1.1.length))
      (encPair (encPair (encList encUnary) encUnary) encUnary) encBool := by
  have hdA : ComputableInPolyTime dA encBool eDesc := .of_tidy (.of_finite dA)
  have hdF : ComputableInPolyTime dF encBool eDesc := .of_tidy (.of_finite dF)
  have hside := computableInPolyTime_side
  have hd := computableInPolyTime_disagree
  unfold approxA approxF
  fun_prop

private theorem computableInPolyTime_stageStep :
    ComputableInPolyTime (stageStep dA dF) (encList encUnary) encUnary := by
  have ha := computableInPolyTime_witnessAt dA dF
  have hw : ComputableInPolyTime (fun p : List ℕ × ℕ => witness dA dF p.1 p.2)
      (encPair (encList encUnary) encUnary) encBool := by
    unfold witness
    fun_prop
  unfold stageStep
  fun_prop

theorem table_eq_iterate (n : ℕ) :
    table dA dF n = (fun T => T ++ [stageStep dA dF T])^[n] [] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [table, Function.iterate_succ_apply', ← ih]

/-- The tables of the stages are polynomial-time in their length, in unary. -/
theorem computableInPolyTime_table :
    ComputableInPolyTime (table dA dF) encUnary (encList encUnary) := by
  have hs := computableInPolyTime_stageStep dA dF
  have h := iterate (encIn := encUnary) (encState := encList encUnary) (count := fun n => n)
    (init := fun _ => []) (step := fun T => T ++ [stageStep dA dF T]) (by fun_prop) (by fun_prop)
    (by fun_prop) (bound := fun n => n * (2 * n + 1))
    (.of_forall_le 2 2 fun n => by simp only [encUnary_apply, List.length_replicate]; nlinarith)
    (fun n i hi => by
      rw [← table_eq_iterate]
      calc (encList encUnary (table dA dF i)).length ≤ (table dA dF i).length * (2 * n + 1) :=
            length_encList_le encUnary _ fun a ha => by
              rw [table_eq] at ha
              obtain ⟨m, hm, rfl⟩ := List.mem_map.mp ha
              simpa using (stage_le_self dA dF m).trans (by have := List.mem_range.mp hm; omega)
        _ ≤ n * (2 * n + 1) := by rw [length_table]; exact Nat.mul_le_mul_right _ hi)
  simpa only [← table_eq_iterate] using h

/-- **The stages are polynomial-time** on unary numbers. -/
theorem computableInPolyTime_stage : ComputableInPolyTime (stage dA dF) encUnary encUnary :=
  (computableInPolyTime_stageStep dA dF).comp (computableInPolyTime_table dA dF)

/-- The words whose length is at a stage of the first side form a problem in `P`. -/
theorem setOf_side_stage_mem_P :
    {w : List Bool | side (stage dA dF w.length) = true} ∈ P encBits := by
  have hs := computableInPolyTime_stage dA dF
  have hside := computableInPolyTime_side
  exact ⟨fun w => side (stage dA dF w.length), by fun_prop, fun _ => Iff.rfl⟩

end UniformDiagonalization

open UniformDiagonalization

/-! ### Uniform diagonalization -/

/-- **Uniform diagonalization, effective form.** Let `A₁`, `A₂` be decidable sets of words and
`F₁`, `F₂` computable families of sets of words, with `A₁` infinitely different from every member
of `F₁` and `A₂` from every member of `F₂`. Some `G ∈ P` makes the set agreeing with `A₁` on `G`
and with `A₂` off `G` differ from every member of both families. -/
theorem exists_mem_P_forall_ite_ne {A₁ A₂ : Set (List Bool)} (hA₁ : IsDecidable A₁ encBits)
    (hA₂ : IsDecidable A₂ encBits) {F₁ F₂ : ℕ × List Bool → Bool}
    (hF₁ : IsComputable F₁ (encPair encUnary encBits) encBool)
    (hF₂ : IsComputable F₂ (encPair encUnary encBits) encBool)
    (h₁ : ∀ i, (A₁ ∆ {w | F₁ (i, w) = true}).Infinite)
    (h₂ : ∀ i, (A₂ ∆ {w | F₂ (i, w) = true}).Infinite) :
    ∃ G ∈ P encBits, ∀ i, G.ite A₁ A₂ ≠ {w | F₁ (i, w) = true} ∧
      G.ite A₁ A₂ ≠ {w | F₂ (i, w) = true} := by
  obtain ⟨f₁, hf₁, hA₁'⟩ := hA₁.exists_isComputable
  obtain ⟨f₂, hf₂, hA₂'⟩ := hA₂.exists_isComputable
  obtain ⟨a₁, sa₁, ca₁⟩ := hf₁.exists_runBool
  obtain ⟨a₂, sa₂, ca₂⟩ := hf₂.exists_runBool
  obtain ⟨e₁, se₁, ce₁⟩ := hF₁.exists_runBool
  obtain ⟨e₂, se₂, ce₂⟩ := hF₂.exists_runBool
  let dA : Bool → Desc := fun b => if b then a₁ else a₂
  let dF : Bool → Desc := fun b => if b then e₁ else e₂
  let A : Bool → Set (List Bool) := fun b => if b then A₁ else A₂
  let F : Bool → ℕ → Set (List Bool) := fun b i =>
    if b then {w | F₁ (i, w) = true} else {w | F₂ (i, w) = true}
  have hS : Spec dA dF A F :=
    { soundA := fun b w t c h => by
        cases b
        · rw [sa₂ w t c h]; exact (hA₂' w).symm
        · rw [sa₁ w t c h]; exact (hA₁' w).symm
      completeA := fun b w => by
        cases b
        · obtain ⟨T, hT⟩ := ca₂ w; exact ⟨T, fun t ht => ⟨_, hT t ht⟩⟩
        · obtain ⟨T, hT⟩ := ca₁ w; exact ⟨T, fun t ht => ⟨_, hT t ht⟩⟩
      soundF := fun b i w t c h => by
        cases b
        · rw [se₂ (i, w) t c h]; exact Iff.rfl
        · rw [se₁ (i, w) t c h]; exact Iff.rfl
      completeF := fun b i w => by
        cases b
        · obtain ⟨T, hT⟩ := ce₂ (i, w); exact ⟨T, fun t ht => ⟨_, hT t ht⟩⟩
        · obtain ⟨T, hT⟩ := ce₁ (i, w); exact ⟨T, fun t ht => ⟨_, hT t ht⟩⟩ }
  have hinf : ∀ b i, (A b ∆ F b i).Infinite := fun b i => by
    cases b
    · exact h₂ i
    · exact h₁ i
  have hD : Set.ite {w : List Bool | side (stage dA dF w.length) = true} A₁ A₂ = D dA dF A := by
    ext w
    simp only [Set.ite, D, Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_ofPred_eq]
    cases side (stage dA dF w.length) <;> simp [A]
  refine ⟨_, setOf_side_stage_mem_P dA dF, fun i => ⟨?_, ?_⟩⟩
  · rw [hD]
    exact D_ne hS hinf true i
  · rw [hD]
    exact D_ne hS hinf false i

/-- A class of sets is **recursively presentable** when it is the class of the sets
`{a | F (i, a) = true}`, `i : ℕ`, for a computable `F`. Such a class is nonempty, so the empty class
is not recursively presentable. -/
@[expose] def RecursivelyPresentable {α : Type} (enc : α ↪ List Bool) (C : Set (Set α)) : Prop :=
  ∃ F : ℕ × α → Bool, IsComputable F (encPair encUnary enc) encBool ∧
    C = Set.range fun i => {a | F (i, a) = true}

/-- A class of sets is **closed under finite variations** when it contains every set finitely
different from one of its members. -/
@[expose] def ClosedUnderFiniteVariation {α : Type} (C : Set (Set α)) : Prop :=
  ∀ ⦃L L' : Set α⦄, L ∈ C → (L ∆ L').Finite → L' ∈ C

/-- A set outside a class closed under finite variations is infinitely different from each of its
members. -/
theorem ClosedUnderFiniteVariation.infinite_symmDiff {α : Type} {C : Set (Set α)}
    (hC : ClosedUnderFiniteVariation C) {A L : Set α} (hA : A ∉ C) (hL : L ∈ C) :
    (A ∆ L).Infinite :=
  fun hfin => hA (hC hL (symmDiff_comm A L ▸ hfin))

/-- **Schöning's uniform diagonalization theorem.** Let `C₁`, `C₂` be recursively presentable
classes of sets of words, closed under finite variations, and `A₁ ∉ C₁`, `A₂ ∉ C₂` decidable. Some
`G ∈ P` makes the set agreeing with `A₁` on `G` and with `A₂` off `G` belong to neither class. -/
theorem exists_mem_P_ite_notMem {C₁ C₂ : Set (Set (List Bool))}
    (hC₁ : RecursivelyPresentable encBits C₁) (hC₂ : RecursivelyPresentable encBits C₂)
    (hv₁ : ClosedUnderFiniteVariation C₁) (hv₂ : ClosedUnderFiniteVariation C₂)
    {A₁ A₂ : Set (List Bool)} (hA₁ : IsDecidable A₁ encBits) (hA₂ : IsDecidable A₂ encBits)
    (h₁ : A₁ ∉ C₁) (h₂ : A₂ ∉ C₂) :
    ∃ G ∈ P encBits, G.ite A₁ A₂ ∉ C₁ ∧ G.ite A₁ A₂ ∉ C₂ := by
  obtain ⟨F₁, hF₁, rfl⟩ := hC₁
  obtain ⟨F₂, hF₂, rfl⟩ := hC₂
  obtain ⟨G, hG, hne⟩ := exists_mem_P_forall_ite_ne hA₁ hA₂ hF₁ hF₂
    (fun i => hv₁.infinite_symmDiff h₁ ⟨i, rfl⟩) (fun i => hv₂.infinite_symmDiff h₂ ⟨i, rfl⟩)
  exact ⟨G, hG, fun ⟨i, hi⟩ => (hne i).1 hi.symm, fun ⟨i, hi⟩ => (hne i).2 hi.symm⟩

/-! ### The mixed set -/

/-- Problems in `P` are decidable. -/
theorem isDecidable_of_mem_P {α : Type} {enc : α ↪ List Bool} {A : Set α} (h : A ∈ P enc) :
    IsDecidable A enc :=
  let ⟨f, hf, hA⟩ := h
  isDecidable_iff.mpr ⟨f, hf.isComputable, hA⟩

/-- **The mixed set is decidable** when `G`, `A₁` and `A₂` are. -/
theorem isDecidable_ite {α : Type} {enc : α ↪ List Bool} {G A₁ A₂ : Set α}
    (hG : IsDecidable G enc) (hA₁ : IsDecidable A₁ enc) (hA₂ : IsDecidable A₂ enc) :
    IsDecidable (G.ite A₁ A₂) enc := by
  obtain ⟨g, hg, hG'⟩ := isDecidable_iff.mp hG
  obtain ⟨f₁, hf₁, hA₁'⟩ := isDecidable_iff.mp hA₁
  obtain ⟨f₂, hf₂, hA₂'⟩ := isDecidable_iff.mp hA₂
  have hsel := IsComputable.of_finite (encIn := encPair encBool (encPair encBool encBool))
    (encMid := encBool) fun p : Bool × Bool × Bool => if p.1 then p.2.1 else p.2.2
  refine isDecidable_iff.mpr ⟨fun a => if g a then f₁ a else f₂ a,
    hsel.comp (hg.prod (enc := encPair encBool (encPair encBool encBool))
      (hf₁.prod (enc := encPair encBool encBool) hf₂)), fun a => ?_⟩
  by_cases ha : a ∈ G
  · simp [Set.ite, ha, (hG' a).mp ha, hA₁']
  · simp [Set.ite, ha, (Bool.not_eq_true _).mp (mt (hG' a).mpr ha), hA₂']

/-- The **marked union** of two sets of words: `false :: x` for `x ∈ A₁` and `true :: x` for
`x ∈ A₂`. -/
@[expose] def markedUnion (A₁ A₂ : Set (List Bool)) : Set (List Bool) :=
  {w | ∃ x, (w = false :: x ∧ x ∈ A₁) ∨ (w = true :: x ∧ x ∈ A₂)}

theorem cons_mem_markedUnion {A₁ A₂ : Set (List Bool)} {b : Bool} {x : List Bool} :
    b :: x ∈ markedUnion A₁ A₂ ↔ x ∈ if b then A₂ else A₁ := by
  cases b <;> simp [markedUnion]

/-- **The mixed set reduces to the marked union** when `G ∈ P`. -/
theorem polyTimeReducible_ite_markedUnion {G A₁ A₂ : Set (List Bool)} (hG : G ∈ P encBits) :
    PolyTimeReducible encBits encBits (G.ite A₁ A₂) (markedUnion A₁ A₂) := by
  obtain ⟨g, hg, hG'⟩ := hG
  refine ⟨fun w => (!g w) :: w, by fun_prop, fun w => ?_⟩
  rw [cons_mem_markedUnion]
  by_cases hw : w ∈ G
  · simp [Set.ite, hw, (hG' w).mp hw]
  · simp [Set.ite, hw, (Bool.not_eq_true _).mp (mt (hG' w).mpr hw)]

/-- **The mixed set reduces to `A₂`** when `G` and `A₁` are in `P` and `A₂` has a member and a
non-member: on `G`, the reduction answers with the member or the non-member. -/
theorem polyTimeReducible_ite_of_mem_P {α : Type} {enc : α ↪ List Bool} {G A₁ A₂ : Set α}
    (hG : G ∈ P enc) (hA₁ : A₁ ∈ P enc) {y₀ y₁ : α} (hy₀ : y₀ ∉ A₂) (hy₁ : y₁ ∈ A₂) :
    PolyTimeReducible enc enc (G.ite A₁ A₂) A₂ := by
  obtain ⟨g, hg, hG'⟩ := hG
  obtain ⟨f, hf, hA₁'⟩ := hA₁
  refine ⟨fun a => if g a then (if f a then y₁ else y₀) else a, ?_, fun a => ?_⟩
  · have hid : ComputableInPolyTime (fun a : α => a) enc enc := .id'
    fun_prop
  · by_cases ha : a ∈ G
    · by_cases ha₁ : a ∈ A₁
      · simp [Set.ite, ha, ha₁, (hG' a).mp ha, (hA₁' a).mp ha₁, hy₁]
      · simp [Set.ite, ha, ha₁, (hG' a).mp ha, (Bool.not_eq_true _).mp (mt (hA₁' a).mpr ha₁),
          hy₀]
    · simp [Set.ite, ha, (Bool.not_eq_true _).mp (mt (hG' a).mpr ha)]

/-! ### `P` is recursively presentable -/

/-- **`P` is closed under finite variations.** -/
theorem closedUnderFiniteVariation_P {α : Type} (enc : α ↪ List Bool) :
    ClosedUnderFiniteVariation (P enc) := fun L L' hL hfin =>
  symmDiff_symmDiff_cancel_left L L' ▸ symmDiff_mem_P hL hfin.mem_P

namespace UniformDiagonalization

open Ladner (runIndexed clock exists_index_of_mem_P)

/-- The presentation of `P`: whether the machine with index `i` accepts `w` within its clock. -/
def pIndexed (p : ℕ × List Bool) : Bool :=
  decide (runIndexed p.1 p.2 (clock p.1 p.2.length) = ([eBit true], true))

theorem setOf_pIndexed_mem_P (i : ℕ) : {w | pIndexed (i, w) = true} ∈ P encBits := by
  have hc : ComputableInPolyTime (fun w : List Bool => clock i w.length) encBits encUnary :=
    (unary_pow i).comp (by fun_prop)
  have hd : ComputableInPolyTime (fun w : List Bool =>
      decide (runIndexed i w (clock i w.length) = ([eBit true], true))) encBits encBool := by
    fun_prop
  exact ⟨fun w => pIndexed (i, w), hd, fun _ => Iff.rfl⟩

theorem exists_setOf_pIndexed_eq {A : Set (List Bool)} (h : A ∈ P encBits) (B : ℕ) :
    ∃ i, B ≤ i ∧ {w | pIndexed (i, w) = true} = A := by
  obtain ⟨f, hf, i, hi, hrun⟩ := exists_index_of_mem_P h B
  refine ⟨i, hi, Set.ext fun w => ?_⟩
  rw [Set.mem_ofPred_eq, pIndexed, hrun, hf]
  cases f w <;> decide

/-- The presentation of `P` with the clock capped at `c`. -/
private def pIndexedCap (p : (ℕ × List Bool) × ℕ) : Bool :=
  decide (runIndexed p.1.1 p.1.2 (Ladner.capPow (2 * p.1.2.length + 2) p.1.1 p.2) =
    ([eBit true], true))

private theorem computableInPolyTime_pIndexedCap :
    ComputableInPolyTime pIndexedCap (encPair (encPair encUnary encBits) encUnary) encBool := by
  unfold pIndexedCap
  fun_prop

theorem clock_le_two_pow (i l : ℕ) : clock i l ≤ 2 ^ ((l + 1) * i) := by
  rw [clock, pow_mul]
  refine Nat.pow_le_pow_left ?_ i
  have h : l + 1 ≤ 2 ^ l := Nat.lt_two_pow_self
  rw [pow_succ]
  omega

/-- **The presentation of `P` is computable**, by running each machine within its clock, written
in unary with an exponential padding. -/
theorem isComputable_pIndexed : IsComputable pIndexed (encPair encUnary encBits) encBool := by
  have hL : ComputableInPolyTime (fun p : ℕ × List Bool => (p.2.length + 1) * p.1)
      (encPair encUnary encBits) encUnary := by fun_prop
  obtain ⟨C, c, hpad, -⟩ := hL.exists_computableInO_unary_two_pow
  have hpair := (isComputable_id (encPair encUnary encBits)).prod
    (enc := encPair (encPair encUnary encBits) encUnary) hpad.isComputable
  have h := computableInPolyTime_pIndexedCap.isComputable.comp hpair
  have heq : pIndexed = pIndexedCap ∘ fun a => (id a, 2 ^ ((a.2.length + 1) * a.1)) := by
    funext p
    have hc := clock_le_two_pow p.1 p.2.length
    rw [clock] at hc
    simp only [Function.comp_apply, id, pIndexedCap, pIndexed, Ladner.capPow, clock,
      min_eq_left hc]
    rfl
  rw [heq]
  exact h

end UniformDiagonalization

open UniformDiagonalization

/-- **`P` is recursively presentable**, by the machines run within polynomial clocks. -/
theorem recursivelyPresentable_P : RecursivelyPresentable encBits (P encBits) := by
  refine ⟨pIndexed, isComputable_pIndexed, Set.ext fun A => ⟨fun h => ?_, ?_⟩⟩
  · obtain ⟨i, -, hi⟩ := exists_setOf_pIndexed_eq h 0
    exact ⟨i, hi⟩
  · rintro ⟨i, rfl⟩
    exact setOf_pIndexed_mem_P i

/-- **Schöning's theorem for `P` against a second class.** -/
theorem exists_mem_P_ite_notMem_P {C : Set (Set (List Bool))}
    (hC : RecursivelyPresentable encBits C) (hv : ClosedUnderFiniteVariation C)
    {A₁ A₂ : Set (List Bool)} (hA₁ : IsDecidable A₁ encBits) (hA₂ : IsDecidable A₂ encBits)
    (h₁ : A₁ ∉ P encBits) (h₂ : A₂ ∉ C) :
    ∃ G ∈ P encBits, G.ite A₁ A₂ ∉ P encBits ∧ G.ite A₁ A₂ ∉ C :=
  exists_mem_P_ite_notMem recursivelyPresentable_P hC (closedUnderFiniteVariation_P encBits) hv
    hA₁ hA₂ h₁ h₂

end Cslib.Complexity
