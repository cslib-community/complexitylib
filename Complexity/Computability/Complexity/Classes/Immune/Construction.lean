/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Immune.Complete
public import Complexity.Computability.Complexity.Classes.Ladner.Basic
import Complexity.Computability.Complexity.Classes.Ladner.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Foundations.Data.List.Lookup
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential
import Mathlib.Data.Set.Finite.List

/-!
# A `P`-bi-immune problem in `E`

Exponential time contains `P`-bi-immune problems [Balcázar and Schöning][BalcazarSchoening1985].
This module constructs one by a priority (slow) diagonalization over all machines,
`Cslib.Complexity.BiImmune.language`, and proves that it is in `E`
(`Cslib.Complexity.BiImmune.language_mem_E`) and `P`-bi-immune
(`Cslib.Complexity.BiImmune.isBiImmune_language`).

Words are enumerated by index (`Cslib.Complexity.Ladner.word`), as are machines: the machine with
index `i` is the one described at the start of the `i`-th word, run by the universal function
(`Cslib.Complexity.Ladner.runIndexed`). Requirement `e` concerns the machine with index `e / 2`.
It asks for a word accepted by that machine inside the language when `e` is even, and outside it
when `e` is odd. At stage `n`, requirement `e` is *eligible* (`Cslib.Complexity.BiImmune.Eligible`)
when `e < n`, it has not acted before, and the machine accepts the `n`-th word within `n` steps.
The least eligible requirement `e`, if any, acts (`Cslib.Complexity.BiImmune.act` is `e + 1`). The
`n`-th word belongs to the language exactly when the requirement acting at stage `n` is even.
Otherwise the word stays outside.

Each requirement acts at most once. If the machine of requirement `e` accepts at infinitely many
stages, then `e` eventually acts: past the finitely many actions of smaller requirements, `e` is
the least eligible requirement (`Cslib.Complexity.BiImmune.exists_act_eq_succ`). Let `B` be an
infinite problem in `P`, decided by a machine within a polynomial time bound, and let `i` be an
index of that machine. The words of `B` have unboundedly large indices, and from some point on
the time bound is below the index. So both requirements `2 i` and `2 i + 1` act, at stages whose
words the machine accepts. These words are in `B`, one inside the language and one outside
(`Cslib.Complexity.BiImmune.exists_act_mem`). Hence the language is `P`-bi-immune
(`Cslib.Complexity.isBiImmune_P_iff`).

Stage `n` runs at most `n` machines for `n` steps each, so the table of the first `n` actions is
polynomial-time in `n` in unary (`Cslib.Complexity.BiImmune.computableInPolyTime_table`). The word
`y` has index below `2 ^ (|y| + 1)`, so its membership is computed in polynomial time from
`(y, 2 ^ |y|)`, and the language is in `E`
(`Cslib.Complexity.setOf_mem_E_of_computableInPolyTime_pad`).

By Berman's theorem (`Complexity.Computability.Complexity.Classes.Immune.Complete`), the language is
not complete for `E` or `EXP` (`Cslib.Complexity.BiImmune.not_polyTimeComplete_E_language`,
`Cslib.Complexity.BiImmune.not_polyTimeComplete_EXP_language`).

## Main definitions

* `Cslib.Complexity.BiImmune.accepts`: the machine of a requirement accepts at a stage.
* `Cslib.Complexity.BiImmune.actStep`, `Cslib.Complexity.BiImmune.table`,
  `Cslib.Complexity.BiImmune.act`: the requirement acting at each stage.
* `Cslib.Complexity.BiImmune.language`: the `P`-bi-immune problem.

## Main results

* `Cslib.Complexity.BiImmune.act_eq_succ_iff`, `Cslib.Complexity.BiImmune.act_eq_zero_iff`: the
  least eligible requirement acts.
* `Cslib.Complexity.BiImmune.exists_act_eq_succ`: a requirement whose machine accepts at
  infinitely many stages acts.
* `Cslib.Complexity.BiImmune.language_mem_E`: the problem is in `E`.
* `Cslib.Complexity.BiImmune.isBiImmune_language`: the problem is `P`-bi-immune.
* `Cslib.Complexity.BiImmune.exists_mem_E_isBiImmune_P`,
  `Cslib.Complexity.BiImmune.exists_mem_EXP_isBiImmune_P`: `E`, and so `EXP`, contain
  `P`-bi-immune problems.
* `Cslib.Complexity.BiImmune.not_polyTimeComplete_E_language`,
  `Cslib.Complexity.BiImmune.not_polyTimeComplete_EXP_language`: the problem is not complete for
  `E` or `EXP` under polynomial-time many-one reductions.

## References

* [J. L. Balcázar, U. Schöning, *Bi-immune sets for complexity classes*][BalcazarSchoening1985]
-/

public section

namespace Cslib.Complexity.BiImmune

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal Ladner

/-! ### The construction -/

/-- The machine of requirement `e` accepts at stage `n`: the machine with index `e / 2` accepts the
`n`-th word within `n` steps. -/
def accepts (e n : ℕ) : Bool :=
  decide (runIndexed (e / 2) (word n) n = ([eBit true], true))

/-- The action at stage `T.length`, from the table `T` of the earlier actions: `e + 1` for the
least requirement `e < T.length` that has not acted and whose machine accepts, or `0`. -/
def actStep (T : List ℕ) : ℕ :=
  ((List.range T.length).find? fun e => !(T.any fun a => a == e + 1) && accepts e T.length).elim
    0 (· + 1)

/-- The table of the actions at the first `n` stages. -/
def table (n : ℕ) : List ℕ := (fun T => T ++ [actStep T])^[n] []

/-- The action at stage `n`: `e + 1` if requirement `e` acts, `0` if none does. -/
def act (n : ℕ) : ℕ := actStep (table n)

/-- **The `P`-bi-immune problem**: the words whose stage is used by an even requirement. -/
def language : Set (List Bool) := {w | act (index w) % 2 = 1}

theorem mem_language_iff {w : List Bool} : w ∈ language ↔ act (index w) % 2 = 1 := Iff.rfl

theorem word_mem_language_iff {n : ℕ} : word n ∈ language ↔ act n % 2 = 1 := by
  rw [mem_language_iff, index_word]

theorem table_succ (n : ℕ) : table (n + 1) = table n ++ [act n] := by
  rw [table, Function.iterate_succ_apply']
  rfl

theorem table_eq (n : ℕ) : table n = (List.range n).map act := by
  induction n with
  | zero => rfl
  | succ n ih => rw [table_succ, List.range_succ, List.map_append, ← ih]; rfl

@[simp]
theorem length_table (n : ℕ) : (table n).length = n := by
  simp [table_eq]

theorem actStep_le (T : List ℕ) : actStep T ≤ T.length := by
  unfold actStep
  cases h : (List.range T.length).find? _ with
  | none => simp
  | some e =>
    have := List.mem_range.mp (List.mem_of_find?_eq_some h)
    simp only [Option.elim_some]
    omega

theorem act_le (n : ℕ) : act n ≤ n := by
  have := actStep_le (table n)
  rwa [length_table] at this

/-! ### The least eligible requirement acts -/

/-- Requirement `e` is eligible at stage `n`: `e < n`, it has not acted before, and its machine
accepts at stage `n`. -/
def Eligible (e n : ℕ) : Prop := e < n ∧ (∀ m < n, act m ≠ e + 1) ∧ accepts e n = true

private theorem eligible_iff {e n : ℕ} : Eligible e n ↔ e ∈ List.range n ∧
    (!((table n).any fun a => a == e + 1) && accepts e n) = true := by
  simp [Eligible, table_eq]

/-- **The least eligible requirement acts.** -/
theorem act_eq_succ_iff {n e : ℕ} :
    act n = e + 1 ↔ Eligible e n ∧ ∀ e' < e, ¬ Eligible e' n := by
  rw [act, actStep, length_table]
  cases h : (List.range n).find? (fun e => !((table n).any fun a => a == e + 1) && accepts e n)
    with
  | none =>
    rw [List.find?_eq_none] at h
    simp only [Option.elim_none, Nat.zero_ne_add_one, false_iff, not_and]
    intro he
    exact absurd (eligible_iff.mp he).2 (h e (eligible_iff.mp he).1)
  | some e₀ =>
    obtain ⟨hp, k, hk, hki, hmin⟩ := List.find?_eq_some_iff_getElem.mp h
    rw [List.getElem_range] at hki
    subst hki
    simp only [Option.elim_some, Nat.add_right_cancel_iff]
    have he₀ : Eligible k n := eligible_iff.mpr ⟨List.mem_of_find?_eq_some h, hp⟩
    have hmin' : ∀ e' < k, ¬ Eligible e' n := fun e' he' hel => by
      have := hmin e' he'
      rw [List.getElem_range, (eligible_iff.mp hel).2] at this
      exact absurd this (by decide)
    constructor
    · rintro rfl
      exact ⟨he₀, hmin'⟩
    · rintro ⟨he, hmin''⟩
      rcases lt_trichotomy k e with hlt | rfl | hgt
      · exact absurd he₀ (hmin'' k hlt)
      · rfl
      · exact absurd he (hmin' e hgt)

/-- **No requirement acts exactly when none is eligible.** -/
theorem act_eq_zero_iff {n : ℕ} : act n = 0 ↔ ∀ e, ¬ Eligible e n := by
  constructor
  · intro h e he
    classical
    have hex : ∃ e, Eligible e n := ⟨e, he⟩
    have := act_eq_succ_iff.mpr ⟨Nat.find_spec hex, fun e' h' => Nat.find_min hex h'⟩
    omega
  · intro h
    rcases hn : act n with _ | e
    · rfl
    · exact absurd (act_eq_succ_iff.mp hn).1 (h e)

/-- **Each requirement acts at most once.** -/
theorem eq_of_act_eq_succ {m n e : ℕ} (hm : act m = e + 1) (hn : act n = e + 1) : m = n := by
  rcases lt_trichotomy m n with h | h | h
  · exact absurd hm ((act_eq_succ_iff.mp hn).1.2.1 m h)
  · exact h
  · exact absurd hn ((act_eq_succ_iff.mp hm).1.2.1 n h)

/-- **A requirement whose machine accepts at infinitely many stages acts**: past the finitely many
actions of smaller requirements, it is the least eligible requirement. -/
theorem exists_act_eq_succ {e : ℕ} (h : ∀ N, ∃ n ≥ N, accepts e n = true) :
    ∃ n, act n = e + 1 := by
  by_contra hne
  simp only [not_exists] at hne
  -- the stages where a smaller requirement acts
  have hfin : {n | ∃ e' < e, act n = e' + 1}.Finite := by
    have : {n | ∃ e' < e, act n = e' + 1} = ⋃ e' ∈ Finset.range e, {n | act n = e' + 1} := by
      ext n
      simp
    rw [this]
    exact Set.Finite.biUnion (Finset.finite_toSet _) fun e' _ =>
      Set.Subsingleton.finite fun m hm n hn => eq_of_act_eq_succ hm hn
  obtain ⟨N₀, hN₀⟩ := hfin.bddAbove
  obtain ⟨n, hn, hacc⟩ := h (N₀ + e + 1)
  have hel : Eligible e n := ⟨by omega, fun m _ => hne m, hacc⟩
  rcases hact : act n with _ | e'
  · exact act_eq_zero_iff.mp hact e hel
  · have hle : e' ≤ e := by
      by_contra hlt
      exact (act_eq_succ_iff.mp hact).2 e (by omega) hel
    rcases hle.lt_or_eq with hlt | rfl
    · have := hN₀ ⟨e', hlt, hact⟩
      omega
    · exact hne n hact

/-! ### The problem is in `E` -/

private theorem computableInPolyTime_accepts :
    ComputableInPolyTime (fun p : ℕ × ℕ => accepts p.1 p.2) (encPair encUnary encUnary)
      encBool := by
  unfold accepts
  fun_prop

private theorem computableInPolyTime_actStep :
    ComputableInPolyTime actStep (encList encUnary) encUnary := by
  have h := computableInPolyTime_accepts
  unfold actStep
  fun_prop

/-- **The tables of actions are polynomial-time** in their length, in unary. -/
theorem computableInPolyTime_table : ComputableInPolyTime table encUnary (encList encUnary) :=
  ComputableInPolyTime.iterate (encIn := encUnary) (encState := encList encUnary)
    (count := fun n => n) (init := fun _ => []) (step := fun T => T ++ [actStep T]) (by fun_prop)
    (by fun_prop) (by have := computableInPolyTime_actStep; fun_prop)
    (bound := fun n => n * (2 * n + 1))
    (.of_forall_le 2 2 fun n => by simp only [encUnary_apply, List.length_replicate]; nlinarith)
    (fun n i hi => by
      change (encList encUnary (table i)).length ≤ _
      calc (encList encUnary (table i)).length ≤ (table i).length * (2 * n + 1) :=
            length_encList_le encUnary _ fun a ha => by
              rw [table_eq] at ha
              obtain ⟨m, hm, rfl⟩ := List.mem_map.mp ha
              simpa using (act_le m).trans (by have := List.mem_range.mp hm; omega)
        _ ≤ n * (2 * n + 1) := by rw [length_table]; exact Nat.mul_le_mul_right _ hi)

/-- Membership of `y`, read from the table of the actions at the first `2 * N` stages. -/
private def memTable (p : List Bool × ℕ) : Bool :=
  ((List.range (2 * p.2)).find? fun j => decide (word j = p.1)).elim false
    fun j => decide ((table (2 * p.2)).getD j 0 % 2 = 1)

private theorem computableInPolyTime_memTable :
    ComputableInPolyTime memTable (encPair encBits encUnary) encBool := by
  have ht := computableInPolyTime_table
  unfold memTable
  fun_prop

private theorem memTable_iff {y : List Bool} {N : ℕ} (hN : index y < 2 * N) :
    memTable (y, N) = true ↔ y ∈ language := by
  have hfind : (List.range (2 * N)).find? (fun j => decide (word j = y)) = some (index y) := by
    rw [List.find?_range_eq_some]
    refine ⟨by simp, List.mem_range.mpr hN, fun j hj => ?_⟩
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
    rintro rfl
    rw [index_word] at hj
    exact lt_irrefl _ hj
  rw [memTable, hfind, Option.elim_some, table_eq, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range hN]
  simp [language]

/-- **The problem is in `E`.** -/
theorem language_mem_E : language ∈ E encBits := by
  have h := setOf_mem_E_of_computableInPolyTime_pad computableInPolyTime_memTable
  convert h using 1
  ext y
  simp only [Set.mem_ofPred_eq]
  rw [memTable_iff]
  have := index_add_two_le y
  rw [pow_succ] at this
  omega

theorem language_mem_EXP : language ∈ EXP encBits := E_subset_EXP language_mem_E

/-! ### The problem is `P`-bi-immune -/

/-- **Every infinite problem in `P` is met by requirements of both parities**: for `r < 2`, some
requirement `2 * i + r` acts at a stage whose word is in the problem. -/
theorem exists_act_mem {B : Set (List Bool)} (hB : B ∈ P encBits) (hinf : B.Infinite) {r : ℕ}
    (hr : r < 2) : ∃ i n, word n ∈ B ∧ act n = 2 * i + r + 1 := by
  obtain ⟨f, ⟨t, s, ht, -, k, State, hfinite, tm, htm⟩, hf⟩ := mem_P.mp hB
  have := Fintype.ofFinite State
  let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  have hrun (x : List Bool) : (tm.runFrom (tm.initCfg x) (t x.length)).Halted ∧
      (tm.runFrom (tm.initCfg x) (t x.length)).output = [f x] :=
    (htm x).runFrom_of_le le_rfl
  obtain ⟨L, hL⟩ := Filter.eventually_atTop.mp (PolynomiallyBounded.eventually_lt_two_pow ht)
  obtain ⟨i, -, hdesc⟩ := exists_index_ge (desc eS eBit tm) 0
  have hdiv : (2 * i + r) / 2 = i := by omega
  -- the machine accepts at the stages of the long words of `B`
  have hinfty : ∀ N, ∃ n ≥ N, accepts (2 * i + r) n = true := by
    intro N
    obtain ⟨w, hwB, hw⟩ := (hinf.sdiff (List.finite_length_lt Bool (max L N + 1))).nonempty
    simp only [Set.mem_ofPred_eq, not_lt] at hw
    have hidx := two_pow_length_word_le (index w)
    rw [word_index] at hidx
    have hlt := hL w.length (by omega)
    have hN : N < 2 ^ w.length :=
      Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
    refine ⟨index w, by omega, ?_⟩
    rw [accepts, decide_eq_true_iff, runIndexed, hdiv, hdesc, word_index,
      universal_desc_of_halted eS tm (t := fun x => t x.length) hrun (by omega), (hf w).mp hwB]
  obtain ⟨n, hn⟩ := exists_act_eq_succ hinfty
  refine ⟨i, n, ?_, hn⟩
  -- acting means that the machine accepted the word, so the word is in `B`
  have hacc := (act_eq_succ_iff.mp hn).1.2.2
  rw [accepts, decide_eq_true_iff, runIndexed, hdiv, hdesc, universal_desc] at hacc
  obtain ⟨hout, hst⟩ := Prod.mk.inj hacc
  have hhalt : (tm.runFrom (tm.initCfg (word n)) n).state = none :=
    Option.isNone_iff_eq_none.mp hst
  obtain ⟨hhalt', hout'⟩ := hrun (word n)
  have heq : tm.runFrom (tm.initCfg (word n)) n =
      tm.runFrom (tm.initCfg (word n)) (t (word n).length) := by
    rcases le_total n (t (word n).length) with hle | hle
    · exact (MultiTapeTM.runFrom_eq_of_halt tm _ hle hhalt).symm
    · simp only [Cfg.Halted] at hhalt'
      exact MultiTapeTM.runFrom_eq_of_halt tm _ hle hhalt'
  rw [heq, hout', List.map_singleton, List.singleton_inj] at hout
  exact (hf _).mpr (eBit.injective hout)

/-- **The problem is `P`-bi-immune.** -/
theorem isBiImmune_language : IsBiImmune (P encBits) language := by
  rw [isBiImmune_P_iff]
  intro B hB hinf
  obtain ⟨i, n, hn, hact⟩ := exists_act_mem hB hinf (r := 0) (by omega)
  obtain ⟨i', n', hn', hact'⟩ := exists_act_mem hB hinf (r := 1) (by omega)
  refine ⟨⟨word n, hn, ?_⟩, ⟨word n', hn', ?_⟩⟩
  · rw [word_mem_language_iff, hact]
    omega
  · rw [word_mem_language_iff, hact']
    omega

/-- **`E` contains a `P`-bi-immune problem** [Balcázar and Schöning][BalcazarSchoening1985]. -/
theorem exists_mem_E_isBiImmune_P : ∃ A ∈ E encBits, IsBiImmune (P encBits) A :=
  ⟨language, language_mem_E, isBiImmune_language⟩

/-- **`EXP` contains a `P`-bi-immune problem.** -/
theorem exists_mem_EXP_isBiImmune_P : ∃ A ∈ EXP encBits, IsBiImmune (P encBits) A :=
  ⟨language, language_mem_EXP, isBiImmune_language⟩

/-! ### The problem is not complete -/

/-- **The problem is not complete for `E`** under polynomial-time many-one reductions. -/
theorem not_polyTimeComplete_E_language : ¬ PolyTimeComplete @E encBits language :=
  fun h => not_isBiImmune_P_of_polyTimeComplete_E h isBiImmune_language

/-- **The problem is not hard for `E`** under polynomial-time many-one reductions. -/
theorem not_polyTimeHard_E_language : ¬ PolyTimeHard @E encBits language :=
  fun h => not_polyTimeComplete_E_language ⟨language_mem_E, h⟩

/-- **The problem is not complete for `EXP`** under polynomial-time many-one reductions. -/
theorem not_polyTimeComplete_EXP_language : ¬ PolyTimeComplete @EXP encBits language :=
  fun h => not_isBiImmune_P_of_polyTimeComplete_EXP h isBiImmune_language

/-- **The problem is not hard for `EXP`** under polynomial-time many-one reductions. -/
theorem not_polyTimeHard_EXP_language : ¬ PolyTimeHard @EXP encBits language :=
  fun h => not_polyTimeComplete_EXP_language ⟨language_mem_EXP, h⟩

end Cslib.Complexity.BiImmune
