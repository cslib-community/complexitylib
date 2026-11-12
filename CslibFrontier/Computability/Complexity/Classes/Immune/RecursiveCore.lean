/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Immune.PolyTimeCore
public import CslibFrontier.Computability.Complexity.Classes.Ladner.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Clocked
import CslibFrontier.Computability.Complexity.Classes.EXP.Decidable
import CslibFrontier.Computability.Complexity.Classes.Ladner.PolyTime
import CslibFrontier.Computability.Complexity.Classes.Ladner.Stages
import CslibFrontier.Computability.Complexity.Classes.P.Closure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.CourseOfValues
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential
import Mathlib.Data.Set.Finite.List

/-!
# Recursive polynomial complexity cores

[Lynch, Lemma 1][Lynch1975] shows that a recursive set outside `P` has an infinite *recursive*
polynomial complexity core. This module proves it for problems on bit strings, with a core that is
also *proper*, that is, inside the set: a decidable problem `A` outside `P` has an infinite
decidable subset `X` on which every machine deciding `A` runs in superpolynomial time almost
everywhere (`Cslib.Complexity.exists_infinite_isDecidable_isPolyTimeCore`). Lynch's core need not
lie inside the set. The proper and recursive form is a strengthening proved here, by a standard
delayed diagonalization; we did not verify a primary source stating it in this form. The
class-generic core theorem (`Cslib.Complexity.exists_infinite_isComplexityCore_P_subset`) gives a
proper core that is not claimed to be decidable.

The statement is restricted to bit strings (`encBits`). The construction runs a decider of `A` on
every bit string and enumerates every bit string as a candidate. Under a general encoding `enc`, a
decider of `A` only answers on the range of `enc`, so the construction would need at least that the
range of `enc` be decidable on all bit strings, which a general encoding does not provide.

## The construction

Fix the description `d` of a decider of `A`, whose clocked runs
(`Turing.MultiTapeTM.Universal.runBool`) are sound and eventually complete
(`Turing.MultiTapeTM.IsComputable.exists_runBool`).

* **Requirements.** Requirement `e` (`Cslib.Complexity.RecursiveCore.requirement`) is the problem
  of the words `w` that the machine with index `e` (`Cslib.Complexity.Ladner.runIndexed`) accepts
  within `(2 |w| + 2) ^ e` steps (`Cslib.Complexity.Ladner.clock`). Every requirement is in `P`,
  and every problem in `P` is a requirement: the clock of a large enough index exceeds the time
  bound of its decider (`Cslib.Complexity.RecursiveCore.exists_requirement_eq`).
* **Stages.** Stage `n` decides whether the `n`-th word (`Cslib.Complexity.Ladner.word`) is
  selected. Everything at stage `n` is clocked by `n`. The decider of `A` is run for `n` steps,
  and membership in requirement `e` is known at stage `n` only when the clock of `e` is at most
  `n` (`Cslib.Complexity.RecursiveCore.memReq`). The *count* at stage `n` is the number of earlier
  selected words that the decider has accepted within `n` steps. Requirement `e` is *refuted* at
  stage `n` when an earlier word is known to be in requirement `e` and rejected by the decider
  within `n` steps (`Cslib.Complexity.RecursiveCore.refuted`). The `n`-th word is selected when
  every requirement below the count is refuted or is not known to contain the word
  (`Cslib.Complexity.RecursiveCore.selects_eq_true_iff`). The core is `A ∩ selected d`
  (`Cslib.Complexity.RecursiveCore.core`).

Stage `n` runs at most `n` machines on words with indices below `n` for at most `n` steps, so the
table of the first `n` stages is polynomial-time in `n` in unary, and `selected d` is in `E`
(`Cslib.Complexity.RecursiveCore.selected_mem_E`, through
`Cslib.Complexity.Ladner.setOf_index_mem_E_of_computableInPolyTime`). The core is therefore
decidable.

**The core is a core** (`Cslib.Complexity.RecursiveCore.isComplexityCore_core`). Let `B ∈ P` lie
inside `A`, and let `B` be requirement `e`. Every refutation is sound, so `e` is never refuted. If
the core is infinite, then from some stage on the count exceeds `e`, and from some length on the
clock of `e` on the `n`-th word is at most `n`. Past both, the core avoids `B`.

**The core is infinite** (`Cslib.Complexity.RecursiveCore.infinite_core`). If it were finite, the
count would stay below its size `K`. Every requirement below `K` that is not inside `A` is
eventually refuted, since the decider of `A` eventually rejects a witness. From then on, every
word of `A` outside the core lies in one of the requirements below `K` inside `A`. So `A` is a
finite union of problems in `P` and a finite set, and `A` would be in `P`.

## Main definitions

* `Cslib.Complexity.RecursiveCore.requirement`: the problems in `P`, by clocked machine index.
* `Cslib.Complexity.RecursiveCore.selected`, `Cslib.Complexity.RecursiveCore.core`: the words
  selected by the stages, and the core.

## Main results

* `Cslib.Complexity.RecursiveCore.exists_requirement_eq`: every problem in `P` is a requirement.
* `Cslib.Complexity.RecursiveCore.selected_mem_E`: the selected words form a problem in `E`.
* `Cslib.Complexity.RecursiveCore.isComplexityCore_core`,
  `Cslib.Complexity.RecursiveCore.infinite_core`: the core is a complexity core for `P`, and it is
  infinite when the problem is outside `P`.
* `Cslib.Complexity.exists_infinite_isDecidable_isPolyTimeCore`: Lynch's Lemma 1 with a proper
  core, for problems on bit strings.
* `Cslib.Complexity.notMem_P_iff_exists_infinite_isDecidable_isPolyTimeCore`: a decidable problem
  is outside `P` exactly when it has an infinite decidable polynomial complexity core inside it.

## References

* [N. Lynch, *On reducibility to complex or sparse sets*][Lynch1975]
-/

public section

namespace Cslib.Complexity.RecursiveCore

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal Ladner

/-! ### The requirements -/

/-- **Requirement `e`**: the problem of the words `w` that the machine with index `e` accepts within
`clock e |w| = (2 |w| + 2) ^ e` steps. -/
def requirement (e : ℕ) : Set (List Bool) :=
  {w | runIndexed e w (clock e w.length) = ([eBit true], true)}

/-- Membership in requirement `e`, known at stage `n`: the clock of `e` on `w` is at most `n`, and
the machine accepts within the clock. The clock is computed capped at `n + 1`, so that this is
polynomial-time in `n` in unary. -/
def memReq (e n : ℕ) (w : List Bool) : Bool :=
  decide (capPow (2 * w.length + 2) e (n + 1) ≤ n) &&
    decide (runIndexed e w (capPow (2 * w.length + 2) e (n + 1)) = ([eBit true], true))

theorem memReq_iff {e n : ℕ} {w : List Bool} :
    memReq e n w = true ↔ clock e w.length ≤ n ∧ w ∈ requirement e := by
  have hcap : capPow (2 * w.length + 2) e (n + 1) ≤ n ↔ clock e w.length ≤ n := by
    unfold capPow clock
    omega
  constructor
  · intro h
    simp only [memReq, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h₁, h₂⟩ := h
    have heq : capPow (2 * w.length + 2) e (n + 1) = clock e w.length := by
      unfold capPow clock at *
      omega
    rw [heq] at h₂
    exact ⟨hcap.mp h₁, h₂⟩
  · rintro ⟨hc, hw⟩
    have heq : capPow (2 * w.length + 2) e (n + 1) = clock e w.length := by
      unfold capPow clock at *
      omega
    simp only [memReq, Bool.and_eq_true, decide_eq_true_eq, heq]
    exact ⟨hc, hw⟩

/-- **Every requirement is in `P`**: its clock is a polynomial. -/
theorem requirement_mem_P (e : ℕ) : requirement e ∈ P encBits := by
  refine ⟨fun w => decide (runIndexed e w (clock e w.length) = ([eBit true], true)), ?_,
    fun w => by simp [requirement]⟩
  unfold clock
  fun_prop

/-- **Every problem in `P` is a requirement**, with arbitrarily large indices: machines of
arbitrarily large index decide it within their clock (`Ladner.exists_index_of_mem_P`). -/
theorem exists_requirement_eq {B : Set (List Bool)} (hB : B ∈ P encBits) (N : ℕ) :
    ∃ e, N ≤ e ∧ requirement e = B := by
  obtain ⟨f, hf, e, he, hrun⟩ := exists_index_of_mem_P hB N
  refine ⟨e, he, Set.ext fun w => ?_⟩
  simp only [requirement, Set.mem_ofPred_eq]
  rw [hrun w, Prod.mk.injEq, List.singleton_inj, and_iff_left rfl, (hf w)]
  exact ⟨fun h => eBit.injective h, fun h => h ▸ rfl⟩

/-! ### The stages -/

section Stages

variable (d : Desc)

/-- The decider described by `d` halts on the `m`-th word within `n` steps with answer `b`. -/
def decAt (n m : ℕ) (b : Bool) : Bool :=
  decide (runBool d (word m) n = some b)

/-- The count at stage `T.length`, from the table `T` of the earlier stages: the number of earlier
selected words that the decider accepts within `T.length` steps. -/
def coreCount (T : List Bool) : ℕ :=
  (List.range T.length).countP fun m => T.getD m false && decAt d T.length m true

/-- Requirement `e` is refuted at stage `n`: an earlier word is known at stage `n` to be in
requirement `e`, and the decider rejects it within `n` steps. -/
def refuted (e n : ℕ) : Bool :=
  (List.range n).any fun m => memReq e n (word m) && decAt d n m false

/-- The decision of stage `T.length`, from the table `T` of the earlier stages: every requirement
below the count is refuted or is not known to contain the word. -/
def stageBit (T : List Bool) : Bool :=
  (List.range (coreCount d T)).all fun e =>
    refuted d e T.length || !memReq e T.length (word T.length)

/-- The table of the decisions of the first `n` stages. -/
def table (n : ℕ) : List Bool := List.courseOfValues (stageBit d) n

/-- Stage `n` selects the `n`-th word. -/
def selects (n : ℕ) : Bool := stageBit d (table d n)

/-- The words selected by their stage. -/
def selected : Set (List Bool) := {w | selects d (index w) = true}

/-- **The core**: the selected words of `A`. -/
def core (A : Set (List Bool)) : Set (List Bool) := A ∩ selected d

/-! ### The stages are polynomial-time -/

private theorem computableInPolyTime_decAt :
    ComputableInPolyTime (fun p : ℕ × ℕ × Bool => decAt d p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encUnary encBool)) encBool := by
  unfold decAt
  fun_prop

private theorem computableInPolyTime_memReq :
    ComputableInPolyTime (fun p : ℕ × ℕ × List Bool => memReq p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encUnary encBits)) encBool := by
  unfold memReq
  fun_prop

private theorem computableInPolyTime_coreCount :
    ComputableInPolyTime (coreCount d) encBits encUnary := by
  have h := computableInPolyTime_decAt d
  unfold coreCount
  fun_prop

private theorem computableInPolyTime_refuted :
    ComputableInPolyTime (fun p : ℕ × ℕ => refuted d p.1 p.2)
      (encPair encUnary encUnary) encBool := by
  have h₁ := computableInPolyTime_decAt d
  have h₂ := computableInPolyTime_memReq
  unfold refuted
  fun_prop

private theorem computableInPolyTime_stageBit :
    ComputableInPolyTime (stageBit d) encBits encBool := by
  have h₁ := computableInPolyTime_coreCount d
  have h₂ := computableInPolyTime_refuted d
  have h₃ := computableInPolyTime_memReq
  unfold stageBit
  fun_prop

theorem table_succ (n : ℕ) : table d (n + 1) = table d n ++ [selects d n] := by
  rw [table, List.courseOfValues_succ]
  rfl

theorem table_eq (n : ℕ) : table d n = (List.range n).map (selects d) :=
  List.courseOfValues_eq (stageBit d) n

@[simp]
theorem length_table (n : ℕ) : (table d n).length = n :=
  List.length_courseOfValues (stageBit d) n

/-- **The stage tables are polynomial-time** in their length, in unary. -/
theorem computableInPolyTime_table : ComputableInPolyTime (table d) encUnary encBits :=
  .bitsCourseOfValues (computableInPolyTime_stageBit d)

/-- **The stage decisions are polynomial-time** in the stage, in unary. -/
theorem computableInPolyTime_selects : ComputableInPolyTime (selects d) encUnary encBool := by
  have h₁ := computableInPolyTime_stageBit d
  have h₂ := computableInPolyTime_table d
  unfold selects
  fun_prop

/-- **The selected words form a problem in `E`**: the decision at each stage is polynomial-time in
the stage (`Cslib.Complexity.Ladner.setOf_index_mem_E_of_computableInPolyTime`). -/
theorem selected_mem_E : selected d ∈ E encBits :=
  setOf_index_mem_E_of_computableInPolyTime (computableInPolyTime_selects d)

theorem isDecidable_selected : IsDecidable (selected d) encBits :=
  isDecidable_of_mem_E (selected_mem_E d)

/-- **The core of a decidable problem is decidable.** -/
theorem isDecidable_core {A : Set (List Bool)} (hA : IsDecidable A encBits) :
    IsDecidable (core d A) encBits :=
  hA.inter (isDecidable_selected d)

theorem core_subset (A : Set (List Bool)) : core d A ⊆ A := Set.inter_subset_left

end Stages

/-! ### Correctness -/

section Correctness

variable {d : Desc} {A : Set (List Bool)}

private theorem decAt_eq_true_iff {n m : ℕ} {b : Bool} :
    decAt d n m b = true ↔ runBool d (word m) n = some b :=
  decide_eq_true_iff

/-- A halted answer of the decider is correct. -/
private theorem decAt_sound (hs : ∀ w t b, runBool d w t = some b → b = indicator A w) {n m : ℕ}
    {b : Bool} (h : decAt d n m b = true) : b = indicator A (word m) :=
  hs _ _ _ (decAt_eq_true_iff.mp h)

/-- The decider eventually halts with the correct answer. -/
private theorem decAt_complete
    (hc : ∀ w, ∃ T, ∀ t, T ≤ t → runBool d w t = some (indicator A w)) (m : ℕ) :
    ∃ T, ∀ n ≥ T, decAt d n m (indicator A (word m)) = true :=
  let ⟨T, hT⟩ := hc (word m)
  ⟨T, fun n hn => decAt_eq_true_iff.mpr (hT n hn)⟩

theorem coreCount_table (n : ℕ) : coreCount d (table d n) =
    ((List.range n).filter fun m => selects d m && decAt d n m true).length := by
  rw [coreCount, length_table, List.countP_eq_length_filter]
  congr 1
  refine List.filter_congr fun m hm => ?_
  rw [table_eq, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (List.mem_range.mp hm)]
  rfl

/-- **Stage `n` selects its word** exactly when every requirement below the count is refuted or is
not known to contain the word. -/
theorem selects_eq_true_iff {n : ℕ} : selects d n = true ↔
    ∀ e < coreCount d (table d n), refuted d e n = true ∨ memReq e n (word n) = false := by
  rw [selects, stageBit, List.all_eq_true, length_table]
  simp only [List.mem_range, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]

/-- **Refutations are sound**: a refuted requirement is not inside `A`. -/
private theorem not_subset_of_refuted (hs : ∀ w t b, runBool d w t = some b → b = indicator A w)
    {e n : ℕ} (h : refuted d e n = true) : ¬ requirement e ⊆ A := by
  intro hsub
  obtain ⟨m, -, hm⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true] at hm
  have hmem := (memReq_iff.mp hm.1).2
  have hfalse := decAt_sound hs hm.2
  exact (indicator_eq_false_iff.mp hfalse.symm) (hsub hmem)

/-- **Refutations are complete**: a requirement not inside `A` is refuted from some stage on. -/
private theorem exists_refuted (hc : ∀ w, ∃ T, ∀ t, T ≤ t → runBool d w t = some (indicator A w))
    {e : ℕ} (h : ¬ requirement e ⊆ A) :
    ∃ N, ∀ n ≥ N, refuted d e n = true := by
  obtain ⟨w, hwB, hwA⟩ := Set.not_subset.mp h
  obtain ⟨T, hT⟩ := decAt_complete hc (index w)
  refine ⟨T + index w + 1 + clock e w.length, fun n hn => List.any_eq_true.mpr
    ⟨index w, List.mem_range.mpr (by omega), ?_⟩⟩
  have hdec := hT n (by omega)
  rw [word_index, indicator_eq_false_iff.mpr hwA] at hdec
  rw [Bool.and_eq_true, word_index, memReq_iff]
  exact ⟨⟨by omega, hwB⟩, hdec⟩

/-- The words counted at any stage are in the core. -/
private theorem coreCount_le (hs : ∀ w t b, runBool d w t = some b → b = indicator A w)
    {S : Finset ℕ} (hS : ∀ m, word m ∈ core d A → m ∈ S) (n : ℕ) :
    coreCount d (table d n) ≤ S.card := by
  rw [coreCount_table, ← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
  refine Finset.card_le_card fun m hm => hS m ?_
  rw [List.mem_toFinset, List.mem_filter, Bool.and_eq_true] at hm
  exact ⟨indicator_eq_true_iff.mp (decAt_sound hs hm.2.2).symm, by simpa [selected] using hm.2.1⟩

/-- Finitely many words of the core are all counted from some stage on. -/
private theorem exists_card_le_coreCount
    (hc : ∀ w, ∃ T, ∀ t, T ≤ t → runBool d w t = some (indicator A w)) (F : Finset ℕ)
    (hF : ∀ m ∈ F, word m ∈ core d A) :
    ∃ N, ∀ n ≥ N, F.card ≤ coreCount d (table d n) := by
  choose T hT using decAt_complete hc
  refine ⟨F.sup fun m => T m + m + 1, fun n hn => ?_⟩
  rw [coreCount_table, ← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
  refine Finset.card_le_card fun m hm => ?_
  have hle : T m + m + 1 ≤ n := (Finset.le_sup (f := fun m => T m + m + 1) hm).trans hn
  obtain ⟨hA, hY⟩ := hF m hm
  have hdec := hT m n (by omega)
  rw [indicator_eq_true_iff.mpr hA] at hdec
  rw [List.mem_toFinset, List.mem_filter, Bool.and_eq_true, List.mem_range]
  exact ⟨by omega, by simpa [selected] using hY, hdec⟩

/-- **The core is a complexity core of `A` for `P`.** A problem in `P` inside `A` is a requirement
`e` that is never refuted. If the core is infinite, the count eventually exceeds `e`, so past the
stages where the clock of `e` has not yet run out, the core avoids the problem. -/
theorem isComplexityCore_core (hs : ∀ w t b, runBool d w t = some b → b = indicator A w)
    (hc : ∀ w, ∃ T, ∀ t, T ≤ t → runBool d w t = some (indicator A w)) :
    IsComplexityCore (P encBits) A (core d A) := by
  rw [isComplexityCore_iff]
  rintro B hB (hBA | hBA)
  swap
  · exact Set.finite_empty.subset fun w ⟨hwB, hwA, _⟩ => hBA hwB hwA
  rcases Set.finite_or_infinite (B ∩ core d A) with hfin | hinf
  · exact hfin
  exfalso
  obtain ⟨e, -, rfl⟩ := exists_requirement_eq hB 0
  -- the count eventually exceeds `e`
  have hcore : {m | word m ∈ core d A}.Infinite := fun hfin' => by
    refine (hinf.mono Set.inter_subset_right) ((hfin'.image word).subset fun w hw => ?_)
    exact ⟨index w, by simpa using hw, word_index w⟩
  obtain ⟨F, hFsub, hFcard⟩ := hcore.exists_subset_card_eq (e + 1)
  obtain ⟨N, hN⟩ := exists_card_le_coreCount hc F fun m hm => hFsub hm
  -- from some length on, the clock of `e` is below `2 ^ l`
  have hclock : PolynomiallyBounded (clock e) := by unfold clock; fun_prop
  obtain ⟨L, hL⟩ := Filter.eventually_atTop.mp (PolynomiallyBounded.eventually_lt_two_pow hclock)
  refine hinf (((List.finite_length_lt Bool L).union
    ((Set.finite_lt_nat N).image word)).subset fun w ⟨hwB, hwA, hwY⟩ => ?_)
  by_contra hw
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_image, not_or, not_lt, not_exists,
    not_and] at hw
  obtain ⟨hlen, hidx⟩ := hw
  have hNi : N ≤ index w := by
    by_contra h
    exact hidx (index w) (by omega) (word_index w)
  have he : e < coreCount d (table d (index w)) := by
    have := hN (index w) hNi
    omega
  rcases (selects_eq_true_iff.mp hwY) e he with href | hmem
  · exact not_subset_of_refuted hs href hBA
  · have hlt := hL w.length hlen
    have hidx' := two_pow_length_word_le (index w)
    rw [word_index] at hidx'
    rw [word_index, Bool.eq_false_iff, Ne, memReq_iff] at hmem
    exact hmem ⟨by omega, hwB⟩

/-- **The core is infinite when `A` is not in `P`.** If the core were finite, the count would stay
below its size. The requirements below that size that are not inside `A` are refuted from some
stage on, and from then on every word of `A` outside the core lies in one of the finitely many
requirements below that size inside `A`. Then `A` would be in `P`. -/
theorem infinite_core (hs : ∀ w t b, runBool d w t = some b → b = indicator A w)
    (hc : ∀ w, ∃ T, ∀ t, T ≤ t → runBool d w t = some (indicator A w))
    (hA : A ∉ P encBits) : (core d A).Infinite := by
  classical
  intro hfin
  obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, ∀ m, word m ∈ core d A → m ∈ S :=
    ⟨((hfin.preimage word_injective.injOn).toFinset), fun m hm => by simpa using hm⟩
  -- the requirements below `S.card` not inside `A` are all refuted from stage `N` on
  choose! R hR using fun e (h : ¬ requirement e ⊆ A) => exists_refuted hc h
  let N := (Finset.range S.card).sup R
  let U := ((Finset.range S.card).filter fun e => requirement e ⊆ A).sup requirement
  have hUP : U ∈ P encBits :=
    Finset.sup_mem (P encBits) empty_mem_P (fun _ hx _ hy => union_mem_P hx hy) _ _
      fun e _ => requirement_mem_P e
  have hUA : U ⊆ A := Finset.sup_le fun e he => (Finset.mem_filter.mp he).2
  apply hA
  have hfin' : (A \ U).Finite := by
    refine (hfin.union ((Set.finite_lt_nat N).image word)).subset fun w ⟨hwA, hwU⟩ => ?_
    by_contra hw
    simp only [core, Set.mem_union, Set.mem_inter_iff, Set.mem_image, Set.mem_ofPred_eq, not_or,
      not_and, not_exists] at hw
    obtain ⟨hwY, hidx⟩ := hw
    have hNi : N ≤ index w := by
      by_contra h
      exact hidx (index w) (by omega) (word_index w)
    have hnY : selects d (index w) = false := by
      simpa [selected] using hwY hwA
    rw [← Bool.not_eq_true, selects_eq_true_iff] at hnY
    obtain ⟨e, he, hne⟩ := not_forall₂.mp hnY
    obtain ⟨hnref, hmem⟩ := not_or.mp hne
    have heS : e < S.card := he.trans_le (coreCount_le hs hS _)
    replace hmem : memReq e (index w) (word (index w)) = true := by simpa using hmem
    rw [word_index, memReq_iff] at hmem
    by_cases hsub : requirement e ⊆ A
    · exact hwU (Finset.le_sup (f := requirement)
        (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr heS, hsub⟩) hmem.2)
    · have hRN : R e ≤ N := Finset.le_sup (f := R) (Finset.mem_range.mpr heS)
      exact hnref (hR e hsub (index w) (hRN.trans hNi))
  rw [← Set.union_sdiff_cancel hUA]
  exact union_mem_P hUP hfin'.mem_P

end Correctness

end Cslib.Complexity.RecursiveCore

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM

/-- **Decidable problems outside `P` have infinite decidable polynomial complexity cores inside
them** ([Lynch, Lemma 1][Lynch1975], strengthened to a proper core; for problems on bit strings): a
decidable problem `A` outside `P` has an infinite decidable subset on which every machine deciding
`A` runs in superpolynomial time almost everywhere. -/
theorem exists_infinite_isDecidable_isPolyTimeCore {A : Set (List Bool)}
    (hdec : IsDecidable A encBits) (hA : A ∉ P encBits) :
    ∃ X ⊆ A, X.Infinite ∧ IsDecidable X encBits ∧ IsPolyTimeCore encBits A X := by
  obtain ⟨d, hs, hc⟩ := (isDecidable_iff_isComputable_indicator.mp hdec).exists_runBool
  exact ⟨RecursiveCore.core d A, RecursiveCore.core_subset d A,
    RecursiveCore.infinite_core hs hc hA, RecursiveCore.isDecidable_core d hdec,
    (RecursiveCore.isComplexityCore_core hs hc).isPolyTimeCore⟩

/-- **A decidable problem is outside `P` exactly when it has an infinite decidable polynomial
complexity core inside it.** -/
theorem notMem_P_iff_exists_infinite_isDecidable_isPolyTimeCore {A : Set (List Bool)}
    (hdec : IsDecidable A encBits) :
    A ∉ P encBits ↔ ∃ X ⊆ A, X.Infinite ∧ IsDecidable X encBits ∧ IsPolyTimeCore encBits A X :=
  ⟨exists_infinite_isDecidable_isPolyTimeCore hdec,
    fun ⟨_, _, hX, _, h⟩ hA => hX (h.finite_of_mem_P hA)⟩

end Cslib.Complexity
