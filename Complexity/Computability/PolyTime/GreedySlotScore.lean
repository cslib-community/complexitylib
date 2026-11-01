/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.GenericRAM.Native.IndexFold
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain
public import Complexity.Foundations.Combinatorics.GreedySchedules
public import Complexity.Foundations.Data.Nat.Radix
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Foundations.Data.List.Lookup
import Complexity.Foundations.Data.List.OfFn
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Greedy slot-score arithmetic and streaming candidate selection

In §4.4, Lemma 4.5 of [OpenAI2026ETH] (printed pp. 30–32), schedules `a_v, d_f ∈ [r]^Q` are chosen
one slot at a time over `K = r ^ Q` candidates per slot. Executing `bestVariableLabel` and
`bestFactorLabel` on a native machine clears denominators to bounded integers and streams
`0 .. r ^ Q - 1` in polynomial workspace.

Encoded `ComputableInPolyTime`, `NativeCertificate`, `ComputableInO`, and `ComputableInPolySpace`
results in `Cslib.BalancedSchedules` govern the concrete list/integer algorithms (`decodeLabelWord`,
`clearedJointScore`, `updateSlotSchedules`, `readSlotSchedule`, `streamBestSlotLabel`,
`streamBestSlotCertificate`), while `labelWordEquiv`, `wordToSchedule`, `scheduleToWord`,
`candidateScheduleList`, `edgesOfFin`, `partialScheduleListOfFin`, and `candidateSlotScore` are
unencoded typed specification bridges. Total fallback conventions: `wordToSchedule` clamps digits
`≥ r` and missing positions to `0`; `streamBestSlotLabel` returns `List.replicate Q 0` when
`r ^ Q = 0`; `clearedPartialCollision`, `updateSlotSchedules`, and `readSlotSchedule` use total
`List.getD` / `List.set` defaults on out-of-bounds indices; and `scoreDenom` replaces zero
normalizers `numEdges * C` or `Q * n` by `1`.

## Main definitions

* `decodeLabelWord`, `labelWordEquiv`, `wordToSchedule`, `scheduleToWord`, `candidateScheduleList`:
  radix-`r` candidate codec and `Fin Q → Fin r` schedule bridges.
* `clearedPartialCollision`, `clearedIncidenceCollisions`, `clearedIncidencePotential`,
  `clearedGroupCollisions`, `clearedGroupPotential`, `scoreDenom`, `clearedJointScore`:
  cleared-integer collision and joint score arithmetic.
* `edgesOfFin`, `partialScheduleListOfFin`, `encPartialSchedules`, `encScoreParams`,
  `encSlotSelectAcc`, `StreamSlotIn`, `encStreamSlotIn`: list bridges and machine encodings.
* `updateSlotSchedules`, `readSlotSchedule`, `SlotSelectAcc`, `selectSlotStep`,
  `streamBestSlotLabel`, `candidateSlotScore`, `streamBestSlotCertificate`: streaming `IndexFold`
  single-slot selector and its uniform `NativeCertificate`.

## Main results

* `decodeLabelWord_ofDigits`, `ofDigits_decodeLabelWord`,
  `wordToSchedule_decodeLabelWord_eq_finFunctionFinEquiv_symm`,
  `computableInPolyTime_decodeLabelWord`: radix bijection and poly-time decoding.
* `clearedJointScore_le`, `length_encNat_clearedJointScore_le`,
  `normalizedPartialScore_eq_clearedJointScore_div`,
  `clearedJointScore_lt_iff_normalizedPartialScore_lt`,
  `clearedJointScore_le_iff_normalizedPartialScore_le`, `computableInPolyTime_clearedJointScore`:
  logarithmic bit bound, exact rational score equivalence, and poly-time score evaluation.
* `clearedIncidencePotential_eq_mul`: the incidence part alone, used by the packing of
  `Cslib.PacketPacking`.
* `exists_min_index_streamBestSlotLabel`, `streamBestSlotLabel_false_eq_bestVariableLabel`,
  `streamBestSlotLabel_true_eq_bestFactorLabel`: first-minimizer and `bestVariableLabel` /
  `bestFactorLabel` bridges.
* `length_encSlotSelectState_run_le`, `streamBestSlotCertificate_bounds`,
  `computableInO_streamBestSlotLabel`, `computableInPolySpace_streamBestSlotLabel`: all-prefix
  live-state bit bound, `O((r ^ Q + 1) * poly(|input|))` native time, and polynomial workspace.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §4.4, Lemma 4.5, pp. 30–32.
-/

@[expose] public section

namespace Cslib.BalancedSchedules

open Finset Cslib.GenericRAM Turing.MultiTapeTM
open ComputableTidilyInO (length_encNat_mono)
open scoped BigOperators

/-! ### Section 1: Radix-`r` candidate word decoder and bijections -/

/-- Binary bit-length bound for `r ^ Q`: at most `Q * |encNat r| + 1`. -/
theorem length_encNat_pow_le (r Q : ℕ) :
    (encNat (r ^ Q)).length ≤ Q * (encNat r).length + 1 := by
  simp only [encNat_apply, Nat.size_eq_bits_len]; exact Nat.size_pow_le r Q

/-- Decode binary candidate index `j` into the length-`Q` radix-`r` word of digits via
`Cslib.Radix.digit` ([OpenAI2026ETH], Lemma 4.5, p. 31). -/
def decodeLabelWord (r Q j : ℕ) : List ℕ :=
  (List.range Q).map fun t => Cslib.Radix.digit r j t

@[simp] theorem decodeLabelWord_zero_right (r j : ℕ) : decodeLabelWord r 0 j = [] := rfl

@[simp] theorem decodeLabelWord_one_left (Q j : ℕ) :
    decodeLabelWord 1 Q j = List.replicate Q 0 := by
  apply List.ext_getElem
    (by simp only [decodeLabelWord, List.length_map, List.length_range, List.length_replicate])
  intro t _ _
  simp only [decodeLabelWord, List.getElem_map, List.getElem_replicate,
    Cslib.Radix.digit_eq_div_pow_mod, Nat.mod_one]

@[simp] theorem length_decodeLabelWord (r Q j : ℕ) : (decodeLabelWord r Q j).length = Q := by
  simp only [decodeLabelWord, List.length_map, List.length_range]

theorem getElem_decodeLabelWord (r Q j t : ℕ) (ht : t < Q) :
    (decodeLabelWord r Q j)[t]'(by simp only [length_decodeLabelWord]; exact ht) =
      Cslib.Radix.digit r j t := by
  simp only [decodeLabelWord, List.getElem_map, List.getElem_range]

/-- Every digit of `decodeLabelWord r Q j` is strictly less than `r` whenever `1 ≤ r`. -/
theorem mem_decodeLabelWord_lt {r Q j x : ℕ} (hr : 1 ≤ r) (hx : x ∈ decodeLabelWord r Q j) :
    x < r := by
  simp only [decodeLabelWord, List.mem_map, List.mem_range] at hx
  obtain ⟨t, _, rfl⟩ := hx; rw [Cslib.Radix.digit_eq_div_pow_mod]; exact Nat.mod_lt _ hr

/-- For any `j < r ^ Q` (even when `r = 0, Q = 0`), every digit of `decodeLabelWord r Q j` is
`< max r 1`. -/
theorem mem_decodeLabelWord_lt_max {r Q j x : ℕ} (hj : j < r ^ Q)
    (hx : x ∈ decodeLabelWord r Q j) : x < max r 1 := by
  rcases Nat.eq_zero_or_pos Q with rfl | hQ
  · simp only [decodeLabelWord_zero_right, List.not_mem_nil] at hx
  · rcases Nat.eq_zero_or_pos r with rfl | hr
    · rw [Nat.zero_pow hQ] at hj; omega
    · exact (mem_decodeLabelWord_lt hr hx).trans_le (le_max_left _ _)

/-- Decoding `Nat.ofDigits r w` for any bounded word `w` recovers `w`. -/
theorem decodeLabelWord_ofDigits {r : ℕ} (hr : 1 ≤ r) {w : List ℕ} (hw : ∀ x ∈ w, x < r) :
    decodeLabelWord r w.length (Nat.ofDigits r w) = w := by
  apply List.ext_getElem (length_decodeLabelWord _ _ _)
  intro t _ ht; rw [getElem_decodeLabelWord _ _ _ _ ht]
  exact Cslib.Radix.digit_ofDigits hr w hw t ht

/-- `Nat.ofDigits r` on `decodeLabelWord r Q j` recovers `j` for all `j < r ^ Q` (including `Q = 0`
and `r = 1`). -/
theorem ofDigits_decodeLabelWord {r Q j : ℕ} (hj : j < r ^ Q) :
    Nat.ofDigits r (decodeLabelWord r Q j) = j := by
  rcases Nat.eq_zero_or_pos Q with rfl | hQ
  · simp only [pow_zero, Nat.lt_one_iff] at hj; subst hj; rfl
  · obtain ⟨x, hx, rfl⟩ := Nat.exists_ofDigits_ofFn hj
    have hr : 0 < r := Nat.zero_lt_of_lt (hx ⟨0, hQ⟩)
    congr 1; apply List.ext_getElem (by simp only [length_decodeLabelWord, List.length_ofFn])
    intro t _ ht; have htQ : t < Q := by simpa only [List.length_ofFn] using ht
    rw [getElem_decodeLabelWord _ _ _ _ htQ, Cslib.Radix.digit_ofDigits hr (List.ofFn x)
      (fun a ha => by obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha; exact hx i) t ht]

/-- Exact bijection between binary indices `Fin (r ^ Q)` and length-`Q` words over `{0, …, r - 1}`
(including `Q = 0` and `r = 1`). -/
def labelWordEquiv {r : ℕ} (hr : 1 ≤ r) (Q : ℕ) :
    Fin (r ^ Q) ≃ {w : List ℕ // w.length = Q ∧ ∀ x ∈ w, x < r} where
  toFun j := ⟨decodeLabelWord r Q j.val, length_decodeLabelWord r Q j.val,
    fun _ hx => mem_decodeLabelWord_lt hr hx⟩
  invFun w := ⟨Nat.ofDigits r w.1,
    by simpa only [w.2.1] using Nat.ofDigits_lt_base_pow_length_of_pos hr w.1 w.2.2⟩
  left_inv j := Fin.ext (ofDigits_decodeLabelWord j.isLt)
  right_inv w := Subtype.ext (by
    have h := decodeLabelWord_ofDigits hr w.2.2
    rwa [w.2.1] at h)

/-- Convert a concrete digit list `w : List ℕ` into a typed schedule `Fin Q → Fin r`, clamping
out-of-range digits to `0`. -/
def wordToSchedule {r : ℕ} (hr : 1 ≤ r) (Q : ℕ) (w : List ℕ) (t : Fin Q) : Fin r :=
  if h : w.getD t.val 0 < r then ⟨w.getD t.val 0, h⟩ else ⟨0, hr⟩

/-- Convert a typed schedule `a : Fin Q → Fin r` into its length-`Q` digit list. -/
def scheduleToWord {r Q : ℕ} (a : Fin Q → Fin r) : List ℕ := List.ofFn fun t => (a t).val

@[simp] theorem length_scheduleToWord {r Q : ℕ} (a : Fin Q → Fin r) :
    (scheduleToWord a).length = Q := List.length_ofFn

theorem mem_scheduleToWord_lt {r Q : ℕ} (a : Fin Q → Fin r) {x : ℕ} (hx : x ∈ scheduleToWord a) :
    x < r := by obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hx; exact (a t).isLt

@[simp] theorem wordToSchedule_scheduleToWord {r : ℕ} (hr : 1 ≤ r) {Q : ℕ}
    (a : Fin Q → Fin r) : wordToSchedule hr Q (scheduleToWord a) = a := by
  funext t; simp only [wordToSchedule, scheduleToWord, List.getD_ofFn, (a t).isLt, ↓reduceDIte,
    Fin.eta]

theorem scheduleToWord_inj {r : ℕ} (hr : 1 ≤ r) {Q : ℕ} {a b : Fin Q → Fin r}
    (h : scheduleToWord a = scheduleToWord b) : a = b := by
  rw [← wordToSchedule_scheduleToWord hr a, ← wordToSchedule_scheduleToWord hr b, h]

theorem scheduleToWord_wordToSchedule {r : ℕ} (hr : 1 ≤ r) {Q : ℕ} {w : List ℕ}
    (hlen : w.length = Q) (hw : ∀ x ∈ w, x < r) :
    scheduleToWord (wordToSchedule hr Q w) = w := by
  apply List.ext_getElem (by simp only [length_scheduleToWord, hlen])
  intro t _ ht; have hlt : w[t] < r := hw w[t] (List.getElem_mem ht)
  simp only [scheduleToWord, List.getElem_ofFn, wordToSchedule, List.getD_eq_getElem w 0 ht, hlt,
    ↓reduceDIte]

/-- `wordToSchedule` composed with `decodeLabelWord` agrees identically with the standard
bijection `finFunctionFinEquiv.symm : Fin (r ^ Q) ≃ (Fin Q → Fin r)`. -/
theorem wordToSchedule_decodeLabelWord_eq_finFunctionFinEquiv_symm {r : ℕ} (hr : 1 ≤ r) (Q : ℕ)
    (j : Fin (r ^ Q)) :
    wordToSchedule hr Q (decodeLabelWord r Q j.val) = finFunctionFinEquiv.symm j := by
  funext t; apply Fin.ext
  have hget : (decodeLabelWord r Q j.val).getD t.val 0 = j.val / r ^ t.val % r := by
    rw [decodeLabelWord, List.getD_map_range _ 0 t.isLt, Cslib.Radix.digit_eq_div_pow_mod]
  simp only [wordToSchedule, hget, Nat.mod_lt _ hr, ↓reduceDIte, finFunctionFinEquiv_symm_apply_val]

/-- Exhaustive list of candidate schedules `Fin Q → Fin r` in `0 .. r ^ Q - 1` radix order. -/
def candidateScheduleList {r : ℕ} (hr : 1 ≤ r) (Q : ℕ) : List (Fin Q → Fin r) :=
  (List.range (r ^ Q)).map fun j => wordToSchedule hr Q (decodeLabelWord r Q j)

theorem mem_candidateScheduleList {r : ℕ} (hr : 1 ≤ r) (Q : ℕ) (a : Fin Q → Fin r) :
    a ∈ candidateScheduleList hr Q := by
  let j := finFunctionFinEquiv a; refine List.mem_map.mpr ⟨j.val, List.mem_range.mpr j.isLt, ?_⟩
  rw [wordToSchedule_decodeLabelWord_eq_finFunctionFinEquiv_symm hr Q j]
  exact Equiv.symm_apply_apply _ _

/-- Encoded bit-length bound for any word of length `Q` with digits `< max r 1`. -/
theorem length_encList_word_le {Q r : ℕ} {w : List ℕ} (hlen : w.length = Q)
    (hw : ∀ x ∈ w, x < max r 1) :
    (encList encNat w).length ≤ Q * (2 * (encNat r).length + 1) := by
  rw [length_encList]
  have hdom : (w.map fun a => 2 * (encNat a).length + 1).sum ≤
      (w.map fun _ => 2 * (encNat r).length + 1).sum := List.sum_le_sum fun x hx => by
    have hlt := hw x hx
    have hsz := length_encNat_mono (by omega : x ≤ r); omega
  simpa only [List.map_const', hlen, List.sum_replicate, smul_eq_mul] using hdom

/-- `decodeLabelWord r Q j` is computable in polynomial time from binary `r`, unary `Q`, and
binary `j`. -/
@[fun_prop] theorem computableInPolyTime_decodeLabelWord :
    ComputableInPolyTime (fun (((r, Q), j) : (ℕ × ℕ) × ℕ) => decodeLabelWord r Q j)
      (encPair (encPair encNat encUnary) encNat) (encList encNat) := by
  simp only [decodeLabelWord, Cslib.Radix.digit_eq_div_pow_mod]; fun_prop

@[fun_prop] theorem computableInPolyTime_decodeLabelWord' {α : Type} {input : α ↪ List Bool}
    {r Q j : α → ℕ} (hr : ComputableInPolyTime r input encNat)
    (hQ : ComputableInPolyTime Q input encUnary) (hj : ComputableInPolyTime j input encNat) :
    ComputableInPolyTime (fun a => decodeLabelWord (r a) (Q a) (j a)) input (encList encNat) :=
  computableInPolyTime_decodeLabelWord.comp ((hr.prod hQ).prod hj)

/-! ### Section 2: Cleared-integer collision scores and exact rational bridge -/

/-- Cleared-integer collision count for two indices `i, j` over a label space of size `cardL`:
returns `cardL` when `i = j` or both assigned values agree, `0` when both are assigned and distinct,
and `1` when at least one slot is unassigned (`1 = cardL * (1 / cardL)`). -/
def clearedPartialCollision {α : Type*} [DecidableEq α] (cardL : ℕ)
    (assigned : List (Option α)) (i j : ℕ) : ℕ :=
  if i = j then cardL
  else match assigned.getD i none, assigned.getD j none with
    | some x, some y => if x = y then cardL else 0
    | _, _ => 1

/-- Sum of cleared incidence-pair collisions over `edges : List (ℕ × ℕ)` (`(f, v)` pairs), scaled
by `K ^ 2 = (r ^ Q) ^ 2`. -/
def clearedIncidenceCollisions (K : ℕ) (edges : List (ℕ × ℕ))
    (varSched facSched : List (Option (List ℕ))) : ℕ :=
  (edges.map fun e => (edges.map fun e' =>
    clearedPartialCollision K varSched e.2 e'.2 *
      clearedPartialCollision K facSched e.1 e'.1).sum).sum

/-- Cleared-integer numerator of `partialIncidencePotential` over common denominator `K ^ 2`. -/
def clearedIncidencePotential (K : ℕ) (edges : List (ℕ × ℕ))
    (varSched facSched : List (Option (List ℕ))) : ℕ :=
  clearedIncidenceCollisions K edges varSched facSched - edges.length ^ 2

/-- Sum of cleared variable-coordinate collisions across `t < Q` and `v, v' < n`, scaled by `r`. -/
def clearedGroupCollisions (n Q r : ℕ) (varSched : List (Option (List ℕ))) : ℕ :=
  ((List.range Q).map fun t =>
    let ct := varSched.map (Option.map fun w => w.getD t 0)
    ((List.range n).map fun v =>
      ((List.range n).map fun v' => clearedPartialCollision r ct v v').sum).sum).sum

/-- Cleared-integer numerator of `partialGroupPotential` over common denominator `r`. -/
def clearedGroupPotential (n Q r : ℕ) (varSched : List (Option (List ℕ))) : ℕ :=
  clearedGroupCollisions n Q r varSched - Q * n ^ 2

/-- Common positive integer denominator clearing `normalizedPartialScore` across all candidate
evaluations without rational GCD reductions ([OpenAI2026ETH], Lemma 4.5, p. 31). -/
def scoreDenom (numEdges n Q r C : ℕ) : ℕ :=
  (r ^ Q) ^ 2 * max (numEdges * C) 1 * r * max (Q * n) 1

/-- Exact natural-number numerator of `normalizedPartialScore` over `scoreDenom`. -/
def clearedJointScore (n Q r C : ℕ) (edges : List (ℕ × ℕ))
    (varSched facSched : List (Option (List ℕ))) : ℕ :=
  (if edges.length * C = 0 then 0
   else clearedIncidencePotential (r ^ Q) edges varSched facSched * (r * max (Q * n) 1)) +
  (if Q * n = 0 then 0
   else clearedGroupPotential n Q r varSched * ((r ^ Q) ^ 2 * max (edges.length * C) 1))

theorem scoreDenom_pos (numEdges n Q : ℕ) {r : ℕ} (hr : 1 ≤ r) (C : ℕ) :
    0 < scoreDenom numEdges n Q r C := by
  unfold scoreDenom; have : 0 < (r ^ Q) ^ 2 := Nat.pow_pos (Nat.pow_pos hr)
  have : 0 < max (numEdges * C) 1 := Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  have : 0 < max (Q * n) 1 := Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _); positivity

/-- Concrete incidence list `[(f₀, v₀), …]` extracted from `edge : Fin E → Fin m × Fin n`. -/
def edgesOfFin {E m n : ℕ} (edge : Fin E → Fin m × Fin n) : List (ℕ × ℕ) :=
  List.ofFn fun e => ((edge e).1.val, (edge e).2.val)

@[simp] theorem length_edgesOfFin {E m n : ℕ} (edge : Fin E → Fin m × Fin n) :
    (edgesOfFin edge).length = E := List.length_ofFn

/-- Concrete partial schedule list extracted from `Fin N → Option (Fin Q → Fin r)`. -/
def partialScheduleListOfFin {N Q r : ℕ}
    (assigned : Fin N → Option (Fin Q → Fin r)) : List (Option (List ℕ)) :=
  List.ofFn fun i => (assigned i).map scheduleToWord

@[simp] theorem length_partialScheduleListOfFin {N Q r : ℕ}
    (assigned : Fin N → Option (Fin Q → Fin r)) :
    (partialScheduleListOfFin assigned).length = N := List.length_ofFn

private theorem clearedPartialCollision_le {α : Type*} [DecidableEq α] (cardL : ℕ)
    (assigned : List (Option α)) (i j : ℕ) :
    clearedPartialCollision cardL assigned i j ≤ cardL + 1 := by
  unfold clearedPartialCollision; split_ifs
  · omega
  · rcases assigned.getD i none with _ | x <;> rcases assigned.getD j none with _ | y <;>
      dsimp only <;> (try split_ifs) <;> omega

private theorem clearedIncidenceCollisions_le (K : ℕ) (edges : List (ℕ × ℕ))
    (varSched facSched : List (Option (List ℕ))) :
    clearedIncidenceCollisions K edges varSched facSched ≤ edges.length ^ 2 * (K + 1) ^ 2 := by
  unfold clearedIncidenceCollisions
  refine (List.sum_le_length_nsmul _ (edges.length * (K + 1) ^ 2)
    (List.forall_mem_map.mpr fun e _ => ?_)).trans
    (by simp only [List.length_map, smul_eq_mul, sq, Nat.mul_assoc]; exact le_rfl)
  refine (List.sum_le_length_nsmul _ ((K + 1) ^ 2)
    (List.forall_mem_map.mpr fun e' _ => ?_)).trans
    (by simp only [List.length_map, smul_eq_mul]; exact le_rfl)
  simpa only [sq] using Nat.mul_le_mul (clearedPartialCollision_le K varSched e.2 e'.2)
    (clearedPartialCollision_le K facSched e.1 e'.1)

private theorem clearedGroupCollisions_le (n Q r : ℕ) (varSched : List (Option (List ℕ))) :
    clearedGroupCollisions n Q r varSched ≤ Q * n ^ 2 * (r + 1) := by
  unfold clearedGroupCollisions
  refine (List.sum_le_length_nsmul _ (n ^ 2 * (r + 1))
    (List.forall_mem_map.mpr fun t _ => ?_)).trans
    (by simp only [List.length_map, List.length_range, smul_eq_mul, Nat.mul_assoc]; exact le_rfl)
  refine (List.sum_le_length_nsmul _ (n * (r + 1))
    (List.forall_mem_map.mpr fun v _ => ?_)).trans
    (by simp only [List.length_map, List.length_range, smul_eq_mul, sq, Nat.mul_assoc]; exact
      le_rfl)
  exact (List.sum_le_length_nsmul _ (r + 1) (List.forall_mem_map.mpr fun v' _ =>
    clearedPartialCollision_le r _ v v')).trans
    (by simp only [List.length_map, List.length_range, smul_eq_mul]; exact le_rfl)

/-- Unconditional upper bound on `clearedJointScore`, independent of `(varSched, facSched)`. -/
theorem clearedJointScore_le (n Q r C : ℕ) (edges : List (ℕ × ℕ))
    (varSched facSched : List (Option (List ℕ))) :
    clearedJointScore n Q r C edges varSched facSched ≤
      edges.length ^ 2 * (r ^ Q + 1) ^ 2 * (r * (Q * n + 1)) +
        Q * n ^ 2 * (r + 1) * ((r ^ Q) ^ 2 * (edges.length * C + 1)) := by
  unfold clearedJointScore clearedIncidencePotential clearedGroupPotential
  have hinc := (Nat.sub_le (clearedIncidenceCollisions (r ^ Q) edges varSched facSched)
    (edges.length ^ 2)).trans (clearedIncidenceCollisions_le (r ^ Q) edges varSched facSched)
  have hgrp := (Nat.sub_le (clearedGroupCollisions n Q r varSched) (Q * n ^ 2)).trans
    (clearedGroupCollisions_le n Q r varSched)
  have hm1 : max (Q * n) 1 ≤ Q * n + 1 := max_le (by omega) (by omega)
  have hm2 : max (edges.length * C) 1 ≤ edges.length * C + 1 := max_le (by omega) (by omega)
  refine Nat.add_le_add
    (by split_ifs; exacts [Nat.zero_le _, Nat.mul_le_mul hinc (Nat.mul_le_mul_left r hm1)])
    (by split_ifs; exacts [Nat.zero_le _, Nat.mul_le_mul hgrp (Nat.mul_le_mul_left _ hm2)])

/-- Logarithmic bit-length bound on `encNat (clearedJointScore ...)` matching Lemma 4.5's
`O(log(2D) + log(2M) + log(2n) + log(2Q) + log(2 + b + w))` bit bound (p. 31), independent of
`(varSched, facSched)`. -/
theorem length_encNat_clearedJointScore_le (n Q r C : ℕ) (edges : List (ℕ × ℕ))
    (varSched facSched : List (Option (List ℕ))) :
    (encNat (clearedJointScore n Q r C edges varSched facSched)).length ≤
      2 * Q * (encNat r).length + 2 * (encNat r).length + (encNat C).length +
        2 * (encNat edges.length).length + 2 * (encNat n).length + 2 * (encNat Q).length + 18 := by
  refine (length_encNat_mono
    (clearedJointScore_le n Q r C edges varSched facSched)).trans ?_
  simp only [encNat_apply, Nat.size_eq_bits_len]
  have hs1 (a : ℕ) : (a + 1).size ≤ a.size + 2 :=
    (Nat.size_add_le a 1).trans (by rw [show (1 : ℕ).size = 1 by decide])
  have h2Q : 2 * Q * r.size = 2 * (Q * r.size) := Nat.mul_assoc 2 Q r.size
  have := Nat.size_pow_le r Q; have := hs1 (r ^ Q)
  have := Nat.size_pow_le (r ^ Q + 1) 2; have := Nat.size_pow_le (r ^ Q) 2
  have := Nat.size_pow_le edges.length 2; have := Nat.size_pow_le n 2
  have := Nat.size_mul_le Q n; have := hs1 (Q * n); have := Nat.size_mul_le r (Q * n + 1)
  have := Nat.size_mul_le edges.length C; have := hs1 (edges.length * C); have := hs1 r
  have := Nat.size_mul_le (edges.length ^ 2) ((r ^ Q + 1) ^ 2)
  have := Nat.size_mul_le (edges.length ^ 2 * (r ^ Q + 1) ^ 2) (r * (Q * n + 1))
  have := Nat.size_mul_le Q (n ^ 2); have := Nat.size_mul_le (Q * n ^ 2) (r + 1)
  have := Nat.size_mul_le ((r ^ Q) ^ 2) (edges.length * C + 1)
  have := Nat.size_mul_le (Q * n ^ 2 * (r + 1)) ((r ^ Q) ^ 2 * (edges.length * C + 1))
  have := Nat.size_add_le_max (edges.length ^ 2 * (r ^ Q + 1) ^ 2 * (r * (Q * n + 1)))
    (Q * n ^ 2 * (r + 1) * ((r ^ Q) ^ 2 * (edges.length * C + 1)))
  omega

/-- Exact rational collision identity on whole-word schedules (`L = Fin Q → Fin r`). -/
theorem clearedPartialCollision_eq_mul_partialCollision {N Q r : ℕ} (hr : 1 ≤ r)
    (assigned : Fin N → Option (Fin Q → Fin r)) (i j : Fin N) :
    (clearedPartialCollision (r ^ Q) (partialScheduleListOfFin assigned) i.val j.val : ℚ) =
      ((r ^ Q : ℕ) : ℚ) * partialCollision assigned i j := by
  have hcard : Fintype.card (Fin Q → Fin r) = r ^ Q := by
    simp only [Fintype.card_fun, Fintype.card_fin]
  have hK0 : ((r ^ Q : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.pow_pos hr).ne'
  have hget (u : Fin N) : (partialScheduleListOfFin assigned).getD u.val none =
      (assigned u).map scheduleToWord := List.getD_ofFn _ u none
  by_cases hij : i = j
  · subst j; simp only [clearedPartialCollision, ↓reduceIte, partialCollision, mul_one]
  · have hij_val : i.val ≠ j.val := fun h => hij (Fin.ext h)
    simp only [clearedPartialCollision, hij_val, ↓reduceIte, hget i, hget j, partialCollision,
      hij, hcard]
    rcases assigned i with _ | x
    · simp only [Option.map_none, Nat.cast_one]; field_simp [hK0]
    · rcases assigned j with _ | y
      · simp only [Option.map_some, Option.map_none, Nat.cast_one]; field_simp [hK0]
      · simp only [Option.map_some]; by_cases hxy : x = y
        · subst y; simp only [↓reduceIte, mul_one]
        · simp only [show scheduleToWord x ≠ scheduleToWord y from fun h =>
            hxy (scheduleToWord_inj hr h), hxy, ↓reduceIte, Nat.cast_zero, mul_zero]

private theorem clearedCoordCollision_eq_mul {n Q r : ℕ} (hr : 1 ≤ r)
    (varLabels : Fin n → Option (Fin Q → Fin r)) (t : Fin Q) (v v' : Fin n) :
    (clearedPartialCollision r
      ((partialScheduleListOfFin varLabels).map (Option.map fun w => w.getD t.val 0))
      v.val v'.val : ℚ) = (r : ℚ) * partialCoordinateCollision varLabels t v v' := by
  let ct := (partialScheduleListOfFin varLabels).map (Option.map fun w => w.getD t.val 0)
  have hct_get (u : Fin n) : ct.getD u.val none = (varLabels u).map fun word => (word t).val := by
    rw [List.getD_eq_getElem _ _
      (by simp only [ct, List.length_map, length_partialScheduleListOfFin]; exact u.isLt)]
    simp only [ct, List.getElem_map, partialScheduleListOfFin, List.getElem_ofFn, Option.map_map]
    rcases varLabels u with _ | word
    · rfl
    · simp only [Option.map_some, Function.comp_apply, scheduleToWord, List.getD_ofFn]
  have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  by_cases hvv : v = v'
  · subst v'
    simp only [clearedPartialCollision, ↓reduceIte, partialCoordinateCollision, partialCollision,
      mul_one]
  · simp only [clearedPartialCollision, show v.val ≠ v'.val from fun h => hvv (Fin.ext h),
      ↓reduceIte, show ((partialScheduleListOfFin varLabels).map
        (Option.map fun w => w.getD t.val 0)) = ct from rfl, hct_get v, hct_get v',
      partialCoordinateCollision, partialCollision, hvv, Fintype.card_fin]
    rcases varLabels v with _ | x
    · simp only [Option.map_none, Nat.cast_one]; field_simp [hr0]
    · rcases varLabels v' with _ | y
      · simp only [Option.map_some, Option.map_none, Nat.cast_one]; field_simp [hr0]
      · simp only [Option.map_some, Fin.ext_iff]
        by_cases hxy : (x t).val = (y t).val <;>
          simp only [hxy, ↓reduceIte, mul_one, Nat.cast_zero, mul_zero]

/-- **Exact cleared incidence potential**: `clearedIncidencePotential` is
`partialIncidencePotential` times the common denominator `(r ^ Q) ^ 2`. -/
theorem clearedIncidencePotential_eq_mul {E m n Q r : ℕ} (hr : 1 ≤ r)
    (edge : Fin E → Fin m × Fin n) (varLabels : Fin n → Option (Fin Q → Fin r))
    (factorLabels : Fin m → Option (Fin Q → Fin r)) :
    (clearedIncidencePotential (r ^ Q) (edgesOfFin edge)
      (partialScheduleListOfFin varLabels) (partialScheduleListOfFin factorLabels) : ℚ) =
      (((r ^ Q : ℕ) : ℚ) ^ 2) * partialIncidencePotential edge varLabels factorLabels := by
  let : Nonempty (Fin Q → Fin r) := ⟨fun _ => ⟨0, hr⟩⟩
  have hcol : (clearedIncidenceCollisions (r ^ Q) (edgesOfFin edge)
      (partialScheduleListOfFin varLabels) (partialScheduleListOfFin factorLabels) : ℚ) =
      (((r ^ Q : ℕ) : ℚ) ^ 2) * ∑ e : Fin E, ∑ e' : Fin E,
        partialIncidenceCollision varLabels factorLabels
          (edge e).2 (edge e').2 (edge e).1 (edge e').1 := by
    simp only [clearedIncidenceCollisions, edgesOfFin, List.map_ofFn, Function.comp_def,
      List.sum_ofFn, Nat.cast_sum, Nat.cast_mul, clearedPartialCollision_eq_mul_partialCollision hr,
      partialIncidenceCollision, Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun e' _ => by ring
  have hnonneg : 0 ≤ partialIncidencePotential edge varLabels factorLabels := by
    rw [partialIncidencePotential_eq_expect]
    exact Finset.expect_nonneg fun _ _ => Finset.expect_nonneg fun _ _ => potential_nonneg _
  have hcard : (Fintype.card ((Fin Q → Fin r) × (Fin Q → Fin r)) : ℚ) = ((r ^ Q : ℕ) : ℚ) ^ 2 := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Nat.cast_mul, sq]
  have hK2 : (0 : ℚ) < ((r ^ Q : ℕ) : ℚ) ^ 2 := by
    have : (0 : ℚ) < ((r ^ Q : ℕ) : ℚ) := by exact_mod_cast Nat.pow_pos hr
    positivity
  have hpot_mul : (((r ^ Q : ℕ) : ℚ) ^ 2) * partialIncidencePotential edge varLabels factorLabels =
      (clearedIncidenceCollisions (r ^ Q) (edgesOfFin edge)
        (partialScheduleListOfFin varLabels) (partialScheduleListOfFin factorLabels) : ℚ) -
        (E : ℚ) ^ 2 := by
    rw [partialIncidencePotential, Fintype.card_fin, hcard, mul_sub, ← hcol]; field_simp [hK2.ne']
  have hge : E ^ 2 ≤ clearedIncidenceCollisions (r ^ Q) (edgesOfFin edge)
      (partialScheduleListOfFin varLabels) (partialScheduleListOfFin factorLabels) := by
    have : ((E ^ 2 : ℕ) : ℚ) ≤ (clearedIncidenceCollisions (r ^ Q) (edgesOfFin edge)
        (partialScheduleListOfFin varLabels) (partialScheduleListOfFin factorLabels) : ℚ) := by
      have := mul_nonneg hK2.le hnonneg; simp only [Nat.cast_pow]; linarith
    exact_mod_cast this
  rw [clearedIncidencePotential, length_edgesOfFin, Nat.cast_sub hge, Nat.cast_pow, hpot_mul]

private theorem clearedGroupPotential_eq_mul {n Q r : ℕ} (hr : 1 ≤ r)
    (varLabels : Fin n → Option (Fin Q → Fin r)) :
    (clearedGroupPotential n Q r (partialScheduleListOfFin varLabels) : ℚ) =
      (r : ℚ) * partialGroupPotential varLabels := by
  let : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hcol : (clearedGroupCollisions n Q r (partialScheduleListOfFin varLabels) : ℚ) =
      (r : ℚ) * ∑ t : Fin Q, ∑ v : Fin n, ∑ v' : Fin n,
        partialCoordinateCollision varLabels t v v' := by
    unfold clearedGroupCollisions
    simp only [List.sum_map_range, Nat.cast_sum, clearedCoordCollision_eq_mul hr, Finset.mul_sum]
  have hnonneg : 0 ≤ partialGroupPotential varLabels := by
    rw [partialGroupPotential_eq_expect]
    exact Finset.expect_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => potential_nonneg _
  have hr_pos : (0 : ℚ) < r := by exact_mod_cast hr
  have hpot_mul : (r : ℚ) * partialGroupPotential varLabels =
      (clearedGroupCollisions n Q r (partialScheduleListOfFin varLabels) : ℚ) -
        (Q : ℚ) * (n : ℚ) ^ 2 := by
    rw [partialGroupPotential, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin, mul_sub,
      ← hcol]; field_simp [hr_pos.ne']
  have hge : Q * n ^ 2 ≤ clearedGroupCollisions n Q r (partialScheduleListOfFin varLabels) := by
    have : ((Q * n ^ 2 : ℕ) : ℚ) ≤
        (clearedGroupCollisions n Q r (partialScheduleListOfFin varLabels) : ℚ) := by
      have := mul_nonneg hr_pos.le hnonneg; simp only [Nat.cast_mul, Nat.cast_pow]; linarith
    exact_mod_cast this
  rw [clearedGroupPotential, Nat.cast_sub hge, Nat.cast_mul, Nat.cast_pow, hpot_mul]

/-- **Exact cleared-integer score identity**: for any `1 ≤ r`, `normalizedPartialScore` equals
`clearedJointScore / scoreDenom` identically (including when `E = 0`, `C = 0`, `Q = 0`, or
`n = 0`). -/
theorem normalizedPartialScore_eq_clearedJointScore_div {E m n Q r : ℕ} (hr : 1 ≤ r)
    (edge : Fin E → Fin m × Fin n) (varLabels : Fin n → Option (Fin Q → Fin r))
    (factorLabels : Fin m → Option (Fin Q → Fin r)) (C : ℕ) :
    normalizedPartialScore edge varLabels factorLabels C =
      (clearedJointScore n Q r C (edgesOfFin edge)
        (partialScheduleListOfFin varLabels) (partialScheduleListOfFin factorLabels) : ℚ) /
        (scoreDenom E n Q r C : ℚ) := by
  have hinc := clearedIncidencePotential_eq_mul hr edge varLabels factorLabels
  have hgrp := clearedGroupPotential_eq_mul hr varLabels
  have hK0 : ((r ^ Q : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.pow_pos hr).ne'
  have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  have hm (k : ℕ) : ((max k 1 : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_right k 1)).ne'
  rw [normalizedPartialScore, clearedJointScore, length_edgesOfFin, Fintype.card_fin,
    Fintype.card_fin, Fintype.card_fin, Nat.cast_add, add_div]
  congr 1
  · by_cases hEC : E * C = 0
    · simp only [hEC, ↓reduceIte, (by exact_mod_cast hEC : (E : ℚ) * (C : ℚ) = 0), div_zero,
        Nat.cast_zero, zero_div]
    · have hEC_rat : (E : ℚ) * (C : ℚ) ≠ 0 := by exact_mod_cast hEC
      simp only [hEC, ↓reduceIte, scoreDenom, max_eq_left (Nat.one_le_iff_ne_zero.mpr hEC),
        Nat.cast_mul, Nat.cast_pow, hinc]
      field_simp [hEC_rat, hK0, hr0, hm (Q * n)]
  · by_cases hQn : Q * n = 0
    · simp only [hQn, ↓reduceIte, (by exact_mod_cast hQn : (Q : ℚ) * (n : ℚ) = 0), div_zero,
        Nat.cast_zero, zero_div]
    · have hQn_rat : (Q : ℚ) * (n : ℚ) ≠ 0 := by exact_mod_cast hQn
      simp only [hQn, ↓reduceIte, scoreDenom, max_eq_left (Nat.one_le_iff_ne_zero.mpr hQn),
        Nat.cast_mul, Nat.cast_pow, hgrp]
      field_simp [hQn_rat, hK0, hr0, hm (E * C)]

/-- Strict `<` on `clearedJointScore : ℕ` is equivalent to `<` on `normalizedPartialScore : ℚ`. -/
theorem clearedJointScore_lt_iff_normalizedPartialScore_lt {E m n Q r : ℕ} (hr : 1 ≤ r)
    (edge : Fin E → Fin m × Fin n) (v₁ v₂ : Fin n → Option (Fin Q → Fin r))
    (f₁ f₂ : Fin m → Option (Fin Q → Fin r)) (C : ℕ) :
    clearedJointScore n Q r C (edgesOfFin edge)
        (partialScheduleListOfFin v₁) (partialScheduleListOfFin f₁) <
      clearedJointScore n Q r C (edgesOfFin edge)
        (partialScheduleListOfFin v₂) (partialScheduleListOfFin f₂) ↔
      normalizedPartialScore edge v₁ f₁ C < normalizedPartialScore edge v₂ f₂ C := by
  have hD : (0 : ℚ) < scoreDenom E n Q r C := by exact_mod_cast scoreDenom_pos E n Q hr C
  rw [normalizedPartialScore_eq_clearedJointScore_div hr edge v₁ f₁ C,
    normalizedPartialScore_eq_clearedJointScore_div hr edge v₂ f₂ C,
    div_lt_div_iff_of_pos_right hD, Nat.cast_lt]

/-- Non-strict `≤` on `clearedJointScore : ℕ` is equivalent to `≤` on
`normalizedPartialScore : ℚ`. -/
theorem clearedJointScore_le_iff_normalizedPartialScore_le {E m n Q r : ℕ} (hr : 1 ≤ r)
    (edge : Fin E → Fin m × Fin n) (v₁ v₂ : Fin n → Option (Fin Q → Fin r))
    (f₁ f₂ : Fin m → Option (Fin Q → Fin r)) (C : ℕ) :
    clearedJointScore n Q r C (edgesOfFin edge)
        (partialScheduleListOfFin v₁) (partialScheduleListOfFin f₁) ≤
      clearedJointScore n Q r C (edgesOfFin edge)
        (partialScheduleListOfFin v₂) (partialScheduleListOfFin f₂) ↔
      normalizedPartialScore edge v₁ f₁ C ≤ normalizedPartialScore edge v₂ f₂ C := by
  have hD : (0 : ℚ) < scoreDenom E n Q r C := by exact_mod_cast scoreDenom_pos E n Q hr C
  rw [normalizedPartialScore_eq_clearedJointScore_div hr edge v₁ f₁ C,
    normalizedPartialScore_eq_clearedJointScore_div hr edge v₂ f₂ C,
    div_le_div_iff_of_pos_right hD, Nat.cast_le]

/-! ### Polynomial-time certificate for `clearedJointScore` -/

private theorem ite_decide_polyTime {γ β : Type} {encIn : γ ↪ List Bool} {encB : β ↪ List Bool}
    {P : γ → Prop} [∀ g, Decidable (P g)] {yes no : γ → β}
    (hP : ComputableInPolyTime (fun g => decide (P g)) encIn encBool)
    (hyes : ComputableInPolyTime yes encIn encB)
    (hno : ComputableInPolyTime no encIn encB) :
    ComputableInPolyTime (fun g => if P g then yes g else no g) encIn encB :=
  (hP.ite' hyes hno).of_enc_eq fun _ => by simp only [decide_eq_true_eq]

private theorem binary_sum_polyTime :
    ComputableInPolyTime List.sum (encList encNat) encNat := by fun_prop

private theorem binary_add_polyTime {γ : Type} {encIn : γ ↪ List Bool} {a b : γ → ℕ}
    (ha : ComputableInPolyTime a encIn encNat) (hb : ComputableInPolyTime b encIn encNat) :
    ComputableInPolyTime (fun x => a x + b x) encIn encNat :=
  (show ComputableInPolyTime (fun p : ℕ × ℕ => p.1 + p.2)
    (encPair encNat encNat) encNat by fun_prop).comp (ha.prod hb)

private theorem computableInPolyTime_clearedPartialCollision {α γ : Type} [DecidableEq α]
    {encA : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {cardL i j : γ → ℕ} {assigned : γ → List (Option α)}
    (hc : ComputableInPolyTime cardL encIn encNat)
    (ha : ComputableInPolyTime assigned encIn (encList (encOption encA)))
    (hi : ComputableInPolyTime i encIn encNat)
    (hj : ComputableInPolyTime j encIn encNat) :
    ComputableInPolyTime
      (fun g => clearedPartialCollision (cardL g) (assigned g) (i g) (j g)) encIn encNat := by
  have hgi := ComputableInPolyTime.listGetD_binary (encA := encOption encA) none ha hi
  have hgj := ComputableInPolyTime.listGetD_binary (encA := encOption encA) none ha hj
  have hboth : ComputableInPolyTime
      (fun g => ((assigned g).getD (i g) none).isSome && ((assigned g).getD (j g) none).isSome)
      encIn encBool := by fun_prop
  have hinner := ite_decide_polyTime (ComputableInPolyTime.decide_eq' hgi hgj) hc (.const 0)
  have hmatch := hboth.ite' hinner (.const 1)
  refine (ite_decide_polyTime (ComputableInPolyTime.decide_eq' hi hj) hc hmatch).of_enc_eq
    fun g => congrArg encNat ?_
  dsimp only [clearedPartialCollision]; by_cases hij : i g = j g
  · simp only [hij, ↓reduceIte]
  · simp only [hij, ↓reduceIte]
    rcases (assigned g).getD (i g) none with _ | x <;>
      rcases (assigned g).getD (j g) none with _ | y <;>
      first | rfl | simp only [Option.isSome_some, Bool.and_self, ↓reduceIte, Option.some.injEq]

private theorem computableInPolyTime_binary_max1 {γ : Type} {encIn : γ ↪ List Bool} {x : γ → ℕ}
    (hx : ComputableInPolyTime x encIn encNat) :
    ComputableInPolyTime (fun g => max (x g) 1) encIn encNat := by
  refine (ite_decide_polyTime (ComputableInPolyTime.decide_eq' hx (.const 0))
    (.const 1) hx).of_enc_eq fun g => congrArg encNat ?_
  rcases Nat.eq_zero_or_pos (x g) with h0 | hpos
  · simp only [h0, ↓reduceIte]; omega
  · simp only [hpos.ne', ↓reduceIte]; omega

/-- Encoding of a pair `(varSched, facSched)` of partial schedule tables. -/
def encPartialSchedules : (List (Option (List ℕ)) × List (Option (List ℕ))) ↪ List Bool :=
  encPair (encList (encOption (encList encNat))) (encList (encOption (encList encNat)))

/-- Encoding of score parameters `((n, Q), (r, C), edges)`. -/
def encScoreParams : ((ℕ × ℕ) × (ℕ × ℕ) × List (ℕ × ℕ)) ↪ List Bool :=
  encPair (encPair encUnary encUnary)
    (encPair (encPair encNat encNat) (encList (encPair encNat encNat)))

/-- `clearedJointScore` is computable in polynomial time in its encoded inputs. -/
@[fun_prop] theorem computableInPolyTime_clearedJointScore :
    ComputableInPolyTime
      (fun ((((n, Q), (r, C), edges), (varSched, facSched)) :
          ((ℕ × ℕ) × (ℕ × ℕ) × List (ℕ × ℕ)) ×
            (List (Option (List ℕ)) × List (Option (List ℕ)))) =>
        clearedJointScore n Q r C edges varSched facSched)
      (encPair encScoreParams encPartialSchedules) encNat := by
  unfold encScoreParams encPartialSchedules
  let ePar := encPair (encPair encUnary encUnary)
    (encPair (encPair encNat encNat) (encList (encPair encNat encNat)))
  let eIn := encPair ePar
    (encPair (encList (encOption (encList encNat))) (encList (encOption (encList encNat))))
  have hK : ComputableInPolyTime (fun p : _ × _ => p.1.2.1.1 ^ p.1.1.2) eIn encNat :=
    ComputableInPolyTime.binary_pow' (by fun_prop) (by fun_prop)
  have hincCol : ComputableInPolyTime (fun p : _ × _ =>
      clearedIncidenceCollisions (p.1.2.1.1 ^ p.1.1.2) p.1.2.2 p.2.1 p.2.2) eIn encNat := by
    unfold clearedIncidenceCollisions
    refine binary_sum_polyTime.comp (ComputableInPolyTime.mapWithInput
      (by fun_prop) (binary_sum_polyTime.comp
        (ComputableInPolyTime.mapWithInput (by fun_prop) ?_)))
    exact ComputableInPolyTime.binary_mul'
      (computableInPolyTime_clearedPartialCollision
        (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop))
      (computableInPolyTime_clearedPartialCollision
        (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop))
  have hgrpCol : ComputableInPolyTime (fun p : _ × _ =>
      clearedGroupCollisions p.1.1.1 p.1.1.2 p.1.2.1.1 p.2.1) eIn encNat := by
    unfold clearedGroupCollisions
    refine binary_sum_polyTime.comp
      (ComputableInPolyTime.mapWithInput (by fun_prop) ?_)
    have hct : ComputableInPolyTime (fun q : _ × ℕ =>
        q.1.2.1.map (Option.map fun w => w.getD q.2 0))
        (encPair eIn encUnary) (encList (encOption encNat)) := by
      refine (show ComputableInPolyTime
          (fun q : _ × ℕ => q.1.2.1.map fun o => o.elim none fun w => some (w.getD q.2 0))
          (encPair eIn encUnary) (encList (encOption encNat)) by fun_prop).of_enc_eq fun q => ?_
      congr 1; apply List.map_congr_left; intro o _; cases o <;> rfl
    refine binary_sum_polyTime.comp (ComputableInPolyTime.mapWithInput
      (by fun_prop) (binary_sum_polyTime.comp
        (ComputableInPolyTime.mapWithInput (by fun_prop) ?_)))
    exact computableInPolyTime_clearedPartialCollision (by fun_prop) (hct.comp (by fun_prop))
      (ComputableInPolyTime.unary_to_binary.comp (by fun_prop))
      (ComputableInPolyTime.unary_to_binary.comp (by fun_prop))
  have heLen := ComputableInPolyTime.unary_to_binary.comp
    (show ComputableInPolyTime (fun p : _ × _ => p.1.2.2.length) eIn encUnary by fun_prop)
  have hnBin := ComputableInPolyTime.unary_to_binary.comp
    (show ComputableInPolyTime (fun p : _ × _ => p.1.1.1) eIn encUnary by fun_prop)
  have hQBin := ComputableInPolyTime.unary_to_binary.comp
    (show ComputableInPolyTime (fun p : _ × _ => p.1.1.2) eIn encUnary by fun_prop)
  have hC : ComputableInPolyTime (fun p : _ × _ => p.1.2.1.2) eIn encNat := by fun_prop
  have hrBin : ComputableInPolyTime (fun p : _ × _ => p.1.2.1.1) eIn encNat := by fun_prop
  have hK2 := ComputableInPolyTime.binary_pow' hK (.const 2)
  have he2 := ComputableInPolyTime.binary_pow' heLen (.const 2)
  have hn2 := ComputableInPolyTime.binary_pow' hnBin (.const 2)
  have hqn := ComputableInPolyTime.binary_mul' hQBin hnBin
  have hec := ComputableInPolyTime.binary_mul' heLen hC
  have hincPot := ComputableInPolyTime.binary_sub' hincCol he2
  have hgrpPot := ComputableInPolyTime.binary_sub' hgrpCol
    (ComputableInPolyTime.binary_mul' hQBin hn2)
  unfold clearedJointScore clearedIncidencePotential clearedGroupPotential
  exact binary_add_polyTime
    (ite_decide_polyTime (ComputableInPolyTime.decide_eq' hec (.const 0))
      (.const 0) (ComputableInPolyTime.binary_mul' hincPot
        (ComputableInPolyTime.binary_mul' hrBin (computableInPolyTime_binary_max1 hqn))))
    (ite_decide_polyTime (ComputableInPolyTime.decide_eq' hqn (.const 0))
      (.const 0) (ComputableInPolyTime.binary_mul' hgrpPot
        (ComputableInPolyTime.binary_mul' hK2 (computableInPolyTime_binary_max1 hec))))

/-! ### Section 3: Streaming `IndexFold` slot selector and rational minimizer bridges -/

/-- Update a variable (`(false, v)`) or factor (`(true, f)`) slot in `(varSched, facSched)`. -/
def updateSlotSchedules (slot : Bool × ℕ) (val : Option (List ℕ))
    (scheds : List (Option (List ℕ)) × List (Option (List ℕ))) :
    List (Option (List ℕ)) × List (Option (List ℕ)) :=
  if slot.1 then (scheds.1, scheds.2.set slot.2 val) else (scheds.1.set slot.2 val, scheds.2)

/-- Read a variable (`(false, v)`) or factor (`(true, f)`) slot from `(varSched, facSched)`. -/
def readSlotSchedule (slot : Bool × ℕ)
    (scheds : List (Option (List ℕ)) × List (Option (List ℕ))) : Option (List ℕ) :=
  if slot.1 then scheds.2.getD slot.2 none else scheds.1.getD slot.2 none

/-- Live accumulator for inner `IndexFold.run` candidate streaming over `j ∈ 0 .. r ^ Q - 1`. -/
abbrev SlotSelectAcc : Type :=
  ((ℕ × ℕ) × (ℕ × ℕ) × List (ℕ × ℕ)) ×
    ((Bool × ℕ) × ((List (Option (List ℕ)) × List (Option (List ℕ))) × Option (List ℕ × ℕ)))

/-- Inner `IndexFold.run` callback evaluating candidate `decodeLabelWord r Q j` under
`clearedJointScore` and retaining the first strict minimizer (`candScore < best.2`). -/
def selectSlotStep (state : ℕ × SlotSelectAcc) : SlotSelectAcc :=
  let (j, (sparams, (slot, (scheds, bestOpt)))) := state
  let ((n, Q), (r, C), edges) := sparams
  let candWord := decodeLabelWord r Q j
  let candScheds := updateSlotSchedules slot (some candWord) scheds
  let candScore := clearedJointScore n Q r C edges candScheds.1 candScheds.2
  let nextBest := bestOpt.elim (some (candWord, candScore)) fun best =>
    if decide (candScore < best.2) then some (candWord, candScore) else some best
  (sparams, (slot, (scheds, nextBest)))

/-- Stream `j ∈ 0 .. r ^ Q - 1` via `Cslib.GenericRAM.IndexFold.run` to select the first candidate
word minimizing `clearedJointScore` for `slot`, falling back to `List.replicate Q 0` if `r ^ Q = 0`
([OpenAI2026ETH], Lemma 4.5, p. 31). -/
def streamBestSlotLabel (n Q r C : ℕ) (edges : List (ℕ × ℕ))
    (scheds : List (Option (List ℕ)) × List (Option (List ℕ))) (slot : Bool × ℕ) : List ℕ :=
  let init : SlotSelectAcc := (((n, Q), (r, C), edges), (slot, (scheds, none)))
  let (_, (_, (_, (_, bestOpt)))) := IndexFold.run selectSlotStep (r ^ Q) init
  bestOpt.elim (List.replicate Q 0) Prod.fst

private theorem run_selectSlotStep_params (sparams : (ℕ × ℕ) × (ℕ × ℕ) × List (ℕ × ℕ))
    (slot : Bool × ℕ) (scheds : List (Option (List ℕ)) × List (Option (List ℕ))) (k : ℕ) :
    let r := IndexFold.run selectSlotStep k (sparams, (slot, (scheds, none)))
    r.2.1 = sparams ∧ r.2.2.1 = slot ∧ r.2.2.2.1 = scheds := by
  induction k with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ k ih =>
    rw [IndexFold.run_succ]; simp only [IndexFold.step, selectSlotStep, ih.1, ih.2.1, ih.2.2,
      and_self]

/-- Cleared-integer score of candidate `decodeLabelWord r Q j` placed in `slot`. -/
def candidateSlotScore (n Q r C : ℕ) (edges : List (ℕ × ℕ))
    (scheds : List (Option (List ℕ)) × List (Option (List ℕ))) (slot : Bool × ℕ) (j : ℕ) : ℕ :=
  let candScheds := updateSlotSchedules slot (some (decodeLabelWord r Q j)) scheds
  clearedJointScore n Q r C edges candScheds.1 candScheds.2

private theorem run_selectSlotStep_spec (n Q r C : ℕ) (edges : List (ℕ × ℕ))
    (scheds : List (Option (List ℕ)) × List (Option (List ℕ))) (slot : Bool × ℕ) :
    ∀ {k : ℕ}, 0 < k →
      ∃ jStar < k,
        (IndexFold.run selectSlotStep k
          (((n, Q), (r, C), edges), (slot, (scheds, none)))).2.2.2.2 =
          some (decodeLabelWord r Q jStar, candidateSlotScore n Q r C edges scheds slot jStar) ∧
        (∀ j < k, candidateSlotScore n Q r C edges scheds slot jStar ≤
          candidateSlotScore n Q r C edges scheds slot j) ∧
        (∀ j < jStar, candidateSlotScore n Q r C edges scheds slot jStar <
          candidateSlotScore n Q r C edges scheds slot j) ∧
        (∀ {α : Type} (g : ℕ → α) (f : α → ℚ),
          (∀ i < k, ∀ j < k,
            candidateSlotScore n Q r C edges scheds slot i <
              candidateSlotScore n Q r C edges scheds slot j ↔ f (g i) < f (g j)) →
          ((List.range k).map g).argmin f = some (g jStar)) := by
  intro k hk; let init : SlotSelectAcc := (((n, Q), (r, C), edges), (slot, (scheds, none)))
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · refine ⟨0, Nat.zero_lt_one, by rw [IndexFold.run_succ, IndexFold.run_zero]; rfl,
        fun j hj => by rw [show j = 0 by omega], fun _ hj => by omega, fun _ _ _ => rfl⟩
    · obtain ⟨jStar, hjStar_lt, hopt, hle, hlt, harg⟩ := ih hkpos
      have hp := run_selectSlotStep_params ((n, Q), (r, C), edges) slot scheds k
      have hidx := IndexFold.run_index selectSlotStep k init
      let scK := candidateSlotScore n Q r C edges scheds slot k
      let scBest := candidateSlotScore n Q r C edges scheds slot jStar
      by_cases hcmp : scK < scBest
      · refine ⟨k, Nat.lt_succ_self k, ?_, ?_, fun j hj => lt_of_lt_of_le hcmp (hle j hj), ?_⟩
        · rw [IndexFold.run_succ]
          simp only [IndexFold.step, selectSlotStep, init, hidx, hp.1, hp.2.1, hp.2.2, hopt,
            Option.elim_some]
          split_ifs with h
          · rfl
          · exact absurd (decide_eq_true hcmp) h
        · intro j hj; rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
          · exact hcmp.le.trans (hle j hj')
          · exact le_rfl
        · intro α g f hiff
          rw [List.range_succ, List.map_append, List.map_singleton, List.argmin_concat,
            harg g f (fun i hi j hj => hiff i (Nat.lt_succ_of_lt hi) j (Nat.lt_succ_of_lt hj))]
          have hf_lt := (hiff k (Nat.lt_succ_self k) jStar (Nat.lt_succ_of_lt hjStar_lt)).mp hcmp
          simp only [hf_lt, ↓reduceIte]
      · refine ⟨jStar, Nat.lt_succ_of_lt hjStar_lt, ?_, ?_, hlt, ?_⟩
        · rw [IndexFold.run_succ]
          simp only [IndexFold.step, selectSlotStep, init, hidx, hp.1, hp.2.1, hp.2.2, hopt,
            Option.elim_some]
          split_ifs with h
          · exact absurd (of_decide_eq_true h) hcmp
          · rfl
        · intro j hj; rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
          · exact hle j hj'
          · exact Nat.le_of_not_lt hcmp
        · intro α g f hiff
          rw [List.range_succ, List.map_append, List.map_singleton, List.argmin_concat,
            harg g f (fun i hi j hj => hiff i (Nat.lt_succ_of_lt hi) j (Nat.lt_succ_of_lt hj))]
          have hf_nlt : ¬ f (g k) < f (g jStar) := fun h =>
            hcmp ((hiff k (Nat.lt_succ_self k) jStar (Nat.lt_succ_of_lt hjStar_lt)).mpr h)
          simp only [hf_nlt, ↓reduceIte]

/-- First-minimizer characterization of `streamBestSlotLabel` when `0 < r ^ Q`. -/
theorem exists_min_index_streamBestSlotLabel (n Q r C : ℕ) (edges : List (ℕ × ℕ))
    (scheds : List (Option (List ℕ)) × List (Option (List ℕ))) (slot : Bool × ℕ)
    (hpos : 0 < r ^ Q) :
    ∃ jStar < r ^ Q, streamBestSlotLabel n Q r C edges scheds slot = decodeLabelWord r Q jStar ∧
      (∀ j < r ^ Q, candidateSlotScore n Q r C edges scheds slot jStar ≤
        candidateSlotScore n Q r C edges scheds slot j) ∧
      (∀ j < jStar, candidateSlotScore n Q r C edges scheds slot jStar <
        candidateSlotScore n Q r C edges scheds slot j) := by
  obtain ⟨jStar, hj, hopt, hle, hlt, _⟩ := run_selectSlotStep_spec n Q r C edges scheds slot hpos
  exact ⟨jStar, hj, by simp only [streamBestSlotLabel, hopt, Option.elim_some], hle, hlt⟩

@[simp] theorem length_streamBestSlotLabel (n Q r C : ℕ) (edges : List (ℕ × ℕ))
    (scheds : List (Option (List ℕ)) × List (Option (List ℕ))) (slot : Bool × ℕ) :
    (streamBestSlotLabel n Q r C edges scheds slot).length = Q := by
  rcases Nat.eq_zero_or_pos (r ^ Q) with h0 | hpos
  · simp only [streamBestSlotLabel, h0, IndexFold.run_zero, Option.elim_none, List.length_replicate]
  · obtain ⟨_, _, hw, _, _⟩ := exists_min_index_streamBestSlotLabel n Q r C edges scheds slot hpos
    rw [hw, length_decodeLabelWord]

theorem mem_streamBestSlotLabel_lt_max (n Q r C : ℕ) (edges : List (ℕ × ℕ))
    (scheds : List (Option (List ℕ)) × List (Option (List ℕ))) (slot : Bool × ℕ)
    {x : ℕ} (hx : x ∈ streamBestSlotLabel n Q r C edges scheds slot) : x < max r 1 := by
  rcases Nat.eq_zero_or_pos (r ^ Q) with h0 | hpos
  · simp only [streamBestSlotLabel, h0, IndexFold.run_zero, Option.elim_none,
      List.mem_replicate] at hx
    rcases hx with ⟨_, rfl⟩; omega
  · obtain ⟨_, hj, hw, _, _⟩ := exists_min_index_streamBestSlotLabel n Q r C edges scheds slot hpos
    rw [hw] at hx; exact mem_decodeLabelWord_lt_max hj hx

theorem mem_streamBestSlotLabel_lt {r : ℕ} (hr : 1 ≤ r) (n Q C : ℕ) (edges : List (ℕ × ℕ))
    (scheds : List (Option (List ℕ)) × List (Option (List ℕ))) (slot : Bool × ℕ)
    {x : ℕ} (hx : x ∈ streamBestSlotLabel n Q r C edges scheds slot) : x < r := by
  simpa only [max_eq_left hr] using mem_streamBestSlotLabel_lt_max n Q r C edges scheds slot hx

/-- Updating `partialScheduleListOfFin` at index `k.val` with a valid length-`Q` word `w` commutes
with `Function.update` via `wordToSchedule`. -/
theorem set_partialScheduleListOfFin {N Q r : ℕ} {hr : 1 ≤ r}
    (assigned : Fin N → Option (Fin Q → Fin r)) (k : Fin N) (w : List ℕ)
    (hlen : w.length = Q) (hw : ∀ x ∈ w, x < r) :
    (partialScheduleListOfFin assigned).set k.val (some w) =
      partialScheduleListOfFin (Function.update assigned k (some (wordToSchedule hr Q w))) := by
  apply List.ext_getElem (by simp only [List.length_set, length_partialScheduleListOfFin])
  intro i hi _
  have hiN : i < N := by simpa only [List.length_set, length_partialScheduleListOfFin] using hi
  rw [List.getElem_set]; simp only [partialScheduleListOfFin, List.getElem_ofFn]
  by_cases hki : k.val = i
  · have hfin : (⟨i, hiN⟩ : Fin N) = k := Fin.ext hki.symm
    simp only [hki, ↓reduceIte, hfin, Function.update_self, Option.map_some,
      scheduleToWord_wordToSchedule hr hlen hw]
  · have hfin : (⟨i, hiN⟩ : Fin N) ≠ k := fun h => hki (congrArg Fin.val h).symm
    simp only [hki, ↓reduceIte, Function.update_of_ne hfin]

/-- Exact agreement between `streamBestSlotLabel` at variable slot `(false, v.val)` and
`bestVariableLabel` over `candidateScheduleList hr Q`. -/
theorem streamBestSlotLabel_false_eq_bestVariableLabel {E m n Q r : ℕ} (hr : 1 ≤ r)
    (edge : Fin E → Fin m × Fin n) (varLabels : Fin n → Option (Fin Q → Fin r))
    (factorLabels : Fin m → Option (Fin Q → Fin r)) (C : ℕ) (v : Fin n) :
    some (wordToSchedule hr Q (streamBestSlotLabel n Q r C (edgesOfFin edge)
      (partialScheduleListOfFin varLabels, partialScheduleListOfFin factorLabels) (false, v.val))) =
      bestVariableLabel edge varLabels factorLabels C v (candidateScheduleList hr Q) := by
  obtain ⟨jStar, _, hopt, _, _, harg⟩ := run_selectSlotStep_spec n Q r C (edgesOfFin edge)
    (partialScheduleListOfFin varLabels, partialScheduleListOfFin factorLabels)
    (false, v.val) (Nat.pow_pos (n := Q) hr)
  simp only [streamBestSlotLabel, hopt, Option.elim_some, bestVariableLabel, candidateScheduleList]
  refine (harg (fun j => wordToSchedule hr Q (decodeLabelWord r Q j))
    (fun word => normalizedPartialScore edge (Function.update varLabels v (some word))
      factorLabels C) fun i _ j _ => ?_).symm
  have hset (k : ℕ) := set_partialScheduleListOfFin (hr := hr) varLabels v (decodeLabelWord r Q k)
    (length_decodeLabelWord r Q k) (fun _ hx => mem_decodeLabelWord_lt hr hx)
  simp only [candidateSlotScore, updateSlotSchedules, Bool.false_eq_true, ↓reduceIte, hset i,
    hset j]
  exact clearedJointScore_lt_iff_normalizedPartialScore_lt hr edge _ _ _ _ C

/-- Exact agreement between `streamBestSlotLabel` at factor slot `(true, f.val)` and
`bestFactorLabel` over `candidateScheduleList hr Q`. -/
theorem streamBestSlotLabel_true_eq_bestFactorLabel {E m n Q r : ℕ} (hr : 1 ≤ r)
    (edge : Fin E → Fin m × Fin n) (varLabels : Fin n → Option (Fin Q → Fin r))
    (factorLabels : Fin m → Option (Fin Q → Fin r)) (C : ℕ) (f : Fin m) :
    some (wordToSchedule hr Q (streamBestSlotLabel n Q r C (edgesOfFin edge)
      (partialScheduleListOfFin varLabels, partialScheduleListOfFin factorLabels) (true, f.val))) =
      bestFactorLabel edge varLabels factorLabels C f (candidateScheduleList hr Q) := by
  obtain ⟨jStar, _, hopt, _, _, harg⟩ := run_selectSlotStep_spec n Q r C (edgesOfFin edge)
    (partialScheduleListOfFin varLabels, partialScheduleListOfFin factorLabels)
    (true, f.val) (Nat.pow_pos (n := Q) hr)
  simp only [streamBestSlotLabel, hopt, Option.elim_some, bestFactorLabel, candidateScheduleList]
  refine (harg (fun j => wordToSchedule hr Q (decodeLabelWord r Q j))
    (fun word => normalizedPartialScore edge varLabels
      (Function.update factorLabels f (some word)) C) fun i _ j _ => ?_).symm
  have hset (k : ℕ) := set_partialScheduleListOfFin (hr := hr) factorLabels f
    (decodeLabelWord r Q k) (length_decodeLabelWord r Q k)
    (fun _ hx => mem_decodeLabelWord_lt hr hx)
  simp only [candidateSlotScore, updateSlotSchedules, ↓reduceIte, hset i, hset j]
  exact clearedJointScore_lt_iff_normalizedPartialScore_lt hr edge _ _ _ _ C

/-! ### Section 4: All-prefix bit-length bounds, `NativeCertificate`, and `ComputableInPolySpace` -/

/-- Encoding of inner `IndexFold` accumulator `SlotSelectAcc`. -/
def encSlotSelectAcc : SlotSelectAcc ↪ List Bool :=
  encPair encScoreParams
    (encPair (encPair encBool encUnary)
      (encPair encPartialSchedules (encOption (encPair (encList encNat) encNat))))

/-- Runtime input tuple for `streamBestSlotLabel`. -/
abbrev StreamSlotIn : Type :=
  ((ℕ × ℕ) × (ℕ × ℕ) × List (ℕ × ℕ)) ×
    ((Bool × ℕ) × (List (Option (List ℕ)) × List (Option (List ℕ))))

/-- Encoding of runtime inputs to `streamBestSlotLabel`. -/
def encStreamSlotIn : StreamSlotIn ↪ List Bool :=
  encPair encScoreParams (encPair (encPair encBool encUnary) encPartialSchedules)

end Cslib.BalancedSchedules
end

public section
namespace Cslib.BalancedSchedules
open Finset Cslib.GenericRAM Turing.MultiTapeTM
open ComputableTidilyInO (length_encNat_mono)

/-- All-prefix live-state bit-length bound for the inner `IndexFold.run selectSlotStep` loop across
every visited prefix `j ≤ r ^ Q` (never multiplying workspace by `r ^ Q`). -/
theorem length_encSlotSelectState_run_le (n Q r C : ℕ) (edges : List (ℕ × ℕ))
    (scheds : List (Option (List ℕ)) × List (Option (List ℕ))) (slot : Bool × ℕ)
    {j : ℕ} (hj : j ≤ r ^ Q) :
    (encPair encNat encSlotSelectAcc
      (IndexFold.run selectSlotStep j
        (((n, Q), (r, C), edges), (slot, (scheds, none))))).length ≤
      2 * (encStreamSlotIn (((n, Q), (r, C), edges), (slot, scheds))).length +
        8 * Q * (encNat r).length + 4 * Q + 2 * (encNat r).length + (encNat C).length +
        2 * (encNat edges.length).length + 2 * (encNat n).length + 2 * (encNat Q).length + 28 := by
  let init : SlotSelectAcc := (((n, Q), (r, C), edges), (slot, (scheds, none)))
  have hp := run_selectSlotStep_params ((n, Q), (r, C), edges) slot scheds j
  have hj_len : (encNat j).length ≤ Q * (encNat r).length + 1 :=
    (length_encNat_mono hj).trans (length_encNat_pow_le r Q)
  have hbest : (encOption (encPair (encList encNat) encNat)
      (IndexFold.run selectSlotStep j init).2.2.2.2).length ≤
      6 * Q * (encNat r).length + 4 * Q + 2 * (encNat r).length + (encNat C).length +
        2 * (encNat edges.length).length + 2 * (encNat n).length + 2 * (encNat Q).length + 20 := by
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · simp only [IndexFold.run_zero, init, encOption_none, List.length_nil]; omega
    · obtain ⟨jStar, hjStar_lt, hopt, _, _, _⟩ :=
        run_selectSlotStep_spec n Q r C edges scheds slot hjpos
      rw [hopt, encOption_some, List.length_cons, length_encPair]
      dsimp only [candidateSlotScore]
      have hw := length_encList_word_le (length_decodeLabelWord r Q jStar)
        (fun _ hx => mem_decodeLabelWord_lt_max (lt_of_lt_of_le hjStar_lt hj) hx)
      have hsc := length_encNat_clearedJointScore_le n Q r C edges
        (updateSlotSchedules slot (some (decodeLabelWord r Q jStar)) scheds).1
        (updateSlotSchedules slot (some (decodeLabelWord r Q jStar)) scheds).2
      linarith
  rw [IndexFold.length_run]
  rcases hst : (IndexFold.run selectSlotStep j init).2 with ⟨sp, sl, sc, bo⟩
  have hsp : sp = ((n, Q), (r, C), edges) := by simpa only [init, hst] using hp.1
  have hsl : sl = slot := by simpa only [init, hst] using hp.2.1
  have hsc_eq : sc = scheds := by simpa only [init, hst] using hp.2.2
  have hbo : bo = (IndexFold.run selectSlotStep j init).2.2.2.2 := by simp only [hst]
  subst hsp hsl hsc_eq; rw [← hbo] at hbest
  simp only [encSlotSelectAcc, encStreamSlotIn, length_encPair]; linarith

private theorem list_set_eq_range_map {α : Type*} (d : α) (l : List α) (i : ℕ) (val : α) :
    l.set i val =
      (List.range l.length).map fun k => if decide (i = k) then val else l.getD k d := by
  apply List.ext_getElem (by simp only [List.length_set, List.length_map, List.length_range])
  intro k hk _; have hkl : k < l.length := by simpa only [List.length_set] using hk
  rw [List.getElem_set, List.getElem_map, List.getElem_range, List.getD_eq_getElem l d hkl]
  by_cases hik : i = k <;>
    simp only [hik, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte]

/-- `updateSlotSchedules` is computable in polynomial time. -/
@[fun_prop] theorem computableInPolyTime_updateSlotSchedules :
    ComputableInPolyTime
      (fun (((slot, val), scheds) :
          ((Bool × ℕ) × Option (List ℕ)) ×
            (List (Option (List ℕ)) × List (Option (List ℕ)))) =>
        updateSlotSchedules slot val scheds)
      (encPair (encPair (encPair encBool encUnary) (encOption (encList encNat)))
        encPartialSchedules) encPartialSchedules := by
  unfold encPartialSchedules; let eOpt := encOption (encList encNat)
  let eIn := encPair (encPair (encPair encBool encUnary) eOpt)
    (encPair (encList eOpt) (encList eOpt))
  have hset1 : ComputableInPolyTime (fun p : (_ × _) × (_ × _) =>
      (List.range p.2.1.length).map fun k =>
        if decide (p.1.1.2 = k) then p.1.2 else p.2.1.getD k none)
      eIn (encList eOpt) := ComputableInPolyTime.mapWithInput (by fun_prop)
    (ComputableInPolyTime.ite'
      (ComputableInPolyTime.decide_eq' (by fun_prop) (by fun_prop))
      (by fun_prop) (by fun_prop))
  have hset2 : ComputableInPolyTime (fun p : (_ × _) × (_ × _) =>
      (List.range p.2.2.length).map fun k =>
        if decide (p.1.1.2 = k) then p.1.2 else p.2.2.getD k none)
      eIn (encList eOpt) := ComputableInPolyTime.mapWithInput (by fun_prop)
    (ComputableInPolyTime.ite'
      (ComputableInPolyTime.decide_eq' (by fun_prop) (by fun_prop))
      (by fun_prop) (by fun_prop))
  refine (ComputableInPolyTime.ite' (show ComputableInPolyTime
      (fun p : _ => p.1.1.1) eIn encBool by fun_prop)
    ((show ComputableInPolyTime (fun p : _ => p.2.1) eIn (encList eOpt) by
        fun_prop).prod hset2)
    (hset1.prod (show ComputableInPolyTime (fun p : _ => p.2.2) eIn (encList eOpt) by
      fun_prop))).of_enc_eq fun p => ?_
  dsimp only [updateSlotSchedules]
  rw [list_set_eq_range_map none p.2.1 p.1.1.2 p.1.2,
    list_set_eq_range_map none p.2.2 p.1.1.2 p.1.2]

/-- `readSlotSchedule` is computable in polynomial time. -/
@[fun_prop] theorem computableInPolyTime_readSlotSchedule :
    ComputableInPolyTime (fun p : (Bool × ℕ) × (List (Option (List ℕ)) × List (Option (List ℕ))) =>
        readSlotSchedule p.1 p.2)
      (encPair (encPair encBool encUnary) encPartialSchedules) (encOption (encList encNat)) := by
  unfold readSlotSchedule encPartialSchedules; fun_prop

private theorem computableInPolyTime_selectSlotStep :
    ComputableInPolyTime selectSlotStep (encPair encNat encSlotSelectAcc) encSlotSelectAcc := by
  let eIn := encPair encNat encSlotSelectAcc
  have hw : ComputableInPolyTime (fun s : ℕ × SlotSelectAcc =>
      decodeLabelWord s.2.1.2.1.1 s.2.1.1.2 s.1) eIn (encList encNat) :=
    computableInPolyTime_decodeLabelWord'
      (by unfold eIn encSlotSelectAcc encScoreParams; fun_prop)
      (by unfold eIn encSlotSelectAcc encScoreParams; fun_prop)
      (by unfold eIn; fun_prop)
  have hupd_in : ComputableInPolyTime (fun s : ℕ × SlotSelectAcc =>
      ((s.2.2.1, some (decodeLabelWord s.2.1.2.1.1 s.2.1.1.2 s.1)), s.2.2.2.1))
      eIn (encPair (encPair (encPair encBool encUnary) (encOption (encList encNat)))
        encPartialSchedules) := by
    unfold eIn encSlotSelectAcc; fun_prop
  have hcs := computableInPolyTime_updateSlotSchedules.comp hupd_in
  have hsc_in : ComputableInPolyTime (fun s : ℕ × SlotSelectAcc =>
      (s.2.1, updateSlotSchedules s.2.2.1
        (some (decodeLabelWord s.2.1.2.1.1 s.2.1.1.2 s.1)) s.2.2.2.1))
      eIn (encPair encScoreParams encPartialSchedules) :=
    (show ComputableInPolyTime (fun s : ℕ × SlotSelectAcc => s.2.1) eIn encScoreParams by
      unfold eIn encSlotSelectAcc; fun_prop).prod hcs
  have hsc := computableInPolyTime_clearedJointScore.comp hsc_in
  let eBest := encPair (encList encNat) encNat
  let candW (s : ℕ × SlotSelectAcc) := decodeLabelWord s.2.1.2.1.1 s.2.1.1.2 s.1
  let candSc (s : ℕ × SlotSelectAcc) :=
    clearedJointScore s.2.1.1.1 s.2.1.1.2 s.2.1.2.1.1 s.2.1.2.1.2 s.2.1.2.2
      (updateSlotSchedules s.2.2.1 (some (candW s)) s.2.2.2.1).1
      (updateSlotSchedules s.2.2.1 (some (candW s)) s.2.2.2.1).2
  have hsomeCand : ComputableInPolyTime (fun s => some (candW s, candSc s))
      eIn (encOption eBest) := (ComputableInPolyTime.optionSome eBest).comp (hw.prod hsc)
  have hbest : ComputableInPolyTime
      (fun s : ℕ × SlotSelectAcc => s.2.2.2.2.elim (some (candW s, candSc s)) fun best =>
        if decide (candSc s < best.2) then some (candW s, candSc s) else some best)
      eIn (encOption eBest) := by
    refine ComputableInPolyTime.optionElimWithInput
      (by unfold eIn encSlotSelectAcc; fun_prop) hsomeCand ?_
    have hq1 := ComputableInPolyTime.fst eIn eBest
    have hq2 := ComputableInPolyTime.snd eIn eBest
    exact ComputableInPolyTime.ite'
      (ComputableInPolyTime.binary_lt' (hsc.comp hq1)
        ((ComputableInPolyTime.snd (encList encNat) encNat).comp hq2))
      (hsomeCand.comp hq1) ((ComputableInPolyTime.optionSome eBest).comp hq2)
  unfold selectSlotStep
  exact (show ComputableInPolyTime (fun s : ℕ × SlotSelectAcc => s.2.1) eIn encScoreParams by
    unfold eIn encSlotSelectAcc; fun_prop).prod
    ((show ComputableInPolyTime (fun s : ℕ × SlotSelectAcc => s.2.2.1)
        eIn (encPair encBool encUnary) by unfold eIn encSlotSelectAcc; fun_prop).prod
      ((show ComputableInPolyTime (fun s : ℕ × SlotSelectAcc => s.2.2.2.1)
          eIn encPartialSchedules by unfold eIn encSlotSelectAcc; fun_prop).prod hbest))

private def streamSlotCount (a : StreamSlotIn) : ℕ := a.1.2.1.1 ^ a.1.1.2
private def streamSlotInit (a : StreamSlotIn) : SlotSelectAcc := (a.1, (a.2.1, (a.2.2, none)))
private def extractBestSlotWord (st : ℕ × SlotSelectAcc) : List ℕ :=
  st.2.2.2.2.elim (List.replicate st.2.1.1.2 0) Prod.fst

private theorem computableInPolyTime_streamSlotCount :
    ComputableInPolyTime streamSlotCount encStreamSlotIn encNat := by
  unfold streamSlotCount encStreamSlotIn encScoreParams
  exact ComputableInPolyTime.binary_pow' (by fun_prop) (by fun_prop)

private theorem computableInPolyTime_streamSlotInit :
    ComputableInPolyTime streamSlotInit encStreamSlotIn encSlotSelectAcc := by
  unfold streamSlotInit encStreamSlotIn encSlotSelectAcc; fun_prop

private theorem computableInPolyTime_extractBestSlotWord :
    ComputableInPolyTime extractBestSlotWord
      (encPair encNat encSlotSelectAcc) (encList encNat) := by
  unfold extractBestSlotWord encSlotSelectAcc encScoreParams; fun_prop

private noncomputable def mkSlotCert
    (cn : NativeCertificate streamSlotCount encStreamSlotIn encNat)
    (ci : NativeCertificate streamSlotInit encStreamSlotIn encSlotSelectAcc)
    (cb : NativeCertificate selectSlotStep (encPair encNat encSlotSelectAcc) encSlotSelectAcc)
    (cEx : NativeCertificate extractBestSlotWord
      (encPair encNat encSlotSelectAcc) (encList encNat)) :
    NativeCertificate (fun a : StreamSlotIn =>
      streamBestSlotLabel a.1.1.1 a.1.1.2 a.1.2.1.1 a.1.2.1.2 a.1.2.2 a.2.2 a.2.1)
      encStreamSlotIn (encList encNat) :=
  (cEx.comp (IndexFold.certificate cn ci cb)).congr
    fun ⟨⟨⟨n, Q⟩, ⟨r, C⟩, edges⟩, ⟨slot, scheds⟩⟩ => by
      have hp := (run_selectSlotStep_params ((n, Q), (r, C), edges) slot scheds (r ^ Q)).1
      simp only [Function.comp_apply, extractBestSlotWord, streamSlotCount, streamSlotInit,
        streamBestSlotLabel, hp]

/-- Uniform native machine certificate for single-slot candidate streaming `streamBestSlotLabel`. -/
noncomputable def streamBestSlotCertificate :
    NativeCertificate
      (fun ((((n, Q), (r, C), edges), (slot, scheds)) : StreamSlotIn) =>
        streamBestSlotLabel n Q r C edges scheds slot)
      encStreamSlotIn (encList encNat) :=
  mkSlotCert (NativeCertificate.ofPolyTime computableInPolyTime_streamSlotCount)
    (NativeCertificate.ofPolyTime computableInPolyTime_streamSlotInit)
    (NativeCertificate.ofPolyTime computableInPolyTime_selectSlotStep)
    (NativeCertificate.ofPolyTime computableInPolyTime_extractBestSlotWord)

private theorem streamSlotIn_parts_le (a : StreamSlotIn) :
    a.1.1.1 ≤ (encStreamSlotIn a).length ∧ a.1.1.2 ≤ (encStreamSlotIn a).length ∧
      (encNat a.1.2.1.1).length ≤ (encStreamSlotIn a).length ∧
      (encNat a.1.2.1.2).length ≤ (encStreamSlotIn a).length ∧
      a.1.2.2.length ≤ (encStreamSlotIn a).length := by
  have hed : a.1.2.2.length ≤ (encList (encPair encNat encNat) a.1.2.2).length := by
    rw [length_encList]; generalize a.1.2.2 = l; induction l with
    | nil => simp only [List.length_nil, List.map_nil, List.sum_nil, le_rfl]
    | cons _ _ ih => simp only [List.length_cons, List.map_cons, List.sum_cons]; omega
  simp only [encStreamSlotIn, encScoreParams, length_encPair, encUnary_apply, List.length_replicate]
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

private theorem hbFull_run_streamSlotInit_le (a : StreamSlotIn) {j : ℕ}
    (hj : j ≤ streamSlotCount a) :
    (encPair encNat encSlotSelectAcc (IndexFold.run selectSlotStep j (streamSlotInit a))).length ≤
      8 * (encStreamSlotIn a).length * (encStreamSlotIn a).length +
        15 * (encStreamSlotIn a).length + 28 := by
  have hparts := streamSlotIn_parts_le a
  rcases a with ⟨⟨⟨n, Q⟩, ⟨r, C⟩, edges⟩, ⟨slot, scheds⟩⟩
  let L := (encStreamSlotIn (((n, Q), (r, C), edges), (slot, scheds))).length
  have hsz {x : ℕ} (hx : x ≤ L) : (encNat x).length ≤ L := by
    rw [encNat_apply, Nat.size_eq_bits_len]; exact (Nat.size_le_self x).trans hx
  have hnL := hsz hparts.1; have hQL := hsz hparts.2.1; have heL := hsz hparts.2.2.2.2
  have hrL := hparts.2.2.1; have hCL := hparts.2.2.2.1
  have hQr : 8 * Q * (encNat r).length ≤ 8 * L * L := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 8 (Nat.mul_le_mul hparts.2.1 hrL)
  have hst := length_encSlotSelectState_run_le n Q r C edges scheds slot hj
  change (encPair encNat encSlotSelectAcc
    (IndexFold.run selectSlotStep j (((n, Q), (r, C), edges), (slot, (scheds, none))))).length ≤
    8 * L * L + 15 * L + 28; linarith

private theorem mkSlotCert_bounds
    (cn : NativeCertificate streamSlotCount encStreamSlotIn encNat)
    (ci : NativeCertificate streamSlotInit encStreamSlotIn encSlotSelectAcc)
    (cb : NativeCertificate selectSlotStep (encPair encNat encSlotSelectAcc) encSlotSelectAcc)
    (cEx : NativeCertificate extractBestSlotWord
      (encPair encNat encSlotSelectAcc) (encList encNat))
    {pCn pCi pCb pEx : ℕ → ℕ}
    (hpCn : Cslib.PolynomiallyBounded pCn)
    (hCn : ∀ a, cn.time a ≤ pCn (encStreamSlotIn a).length ∧
      cn.space a ≤ pCn (encStreamSlotIn a).length)
    (hpCi : Cslib.PolynomiallyBounded pCi)
    (hCi : ∀ a, ci.time a ≤ pCi (encStreamSlotIn a).length ∧
      ci.space a ≤ pCi (encStreamSlotIn a).length)
    (hpCb : Cslib.PolynomiallyBounded pCb) (hmCb : Monotone pCb)
    (hCb : ∀ s, cb.time s ≤ pCb (encPair encNat encSlotSelectAcc s).length ∧
      cb.space s ≤ pCb (encPair encNat encSlotSelectAcc s).length)
    (hpEx : Cslib.PolynomiallyBounded pEx) (hmEx : Monotone pEx)
    (hEx : ∀ s, cEx.time s ≤ pEx (encPair encNat encSlotSelectAcc s).length ∧
      cEx.space s ≤ pEx (encPair encNat encSlotSelectAcc s).length) :
    ∃ poly : ℕ → ℕ, Cslib.PolynomiallyBounded poly ∧ Monotone poly ∧
      ∀ a, (mkSlotCert cn ci cb cEx).time a ≤
          (a.1.2.1.1 ^ a.1.1.2 + 1) * poly (encStreamSlotIn a).length ∧
        (mkSlotCert cn ci cb cEx).space a ≤ poly (encStreamSlotIn a).length := by
  let bFull (L : ℕ) := 8 * L * L + 15 * L + 28; let lIdx (L : ℕ) := L * L + 1
  let roundOver (L : ℕ) := 3 * bFull L + 2 * (lIdx L + 1) ^ 2 + pCb (bFull L)
  let initExt (L : ℕ) := pCn L + L + pCi L + pEx (bFull L) + lIdx L
  have hraw : Cslib.PolynomiallyBounded (fun L => initExt L + roundOver L) := by
    dsimp only [initExt, roundOver, bFull, lIdx]; fun_prop
  obtain ⟨poly, hpoly, hmpoly, h0⟩ := exists_mono_poly (.of_polynomiallyBounded id hraw)
  refine ⟨poly, hpoly, hmpoly, fun a => ?_⟩
  let L := (encStreamSlotIn a).length; let K := streamSlotCount a
  have hpolyL : initExt L + roundOver L ≤ poly L := h0 L; have hparts := streamSlotIn_parts_le a
  have hlIdx : (encNat K).length ≤ lIdx L := (length_encNat_pow_le a.1.2.1.1 a.1.1.2).trans
    (Nat.add_le_add_right (Nat.mul_le_mul hparts.2.1 hparts.2.2.1) 1)
  let runAt (j : ℕ) := IndexFold.run selectSlotStep j (streamSlotInit a)
  have hbFull (j : ℕ) (hj : j ≤ K) : (encPair encNat encSlotSelectAcc (runAt j)).length ≤ bFull L :=
    hbFull_run_streamSlotInit_le a hj
  let rstep := IndexFold.roundCertificate cb; let initPair := (0, streamSlotInit a)
  let M := NativeCertificate.maxStateLength (encPair encNat encSlotSelectAcc)
    (IndexFold.step selectSlotStep) K initPair
  let RT := NativeCertificate.maxRoundTime rstep K initPair
  let RS := NativeCertificate.maxRoundSpace rstep K initPair
  have hmaxS : M ≤ bFull L := NativeCertificate.maxStateLength_le _ _ _ _ hbFull
  have hcn_a : cn.time a ≤ pCn L ∧ cn.space a ≤ pCn L := hCn a
  have hci_a : ci.time a ≤ pCi L ∧ ci.space a ≤ pCi L := hCi a
  have hexT : cEx.time (runAt K) ≤ pEx (bFull L) := (hEx _).1.trans (hmEx (hbFull K le_rfl))
  have hexS : cEx.space (runAt K) ≤ pEx (bFull L) := (hEx _).2.trans (hmEx (hbFull K le_rfl))
  refine ⟨?_, ?_⟩
  · have hmaxRT : RT ≤ bFull L + (lIdx L + 1) ^ 2 + pCb (bFull L) := by
      refine NativeCertificate.maxRoundTime_le _ _ _ fun j hj => ?_
      have hj_len : (encNat (runAt j).1).length ≤ lIdx L := by
        rw [IndexFold.run_index]; exact (length_encNat_mono hj).trans hlIdx
      have hsq := Nat.pow_le_pow_left (Nat.add_le_add_right hj_len 1) 2
      have hcbT : cb.time (runAt j) ≤ pCb (bFull L) := (hCb _).1.trans (hmCb (hbFull j hj))
      have hst_len := hbFull j hj
      change (encPair encNat encSlotSelectAcc (runAt j)).length +
        ((encNat (runAt j).1).length + 1) ^ 2 + cb.time (runAt j) ≤ _; omega
    have hsqK : ((encNat K).length + 1) ^ 2 ≤ (lIdx L + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hround : RT + M + ((encNat K).length + 1) ^ 2 ≤ roundOver L := by
      dsimp only [roundOver]; omega
    calc (mkSlotCert cn ci cb cEx).time a
        = (cn.time a + (L + ci.time a) +
            (K + 1) * (RT + M + ((encNat K).length + 1) ^ 2)) + cEx.time (runAt K) := rfl
      _ ≤ initExt L + (K + 1) * roundOver L := by
            have := Nat.mul_le_mul_left (K + 1) hround; dsimp only [initExt]; omega
      _ ≤ (K + 1) * initExt L + (K + 1) * roundOver L :=
            Nat.add_le_add_right (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)) _
      _ = (K + 1) * (initExt L + roundOver L) := by ring
      _ ≤ (K + 1) * poly L := Nat.mul_le_mul_left _ hpolyL
  · have hmaxRS : RS ≤ bFull L + (lIdx L + 1) + pCb (bFull L) := by
      refine NativeCertificate.maxRoundSpace_le _ _ _ fun j hj => ?_
      have hj_len : (encNat (runAt j).1).length ≤ lIdx L := by
        rw [IndexFold.run_index]; exact (length_encNat_mono hj).trans hlIdx
      have hcbS : cb.space (runAt j) ≤ pCb (bFull L) := (hCb _).2.trans (hmCb (hbFull j hj))
      have hst_len := hbFull j hj
      change (encPair encNat encSlotSelectAcc (runAt j)).length +
        ((encNat (runAt j).1).length + 1) + cb.space (runAt j) ≤ _; omega
    have hlin_sq : lIdx L + 1 ≤ 2 * (lIdx L + 1) ^ 2 :=
      (Nat.le_mul_self _).trans (by rw [sq]; omega)
    calc (mkSlotCert cn ci cb cEx).space a
        = (cn.space a + (L + ci.space a) + RS + M + (encNat K).length) + cEx.space (runAt K) := rfl
      _ ≤ initExt L + roundOver L := by dsimp only [initExt, roundOver]; omega
      _ ≤ poly L := hpolyL

/-- Trajectory-maximum time and polynomial-workspace bounds for `streamBestSlotCertificate`. -/
theorem streamBestSlotCertificate_bounds :
    ∃ poly : ℕ → ℕ, Cslib.PolynomiallyBounded poly ∧ Monotone poly ∧
      ∀ a : StreamSlotIn,
        let (((_, Q), (r, _), _), _) := a
        streamBestSlotCertificate.time a ≤
            (r ^ Q + 1) * poly (encStreamSlotIn a).length ∧
          streamBestSlotCertificate.space a ≤ poly (encStreamSlotIn a).length := by
  obtain ⟨pCn, hpCn, _, hCn⟩ := exists_mono_poly_cert computableInPolyTime_streamSlotCount
  obtain ⟨pCi, hpCi, _, hCi⟩ := exists_mono_poly_cert computableInPolyTime_streamSlotInit
  obtain ⟨pCb, hpCb, hmCb, hCb⟩ := exists_mono_poly_cert computableInPolyTime_selectSlotStep
  obtain ⟨pEx, hpEx, hmEx, hEx⟩ := exists_mono_poly_cert computableInPolyTime_extractBestSlotWord
  exact mkSlotCert_bounds _ _ _ _ hpCn hCn hpCi hCi hpCb hmCb hCb hpEx hmEx hEx

/-- `streamBestSlotLabel` runs in `O((r ^ Q + 1) * poly(|input|))` native time and polynomial
workspace. -/
theorem computableInO_streamBestSlotLabel :
    ∃ poly : ℕ → ℕ, Cslib.PolynomiallyBounded poly ∧
      ComputableInO
        (fun ((((n, Q), (r, C), edges), (slot, scheds)) : StreamSlotIn) =>
          streamBestSlotLabel n Q r C edges scheds slot)
        encStreamSlotIn (encList encNat)
        (fun a =>
          let (((_, Q), (r, _), _), _) := a
          (r ^ Q + 1) * poly (encStreamSlotIn a).length)
        (fun a => poly (encStreamSlotIn a).length) := by
  obtain ⟨poly, hpoly, _, hB⟩ := streamBestSlotCertificate_bounds
  exact ⟨poly, hpoly, streamBestSlotCertificate.computes.mono_le
    (fun a => (hB a).1) (fun a => (hB a).2)⟩

/-- `streamBestSlotLabel` runs in polynomial workspace (`ComputableInPolySpace`) without
materializing `r ^ Q` candidate words. -/
theorem computableInPolySpace_streamBestSlotLabel :
    ComputableInPolySpace
      (fun ((((n, Q), (r, C), edges), (slot, scheds)) : StreamSlotIn) =>
        streamBestSlotLabel n Q r C edges scheds slot)
      encStreamSlotIn (encList encNat) := by
  obtain ⟨poly, hpoly, c, hc, hl⟩ := computableInO_streamBestSlotLabel
  exact ⟨_, fun n => c * (poly n + 1), by fun_prop, hc, hl⟩

end Cslib.BalancedSchedules

end
