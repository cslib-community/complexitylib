/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.GenericRAM.Native.IndexFold
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import Complexity.Foundations.Data.Nat.Radix
public import Complexity.Logics.Propositional.CNF.ParityTests
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.List.Dedup

/-!
# Runtime greedy parity-row search for CNF formulas

In §6 and Lemma 6.2 of [OpenAI2026ETH] (pp. 40, 42), given an initial parity-check matrix where
every passing nonsatisfying assignment violates at least `m / P` clauses, a deterministic greedy
loop runs for `3n` rounds, streaming all `(2m)^P` tuples `γ ∈ ([m] × {0, 1})^P` via
`Cslib.GenericRAM.IndexFold.run`, materializing `h_γ` mod `2`, and—whenever the candidate space is
nonempty (`0 < candidateTupleCount m P`)—appending the first candidate in enumeration order
minimizing `countSys (rows ++ [h_γ])` (falling back to the length-`m` zero row
`List.replicate m false` when `candidateTupleCount m P = 0`, i.e., `m = 0` and `P > 0`).

## Scope and fixed-counter quantifier

In the native certificate and complexity API (`selectBestStepCertificate`,
`selectBestTestRowCertificate`, `greedyParityRowsCertificate`, `computableInO_selectBestTestRow`,
`computableInO_greedyParityRows`, `computableInPolySpace_greedyParityRows`), the candidate counter
`countSys : List (List Bool) → ℕ` and its certificate
`cCount : NativeCertificate countSys (encList encBits) encNat` are fixed before the runtime inputs
`(m, P, rows)` / `(n, m, P, rows)`. Neither the original CNF formula `φ` nor an arbitrary encoded
context is a runtime input to this machine: choosing a separate `countSys` per `φ` allows a
different machine and polynomial bound per `φ`. Uniform composition with a variable-CNF Theorem 2.2
common-zero counter therefore requires a captured-context certificate interface—for example, a
counter on `(context, rows)` whose encoded `context` is retained and charged throughout `IndexFold`
and the outer `3n`-round loop.

## Main definitions

* `Cslib.Logic.PL.CNF.candidateTupleCount`, `Cslib.Logic.PL.CNF.encodeTestTuple`,
  `Cslib.Logic.PL.CNF.decodeTestTuple`, `Cslib.Logic.PL.CNF.materializeTestRow`: base-`2m` codec
  and length-`m` mod-`2` parity-test row materializer.
* `Cslib.Logic.PL.CNF.selectBestTestRow`, `Cslib.Logic.PL.CNF.greedyParityRows`,
  `Cslib.Logic.PL.CNF.selectBestTestRowCertificate`,
  `Cslib.Logic.PL.CNF.greedyParityRowsCertificate`: streaming selector, `3n`-round greedy loop, and
  fixed-counter native certificates.

## Main results

* `Cslib.Logic.PL.CNF.decodeTestTuple_encodeTestTuple`,
  `Cslib.Logic.PL.CNF.encodeTestTuple_decodeTestTuple`,
  `Cslib.Logic.PL.CNF.mem_map_decodeTestTuple_range`,
  `Cslib.Logic.PL.CNF.length_materializeTestRow`,
  `Cslib.Logic.PL.CNF.count_true_materializeTestRow_le`,
  `Cslib.Logic.PL.CNF.materializeTestRow_ofFn`: base-`2m` bijection, weight `≤ P`, and `testRow`.
* `Cslib.Logic.PL.CNF.computableInPolyTime_candidateTupleCount`,
  `Cslib.Logic.PL.CNF.computableInPolyTime_decodeTestTuple`,
  `Cslib.Logic.PL.CNF.computableInPolyTime_materializeTestRow`: plain polynomial-time certificates.
* `Cslib.Logic.PL.CNF.exists_min_index_selectBestTestRow`,
  `Cslib.Logic.PL.CNF.countSys_selectBestTestRow_le`,
  `Cslib.Logic.PL.CNF.countSys_greedyParityRows_eq_card_sat`,
  `Cslib.Logic.PL.CNF.numPassing_greedyParityRows_fin`: nonempty-space
  (`0 < candidateTupleCount m P`) tie-breaking, minimality, and Lemma 6.2 under
  `hn : 1 ≤ Fintype.card V` and `hP : 1 ≤ P`.
* `Cslib.Logic.PL.CNF.computableInO_selectBestTestRow`,
  `Cslib.Logic.PL.CNF.computableInO_greedyParityRows`,
  `Cslib.Logic.PL.CNF.computableInPolySpace_greedyParityRows`: fixed-counter native time and
  workspace bounds.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §6, §6.2 Lemma 6.2, §6.3
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF

open Finset Cslib.BitString Cslib.GenericRAM Turing.MultiTapeTM

/-! ### Candidate-tuple count and base-`2m` tuple decoding -/

/-- Number `(2 * m) ^ P` of ordered candidate lists `γ ∈ ([m] × {0, 1})^P` (Lemma 6.2, p. 42). -/
def candidateTupleCount (m P : ℕ) : ℕ := (2 * m) ^ P

@[simp] theorem candidateTupleCount_zero_right (m : ℕ) : candidateTupleCount m 0 = 1 := rfl

@[simp] theorem candidateTupleCount_zero_left {P : ℕ} (hP : 1 ≤ P) : candidateTupleCount 0 P = 0 :=
  by simp only [candidateTupleCount, Nat.mul_zero]; exact Nat.zero_pow (by omega)

/-- The binary encoding of `(2 * m) ^ P` has bit-length at most `P * (2 * m) + 1`. -/
theorem length_encNat_candidateTupleCount_le (m P : ℕ) :
    (encNat (candidateTupleCount m P)).length ≤ P * (2 * m) + 1 := by
  rw [encNat_apply, Nat.size_eq_bits_len, candidateTupleCount]
  exact (Nat.size_pow_le (2 * m) P).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left P (Nat.size_le_self (2 * m))) 1)

/-- `candidateTupleCount m P` is computable in polynomial time in binary from unary `(m, P)`. -/
@[fun_prop] theorem computableInPolyTime_candidateTupleCount :
    ComputableInPolyTime (fun p : ℕ × ℕ => candidateTupleCount p.1 p.2)
      (encPair encUnary encUnary) encNat := by
  unfold candidateTupleCount
  exact ComputableInPolyTime.binary_pow'
    (ComputableInPolyTime.unary_to_binary.comp (by fun_prop))
    (ComputableInPolyTime.snd encUnary encUnary)

@[fun_prop] theorem computableInPolyTime_candidateTupleCount' {α : Type} {input : α ↪ List Bool}
    {m P : α → ℕ} (hm : ComputableInPolyTime m input encUnary)
    (hP : ComputableInPolyTime P input encUnary) :
    ComputableInPolyTime (fun a => candidateTupleCount (m a) (P a)) input encNat :=
  computableInPolyTime_candidateTupleCount.comp (hm.prod hP)

/-- Decode a binary candidate index `j : ℕ` in base `2 * m` into `((e₁, c₁), …, (e_P, c_P))`
via `Cslib.Radix.digit` without materializing `(2 * m) ^ P` lists
([OpenAI2026ETH], §6, p. 40; Lemma 6.2, p. 42). At `m = 0`, digits default to `0` so clause
indices remain bounded in unary. -/
def decodeTestTuple (m P j : ℕ) : List (ℕ × Bool) :=
  (List.range P).map fun i =>
    let d := if m = 0 then 0 else Cslib.Radix.digit (2 * m) j i
    (d / 2, decide (d % 2 = 1))

/-- Little-endian base-`2m` encoder inverse to `decodeTestTuple m P` on lists with clause
indices `< m`, defined via `Nat.ofDigits (2 * m)`. -/
def encodeTestTuple (m : ℕ) (γ : List (ℕ × Bool)) : ℕ :=
  Nat.ofDigits (2 * m) (γ.map fun p => 2 * p.1 + p.2.toNat)

@[simp] theorem decodeTestTuple_zero_right (m j : ℕ) : decodeTestTuple m 0 j = [] := rfl

@[simp] theorem length_decodeTestTuple (m P j : ℕ) : (decodeTestTuple m P j).length = P := by
  simp only [decodeTestTuple, List.length_map, List.length_range]

private theorem decodeTestTuple_succ (m P j : ℕ) :
    decodeTestTuple m (P + 1) j =
      (let d := if m = 0 then 0 else j % (2 * m); (d / 2, decide (d % 2 = 1))) ::
        decodeTestTuple m P (j / (2 * m)) := by
  simp only [decodeTestTuple, List.range_succ_eq_map, List.map_cons, List.map_map,
    Function.comp_def, Cslib.Radix.digit]; rfl

/-- Every pair `(e, c)` produced by `decodeTestTuple m P j` satisfies `e < m` when `1 ≤ m`. -/
theorem fst_lt_of_mem_decodeTestTuple {m P j : ℕ} (hm : 1 ≤ m) {p : ℕ × Bool}
    (hp : p ∈ decodeTestTuple m P j) : p.1 < m := by
  have hm0 : m ≠ 0 := by omega
  simp only [decodeTestTuple, hm0, ↓reduceIte, List.mem_map, List.mem_range] at hp
  obtain ⟨i, _, rfl⟩ := hp; rw [Cslib.Radix.digit_eq_div_pow_mod]
  have := Nat.mod_lt (j / (2 * m) ^ i) (show 0 < 2 * m by omega); omega

/-- Encoding any list `γ` with clause indices `< m` yields an index `< (2 * m) ^ γ.length`. -/
theorem encodeTestTuple_lt {m : ℕ} {γ : List (ℕ × Bool)} (hγ : ∀ p ∈ γ, p.1 < m) :
    encodeTestTuple m γ < candidateTupleCount m γ.length := by
  rcases γ with _ | ⟨p, tl⟩
  · simp only [encodeTestTuple, List.map_nil, Nat.ofDigits_nil, List.length_nil,
      candidateTupleCount_zero_right, zero_lt_one]
  · have hp : p.1 < m := hγ p List.mem_cons_self
    simpa only [encodeTestTuple, candidateTupleCount, List.length_map] using
      Nat.ofDigits_lt_base_pow_length_of_pos (B := 2 * m) (by omega)
        ((p :: tl).map fun q => 2 * q.1 + q.2.toNat) (fun a ha => by
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
          have := hγ q hq; have := Bool.toNat_le q.2; omega)

/-- Decoding the index of any valid list `γ` recovers `γ` exactly. -/
theorem decodeTestTuple_encodeTestTuple {m : ℕ} {γ : List (ℕ × Bool)} (hγ : ∀ p ∈ γ, p.1 < m) :
    decodeTestTuple m γ.length (encodeTestTuple m γ) = γ := by
  apply List.ext_getElem (length_decodeTestTuple _ _ _); intro i h1 h2
  have hi_lt : γ[i].1 < m := hγ γ[i] (List.getElem_mem h2)
  have hm0 : m ≠ 0 := by omega
  have hdig : Cslib.Radix.digit (2 * m) (encodeTestTuple m γ) i = 2 * γ[i].1 + γ[i].2.toNat := by
    rw [encodeTestTuple, Cslib.Radix.digit_ofDigits (B := 2 * m) (by omega)
      (γ.map fun p => 2 * p.1 + p.2.toNat)
      (fun a ha => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
        have := hγ q hq; have := Bool.toNat_le q.2; omega)
      i (by simp only [List.length_map]; exact h2), List.getElem_map]
  simp only [decodeTestTuple, List.getElem_map, List.getElem_range, hm0, ↓reduceIte, hdig]
  generalize γ[i] = p; rcases p with ⟨e, _ | _⟩
  · simp only [Bool.toNat_false, Nat.add_zero, Prod.mk.injEq, decide_eq_false_iff_not]
    exact ⟨by omega, by omega⟩
  · simp only [Bool.toNat_true, Prod.mk.injEq, decide_eq_true_eq]; exact ⟨by omega, by omega⟩

/-- Encoding the decoded tuple of any `j < (2 * m) ^ P` recovers `j`. -/
theorem encodeTestTuple_decodeTestTuple {m P j : ℕ} (hj : j < candidateTupleCount m P) :
    encodeTestTuple m (decodeTestTuple m P j) = j := by
  rcases Nat.eq_zero_or_pos P with rfl | hP
  · simp only [candidateTupleCount_zero_right, Nat.lt_one_iff] at hj; subst hj; rfl
  · obtain ⟨x, hx, rfl⟩ := Nat.exists_ofDigits_ofFn hj
    have hB : 0 < 2 * m := Nat.zero_lt_of_lt (hx ⟨0, hP⟩)
    have hm0 : m ≠ 0 := by omega
    rw [encodeTestTuple]; congr 1
    apply List.ext_getElem
      (by simp only [List.length_map, length_decodeTestTuple, List.length_ofFn])
    intro i _ h2
    have hi : i < P := by simpa only [List.length_ofFn] using h2
    have hdig :
        Cslib.Radix.digit (2 * m) (Nat.ofDigits (2 * m) (List.ofFn x)) i = x ⟨i, hi⟩ := by
      rw [Cslib.Radix.digit_ofDigits hB (List.ofFn x)
        (fun a ha => by obtain ⟨r, rfl⟩ := List.mem_ofFn.mp ha; exact hx r)
        i (by simp only [List.length_ofFn]; exact hi), List.getElem_ofFn]
    simp only [decodeTestTuple, List.getElem_map, List.getElem_range, hm0, ↓reduceIte, hdig,
      List.getElem_ofFn]
    rcases Nat.mod_two_eq_zero_or_one (x ⟨i, hi⟩) with h0 | h1
    · simp only [h0, zero_ne_one, decide_false, Bool.toNat_false, Nat.add_zero]; omega
    · simp only [h1, decide_true, Bool.toNat_true]; omega

private theorem encodeTestTuple_ofFn_lt {m P : ℕ} (γ : Fin P → Fin m × Bool) :
    encodeTestTuple m (List.ofFn fun r => ((γ r).1.val, (γ r).2)) < candidateTupleCount m P := by
  simpa only [List.length_ofFn] using encodeTestTuple_lt (m := m)
    (γ := List.ofFn fun r => ((γ r).1.val, (γ r).2))
    (fun p hp => by obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hp; exact (γ r).1.isLt)

private theorem decodeTestTuple_encodeTestTuple_ofFn {m P : ℕ} (γ : Fin P → Fin m × Bool) :
    decodeTestTuple m P (encodeTestTuple m (List.ofFn fun r => ((γ r).1.val, (γ r).2))) =
      List.ofFn fun r => ((γ r).1.val, (γ r).2) := by
  simpa only [List.length_ofFn] using decodeTestTuple_encodeTestTuple (m := m)
    (γ := List.ofFn fun r => ((γ r).1.val, (γ r).2))
    (fun p hp => by obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hp; exact (γ r).1.isLt)

/-- Completeness of `decodeTestTuple m P` over `List.range ((2 * m) ^ P)`. -/
theorem mem_map_decodeTestTuple_range {m P : ℕ} (γ : Fin P → Fin m × Bool) :
    (List.ofFn fun r => ((γ r).1.val, (γ r).2)) ∈
      (List.range (candidateTupleCount m P)).map (decodeTestTuple m P) :=
  List.mem_map.mpr ⟨encodeTestTuple m (List.ofFn fun r => ((γ r).1.val, (γ r).2)),
    List.mem_range.mpr (encodeTestTuple_ofFn_lt γ), decodeTestTuple_encodeTestTuple_ofFn γ⟩

/-- Every valid candidate index `j < (2 * m) ^ P` decodes to a typed `γ : Fin P → Fin m × Bool`. -/
theorem exists_fin_of_lt_candidateTupleCount {m P j : ℕ} (hj : j < candidateTupleCount m P) :
    ∃ γ : Fin P → Fin m × Bool,
      decodeTestTuple m P j = List.ofFn fun r => ((γ r).1.val, (γ r).2) := by
  rcases Nat.eq_zero_or_pos P with rfl | hP
  · exact ⟨Fin.elim0, by simp only [decodeTestTuple_zero_right, List.ofFn_zero]⟩
  · have hm : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rw [candidateTupleCount_zero_left hP] at hj; omega
      · exact hm
    refine ⟨fun r =>
      let p := (decodeTestTuple m P j)[r.val]'(by rw [length_decodeTestTuple]; exact r.isLt)
      (⟨p.1, fst_lt_of_mem_decodeTestTuple hm (List.getElem_mem _)⟩, p.2), ?_⟩
    apply List.ext_getElem (by simp only [length_decodeTestTuple, List.length_ofFn])
    intro i _ _; simp only [List.getElem_ofFn, Prod.mk.eta]

/-- `decodeTestTuple m P j` is computable in polynomial time from unary `(m, P)` and binary `j`. -/
@[fun_prop] theorem computableInPolyTime_decodeTestTuple :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => decodeTestTuple p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encUnary) encNat) (encList (encPair encUnary encBool)) := by
  let encElem := encPair encUnary encBool
  let encState := encPair encNat (encList encElem)
  let encQ := encPair (encPair encUnary encState) encBool
  let step (m : ℕ) (state : ℕ × List (ℕ × Bool)) : ℕ × List (ℕ × Bool) :=
    let d := if m = 0 then 0 else state.1 % (2 * m)
    (state.1 / (2 * m), state.2 ++ [(d / 2, decide (d % 2 = 1))])
  have hfold_acc (m P j : ℕ) (acc : List (ℕ × Bool)) :
      ((List.replicate P true).foldl (fun state _ => step m state) (j, acc)).2 =
        acc ++ decodeTestTuple m P j := by
    induction P generalizing j acc with
    | zero => simp only [List.replicate_zero, List.foldl_nil, decodeTestTuple_zero_right,
        List.append_nil]
    | succ P ih =>
      rw [List.replicate_succ, List.foldl_cons, ih, decodeTestTuple_succ,
        List.append_assoc, List.singleton_append]
  have hq1 := ComputableInPolyTime.fst (encPair encUnary encState) encBool
  have hm_q := (ComputableInPolyTime.fst encUnary encState).comp hq1
  have hst_q := (ComputableInPolyTime.snd encUnary encState).comp hq1
  have hcur := (ComputableInPolyTime.fst encNat (encList encElem)).comp hst_q
  have hacc := (ComputableInPolyTime.snd encNat (encList encElem)).comp hst_q
  have hm0 : ComputableInPolyTime
      (fun q : (ℕ × (ℕ × List (ℕ × Bool))) × Bool => decide (q.1.1 = 0)) encQ encBool :=
    ComputableInPolyTime.decide_eq' hm_q (ComputableInPolyTime.const 0)
  have h2m : ComputableInPolyTime
      (fun q : (ℕ × (ℕ × List (ℕ × Bool))) × Bool => 2 * q.1.1) encQ encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hd : ComputableInPolyTime
      (fun q : (ℕ × (ℕ × List (ℕ × Bool))) × Bool =>
        if q.1.1 = 0 then 0 else q.1.2.1 % (2 * q.1.1)) encQ encNat := by
    convert hm0.ite (ComputableInPolyTime.const 0)
      (ComputableInPolyTime.binary_mod.comp (hcur.prod h2m)) using 1
    funext q; simp only [Function.comp_apply, decide_eq_true_eq]
  have hdigitIdx : ComputableInPolyTime
      (fun q : (ℕ × (ℕ × List (ℕ × Bool))) × Bool =>
        (if q.1.1 = 0 then 0 else q.1.2.1 % (2 * q.1.1)) / 2) encQ encUnary := by
    refine ComputableInPolyTime.binary_to_unary_bounded
      (ComputableInPolyTime.binary_div.comp (hd.prod (ComputableInPolyTime.const 2))) hm_q ?_
    intro q; dsimp only [Function.comp_apply]; split_ifs with hm
    · omega
    · have := Nat.mod_lt q.1.2.1 (show 0 < 2 * q.1.1 by omega); omega
  have hstep : ComputableInPolyTime
      (fun q : (ℕ × (ℕ × List (ℕ × Bool))) × Bool => step q.1.1 q.1.2) encQ encState := by
    have hbit := (ComputableInPolyTime.binary_mod.comp (hd.prod
      (ComputableInPolyTime.const 2))).beq (ComputableInPolyTime.const 1)
    have hbit_eq (n : ℕ) : (n == 1) = decide (n = 1) :=
      Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq, decide_eq_true_eq])
    convert (ComputableInPolyTime.binary_div.comp (hcur.prod h2m)).prod
      ((ComputableInPolyTime.snoc encElem).comp (hacc.prod (hdigitIdx.prod hbit)))
      using 1
    funext q; simp only [Function.comp_apply, step, hbit_eq]
  have hlist := (ComputableInPolyTime.of_eq (encIn := encUnary) (encOut := encBits)
    fun _ => rfl).comp ((ComputableInPolyTime.snd encUnary encUnary).comp
      (ComputableInPolyTime.fst (encPair encUnary encUnary) encNat))
  have hinit := (ComputableInPolyTime.snd (encPair encUnary encUnary) encNat).prod
    (ComputableInPolyTime.const (encOut := encList encElem) [])
  have hpar := (ComputableInPolyTime.fst encUnary encUnary).comp
    (ComputableInPolyTime.fst (encPair encUnary encUnary) encNat)
  have hfold := ComputableInPolyTime.foldlWith_of_bounded_growth
    (encA := encBool) (encL := encBits) (encB := encState) (encP := encUnary)
    (par := fun p : (ℕ × ℕ) × ℕ => p.1.1) (step := fun m state _ => step m state)
    hpar hlist hinit hstep
    (growth := fun p => 4 * (encPair (encPair encUnary encUnary) encNat p).length + 6)
    (((PolyBounded.const 4).mul .self).add (.const 6))
    (fun p state _ _ => by
      have hm_le : p.1.1 ≤ (encPair (encPair encUnary encUnary) encNat p).length := by
        simp only [length_encPair, encUnary_apply, List.length_replicate]; omega
      have hd_le : (if p.1.1 = 0 then 0 else state.1 % (2 * p.1.1)) / 2 ≤ p.1.1 := by
        split_ifs with hm
        · omega
        · have := Nat.mod_lt state.1 (show 0 < 2 * p.1.1 by omega); omega
      have hdiv_le : (encNat (state.1 / (2 * p.1.1))).length ≤ (encNat state.1).length := by
        simp only [encNat_apply, Nat.size_eq_bits_len]
        exact Nat.size_le_size (Nat.div_le_self _ _)
      simp only [step, encState, encElem, length_encPair, encList_append, List.length_append,
        encList_cons, encList_nil, List.append_nil, length_frame, encUnary_apply,
        List.length_replicate, encBool_apply, List.length_singleton]
      omega)
  convert (ComputableInPolyTime.snd encNat (encList encElem)).comp hfold using 1
  funext p; simp only [Function.comp_apply, hfold_acc, List.nil_append]

@[fun_prop] theorem computableInPolyTime_decodeTestTuple' {α : Type} {input : α ↪ List Bool}
    {m P j : α → ℕ} (hm : ComputableInPolyTime m input encUnary)
    (hP : ComputableInPolyTime P input encUnary) (hj : ComputableInPolyTime j input encNat) :
    ComputableInPolyTime (fun a => decodeTestTuple (m a) (P a) (j a))
      input (encList (encPair encUnary encBool)) :=
  computableInPolyTime_decodeTestTuple.comp ((hm.prod hP).prod hj)

/-! ### Mod-`2` row materialization -/

/-- Materialize the length-`m` binary row `h_γ` from a test list `γ`, summing coefficients `c_r`
modulo `2` (`xor`) across occurrences of `e` ([OpenAI2026ETH], §6, p. 40; Lemma 6.2, p. 42). -/
def materializeTestRow (m : ℕ) (γ : List (ℕ × Bool)) : List Bool :=
  (List.range m).map fun e =>
    γ.foldl (fun acc p => if p.1 = e then xor acc p.2 else acc) false

@[simp] theorem length_materializeTestRow (m : ℕ) (γ : List (ℕ × Bool)) :
    (materializeTestRow m γ).length = m := by
  simp only [materializeTestRow, List.length_map, List.length_range]

private theorem foldl_xor_eq_sum (e : ℕ) (γ : List (ℕ × Bool)) (init : Bool) :
    γ.foldl (fun acc p => if p.1 = e then xor acc p.2 else acc) init =
      init + (γ.map fun p => if p.1 = e then p.2 else 0).sum := by
  induction γ generalizing init with
  | nil => simp only [List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
  | cons p γ ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
    rw [← add_assoc]; congr 1; split_ifs <;> cases init <;> cases p.2 <;> rfl

/-- Exact bridge to `Cslib.BitString.testRow` on `γ : Fin P → Fin m × Bool`. -/
theorem materializeTestRow_ofFn {m P : ℕ} (γ : Fin P → Fin m × Bool) :
    materializeTestRow m (List.ofFn fun r => ((γ r).1.val, (γ r).2)) = List.ofFn (testRow γ) := by
  apply List.ext_getElem (by simp only [length_materializeTestRow, List.length_ofFn]); intro i _ _
  simp only [materializeTestRow, List.getElem_map, List.getElem_range, List.getElem_ofFn,
    foldl_xor_eq_sum, List.map_ofFn, testRow]
  change (0 : Bool) + _ = _; rw [zero_add, ← List.sum_ofFn]
  exact congrArg (fun fn => (List.ofFn fn).sum)
    (funext fun r => by simp only [Function.comp_apply, Fin.ext_iff])

private theorem foldl_xor_eq_false_of_not_mem (e : ℕ) (γ : List (ℕ × Bool))
    (h : e ∉ γ.map Prod.fst) :
    γ.foldl (fun acc p => if p.1 = e then xor acc p.2 else acc) false = false := by
  induction γ with
  | nil => rfl
  | cons p γ ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [List.foldl_cons, Ne.symm h.1, ↓reduceIte]; exact ih h.2

/-- Every materialized row has at most `γ.length` ones (fewer when repeated indices cancel). -/
theorem count_true_materializeTestRow_le (m : ℕ) (γ : List (ℕ × Bool)) :
    (materializeTestRow m γ).count true ≤ γ.length := by
  let f (e : ℕ) : Bool := γ.foldl (fun acc p => if p.1 = e then xor acc p.2 else acc) false
  have hsub : ((List.range m).filter f).toFinset ⊆ (γ.map Prod.fst).toFinset := by
    intro e he; rw [List.mem_toFinset, List.mem_filter] at he; rw [List.mem_toFinset]
    by_contra hnot
    exact Bool.false_ne_true ((foldl_xor_eq_false_of_not_mem e γ hnot).symm.trans he.2)
  have hcnt : (materializeTestRow m γ).count true = ((List.range m).filter f).length := by
    rw [materializeTestRow, List.count_eq_countP, List.countP_map, List.countP_eq_length_filter]
    exact congrArg List.length
      (List.filter_congr fun e _ => by simp only [Function.comp_apply, beq_true, f])
  rw [hcnt, ← List.toFinset_card_of_nodup (List.nodup_range.filter f)]
  exact (Finset.card_le_card hsub).trans
    ((List.toFinset_card_le (γ.map Prod.fst)).trans (by simp only [List.length_map, le_rfl]))

/-- Every decoded candidate row for `(m, P)` has Hamming weight at most `P`. -/
theorem count_true_materializeTestRow_decodeTestTuple_le (m P j : ℕ) :
    (materializeTestRow m (decodeTestTuple m P j)).count true ≤ P := by
  simpa only [length_decodeTestTuple] using
    count_true_materializeTestRow_le m (decodeTestTuple m P j)

/-- `materializeTestRow` is computable in polynomial time from unary `m` and `(e, c)` pairs. -/
@[fun_prop] theorem computableInPolyTime_materializeTestRow :
    ComputableInPolyTime (fun p : ℕ × List (ℕ × Bool) => materializeTestRow p.1 p.2)
      (encPair encUnary (encList (encPair encUnary encBool))) encBits := by
  unfold materializeTestRow
  let encElem := encPair encUnary encBool; let encIn := encPair encUnary (encList encElem)
  apply ComputableInPolyTime.mapToBitsWithInput
    (ComputableInPolyTime.range.comp
      (ComputableInPolyTime.fst encUnary (encList encElem)))
  apply ComputableInPolyTime.foldlWith
    (encA := encElem) (encL := encList encElem) (encB := encBool) (encP := encUnary)
    (par := fun q : (ℕ × List (ℕ × Bool)) × ℕ => q.2)
    (list := fun q : (ℕ × List (ℕ × Bool)) × ℕ => q.1.2)
    (init := fun _ : (ℕ × List (ℕ × Bool)) × ℕ => false)
    (step := fun e acc p => if p.1 = e then xor acc p.2 else acc)
    (ComputableInPolyTime.snd encIn encUnary)
    ((ComputableInPolyTime.snd encUnary (encList encElem)).comp
      (ComputableInPolyTime.fst encIn encUnary))
    (ComputableInPolyTime.const false)
    (by
      let encStep := encPair (encPair encUnary encBool) encElem
      have hr1 := ComputableInPolyTime.fst (encPair encUnary encBool) encElem
      have hr2 := ComputableInPolyTime.snd (encPair encUnary encBool) encElem
      have heq : ComputableInPolyTime
          (fun r : (ℕ × Bool) × (ℕ × Bool) => decide (r.2.1 = r.1.1)) encStep encBool :=
        ComputableInPolyTime.decide_eq'
          ((ComputableInPolyTime.fst encUnary encBool).comp hr2)
          ((ComputableInPolyTime.fst encUnary encBool).comp hr1)
      have hxor : ComputableInPolyTime
          (fun r : (ℕ × Bool) × (ℕ × Bool) => xor r.1.2 r.2.2) encStep encBool :=
        (ComputableInPolyTime.of_finite (fun b : Bool × Bool => xor b.1 b.2)).comp
          (((ComputableInPolyTime.snd encUnary encBool).comp hr1).prod
            ((ComputableInPolyTime.snd encUnary encBool).comp hr2))
      convert heq.ite hxor ((ComputableInPolyTime.snd encUnary encBool).comp hr1) using 1
      funext r; simp only [Function.comp_apply, decide_eq_true_eq])
    (B := fun _ => 1) (.const 1)
    (fun _ _ _ => by simp only [encBool_apply, List.length_singleton, le_rfl])

@[fun_prop] theorem computableInPolyTime_materializeTestRow' {α : Type} {input : α ↪ List Bool}
    {m : α → ℕ} {γ : α → List (ℕ × Bool)} (hm : ComputableInPolyTime m input encUnary)
    (hγ : ComputableInPolyTime γ input (encList (encPair encUnary encBool))) :
    ComputableInPolyTime (fun a => materializeTestRow (m a) (γ a)) input encBits :=
  computableInPolyTime_materializeTestRow.comp (hm.prod hγ)

/-! ### Streaming `(2m)^P` min-count selector and `3n`-round greedy loop -/

/-- Live streaming accumulator: `(m, P)`, `rows`, and optional `(bestRow, bestVal)`. -/
abbrev SelectBestAcc : Type := (ℕ × ℕ) × (List (List Bool) × Option (List Bool × ℕ))

/-- Callback body of `IndexFold.run` for candidate index `j`, replacing the incumbent only on
strict improvement `candVal < best.2` ([OpenAI2026ETH], Lemma 6.2, p. 42). -/
def selectBestStep (countSys : List (List Bool) → ℕ)
    (state : ℕ × SelectBestAcc) : SelectBestAcc :=
  let m := state.2.1.1; let P := state.2.1.2; let rows := state.2.2.1
  let candRow := materializeTestRow m (decodeTestTuple m P state.1)
  let candVal := countSys (rows ++ [candRow])
  let nextBest := state.2.2.2.elim (some (candRow, candVal)) fun best =>
    if decide (candVal < best.2) then some (candRow, candVal) else some best
  ((m, P), (rows, nextBest))

/-- Stream `j ∈ 0 .. (2 * m) ^ P - 1` via `Cslib.GenericRAM.IndexFold.run`: when the candidate
space is nonempty (`0 < candidateTupleCount m P`), select the first candidate parity-test row in
enumeration order attaining the minimum of `countSys (rows ++ [h_γ])`; if
`candidateTupleCount m P = 0` (`m = 0`, `P > 0`), return the total fallback length-`m` zero row
`List.replicate m false`. -/
def selectBestTestRow (countSys : List (List Bool) → ℕ)
    (m P : ℕ) (rows : List (List Bool)) : List Bool :=
  ((IndexFold.run (selectBestStep countSys) (candidateTupleCount m P)
      ((m, P), (rows, none))).2.2.2).elim (List.replicate m false) Prod.fst

/-- Prefix sequence of rows after `i` greedy rounds from `initRows`. -/
def greedyParityRowsAt (countSys : List (List Bool) → ℕ)
    (m P : ℕ) (initRows : List (List Bool)) (i : ℕ) : List (List Bool) :=
  (fun rows => rows ++ [selectBestTestRow countSys m P rows])^[i] initRows

/-- Append `3 * n` greedily selected parity-test rows of list length `P` and width `m`, starting
from `initRows` ([OpenAI2026ETH], Lemma 6.2, p. 42). -/
def greedyParityRows (countSys : List (List Bool) → ℕ)
    (n m P : ℕ) (initRows : List (List Bool)) : List (List Bool) :=
  greedyParityRowsAt countSys m P initRows (3 * n)

@[simp] theorem greedyParityRowsAt_zero (countSys : List (List Bool) → ℕ)
    (m P : ℕ) (initRows : List (List Bool)) :
    greedyParityRowsAt countSys m P initRows 0 = initRows := rfl

theorem greedyParityRowsAt_succ (countSys : List (List Bool) → ℕ)
    (m P : ℕ) (initRows : List (List Bool)) (i : ℕ) :
    greedyParityRowsAt countSys m P initRows (i + 1) =
      greedyParityRowsAt countSys m P initRows i ++
        [selectBestTestRow countSys m P (greedyParityRowsAt countSys m P initRows i)] :=
  Function.iterate_succ_apply' _ _ _

/-! ### Prefix invariant, tie-breaking, and minimality -/

private theorem run_selectBestStep_params (countSys : List (List Bool) → ℕ)
    (m P k : ℕ) (rows : List (List Bool)) :
    (IndexFold.run (selectBestStep countSys) k ((m, P), (rows, none))).2.1 = (m, P) ∧
      (IndexFold.run (selectBestStep countSys) k ((m, P), (rows, none))).2.2.1 = rows := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    rw [IndexFold.run_succ]; simp only [IndexFold.step, selectBestStep, ih.1, ih.2, and_self]

private theorem run_selectBestStep_spec (countSys : List (List Bool) → ℕ)
    (m P : ℕ) (rows : List (List Bool)) :
    ∀ {k : ℕ}, 0 < k →
      ∃ jStar < k,
        (IndexFold.run (selectBestStep countSys) k ((m, P), (rows, none))).2.2.2 =
          some (materializeTestRow m (decodeTestTuple m P jStar),
            countSys (rows ++ [materializeTestRow m (decodeTestTuple m P jStar)])) ∧
        (∀ j < k,
          countSys (rows ++ [materializeTestRow m (decodeTestTuple m P jStar)]) ≤
            countSys (rows ++ [materializeTestRow m (decodeTestTuple m P j)])) ∧
        (∀ j < jStar,
          countSys (rows ++ [materializeTestRow m (decodeTestTuple m P jStar)]) <
            countSys (rows ++ [materializeTestRow m (decodeTestTuple m P j)])) := by
  intro k hk; induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · refine ⟨0, Nat.zero_lt_one, by rw [IndexFold.run_succ, IndexFold.run_zero]; exact rfl, ?_, ?_⟩
      · intro j hj; rw [show j = 0 by omega]
      · intro _ hj; omega
    · obtain ⟨jStar, hjStar_lt, hopt, hle, hlt⟩ := ih hkpos
      have hparams := run_selectBestStep_params countSys m P k rows
      have hidx := IndexFold.run_index (selectBestStep countSys) k ((m, P), (rows, none))
      let candRowK := materializeTestRow m (decodeTestTuple m P k)
      let candValK := countSys (rows ++ [candRowK])
      let bestVal := countSys (rows ++ [materializeTestRow m (decodeTestTuple m P jStar)])
      by_cases hcmp : candValK < bestVal
      · refine ⟨k, Nat.lt_succ_self k, ?_, ?_, fun j hj => lt_of_lt_of_le hcmp (hle j hj)⟩
        · rw [IndexFold.run_succ]
          simp only [IndexFold.step, selectBestStep, hidx, hparams.1, hparams.2, hopt,
            Option.elim_some, candRowK, candValK, bestVal, decide_eq_true hcmp, ↓reduceIte]
        · intro j hj; rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
          · exact hcmp.le.trans (hle j hj')
          · exact le_rfl
      · refine ⟨jStar, Nat.lt_succ_of_lt hjStar_lt, ?_, ?_, hlt⟩
        · rw [IndexFold.run_succ]
          simp only [IndexFold.step, selectBestStep, hidx, hparams.1, hparams.2, hopt,
            Option.elim_some, candRowK, candValK, bestVal, decide_eq_false hcmp,
            Bool.false_eq_true, ↓reduceIte]
        · intro j hj; rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
          · exact hle j hj'
          · exact Nat.le_of_not_lt hcmp

/-- Enumeration-order tie-breaking characterization of `selectBestTestRow` when `(2 * m) ^ P > 0`:
`jStar < (2 * m) ^ P` attains the minimum count and strictly beats every `j < jStar`. -/
theorem exists_min_index_selectBestTestRow (countSys : List (List Bool) → ℕ)
    {m P : ℕ} (rows : List (List Bool)) (hpos : 0 < candidateTupleCount m P) :
    ∃ jStar < candidateTupleCount m P,
      selectBestTestRow countSys m P rows =
        materializeTestRow m (decodeTestTuple m P jStar) ∧
      (∀ j < candidateTupleCount m P,
        countSys (rows ++ [materializeTestRow m (decodeTestTuple m P jStar)]) ≤
          countSys (rows ++ [materializeTestRow m (decodeTestTuple m P j)])) ∧
      (∀ j < jStar,
        countSys (rows ++ [materializeTestRow m (decodeTestTuple m P jStar)]) <
          countSys (rows ++ [materializeTestRow m (decodeTestTuple m P j)])) := by
  obtain ⟨jStar, hjStar, hopt, hle, hlt⟩ := run_selectBestStep_spec countSys m P rows hpos
  exact ⟨jStar, hjStar, by simp only [selectBestTestRow, hopt, Option.elim_some], hle, hlt⟩

@[simp] theorem length_selectBestTestRow (countSys : List (List Bool) → ℕ)
    (m P : ℕ) (rows : List (List Bool)) :
    (selectBestTestRow countSys m P rows).length = m := by
  rcases Nat.eq_zero_or_pos (candidateTupleCount m P) with h0 | hpos
  · simp only [selectBestTestRow, h0, IndexFold.run_zero, Option.elim_none, List.length_replicate]
  · obtain ⟨jStar, _, hrow, _, _⟩ := exists_min_index_selectBestTestRow countSys rows hpos
    rw [hrow, length_materializeTestRow]

/-- The selected parity-test row has Hamming weight (`count true`) at most `P`. -/
theorem count_true_selectBestTestRow_le (countSys : List (List Bool) → ℕ)
    (m P : ℕ) (rows : List (List Bool)) :
    (selectBestTestRow countSys m P rows).count true ≤ P := by
  rcases Nat.eq_zero_or_pos (candidateTupleCount m P) with h0 | hpos
  · simp only [selectBestTestRow, h0, IndexFold.run_zero, Option.elim_none, List.count_replicate,
      beq_iff_eq, Bool.false_eq_true, ↓reduceIte, Nat.zero_le]
  · obtain ⟨jStar, _, hrow, _, _⟩ := exists_min_index_selectBestTestRow countSys rows hpos
    rw [hrow]; exact count_true_materializeTestRow_decodeTestTuple_le m P jStar

/-- Minimality over all test tuples `γ : Fin P → Fin m × Bool`. -/
theorem countSys_selectBestTestRow_le (countSys : List (List Bool) → ℕ)
    {m P : ℕ} (rows : List (List Bool)) (γ : Fin P → Fin m × Bool) :
    countSys (rows ++ [selectBestTestRow countSys m P rows]) ≤
      countSys (rows ++ [List.ofFn (testRow γ)]) := by
  have hj_lt := encodeTestTuple_ofFn_lt γ
  obtain ⟨jStar, _, hrow, hle, _⟩ :=
    exists_min_index_selectBestTestRow countSys rows (Nat.zero_lt_of_lt hj_lt)
  rw [hrow]; have htarget := hle _ hj_lt
  rwa [decodeTestTuple_encodeTestTuple_ofFn, materializeTestRow_ofFn] at htarget

/-- Whenever `(2 * m) ^ P > 0`, `selectBestTestRow` equals `List.ofFn (testRow γ)` for some `γ`. -/
theorem exists_fin_selectBestTestRow (countSys : List (List Bool) → ℕ)
    {m P : ℕ} (rows : List (List Bool)) (hpos : 0 < candidateTupleCount m P) :
    ∃ γ : Fin P → Fin m × Bool,
      selectBestTestRow countSys m P rows = List.ofFn (testRow γ) := by
  obtain ⟨jStar, hjStar, hrow, _, _⟩ := exists_min_index_selectBestTestRow countSys rows hpos
  obtain ⟨γ, hγ⟩ := exists_fin_of_lt_candidateTupleCount hjStar
  exact ⟨γ, by rw [hrow, hγ, materializeTestRow_ofFn]⟩

/-! ### Row counts, widths, weights, and CNF bridge for `greedyParityRows` -/

@[simp] theorem length_greedyParityRowsAt (countSys : List (List Bool) → ℕ)
    (m P : ℕ) (initRows : List (List Bool)) (i : ℕ) :
    (greedyParityRowsAt countSys m P initRows i).length = initRows.length + i := by
  induction i with
  | zero => simp only [greedyParityRowsAt_zero, Nat.add_zero]
  | succ i ih =>
    rw [greedyParityRowsAt_succ, List.length_append, List.length_singleton, ih, Nat.add_assoc]

@[simp] theorem length_greedyParityRows (countSys : List (List Bool) → ℕ)
    (n m P : ℕ) (initRows : List (List Bool)) :
    (greedyParityRows countSys n m P initRows).length = initRows.length + 3 * n :=
  length_greedyParityRowsAt countSys m P initRows (3 * n)

private theorem prefix_greedyParityRowsAt (countSys : List (List Bool) → ℕ)
    (m P : ℕ) (initRows : List (List Bool)) (i : ℕ) :
    initRows <+: greedyParityRowsAt countSys m P initRows i := by
  induction i with
  | zero => exact List.prefix_rfl
  | succ i ih => rw [greedyParityRowsAt_succ]; exact ih.trans (List.prefix_append _ _)

private theorem mem_greedyParityRowsAt (countSys : List (List Bool) → ℕ)
    {m P : ℕ} {initRows : List (List Bool)} {i : ℕ} {r : List Bool}
    (hr : r ∈ greedyParityRowsAt countSys m P initRows i) :
    r ∈ initRows ∨ (r.length = m ∧ r.count true ≤ P) := by
  induction i with
  | zero => exact Or.inl hr
  | succ i ih =>
    rw [greedyParityRowsAt_succ, List.mem_append, List.mem_singleton] at hr
    exact hr.elim ih fun h =>
      Or.inr (h ▸ ⟨length_selectBestTestRow _ _ _ _, count_true_selectBestTestRow_le _ _ _ _⟩)

theorem length_of_mem_greedyParityRowsAt (countSys : List (List Bool) → ℕ)
    {m P : ℕ} {initRows : List (List Bool)} (hinit : ∀ r ∈ initRows, r.length = m)
    (i : ℕ) {r : List Bool} (hr : r ∈ greedyParityRowsAt countSys m P initRows i) :
    r.length = m :=
  (mem_greedyParityRowsAt countSys hr).elim (hinit r) And.left

theorem length_of_mem_greedyParityRows (countSys : List (List Bool) → ℕ)
    {n m P : ℕ} {initRows : List (List Bool)} (hinit : ∀ r ∈ initRows, r.length = m)
    {r : List Bool} (hr : r ∈ greedyParityRows countSys n m P initRows) :
    r.length = m :=
  length_of_mem_greedyParityRowsAt countSys hinit (3 * n) hr

theorem length_encList_greedyParityRowsAt (countSys : List (List Bool) → ℕ)
    (m P : ℕ) (initRows : List (List Bool)) (i : ℕ) :
    (encList encBits (greedyParityRowsAt countSys m P initRows i)).length =
      (encList encBits initRows).length + i * (2 * m + 1) := by
  induction i with
  | zero => simp only [greedyParityRowsAt_zero, Nat.zero_mul, Nat.add_zero]
  | succ i ih =>
    rw [greedyParityRowsAt_succ, encList_append, List.length_append, ih, encList_cons, encList_nil,
      List.append_nil, length_frame, encBits_apply, length_selectBestTestRow]; ring

/-- **Exact bridge from `greedyParityRows` to `CNF.numPassing_greedy`**
([OpenAI2026ETH], Lemma 6.2).
Under `hn : 1 ≤ Fintype.card V` and `hP : 1 ≤ P`, when `initRows` has row width `φ.length`,
`countSys` computes `numPassing φ.violations` on width-`φ.length` candidate row lists of length at
most `initRows.length + 3 * Fintype.card V` whose appended rows have weight `≤ P`, and `initRows`
satisfies Lemma 6.1's `φ.length ≤ P * weight (φ.violations σ)` bound, `3 * Fintype.card V` greedy
rounds yield `countSys finalRows = #{σ : V → Bool | φ.eval σ = true}`. Positivity is material:
for `V = Fin 0`, `φ = [[]]`, `P = 1`, `initRows = []`, and `countSys` given by `numPassing`, the
agreement and support conditions hold, yet `0` rounds leave count `1` while `#sat = 0`. -/
theorem countSys_greedyParityRows_eq_card_sat {V : Type*} [Fintype V] [DecidableEq V]
    (φ : CNF V) {P : ℕ} (hn : 1 ≤ Fintype.card V) (hP : 1 ≤ P)
    {countSys : List (List Bool) → ℕ} {initRows : List (List Bool)}
    (hinit_len : ∀ r ∈ initRows, r.length = φ.length)
    (hcount : ∀ rows, (∀ r ∈ rows, r.length = φ.length) →
      rows.length ≤ initRows.length + 3 * Fintype.card V →
      (∀ r ∈ rows, r ∈ initRows ∨ r.count true ≤ P) →
      countSys rows = numPassing φ.violations (rows.map (ofList φ.length)))
    (hinit : ∀ σ : V → Bool,
      PassesTests φ.violations (initRows.map (ofList φ.length)) σ →
        φ.eval σ = false → φ.length ≤ P * weight (φ.violations σ)) :
    countSys (greedyParityRows countSys (Fintype.card V) φ.length P initRows) =
      #{σ : V → Bool | φ.eval σ = true} := by
  let N := 3 * Fintype.card V
  let rowsAt (i : ℕ) := greedyParityRowsAt countSys φ.length P initRows i
  change countSys (rowsAt N) = _
  rw [hcount (rowsAt N) (fun _ hr => length_of_mem_greedyParityRows countSys hinit_len hr)
    (by simp only [rowsAt, length_greedyParityRowsAt, N, le_rfl])
    (fun _ hr => (mem_greedyParityRowsAt countSys hr).imp_right And.right)]
  rcases Nat.eq_zero_or_pos φ.length with hm0 | hmpos
  · have hsat : ∀ σ : V → Bool, φ.eval σ = true := fun σ => by
      rw [← CNF.violations_eq_zero_iff]; funext e; exact Fin.elim0 (hm0 ▸ e)
    rw [numPassing]; congr 1; ext σ
    simp only [mem_filter, mem_univ, true_and, hsat σ, iff_true]
    intro h _; rw [(CNF.violations_eq_zero_iff φ σ).mpr (hsat σ), dotProduct_zero]; rfl
  · have hcand_pos : 0 < candidateTupleCount φ.length P := Nat.pow_pos (by omega)
    choose γExec hγExec using fun i => exists_fin_selectBestTestRow countSys (rowsAt i) hcand_pos
    have hEx (B : List (Fin φ.length → Bool)) := Finset.exists_min_image
      (Finset.univ : Finset (Fin P → Fin φ.length × Bool))
      (fun g => numPassing φ.violations (B ++ [testRow g]))
      ⟨fun _ => (⟨0, hmpos⟩, false), Finset.mem_univ _⟩
    choose optGamma _ hopt_le using hEx
    let tailA : ℕ → List (Fin φ.length → Bool) :=
      Nat.rec ((rowsAt N).map (ofList φ.length)) fun _ acc => acc ++ [testRow (optGamma acc)]
    let A (i : ℕ) : List (Fin φ.length → Bool) :=
      if i ≤ N then (rowsAt i).map (ofList φ.length) else tailA (i - N)
    let γ (i : ℕ) : Fin P → Fin φ.length × Bool := if i < N then γExec i else optGamma (A i)
    have hA_ge {i : ℕ} (hi : N ≤ i) : A i = tailA (i - N) := by
      rcases eq_or_lt_of_le hi with rfl | hlt
      · simp only [A, le_rfl, ↓reduceIte, Nat.sub_self, tailA]; rfl
      · simp only [A, Nat.not_le_of_gt hlt, ↓reduceIte]
    have hA (i : ℕ) : A (i + 1) = A i ++ [testRow (γ i)] := by
      by_cases hi : i < N
      · simp only [A, γ, hi, Nat.succ_le_of_lt hi, Nat.le_of_lt hi, ↓reduceIte, rowsAt,
          greedyParityRowsAt_succ, List.map_append, List.map_singleton, hγExec i, ofList_ofFn]
      · have hsub : i + 1 - N = (i - N) + 1 := by omega
        rw [hA_ge (by omega : N ≤ i + 1), hsub]
        change tailA (i - N) ++ [testRow (optGamma (tailA (i - N)))] = _
        simp only [γ, hi, ↓reduceIte, hA_ge (Nat.le_of_not_lt hi)]
    have hγ_min (i : ℕ) (γ' : Fin P → Fin φ.length × Bool) :
        numPassing φ.violations (A i ++ [testRow (γ i)]) ≤
          numPassing φ.violations (A i ++ [testRow γ']) := by
      by_cases hi : i < N
      · have hcand_ok (c : List Bool) (hc_len : c.length = φ.length) (hc_wt : c.count true ≤ P) :
            countSys (rowsAt i ++ [c]) =
              numPassing φ.violations ((rowsAt i ++ [c]).map (ofList φ.length)) :=
          hcount _ (fun r hr => by
              rw [List.mem_append, List.mem_singleton] at hr
              exact hr.elim (length_of_mem_greedyParityRowsAt countSys hinit_len i)
                (fun h => h ▸ hc_len))
            (by simp only [rowsAt, List.length_append, List.length_singleton,
                length_greedyParityRowsAt]; omega)
            (fun r hr => by
              rw [List.mem_append, List.mem_singleton] at hr
              exact hr.elim (fun h => (mem_greedyParityRowsAt countSys h).imp_right And.right)
                (fun h => Or.inr (h ▸ hc_wt)))
        have hmin := countSys_selectBestTestRow_le countSys (rowsAt i) γ'
        have hwt' : (List.ofFn (testRow γ')).count true ≤ P := by
          rw [← materializeTestRow_ofFn]
          simpa only [List.length_ofFn] using
            count_true_materializeTestRow_le φ.length (List.ofFn fun r => ((γ' r).1.val, (γ' r).2))
        rw [hcand_ok _ (length_selectBestTestRow _ _ _ _) (count_true_selectBestTestRow_le _ _ _ _),
          hcand_ok _ List.length_ofFn hwt'] at hmin
        simpa only [A, γ, hi, Nat.le_of_lt hi, ↓reduceIte, List.map_append, List.map_singleton,
          hγExec i, ofList_ofFn] using hmin
      · simp only [γ, hi, ↓reduceIte]; exact hopt_le (A i) γ' (Finset.mem_univ _)
    simpa only [A, N, le_rfl, ↓reduceIte] using CNF.numPassing_greedy φ hn hP A
      (by simpa only [A, Nat.zero_le, ↓reduceIte, rowsAt, greedyParityRowsAt_zero] using hinit)
      γ hA hγ_min

/-- Concrete `Fin n` specialization of Lemma 6.2: under `hn : 1 ≤ n` and `hP : 1 ≤ P`, `3 * n`
greedy rounds yield `N(A) = #F` and `D(A) = 0`. -/
theorem numPassing_greedyParityRows_fin {n P : ℕ} (φ : CNF (Fin n))
    (hn : 1 ≤ n) (hP : 1 ≤ P) (initRows : List (List Bool))
    (hinit_len : ∀ r ∈ initRows, r.length = φ.length)
    (hinit : ∀ σ : Fin n → Bool,
      PassesTests φ.violations (initRows.map (ofList φ.length)) σ →
        φ.eval σ = false → φ.length ≤ P * weight (φ.violations σ)) :
    let countSys := fun rows : List (List Bool) =>
      numPassing φ.violations (rows.map (ofList φ.length))
    let finalRows := greedyParityRows countSys n φ.length P initRows
    countSys finalRows = #{σ : Fin n → Bool | φ.eval σ = true} ∧
      #{σ : Fin n → Bool |
        PassesTests φ.violations (finalRows.map (ofList φ.length)) σ ∧ φ.eval σ = false} = 0 := by
  dsimp only
  set countSys := fun rows : List (List Bool) =>
    numPassing φ.violations (rows.map (ofList φ.length))
  set finalRows := greedyParityRows countSys n φ.length P initRows
  have hmain : countSys finalRows = #{σ : Fin n → Bool | φ.eval σ = true} := by
    simpa only [Fintype.card_fin] using countSys_greedyParityRows_eq_card_sat (V := Fin n) φ
      (by simpa only [Fintype.card_fin] using hn) hP hinit_len
      (countSys := countSys) (fun _ _ _ _ => rfl) hinit
  have hdecomp := numPassing_eq φ.violations (finalRows.map (ofList φ.length))
  simp only [CNF.violations_eq_zero_iff, ne_eq, Bool.not_eq_true] at hdecomp
  change countSys finalRows = _ at hdecomp
  exact ⟨hmain, by omega⟩

/-! ### Encodings for native `IndexFold` certificates -/

/-- Binary encoding of the live streaming accumulator `((m, P), (rows, bestOpt))`. -/
def encSelectBestAcc : SelectBestAcc ↪ List Bool :=
  encPair (encPair encUnary encUnary)
    (encPair (encList encBits) (encOption (encPair encBits encNat)))

/-- Input encoding for `selectBestTestRow` (and outer-loop state): unary `(m, P)` and `rows`. -/
def encSelectBestIn : (ℕ × ℕ × List (List Bool)) ↪ List Bool :=
  encPair encUnary (encPair encUnary (encList encBits))

/-- Input encoding for `greedyParityRows`: unary `(n, m, P)` and framed bit-rows `initRows`. -/
def encGreedyIn : (ℕ × ℕ × ℕ × List (List Bool)) ↪ List Bool :=
  encPair encUnary encSelectBestIn

end Cslib.Logic.PL.CNF

end

public section

namespace Cslib.Logic.PL.CNF

open Finset Cslib.BitString Cslib.GenericRAM Turing.MultiTapeTM

/-! ### Native `IndexFold` certificates and `ComputableInO` / `ComputableInPolySpace` bounds -/

/-- Candidate test row decoded and materialized from an `IndexFold` state `(j, acc)`. -/
@[expose] def candRowOfState (s : ℕ × SelectBestAcc) : List Bool :=
  materializeTestRow s.2.1.1 (decodeTestTuple s.2.1.1 s.2.1.2 s.1)

theorem computableInPolyTime_candRowOfState :
    ComputableInPolyTime candRowOfState (encPair encNat encSelectBestAcc) encBits := by
  unfold candRowOfState encSelectBestAcc
  let encRest := encPair (encList encBits) (encOption (encPair encBits encNat))
  let encAcc := encPair (encPair encUnary encUnary) encRest
  have hj := ComputableInPolyTime.fst encNat encAcc
  have hmP := (ComputableInPolyTime.fst (encPair encUnary encUnary) encRest).comp
    (ComputableInPolyTime.snd encNat encAcc)
  have hm := (ComputableInPolyTime.fst encUnary encUnary).comp hmP
  have hP := (ComputableInPolyTime.snd encUnary encUnary).comp hmP
  exact computableInPolyTime_materializeTestRow' hm (computableInPolyTime_decodeTestTuple' hm hP hj)

/-- Existing parity-test rows extended with the candidate row at `IndexFold` state `s`. -/
@[expose] def augCandidateRows (s : ℕ × SelectBestAcc) : List (List Bool) :=
  s.2.2.1 ++ [candRowOfState s]

theorem computableInPolyTime_augCandidateRows :
    ComputableInPolyTime augCandidateRows (encPair encNat encSelectBestAcc) (encList encBits) := by
  unfold augCandidateRows
  have hcand := computableInPolyTime_candRowOfState
  unfold encSelectBestAcc at hcand ⊢
  let encRest := encPair (encList encBits) (encOption (encPair encBits encNat))
  have hrows := (ComputableInPolyTime.fst (encList encBits) _).comp
    ((ComputableInPolyTime.snd (encPair encUnary encUnary) encRest).comp
      (ComputableInPolyTime.snd encNat (encPair (encPair encUnary encUnary) encRest)))
  exact (ComputableInPolyTime.snoc encBits).comp (hrows.prod hcand)

/-- Update `SelectBestAcc` after evaluating the candidate score `p.2` at `IndexFold` state `p.1`. -/
@[expose] def finishSelectBestStep (p : (ℕ × SelectBestAcc) × ℕ) : SelectBestAcc :=
  let candRow := candRowOfState p.1
  let nextBest := p.1.2.2.2.elim (some (candRow, p.2)) fun best =>
    if decide (p.2 < best.2) then some (candRow, p.2) else some best
  (p.1.2.1, (p.1.2.2.1, nextBest))

theorem computableInPolyTime_finishSelectBestStep :
    ComputableInPolyTime finishSelectBestStep
      (encPair (encPair encNat encSelectBestAcc) encNat) encSelectBestAcc := by
  unfold finishSelectBestStep
  have hcand0 := computableInPolyTime_candRowOfState
  unfold encSelectBestAcc at hcand0 ⊢
  let eBest := encPair encBits encNat; let encRest := encPair (encList encBits) (encOption eBest)
  let encAcc := encPair (encPair encUnary encUnary) encRest
  let encIn := encPair (encPair encNat encAcc) encNat
  have hs := ComputableInPolyTime.fst (encPair encNat encAcc) encNat
  have hval := ComputableInPolyTime.snd (encPair encNat encAcc) encNat
  have hacc := (ComputableInPolyTime.snd encNat encAcc).comp hs
  have hmP := (ComputableInPolyTime.fst (encPair encUnary encUnary) encRest).comp hacc
  have hrest := (ComputableInPolyTime.snd (encPair encUnary encUnary) encRest).comp hacc
  have hrows := (ComputableInPolyTime.fst (encList encBits) (encOption eBest)).comp hrest
  have hbestOpt := (ComputableInPolyTime.snd (encList encBits) (encOption eBest)).comp hrest
  have hsomeCand := (ComputableInPolyTime.optionSome eBest).comp ((hcand0.comp hs).prod hval)
  refine hmP.prod (hrows.prod
    (ComputableInPolyTime.optionElimWithInput hbestOpt hsomeCand ?_))
  have hq_in := ComputableInPolyTime.fst encIn eBest
  have hq_best := ComputableInPolyTime.snd encIn eBest
  exact (ComputableInPolyTime.binary_lt' (hval.comp hq_in)
    ((ComputableInPolyTime.snd encBits encNat).comp hq_best)).ite (hsomeCand.comp hq_in)
      ((ComputableInPolyTime.optionSome eBest).comp hq_best)

/-- Native callback certificate for one candidate step `selectBestStep countSys`. -/
noncomputable def selectBestStepCertificate {countSys : List (List Bool) → ℕ}
    (cCount : NativeCertificate countSys (encList encBits) encNat) :
    NativeCertificate (selectBestStep countSys)
      (encPair encNat encSelectBestAcc) encSelectBestAcc :=
  let cId : NativeCertificate id (encPair encNat encSelectBestAcc)
      (encPair encNat encSelectBestAcc) :=
    NativeCertificate.linear (ComputableInO.of_linear (.of_eq fun _ => rfl))
  ((NativeCertificate.ofPolyTime computableInPolyTime_finishSelectBestStep).comp
    (cId.prod (cCount.comp (NativeCertificate.ofPolyTime
      computableInPolyTime_augCandidateRows)))).congr fun _ => rfl

private def selectBestCountIn (a : ℕ × ℕ × List (List Bool)) : ℕ := candidateTupleCount a.1 a.2.1

private theorem computableInPolyTime_selectBestCountIn :
    ComputableInPolyTime selectBestCountIn encSelectBestIn encNat := by
  unfold selectBestCountIn encSelectBestIn
  exact computableInPolyTime_candidateTupleCount' (by fun_prop) (by fun_prop)

private def selectBestInitIn (a : ℕ × ℕ × List (List Bool)) : SelectBestAcc :=
  ((a.1, a.2.1), (a.2.2, none))

private theorem computableInPolyTime_selectBestInitIn :
    ComputableInPolyTime selectBestInitIn encSelectBestIn encSelectBestAcc := by
  unfold selectBestInitIn encSelectBestIn encSelectBestAcc; fun_prop

private def extractSelectBestRow (r : ℕ × SelectBestAcc) : List Bool :=
  r.2.2.2.elim (List.replicate r.2.1.1 false) Prod.fst

private theorem computableInPolyTime_extractSelectBestRow :
    ComputableInPolyTime extractSelectBestRow (encPair encNat encSelectBestAcc) encBits := by
  unfold extractSelectBestRow encSelectBestAcc
  let eBest := encPair encBits encNat; let encRest := encPair (encList encBits) (encOption eBest)
  let encAcc := encPair (encPair encUnary encUnary) encRest
  have hacc := ComputableInPolyTime.snd encNat encAcc
  have hm := (ComputableInPolyTime.fst encUnary encUnary).comp
    ((ComputableInPolyTime.fst (encPair encUnary encUnary) encRest).comp hacc)
  have hopt := (ComputableInPolyTime.snd (encList encBits) (encOption eBest)).comp
    ((ComputableInPolyTime.snd (encPair encUnary encUnary) encRest).comp hacc)
  exact ComputableInPolyTime.optionElimWithInput hopt
    ((ComputableInPolyTime.bitsReplicate false).comp hm)
    ((ComputableInPolyTime.fst encBits encNat).comp
      (ComputableInPolyTime.snd (encPair encNat encAcc) eBest))

/-- Native streaming machine certificate for `selectBestTestRow` via `IndexFold.certificate`, for a
fixed counter `(countSys, cCount)` supplied before runtime inputs `(m, P, rows)`. -/
noncomputable def selectBestTestRowCertificate {countSys : List (List Bool) → ℕ}
    (cCount : NativeCertificate countSys (encList encBits) encNat) :
    NativeCertificate (fun a : ℕ × ℕ × List (List Bool) =>
        selectBestTestRow countSys a.1 a.2.1 a.2.2) encSelectBestIn encBits :=
  let cLoop := IndexFold.certificate
    (NativeCertificate.ofPolyTime computableInPolyTime_selectBestCountIn)
    (NativeCertificate.ofPolyTime computableInPolyTime_selectBestInitIn)
    (selectBestStepCertificate cCount)
  ((NativeCertificate.ofPolyTime computableInPolyTime_extractSelectBestRow).comp cLoop).congr
    fun a => by
      have hp := (run_selectBestStep_params countSys a.1 a.2.1
        (candidateTupleCount a.1 a.2.1) a.2.2).1
      simp only [Function.comp_apply, extractSelectBestRow, selectBestCountIn, selectBestInitIn,
        selectBestTestRow, show (IndexFold.run (selectBestStep countSys)
          (candidateTupleCount a.1 a.2.1) ((a.1, a.2.1), (a.2.2, none))).2.1.1 = a.1 by rw [hp]]

private def appendSelectedRow (p : (ℕ × ℕ × List (List Bool)) × List Bool) :
    ℕ × ℕ × List (List Bool) := (p.1.1, p.1.2.1, p.1.2.2 ++ [p.2])

private theorem computableInPolyTime_appendSelectedRow :
    ComputableInPolyTime appendSelectedRow (encPair encSelectBestIn encBits) encSelectBestIn := by
  unfold appendSelectedRow encSelectBestIn
  let encTail := encPair encUnary (encList encBits)
  let encS := encPair encUnary encTail
  have hs := ComputableInPolyTime.fst encS encBits
  have hrow := ComputableInPolyTime.snd encS encBits
  have hm := (ComputableInPolyTime.fst encUnary encTail).comp hs
  have htail := (ComputableInPolyTime.snd encUnary encTail).comp hs
  exact hm.prod (((ComputableInPolyTime.fst encUnary (encList encBits)).comp htail).prod
    ((ComputableInPolyTime.snoc encBits).comp
      (((ComputableInPolyTime.snd encUnary (encList encBits)).comp htail).prod hrow)))

private def greedyOuterStep (countSys : List (List Bool) → ℕ)
    (s : ℕ × ℕ × List (List Bool)) : ℕ × ℕ × List (List Bool) :=
  (s.1, s.2.1, s.2.2 ++ [selectBestTestRow countSys s.1 s.2.1 s.2.2])

private theorem greedyOuterStep_iterate (countSys : List (List Bool) → ℕ)
    (m P k : ℕ) (initRows : List (List Bool)) :
    (greedyOuterStep countSys)^[k] (m, P, initRows) =
      (m, P, greedyParityRowsAt countSys m P initRows k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, greedyOuterStep, greedyParityRowsAt_succ]

private noncomputable def greedyOuterStepCertificate {countSys : List (List Bool) → ℕ}
    (cCount : NativeCertificate countSys (encList encBits) encNat) :
    NativeCertificate (greedyOuterStep countSys) encSelectBestIn encSelectBestIn :=
  let cId : NativeCertificate id encSelectBestIn encSelectBestIn :=
    NativeCertificate.linear (ComputableInO.of_linear (.of_eq fun _ => rfl))
  ((NativeCertificate.ofPolyTime computableInPolyTime_appendSelectedRow).comp
    (cId.prod (selectBestTestRowCertificate cCount))).congr fun _ => rfl

private def greedyRoundCountIn (a : ℕ × ℕ × ℕ × List (List Bool)) : ℕ := 3 * a.1

private theorem computableInPolyTime_greedyRoundCountIn :
    ComputableInPolyTime greedyRoundCountIn encGreedyIn encNat := by
  unfold greedyRoundCountIn encGreedyIn
  exact ComputableInPolyTime.unary_to_binary.comp (by fun_prop)

/-- Native machine certificate for the `3 * n`-round `greedyParityRows` procedure for a fixed
counter `(countSys, cCount)`.

Here `countSys` and `cCount` are fixed before the runtime inputs `(n, m, P, rows)` encoded by
`encGreedyIn`; neither the original CNF nor an arbitrary encoded context is an input to this
machine, and choosing a separate `countSys` per `φ` allows a different machine and polynomial per
`φ`. Uniform composition with a variable-CNF Theorem 2.2 counter requires a captured-context
certificate interface (such as a counter on `(context, rows)` retaining and charging `context`
throughout the loop). -/
noncomputable def greedyParityRowsCertificate {countSys : List (List Bool) → ℕ}
    (cCount : NativeCertificate countSys (encList encBits) encNat) :
    NativeCertificate (fun a : ℕ × ℕ × ℕ × List (List Bool) =>
        greedyParityRows countSys a.1 a.2.1 a.2.2.1 a.2.2.2) encGreedyIn (encList encBits) :=
  (NativeCertificate.snd (NativeCertificate.snd (NativeCertificate.iterate
    (NativeCertificate.ofPolyTime computableInPolyTime_greedyRoundCountIn)
    (NativeCertificate.payload encUnary encSelectBestIn)
    (greedyOuterStepCertificate cCount)))).congr fun ⟨_, _, _, _⟩ => by
      simp only [greedyRoundCountIn, greedyOuterStep_iterate]; rfl

/-! ### Live-state length bounds and `ComputableInO` / `ComputableInPolySpace` theorems -/

/-- Live accumulator length bound during `IndexFold.run (selectBestStep countSys)`, independent of
the number `k` of visited candidates. -/
theorem length_encSelectBestAcc_run_le (countSys : List (List Bool) → ℕ)
    (m P k : ℕ) (rows : List (List Bool)) {V : ℕ}
    (hV : ∀ j < k,
      (encNat (countSys (rows ++ [materializeTestRow m (decodeTestTuple m P j)]))).length ≤ V) :
    (encSelectBestAcc
      (IndexFold.run (selectBestStep countSys) k ((m, P), (rows, none))).2).length ≤
      6 * m + 2 * P + 2 * (encList encBits rows).length + V + 6 := by
  have hparams := run_selectBestStep_params countSys m P k rows
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simp only [IndexFold.run_zero, encSelectBestAcc, length_encPair, encUnary_apply,
      List.length_replicate, encOption_none, List.length_nil]; omega
  · obtain ⟨jStar, hjStar_lt, hopt, _, _⟩ := run_selectBestStep_spec countSys m P rows hkpos
    have hv := hV jStar hjStar_lt
    rcases r : IndexFold.run (selectBestStep countSys) k ((m, P), (rows, none)) with ⟨_, _, _, _⟩
    simp only [r] at hparams hopt ⊢; rcases hparams with ⟨rfl, rfl⟩; subst hopt
    simp only [encSelectBestAcc, length_encPair, encUnary_apply, List.length_replicate,
      encOption_some, List.length_cons, encBits_apply, length_materializeTestRow]; omega

private theorem selectBestIn_le (m P : ℕ) (rows : List (List Bool)) :
    m ≤ (encSelectBestIn (m, P, rows)).length ∧ P ≤ (encSelectBestIn (m, P, rows)).length ∧
      (encList encBits rows).length ≤ (encSelectBestIn (m, P, rows)).length := by
  simp only [encSelectBestIn, length_encPair, encUnary_apply, List.length_replicate]
  exact ⟨by omega, by omega, by omega⟩

private theorem selectBestTestRowCertificate_bounds {countSys : List (List Bool) → ℕ}
    (cCount : NativeCertificate countSys (encList encBits) encNat)
    (hSpace : PolyBounded (fun r => (encList encBits r).length) cCount.space) :
    ∃ poly : ℕ → ℕ, Cslib.PolynomiallyBounded poly ∧ Monotone poly ∧
      (∀ a : ℕ × ℕ × List (List Bool),
        (∀ R : ℕ,
          (∀ j ≤ candidateTupleCount a.1 a.2.1,
            cCount.time (a.2.2 ++ [materializeTestRow a.1 (decodeTestTuple a.1 a.2.1 j)]) ≤ R) →
          (selectBestTestRowCertificate cCount).time a ≤
            (candidateTupleCount a.1 a.2.1 + 1) * (poly (encSelectBestIn a).length + R)) ∧
        (selectBestTestRowCertificate cCount).space a ≤ poly (encSelectBestIn a).length) := by
  obtain ⟨cOut, _, hOutLen⟩ := cCount.computes
  obtain ⟨pSp, hpSp, hmSp, hSp⟩ := exists_mono_poly hSpace
  obtain ⟨pCn, hpCn, _, hCn⟩ := exists_mono_poly_cert computableInPolyTime_selectBestCountIn
  obtain ⟨pCi, hpCi, _, hCi⟩ := exists_mono_poly_cert computableInPolyTime_selectBestInitIn
  obtain ⟨pAug, hpAug, hmAug, hAug⟩ := exists_mono_poly_cert computableInPolyTime_augCandidateRows
  obtain ⟨pFin, hpFin, hmFin, hFin⟩ :=
    exists_mono_poly_cert computableInPolyTime_finishSelectBestStep
  obtain ⟨pExt, hpExt, hmExt, hExt⟩ :=
    exists_mono_poly_cert computableInPolyTime_extractSelectBestRow
  let qSys (L : ℕ) := pSp (3 * L + 1); let vBound (L : ℕ) := cOut * (qSys L + 1)
  let bAcc (L : ℕ) := 10 * L + vBound L + 6; let lIdx (L : ℕ) := 2 * L * L + 1
  let bFull (L : ℕ) := 2 * lIdx L + 1 + bAcc L; let finIn (L : ℕ) := 2 * bFull L + 1 + vBound L
  let cbOver (L : ℕ) := bFull L + pAug (bFull L) + qSys L + pFin (finIn L)
  let roundOver (L : ℕ) := 2 * bFull L + 2 * (lIdx L + 1) ^ 2 + cbOver L
  let initExt (L : ℕ) := pCn L + L + pCi L + pExt (bFull L) + lIdx L
  have hraw : Cslib.PolynomiallyBounded (fun L => initExt L + roundOver L) := by
    dsimp only [initExt, roundOver, cbOver, finIn, bFull, lIdx, bAcc, vBound, qSys]; fun_prop
  obtain ⟨poly, hpoly, hmpoly, hle_poly⟩ := exists_mono_poly (.of_polynomiallyBounded id hraw)
  refine ⟨poly, hpoly, hmpoly, fun ⟨m, P, rows⟩ => ?_⟩; dsimp only
  obtain ⟨hm_le, hP_le, hrows_le⟩ := selectBestIn_le m P rows
  set L := (encSelectBestIn (m, P, rows)).length; set K := candidateTupleCount m P
  have hpolyL : initExt L + roundOver L ≤ poly L := hle_poly L
  let candRow (j : ℕ) := materializeTestRow m (decodeTestTuple m P j)
  let runAt (j : ℕ) := IndexFold.run (selectBestStep countSys) j ((m, P), (rows, none))
  have hq_j (j : ℕ) : cCount.space (rows ++ [candRow j]) ≤ qSys L :=
    (hSp _).trans (hmSp (by
      simp only [candRow, encList_append, List.length_append, encList_cons, encList_nil,
        List.append_nil, length_frame, encBits_apply, length_materializeTestRow]; omega))
  have hv_j (j : ℕ) : (encNat (countSys (rows ++ [candRow j]))).length ≤ vBound L :=
    (hOutLen _).trans (Nat.mul_le_mul_left cOut (Nat.add_le_add_right (hq_j j) 1))
  have hlIdx : (encNat K).length ≤ lIdx L := by
    refine (length_encNat_candidateTupleCount_le m P).trans ?_
    have := Nat.mul_le_mul hP_le (show 2 * m ≤ 2 * L by omega); dsimp only [lIdx]; nlinarith
  have hbAcc (j : ℕ) : (encSelectBestAcc (runAt j).2).length ≤ bAcc L :=
    (length_encSelectBestAcc_run_le countSys m P j rows (fun i _ => hv_j i)).trans
      (by dsimp only [bAcc]; omega)
  have hbFull (j : ℕ) (hj : j ≤ K) : (encPair encNat encSelectBestAcc (runAt j)).length ≤ bFull L :=
    (IndexFold.length_run_le (selectBestStep countSys) ((m, P), (rows, none))
      hj (hbAcc j)).trans (by dsimp only [bFull]; omega)
  let cb := selectBestStepCertificate cCount; let rstep := IndexFold.roundCertificate cb
  let initPair : ℕ × SelectBestAcc := (0, ((m, P), (rows, none)))
  let cn := NativeCertificate.ofPolyTime computableInPolyTime_selectBestCountIn
  let ci := NativeCertificate.ofPolyTime computableInPolyTime_selectBestInitIn
  let cExt := NativeCertificate.ofPolyTime computableInPolyTime_extractSelectBestRow
  set M := NativeCertificate.maxStateLength (encPair encNat encSelectBestAcc)
    (IndexFold.step (selectBestStep countSys)) K initPair
  set RT := NativeCertificate.maxRoundTime rstep K initPair
  set RS := NativeCertificate.maxRoundSpace rstep K initPair
  have hmaxS : M ≤ bFull L := NativeCertificate.maxStateLength_le _ _ _ _ hbFull
  have hcb_bounds (j : ℕ) (hj : j ≤ K) :
      cb.time (runAt j) ≤ cbOver L + cCount.time (rows ++ [candRow j]) ∧
        cb.space (runAt j) ≤ cbOver L := by
    let st := runAt j
    have hparams : st.2.1 = (m, P) ∧ st.2.2.1 = rows :=
      run_selectBestStep_params countSys m P j rows
    have hidx : st.1 = j := IndexFold.run_index (selectBestStep countSys) j ((m, P), (rows, none))
    have haug_st : augCandidateRows st = rows ++ [candRow j] := by
      simp only [augCandidateRows, candRowOfState, candRow]
      rw [hparams.2, hidx, show st.2.1.1 = m by rw [hparams.1], show st.2.1.2 = P by rw [hparams.1]]
    have hst_len : (encPair encNat encSelectBestAcc st).length ≤ bFull L := hbFull j hj
    have hfin_len : (encPair (encPair encNat encSelectBestAcc) encNat
        (st, countSys (augCandidateRows st))).length ≤ finIn L := by
      rw [length_encPair, haug_st]; have := hv_j j; dsimp only [finIn]; omega
    have haugT := (hAug st).1.trans (hmAug hst_len); have haugS := (hAug st).2.trans (hmAug hst_len)
    have hfinT := (hFin (st, countSys (augCandidateRows st))).1.trans (hmFin hfin_len)
    have hfinS := (hFin (st, countSys (augCandidateRows st))).2.trans (hmFin hfin_len)
    have hcntT : cCount.time (augCandidateRows st) = cCount.time (rows ++ [candRow j]) :=
      congrArg cCount.time haug_st
    have hcntS : cCount.space (augCandidateRows st) ≤ qSys L := haug_st ▸ hq_j j
    refine ⟨?_, ?_⟩
    · change ((encPair encNat encSelectBestAcc st).length +
          ((NativeCertificate.ofPolyTime computableInPolyTime_augCandidateRows).time st +
            cCount.time (augCandidateRows st))) +
        (NativeCertificate.ofPolyTime computableInPolyTime_finishSelectBestStep).time
          (st, countSys (augCandidateRows st)) ≤ _; dsimp only [cbOver]; omega
    · change ((encPair encNat encSelectBestAcc st).length +
          ((NativeCertificate.ofPolyTime computableInPolyTime_augCandidateRows).space st +
            cCount.space (augCandidateRows st))) +
        (NativeCertificate.ofPolyTime computableInPolyTime_finishSelectBestStep).space
          (st, countSys (augCandidateRows st)) ≤ _; dsimp only [cbOver]; omega
  have hcn_a : cn.time (m, P, rows) ≤ pCn L ∧ cn.space (m, P, rows) ≤ pCn L := hCn (m, P, rows)
  have hci_a : ci.time (m, P, rows) ≤ pCi L ∧ ci.space (m, P, rows) ≤ pCi L := hCi (m, P, rows)
  have hextT : cExt.time (runAt K) ≤ pExt (bFull L) :=
    (hExt (runAt K)).1.trans (hmExt (hbFull K le_rfl))
  have hextS : cExt.space (runAt K) ≤ pExt (bFull L) :=
    (hExt (runAt K)).2.trans (hmExt (hbFull K le_rfl))
  refine ⟨fun R hR => ?_, ?_⟩
  · have hmaxRT : RT ≤ bFull L + (lIdx L + 1) ^ 2 + cbOver L + R := by
      refine NativeCertificate.maxRoundTime_le _ _ _ fun j hj => ?_
      have hst_len := hbFull j hj
      have hj_len : (encNat (runAt j).1).length ≤ lIdx L := by
        rw [IndexFold.run_index]
        have hm : (encNat j).length ≤ (encNat K).length := by
          simpa only [encNat_apply, Nat.size_eq_bits_len] using Nat.size_le_size hj
        exact hm.trans hlIdx
      have hsq : ((encNat (runAt j).1).length + 1) ^ 2 ≤ (lIdx L + 1) ^ 2 :=
        Nat.pow_le_pow_left (by omega) 2
      have hcbT := (hcb_bounds j hj).1
      have hRJ : cCount.time (rows ++ [candRow j]) ≤ R := hR j hj
      change (encPair encNat encSelectBestAcc (runAt j)).length +
        ((encNat (runAt j).1).length + 1) ^ 2 + cb.time (runAt j) ≤ _; omega
    have hsqN : ((encNat K).length + 1) ^ 2 ≤ (lIdx L + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hround_sum : RT + M + ((encNat K).length + 1) ^ 2 ≤ roundOver L + R := by
      dsimp only [roundOver]; omega
    calc (selectBestTestRowCertificate cCount).time (m, P, rows)
        = cn.time (m, P, rows) + (L + ci.time (m, P, rows)) +
            (K + 1) * (RT + M + ((encNat K).length + 1) ^ 2) + cExt.time (runAt K) := rfl
      _ ≤ initExt L + (K + 1) * (roundOver L + R) := by
            have h1 : cn.time (m, P, rows) + (L + ci.time (m, P, rows)) + cExt.time (runAt K) ≤
              initExt L := by dsimp only [initExt]; omega
            have h2 := Nat.mul_le_mul_left (K + 1) hround_sum; omega
      _ ≤ (K + 1) * initExt L + (K + 1) * (roundOver L + R) :=
            Nat.add_le_add_right (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)) _
      _ = (K + 1) * (initExt L + roundOver L + R) := by ring
      _ ≤ (K + 1) * (poly L + R) := Nat.mul_le_mul_left _ (by omega)
  · have hmaxRS : RS ≤ bFull L + (lIdx L + 1) + cbOver L := by
      refine NativeCertificate.maxRoundSpace_le _ _ _ fun j hj => ?_
      have hst_len := hbFull j hj
      have hj_len : (encNat (runAt j).1).length ≤ lIdx L := by
        rw [IndexFold.run_index]
        have hm : (encNat j).length ≤ (encNat K).length := by
          simpa only [encNat_apply, Nat.size_eq_bits_len] using Nat.size_le_size hj
        exact hm.trans hlIdx
      have hcbS := (hcb_bounds j hj).2
      change (encPair encNat encSelectBestAcc (runAt j)).length +
        ((encNat (runAt j).1).length + 1) + cb.space (runAt j) ≤ _; omega
    have hlin_sq : lIdx L + 1 ≤ 2 * (lIdx L + 1) ^ 2 := by nlinarith
    calc (selectBestTestRowCertificate cCount).space (m, P, rows)
        = cn.space (m, P, rows) + (L + ci.space (m, P, rows)) + RS + M + (encNat K).length +
            cExt.space (runAt K) := rfl
      _ ≤ initExt L + roundOver L := by dsimp only [initExt, roundOver]; omega
      _ ≤ poly L := hpolyL

/-- **Fixed-counter per-round `ComputableInO` time and polynomial-workspace bound for
`selectBestTestRow`** (with `countSys` and `cCount` fixed before runtime inputs `(m, P, rows)`). -/
theorem computableInO_selectBestTestRow {countSys : List (List Bool) → ℕ}
    (cCount : NativeCertificate countSys (encList encBits) encNat)
    (hSpace : PolyBounded (fun r => (encList encBits r).length) cCount.space)
    (R : ℕ × ℕ × List (List Bool) → ℕ)
    (hR : ∀ a, ∀ j ≤ candidateTupleCount a.1 a.2.1,
      cCount.time (a.2.2 ++ [materializeTestRow a.1 (decodeTestTuple a.1 a.2.1 j)]) ≤ R a) :
    ∃ poly : ℕ → ℕ, Cslib.PolynomiallyBounded poly ∧
      ComputableInO
        (fun a : ℕ × ℕ × List (List Bool) => selectBestTestRow countSys a.1 a.2.1 a.2.2)
        encSelectBestIn encBits
        (fun a => (candidateTupleCount a.1 a.2.1 + 1) * (poly (encSelectBestIn a).length + R a))
        (fun a => poly (encSelectBestIn a).length) := by
  obtain ⟨poly, hpoly, _, hB⟩ := selectBestTestRowCertificate_bounds cCount hSpace
  exact ⟨poly, hpoly, (selectBestTestRowCertificate cCount).computes.mono_le
    (fun a => (hB a).1 (R a) (hR a)) (fun a => (hB a).2)⟩

private theorem greedyIn_le (n m P : ℕ) (rows : List (List Bool)) :
    n ≤ (encGreedyIn (n, m, P, rows)).length ∧ m ≤ (encGreedyIn (n, m, P, rows)).length ∧
      P ≤ (encGreedyIn (n, m, P, rows)).length ∧
      (encList encBits rows).length ≤ (encGreedyIn (n, m, P, rows)).length := by
  simp only [encGreedyIn, encSelectBestIn, length_encPair, encUnary_apply, List.length_replicate]
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- **Fixed-counter `3n`-round `ComputableInO` time and polynomial-workspace bound for
`greedyParityRows`.** For fixed `countSys` and `cCount` (supplied before runtime inputs
`(n, m, P, rows)`), runs in time `O((3 * n + 1) * ((2 * m) ^ P + 1) * (poly(|input|) + R))` and
polynomial workspace `O(poly(|input|))`, never storing `(2 * m) ^ P` lists or counts
([OpenAI2026ETH], §6.3, p. 43). -/
theorem computableInO_greedyParityRows {countSys : List (List Bool) → ℕ}
    (cCount : NativeCertificate countSys (encList encBits) encNat)
    (hSpace : PolyBounded (fun r => (encList encBits r).length) cCount.space)
    (R : ℕ × ℕ × ℕ × List (List Bool) → ℕ)
    (hR : ∀ a, ∀ i ≤ 3 * a.1, ∀ j ≤ candidateTupleCount a.2.1 a.2.2.1,
      cCount.time (greedyParityRowsAt countSys a.2.1 a.2.2.1 a.2.2.2 i ++
        [materializeTestRow a.2.1 (decodeTestTuple a.2.1 a.2.2.1 j)]) ≤ R a) :
    ∃ poly : ℕ → ℕ, Cslib.PolynomiallyBounded poly ∧
      ComputableInO
        (fun a : ℕ × ℕ × ℕ × List (List Bool) =>
          greedyParityRows countSys a.1 a.2.1 a.2.2.1 a.2.2.2)
        encGreedyIn (encList encBits)
        (fun a => (3 * a.1 + 1) * (candidateTupleCount a.2.1 a.2.2.1 + 1) *
          (poly (encGreedyIn a).length + R a))
        (fun a => poly (encGreedyIn a).length) := by
  obtain ⟨polySel, hpolySel, hmpolySel, hSelB⟩ := selectBestTestRowCertificate_bounds cCount hSpace
  obtain ⟨pCn, hpCn, _, hCn⟩ := exists_mono_poly_cert computableInPolyTime_greedyRoundCountIn
  obtain ⟨pApp, hpApp, hmApp, hApp⟩ := exists_mono_poly_cert computableInPolyTime_appendSelectedRow
  let bOuter (L : ℕ) := 6 * L * L + 8 * L + 2; let selDom (L : ℕ) := polySel (bOuter L)
  let bAppIn (L : ℕ) := 2 * bOuter L + 1 + L
  let outerFixed (L : ℕ) := 2 * bOuter L + pApp (bAppIn L) + (3 * L + 1) ^ 2
  let initOuter (L : ℕ) := pCn L + 4 * L; let poly (L : ℕ) := initOuter L + outerFixed L + selDom L
  have hpoly : Cslib.PolynomiallyBounded poly := by
    dsimp only [poly, initOuter, outerFixed, bAppIn, selDom, bOuter]; fun_prop
  have hboth : ∀ a : ℕ × ℕ × ℕ × List (List Bool),
      (greedyParityRowsCertificate cCount).time a ≤
        (3 * a.1 + 1) * (candidateTupleCount a.2.1 a.2.2.1 + 1) *
          (poly (encGreedyIn a).length + R a) ∧
      (greedyParityRowsCertificate cCount).space a ≤ poly (encGreedyIn a).length := by
    rintro ⟨n, m, P, rows₀⟩; dsimp only
    obtain ⟨hn_le, hm_le, hP_le, hrows0_le⟩ := greedyIn_le n m P rows₀
    set L := (encGreedyIn (n, m, P, rows₀)).length; set K := candidateTupleCount m P
    set R₀ := R (n, m, P, rows₀)
    have hbOuter (i : ℕ) (hi : i ≤ 3 * n) :
        (encSelectBestIn ((greedyOuterStep countSys)^[i] (m, P, rows₀))).length ≤ bOuter L := by
      rw [greedyOuterStep_iterate, encSelectBestIn, length_encPair, length_encPair,
        encUnary_apply, List.length_replicate, encUnary_apply, List.length_replicate,
        length_encList_greedyParityRowsAt]
      have hgrow : i * (2 * m + 1) ≤ (3 * L) * (2 * L + 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      have hxp : (3 * L) * (2 * L + 1) = 6 * L * L + 3 * L := by ring
      dsimp only [bOuter]; omega
    let cstep := greedyOuterStepCertificate cCount
    let cn := NativeCertificate.ofPolyTime computableInPolyTime_greedyRoundCountIn
    set MO := NativeCertificate.maxStateLength encSelectBestIn
      (greedyOuterStep countSys) (3 * n) (m, P, rows₀)
    set RTO := NativeCertificate.maxRoundTime cstep (3 * n) (m, P, rows₀)
    set RSO := NativeCertificate.maxRoundSpace cstep (3 * n) (m, P, rows₀)
    have hmaxS : MO ≤ bOuter L := NativeCertificate.maxStateLength_le _ _ _ _ hbOuter
    have hstep_b (i : ℕ) (hi : i ≤ 3 * n) :
        let st := (greedyOuterStep countSys)^[i] (m, P, rows₀)
        cstep.time st ≤ bOuter L + (K + 1) * (selDom L + R₀) + pApp (bAppIn L) ∧
          cstep.space st ≤ bOuter L + selDom L + pApp (bAppIn L) := by
      dsimp only; set st := (greedyOuterStep countSys)^[i] (m, P, rows₀)
      have hst_eq : st = (m, P, greedyParityRowsAt countSys m P rows₀ i) :=
        greedyOuterStep_iterate countSys m P i rows₀
      have hst_len : (encSelectBestIn st).length ≤ bOuter L := hbOuter i hi
      have hpoly_sel_le : polySel (encSelectBestIn st).length ≤ selDom L := hmpolySel hst_len
      have hsel_t : (selectBestTestRowCertificate cCount).time st ≤ (K + 1) * (selDom L + R₀) := by
        have h1 := (hSelB st).1 R₀ (by simpa only [hst_eq] using hR (n, m, P, rows₀) i hi)
        rw [show candidateTupleCount st.1 st.2.1 = K by simp only [hst_eq, K]] at h1
        exact h1.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hpoly_sel_le _))
      have hsel_s : (selectBestTestRowCertificate cCount).space st ≤ selDom L :=
        (hSelB st).2.trans hpoly_sel_le
      set selRow := selectBestTestRow countSys st.1 st.2.1 st.2.2
      have happ_in_len : (encPair encSelectBestIn encBits (st, selRow)).length ≤ bAppIn L := by
        rw [length_encPair]
        have hrow_len : (encBits selRow).length ≤ L := by
          simp only [selRow, hst_eq, encBits_apply, length_selectBestTestRow]; exact hm_le
        dsimp only [bAppIn]; omega
      have happ_t := (hApp (st, selRow)).1.trans (hmApp happ_in_len)
      have happ_s := (hApp (st, selRow)).2.trans (hmApp happ_in_len)
      refine ⟨?_, ?_⟩
      · change ((encSelectBestIn st).length + (selectBestTestRowCertificate cCount).time st) +
          (NativeCertificate.ofPolyTime computableInPolyTime_appendSelectedRow).time
            (st, selRow) ≤ _; omega
      · change ((encSelectBestIn st).length + (selectBestTestRowCertificate cCount).space st) +
          (NativeCertificate.ofPolyTime computableInPolyTime_appendSelectedRow).space
            (st, selRow) ≤ _; omega
    have h3n_len : (encNat (3 * n)).length ≤ 3 * L := by
      rw [encNat_apply, Nat.size_eq_bits_len]; exact (Nat.size_le_self (3 * n)).trans (by omega)
    have hcn_a : cn.time (n, m, P, rows₀) ≤ pCn L ∧ cn.space (n, m, P, rows₀) ≤ pCn L :=
      hCn (n, m, P, rows₀)
    refine ⟨?_, ?_⟩
    · have hmaxRT : RTO ≤ bOuter L + (K + 1) * (selDom L + R₀) + pApp (bAppIn L) :=
        NativeCertificate.maxRoundTime_le cstep (3 * n) (m, P, rows₀) fun i hi => (hstep_b i hi).1
      have h3n_sq : ((encNat (3 * n)).length + 1) ^ 2 ≤ (3 * L + 1) ^ 2 :=
        Nat.pow_le_pow_left (by omega) 2
      have hper : RTO + MO + ((encNat (3 * n)).length + 1) ^ 2 ≤
          (K + 1) * (outerFixed L + selDom L + R₀) :=
        calc RTO + MO + ((encNat (3 * n)).length + 1) ^ 2
            ≤ outerFixed L + (K + 1) * (selDom L + R₀) := by dsimp only [outerFixed]; omega
          _ ≤ (K + 1) * outerFixed L + (K + 1) * (selDom L + R₀) :=
                Nat.add_le_add_right (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)) _
          _ = (K + 1) * (outerFixed L + selDom L + R₀) := by ring
      calc (greedyParityRowsCertificate cCount).time (n, m, P, rows₀)
          = cn.time (n, m, P, rows₀) + L +
              (3 * n + 1) * (RTO + MO + ((encNat (3 * n)).length + 1) ^ 2) := rfl
        _ ≤ initOuter L + (3 * n + 1) * ((K + 1) * (outerFixed L + selDom L + R₀)) :=
              Nat.add_le_add (by dsimp only [initOuter]; omega) (Nat.mul_le_mul_left _ hper)
        _ = initOuter L + ((3 * n + 1) * (K + 1)) * (outerFixed L + selDom L + R₀) := by ring
        _ ≤ ((3 * n + 1) * (K + 1)) * initOuter L +
              ((3 * n + 1) * (K + 1)) * (outerFixed L + selDom L + R₀) :=
              Nat.add_le_add_right
                (Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))) _
        _ = (3 * n + 1) * (K + 1) * (poly L + R₀) := by dsimp only [poly]; ring
    · have hmaxRS : RSO ≤ bOuter L + selDom L + pApp (bAppIn L) :=
        NativeCertificate.maxRoundSpace_le cstep (3 * n) (m, P, rows₀) fun i hi => (hstep_b i hi).2
      calc (greedyParityRowsCertificate cCount).space (n, m, P, rows₀)
          = cn.space (n, m, P, rows₀) + L + RSO + MO + (encNat (3 * n)).length := rfl
        _ ≤ poly L := by dsimp only [poly, initOuter, outerFixed]; omega
  exact ⟨poly, hpoly, (greedyParityRowsCertificate cCount).computes.mono_le
    (fun a => (hboth a).1) (fun a => (hboth a).2)⟩

/-- For a fixed counter `(countSys, cCount)` using polynomial workspace, `greedyParityRows` runs in
polynomial space on runtime inputs `(n, m, P, rows)`. -/
theorem computableInPolySpace_greedyParityRows {countSys : List (List Bool) → ℕ}
    (cCount : NativeCertificate countSys (encList encBits) encNat)
    (hSpace : PolyBounded (fun r => (encList encBits r).length) cCount.space) :
    ComputableInPolySpace
      (fun a : ℕ × ℕ × ℕ × List (List Bool) =>
        greedyParityRows countSys a.1 a.2.1 a.2.2.1 a.2.2.2)
      encGreedyIn (encList encBits) := by
  let cell (a : ℕ × ℕ × ℕ × List (List Bool)) (i j : ℕ) : ℕ :=
    cCount.time (greedyParityRowsAt countSys a.2.1 a.2.2.1 a.2.2.2 i ++
      [materializeTestRow a.2.1 (decodeTestTuple a.2.1 a.2.2.1 j)])
  let rowMax (a : ℕ × ℕ × ℕ × List (List Bool)) (i : ℕ) : ℕ :=
    listMax (cell a i) (List.range (candidateTupleCount a.2.1 a.2.2.1 + 1))
  let R (a : ℕ × ℕ × ℕ × List (List Bool)) : ℕ := listMax (rowMax a) (List.range (3 * a.1 + 1))
  have hR : ∀ a, ∀ i ≤ 3 * a.1, ∀ j ≤ candidateTupleCount a.2.1 a.2.2.1, cell a i j ≤ R a :=
    fun a i hi j hj => (le_listMax (f := cell a i) (List.mem_range.mpr (by omega))).trans
      (le_listMax (f := rowMax a) (List.mem_range.mpr (by omega)))
  obtain ⟨poly, hpoly, c, hc, hl⟩ := computableInO_greedyParityRows cCount hSpace R hR
  exact ⟨_, fun n => c * (poly n + 1), by fun_prop, hc, hl⟩

end Cslib.Logic.PL.CNF

end
