/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Ladner.Basic
public import Complexity.Computability.Complexity.Problems.SAT.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option

/-!
# Ladner's language in polynomial time and in NP

The exponent function `Cslib.Complexity.Ladner.H` of Ladner's language is tidily computable in
polynomial time on unary numbers (`Cslib.Complexity.Ladner.computableInPolyTime_H`), and
Ladner's language is in `NP` (`Cslib.Complexity.Ladner.SATH_mem_NP`), with a verifier that reads
the padded formula and evaluates it under the assignment the certificate describes.

The table of the values `H m`, `m < n`, is built by iterating one step `n` times. The step
(`Cslib.Complexity.Ladner.hstepB`, equal to `Cslib.Complexity.Ladner.Hstep`) searches the first
`log₂ (log₂ n)` machine indices; for each, it runs the machine on each of the `n` words with
indices below `n` with the universal function, for at most `n` steps, and compares the answer with
membership in the padded language along the table. A word with index below `n` has length at most
`log₂ n`, so membership is decided by decoding the padded formula and trying the `n` words with
indices below `n` as certificates (`Cslib.Complexity.Ladner.bruteSAT_iff`). Every intermediate
value is polynomial in `n`, and the polynomial-time calculus certifies the composite.

The certificate rests on general tools: a total decoder for formulas
(`Cslib.Complexity.cnfDecoder`, built from `Turing.MultiTapeTM.Decoder.nat` and
`Turing.MultiTapeTM.Decoder.bool`), capped powers on unary numbers
(`Cslib.Complexity.Ladner.computableInPolyTime_capPow`), the universal function with its
number of steps in unary (`Turing.MultiTapeTM.Universal.computableTidilyInPolyTime_universal`), and
the words by index (`Cslib.Complexity.Ladner.computableInPolyTime_word`). Decoding machine
descriptions and coding their input bits use the shared polynomial-time rules in
`Complexity.Computability.Machines.Turing.MultiTape.Universal.PolyTime`.

## Main definitions

* `Cslib.Complexity.Ladner.capPow`: powers capped at a bound.
* `Cslib.Complexity.Ladner.padCheckAt`, `Cslib.Complexity.Ladner.padCheck`: the formula padded in a
  word, if any.
* `Cslib.Complexity.Ladner.bruteSAT`: satisfiability by trying the words with small indices.
* `Cslib.Complexity.Ladner.hstepB`: the step of the exponent function as a search.
* `Cslib.Complexity.Ladner.verifier`: the verifier of Ladner's language.

## Main results

* `Cslib.Complexity.Ladner.computableInPolyTime_capPow`: capped powers in unary.
* `Cslib.Complexity.Ladner.mem_padSAT_iff`: membership in a padded language through `padCheck`.
* `Cslib.Complexity.Ladner.computableInPolyTime_padCheck`: `padCheck` is polynomial-time for a
  polynomial-time exponent function.
* `Cslib.Complexity.Ladner.hstepB_eq`: the search computes the step.
* `Cslib.Complexity.Ladner.computableInPolyTime_H`: `H` is polynomial-time.
* `Cslib.Complexity.Ladner.SATH_mem_NP`: Ladner's language is in `NP`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity.Ladner

open Turing.MultiTapeTM Turing.MultiTapeTM.Universal ComputableTidilyInPolyTime
open Cslib.Logic.PL

/-! ### Decoding formulas -/

/-- The formula decoded from a word. -/
def decodeCNF (w : List Bool) : CNF ℕ := Complexity.cnfDecoder.decode w

@[simp]
theorem decodeCNF_encCNF (φ : CNF ℕ) : decodeCNF (encCNF φ) = φ :=
  Complexity.cnfDecoder.decode_enc φ

private theorem computableTidilyInPolyTime_decodeCNF :
    ComputableTidilyInPolyTime decodeCNF encBits encCNF :=
  let ⟨_, _, h⟩ := Complexity.cnfDecoder.computable
  h.computableTidilyInPolyTime

attribute [local fun_prop] computableTidilyInPolyTime_decodeCNF

@[fun_prop]
theorem computableInPolyTime_decodeCNF :
    ComputableInPolyTime decodeCNF encBits encCNF :=
  .of_tidy (computableTidilyInPolyTime_decodeCNF)

/-! ### Capped powers -/

private theorem min_min_mul (a b c : ℕ) : min (min a c * b) c = min (a * b) c := by
  rcases le_total a c with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h]
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    · rw [min_eq_right (Nat.le_mul_of_pos_right c hb),
        min_eq_right (h.trans (Nat.le_mul_of_pos_right a hb))]

private theorem iterate_min_mul (b c e a : ℕ) :
    (fun x => min (x * b) c)^[e] (min a c) = min (a * b ^ e) c := by
  induction e generalizing a with
  | zero => simp
  | succ e ih =>
    rw [Function.iterate_succ_apply, min_min_mul, ih, pow_succ', mul_assoc]

/-- The power `b ^ e`, capped at `c`. -/
def capPow (b e c : ℕ) : ℕ := min (b ^ e) c

/-- **Capped powers in unary.** `min (b ^ e) c` is polynomial-time on unary numbers: multiplying
`e` times and capping at `c` never holds a number larger than the input. -/
private theorem computableTidilyInPolyTime_capPow_pair :
    ComputableTidilyInPolyTime (fun p : ℕ × ℕ × ℕ => capPow p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encUnary encUnary)) encUnary := by
  have h := iterateWith (encIn := encPair encUnary (encPair encUnary encUnary))
    (encState := encUnary) (encPar := encPair encUnary encUnary)
    (par := fun p => (p.1, p.2.2)) (count := fun p => p.2.1) (init := fun p => min 1 p.2.2)
    (step := fun q x => min (x * q.1) q.2) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (bound := fun p => (encPair encUnary (encPair encUnary encUnary) p).length) .self
    (fun p i _ => by
      simp only [iterate_min_mul, encUnary_apply, List.length_replicate, encPair_apply,
        List.length_append, length_frame]
      have := min_le_right (1 * p.1 ^ i) p.2.2
      omega)
  simpa only [iterate_min_mul, one_mul, capPow] using h

private theorem computableTidilyInPolyTime_capPow {α : Type} {input : α ↪ List Bool}
    {base exp cap : α → ℕ} (hbase : ComputableTidilyInPolyTime base input encUnary)
    (hexp : ComputableTidilyInPolyTime exp input encUnary)
    (hcap : ComputableTidilyInPolyTime cap input encUnary) :
    ComputableTidilyInPolyTime (fun x => capPow (base x) (exp x) (cap x)) input encUnary :=
  computableTidilyInPolyTime_capPow_pair.comp (hbase.prod (hexp.prod hcap))

attribute [local fun_prop] computableTidilyInPolyTime_capPow

@[fun_prop]
theorem computableInPolyTime_capPow {α : Type} {input : α ↪ List Bool}
    {base exp cap : α → ℕ} (hbase : ComputableInPolyTime base input encUnary)
    (hexp : ComputableInPolyTime exp input encUnary)
    (hcap : ComputableInPolyTime cap input encUnary) :
    ComputableInPolyTime (fun x => capPow (base x) (exp x) (cap x)) input encUnary :=
  .of_tidy (computableTidilyInPolyTime_capPow hbase.tidy hexp.tidy hcap.tidy)

/-! ### Words by index -/

private theorem computableTidilyInPolyTime_word : ComputableTidilyInPolyTime word encUnary
    encBits := by
  have h : word = fun j => (encNat (j + 1)).take ((encNat (j + 1)).length - 1) := by
    funext j
    simp [word, encNat_apply, List.dropLast_eq_take]
  rw [h]
  fun_prop

attribute [local fun_prop] computableTidilyInPolyTime_word

/-- The word with a given index is polynomial-time in the index in unary. -/
@[fun_prop]
theorem computableInPolyTime_word : ComputableInPolyTime word encUnary encBits :=
  .of_tidy (computableTidilyInPolyTime_word)

/-! ### Reading a padded formula -/

/-- The formula `φ` such that `y` is `encCNF φ` padded with `(encCNF φ).length ^ h` ones, if there
is one. -/
def padCheckAt (y : List Bool) (h : ℕ) : Option (CNF ℕ) :=
  if (unpad y).2 < y.length ∧ encCNF (decodeCNF (unpad y).1) = (unpad y).1 ∧
      capPow (unpad y).1.length h ((unpad y).2 + 1) = (unpad y).2 then
    some (decodeCNF (unpad y).1)
  else none

theorem padCheckAt_eq_some_iff {y : List Bool} {h : ℕ} {φ : CNF ℕ} :
    padCheckAt y h = some φ ↔ y = pad (encCNF φ) ((encCNF φ).length ^ h) := by
  constructor
  · intro hφ
    rw [padCheckAt] at hφ
    split_ifs at hφ with hc
    obtain ⟨hlt, henc, hpow⟩ := hc
    obtain rfl := Option.some_injective _ hφ
    have hk : (unpad y).1.length ^ h = (unpad y).2 := by
      rw [capPow] at hpow
      rcases le_total ((unpad y).1.length ^ h) ((unpad y).2 + 1) with h₁ | h₁
      · rwa [min_eq_left h₁] at hpow
      · rw [min_eq_right h₁] at hpow
        omega
    rw [henc, hk, pad_unpad hlt]
  · rintro rfl
    rw [padCheckAt, unpad_pad]
    simp [capPow]

/-- The formula padded in `y` along the exponent function `e`, if any. -/
def padCheck (e : ℕ → ℕ) (y : List Bool) : Option (CNF ℕ) :=
  padCheckAt y (e (unpad y).1.length)

theorem padCheck_eq_some_iff {e : ℕ → ℕ} {y : List Bool} {φ : CNF ℕ} :
    padCheck e y = some φ ↔ y = pad (encCNF φ) ((encCNF φ).length ^ e (encCNF φ).length) := by
  rw [padCheck, padCheckAt_eq_some_iff]
  constructor
  · intro h
    have hu : (unpad y).1 = encCNF φ := by rw [h, unpad_pad]
    rwa [hu] at h
  · intro h
    rw [h, unpad_pad]

/-- **Membership in a padded language through `padCheck`.** -/
theorem mem_padSAT_iff {e : ℕ → ℕ} {y : List Bool} :
    y ∈ padSAT e ↔ ∃ φ, padCheck e y = some φ ∧ φ ∈ SAT := by
  simp only [padCheck_eq_some_iff, padSAT, Set.mem_ofPred_eq]
  exact ⟨fun ⟨φ, hφ, h⟩ => ⟨φ, h, hφ⟩, fun ⟨φ, h, hφ⟩ => ⟨φ, hφ, h⟩⟩

private theorem computableTidilyInPolyTime_idxOf_false_reverse :
    ComputableTidilyInPolyTime (fun y : List Bool => y.reverse.idxOf false) encBits encUnary :=
  idxOfWithInput (encA := encBool) (list := fun y : List Bool => y.reverse)
    (value := fun _ => false) (bitsToList.comp bitsReverse) (const false)

private theorem computableTidilyInPolyTime_unpad :
    ComputableTidilyInPolyTime unpad encBits (encPair encBits encUnary) := by
  have hk := computableTidilyInPolyTime_idxOf_false_reverse
  unfold unpad
  fun_prop

attribute [local fun_prop] computableTidilyInPolyTime_unpad

/-- Splitting a padded word is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_unpad :
    ComputableInPolyTime unpad encBits (encPair encBits encUnary) :=
  .of_tidy (computableTidilyInPolyTime_unpad)

/-- Reading the formula padded with a given exponent is polynomial-time. -/
private theorem computableTidilyInPolyTime_padCheckAt :
    ComputableTidilyInPolyTime (fun p : List Bool × ℕ => padCheckAt p.1 p.2)
      (encPair encBits encUnary) (encOption encCNF) := by
  have henc : ComputableTidilyInPolyTime (fun φ => encCNF φ) encCNF encBits := encode encCNF
  unfold padCheckAt
  fun_prop

private theorem computableTidilyInPolyTime_padCheck {α : Type} {input : α ↪ List Bool}
    {e : α → ℕ → ℕ} {y : α → List Bool}
    (he : ComputableTidilyInPolyTime (fun p : α × ℕ => e p.1 p.2) (encPair input encUnary)
      encUnary)
    (hy : ComputableTidilyInPolyTime y input encBits) :
    ComputableTidilyInPolyTime (fun x => padCheck (e x) (y x)) input (encOption encCNF) := by
  have h := computableTidilyInPolyTime_padCheckAt
  unfold padCheck
  fun_prop

attribute [local fun_prop] computableTidilyInPolyTime_padCheck

/-- Reading the formula padded along a computed exponent function is polynomial-time. The
exponent function may capture the input. -/
@[fun_prop]
theorem computableInPolyTime_padCheck {α : Type} {input : α ↪ List Bool}
    {e : α → ℕ → ℕ} {y : α → List Bool}
    (he : ComputableInPolyTime (fun p : α × ℕ => e p.1 p.2) (encPair input encUnary)
      encUnary)
    (hy : ComputableInPolyTime y input encBits) :
    ComputableInPolyTime (fun x => padCheck (e x) (y x)) input (encOption encCNF) :=
  .of_tidy (computableTidilyInPolyTime_padCheck he.tidy hy.tidy)

/-! ### Satisfiability of short formulas -/

/-- Whether one of the words with indices below `n` is a satisfying certificate for `φ`. -/
def bruteSAT (n : ℕ) (φ : CNF ℕ) : Bool := (List.range n).any fun j => SAT.verifier (φ, word j)

/-- **Short formulas are decided by trying the words with small indices**: every certificate of
the length of the encoded formula has a smaller index than `n`. -/
theorem bruteSAT_iff {n : ℕ} {φ : CNF ℕ} (h : 2 ^ ((encCNF φ).length + 1) ≤ n + 1) :
    bruteSAT n φ = true ↔ φ ∈ SAT := by
  constructor
  · intro hb
    obtain ⟨j, -, hj⟩ := List.any_eq_true.mp hb
    exact ⟨_, hj⟩
  · intro hφ
    obtain ⟨w, hw, hv⟩ := (SAT.isVerifier φ).mp hφ
    rw [Polynomial.eval_X] at hw
    have hi := index_add_two_le w
    rw [hw] at hi
    exact List.any_eq_true.mpr ⟨index w, List.mem_range.mpr (by omega), by rwa [word_index]⟩

private theorem computableTidilyInPolyTime_bruteSAT {α : Type} {input : α ↪ List Bool}
    {n : α → ℕ} {φ : α → CNF ℕ} (hn : ComputableTidilyInPolyTime n input encUnary)
    (hφ : ComputableTidilyInPolyTime φ input encCNF) :
    ComputableTidilyInPolyTime (fun x => bruteSAT (n x) (φ x)) input encBool := by
  have hverifier := SAT.computableInPolyTime_verifier.tidy
  unfold bruteSAT
  fun_prop

attribute [local fun_prop] computableTidilyInPolyTime_bruteSAT

@[fun_prop]
theorem computableInPolyTime_bruteSAT {α : Type} {input : α ↪ List Bool}
    {n : α → ℕ} {φ : α → CNF ℕ} (hn : ComputableInPolyTime n input encUnary)
    (hφ : ComputableInPolyTime φ input encCNF) :
    ComputableInPolyTime (fun x => bruteSAT (n x) (φ x)) input encBool :=
  .of_tidy (computableTidilyInPolyTime_bruteSAT hn.tidy hφ.tidy)

/-! ### The step of the exponent function -/

/-- Membership in the padded language along the table `T`, decided by `bruteSAT` with the
words with indices below the length of `T`. -/
def memB (T : List ℕ) (y : List Bool) : Bool :=
  (padCheck (fun m => T.getD m 0) y).elim false (bruteSAT T.length)

theorem memB_word_iff {T : List ℕ} {j : ℕ} (hj : j < T.length) :
    memB T (word j) = true ↔ word j ∈ padSAT (fun m => T.getD m 0) := by
  rw [mem_padSAT_iff, memB]
  cases hc : padCheck (fun m => T.getD m 0) (word j) with
  | none => simp
  | some φ =>
    simp only [Option.elim_some, Option.some.injEq, exists_eq_left']
    refine bruteSAT_iff ?_
    have hy := congrArg List.length (padCheck_eq_some_iff.mp hc)
    have h₂ := two_pow_length_word_le j
    rw [length_pad] at hy
    calc 2 ^ ((encCNF φ).length + 1) ≤ 2 ^ (word j).length :=
          Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ T.length + 1 := by omega

/-- The test of `Cslib.Complexity.Ladner.Agrees` along the table `T`, as a Boolean. -/
def agreesB (T : List ℕ) (i j : ℕ) : Bool :=
  decide (runIndexed i (word j) (capPow (2 * (word j).length + 2) i T.length) =
    ([eBit (memB T (word j))], true))

theorem agreesB_iff {T : List ℕ} {i j : ℕ} (hj : j < T.length) :
    agreesB T i j = true ↔ Agrees (fun m => T.getD m 0) T.length i j := by
  rw [agreesB, decide_eq_true_iff, Agrees, ← memB_word_iff hj]
  constructor
  · intro h
    exact ⟨_, h, Iff.rfl⟩
  · rintro ⟨b, hb, hiff⟩
    have : memB T (word j) = b := by
      cases b <;> cases hm : memB T (word j) <;> simp_all
    rwa [this]

/-- The step of the exponent function as a search over machine indices and words. -/
def hstepB (T : List ℕ) : ℕ :=
  ((List.range (Nat.log 2 (Nat.log 2 T.length))).find? fun i =>
    (List.range T.length).all fun j => agreesB T i j).getD (Nat.log 2 (Nat.log 2 T.length))

/-- The least index below `m` passing a test, or `m`, as a search over `List.range m`. -/
private theorem find?_range_getD_eq_sInf (m : ℕ) (p : ℕ → Bool) :
    ((List.range m).find? p).getD m = sInf {i | i = m ∨ p i = true} := by
  set v := ((List.range m).find? p).getD m with hv
  have hmem : v ∈ {i | i = m ∨ p i = true} ∧ ∀ i < v, i ∉ {i | i = m ∨ p i = true} := by
    cases hf : (List.range m).find? p with
    | none =>
      rw [hv, hf, Option.getD_none]
      rw [List.find?_eq_none] at hf
      refine ⟨Or.inl rfl, fun i hi hmem => ?_⟩
      rcases hmem with rfl | h
      · exact lt_irrefl _ hi
      · exact hf i (List.mem_range.mpr hi) h
    | some i₀ =>
      rw [hv, hf, Option.getD_some]
      obtain ⟨hp, k, hk, hki, hmin⟩ := List.find?_eq_some_iff_getElem.mp hf
      rw [List.getElem_range] at hki
      subst hki
      rw [List.length_range] at hk
      refine ⟨Or.inr hp, fun i hi hmem => ?_⟩
      rcases hmem with rfl | h
      · omega
      · have := hmin i hi
        simp_all
  exact le_antisymm (not_lt.mp fun h => hmem.2 _ h (Nat.sInf_mem ⟨v, hmem.1⟩)) (Nat.sInf_le hmem.1)

/-- **The search computes the step.** -/
theorem hstepB_eq (T : List ℕ) : hstepB T = Hstep T := by
  rw [hstepB, find?_range_getD_eq_sInf, Hstep]
  congr 1
  ext i
  simp only [Set.mem_ofPred_eq, List.all_eq_true, List.mem_range]
  exact or_congr_right (forall₂_congr fun j hj => agreesB_iff hj)

private theorem computableTidilyInPolyTime_runIndexed {α : Type} {input : α ↪ List Bool}
    {i : α → ℕ} {w : α → List Bool} {t : α → ℕ}
    (hi : ComputableTidilyInPolyTime i input encUnary)
    (hw : ComputableTidilyInPolyTime w input encBits)
    (ht : ComputableTidilyInPolyTime t input encUnary) :
    ComputableTidilyInPolyTime (fun x => runIndexed (i x) (w x) (t x)) input eOut := by
  unfold runIndexed
  fun_prop

attribute [local fun_prop] computableTidilyInPolyTime_runIndexed

/-- The run of an indexed machine, with the number of steps in unary, is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_runIndexed {α : Type} {input : α ↪ List Bool}
    {i : α → ℕ} {w : α → List Bool} {t : α → ℕ}
    (hi : ComputableInPolyTime i input encUnary)
    (hw : ComputableInPolyTime w input encBits)
    (ht : ComputableInPolyTime t input encUnary) :
    ComputableInPolyTime (fun x => runIndexed (i x) (w x) (t x)) input eOut :=
  .of_tidy (computableTidilyInPolyTime_runIndexed hi.tidy hw.tidy ht.tidy)

private theorem computableTidilyInPolyTime_memB :
    ComputableTidilyInPolyTime (fun p : List ℕ × List Bool => memB p.1 p.2)
      (encPair (encList encUnary) encBits) encBool := by
  unfold memB
  fun_prop

private theorem computableTidilyInPolyTime_agreesB :
    ComputableTidilyInPolyTime (fun p : (List ℕ × ℕ) × ℕ => agreesB p.1.1 p.1.2 p.2)
      (encPair (encPair (encList encUnary) encUnary) encUnary) encBool := by
  have hm := computableTidilyInPolyTime_memB
  unfold agreesB
  fun_prop

/-- The step of the exponent function is polynomial-time in its table. -/
private theorem computableTidilyInPolyTime_hstepB :
    ComputableTidilyInPolyTime hstepB (encList encUnary) encUnary := by
  have ha := computableTidilyInPolyTime_agreesB
  have hall : ComputableTidilyInPolyTime
      (fun p : List ℕ × ℕ => (List.range p.1.length).all fun j => agreesB p.1 p.2 j)
      (encPair (encList encUnary) encUnary) encBool := by
    fun_prop
  unfold hstepB
  fun_prop

/-! ### The exponent function -/

theorem Htable_eq_iterate (n : ℕ) : Htable n = (fun T => T ++ [hstepB T])^[n] [] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Htable, Function.iterate_succ_apply', ← ih, hstepB_eq]

private theorem computableTidilyInPolyTime_Htable :
    ComputableTidilyInPolyTime Htable encUnary (encList encUnary) := by
  have hs := computableTidilyInPolyTime_hstepB
  have h := iterate (encIn := encUnary) (encState := encList encUnary) (count := fun n => n)
    (init := fun _ => []) (step := fun T => T ++ [hstepB T]) (by fun_prop) (by fun_prop)
    (by fun_prop) (bound := fun n => n * (2 * n + 1))
    (.of_forall_le 2 2 fun n => by simp only [encUnary_apply, List.length_replicate]; nlinarith)
    (fun n i hi => by
      rw [← Htable_eq_iterate]
      calc (encList encUnary (Htable i)).length ≤ (Htable i).length * (2 * n + 1) :=
            length_encList_le encUnary _ fun a ha => by
              rw [Htable_eq] at ha
              obtain ⟨m, hm, rfl⟩ := List.mem_map.mp ha
              simpa using (H_le_self m).trans (by have := List.mem_range.mp hm; omega)
        _ ≤ n * (2 * n + 1) := by rw [length_Htable]; exact Nat.mul_le_mul_right _ hi)
  simpa only [← Htable_eq_iterate] using h

attribute [local fun_prop] computableTidilyInPolyTime_Htable

/-- The tables of `H` are polynomial-time in their length, in unary. -/
theorem computableInPolyTime_Htable :
    ComputableInPolyTime Htable encUnary (encList encUnary) :=
  .of_tidy (computableTidilyInPolyTime_Htable)

private theorem computableTidilyInPolyTime_H : ComputableTidilyInPolyTime H encUnary encUnary := by
  have h := computableTidilyInPolyTime_hstepB.comp computableTidilyInPolyTime_Htable
  have heq : hstepB ∘ Htable = H := funext fun n => hstepB_eq _
  rwa [heq] at h

attribute [local fun_prop] computableTidilyInPolyTime_H

/-- **`H` is polynomial-time** on unary numbers. -/
@[fun_prop]
theorem computableInPolyTime_H : ComputableInPolyTime H encUnary encUnary :=
  .of_tidy (computableTidilyInPolyTime_H)

/-! ### Ladner's language is in NP -/

/-- The verifier of Ladner's language: read the padded formula and evaluate it under the
assignment the certificate describes. -/
noncomputable def verifier (x : List Bool × List Bool) : Bool :=
  (padCheck H x.1).elim false fun φ => SAT.verifier (φ, x.2)

private theorem computableTidilyInPolyTime_verifier :
    ComputableTidilyInPolyTime verifier (encPair encBits encBits) encBool := by
  have hH : ComputableTidilyInPolyTime (fun p : (List Bool × List Bool) × ℕ => H p.2)
      (encPair (encPair encBits encBits) encUnary) encUnary :=
    computableInPolyTime_H.tidy.comp (snd _ _)
  have hverifier := SAT.computableInPolyTime_verifier.tidy
  unfold verifier
  fun_prop

/-- Padding a certificate with `false` does not change the assignment it describes. -/
private theorem assignment_append_replicate (φ : CNF ℕ) (w : List Bool) (k : ℕ) :
    SAT.assignment φ (w ++ List.replicate k false) = SAT.assignment φ w := by
  funext v
  simp only [SAT.assignment, List.getD_eq_getElem?_getD, List.getElem?_append]
  split_ifs with h
  · rfl
  · rw [List.getElem?_eq_none (l := w) (by omega), List.getElem?_replicate]
    split <;> rfl

/-- `Cslib.Complexity.Ladner.verifier` verifies Ladner's language with certificates as long as the
word. -/
theorem isVerifier : IsVerifier encBits Polynomial.X verifier SATH := by
  intro y
  simp only [Polynomial.eval_X, encBits_apply, verifier]
  constructor
  · intro hy
    obtain ⟨φ, hφ, hsat⟩ := mem_padSAT_iff.mp hy
    obtain ⟨w, hw, hv⟩ := (SAT.isVerifier φ).mp hsat
    rw [Polynomial.eval_X] at hw
    have hlen := congrArg List.length (padCheck_eq_some_iff.mp hφ)
    rw [length_pad] at hlen
    refine ⟨w ++ List.replicate (y.length - w.length) false,
      by rw [List.length_append, List.length_replicate]; omega, ?_⟩
    rw [hφ, Option.elim_some]
    simpa only [SAT.verifier, assignment_append_replicate] using hv
  · rintro ⟨w, -, hv⟩
    cases hφ : padCheck H y with
    | none => simp [hφ] at hv
    | some φ =>
      rw [hφ, Option.elim_some] at hv
      exact mem_padSAT_iff.mpr ⟨φ, hφ, _, hv⟩

/-- **Ladner's language is in `NP`**, with the verifier evaluating the padded formula. -/
theorem SATH_mem_NP : SATH ∈ NP encBits :=
  ⟨Polynomial.X, verifier, .of_tidy computableTidilyInPolyTime_verifier, isVerifier⟩

end Cslib.Complexity.Ladner
