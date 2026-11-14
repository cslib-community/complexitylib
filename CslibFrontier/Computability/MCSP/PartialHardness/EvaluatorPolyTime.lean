/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.MCSP.PartialHardness.Evaluator
public import CslibFrontier.Computability.MCSP.PartialNP
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Max
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Foundations.Data.Nat.Log
import Mathlib.Data.List.Fold
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax

/-!
# The CMMSA table evaluator runs in polynomial time

The evaluator of `Cslib.Computability.MCSP.PartialHardness.Evaluator` computes the partial truth
table of `FromCMMSA.toInstance` from explicit tables. This module proves that it runs in polynomial
time for fixed `Δ`, `k` and `P`. The instance `I` uses `CMMSAInstance.encoding`, `λ` and term and
slot indices are unary, the input `x` is binary and the tables `T` are a framed list of bit
strings (`encList encBits`).

Every statement has the form "if the arguments are polynomial-time functions of an input `a`, so is
the result". A client may therefore compute the arguments from any context, for instance under
`mapWithInput`, and the per-entry statements are `fun_prop` lemmas.

The widths that place the input fields are polynomial-time in unary. The seed width is a maximum
over the variables (`seedWidth_eq`), so it is read from the largest weight `maxWeight`. The number
`2 ^ L` of table entries is polynomial-time in unary, and polynomially bounded for every instance
and every `λ` (`two_pow_inputLength_le`). Given a list of tables that has the table of every
variable (`IsVarTable`), the instance `toInstance I Δ k λ P f` is then polynomial-time in
`PartialMCSP.enc` (`computableInPolyTime_toInstance`).

## Main definitions

* `Cslib.PartialMCSP.FromCMMSA.maxWeight`: the largest weight of an instance.

## Main results

* `Cslib.PartialMCSP.FromCMMSA.le_maxWeight`, `maxWeight_le`, `maxWeight_eq_zero_or_mem`: the
  largest weight bounds the weights, is at most any bound on them and is `0` or one of them.
* `Cslib.PartialMCSP.FromCMMSA.seedWidth_eq`: the seed width is `⌈log₂ (maxWeight I · λ)⌉`.
* `Cslib.PartialMCSP.FromCMMSA.two_pow_inputLength_le`: a polynomial bound on `2 ^ L` for every
  instance and every `λ`.
* `Cslib.PartialMCSP.FromCMMSA.computableInPolyTime_indexWidth`, `…_seedWidth`, `…_slotWidth`,
  `…_inputLength`, `…_slotOffset`, `…_two_pow_inputLength`: the widths, in unary.
* `Cslib.PartialMCSP.FromCMMSA.computableInPolyTime_mod_two_pow_indexWidth`: the formula index of a
  numeric input.
* `Cslib.PartialMCSP.FromCMMSA.computableInPolyTime_slotBitN`, `…_termParityN`, `…_entryN`,
  `…_tableN`: the evaluator.
* `Cslib.PartialMCSP.FromCMMSA.computableInPolyTime_sizeThreshold`: the size threshold, in unary.
* `Cslib.PartialMCSP.FromCMMSA.computableInPolyTime_toInstance`: the partial MCSP instance from
  explicit tables.

## References

* [S. Hirahara, *NP-Hardness of Learning Programs and Partial MCSP*][Hirahara2022]
-/

public section

namespace Cslib.PartialMCSP.FromCMMSA

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

/-! ### The seed width as a maximum -/

private theorem foldr_max_eq_zero_or_mem (l : List ℕ) :
    l.foldr max 0 = 0 ∨ l.foldr max 0 ∈ l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.foldr_cons]
    rcases max_choice a (l.foldr max 0) with h | h <;> rw [h]
    · simp
    · rcases ih with h' | h'
      · simp [h']
      · simp [h']

/-- The largest weight of `I`, `0` when there is none. -/
def maxWeight (I : CMMSAInstance) : ℕ := I.weights.foldr max 0

/-- Every weight is at most the largest weight. -/
theorem le_maxWeight {I : CMMSAInstance} {w : ℕ} (hw : w ∈ I.weights) : w ≤ maxWeight I :=
  List.le_max_of_le' 0 hw le_rfl

/-- The largest weight is `0` or one of the weights. -/
theorem maxWeight_eq_zero_or_mem (I : CMMSAInstance) :
    maxWeight I = 0 ∨ maxWeight I ∈ I.weights :=
  foldr_max_eq_zero_or_mem I.weights

/-- The largest weight is at most any bound on the weights. -/
theorem maxWeight_le {I : CMMSAInstance} {b : ℕ} (h : ∀ w ∈ I.weights, w ≤ b) :
    maxWeight I ≤ b :=
  List.max_le_of_forall_le _ _ h

/-- **The seed width is `⌈log₂ (w_max λ)⌉`** for the largest weight `w_max`. -/
theorem seedWidth_eq (I : CMMSAInstance) (lam : ℕ) :
    seedWidth I lam = Nat.clog 2 (maxWeight I * lam) := by
  refine le_antisymm (Finset.sup_le fun v hv => ?_) ?_
  · refine Nat.clog_mono_right _ (Nat.mul_le_mul_right _ (le_maxWeight ?_))
    rw [List.getD_eq_getElem _ _ (Finset.mem_range.1 hv)]
    exact List.getElem_mem _
  · rcases maxWeight_eq_zero_or_mem I with h | h
    · simp [h]
    · obtain ⟨v, hv, hw⟩ := List.getElem_of_mem h
      refine le_trans (le_of_eq ?_) (Finset.le_sup (f := varLength I lam) (Finset.mem_range.2 hv))
      rw [varLength, List.getD_eq_getElem _ _ hv, hw]

/-! ### Polynomial time -/

variable {α : Type} {input : α ↪ List Bool}

/-- Reading term `t` of formula `j` is polynomial-time, with `j` in binary and `t` in unary. -/
@[fun_prop]
theorem computableInPolyTime_term {I : α → CMMSAInstance} {j t : α → ℕ}
    (hI : ComputableInPolyTime I input CMMSAInstance.encoding)
    (hj : ComputableInPolyTime j input encNat) (ht : ComputableInPolyTime t input encUnary) :
    ComputableInPolyTime (fun a => term (I a) (j a) (t a)) input (encTermOver encNat) :=
  ComputableInPolyTime.listGetDWithInput
    (ComputableInPolyTime.listGetD_binary [] (CMMSAInstance.isPolyTime_formulas hI) hj) ht []

/-- Reading the variable of a literal is polynomial-time; the variable is written in binary. -/
@[fun_prop]
theorem computableInPolyTime_var {I : α → CMMSAInstance} {j t q : α → ℕ}
    (hI : ComputableInPolyTime I input CMMSAInstance.encoding)
    (hj : ComputableInPolyTime j input encNat) (ht : ComputableInPolyTime t input encUnary)
    (hq : ComputableInPolyTime q input encUnary) :
    ComputableInPolyTime (fun a => var (I a) (j a) (t a) (q a)) input encNat :=
  (ComputableInPolyTime.listGetDWithInput (computableInPolyTime_term hI hj ht) hq (0, true)).fst'

/-- The input length of the function of a variable is polynomial-time, in unary. -/
@[fun_prop]
theorem computableInPolyTime_varLength {I : α → CMMSAInstance} {lam v : α → ℕ}
    (hI : ComputableInPolyTime I input CMMSAInstance.encoding)
    (hlam : ComputableInPolyTime lam input encUnary) (hv : ComputableInPolyTime v input encNat) :
    ComputableInPolyTime (fun a => varLength (I a) (lam a) (v a)) input encUnary :=
  (ComputableInPolyTime.unary_clog_const 2).comp
    (ComputableInPolyTime.unary_mul'
      (ComputableInPolyTime.listGetD_binary 0 (CMMSAInstance.isPolyTime_weights hI) hv) hlam)

/-- The largest weight is polynomial-time, in unary. -/
@[fun_prop]
theorem computableInPolyTime_maxWeight {I : α → CMMSAInstance}
    (hI : ComputableInPolyTime I input CMMSAInstance.encoding) :
    ComputableInPolyTime (fun a => maxWeight (I a)) input encUnary := by
  refine ComputableInPolyTime.of_enc_eq ((ComputableInPolyTime.unary_foldl_max 0).comp
    (CMMSAInstance.isPolyTime_weights hI)) fun a => ?_
  rw [Function.comp_apply, maxWeight, List.foldl_eq_foldr]

/-- The width of the formula index is polynomial-time, in unary. -/
@[fun_prop]
theorem computableInPolyTime_indexWidth {I : α → CMMSAInstance}
    (hI : ComputableInPolyTime I input CMMSAInstance.encoding) :
    ComputableInPolyTime (fun a => indexWidth (I a)) input encUnary :=
  (ComputableInPolyTime.unary_clog_const 2).comp
    ((ComputableInPolyTime.length_list _).comp (CMMSAInstance.isPolyTime_formulas hI))

/-- The seed width is polynomial-time, in unary. -/
@[fun_prop]
theorem computableInPolyTime_seedWidth {I : α → CMMSAInstance} {lam : α → ℕ}
    (hI : ComputableInPolyTime I input CMMSAInstance.encoding)
    (hlam : ComputableInPolyTime lam input encUnary) :
    ComputableInPolyTime (fun a => seedWidth (I a) (lam a)) input encUnary := by
  simp only [seedWidth_eq]
  exact (ComputableInPolyTime.unary_clog_const 2).comp
    (ComputableInPolyTime.unary_mul' (computableInPolyTime_maxWeight hI) hlam)

/-- The slot width is polynomial-time, in unary. -/
@[fun_prop]
theorem computableInPolyTime_slotWidth {I : α → CMMSAInstance} {lam : α → ℕ} (k : ℕ)
    (hI : ComputableInPolyTime I input CMMSAInstance.encoding)
    (hlam : ComputableInPolyTime lam input encUnary) :
    ComputableInPolyTime (fun a => slotWidth (I a) k (lam a)) input encUnary :=
  ComputableInPolyTime.unary_add'
    (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const k)
      (computableInPolyTime_seedWidth hI hlam))
    (ComputableInPolyTime.const 1)

/-- The input length is polynomial-time, in unary. -/
@[fun_prop]
theorem computableInPolyTime_inputLength {I : α → CMMSAInstance} {lam : α → ℕ} (Δ k : ℕ)
    (hI : ComputableInPolyTime I input CMMSAInstance.encoding)
    (hlam : ComputableInPolyTime lam input encUnary) :
    ComputableInPolyTime (fun a => inputLength (I a) Δ k (lam a)) input encUnary :=
  ComputableInPolyTime.unary_add' (computableInPolyTime_indexWidth hI)
    (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const (Δ * Δ))
      (computableInPolyTime_slotWidth k hI hlam))

/-- The offset of a slot is polynomial-time, in unary. -/
@[fun_prop]
theorem computableInPolyTime_slotOffset {I : α → CMMSAInstance} {lam t q : α → ℕ} (Δ k : ℕ)
    (hI : ComputableInPolyTime I input CMMSAInstance.encoding)
    (hlam : ComputableInPolyTime lam input encUnary) (ht : ComputableInPolyTime t input encUnary)
    (hq : ComputableInPolyTime q input encUnary) :
    ComputableInPolyTime (fun a => slotOffset (I a) Δ k (lam a) (t a) (q a)) input encUnary :=
  ComputableInPolyTime.unary_add' (computableInPolyTime_indexWidth hI)
    (ComputableInPolyTime.unary_mul' (computableInPolyTime_slotWidth k hI hlam)
      (ComputableInPolyTime.unary_add' hq
        (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const Δ) ht)))

private theorem two_pow_inputLength_eq (I : CMMSAInstance) (Δ k lam : ℕ) :
    2 ^ inputLength I Δ k lam =
      2 ^ indexWidth I * ((2 ^ seedWidth I lam) ^ k * 2) ^ (Δ * Δ) := by
  rw [inputLength, slotWidth, pow_add]
  ring

/-- The number `2 ^ L` of table entries is polynomial-time, in unary. -/
theorem computableInPolyTime_two_pow_inputLength {I : α → CMMSAInstance} {lam : α → ℕ}
    (Δ k : ℕ) (hI : ComputableInPolyTime I input CMMSAInstance.encoding)
    (hlam : ComputableInPolyTime lam input encUnary) :
    ComputableInPolyTime (fun a => 2 ^ inputLength (I a) Δ k (lam a)) input encUnary := by
  simp only [two_pow_inputLength_eq, seedWidth_eq]
  exact ComputableInPolyTime.unary_mul'
    (ComputableInPolyTime.unary_pow_clog_const
      ((ComputableInPolyTime.length_list _).comp (CMMSAInstance.isPolyTime_formulas hI)) 2 2)
    ((ComputableInPolyTime.unary_pow (Δ * Δ)).comp
      (ComputableInPolyTime.unary_mul'
        ((ComputableInPolyTime.unary_pow k).comp
          (ComputableInPolyTime.unary_pow_clog_const
            (ComputableInPolyTime.unary_mul' (computableInPolyTime_maxWeight hI) hlam) 2 2))
        (ComputableInPolyTime.const 2)))

/-- **The number of table entries is polynomial**, for every instance `I` and every `λ`:
`2 ^ L ≤ 2 (m + 1) (2 (2 (w_max λ + 1)) ^ k) ^ Δ²` for `m` formulas and largest weight `w_max`. -/
theorem two_pow_inputLength_le (I : CMMSAInstance) (Δ k lam : ℕ) :
    2 ^ inputLength I Δ k lam ≤
      2 * (I.formulas.length + 1) * ((2 * (maxWeight I * lam + 1)) ^ k * 2) ^ (Δ * Δ) := by
  rw [two_pow_inputLength_eq, seedWidth_eq, indexWidth]
  gcongr
  · exact Nat.two_pow_clog_two_le _
  · exact Nat.two_pow_clog_two_le _

/-! ### The evaluator -/

/-- `xor`-folding a polynomial-time family over `0, …, n - 1` is polynomial-time, for a fixed `n`.
-/
private theorem computableInPolyTime_foldl_xor_range {g : α → ℕ → Bool} {b : α → Bool} (n : ℕ)
    (hb : ComputableInPolyTime b input encBool)
    (hg : ∀ i < n, ComputableInPolyTime (fun a => g a i) input encBool) :
    ComputableInPolyTime (fun a => (List.range n).foldl (fun acc i => acc ^^ g a i) (b a))
      input encBool := by
  induction n with
  | zero => simpa using hb
  | succ n ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact ComputableInPolyTime.bool_xor.comp
      ((ih fun i hi => hg i (hi.trans n.lt_succ_self)).prod (hg n n.lt_succ_self))

/-- The formula index `x mod 2 ^ indexWidth` of a numeric input is polynomial-time, in binary. -/
theorem computableInPolyTime_mod_two_pow_indexWidth {I : α → CMMSAInstance} {x : α → ℕ}
    (hI : ComputableInPolyTime I input CMMSAInstance.encoding)
    (hx : ComputableInPolyTime x input encNat) :
    ComputableInPolyTime (fun a => x a % 2 ^ indexWidth (I a)) input encNat :=
  ComputableInPolyTime.binary_mod.comp
    (hx.prod (ComputableInPolyTime.binary_two_pow.comp (computableInPolyTime_indexWidth hI)))

/-- A slot bit computed from explicit tables is polynomial-time, for fixed `Δ` and `k`: the
instance `I` (in `CMMSAInstance.encoding`), `λ` and the slot `(t, q)` in unary, the tables `T` and
the input `x` in binary. -/
@[fun_prop]
theorem computableInPolyTime_slotBitN {I : α → CMMSAInstance} {lam t q x : α → ℕ}
    {T : α → List (List Bool)} (Δ k : ℕ)
    (hI : ComputableInPolyTime I input CMMSAInstance.encoding)
    (hlam : ComputableInPolyTime lam input encUnary)
    (hT : ComputableInPolyTime T input (encList encBits))
    (hx : ComputableInPolyTime x input encNat) (ht : ComputableInPolyTime t input encUnary)
    (hq : ComputableInPolyTime q input encUnary) :
    ComputableInPolyTime (fun a => slotBitN (I a) Δ k (lam a) (T a) (x a) (t a) (q a))
      input encBool := by
  have hv := computableInPolyTime_var hI (computableInPolyTime_mod_two_pow_indexWidth hI hx) ht hq
  have hoff := computableInPolyTime_slotOffset Δ k hI hlam ht hq
  have hW := computableInPolyTime_seedWidth hI hlam
  unfold slotBitN
  refine computableInPolyTime_foldl_xor_range k
    (ComputableInPolyTime.binary_testBit hx (ComputableInPolyTime.unary_add' hoff
      (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const k) hW))) fun i _ => ?_
  exact ComputableInPolyTime.listGetD_binary (encA := encBool) (encL := encBits) false
    (ComputableInPolyTime.listGetD_binary (encA := encBits) (encL := encList encBits) [] hT hv)
    (ComputableInPolyTime.binary_mod.comp ((ComputableInPolyTime.binary_div' hx
      (ComputableInPolyTime.binary_two_pow.comp (ComputableInPolyTime.unary_add' hoff
        (ComputableInPolyTime.unary_mul' hW (ComputableInPolyTime.const i))))).prod
      (ComputableInPolyTime.binary_two_pow.comp (computableInPolyTime_varLength hI hlam hv))))

/-- The parity of a term computed from explicit tables is polynomial-time, for fixed `Δ` and `k`:
the instance `I` (in `CMMSAInstance.encoding`), `λ` and the term `t` in unary, the tables `T` and
the input `x` in binary. -/
@[fun_prop]
theorem computableInPolyTime_termParityN {I : α → CMMSAInstance} {lam t x : α → ℕ}
    {T : α → List (List Bool)} (Δ k : ℕ)
    (hI : ComputableInPolyTime I input CMMSAInstance.encoding)
    (hlam : ComputableInPolyTime lam input encUnary)
    (hT : ComputableInPolyTime T input (encList encBits))
    (hx : ComputableInPolyTime x input encNat) (ht : ComputableInPolyTime t input encUnary) :
    ComputableInPolyTime (fun a => termParityN (I a) Δ k (lam a) (T a) (x a) (t a))
      input encBool := by
  have hterm := computableInPolyTime_term hI (computableInPolyTime_mod_two_pow_indexWidth hI hx) ht
  unfold termParityN
  refine computableInPolyTime_foldl_xor_range Δ (ComputableInPolyTime.const false) fun q _ => ?_
  exact ComputableInPolyTime.bool_and'
    (ComputableInPolyTime.unary_lt' (ComputableInPolyTime.const q)
      ((ComputableInPolyTime.length_list _).comp hterm))
    (computableInPolyTime_slotBitN Δ k hI hlam hT hx ht (ComputableInPolyTime.const q))

/-- An entry computed from explicit tables is polynomial-time, for fixed `Δ` and `k`: the instance
`I` (in `CMMSAInstance.encoding`), `λ` in unary, the tables `T` and the input `x` in binary. -/
@[fun_prop]
theorem computableInPolyTime_entryN {I : α → CMMSAInstance} {lam x : α → ℕ}
    {T : α → List (List Bool)} (Δ k : ℕ)
    (hI : ComputableInPolyTime I input CMMSAInstance.encoding)
    (hlam : ComputableInPolyTime lam input encUnary)
    (hT : ComputableInPolyTime T input (encList encBits))
    (hx : ComputableInPolyTime x input encNat) :
    ComputableInPolyTime (fun a => entryN (I a) Δ k (lam a) (T a) (x a))
      input (encOption encBool) := by
  have hj := computableInPolyTime_mod_two_pow_indexWidth hI hx
  have hφ := ComputableInPolyTime.listGetD_binary (encA := encDNFOver encNat)
    (encL := encList (encDNFOver encNat)) [] (CMMSAInstance.isPolyTime_formulas hI) hj
  have hlen := (ComputableInPolyTime.length_list _).comp hφ
  have hnot (t : ℕ) := ComputableInPolyTime.bool_not.comp
    (ComputableInPolyTime.unary_lt' (ComputableInPolyTime.const t) hlen)
  have hpar (t : ℕ) :=
    computableInPolyTime_termParityN Δ k hI hlam hT hx (ComputableInPolyTime.const t)
  have hyes := ComputableInPolyTime.allConst (List.range Δ) fun t _ =>
    ComputableInPolyTime.bool_or' (hnot t) (hpar t)
  have hno := ComputableInPolyTime.allConst (List.range Δ) fun t _ =>
    ComputableInPolyTime.bool_or' (hnot t) (ComputableInPolyTime.bool_not.comp (hpar t))
  have hsome (b : Bool) : ComputableInPolyTime (fun _ : α => some b) input (encOption encBool) :=
    ComputableInPolyTime.const _
  unfold entryN
  exact ComputableInPolyTime.ite_decide
    (ComputableInPolyTime.binary_lt' hj (ComputableInPolyTime.unary_to_binary.comp
      ((ComputableInPolyTime.length_list _).comp (CMMSAInstance.isPolyTime_formulas hI))))
    (ComputableInPolyTime.ite' (encC := encBool) hyes (hsome true)
      (ComputableInPolyTime.ite' (encC := encBool) hno (hsome false)
        (ComputableInPolyTime.const _)))
    (ComputableInPolyTime.const _)

/-- The whole table computed from explicit tables is polynomial-time, for fixed `Δ` and `k`: the
instance `I` (in `CMMSAInstance.encoding`), `λ` in unary, the tables `T`. -/
@[fun_prop]
theorem computableInPolyTime_tableN {I : α → CMMSAInstance} {lam : α → ℕ}
    {T : α → List (List Bool)} (Δ k : ℕ)
    (hI : ComputableInPolyTime I input CMMSAInstance.encoding)
    (hlam : ComputableInPolyTime lam input encUnary)
    (hT : ComputableInPolyTime T input (encList encBits)) :
    ComputableInPolyTime (fun a => tableN (I a) Δ k (lam a) (T a)) input PartialMCSP.encTable := by
  have h₁ := ComputableInPolyTime.fst input encUnary
  unfold tableN
  exact ComputableInPolyTime.mapWithInput
    (ComputableInPolyTime.unary_range' (computableInPolyTime_two_pow_inputLength Δ k hI hlam))
    (computableInPolyTime_entryN Δ k (hI.comp h₁) (hlam.comp h₁) (hT.comp h₁)
      (ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd input encUnary)))

/-- The size threshold is polynomial-time, in unary. -/
@[fun_prop]
theorem computableInPolyTime_sizeThreshold {I : α → CMMSAInstance} {lam : α → ℕ} (P : ℕ)
    (hI : ComputableInPolyTime I input CMMSAInstance.encoding)
    (hlam : ComputableInPolyTime lam input encUnary) :
    ComputableInPolyTime (fun a => sizeThreshold (I a) (lam a) P) input encUnary := by
  have hsize := ComputableInPolyTime.unary_mul' (ComputableInPolyTime.unary_mul'
    (ComputableInPolyTime.const 2) (CMMSAInstance.isPolyTime_threshold hI)) hlam
  unfold sizeThreshold tableLength
  exact ComputableInPolyTime.unary_div'
    (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const (P + 2))
      (ComputableInPolyTime.unary_pow_clog_const hsize 2 2))
    (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const P)
      ((ComputableInPolyTime.unary_clog_const 2).comp hsize))

/-- **The partial MCSP instance is polynomial-time from explicit tables**, for fixed `Δ`, `k` and
`P`. If `T a` has the table of every variable of `I a` under the functions `f a`, then
`toInstance (I a) Δ k (lam a) P (f a)` is computed in polynomial time from the instance `I a`, `λ`
in unary and the tables `T a`. -/
theorem computableInPolyTime_toInstance {I : α → CMMSAInstance} {lam : α → ℕ}
    {T : α → List (List Bool)} {f : (a : α) → VarFunctions (I a) (lam a)} (Δ k P : ℕ)
    (hI : ComputableInPolyTime I input CMMSAInstance.encoding)
    (hlam : ComputableInPolyTime lam input encUnary)
    (hT : ComputableInPolyTime T input (encList encBits))
    (hf : ∀ a v, IsVarTable (I a) (lam a) (f a) (T a) v) :
    ComputableInPolyTime (fun a => toInstance (I a) Δ k (lam a) P (f a)) input PartialMCSP.enc :=
  ((computableInPolyTime_tableN Δ k hI hlam hT).prod
    (computableInPolyTime_sizeThreshold P hI hlam)).of_enc_eq fun a => by
    rw [PartialMCSP.enc_apply, ← tableN_eq_ofFn (hf a) P]
    rfl

end Cslib.PartialMCSP.FromCMMSA
