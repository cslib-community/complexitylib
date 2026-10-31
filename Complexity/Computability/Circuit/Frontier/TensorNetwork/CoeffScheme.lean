/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.DescribedContraction
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.PacketEvaluator
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryDivision
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListBinaryLookup
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListLookup
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.GetD

/-!
# Coefficient extraction as a stack recursion

An entry of a packet tensor of the contraction algorithm of [OpenAI2026ETH] expands a product of
at most `L` affine row factors and keeps the coefficient of a mode monomial. The source evaluates
it in time `exp(O(L log s))` and polynomial space (§D.4.6, p. 63). This file gives that
evaluation as an instance of `Cslib.GenericRAM.StackRecursion.Scheme`, on the coefficient lists
of `A_p = (ℤ / 2 ^ p)[U] / (f)`.

The data (`CoeffScheme.Terms`) are, at a context `x : C`, the precision `(p, fl)`, the list of
the (dense indices of the) modes, and the terms of the row factors: `term x r none` is the local
term of the row `r`, and `term x r (some k)` the coefficient of the mode `k`. A node of the
recursion is a context, the rows still to expand and the exponents still needed, as a dense list.
A node with rows `r :: rs` has `m + 1` children for `m` modes: the local term (`c = 0`), and the
mode `modes[c - 1]` with its exponent lowered (`c ≥ 1`); it adds the products of their values
with the terms of `r`, skipping the modes with exponent zero. A node without rows is a leaf: one
when every exponent is zero, else zero.

* `CoeffScheme.Terms.value` is the value the recursion computes, and
  `CoeffScheme.Terms.val_value` proves that its value in `A_p` is `TensorNetwork.listCoeff` along
  the modes, at the values of the terms.
* `CoeffScheme.Terms.eval_value`: the derivation has `CoeffScheme.count m L ≤ (m + 2) ^ L` nodes
  for `L` rows (`CoeffScheme.count_le`) and at most `L` open calls, with nodes whose rows are a
  suffix of the root's and whose exponents are below the root's, and reduced values.

So the run has `exp(O(L log m))` steps on a stack of at most `L + 1` frames of polynomial size:
the time and space of §D.4.6. With polynomial-time data (`CoeffScheme.Terms.PolyTime`: the
precision with `p` in unary, the modes and the terms), every component of the scheme is
polynomial-time (`CoeffScheme.Terms.scheme_polyTime`), and one native machine computes `value`
on every node (`CoeffScheme.Terms.valueCertificate`), within time `K (m + 2) ^ L Z ^ K` and space
`K Z ^ K` for `Z = n + m + Rv + 2`, where `n` is the length of the node and `Rv` bounds the
reduced coefficient lists (`CoeffScheme.Terms.valueCertificate_le`).

## Main definitions

* `Cslib.Circuits.Frontier.CoeffScheme.Terms`: the data of coefficient extraction.
* `Cslib.Circuits.Frontier.CoeffScheme.Terms.value`: its value.
* `Cslib.Circuits.Frontier.CoeffScheme.Terms.scheme`: the recursion scheme.
* `Cslib.Circuits.Frontier.CoeffScheme.Terms.valueCertificate`: one native machine for `value`.

## Main results

* `Cslib.Circuits.Frontier.CoeffScheme.Terms.val_value`: the value is `listCoeff`.
* `Cslib.Circuits.Frontier.CoeffScheme.Terms.eval_value`: the derivation, its nodes and height.
* `Cslib.Circuits.Frontier.CoeffScheme.count_le`: the node count.
* `Cslib.Circuits.Frontier.CoeffScheme.Terms.scheme_polyTime`: polynomial-time components.
* `Cslib.Circuits.Frontier.CoeffScheme.Terms.run_scheme`: the machine computes `value`.
* `Cslib.Circuits.Frontier.CoeffScheme.Terms.valueCertificate_le`: its time and space.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §D.4.6 (p. 63).
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

namespace CoeffScheme

open Finset GaloisRingArith NativePacket Cslib.GenericRAM Cslib.GenericRAM.StackRecursion

/-- **The data of coefficient extraction**: at a context `x : C`, the precision `(p, fl)` of the
coefficient lists, the list of the modes, and the terms of the row factors (`term x r none` the
local term of the row `r`, `term x r (some k)` the coefficient of the mode `k`). -/
structure Terms (C Rw : Type) where
  /-- The precision `(p, fl)`. -/
  prec : C → ℕ × List ℕ
  /-- The modes, as dense indices. -/
  modes : C → List ℕ
  /-- The terms of the row factors. -/
  term : C → Rw → Option ℕ → List ℕ

/-- A node: a context, the rows still to expand, and the exponents still needed, as a dense
list. -/
abbrev Node (C Rw : Type) := C × (List Rw × List ℕ)

/-- The number of nodes of the derivation for `m` modes and `L` rows. -/
def count (m : ℕ) : ℕ → ℕ
  | 0 => 1
  | L + 1 => (m + 1) * count m L + 1

/-- **At most `(m + 2) ^ L` nodes.** -/
theorem count_le (m : ℕ) : ∀ L, count m L ≤ (m + 2) ^ L
  | 0 => le_rfl
  | L + 1 => by
    have h := count_le m L
    have h1 := Nat.one_le_two_pow.trans (Nat.pow_le_pow_left (show 2 ≤ m + 2 by omega) L)
    rw [count, pow_succ]
    nlinarith

namespace Terms

variable {C Rw : Type} (S : Terms C Rw)

/-- The mode of child `c ≥ 1`: `modes[c - 1]`. -/
def modeOf (x : C) (c : ℕ) : ℕ := (S.modes x).getD (c - 1) 0

/-- The exponents of child `c`: unchanged for the local term `c = 0`, and with the exponent of
the mode `modeOf c` lowered by one for `c ≥ 1`. -/
def childExps (x : C) (γ : List ℕ) (c : ℕ) : List ℕ :=
  (List.range γ.length).map fun j =>
    if c ≠ 0 ∧ j = S.modeOf x c then γ.getD j 0 - 1 else γ.getD j 0

/-- The contribution of child `c` with value `y` at the row `r`: the local term times `y` for
`c = 0`; for `c ≥ 1`, zero when the mode has exponent zero, else its coefficient times `y`. -/
def contrib (x : C) (r : Rw) (γ : List ℕ) (c : ℕ) (y : List ℕ) : List ℕ :=
  if c = 0 then mul (S.prec x).1 (S.prec x).2 (S.term x r none) y
  else if γ.getD (S.modeOf x c) 0 = 0 then zero (S.prec x).2
  else mul (S.prec x).1 (S.prec x).2 (S.term x r (some (S.modeOf x c))) y

/-- The leaf: one when every mode has exponent zero, else zero. -/
def leafValue (x : C) (γ : List ℕ) : List ℕ :=
  if (S.modes x).all (fun k => γ.getD k 0 == 0) then one (S.prec x).2 else zero (S.prec x).2

/-- **The value of coefficient extraction**, as the recursion computes it: the sum over the
children of their contributions. -/
def value (x : C) : List Rw → List ℕ → List ℕ
  | [], γ => S.leafValue x γ
  | r :: rs, γ => (List.range ((S.modes x).length + 1)).foldl
      (fun s c => add (S.prec x).1 (S.prec x).2 s
        (S.contrib x r γ c (value x rs (S.childExps x γ c)))) (zero (S.prec x).2)

/-! ### Correctness -/

theorem length_childExps (x : C) (γ : List ℕ) (c : ℕ) : (S.childExps x γ c).length = γ.length := by
  simp [childExps]

theorem getD_childExps (x : C) (γ : List ℕ) (c j : ℕ) :
    (S.childExps x γ c).getD j 0 =
      if c ≠ 0 ∧ j = S.modeOf x c then γ.getD j 0 - 1 else γ.getD j 0 := by
  by_cases hj : j < γ.length
  · rw [childExps, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map,
      List.getElem_range]
  · rw [List.getD_eq_default _ _ (by simp [childExps]; omega),
      List.getD_eq_default _ _ (by omega)]
    split_ifs <;> simp

/-- The exponents of child `c ≥ 1` are those of the node with the exponent of its mode lowered. -/
theorem getD_childExps_succ (x : C) (γ : List ℕ) (c : ℕ) :
    (fun j => (S.childExps x γ (c + 1)).getD j 0) =
      Function.update (fun j => γ.getD j 0) (S.modeOf x (c + 1))
        (γ.getD (S.modeOf x (c + 1)) 0 - 1) := by
  funext j
  rw [getD_childExps]
  by_cases hj : j = S.modeOf x (c + 1)
  · subst hj; simp
  · simp [hj]

private theorem val_foldl_range_add {p : ℕ} {fl : List ℕ} (g : ℕ → List ℕ) (n : ℕ)
    (a : List ℕ) :
    val p fl ((List.range n).foldl (fun s c => add p fl s (g c)) a) =
      val p fl a + ∑ c ∈ range n, val p fl (g c) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, val_add, ih,
      sum_range_succ, add_assoc]

private theorem sum_range_getD {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ l : List ℕ, ∑ c ∈ range l.length, f (l.getD c 0) = (l.map f).sum
  | [] => by simp
  | Z :: l => by
    rw [List.length_cons, sum_range_succ', List.map_cons, List.sum_cons, add_comm]
    simp only [List.getD_cons_succ, List.getD_cons_zero, sum_range_getD f l]

/-- **The value is `listCoeff`**: along duplicate-free modes, the value in `A_p` of `value` is
`TensorNetwork.listCoeff` at the values of the terms and the exponents of the dense list. -/
theorem val_value (x : C) (hm : (S.modes x).Nodup) :
    ∀ (rows : List Rw) (γ : List ℕ),
      val (S.prec x).1 (S.prec x).2 (S.value x rows γ) =
        TensorNetwork.listCoeff (S.modes x).toFinset
          (rows.map fun r o => val (S.prec x).1 (S.prec x).2 (S.term x r o))
          (fun k => γ.getD k 0)
  | [], γ => by
    rw [value, leafValue, List.map_nil, TensorNetwork.listCoeff_nil]
    simp only [List.all_eq_true, beq_iff_eq, List.mem_toFinset]
    split_ifs
    · exact val_one
    · exact val_zero
  | r :: rs, γ => by
    rw [value, val_foldl_range_add, val_zero, zero_add, sum_range_succ', List.map_cons,
      TensorNetwork.listCoeff_cons, add_comm]
    congr 1
    · simp only [contrib, ↓reduceIte, val_mul, childExps, Ne, not_true_eq_false, false_and]
      rw [val_value x hm rs]
      congr 2
      funext j
      by_cases hj : j < γ.length
      · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range]
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
    · rw [List.sum_toFinset _ hm, ← sum_range_getD]
      refine sum_congr rfl fun c hc => ?_
      simp only [contrib, Nat.add_one_ne_zero, ↓reduceIte, modeOf, Nat.add_sub_cancel]
      split_ifs with h0
      · exact val_zero
      · rw [val_mul, val_value x hm rs, getD_childExps_succ S x γ c]
        rfl

/-! ### The recursion scheme -/

/-- **Coefficient extraction as a recursion scheme.** A node with rows has `m + 1` children,
counted by the accumulator, and adds their contributions at its first row; a node without rows
is a leaf. -/
def scheme : Scheme (Node C Rw) (ℕ × List ℕ) (List ℕ) where
  isLeaf x := x.2.1.isEmpty
  leaf x := S.leafValue x.1 x.2.2
  start x := (0, zero (S.prec x.1).2)
  next x a :=
    if x.2.1 ≠ [] ∧ a.1 ≤ (S.modes x.1).length then
      some (x.1, (x.2.1.tail, S.childExps x.1 x.2.2 a.1))
    else none
  absorb x a y := (a.1 + 1, (x.2.1.head?).elim a.2 fun r =>
    add (S.prec x.1).1 (S.prec x.1).2 a.2 (S.contrib x.1 r x.2.2 a.1 y))
  finish _ a := a.2

/-- The invariant at the root `(x₀, (rows₀, γ₀))`: nodes keep the context, have a suffix of the
rows and exponents of the same length below those of the root; frames also have a counter at
most `m + 1` and a reduced value; values are reduced. -/
def invariant (x₀ : C) (rows₀ : List Rw) (γ₀ : List ℕ) :
    Invariant (Node C Rw) (ℕ × List ℕ) (List ℕ) :=
  ⟨fun x => x.1 = x₀ ∧ x.2.1 <:+ rows₀ ∧ x.2.2.length = γ₀.length ∧
      ∀ j, x.2.2.getD j 0 ≤ γ₀.getD j 0,
    fun x a => (x.1 = x₀ ∧ x.2.1 <:+ rows₀ ∧ x.2.2.length = γ₀.length ∧
      ∀ j, x.2.2.getD j 0 ≤ γ₀.getD j 0) ∧ a.1 ≤ (S.modes x₀).length + 1 ∧
      SumOps.galois.Reduced (S.prec x₀) a.2,
    fun y => SumOps.galois.Reduced (S.prec x₀) y⟩

/-- The leaf value is reduced. -/
theorem reduced_leafValue (x : C) (γ : List ℕ) :
    SumOps.galois.Reduced (S.prec x) (S.leafValue x γ) := by
  unfold leafValue
  split_ifs
  · exact SumOps.galois.reduced_one (S.prec x)
  · exact SumOps.galois.reduced_zero (S.prec x)

/-- **The derivation of coefficient extraction.** From a node whose rows are a suffix of the
root's and whose exponents are below the root's, the recursion computes `value`, with
`count m L` nodes for `L` rows and at most `L` open calls. -/
theorem eval_value (x₀ : C) (rows₀ : List Rw) (γ₀ : List ℕ) :
    ∀ (rows : List Rw) (γ : List ℕ), rows <:+ rows₀ → γ.length = γ₀.length →
      (∀ j, γ.getD j 0 ≤ γ₀.getD j 0) →
      ∃ h ≤ rows.length, S.scheme.Eval (S.invariant x₀ rows₀ γ₀) (x₀, (rows, γ))
        (S.value x₀ rows γ) (count (S.modes x₀).length rows.length) h
  | [], γ, hs, hl, hγ =>
    ⟨0, le_rfl, Scheme.Eval.leaf (R := S.scheme) ⟨rfl, hs, hl, hγ⟩ rfl
      (S.reduced_leafValue x₀ γ)⟩
  | r :: rs, γ, hs, hl, hγ => by
    set m := (S.modes x₀).length
    set acc : ℕ → ℕ × List ℕ := fun c => (c, (List.range c).foldl
      (fun s c => add (S.prec x₀).1 (S.prec x₀).2 s
        (S.contrib x₀ r γ c (S.value x₀ rs (S.childExps x₀ γ c)))) (zero (S.prec x₀).2))
    have hred (c : ℕ) : SumOps.galois.Reduced (S.prec x₀) (acc c).2 :=
      SumOps.galois.reduced_foldl (S.prec x₀) _ (SumOps.galois.reduced_add (S.prec x₀)) _ _
        (SumOps.galois.reduced_zero (S.prec x₀))
    have hchild (c : ℕ) := eval_value x₀ rows₀ γ₀ rs (S.childExps x₀ γ c)
      ((List.suffix_cons r rs).trans hs) (by rw [length_childExps, hl])
      (fun j => by have := hγ j; rw [getD_childExps]; split_ifs <;> omega)
    choose hgt hhgt heval using hchild
    have hnode : (S.invariant x₀ rows₀ γ₀).node (x₀, (r :: rs, γ)) := ⟨rfl, hs, hl, hγ⟩
    obtain ⟨h, hh, hloop⟩ := Scheme.Loop.counted (R := S.scheme)
      (I := S.invariant x₀ rows₀ γ₀) (x := (x₀, (r :: rs, γ))) (acc := acc)
      (child := fun c => (x₀, (rs, S.childExps x₀ γ c)))
      (val := fun c => S.value x₀ rs (S.childExps x₀ γ c))
      (nodes := fun _ => count m rs.length) (height := hgt) (m + 1) rs.length
      (fun c hc => by
        simp only [scheme, acc, ne_eq, reduceCtorEq, not_false_eq_true, true_and,
          List.tail_cons, ite_eq_left_iff, not_le]
        omega)
      (by simp [scheme, acc, m])
      (fun c hc => by
        simp only [scheme, acc, List.head?_cons, Option.elim_some, List.range_succ,
          List.foldl_append, List.foldl_cons, List.foldl_nil])
      (fun c _ => heval c)
      (fun c hc => ⟨hnode, by simp only [acc]; omega, hred c⟩)
      (fun c _ => hhgt c)
    have hstart : S.scheme.start (x₀, (r :: rs, γ)) = acc 0 := by simp [scheme, acc]
    rw [← hstart] at hloop
    refine ⟨h + 1, by simp only [List.length_cons]; omega, ?_⟩
    have := Scheme.Eval.call (R := S.scheme) (I := S.invariant x₀ rows₀ γ₀)
      (x := (x₀, (r :: rs, γ))) hnode rfl hloop (hred (m + 1))
    rw [sum_const, card_range, smul_eq_mul] at this
    exact this

/-- **The root**: from `(x, (rows, γ))`, the recursion computes `value x rows γ` with at most
`(m + 2) ^ L` nodes for `m` modes and `L` rows. -/
theorem eval_root (x : C) (rows : List Rw) (γ : List ℕ) :
    ∃ h ≤ rows.length, S.scheme.Eval (S.invariant x rows γ) (x, (rows, γ)) (S.value x rows γ)
      (count (S.modes x).length rows.length) h :=
  S.eval_value x rows γ rows γ (List.suffix_refl _) rfl fun _ => le_rfl


/-! ### Polynomial-time components -/

section PolyTime

open Turing.MultiTapeTM

variable {encC : C ↪ List Bool} {encRw : Rw ↪ List Bool}

/-- The encoding of a node: the context, the rows and the exponents in binary. -/
abbrev encNode (encC : C ↪ List Bool) (encRw : Rw ↪ List Bool) : Node C Rw ↪ List Bool :=
  encPair encC (encPair (encList encRw) (encList encNat))

/-- The encoding of an accumulator: the counter and the sum, in binary. -/
abbrev encAcc : ℕ × List ℕ ↪ List Bool := encPair encNat (encList encNat)

/-- **Polynomial-time data**: the precision with `p` in unary, the modes, and the terms. -/
structure PolyTime (encC : C ↪ List Bool) (encRw : Rw ↪ List Bool) : Prop where
  prec : ComputableInPolyTime S.prec encC (encPair encUnary (encList encNat))
  modes : ComputableInPolyTime S.modes encC (encList encNat)
  term : ComputableInPolyTime (fun z : C × Rw × Option ℕ => S.term z.1 z.2.1 z.2.2)
    (encPair encC (encPair encRw (encOption encNat))) (encList encNat)

variable {S} (hS : S.PolyTime encC encRw)
include hS

section Lift

variable {α : Type} {encIn : α ↪ List Bool} {x : α → C}
  (hx : ComputableInPolyTime x encIn encC)
include hx

theorem precision_polyTime : ComputableInPolyTime (fun a => (S.prec (x a)).1) encIn encUnary :=
  (ComputableInPolyTime.fst _ _).comp (hS.prec.comp hx)

theorem coeffs_polyTime : ComputableInPolyTime (fun a => (S.prec (x a)).2) encIn
    (encList encNat) :=
  (ComputableInPolyTime.snd _ _).comp (hS.prec.comp hx)

theorem zero_polyTime : ComputableInPolyTime (fun a => zero (S.prec (x a)).2) encIn
    (encList encNat) :=
  computableInPolyTime_tabulate (g := fun _ _ => 0)
    ((ComputableInPolyTime.length_list encNat).comp (coeffs_polyTime hS hx))
    (ComputableInPolyTime.const 0)

theorem modeOf_polyTime {c : α → ℕ} (hc : ComputableInPolyTime c encIn encNat) :
    ComputableInPolyTime (fun a => S.modeOf (x a) (c a)) encIn encNat :=
  ComputableInPolyTime.listGetD_binary (encA := encNat) 0 (hS.modes.comp hx)
    (ComputableInPolyTime.binary_sub' hc (ComputableInPolyTime.const 1))

theorem childExps_polyTime {γ : α → List ℕ} {c : α → ℕ}
    (hγ : ComputableInPolyTime γ encIn (encList encNat))
    (hc : ComputableInPolyTime c encIn encNat) :
    ComputableInPolyTime (fun a => S.childExps (x a) (γ a) (c a)) encIn (encList encNat) := by
  have h1 := ComputableInPolyTime.fst encIn encUnary
  have h2 := ComputableInPolyTime.snd encIn encUnary
  have hget := computableInPolyTime_getD (hγ.comp h1) h2
  have hf : ComputableInPolyTime (fun q : α × ℕ =>
      if c q.1 = 0 then (γ q.1).getD q.2 0 else
        if q.2 = S.modeOf (x q.1) (c q.1) then (γ q.1).getD q.2 0 - 1 else (γ q.1).getD q.2 0)
      (encPair encIn encUnary) encNat :=
    (ComputableInPolyTime.ite (ComputableInPolyTime.beq (hc.comp h1)
      (ComputableInPolyTime.const 0)) hget
      (ComputableInPolyTime.ite (ComputableInPolyTime.beq
        (ComputableInPolyTime.unary_to_binary.comp h2) (modeOf_polyTime hS (hx.comp h1)
          (hc.comp h1)))
        (ComputableInPolyTime.binary_sub' hget (ComputableInPolyTime.const 1)) hget)).of_enc_eq
      fun q => by
        by_cases h0 : c q.1 = 0
        · simp [h0]
        · by_cases hj : q.2 = S.modeOf (x q.1) (c q.1) <;> simp [h0, hj]
  refine (ComputableInPolyTime.mapWithInput (f := fun a j =>
      if c a = 0 then (γ a).getD j 0 else
        if j = S.modeOf (x a) (c a) then (γ a).getD j 0 - 1 else (γ a).getD j 0)
    (ComputableInPolyTime.range.comp ((ComputableInPolyTime.length_list encNat).comp hγ))
    hf).of_enc_eq fun a => ?_
  refine congrArg _ (List.map_congr_left fun j _ => ?_)
  by_cases h0 : c a = 0
  · simp [h0]
  · by_cases hj : j = S.modeOf (x a) (c a) <;> simp [h0, hj]

theorem contrib_polyTime {r : α → Rw} {γ : α → List ℕ} {c : α → ℕ} {y : α → List ℕ}
    (hr : ComputableInPolyTime r encIn encRw)
    (hγ : ComputableInPolyTime γ encIn (encList encNat))
    (hc : ComputableInPolyTime c encIn encNat)
    (hy : ComputableInPolyTime y encIn (encList encNat)) :
    ComputableInPolyTime (fun a => S.contrib (x a) (r a) (γ a) (c a) (y a)) encIn
      (encList encNat) := by
  have hp := precision_polyTime hS hx
  have hfl := coeffs_polyTime hS hx
  have hk := modeOf_polyTime hS hx hc
  have hterm (o : α → Option ℕ) (ho : ComputableInPolyTime o encIn (encOption encNat)) :
      ComputableInPolyTime (fun a => S.term (x a) (r a) (o a)) encIn (encList encNat) :=
    hS.term.comp (hx.prod (hr.prod ho))
  exact (ComputableInPolyTime.ite (ComputableInPolyTime.beq hc (ComputableInPolyTime.const 0))
    (computableInPolyTime_mul hp hfl (hterm _ (ComputableInPolyTime.const none)) hy)
    (ComputableInPolyTime.ite (ComputableInPolyTime.beq
      (ComputableInPolyTime.listGetD_binary (encA := encNat) 0 hγ hk)
        (ComputableInPolyTime.const 0))
      (zero_polyTime hS hx)
      (computableInPolyTime_mul hp hfl
        (hterm _ ((ComputableInPolyTime.optionSome encNat).comp hk)) hy))).of_enc_eq
    fun a => by
      by_cases h0 : c a = 0
      · simp [contrib, h0]
      · simp [contrib, h0]

end Lift

/-- The leaf is polynomial-time. -/
theorem leafValue_polyTime :
    ComputableInPolyTime (fun x : Node C Rw => S.leafValue x.1 x.2.2) (encNode encC encRw)
      (encList encNat) := by
  have hx := ComputableInPolyTime.fst encC (encPair (encList encRw) (encList encNat))
  have hγ := (ComputableInPolyTime.snd (encList encRw) (encList encNat)).comp
    (ComputableInPolyTime.snd encC (encPair (encList encRw) (encList encNat)))
  have htest : ComputableInPolyTime (fun z : Node C Rw × ℕ => z.1.2.2.getD z.2 0 == 0)
      (encPair (encNode encC encRw) encNat) encBool :=
    ComputableInPolyTime.beq (ComputableInPolyTime.listGetD_binary (encA := encNat) 0
      (hγ.comp (ComputableInPolyTime.fst _ _)) (ComputableInPolyTime.snd _ _))
      (ComputableInPolyTime.const 0)
  exact ComputableInPolyTime.ite (ComputableInPolyTime.allWithInput (hS.modes.comp hx) htest)
    (computableInPolyTime_one (coeffs_polyTime hS hx)) (zero_polyTime hS hx)

/-- **The components of coefficient extraction are polynomial-time.** -/
theorem scheme_polyTime : S.scheme.PolyTime (encNode encC encRw) encAcc (encList encNat) where
  isLeaf := (ComputableInPolyTime.listIsEmpty (encA := encRw)).comp
    ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _))
  start := (ComputableInPolyTime.const 0).prod (zero_polyTime hS (ComputableInPolyTime.fst _ _))
  next := by
    have hn := ComputableInPolyTime.fst (encNode encC encRw) encAcc
    have hx := (ComputableInPolyTime.fst _ _).comp hn
    have hrows := (ComputableInPolyTime.fst (encList encRw) (encList encNat)).comp
      ((ComputableInPolyTime.snd _ _).comp hn)
    have hγ := (ComputableInPolyTime.snd (encList encRw) (encList encNat)).comp
      ((ComputableInPolyTime.snd _ _).comp hn)
    have hc := (ComputableInPolyTime.fst encNat (encList encNat)).comp
      (ComputableInPolyTime.snd (encNode encC encRw) encAcc)
    have hm := ComputableInPolyTime.unary_to_binary.comp
      ((ComputableInPolyTime.length_list encNat).comp (hS.modes.comp hx))
    have hsome : ComputableInPolyTime (fun z : Node C Rw × (ℕ × List ℕ) =>
        some (z.1.1, (z.1.2.1.tail, S.childExps z.1.1 z.1.2.2 z.2.1)))
        (encPair (encNode encC encRw) encAcc) (encOption (encNode encC encRw)) :=
      (ComputableInPolyTime.optionSome (encNode encC encRw)).comp
        (hx.prod (((ComputableInPolyTime.tail (encA := encRw)).comp hrows).prod
          (childExps_polyTime hS hx hγ hc)))
    refine (ComputableInPolyTime.ite ((ComputableInPolyTime.listIsEmpty (encA := encRw)).comp hrows)
      (ComputableInPolyTime.const none)
      (ComputableInPolyTime.ite (ComputableInPolyTime.binary_le' hc hm) hsome
        (ComputableInPolyTime.const none))).of_enc_eq fun z => ?_
    by_cases he : z.1.2.1 = []
    · simp [scheme, he]
    · by_cases hle : z.2.1 ≤ (S.modes z.1.1).length <;> simp [scheme, he, hle]
  absorb := by
    have hq := ComputableInPolyTime.fst (encPair (encNode encC encRw) encAcc) (encList encNat)
    have hn := (ComputableInPolyTime.fst (encNode encC encRw) encAcc).comp hq
    have ha := (ComputableInPolyTime.snd (encNode encC encRw) encAcc).comp hq
    have hy := ComputableInPolyTime.snd (encPair (encNode encC encRw) encAcc) (encList encNat)
    have hx := (ComputableInPolyTime.fst _ _).comp hn
    have hrows := (ComputableInPolyTime.fst (encList encRw) (encList encNat)).comp
      ((ComputableInPolyTime.snd _ _).comp hn)
    have hγ := (ComputableInPolyTime.snd (encList encRw) (encList encNat)).comp
      ((ComputableInPolyTime.snd _ _).comp hn)
    have hc := (ComputableInPolyTime.fst encNat (encList encNat)).comp ha
    have hs := (ComputableInPolyTime.snd encNat (encList encNat)).comp ha
    let E := encPair (encPair (encNode encC encRw) encAcc) (encList encNat)
    have hbody : ComputableInPolyTime
        (fun w : ((Node C Rw × (ℕ × List ℕ)) × List ℕ) × Rw =>
          add (S.prec w.1.1.1.1).1 (S.prec w.1.1.1.1).2 w.1.1.2.2
            (S.contrib w.1.1.1.1 w.2 w.1.1.1.2.2 w.1.1.2.1 w.1.2)) (encPair E encRw)
        (encList encNat) := by
      have h1 := ComputableInPolyTime.fst E encRw
      exact computableInPolyTime_add (precision_polyTime hS (hx.comp h1))
        (coeffs_polyTime hS (hx.comp h1)) (hs.comp h1)
        (contrib_polyTime hS (hx.comp h1) (ComputableInPolyTime.snd E encRw) (hγ.comp h1)
          (hc.comp h1) (hy.comp h1))
    exact (ComputableInPolyTime.binary_add.comp (hc.prod (ComputableInPolyTime.const 1))).prod
      (ComputableInPolyTime.optionElimWithInput ((ComputableInPolyTime.head? encRw).comp hrows)
        hs hbody)
  finish := (ComputableInPolyTime.snd encNat (encList encNat)).comp (ComputableInPolyTime.snd _ _)


/-! ### The native machine and its resources -/

/-- The number of steps: `2 (m + 2) ^ L` for `m` modes and `L` rows, at least the `2 N - 1`
steps of a derivation with `N ≤ (m + 2) ^ L` nodes. -/
def fuel (x : Node C Rw) : ℕ := 2 * ((S.modes x.1).length + 2) ^ x.2.1.length

theorem fuel_polyTime : ComputableInPolyTime S.fuel (encNode encC encRw) encNat := by
  have hx := ComputableInPolyTime.fst encC (encPair (encList encRw) (encList encNat))
  have hrows := (ComputableInPolyTime.fst (encList encRw) (encList encNat)).comp
    (ComputableInPolyTime.snd encC (encPair (encList encRw) (encList encNat)))
  exact ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const 2)
    (ComputableInPolyTime.binary_pow' (ComputableInPolyTime.binary_add.comp
      ((ComputableInPolyTime.unary_to_binary.comp ((ComputableInPolyTime.length_list encNat).comp
        (hS.modes.comp hx))).prod (ComputableInPolyTime.const 2)))
      ((ComputableInPolyTime.length_list encRw).comp hrows))

/-- The leaf certificate. -/
noncomputable def leafCertificate :
    NativeCertificate S.scheme.leaf (encNode encC encRw) (encList encNat) :=
  NativeCertificate.ofPolyTime (leafValue_polyTime hS)

/-- **One native machine for coefficient extraction**, from polynomial-time data: the clocked
run of the scheme from the node itself. -/
noncomputable def runCertificate :
    NativeCertificate (S.scheme.run S.fuel id) (encNode encC encRw)
      (encOption (encList encNat)) :=
  Scheme.certificate (scheme_polyTime hS) (leafCertificate hS)
    (NativeCertificate.ofPolyTime (fuel_polyTime hS))
    (NativeCertificate.ofPolyTime ComputableInPolyTime.id')

omit hS in
/-- **The machine computes `value`.** -/
theorem run_scheme (x : Node C Rw) : S.scheme.run S.fuel id x = some (S.value x.1 x.2.1 x.2.2) := by
  obtain ⟨h, -, he⟩ := S.eval_root x.1 x.2.1 x.2.2
  refine Scheme.run_eq_some he ?_
  have := count_le (S.modes x.1).length x.2.1.length
  simp only [fuel]
  omega

/-- **Coefficient extraction, as a native certificate** for `value` on every node. -/
noncomputable def valueCertificate :
    NativeCertificate (fun x : Node C Rw => S.value x.1 x.2.1 x.2.2) (encNode encC encRw)
      (encList encNat) :=
  (NativeCertificate.post (runCertificate hS)
    (ComputableInDegree.getD (enc₁ := encList encNat) (enc := encOption (encList encNat))
      []).inO_one).congr fun x => by simp [run_scheme]

@[simp] theorem valueCertificate_time :
    (valueCertificate hS).time = (runCertificate hS).time := rfl

@[simp] theorem valueCertificate_space :
    (valueCertificate hS).space = (runCertificate hS).space := rfl

omit hS in
private theorem sum_map_le_of_getD_le {g : ℕ → ℕ} (hg : Monotone g) :
    ∀ (γ γ₀ : List ℕ), γ.length = γ₀.length → (∀ j, γ.getD j 0 ≤ γ₀.getD j 0) →
      (γ.map g).sum ≤ (γ₀.map g).sum
  | [], [], _, _ => le_rfl
  | a :: γ, b :: γ₀, hl, h => by
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (hg (by simpa using h 0))
      (sum_map_le_of_getD_le hg γ γ₀ (by simpa using hl) fun j => by simpa using h (j + 1))

omit hS in
/-- A node of the derivation from a root is at most as long as the root. -/
theorem length_encNode_le {x₀ : C} {rows₀ : List Rw} {γ₀ : List ℕ} {x : Node C Rw}
    (hx : (S.invariant x₀ rows₀ γ₀).node x) :
    (encNode encC encRw x).length ≤ (encNode encC encRw (x₀, (rows₀, γ₀))).length := by
  obtain ⟨hx₀, ⟨pre, hpre⟩, hl, hγ⟩ := hx
  obtain ⟨x', rs, γ⟩ := x
  simp only at hx₀ hpre hl hγ
  subst hx₀ hpre
  have h1 : (encList encRw rs).length ≤ (encList encRw (pre ++ rs)).length := by
    simp only [length_encList, List.map_append, List.sum_append]
    omega
  have h2 : (encList encNat γ).length ≤ (encList encNat γ₀).length := by
    simp only [length_encList]
    exact sum_map_le_of_getD_le (fun a b hab => by
      change 2 * a.bits.length + 1 ≤ 2 * b.bits.length + 1
      rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]
      exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.size_le_size hab)) 1) γ γ₀ hl hγ
  simp only [length_encPair]
  omega

omit hS in
private theorem length_encNat_lt {y P : ℕ} (h : y < 2 ^ P) : (encNat y).length ≤ P := by
  have h' := Nat.size_le.mpr h
  rw [← Nat.size_eq_bits_len] at h'
  exact h'

/-- **The resources of coefficient extraction.** There is `K` such that on a node of length `n`
with `m` modes and `L` rows, if the reduced values of its precision are at most `Rv` bits long,
then with `Z = n + m + Rv + 2` the time is at most `K (m + 2) ^ L Z ^ K` and the space at most
`K Z ^ K`: time `exp(O(L log m))` times a polynomial, in polynomial space. -/
theorem valueCertificate_le :
    ∃ K : ℕ, ∀ (x : Node C Rw) (Rv : ℕ),
      (∀ y, SumOps.galois.Reduced (S.prec x.1) y → (encList encNat y).length ≤ Rv) →
      (valueCertificate hS).time x ≤ K * ((S.modes x.1).length + 2) ^ x.2.1.length *
          ((encNode encC encRw x).length + (S.modes x.1).length + Rv + 2) ^ K ∧
        (valueCertificate hS).space x ≤
          K * ((encNode encC encRw x).length + (S.modes x.1).length + Rv + 2) ^ K := by
  obtain ⟨K₀, hK₀⟩ := Scheme.certificate_le (scheme_polyTime hS) (leafCertificate hS)
  have hL := NativeCertificate.ofPolyTime_isPolynomial (leafValue_polyTime hS)
  have hF := NativeCertificate.ofPolyTime_isPolynomial (fuel_polyTime hS)
  have hR := NativeCertificate.ofPolyTime_isPolynomial
    (ComputableInPolyTime.id' (encIn := encNode encC encRw))
  obtain ⟨cl, dl, hlt⟩ := hL.1.exists_le
  obtain ⟨cl', dl', hls⟩ := hL.2.exists_le
  obtain ⟨cf, df, hft⟩ := hF.1.exists_le
  obtain ⟨cf', df', hfs⟩ := hF.2.exists_le
  obtain ⟨cr, dr, hrt⟩ := hR.1.exists_le
  obtain ⟨cr', dr', hrs⟩ := hR.2.exists_le
  obtain ⟨D, hD⟩ : ∃ D, D = 2 * K₀ + dl + dl' + df + df' + dr + dr' + 4 := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = cf + cr + 2 + 3 * (K₀ * 8 ^ K₀ + cl + 9) := ⟨_, rfl⟩
  obtain ⟨G', hG'⟩ : ∃ G', G' = cf' + cr' + 2 + K₀ * 8 ^ K₀ + cl' + 2 := ⟨_, rfl⟩
  refine ⟨G + G' + D, fun x Rv hRv => ?_⟩
  obtain ⟨x₀, rows₀, γ₀⟩ := x
  simp only
  obtain ⟨n, hn⟩ : ∃ n, n = (encNode encC encRw (x₀, (rows₀, γ₀))).length := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = (S.modes x₀).length := ⟨_, rfl⟩
  obtain ⟨L, hLen⟩ : ∃ L, L = rows₀.length := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = n + m + Rv + 2 := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = Z ^ D := ⟨_, rfl⟩
  rw [← hn, ← hm, ← hLen, ← hZ]
  have hZ2 : 2 ≤ Z := by omega
  have hLn : L ≤ n := by
    have := length_le_length_encList encRw rows₀
    rw [hn, hLen]
    simp only [length_encPair]
    omega
  have hpowZ {a : ℕ} (ha : a ≤ D) : Z ^ a ≤ W := by
    rw [hW]; exact Nat.pow_le_pow_right (by omega) ha
  have hZW : Z ≤ W := by
    calc Z = Z ^ 1 := (pow_one Z).symm
      _ ≤ W := hpowZ (by omega)
  have hn1 {c e : ℕ} (he : e ≤ D) : c * (n + 1) ^ e ≤ c * W :=
    Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by omega) _).trans (hpowZ he))
  have hP : 1 ≤ (m + 2) ^ L := Nat.one_le_pow _ _ (by omega)
  -- The derivation and the bounds on its nodes, frames and values.
  obtain ⟨h, hh, he⟩ := S.eval_root x₀ rows₀ γ₀
  have hnode (x : Node C Rw) (hx : (S.invariant x₀ rows₀ γ₀).node x) :
      (encNode encC encRw x).length ≤ n := hn ▸ length_encNode_le (S := S) hx
  have hres := hK₀ (NativeCertificate.ofPolyTime (fuel_polyTime hS))
    (NativeCertificate.ofPolyTime ComputableInPolyTime.id') (S.invariant x₀ rows₀ γ₀) (3 * Z)
    (cl * Z ^ dl) (cl' * Z ^ dl')
    (fun x hx => ⟨(hnode x hx).trans (by omega), fun _ =>
      ⟨(hlt x).trans (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by
          have := hnode x hx; omega) _))),
        (hls x).trans (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by
          have := hnode x hx; omega) _)))⟩⟩)
    (fun x a ha => by
      obtain ⟨hx, ha1, ha2⟩ := ha
      have h1 := hnode x hx
      have h2 : (encNat a.1).length ≤ m + 2 :=
        length_encNat_lt (lt_of_le_of_lt (hm ▸ ha1) (by
          have := Nat.lt_two_pow_self (n := m + 2); omega))
      have h3 := hRv a.2 ha2
      have h4 : (encPair (encNode encC encRw) encAcc (x, a)).length =
          2 * (encNode encC encRw x).length + 1 + (encAcc a).length := length_encPair (x, a)
      have h5 : (encAcc a).length = 2 * (encNat a.1).length + 1 + (encList encNat a.2).length :=
        length_encPair a
      omega)
    (fun y hy => by have := hRv y hy; omega)
    (x₀, (rows₀, γ₀)) _ _ _ he
  obtain ⟨htime, hspace⟩ := hres
  -- The fuel and its clock.
  have hfuel : S.fuel (x₀, (rows₀, γ₀)) = 2 * (m + 2) ^ L := by simp only [fuel, hm, hLen]
  have hfuelLen : (encNat (S.fuel (x₀, (rows₀, γ₀)))).length ≤ 2 * Z ^ 2 := by
    have hpow : (m + 2) ^ L < 2 ^ ((m + 2) * L + 1) := by
      calc (m + 2) ^ L ≤ (2 ^ (m + 2)) ^ L :=
            Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
        _ = 2 ^ ((m + 2) * L) := (pow_mul _ _ _).symm
        _ < 2 ^ ((m + 2) * L + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have h1 : S.fuel (x₀, (rows₀, γ₀)) < 2 ^ ((m + 2) * L + 2) := by
      rw [hfuel, pow_succ]; omega
    have h2 := length_encNat_lt h1
    have h3 : (m + 2) * L ≤ Z * Z := Nat.mul_le_mul (by omega) (by omega)
    have h4 : 4 ≤ Z * Z := Nat.mul_le_mul hZ2 hZ2
    rw [sq]
    omega
  have hclock : ((encNat (S.fuel (x₀, (rows₀, γ₀)))).length + 1) ^ 2 ≤ 9 * W := by
    have hZsq : 1 ≤ Z ^ 2 := Nat.one_le_pow _ _ (by omega)
    calc ((encNat (S.fuel (x₀, (rows₀, γ₀)))).length + 1) ^ 2 ≤ (3 * Z ^ 2) ^ 2 :=
          Nat.pow_le_pow_left (by omega) 2
      _ = 9 * Z ^ 4 := by ring
      _ ≤ 9 * W := Nat.mul_le_mul_left _ (hpowZ (by omega))
  have hstack : K₀ * ((h + 1) * (3 * Z + 1)) ^ K₀ ≤ K₀ * 8 ^ K₀ * W := by
    have h1 : (h + 1) * (3 * Z + 1) ≤ 8 * Z ^ 2 := by
      have hh2 : h + 1 ≤ 2 * Z := by omega
      have hZZ : Z ≤ Z ^ 2 := Nat.le_self_pow (by norm_num) Z
      calc (h + 1) * (3 * Z + 1) ≤ (2 * Z) * (3 * Z + 1) := Nat.mul_le_mul_right _ hh2
        _ = 6 * Z ^ 2 + 2 * Z := by ring
        _ ≤ 8 * Z ^ 2 := by omega
    calc K₀ * ((h + 1) * (3 * Z + 1)) ^ K₀ ≤ K₀ * (8 * Z ^ 2) ^ K₀ :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _)
      _ = K₀ * 8 ^ K₀ * Z ^ (2 * K₀) := by rw [Nat.mul_pow, ← pow_mul]; ring
      _ ≤ K₀ * 8 ^ K₀ * W := Nat.mul_le_mul_left _ (hpowZ (by omega))
  have hTL : cl * Z ^ dl ≤ cl * W := Nat.mul_le_mul_left _ (hpowZ (by omega))
  have hSL : cl' * Z ^ dl' ≤ cl' * W := Nat.mul_le_mul_left _ (hpowZ (by omega))
  have hcf := (hft (x₀, (rows₀, γ₀))).trans (hn ▸ hn1 (c := cf) (show df ≤ D by omega))
  have hcr := (hrt (x₀, (rows₀, γ₀))).trans (hn ▸ hn1 (c := cr) (show dr ≤ D by omega))
  have hcf' := (hfs (x₀, (rows₀, γ₀))).trans (hn ▸ hn1 (c := cf') (show df' ≤ D by omega))
  have hcr' := (hrs (x₀, (rows₀, γ₀))).trans (hn ▸ hn1 (c := cr') (show dr' ≤ D by omega))
  rw [← hn] at htime hspace
  have hWK : W ≤ Z ^ (G + G' + D) := hW ▸ Nat.pow_le_pow_right (by omega) (by omega)
  have hnW : n ≤ W := by omega
  constructor
  · rw [valueCertificate_time]
    unfold runCertificate
    obtain ⟨P, hPdef⟩ : ∃ P, P = (m + 2) ^ L := ⟨_, rfl⟩
    rw [← hPdef] at hP ⊢
    obtain ⟨Y, hY⟩ : ∃ Y, Y = K₀ * ((h + 1) * (3 * Z + 1)) ^ K₀ + cl * Z ^ dl +
        ((encNat (S.fuel (x₀, (rows₀, γ₀)))).length + 1) ^ 2 := ⟨_, rfl⟩
    rw [← hY] at htime
    have hfP : (S.fuel (x₀, (rows₀, γ₀)) + 1) * Y = (2 * P + 1) * Y := by rw [hfuel, hPdef]
    have hstep : Y ≤ (K₀ * 8 ^ K₀ + cl + 9) * W := by
      have e : (K₀ * 8 ^ K₀ + cl + 9) * W = K₀ * 8 ^ K₀ * W + cl * W + 9 * W := by ring
      omega
    have h1 := Nat.mul_le_mul_left (2 * P + 1) hstep
    have h2 : (2 * P + 1) * ((K₀ * 8 ^ K₀ + cl + 9) * W) ≤
        P * (3 * (K₀ * 8 ^ K₀ + cl + 9) * W) := by
      have : 2 * P + 1 ≤ 3 * P := by omega
      calc (2 * P + 1) * ((K₀ * 8 ^ K₀ + cl + 9) * W)
          ≤ (3 * P) * ((K₀ * 8 ^ K₀ + cl + 9) * W) := Nat.mul_le_mul_right _ this
        _ = P * (3 * (K₀ * 8 ^ K₀ + cl + 9) * W) := by ring
    have h3 : cf * W + cr * W + 2 * W ≤ P * ((cf + cr + 2) * W) := by
      have e : cf * W + cr * W + 2 * W = (cf + cr + 2) * W := by ring
      rw [e]; exact Nat.le_mul_of_pos_left _ hP
    have h4 : P * ((cf + cr + 2) * W) + P * (3 * (K₀ * 8 ^ K₀ + cl + 9) * W) = P * (G * W) := by
      rw [hG]; ring
    calc _ ≤ P * (G * W) := by omega
      _ ≤ (G + G' + D) * P * Z ^ (G + G' + D) := by
          rw [show (G + G' + D) * P * Z ^ (G + G' + D) = P * ((G + G' + D) * Z ^ (G + G' + D)) by
            ring]
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) hWK)
  · rw [valueCertificate_space]
    unfold runCertificate
    have h1 : (encNat (S.fuel (x₀, (rows₀, γ₀)))).length ≤ 2 * W := by
      have := hpowZ (show 2 ≤ D by omega); omega
    calc _ ≤ cf' * W + cr' * W + 2 * W + K₀ * 8 ^ K₀ * W + cl' * W + 2 * W := by omega
      _ = G' * W := by rw [hG']; ring
      _ ≤ (G + G' + D) * Z ^ (G + G' + D) := Nat.mul_le_mul (by omega) hWK

end PolyTime

end Terms

end CoeffScheme

end Cslib.Circuits.Frontier
