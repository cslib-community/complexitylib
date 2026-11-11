/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.TreeEval.Reader.Defs
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.BigOperators.Fin
import CslibFrontier.Foundations.FieldTheory.Finite.Basic

/-!
# Residues and registers of the Tree Evaluation read machine

The read machine computes with natural numbers below a prime `p`; this file relates them to
`ZMod p`. The residue operations cast to the field operations, and the register operations to
those of `Cslib.TreeEval.Iter` on the registers read as field elements. The weight of a table entry
casts to the value of the indicator polynomial of its inputs, so that the sums over the table give
the multilinear extension of a gate.

## Main definitions

* `Cslib.TreeEval.Reader.Regs.toState`: the registers read in `ZMod p`.
* `Cslib.TreeEval.Reader.Regs.WF`: registers of length `ℓ` holding residues below `p`.

## Main results

* `Cslib.TreeEval.Reader.cast_weight`: the weight casts to the product of `x` or `1 - x` over the
  bits of the inputs.
* `Cslib.TreeEval.Reader.eval_gatePoly_eq_sum`: the multilinear extension of an output bit of a
  gate as a sum over the table indices `k < 4^ℓ`.

## References

* [J. Cook and I. Mertz, *Tree Evaluation is in Space O(log n · log log n)*][CookMertz2024]
* [O. Goldreich, *On the Cook–Mertz Tree Evaluation procedure*][Goldreich2024TreeEval],
  Algorithm 1, which the machine runs.
-/

@[expose] public section

open MvPolynomial Cslib.BitString

namespace Cslib.TreeEval

namespace Reader

variable {p : ℕ}

/-! ### Residues -/

section Cast

@[simp] theorem cast_addMod (a b : ℕ) : ((addMod p a b : ℕ) : ZMod p) = a + b := by
  simp [addMod]

@[simp] theorem cast_mulMod (a b : ℕ) : ((mulMod p a b : ℕ) : ZMod p) = a * b := by
  simp [mulMod]

@[simp] theorem cast_negMod [NeZero p] (a : ℕ) : ((negMod p a : ℕ) : ZMod p) = -a := by
  rw [negMod, ZMod.natCast_mod, Nat.cast_sub (Nat.mod_lt _ (NeZero.pos p)).le, ZMod.natCast_self,
    ZMod.natCast_mod, zero_sub]

@[simp] theorem cast_powMod (a n : ℕ) : ((powMod p a n : ℕ) : ZMod p) = (a : ZMod p) ^ n := by
  induction n with
  | zero => simp [powMod]
  | succ n ih => simp [powMod, ih, pow_succ]

@[simp] theorem cast_chi [NeZero p] (b : Bool) (x : ℕ) :
    ((chi p b x : ℕ) : ZMod p) = if b then (x : ZMod p) else 1 - x := by
  cases b <;> simp [chi, sub_eq_add_neg]

private theorem mulMod_lt (hp : 0 < p) (a b : ℕ) : mulMod p a b < p := Nat.mod_lt _ hp
private theorem addMod_lt (hp : 0 < p) (a b : ℕ) : addMod p a b < p := Nat.mod_lt _ hp

variable [Fact p.Prime]

@[simp] theorem cast_sgnVal (neg : Bool) : ((sgnVal p neg : ℕ) : ZMod p) = Iter.sgn neg := by
  cases neg
  · simp [sgnVal, Iter.sgn]
  · have := (Fact.out : p.Prime).one_lt
    simp [sgnVal, Iter.sgn, Nat.cast_sub this.le]

/-- The unit of round `j` casts to the unit `Iter.zmodUnit p j`, for `j < p - 1`. -/
theorem cast_unitVal {j : ℕ} (hj : j < p - 1) :
    ((unitVal j : ℕ) : ZMod p) = (Iter.zmodUnit p j : ZMod p) := by
  rw [unitVal, Iter.zmodUnit_val hj]

/-- The inverse of the unit of round `j` casts to the inverse of `Iter.zmodUnit p j`. -/
theorem cast_unitInv_eq {j : ℕ} (hj : j < p - 1) :
    ((unitInv p j : ℕ) : ZMod p) = (((Iter.zmodUnit p j)⁻¹ : (ZMod p)ˣ) : ZMod p) := by
  rw [Units.val_inv_eq_inv_val, ← ZMod.pow_card_sub_two_eq_inv (Iter.zmodUnit p j).ne_zero,
    Iter.zmodUnit_val hj, unitInv, cast_powMod, Nat.cast_succ]

/-! ### Registers -/

/-- The registers read as field elements: element `i` of register `r`, or `0`. -/
def Regs.toState (p ℓ : ℕ) (R : Regs) : TreeEval.State (ZMod p) ℓ :=
  fun r i => ((R.get r).getD i 0 : ZMod p)

/-- Registers of length `ℓ` holding residues below `p`. -/
def Regs.WF (p ℓ : ℕ) (R : Regs) : Prop :=
  ∀ r, (R.get r).length = ℓ ∧ ∀ v ∈ R.get r, v < p

@[simp] theorem Regs.get_set_self (R : Regs) (r : Fin 3) (l : List ℕ) : (R.set r l).get r = l := by
  fin_cases r <;> rfl

private theorem Regs.get_set_of_ne (R : Regs) {r r' : Fin 3} (h : r' ≠ r) (l : List ℕ) :
    (R.set r l).get r' = R.get r' := by
  fin_cases r <;> fin_cases r' <;> first | rfl | exact absurd rfl h

private theorem Regs.get_set (R : Regs) (r r' : Fin 3) (l : List ℕ) :
    (R.set r l).get r' = if r' = r then l else R.get r' := by
  split_ifs with h
  · subst h; exact R.get_set_self _ _
  · exact R.get_set_of_ne h l

variable {ℓ : ℕ}

omit [Fact p.Prime] in
private theorem Regs.WF.set {R : Regs} (hR : R.WF p ℓ) {t : Fin 3} {l : List ℕ} (hl : l.length = ℓ)
    (hv : ∀ v ∈ l, v < p) : (R.set t l).WF p ℓ := by
  intro r
  rw [Regs.get_set]
  split_ifs
  exacts [⟨hl, hv⟩, hR r]

omit [Fact p.Prime] in
theorem modifyAt_addMod_wf (hp : 0 < p) {acc : List ℕ} (hacc : ∀ v ∈ acc, v < p) (i a : ℕ) :
    (modifyAt acc i (addMod p a)).length = acc.length ∧
      ∀ v ∈ modifyAt acc i (addMod p a), v < p := by
  refine ⟨by simp [modifyAt], fun v hv => ?_⟩
  rcases List.mem_or_eq_of_mem_set hv with hv | rfl
  · exact hacc v hv
  · exact addMod_lt hp _ _

theorem toState_scale (R : Regs) (r : Fin 3) (a : ℕ) :
    (R.scale p r a).toState p ℓ = scale r (a : ZMod p) (R.toState p ℓ) := by
  funext r' i
  by_cases h : r' = r
  · subst h
    simp only [Regs.toState, Regs.scale, TreeEval.scale, Regs.get_set_self, Function.update_self,
      Pi.smul_apply, smul_eq_mul, List.getD_eq_getElem?_getD, List.getElem?_map]
    rcases h' : (R.get r')[i.val]? with _ | v <;> simp [mulMod]
  · simp [Regs.toState, Regs.scale, TreeEval.scale, Regs.get_set_of_ne _ h, h]

omit [Fact p.Prime] in
theorem Regs.WF.scale (hp : 0 < p) {R : Regs} (hR : R.WF p ℓ) (r : Fin 3) (a : ℕ) :
    (R.scale p r a).WF p ℓ :=
  hR.set (by simp [(hR r).1]) fun v hv => by
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hv
    exact mulMod_lt hp _ _

theorem toState_set_modifyAt (R : Regs) (t : Fin 3) (i : Fin ℓ) (hlen : (R.get t).length = ℓ)
    (g : ℕ → ℕ) :
    (R.set t (modifyAt (R.get t) i g)).toState p ℓ =
      Function.update (R.toState p ℓ) t
        (Function.update (R.toState p ℓ t) i (g ((R.get t).getD i 0) : ZMod p)) := by
  funext r j
  by_cases h : r = t
  · subst h
    by_cases hj : j = i
    · subst hj
      simp [Regs.toState, modifyAt, List.getD_eq_getElem?_getD, hlen]
    · have : (i : ℕ) ≠ j := fun e => hj (Fin.ext e.symm)
      simp [Regs.toState, modifyAt, List.getD_eq_getElem?_getD, this, hj]
  · simp [Regs.toState, Regs.get_set_of_ne _ h, h]

omit [Fact p.Prime] in
theorem Regs.WF.set_modifyAt (hp : 0 < p) {R : Regs} (hR : R.WF p ℓ) (t : Fin 3) (i : ℕ) (a : ℕ) :
    (R.set t (modifyAt (R.get t) i (addMod p a))).WF p ℓ :=
  have h := modifyAt_addMod_wf hp (hR t).2 i a
  hR.set (h.1.trans (hR t).1) h.2

omit [Fact p.Prime] in
theorem Regs.WF.subtractSums (hp : 0 < p) {R : Regs} (hR : R.WF p ℓ) (c : ℕ) (t : Fin 3)
    (acc : List ℕ) : (subtractSums p c t acc R).WF p ℓ :=
  hR.set (by simp [(hR t).1]) fun v hv => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hv
    exact addMod_lt hp _ _

theorem toState_subtractSums (R : Regs) (c : ℕ) (t : Fin 3) (acc : List ℕ)
    (hlen : (R.get t).length = ℓ) :
    (subtractSums p c t acc R).toState p ℓ =
      Function.update (R.toState p ℓ) t
        fun i => R.toState p ℓ t i - (c : ZMod p) * (acc.getD i 0 : ZMod p) := by
  funext r j
  by_cases h : r = t
  · subst h
    have hj : (j : ℕ) < (R.get r).length := hlen ▸ j.isLt
    simp [Regs.toState, TreeEval.Reader.subtractSums, List.getD_eq_getElem?_getD, hj,
      sub_eq_add_neg]
  · simp [Regs.toState, TreeEval.Reader.subtractSums, Regs.get_set_of_ne _ h, h]

/-! ### Weights and the multilinear extension -/

private theorem cast_foldl_mulMod (F : ℕ → ℕ) (n : ℕ) :
    (((List.range n).foldl (fun a j => mulMod p a (F j)) (1 % p) : ℕ) : ZMod p) =
      ∏ j ∈ Finset.range n, (F j : ZMod p) := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      cast_mulMod, ih, Finset.prod_range_succ]

/-- The weight casts to the product of `x` or `1 - x` over the low bits of `k`, times the same
over its high bits for `y`. -/
theorem cast_weight (k : ℕ) (x y : List ℕ) :
    ((weight p ℓ k x y : ℕ) : ZMod p) =
      (∏ j : Fin ℓ, if lowBits ℓ k j then (x.getD j 0 : ZMod p) else 1 - x.getD j 0) *
        ∏ j : Fin ℓ, if highBits ℓ k j then (y.getD j 0 : ZMod p) else 1 - y.getD j 0 := by
  rw [weight, cast_mulMod, cast_foldl_mulMod, cast_foldl_mulMod,
    ← Fin.prod_univ_eq_prod_range (fun j => ((chi p (k.testBit j) (x.getD j 0) : ℕ) : ZMod p)),
    ← Fin.prod_univ_eq_prod_range
      (fun j => ((chi p (k.testBit (ℓ + j)) (y.getD j 0) : ℕ) : ZMod p))]
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  simp [lowBits, highBits]

omit [Fact p.Prime] in
/-- The inputs of a gate as the indices below `2^(2ℓ)`. -/
def cubeEquiv (ℓ : ℕ) : (Fin ℓ ⊕ Fin ℓ → Bool) ≃ Fin (2 ^ (ℓ + ℓ)) :=
  (Equiv.arrowCongr finSumFinEquiv finTwoEquiv.symm).trans finFunctionFinEquiv

omit [Fact p.Prime] in
/-- An index reads as its low and high bits. -/
theorem cubeEquiv_symm_apply (k : Fin (2 ^ (ℓ + ℓ))) :
    (cubeEquiv ℓ).symm k = Sum.elim (lowBits ℓ k) (highBits ℓ k) := by
  funext ι
  have key (n : ℕ) (x : Fin 2) (hx : (x : ℕ) = k / 2 ^ n % 2) :
      finTwoEquiv x = (k : ℕ).testBit n := by
    rw [Nat.testBit_eq_decide_div_mod_eq, ← hx]
    fin_cases x <;> rfl
  rcases ι with j | j
  · simp only [cubeEquiv, Equiv.symm_trans_apply, Equiv.arrowCongr_symm, Equiv.symm_symm,
      Equiv.arrowCongr_apply, Function.comp_apply, Sum.elim_inl, lowBits]
    exact key j _ (by simp [finFunctionFinEquiv_symm_apply_val])
  · simp only [cubeEquiv, Equiv.symm_trans_apply, Equiv.arrowCongr_symm, Equiv.symm_symm,
      Equiv.arrowCongr_apply, Function.comp_apply, Sum.elim_inr, highBits]
    exact key (ℓ + j) _ (by simp [finFunctionFinEquiv_symm_apply_val, Nat.add_comm])

omit [Fact p.Prime] in
theorem four_pow_eq (ℓ : ℕ) : 4 ^ ℓ = 2 ^ (ℓ + ℓ) := by rw [← two_mul, pow_mul]; norm_num

/-- The indices `k < 4^ℓ`, read as the low and high bits, enumerate the inputs of a gate. -/
private theorem sum_cube {M : Type*} [AddCommMonoid M] (G : (Fin ℓ ⊕ Fin ℓ → Bool) → M) :
    ∑ a, G a = ∑ k ∈ Finset.range (4 ^ ℓ), G (Sum.elim (lowBits ℓ k) (highBits ℓ k)) := by
  rw [← (cubeEquiv ℓ).symm.sum_comp, four_pow_eq,
    ← Fin.sum_univ_eq_sum_range (fun k => G (Sum.elim (lowBits ℓ k) (highBits ℓ k)))]
  exact Finset.sum_congr rfl fun k _ => by rw [cubeEquiv_symm_apply]

/-- **The multilinear extension of an output bit as a sum over the table indices.** -/
theorem eval_gatePoly_eq_sum (f : Gate ℓ) (i : Fin ℓ)
    (X Y : Fin ℓ → ZMod p) :
    eval (Sum.elim X Y) (gatePoly f i) = ∑ k ∈ Finset.range (4 ^ ℓ),
      bitVal (ZMod p) (f (lowBits ℓ k) (highBits ℓ k) i) *
        ((∏ j : Fin ℓ, if lowBits ℓ k j then X j else 1 - X j) *
          ∏ j : Fin ℓ, if highBits ℓ k j then Y j else 1 - Y j) := by
  rw [gatePoly, multilinearExtension, map_sum]
  simp only [map_mul, eval_C, eval_indicatorPoly_apply, Fintype.prod_sum_type, Sum.elim_inl,
    Sum.elim_inr]
  rw [sum_cube (fun a => bitVal (ZMod p) (f (a ∘ Sum.inl) (a ∘ Sum.inr) i) *
    ((∏ j, if a (Sum.inl j) then X j else 1 - X j) * ∏ j, if a (Sum.inr j) then Y j else 1 - Y j))]
  rfl

end Cast

end Reader

end Cslib.TreeEval
