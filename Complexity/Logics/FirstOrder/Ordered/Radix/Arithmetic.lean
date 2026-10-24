/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Ordered.Multiplication
public import Complexity.Foundations.Data.Nat.Radix
import Mathlib.Tactic.Linarith

/-!
# Native arithmetic on fixed-length radix words

The radix is a source element, but a word may represent a value much larger than the source
universe. Native PLUS and TIMES check only individual digit equations. Bounded digits and
zero initial and final carries make these equations exact rather than modular.

## Main definitions

* `Cslib.Logic.FO.Ordered.mulEq`: apply native TIMES to arbitrary terms.
* `Cslib.Logic.FO.Ordered.Radix.digits`: bound every digit by the radix.
* `Cslib.Logic.FO.Ordered.Radix.cell`, `Cslib.Logic.FO.Ordered.Radix.affine`: one affine digit
  equation, and multiplying one word by a digit and adding another word.

## Main results

* `Cslib.Logic.FO.Ordered.Radix.realize_affine`: exact ordinary arithmetic, provided
  the radix is at least two and its cube fits in the source universe.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Exercise 1.33(3) and Theorem 1.17(1): the
  digit construction implements the suggested arithmetic with the native arithmetic of the
  theorem.
-/

@[expose] public section

namespace Cslib.Logic.FO.Ordered

open FirstOrder Language Structure

/-- Apply native TIMES to three arbitrary terms. -/
noncomputable def mulEq (L : Language) {α : Type*} (x y z : (language L).Term α) :
    (language L).Formula α := (multiplication L).subst ![x, y, z]

/-- `mulEq L x y z` holds iff the product of `x` and `y` equals `z`. -/
@[simp, fo_realize]
theorem realize_mulEq {L : Language} {n : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)]
    {α : Type*} (x y z : (language L).Term α) (v : α → Fin n) :
    (mulEq L x y z).Realize v ↔ (x.realize v).val * (y.realize v).val = (z.realize v).val := by
  change ((multiplication L).subst ![x, y, z]).Realize v _ ↔ _
  rw [BoundedFormula.realize_subst]
  exact realize_multiplication _

namespace Radix

variable (L : Language)

/-- Every word digit is strictly below the radix. -/
noncomputable def digits {α : Type*} {d : ℕ} (B : (language L).Term α)
    (x : Fin d → (language L).Term α) : (language L).Formula α :=
  Formula.iInf fun i => (le L B (x i)).not

/-- One exact affine digit equation, with all its scalar intermediate values checked. -/
noncomputable def cell {α : Type*} (B a b y c z c' : (language L).Term α) :
    (language L).Formula α := Formula.iExs (Fin 4)
  (mulEq L (a.relabel Sum.inl) (b.relabel Sum.inl) (.var (.inr 0)) ⊓
   addEq L (.var (.inr 0)) (y.relabel Sum.inl) (.var (.inr 1)) ⊓
   addEq L (.var (.inr 1)) (c.relabel Sum.inl) (.var (.inr 2)) ⊓
   mulEq L (B.relabel Sum.inl) (c'.relabel Sum.inl) (.var (.inr 3)) ⊓
   addEq L (z.relabel Sum.inl) (.var (.inr 3)) (.var (.inr 2)))

/-- Multiply a word by a coefficient at most the radix and add another word, rejecting
final overflow. Allowing the radix itself as coefficient also provides exact word shifts. -/
noncomputable def affine {α : Type*} {d : ℕ} (B b : (language L).Term α)
    (x y z : Fin d → (language L).Term α) : (language L).Formula α :=
  le L b B ⊓ digits L B x ⊓ digits L B y ⊓ digits L B z ⊓
  Formula.iExs (Fin (d + 1))
    ((Term.var (.inr 0)).equal (zero L) ⊓
     (Term.var (.inr (Fin.last d))).equal (zero L) ⊓
     (Formula.iInf fun i => le L (.var (.inr i)) (B.relabel Sum.inl)) ⊓
     Formula.iInf fun i : Fin d =>
       cell L (B.relabel Sum.inl) ((x i).relabel Sum.inl) (b.relabel Sum.inl)
         ((y i).relabel Sum.inl) (.var (.inr i.castSucc))
         ((z i).relabel Sum.inl) (.var (.inr i.succ)))

variable {L : Language} {n : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)] {α : Type*}

/-- `digits L B x` holds iff every digit `x i` is strictly less than `B`. -/
@[simp, fo_realize]
theorem realize_digits {d : ℕ} (B : (language L).Term α)
    (x : Fin d → (language L).Term α) (v : α → Fin n) :
    (digits L B x).Realize v ↔ ∀ i, (x i |>.realize v).val < (B.realize v).val := by
  simp [digits, not_le]

/-- `cell L B a b y c z c'` holds iff `a * b + y + c = z + B * c'` and `a * b + y + c < n`. -/
@[fo_realize]
theorem realize_cell (B a b y c z c' : (language L).Term α) (v : α → Fin n) :
    (cell L B a b y c z c').Realize v ↔
      (a.realize v).val * (b.realize v).val + (y.realize v).val + (c.realize v).val =
        (z.realize v).val + (B.realize v).val * (c'.realize v).val ∧
      (a.realize v).val * (b.realize v).val + (y.realize v).val + (c.realize v).val < n := by
  simp only [cell, Formula.realize_iExs, Formula.realize_inf, realize_mulEq, realize_addEq,
    Term.realize_var, Term.realize_relabel, Function.comp_def, Sum.elim_inl, Sum.elim_inr,
    and_assoc]
  constructor
  · rintro ⟨u, hp, ht, hs, hu, he⟩
    have := (u 2).isLt
    constructor <;> lia
  · rintro ⟨he, hs⟩
    refine ⟨![⟨(a.realize v).val * (b.realize v).val, by lia⟩,
      ⟨(a.realize v).val * (b.realize v).val + (y.realize v).val, by lia⟩,
      ⟨_, hs⟩, ⟨(B.realize v).val * (c'.realize v).val, by lia⟩],
      rfl, rfl, rfl, rfl, ?_⟩
    exact he.symm

/-- When the radix `B` is at least two and `B ^ 3` fits in the universe, `affine L B b x y z`
holds exactly when `b ≤ B`, the words `x`, `y` and `z` have digits below `B`, and their values
satisfy `b x + y = z`. -/
@[fo_realize]
theorem realize_affine {d : ℕ} (B b : (language L).Term α)
    (x y z : Fin d → (language L).Term α) (v : α → Fin n)
    (hB : 1 < (B.realize v).val) (hBn : (B.realize v).val ^ 3 < n) :
    (affine L B b x y z).Realize v ↔
      (b.realize v).val ≤ (B.realize v).val ∧
      (∀ i, ((x i).realize v).val < (B.realize v).val) ∧
      (∀ i, ((y i).realize v).val < (B.realize v).val) ∧
      (∀ i, ((z i).realize v).val < (B.realize v).val) ∧
      (b.realize v).val * Nat.ofDigits (B.realize v).val
          (List.ofFn fun i => ((x i).realize v).val) +
        Nat.ofDigits (B.realize v).val (List.ofFn fun i => ((y i).realize v).val) =
        Nat.ofDigits (B.realize v).val (List.ofFn fun i => ((z i).realize v).val) := by
  simp only [affine, Formula.realize_inf, realize_le,
    realize_digits, Formula.realize_iExs, Formula.realize_equal, Term.realize_var,
    realize_zero_val, Fin.ext_iff, Formula.realize_iInf, realize_cell, Term.realize_relabel,
    Function.comp_def, Sum.elim_inl, Sum.elim_inr, Fin.le_def, and_assoc]
  constructor
  · rintro ⟨hb, hx, hy, hz, c, hc0, hce, hc, hstep⟩
    refine ⟨hb, hx, hy, hz, ?_⟩
    simpa only [Nat.add_zero] using
      (Nat.radix_affine_carries_iff hB hb (Nat.zero_le _)
        _ _ _ hx hy hz).mp
        ⟨fun i => (c i).val, hc0, hce, hc, fun i => (hstep i).1⟩
  · rintro ⟨hb, hx, hy, hz, he⟩
    obtain ⟨c, hc0, hce, hc, hstep⟩ :=
      (Nat.radix_affine_carries_iff hB hb (Nat.zero_le _)
        _ _ _ hx hy hz).mpr (by simpa only [Nat.add_zero] using he)
    refine ⟨hb, hx, hy, hz, (fun i => ⟨c i, lt_of_le_of_lt (hc i) (B.realize v).isLt⟩),
      hc0, hce, hc, fun i => ⟨hstep i, ?_⟩⟩
    have hxi := hx i
    have hyi := hy i
    have hci := hc i.castSucc
    have hp := Nat.mul_le_mul
      (show ((x i).realize v).val ≤ (B.realize v).val - 1 by lia)
      hb
    have hpred : (B.realize v).val - 1 + 1 = (B.realize v).val := by lia
    have hcube : (B.realize v).val * ((B.realize v).val + 1) ≤ (B.realize v).val ^ 3 := by
      calc
        _ ≤ (B.realize v).val * ((B.realize v).val * (B.realize v).val) :=
          Nat.mul_le_mul_left _ (by nlinarith)
        _ = _ := by ring
    nlinarith

end Radix
end Cslib.Logic.FO.Ordered
