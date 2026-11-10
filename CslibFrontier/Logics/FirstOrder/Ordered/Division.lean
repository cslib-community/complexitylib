/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Ordered.BitArithmetic

/-!
# Bounds, quotients and remainders by fixed literals

Formulas comparing with a fixed numeral and taking quotient and remainder by a fixed literal
divisor, built from the native addition formula and `scaleEq`. As with `natEq`, the literal need
not be an element of the universe: `ltNat L k x` holds exactly when the value of `x` is below
`k`, and the quotient and remainder formulas use only witnesses bounded by their dividend, so they
have exact natural-number semantics in every canonical universe.

## Main definitions

* `Cslib.Logic.FO.Ordered.ltNat`: comparison with a fixed numeral.
* `Cslib.Logic.FO.Ordered.scaleAddEq`: the equation `d * x + y = z` for a literal `d`.
* `Cslib.Logic.FO.Ordered.divNatEq`, `Cslib.Logic.FO.Ordered.modNatEq`: quotient and remainder
  by a fixed positive literal.

## Main results

* `Cslib.Logic.FO.Ordered.realize_ltNat`, `Cslib.Logic.FO.Ordered.realize_scaleAddEq`,
  `Cslib.Logic.FO.Ordered.realize_divNatEq`, `Cslib.Logic.FO.Ordered.realize_modNatEq`: exact
  natural-number semantics.
-/

public section

namespace Cslib.Logic.FO.Ordered

open FirstOrder Language Structure

variable (L : Language)

/-- The value is below a fixed numeral, which need not be an element of the universe. -/
noncomputable def ltNat (k : ℕ) {α : Type*} (x : (language L).Term α) :
    (language L).Formula α :=
  Formula.iSup fun j : Fin k => natEq L j x

/-- The equation `d * x + y = z` for a fixed literal `d`. -/
noncomputable def scaleAddEq (d : ℕ) {α : Type*} (x y z : (language L).Term α) :
    (language L).Formula α :=
  Formula.iExs Unit (scaleEq L d (x.relabel Sum.inl) (.var (.inr ())) ⊓
    addEq L (.var (.inr ())) (y.relabel Sum.inl) (z.relabel Sum.inl))

/-- `y` is the quotient of `x` by the fixed literal `d`. -/
noncomputable def divNatEq (d : ℕ) {α : Type*} (x y : (language L).Term α) :
    (language L).Formula α :=
  Formula.iExs Unit (ltNat L d (.var (.inr ())) ⊓
    scaleAddEq L d (y.relabel Sum.inl) (.var (.inr ())) (x.relabel Sum.inl))

/-- `y` is the remainder of `x` by the fixed literal `d`. -/
noncomputable def modNatEq (d : ℕ) {α : Type*} (x y : (language L).Term α) :
    (language L).Formula α :=
  ltNat L d y ⊓ Formula.iExs Unit
    (scaleAddEq L d (.var (.inr ())) (y.relabel Sum.inl) (x.relabel Sum.inl))

variable {L : Language} {n : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)] {α : Type*}

/-- `ltNat L k x` holds exactly when `x` denotes a number below `k`. -/
@[simp, fo_realize]
theorem realize_ltNat (k : ℕ) (x : (language L).Term α) (v : α → Fin n) :
    (ltNat L k x).Realize v ↔ (x.realize v).val < k := by
  simp only [ltNat, Formula.realize_iSup, realize_natEq]
  exact ⟨fun ⟨j, hj⟩ => hj ▸ j.isLt, fun h => ⟨⟨_, h⟩, rfl⟩⟩

/-- `scaleAddEq L d x y z` holds exactly when `d * x + y = z`. -/
@[simp, fo_realize]
theorem realize_scaleAddEq (d : ℕ) (x y z : (language L).Term α) (v : α → Fin n) :
    (scaleAddEq L d x y z).Realize v ↔
      d * (x.realize v).val + (y.realize v).val = (z.realize v).val := by
  simp only [scaleAddEq, Formula.realize_iExs, Formula.realize_inf, realize_scaleEq,
    realize_addEq, Term.realize_relabel, Term.realize_var, Sum.elim_comp_inl,
    Sum.elim_inr]
  constructor
  · rintro ⟨t, ht, he⟩
    omega
  · intro h
    exact ⟨fun _ => ⟨d * (x.realize v).val, by have := (z.realize v).isLt; omega⟩, rfl, h⟩

/-- `divNatEq L d x y` holds exactly when `y = x / d`, for a positive literal `d`. -/
@[simp, fo_realize]
theorem realize_divNatEq {d : ℕ} (hd : 0 < d) (x y : (language L).Term α) (v : α → Fin n) :
    (divNatEq L d x y).Realize v ↔ (y.realize v).val = (x.realize v).val / d := by
  simp only [divNatEq, Formula.realize_iExs, Formula.realize_inf, realize_ltNat,
    realize_scaleAddEq, Term.realize_relabel, Term.realize_var, Sum.elim_comp_inl,
    Sum.elim_inr]
  constructor
  · rintro ⟨m, hm, he⟩
    rw [← he, Nat.add_comm, Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hm, Nat.zero_add]
  · intro h
    refine ⟨fun _ => ⟨(x.realize v).val % d,
      (Nat.mod_le _ _).trans_lt (x.realize v).isLt⟩, Nat.mod_lt _ hd, ?_⟩
    rw [h]
    exact Nat.div_add_mod _ _

/-- `modNatEq L d x y` holds exactly when `y = x % d`, for a positive literal `d`. -/
@[simp, fo_realize]
theorem realize_modNatEq {d : ℕ} (hd : 0 < d) (x y : (language L).Term α) (v : α → Fin n) :
    (modNatEq L d x y).Realize v ↔ (y.realize v).val = (x.realize v).val % d := by
  simp only [modNatEq, Formula.realize_iExs, Formula.realize_inf, realize_ltNat,
    realize_scaleAddEq, Term.realize_relabel, Term.realize_var, Sum.elim_comp_inl,
    Sum.elim_inr]
  constructor
  · rintro ⟨hy, q, he⟩
    rw [← he, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy]
  · intro h
    refine ⟨h ▸ Nat.mod_lt _ hd, fun _ => ⟨(x.realize v).val / d,
      (Nat.div_le_self _ _).trans_lt (x.realize v).isLt⟩, ?_⟩
    rw [h]
    exact Nat.div_add_mod _ _

end Cslib.Logic.FO.Ordered
