/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.MCSP.PartialHardness.Construction
import CslibFrontier.Foundations.Data.BitString.Binary
import CslibFrontier.Foundations.Data.BitString.Prefix

/-!
# Evaluating the CMMSA partial truth table from explicit tables

`FromCMMSA.entry f x` reads its input `x` as a bit string and the functions `f v` of the variables
as Boolean functions. This module computes the same entries from explicit data: the input is a
number `x < 2 ^ L`, and the function of variable `v` is a list `T[v]` of its values in the order
of `BitString.equivFin`. The definitions use only `Nat.testBit`, division and remainder by powers
of two, `List.getD` and folds, so a polynomial-time proof can follow them directly.

The input fields are read arithmetically. The formula index is `x mod 2 ^ indexWidth`
(`formulaIndex_equivFin_symm`). The slot `(t, q)` starts at bit
`slotOffset I Δ k lam t q = indexWidth + slotWidth · (q + Δ t)`, its `k` seeds of `W` bits come
first, then its mask bit. A variable `v` evaluates a seed `z` at entry `z mod 2 ^ ℓ v` of `T[v]`,
reading `false` past the end of `T[v]`.

Correctness is local. `termParityN T x t` equals `termParity f x t` as soon as `T[v]` is the table
of `f v` for the variables `v` of term `t` alone (`termParityN_eq`), so a caller can evaluate a
term from the tables of only some variables. With every table present (`IsVarTable` for all `v`),
the entries agree (`entryN_eq`), and `tables f`, the list of all tables, gives the whole table of
`toInstance` (`tableN_tables`).

The evaluator definitions are exposed because their polynomial-time proofs, in a separate module,
follow their bodies.

## Main definitions

* `Cslib.PartialMCSP.FromCMMSA.slotOffset`: the position of the first bit of a slot.
* `Cslib.PartialMCSP.FromCMMSA.slotBitN`, `termParityN`, `entryN`, `tableN`: the slot bits, term
  parities, entries and whole table, computed from explicit tables and a numeric input.
* `Cslib.PartialMCSP.FromCMMSA.IsVarTable`: `T[v]` is the table of `f v`.
* `Cslib.PartialMCSP.FromCMMSA.varTable`, `tables`: the explicit tables of the functions `f`.

## Main results

* `Cslib.PartialMCSP.FromCMMSA.formulaIndex_equivFin_symm`: the formula index of the input numbered
  `x` is `x mod 2 ^ indexWidth`, the index that `termParityN` and `entryN` read.
* `Cslib.PartialMCSP.FromCMMSA.slotBitN_eq`, `termParityN_eq`: local correctness, from the tables of
  the variables that the slot or term reads.
* `Cslib.PartialMCSP.FromCMMSA.entryN_eq`: with every table present, `entryN` is `entry`.
* `Cslib.PartialMCSP.FromCMMSA.tableN_eq_ofFn`: from any list `T` with the table of every variable,
  `tableN T` is the table of `toInstance I Δ k lam P f`.
* `Cslib.PartialMCSP.FromCMMSA.tableN_tables`: in particular, `tableN (tables f)` is.
* `Cslib.PartialMCSP.FromCMMSA.isVarTable_tables`, `IsVarTable.of_getD_eq`: `tables f` has the
  table of every variable, and so does any list that agrees with it at `v`.

## References

* [S. Hirahara, *NP-Hardness of Learning Programs and Partial MCSP*][Hirahara2022]
-/

public section

namespace Cslib.PartialMCSP.FromCMMSA

open Cslib.Complexity Cslib.Logic.PL

variable {I : CMMSAInstance} {Δ k lam : ℕ}

/-! ### The evaluator -/

variable (I Δ k lam) in
/-- The position of the first bit of slot `(t, q)`: `indexWidth + slotWidth · (q + Δ t)`. -/
@[expose] def slotOffset (t q : ℕ) : ℕ := indexWidth I + slotWidth I k lam * (q + Δ * t)

variable (I Δ k lam) in
/-- The bit of slot `(t, q)` at a numeric input `x`, computed from the tables `T`: the mask bit of
the slot plus, over its `k` seeds `z`, entry `z mod 2 ^ ℓ v` of `T[v]` for the variable `v` of its
literal. -/
@[expose] def slotBitN (T : List (List Bool)) (x t q : ℕ) : Bool :=
  let v := var I (x % 2 ^ indexWidth I) t q
  (List.range k).foldl
    (fun acc i => acc ^^ (T.getD v []).getD
      (x / 2 ^ (slotOffset I Δ k lam t q + seedWidth I lam * i) % 2 ^ varLength I lam v) false)
    (x.testBit (slotOffset I Δ k lam t q + k * seedWidth I lam))

variable (I Δ k lam) in
/-- The parity of term `t` at a numeric input `x`: the sum of the bits of its occupied slots. -/
@[expose] def termParityN (T : List (List Bool)) (x t : ℕ) : Bool :=
  (List.range Δ).foldl
    (fun acc q => acc ^^
      (decide (q < (term I (x % 2 ^ indexWidth I) t).length) && slotBitN I Δ k lam T x t q))
    false

variable (I Δ k lam) in
/-- The entry at a numeric input `x`: `b` when the formula index `j` is below `m` and every term of
`φ_j` has parity `b`; otherwise undefined. -/
@[expose] def entryN (T : List (List Bool)) (x : ℕ) : Option Bool :=
  let j := x % 2 ^ indexWidth I
  if j < I.formulas.length then
    if (List.range Δ).all fun t =>
        !decide (t < (I.formulas.getD j []).length) || termParityN I Δ k lam T x t then
      some true
    else if (List.range Δ).all fun t =>
        !decide (t < (I.formulas.getD j []).length) || !termParityN I Δ k lam T x t then
      some false
    else none
  else none

variable (I Δ k lam) in
/-- The whole table: the entries at `x = 0, …, 2 ^ L - 1`. -/
@[expose] def tableN (T : List (List Bool)) : List (Option Bool) :=
  (List.range (2 ^ inputLength I Δ k lam)).map (entryN I Δ k lam T)

variable (I lam) in
/-- `T[v]` is the table of `f v` in the order of `BitString.equivFin`, and reads `false` at `0` when
`v` is not a variable. -/
@[expose] def IsVarTable (f : VarFunctions I lam) (T : List (List Bool)) (v : ℕ) : Prop :=
  ∀ y : BitString (varLength I lam v),
    (T.getD v []).getD (BitString.equivFin _ y) false = evalVar f v y

/-- The table of `f v` in the order of `BitString.equivFin`; empty when `v` is not a variable. -/
@[expose] def varTable (f : VarFunctions I lam) (v : ℕ) : List Bool :=
  if hv : v < I.weights.length then
    List.ofFn fun y : Fin (2 ^ varLength I lam v) => f ⟨v, hv⟩ ((BitString.equivFin _).symm y)
  else []

/-- The tables of all variables. -/
@[expose] def tables (f : VarFunctions I lam) : List (List Bool) :=
  (List.range I.weights.length).map (varTable f)

/-! ### Reading the input fields -/

/-- The formula index of the input numbered `x` is `x mod 2 ^ indexWidth`. -/
theorem formulaIndex_equivFin_symm (x : Fin (2 ^ inputLength I Δ k lam)) :
    formulaIndex ((BitString.equivFin _).symm x) = (x : ℕ) % 2 ^ indexWidth I := by
  rw [formulaIndex, BitString.val_equivFin_eq_div_mod_of_testBit (s := 0) (N := x) fun i => ?_]
  · simp
  · rw [BitString.equivFin_symm_apply]
    simp [indexPos]

private theorem slotPos_val (t q : Fin Δ) (p : Fin (slotWidth I k lam)) :
    (slotPos I Δ k lam t q p : ℕ) = slotOffset I Δ k lam t q + p := by
  simp only [slotPos, Fin.natAdd, finProdFinEquiv_apply_val, slotOffset]
  ring

private theorem maskPos_val (t q : Fin Δ) :
    (maskPos I Δ k lam t q : ℕ) = slotOffset I Δ k lam t q + k * seedWidth I lam :=
  slotPos_val t q (Fin.last _)

private theorem seedPos_val (t q : Fin Δ) (i : Fin k) (r : Fin (seedWidth I lam)) :
    (seedPos I Δ k lam t q i r : ℕ) = slotOffset I Δ k lam t q + seedWidth I lam * i + r := by
  refine (slotPos_val t q (Fin.castSucc (finProdFinEquiv (i, r)))).trans ?_
  change slotOffset I Δ k lam t q + ((finProdFinEquiv (i, r) : Fin (k * seedWidth I lam)) : ℕ) = _
  rw [finProdFinEquiv_apply_val]
  ring

private theorem varLength_le_seedWidth' (v : ℕ) : varLength I lam v ≤ seedWidth I lam := by
  by_cases hv : v < I.weights.length
  · exact varLength_le_seedWidth hv
  · simp [varLength, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hv)]

/-- The value of variable `v` at seed `i` of slot `(t, q)`, read from a table of `f v`. -/
private theorem evalVar_seed_eq {f : VarFunctions I lam} {T : List (List Bool)} {v : ℕ}
    (hT : IsVarTable I lam f T v) (x : Fin (2 ^ inputLength I Δ k lam)) (t q : Fin Δ) (i : Fin k) :
    evalVar f v (seed ((BitString.equivFin _).symm x) t q i) =
      (T.getD v []).getD
        ((x : ℕ) / 2 ^ (slotOffset I Δ k lam t q + seedWidth I lam * i) % 2 ^ varLength I lam v)
        false := by
  set z := seed ((BitString.equivFin _).symm x) t q i
  have hz : evalVar f v z = evalVar f v (BitString.zeroExtend (d' := varLength I lam v) z) := by
    unfold evalVar
    split_ifs with hv
    · congr 1
      funext r
      simp [BitString.zeroExtend, (varLength_le_seedWidth' (lam := lam) v).trans_lt' r.isLt]
    · rfl
  rw [hz, ← hT, BitString.val_equivFin_eq_div_mod_of_testBit fun r => ?_]
  have hr : (r : ℕ) < seedWidth I lam := r.isLt.trans_le (varLength_le_seedWidth' v)
  simp only [BitString.zeroExtend, hr, dite_true, z, seed, BitString.equivFin_symm_apply,
    seedPos_val]

/-! ### Correctness -/

/-- `xor`-folding `g` over `0, …, n - 1` from `b` is `b` plus the sum of `g`. -/
private theorem foldl_xor_range (g : ℕ → Bool) (b : Bool) (n : ℕ) :
    (List.range n).foldl (fun acc i => acc ^^ g i) b = b + ∑ i : Fin n, g i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih, Fin.sum_univ_castSucc, List.foldl_cons,
      List.foldl_nil, ← Bool.add_eq_xor, add_assoc]
    rfl

/-- **Local correctness of a slot.** If `T[v]` is the table of `f v` for the variable `v` of slot
`(t, q)`, then `slotBitN` computes the slot bit. -/
theorem slotBitN_eq {f : VarFunctions I lam} {T : List (List Bool)}
    (x : Fin (2 ^ inputLength I Δ k lam)) (t q : Fin Δ)
    (hT : IsVarTable I lam f T (var I ((x : ℕ) % 2 ^ indexWidth I) t q)) :
    slotBitN I Δ k lam T x t q = slotBit f ((BitString.equivFin _).symm x) t q := by
  rw [slotBitN, slotBit, formulaIndex_equivFin_symm, BitString.equivFin_symm_apply, maskPos_val,
    foldl_xor_range]
  exact congrArg _ (Finset.sum_congr rfl fun i _ => (evalVar_seed_eq hT x t q i).symm)

/-- **Local correctness of a term.** If `T[v]` is the table of `f v` for every variable `v` of
term `t` of the indexed formula, then `termParityN` computes the parity of term `t`. -/
theorem termParityN_eq {f : VarFunctions I lam} {T : List (List Bool)}
    (x : Fin (2 ^ inputLength I Δ k lam)) (t : Fin Δ)
    (hT : ∀ q : Fin Δ, (q : ℕ) < (term I ((x : ℕ) % 2 ^ indexWidth I) t).length →
      IsVarTable I lam f T (var I ((x : ℕ) % 2 ^ indexWidth I) t q)) :
    termParityN I Δ k lam T x t = termParity f ((BitString.equivFin _).symm x) t := by
  rw [termParityN, termParity, formulaIndex_equivFin_symm, foldl_xor_range, Bool.add_eq_xor,
    Bool.false_xor]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hq : (q : ℕ) < (term I ((x : ℕ) % 2 ^ indexWidth I) t).length
  · simp [hq, slotBitN_eq x t q (hT q hq)]
  · simp only [hq, decide_false, Bool.false_and, ite_false]
    rfl

private theorem all_range_iff {n : ℕ} {p : ℕ → Bool} :
    (List.range n).all p = true ↔ ∀ t : Fin n, p t = true := by
  simp [List.all_eq_true, Fin.forall_iff]

/-- **Correctness of an entry.** With the table of every variable, `entryN` is `entry`. -/
theorem entryN_eq {f : VarFunctions I lam} {T : List (List Bool)}
    (hT : ∀ v, IsVarTable I lam f T v) (x : Fin (2 ^ inputLength I Δ k lam)) :
    entryN I Δ k lam T x = entry f ((BitString.equivFin _).symm x) := by
  have hpar (t : Fin Δ) := termParityN_eq (f := f) x t fun q _ => hT _
  simp only [entryN, entry, formulaIndex_equivFin_symm, all_range_iff, hpar]
  congr 1
  simp [Bool.or_eq_true, imp_iff_not_or]

/-- With every table, `tableN` lists the table of `toInstance I Δ k lam P f`. -/
theorem tableN_eq_ofFn {f : VarFunctions I lam} {T : List (List Bool)}
    (hT : ∀ v, IsVarTable I lam f T v) (P : ℕ) :
    tableN I Δ k lam T = List.ofFn (toInstance I Δ k lam P f).table := by
  refine List.ext_getElem (by simp [tableN, toInstance]) fun i h₁ h₂ => ?_
  simp only [tableN, List.getElem_map, List.getElem_range, List.getElem_ofFn, toInstance]
  exact entryN_eq hT ⟨i, by simpa [tableN] using h₁⟩

/-- The tables of all variables, as a list, at a number `v`. -/
theorem getD_tables (f : VarFunctions I lam) (v : ℕ) : (tables f).getD v [] = varTable f v := by
  by_cases hv : v < I.weights.length
  · simp [tables, List.getD_eq_getElem?_getD, hv]
  · simp [tables, varTable, List.getD_eq_getElem?_getD, hv]

/-- A list of tables that agrees with `tables f` at `v` has the table of `f v`. -/
theorem IsVarTable.of_getD_eq {f : VarFunctions I lam} {T : List (List Bool)} {v : ℕ}
    (h : T.getD v [] = varTable f v) : IsVarTable I lam f T v := by
  intro y
  rw [h, varTable, evalVar]
  split_ifs with hv
  · simp [List.getD_eq_getElem?_getD]
  · rfl

/-- `tables f` has the table of every variable. -/
theorem isVarTable_tables (f : VarFunctions I lam) (v : ℕ) : IsVarTable I lam f (tables f) v :=
  .of_getD_eq (getD_tables f v)

/-- **The table of `toInstance` from explicit tables.** -/
theorem tableN_tables (f : VarFunctions I lam) (P : ℕ) :
    tableN I Δ k lam (tables f) = List.ofFn (toInstance I Δ k lam P f).table :=
  tableN_eq_ofFn (isVarTable_tables f) P

end Cslib.PartialMCSP.FromCMMSA
