/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Run
public import Complexity.Computability.Complexity.CookLevin.Correctness
public import Complexity.Computability.Complexity.Problems.SAT
public import Mathlib.Logic.Equiv.Nat

/-!
# The Cook–Levin reduction

Let `A` be a problem in `NP`, verified by `V` with certificates of length `p` of the instance
length, where `V` is computed by the machine `tm` in time `c * (n + 1) ^ d`. The reduction maps
an instance `a` to the tableau of `tm` on inputs `encode (a, w) = delimit (encode a) ++ w`, for
the unknown certificate `w` of length `p (encode a).length`, unrolled for exactly the number of
steps `tm` is allowed on such inputs. Its variables are then renamed injectively to natural
numbers.

`reduce_mem_SAT_iff` says that the reduction is correct: `reduce tm p c d enc a` is satisfiable
exactly when `a ∈ A`. It only uses that the run of `tm` on `frame (enc a) ++ w` has halted by the
allowed number of steps with output `[V (a, w)]`, so it applies to any machine computing `V` in
that time, tidily (`reduce_mem_SAT_iff_of_computesTidily`) or not.

The input prefix and unary bounds are jointly computable in polynomial time
(`computableInPolyTime_parameters` in
`Complexity/Computability/Complexity/CookLevin/Parameters.lean`).
Variable construction and numbering are certified in
`Complexity/Computability/Complexity/CookLevin/Encoding.lean`, and all clause
families in `Complexity/Computability/Complexity/CookLevin/Clauses.lean`.
`Complexity/Computability/Complexity/CookLevin/PolyTime.lean` certifies the complete reduction;
`Complexity/Computability/Complexity/CookLevin/Completeness.lean` derives unconditional
NP-completeness of SAT and coNP-completeness
of UNSAT.

## Main definitions

* `Cslib.Complexity.CookLevin.featureIndex`, `Cslib.Complexity.CookLevin.Var.index`: injective
  numberings of the features and of the tableau variables.
* `Cslib.Complexity.CookLevin.parameters`: the input prefix, certificate length and time bound.
* `Cslib.Complexity.CookLevin.reduce`: the reduction.

## Main results

* `Cslib.Complexity.CookLevin.reduce_mem_SAT_iff`: correctness of the reduction.
* `Cslib.Complexity.CookLevin.reduce_mem_SAT_iff_of_computesTidily`: the same for a verifier
  computed tidily.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 2.3.
-/

@[expose] public section

namespace Cslib.Complexity.CookLevin

open Turing Turing.MultiTapeTM Cslib.Logic.PL

variable {k : ℕ} {State : Type} [Fintype State]

/-! ### Numbering the variables -/

/-- The index of a control state, through `Fintype.equivFin`, with `none` first. -/
noncomputable def stateIndex (q : Option State) : ℕ :=
  q.elim 0 fun q => Fintype.equivFin State q + 1

theorem stateIndex_injective : Function.Injective (stateIndex (State := State)) := by
  rintro (_ | a) (_ | b) h
  · rfl
  · exact absurd h (by simp [stateIndex])
  · exact absurd h (by simp [stateIndex])
  · simp only [stateIndex, Option.elim_some, Nat.add_right_cancel_iff, Fin.val_inj] at h
    rw [(Fintype.equivFin State).injective h]

/-- The number of a feature: its constructor and its arguments, combined with `Nat.pair`, with
work-tape cells numbered through `Equiv.intEquivNat`, tape symbols through `Encodable.encode`
(blank, `false`, `true` as `0, 1, 2`), and situations through `Fintype.equivFin`. -/
noncomputable def featureIndex : Feature k State → ℕ
  | .state q => Nat.pair 0 (stateIndex q)
  | .inPos j => Nat.pair 1 j
  | .head i z => Nat.pair 2 (Nat.pair i (Equiv.intEquivNat z))
  | .cell i z s => Nat.pair 3 (Nat.pair i (Nat.pair (Equiv.intEquivNat z) (Encodable.encode s)))
  | .out o => Nat.pair 4 o.index
  | .read i s => Nat.pair 5 (Nat.pair i (Encodable.encode s))
  | .inRead s => Nat.pair 6 (Encodable.encode s)
  | .sit y => Nat.pair 7 (Fintype.equivFin (Situation k State) y)

theorem featureIndex_injective : Function.Injective (featureIndex (k := k) (State := State)) := by
  intro a b h
  rcases a <;> rcases b <;> simp_all [featureIndex, Nat.pair_eq_pair, stateIndex_injective.eq_iff,
    Encodable.encode_injective.eq_iff, OutView.index_injective.eq_iff,
    Equiv.intEquivNat.injective.eq_iff, Fin.val_inj]

/-- The number of a tableau variable. -/
noncomputable def Var.index : Var k State → ℕ
  | .holds t φ => Nat.pair 0 (Nat.pair t (featureIndex φ))
  | .cert j => Nat.pair 1 j

theorem Var.index_injective : Function.Injective (Var.index (k := k) (State := State)) := by
  intro a b h
  rcases a <;> rcases b <;> simp_all [Var.index, Nat.pair_eq_pair, featureIndex_injective.eq_iff]

/-! ### The reduction -/

variable [DecidableEq State] {α : Type}

/-- The framed input prefix, certificate length and verifier time bound supplied to the tableau.
The verifier is allowed `c * (n + 1) ^ d` steps on an input of encoded length `n`.
The tuple wrapper is reducible so projection clients can compute its components directly. -/
@[reducible]
def parameters (p : Polynomial ℕ) (c d : ℕ) (enc : α ↪ List Bool) (a : α) :
    List Bool × ℕ × ℕ :=
  (frame (enc a), p.eval (enc a).length,
    c * (2 * (enc a).length + 1 + p.eval (enc a).length + 1) ^ d)

/-- The Cook–Levin reduction for the verifier computed by `tm` within `c * (n + 1) ^ d` steps on
inputs of length `n`, with certificates of length `p` of the instance length: the tableau of `tm`
on inputs `frame (enc a) ++ w`, unrolled for exactly the allowed number of steps. -/
noncomputable def reduce (tm : MultiTapeTM k Bool State) (p : Polynomial ℕ) (c d : ℕ)
    (enc : α ↪ List Bool) (a : α) : CNF ℕ :=
  let q := parameters p c d enc a
  (tableau tm q.1 q.2.1 q.2.2).relabel Var.index

/-- **Correctness of the Cook–Levin reduction.** If `V` verifies `A` with certificates of length
`p`, and on every input `frame (enc a) ++ w` with `|w| = p (enc a).length` the machine `tm` has
halted with output `[V (a, w)]` after `c * (|frame (enc a) ++ w| + 1) ^ d` steps, then
`reduce tm p c d enc a` is satisfiable exactly when `a ∈ A`. -/
theorem reduce_mem_SAT_iff {enc : α ↪ List Bool} {A : Set α} {p : Polynomial ℕ}
    {V : α × List Bool → Bool} (hV : IsVerifier enc p V A) {tm : MultiTapeTM k Bool State}
    {c d : ℕ} (a : α)
    (hrun : ∀ w : List Bool, w.length = p.eval (enc a).length →
      (tm.runFrom (tm.initCfg (encPair enc encBits (a, w)))
          (c * ((encPair enc encBits (a, w)).length + 1) ^ d)).state = none ∧
        (tm.runFrom (tm.initCfg (encPair enc encBits (a, w)))
          (c * ((encPair enc encBits (a, w)).length + 1) ^ d)).output = [V (a, w)]) :
    reduce tm p c d enc a ∈ SAT ↔ a ∈ A := by
  rw [mem_SAT, reduce, parameters, CNF.satisfiable_relabel Var.index_injective,
    tableau_satisfiable_iff, hV a]
  refine exists_congr fun w => and_congr_right fun hw => ?_
  have hlen : (encPair enc encBits (a, w)).length =
      2 * (enc a).length + 1 + p.eval (enc a).length := by
    rw [length_encPair, encBits_apply, hw]
  obtain ⟨hhalt, hout⟩ := hrun w hw
  rw [hlen, encPair_apply, encBits_apply] at hhalt hout
  rw [hhalt, hout]
  simp

/-- `reduce_mem_SAT_iff` for a machine computing the verifier tidily within
`c * (n + 1) ^ d` steps. -/
theorem reduce_mem_SAT_iff_of_computesTidily {enc : α ↪ List Bool} {A : Set α} {p : Polynomial ℕ}
    {V : α × List Bool → Bool} (hV : IsVerifier enc p V A) {tm : MultiTapeTM k Bool State}
    {c d : ℕ} {s : α × List Bool → ℕ}
    (htm : tm.ComputesFunTidilyInTimeAndSpace (encPair enc encBits) encBool V
      (fun x => c * ((encPair enc encBits x).length + 1) ^ d) s) (a : α) :
    reduce tm p c d enc a ∈ SAT ↔ a ∈ A :=
  reduce_mem_SAT_iff hV a fun w _ => (htm (a, w)).runFrom_initCfg

end Cslib.Complexity.CookLevin
