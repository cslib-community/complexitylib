/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Advice
public import CslibFrontier.Computability.Complexity.Reduction
import CslibFrontier.Computability.Complexity.Reduction.Word
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Foundations.Data.List.TakeQuantifiers
import Cslib.Foundations.Data.Polynomial.Monotone

/-!
# Closure properties of `P/poly`

This module proves closure properties of `PPolyOn enc` that go beyond its Boolean operations
(`Cslib.Circuits.Boolean.PPolyOn.compl`, `Cslib.Circuits.Boolean.PPolyOn.sup`,
`Cslib.Circuits.Boolean.PPolyOn.inf`). These are the facts that circuit lower-bound and
magnification arguments need to take from the Karp–Lipton theorem without importing its proof.

Preimages of `P/poly` are closed under polynomial-time many-one reductions
(`Cslib.Complexity.PolyTimeReducible.mem_PPolyOn`). The proof evaluates the circuits for the target
language from an advice string (`Cslib.Circuits.Boolean.PPoly.exists_evalAdvice`) and then hardwires
that string (`Cslib.Circuits.Boolean.PPoly.of_advice`).

The same advice-string mechanism eliminates quantifiers nonuniformly. Suppose `M ∈ P/poly`, and
replace `M` by an advice string listing its circuits up to length `2 |x| + 1 + p |x|`. This turns
the existential quantifier over `w` of length `p |x|` in `frame x ++ w ∈ M` into a language in `NP`.
Hence the existential projection remains in `P/poly` when `NP ⊆ P/poly`
(`Cslib.Complexity.mem_PPoly_of_exists_frame_append`)
[Karp and Lipton, Section 3][KarpLipton1980]. Combined with closure under reductions and complement,
this gives existential and universal quantifier elimination over polynomial-length witnesses for any
instance encoding.

## Main results

* `Cslib.Circuits.Boolean.PPolyOn.of_computableInPolyTime`: a predicate decided in polynomial time
  is in `PPolyOn`, a form of `P ⊆ P/poly` (`Cslib.Circuits.Boolean.P_subset_PPolyOn`).
* `Cslib.Circuits.Boolean.PPolyOn.imp`: closure of `PPolyOn` under implication.
* `Cslib.Complexity.PolyTimeReducible.mem_PPolyOn`: preimages of `P/poly` are closed under
  polynomial-time many-one reductions.
* `Cslib.Complexity.mem_PPoly_of_exists_frame_append`,
  `Cslib.Complexity.PPolyOn.exists_of_computableInPolyTime_length`,
  `Cslib.Complexity.PPolyOn.forall_of_computableInPolyTime_length`: nonuniform existential and
  universal quantifier elimination in `P/poly` under `NP ⊆ P/poly`.

## References

* [R. M. Karp, R. J. Lipton, *Some connections between nonuniform and uniform complexity
  classes*][KarpLipton1980]
-/

public section

namespace Cslib.Circuits.Boolean

open Turing.MultiTapeTM

/-- **Polynomial-time predicates are in `P/poly`.** If `f` is computable in polynomial time, then
the set of instances on which `f` is `true` is in `PPolyOn enc`. -/
theorem PPolyOn.of_computableInPolyTime {α : Type} {enc : α ↪ List Bool}
    {f : α → Bool} (hf : ComputableInPolyTime f enc encBool) :
    {a : α | f a = true} ∈ PPolyOn enc :=
  P_subset_PPolyOn ⟨f, hf, fun _ => Iff.rfl⟩

/-- **`PPolyOn` is closed under implication.** -/
theorem PPolyOn.imp {α : Type} {enc : α ↪ List Bool} {P Q : α → Prop}
    (hP : {a | P a} ∈ PPolyOn enc) (hQ : {a | Q a} ∈ PPolyOn enc) :
    {a | P a → Q a} ∈ PPolyOn enc := by
  have h : {a | P a → Q a} = {a | P a}ᶜ ∪ {a | Q a} := by
    ext a
    simp [imp_iff_not_or]
  rw [h]
  exact PPolyOn.sup (PPolyOn.compl hP) hQ

end Cslib.Circuits.Boolean

namespace Cslib.Complexity

open Circuits Circuits.Boolean Turing.MultiTapeTM ComputableInPolyTime

variable {α : Type} {enc : α ↪ List Bool}

/-- **Preimages of `P/poly` are closed under polynomial-time reductions.** If `A` reduces to `B`
in polynomial time and `B` is the preimage under `encB` of a language in `P/poly`, then `A` is
the preimage under `enc` of a language in `P/poly`: evaluating the circuits for `B` up to the
polynomial output-length bound of the reduction from an advice string is polynomial-time, and
hardwiring the advice string (`PPoly.of_advice`) gives circuits of polynomial size. -/
theorem PolyTimeReducible.mem_PPolyOn {β : Type} {encB : β ↪ List Bool} {A : Set α}
    {B : Set β} (hAB : PolyTimeReducible enc encB A B)
    (hB : B ∈ PPolyOn encB) :
    A ∈ PPolyOn enc := by
  obtain ⟨f, hf, hiff⟩ := hAB
  obtain ⟨L_B, hL_B, hLB⟩ := hB
  obtain ⟨c', d', hf'⟩ := hf.polyBounded_length.exists_le
  let N : Polynomial ℕ := Polynomial.C c' * (Polynomial.X + 1) ^ d'
  obtain ⟨S, W, _, α_adv, -, hα, h_eval⟩ := PPoly.exists_evalAdvice hL_B N
  have hN (a : α) : (encB (f a)).length ≤ N.eval (enc a).length := by
    refine (hf' a).trans (le_of_eq ?_)
    simp [N]
  let g : List Bool × α → Bool := fun x =>
    evalAdvice (S.eval (enc x.2).length) (W.eval (enc x.2).length) x.1 (encB (f x.2))
  have hg : ComputableInPolyTime g (encPair encBits enc) encBool := by fun_prop
  obtain ⟨M, hM, hgM⟩ := PPoly.exists_of_polyTime hg
  let L : Language Bool := {x : List Bool | frame (α_adv x.length) ++ x ∈ M}
  refine ⟨L, PPoly.of_advice hM α_adv hα (fun _ => Iff.rfl), fun a => ?_⟩
  change a ∈ A ↔ frame (α_adv (enc a).length) ++ enc a ∈ M
  have hgM' := hgM (α_adv (enc a).length, a)
  rw [encPair_apply, encBits_apply] at hgM'
  rw [hiff a, hLB (f a), ← hgM']
  exact (h_eval (enc a).length (encB (f a)) (hN a)).symm

/-- **Nonuniform quantifier elimination.** If every language in `NP` over `Bool` is in `P/poly`
and `M` is in `P/poly`, then the language of words `x` for which `frame x ++ w ∈ M` for some `w` of
length `p |x|` is in `P/poly`: replacing `M` by an advice string listing its circuits up to length
`2 |x| + 1 + p |x|` turns the existential quantifier over `w` into a language in `NP`, and
hardwiring the advice string (`Cslib.Circuits.Boolean.PPoly.of_advice`) gives circuits of
polynomial size [Karp and Lipton, Section 3][KarpLipton1980]. -/
theorem mem_PPoly_of_exists_frame_append
    (hNP : NP encBits ⊆ PPolyOn encBits)
    {M : Language Bool} (hM : M ∈ PPoly) (p : Polynomial ℕ) :
    ({x : List Bool | ∃ w : List Bool, w.length = p.eval x.length ∧ frame x ++ w ∈ M} :
      Language Bool) ∈ PPoly := by
  let N : Polynomial ℕ := 2 * Polynomial.X + 1 + p
  obtain ⟨S, W, _, α_adv, -, hα, h_eval⟩ := PPoly.exists_evalAdvice hM N
  have hN (n : ℕ) : N.eval n = 2 * n + 1 + p.eval n := by
    simp [N, Polynomial.eval_add, Polynomial.eval_mul]
  let V : List Bool × List Bool → Bool := fun z =>
    evalAdvice (S.eval (dropFrame z.1).length) (W.eval (dropFrame z.1).length) (unframe z.1)
      (frame (dropFrame z.1) ++ z.2.take (p.eval (dropFrame z.1).length))
  have hV : ComputableInPolyTime V (encPair encBits encBits) encBool := by fun_prop
  let D : Language Bool := {z : List Bool | ∃ w : List Bool, w.length = p.eval z.length ∧
    V (z, w) = true}
  have hD : D ∈ PPoly := mem_PPolyOn_encBits_iff.1 (hNP ⟨p, V, hV, fun _ => Iff.rfl⟩)
  refine PPoly.of_advice hD α_adv hα fun x => ?_
  change (∃ w : List Bool, w.length = p.eval x.length ∧ frame x ++ w ∈ M) ↔
    (∃ w : List Bool, w.length = p.eval (frame (α_adv x.length) ++ x).length ∧
      V (frame (α_adv x.length) ++ x, w) = true)
  have hle : p.eval x.length ≤ p.eval (frame (α_adv x.length) ++ x).length :=
    p.eval_mono (by simp)
  have hV_frame (w : List Bool) (hw : w.length = p.eval x.length) :
      frame x ++ w ∈ M ↔
        evalAdvice (S.eval x.length) (W.eval x.length) (α_adv x.length) (frame x ++ w) = true :=
    (h_eval x.length (frame x ++ w) (by simp [hN, hw])).symm
  simp only [V, unframe_frame_append, dropFrame_frame_append]
  exact (exists_congr fun w => and_congr_right (hV_frame w)).trans
    (List.exists_length_eq_take_iff (P := fun u =>
      evalAdvice (S.eval x.length) (W.eval x.length) (α_adv x.length) (frame x ++ u) = true)
      hle).symm

/-- **Nonuniform existential quantifier elimination in `PPolyOn`.** Under `NP ⊆ P/poly`, if a
relation `P : α → List Bool → Prop` is in `PPolyOn (encPair enc encBits)` and the witness length
`N : α → ℕ` is computable in polynomial time in unary, then `{a | ∃ u, u.length = N a ∧ P a u}` is
in `PPolyOn enc`. -/
theorem PPolyOn.exists_of_computableInPolyTime_length
    (hNP : NP encBits ⊆ PPolyOn encBits) {N : α → ℕ}
    (hN : ComputableInPolyTime N enc encUnary) {P : α → List Bool → Prop}
    (hP : {p : α × List Bool | P p.1 p.2} ∈ PPolyOn (encPair enc encBits)) :
    {a : α | ∃ u : List Bool, u.length = N a ∧ P a u} ∈ PPolyOn enc := by
  obtain ⟨M, hM, hBM⟩ := (polyTimeReducible_take hN {p : α × List Bool | P p.1 p.2}).mem_PPolyOn hP
  obtain ⟨p, hp⟩ := hN.polyBounded.exists_polynomial
  refine ⟨{x : List Bool | ∃ w : List Bool, w.length = p.eval x.length ∧ frame x ++ w ∈ M},
    mem_PPoly_of_exists_frame_append hNP hM p, fun a => ?_⟩
  have hBM' (w : List Bool) : P a (w.take (N a)) ↔ frame (enc a) ++ w ∈ M := by
    simpa [encPair_apply, encBits_apply] using hBM (a, w)
  exact (List.exists_length_eq_take_iff (P := P a) (hp a)).symm.trans
    (exists_congr fun w => and_congr_right fun _ => hBM' w)

/-- **Nonuniform universal quantifier elimination in `PPolyOn`.** Under `NP ⊆ P/poly`, if a
relation `P : α → List Bool → Prop` is in `PPolyOn (encPair enc encBits)` and the bound `N : α → ℕ`
is computable in polynomial time in unary, then `{a | ∀ u, u.length = N a → P a u}` is in
`PPolyOn enc`. -/
theorem PPolyOn.forall_of_computableInPolyTime_length
    (hNP : NP encBits ⊆ PPolyOn encBits) {N : α → ℕ}
    (hN : ComputableInPolyTime N enc encUnary) {P : α → List Bool → Prop}
    (hP : {p : α × List Bool | P p.1 p.2} ∈ PPolyOn (encPair enc encBits)) :
    {a : α | ∀ u : List Bool, u.length = N a → P a u} ∈ PPolyOn enc := by
  have hex : {a : α | ∃ u : List Bool, u.length = N a ∧ ¬ P a u} ∈ PPolyOn enc :=
    PPolyOn.exists_of_computableInPolyTime_length hNP hN (PPolyOn.compl hP)
  have h_eq : {a : α | ∀ u : List Bool, u.length = N a → P a u} =
      {a : α | ∃ u : List Bool, u.length = N a ∧ ¬ P a u}ᶜ := by
    ext a
    simp
  rw [h_eq]
  exact PPolyOn.compl hex

end Cslib.Complexity
