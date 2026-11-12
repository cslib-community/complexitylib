/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.CarrySave
public import CslibFrontier.Foundations.Combinatorics.MajorityTree
import Mathlib.Tactic

/-!
# Majority trees of formulas

A majority tree of depth `L` over `3 ^ L` De Morgan formulas (`majTreeFormula`) computes the
majority tree `Cslib.majTree` of their values (`eval_majTreeFormula`). Each level is the
three-input majority formula `maj3Formula` with the subtrees substituted for its inputs, so it adds
three levels of AND and OR gates (`depthWith_majTreeFormula_le`).

With the amplification of `Cslib.exists_forall_majTree_majTree_eq`, this gives the formula form of
[ChukhinKulikovMihajlinSmal2026], Lemma 3.7 (printed p. 8; PDF p. 9), which goes back to
[Valiant1984Majority]. Let a weighted family of formulas of depth at most `d` be correct with
probability at least `1/2 + ε` at every point of a finite set `S`. Then some single formula of
depth at most `d + 3 (m₁ + 1) + 3 m₂` is correct on all of `S`, where `(11/8)^{m₁} ε ≥ 1/4` and
`|S| ≤ 2^{2^{m₂}}` (`exists_eq_of_forall_sum_ne_le`). The source states the added depth as
`O(log (1/ε) + log log |Z|)`; here `m₁` and `m₂` are explicit.

## Main definitions

* `Cslib.Circuits.Boolean.maj3Of`: the majority of three formulas.
* `Cslib.Circuits.Boolean.majTreeFormula`: the majority tree of formulas.

## Main results

* `Cslib.Circuits.Boolean.eval_majTreeFormula`,
  `Cslib.Circuits.Boolean.depthWith_majTreeFormula_le`: what it computes and its depth.
* `Cslib.Circuits.Boolean.exists_eq_of_forall_sum_ne_le`: Lemma 3.7 for formulas.

## References

* [N. Chukhin, A. S. Kulikov, I. Mihajlin and A. V. Smal, *Solving One of Many Instances is
  Almost as Hard as Solving One*][ChukhinKulikovMihajlinSmal2026]
* [L. G. Valiant, *Short monotone formulae for the majority function*][Valiant1984Majority]
-/

public section

namespace Cslib.Circuits.Boolean

open Formula

variable {n : ℕ}

/-- The three-input majority of `Cslib.majTree` is the carry of a full adder on Booleans. -/
theorem majority_maj3_eq_maj3 (a b c : Bool) : Cslib.maj3 a b c = maj3 a b c := by
  cases a <;> cases b <;> cases c <;> rfl

/-- The majority of three formulas: `maj3Formula` with them substituted for its inputs. -/
@[expose] def maj3Of (F G H : Formula signature n) : Formula signature n :=
  (maj3Formula (0 : Fin 3) 1 2).bind ![F, G, H]

/-- The majority formula computes the majority of the values. -/
@[simp] theorem eval_maj3Of (F G H : Formula signature n) (x : BitString n) :
    (maj3Of F G H).eval interpretation x =
      Cslib.maj3 (F.eval interpretation x) (G.eval interpretation x) (H.eval interpretation x) := by
  simp [maj3Of, majority_maj3_eq_maj3]

/-- The majority formula adds three levels of AND and OR gates. -/
theorem depthWith_maj3Of_le {F G H : Formula signature n} {d : ℕ}
    (hF : F.depthWith binaryCost ≤ d) (hG : G.depthWith binaryCost ≤ d)
    (hH : H.depthWith binaryCost ≤ d) : (maj3Of F G H).depthWith binaryCost ≤ d + 3 := by
  have h := depthWith_bind_le (cost := binaryCost) (s := ![F, G, H]) (c := d)
    (fun i => by fin_cases i <;> assumption) (maj3Formula (0 : Fin 3) 1 2)
  have h3 : (maj3Formula (0 : Fin 3) 1 2).depthWith binaryCost ≤ 3 := by
    simp [maj3Formula]
  rw [maj3Of]
  omega

/-- **The majority tree of formulas** of depth `L` over `3 ^ L` formulas, with the blocks of
`Cslib.majTree`. -/
@[expose] def majTreeFormula : (L : ℕ) → (Fin (3 ^ L) → Formula signature n) → Formula signature n
  | 0, V => V ⟨0, by simp⟩
  | L + 1, V => maj3Of (majTreeFormula L fun k => V (tripleEquiv L (0, k)))
      (majTreeFormula L fun k => V (tripleEquiv L (1, k)))
      (majTreeFormula L fun k => V (tripleEquiv L (2, k)))

/-- The majority tree of formulas computes the majority tree of their values. -/
@[simp] theorem eval_majTreeFormula :
    ∀ (L : ℕ) (V : Fin (3 ^ L) → Formula signature n) (x : BitString n),
      (majTreeFormula L V).eval interpretation x = majTree L fun i => (V i).eval interpretation x
  | 0, V, x => rfl
  | L + 1, V, x => by
    simp only [majTreeFormula, eval_maj3Of, eval_majTreeFormula L]
    rfl

/-- A majority tree of depth `L` over formulas of depth at most `d` has depth at most
`d + 3 L`. -/
theorem depthWith_majTreeFormula_le {d : ℕ} :
    ∀ (L : ℕ) (V : Fin (3 ^ L) → Formula signature n),
      (∀ i, (V i).depthWith binaryCost ≤ d) →
        (majTreeFormula L V).depthWith binaryCost ≤ d + 3 * L
  | 0, V, hV => (hV _).trans (Nat.le_add_right _ _)
  | L + 1, V, hV => by
    have h := depthWith_maj3Of_le
      (depthWith_majTreeFormula_le L (fun k => V (tripleEquiv L (0, k))) fun k => hV _)
      (depthWith_majTreeFormula_le L (fun k => V (tripleEquiv L (1, k))) fun k => hV _)
      (depthWith_majTreeFormula_le L (fun k => V (tripleEquiv L (2, k))) fun k => hV _)
    exact h.trans (by omega)

/-- **[ChukhinKulikovMihajlinSmal2026], Lemma 3.7, for formulas.** Let `w` be a probability
vector on a finite type `Ω`, and `H ω` formulas of `binaryCost` depth at most `d`. If at every
point `x` of a finite set `S` the formulas that miss `f x` have weight at most `1/2 - ε`, then
some single formula of depth at most `d + 3 (m₁ + 1) + 3 m₂` computes `f` on `S`, whenever
`(11/8)^{m₁} ε ≥ 1/4` and `|S| ≤ 2^{2^{m₂}}`. The formula is a majority tree of majority trees
of the `H ω`. -/
theorem exists_eq_of_forall_sum_ne_le {Ω : Type*} [Fintype Ω] {w : Ω → ℝ}
    (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω = 1) {H : Ω → Formula signature n} {d : ℕ}
    (hH : ∀ ω, (H ω).depthWith binaryCost ≤ d) (S : Finset (BitString n))
    (f : BitString n → Bool) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ x ∈ S, ∑ ω with (H ω).eval interpretation x ≠ f x, w ω ≤ 1 / 2 - ε)
    {m₁ m₂ : ℕ} (hm₁ : 1 / 4 ≤ (11 / 8) ^ m₁ * ε) (hS : S.card ≤ 2 ^ (2 ^ m₂)) :
    ∃ G : Formula signature n, (∀ x ∈ S, G.eval interpretation x = f x) ∧
      G.depthWith binaryCost ≤ d + 3 * (m₁ + 1) + 3 * m₂ := by
  obtain ⟨V, hV⟩ := exists_forall_majTree_majTree_eq hw hw1 S
    (fun x ω => (H ω).eval interpretation x) f hε h hm₁ hS
  refine ⟨majTreeFormula m₂ fun i => majTreeFormula (m₁ + 1) (H ∘ V i), fun x hx => ?_, ?_⟩
  · simpa [Function.comp_def] using hV x hx
  · have := depthWith_majTreeFormula_le m₂ (d := d + 3 * (m₁ + 1)) _ fun i =>
      depthWith_majTreeFormula_le (m₁ + 1) (H ∘ V i) fun k => hH _
    omega

end Cslib.Circuits.Boolean
