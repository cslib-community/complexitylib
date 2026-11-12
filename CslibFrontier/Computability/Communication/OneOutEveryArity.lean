/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.OneOutLowerBound
public import CslibFrontier.Computability.Communication.Rectangle
import Mathlib.Tactic

/-!
# The one-out-of-`k` lower bound at every arity

[ChukhinKulikovMihajlinSmal2026], Corollary 1.4 (printed pp. 1, 12; PDF pp. 2, 13): there are
absolute constants `0 < c ≤ 1` and `C > 0` with `CC(OneOut_k(F)) ≥ c · CC(F) - C log n` for
every `1 ≤ k ≤ min {|A|, |B|}`. Here the constants are explicit: `ecomplexity_le_mul_oneOut`
proves `CC(R) ≤ 19 · CC(OneOut_k(R)) + ⌈log₂ |Z|⌉ + 3 ⌈log₂ (n + 1)⌉ + 3` for every total
relation `R`, so `c = 1/19`.

The proof follows the source. A protocol `p` of depth `d` for `OneOut_k(R)` answers only at the
coordinates named at its leaves (`leafIndices`), at most `2 ^ d` of them. Restricting to these
`r` coordinates, and filling the other coordinates with fixed distinct inputs
(`Function.Embedding.exists_extend_of_card_le`), solves `OneOut_r(R)` in depth `d`
(`exists_solves_leafIndices`). Theorem 1.2 with arity `r` then costs `18 ⌈log₂ r⌉ ≤ 18 d`.

The formula-depth half of Corollary 1.4 is `Cslib.Circuits.Boolean.partialFormulaDepth_le_mul`.

## Main definitions

* `Cslib.Communication.OneOut.leafIndices`: the coordinates named at the leaves of a protocol.

## Main results

* `Function.Embedding.exists_extend_of_card_le`: an embedding into a finite type extends along
  an embedding of its domain into one at most as large as the target.
* `Cslib.Communication.OneOut.exists_solves_leafIndices`: the protocol restricted to the
  coordinates named at its leaves.
* `Cslib.Communication.OneOut.ecomplexity_le_mul_oneOut`: Corollary 1.4 for total relations.
* `Cslib.Communication.OneOut.ecomplexityFun_le_mul_oneOut`: Corollary 1.4 for Boolean functions.
-/

public section

/-- An embedding `x : α ↪ γ` into a finite type extends along an embedding `e : α ↪ β` of
finite types, when `β` is at most as large as `γ`. -/
theorem Function.Embedding.exists_extend_of_card_le {α β γ : Type*} [Finite α] [Fintype β]
    [Fintype γ] (e : α ↪ β) (x : α ↪ γ) (h : Fintype.card β ≤ Fintype.card γ) :
    ∃ x' : β ↪ γ, ∀ a, x' (e a) = x a := by
  classical
  have := Fintype.ofFinite α
  rcases isEmpty_or_nonempty γ with hγ | hγ
  · have : IsEmpty β := Fintype.card_eq_zero_iff.mp (by simpa using h)
    have : IsEmpty α := Function.isEmpty e
    exact ⟨Function.Embedding.ofIsEmpty, isEmptyElim⟩
  have c : γ := Classical.choice hγ
  have hs : (Finset.univ.image x).card ≤ Fintype.card β := by
    rw [Finset.card_image_of_injective _ x.injective, Finset.card_univ]
    exact Fintype.card_le_of_embedding e
  obtain ⟨t, hst, -, ht⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ _) hs
    (by simpa using h)
  set f : β → γ := Function.extend e x fun _ => c
  have hf (a : α) : f (e a) = x a := e.injective.extend_apply _ _ a
  obtain ⟨g, hg⟩ := Set.MapsTo.exists_equiv_extend_of_card_eq (s := Set.range e) (f := f)
    (t := t) ht.symm
    (by rintro _ ⟨a, rfl⟩; exact hst (by simp [hf]))
    (by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab; simp only [hf] at hab; rw [x.injective hab])
  exact ⟨g.toEmbedding.trans (Function.Embedding.subtype _), fun a => by
    simp [hg (e a) ⟨a, rfl⟩, hf]⟩

namespace Cslib.Communication.OneOut

open Protocol

variable {X Y Z : Type*} {k : ℕ}

/-- The coordinates named at the leaves of a protocol for the one-out-of-`k` problem. -/
@[expose] def leafIndices (p : Protocol (Fin k ↪ X) (Fin k ↪ Y) (Answer k Z)) : Finset (Fin k) :=
  Finset.univ.image fun i => (p.leafOutput i).index

/-- A protocol of depth `d` names at most `2 ^ d` coordinates at its leaves. -/
theorem card_leafIndices_le (p : Protocol (Fin k ↪ X) (Fin k ↪ Y) (Answer k Z)) :
    (leafIndices p).card ≤ 2 ^ p.depth :=
  Finset.card_image_le.trans (by simpa using p.leafCount_le_two_pow_depth)

/-- Every run answers at a coordinate named at a leaf. -/
theorem index_run_mem_leafIndices (p : Protocol (Fin k ↪ X) (Fin k ↪ Y) (Answer k Z))
    (x : Fin k ↪ X) (y : Fin k ↪ Y) : (p.run x y).index ∈ leafIndices p := by
  rw [run_eq_leafOutput_leaf]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

/-- Some coordinate is named at a leaf. -/
theorem card_leafIndices_pos (p : Protocol (Fin k ↪ X) (Fin k ↪ Y) (Answer k Z)) :
    0 < (leafIndices p).card :=
  Finset.card_pos.mpr ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ⟨0, p.leafCount_pos⟩)⟩

variable {R : X → Y → Z → Prop}

open scoped Classical in
/-- **Restriction to the coordinates named at the leaves** (proof of
[ChukhinKulikovMihajlinSmal2026], Corollary 1.4, printed p. 12; PDF p. 13). If `p` solves the
one-out-of-`k` problem and both players have at least `k` inputs, then the one-out-of-`r`
problem, for the number `r` of coordinates named at the leaves of `p`, has a protocol of at most
the same depth: the players place their `r` inputs at those coordinates, fill the others with
distinct inputs by a fixed rule, and run `p`. -/
theorem exists_solves_leafIndices [Fintype X] [Fintype Y]
    (hX : k ≤ Fintype.card X) (hY : k ≤ Fintype.card Y)
    {p : Protocol (Fin k ↪ X) (Fin k ↪ Y) (Answer k Z)}
    (hp : p.Solves (Relation R) Set.univ Set.univ) :
    ∃ q : Protocol (Fin (leafIndices p).card ↪ X) (Fin (leafIndices p).card ↪ Y)
      (Answer (leafIndices p).card Z),
      q.Solves (Relation R) Set.univ Set.univ ∧ q.depth ≤ p.depth := by
  set I := leafIndices p
  set σ := I.orderIsoOfFin rfl
  let e : Fin I.card ↪ Fin k := (σ.toEquiv.toEmbedding).trans (Function.Embedding.subtype _)
  have he (j : Fin I.card) : e j = (σ j : Fin k) := rfl
  have hcard : Fintype.card (Fin k) = k := Fintype.card_fin k
  let extX (x : Fin I.card ↪ X) : Fin k ↪ X :=
    (Function.Embedding.exists_extend_of_card_le e x (hcard.trans_le hX)).choose
  let extY (y : Fin I.card ↪ Y) : Fin k ↪ Y :=
    (Function.Embedding.exists_extend_of_card_le e y (hcard.trans_le hY)).choose
  have hextX (x : Fin I.card ↪ X) (j) : extX x (e j) = x j :=
    (Function.Embedding.exists_extend_of_card_le e x (hcard.trans_le hX)).choose_spec j
  have hextY (y : Fin I.card ↪ Y) (j) : extY y (e j) = y j :=
    (Function.Embedding.exists_extend_of_card_le e y (hcard.trans_le hY)).choose_spec j
  let back (i : Fin k) : Fin I.card :=
    if h : i ∈ I then σ.symm ⟨i, h⟩ else ⟨0, card_leafIndices_pos p⟩
  have hback {i : Fin k} (h : i ∈ I) : e (back i) = i := by
    simp only [back, h, dite_true, he, OrderIso.apply_symm_apply]
  refine ⟨(p.comap extX extY).map fun a => ⟨back a.index, a.value⟩, fun x _ y _ => ?_, by simp⟩
  have hr := hp (extX x) trivial (extY y) trivial
  have hmem := index_run_mem_leafIndices p (extX x) (extY y)
  simp only [Relation, run_map, run_comap] at hr ⊢
  rw [← hextX x, ← hextY y, hback hmem]
  exact hr

/-- `⌈log₂ |leafIndices p|⌉` is at most the depth of `p`. -/
private theorem clog_card_leafIndices_le (p : Protocol (Fin k ↪ X) (Fin k ↪ Y) (Answer k Z)) :
    Nat.clog 2 (leafIndices p).card ≤ p.depth :=
  Nat.clog_le_of_le_pow (card_leafIndices_le p)

/-- **[ChukhinKulikovMihajlinSmal2026], Corollary 1.4, for total relations.** Let `R` be a total
relation on finite nonempty types with `|X|, |Y| ≤ 2ⁿ`, and let `k ≤ min {|X|, |Y|}`. Then
`CC(R) ≤ 19 · CC(OneOut_k(R)) + ⌈log₂ |Z|⌉ + 3 ⌈log₂ (n + 1)⌉ + 3`: a lower bound
`CC(OneOut_k(R)) ≥ CC(R)/19 - O(log |Z| + log n)` at every arity. The source's `k ≥ 1` is not
needed: for `k = 0` the one-out problem has no answers and complexity `⊤`. -/
theorem ecomplexity_le_mul_oneOut [Fintype X] [Fintype Y] [Fintype Z] [Nonempty X] [Nonempty Y]
    (htotal : ∀ x y, ∃ z, R x y z) {n : ℕ} (hX : Fintype.card X ≤ 2 ^ n)
    (hY : Fintype.card Y ≤ 2 ^ n) (hkX : k ≤ Fintype.card X) (hkY : k ≤ Fintype.card Y) :
    ecomplexity R Set.univ Set.univ ≤
      19 * ecomplexity (Relation (k := k) R) Set.univ Set.univ +
        (Nat.clog 2 (Fintype.card Z) + 3 * Nat.clog 2 (n + 1) + 3 : ℕ) := by
  by_cases h : ∃ p : Protocol (Fin k ↪ X) (Fin k ↪ Y) (Answer k Z),
      p.Solves (Relation R) Set.univ Set.univ
  · obtain ⟨p, hp, hpd⟩ := exists_solves_depth_eq_ecomplexity h
    obtain ⟨q, hq, hqd⟩ := exists_solves_leafIndices hkX hkY hp
    have h12 := ecomplexity_le_oneOut (k := (leafIndices p).card) htotal hX hY
    have hq' : ecomplexity (Relation (k := (leafIndices p).card) R) Set.univ Set.univ ≤
        (p.depth : ℕ∞) :=
      (ecomplexity_le_depth hq).trans (by exact_mod_cast hqd)
    have hlog := clog_card_leafIndices_le p
    rw [← hpd]
    refine h12.trans ?_
    calc max (ecomplexity (Relation (k := (leafIndices p).card) R) Set.univ Set.univ)
          ((Nat.clog 2 (Fintype.card Z) : ℕ) : ℕ∞) +
          ((18 * Nat.clog 2 (leafIndices p).card + 3 * Nat.clog 2 (n + 1) + 3 : ℕ) : ℕ∞)
        ≤ max (p.depth : ℕ∞) ((Nat.clog 2 (Fintype.card Z) : ℕ) : ℕ∞) +
          ((18 * p.depth + 3 * Nat.clog 2 (n + 1) + 3 : ℕ) : ℕ∞) := by
          gcongr
      _ ≤ 19 * (p.depth : ℕ∞) +
          ((Nat.clog 2 (Fintype.card Z) + 3 * Nat.clog 2 (n + 1) + 3 : ℕ) : ℕ∞) := by
          have hmax : ((max p.depth (Nat.clog 2 (Fintype.card Z)) : ℕ) : ℕ∞) =
              max (p.depth : ℕ∞) (Nat.clog 2 (Fintype.card Z) : ℕ) :=
            Monotone.map_max fun _ _ h => Nat.cast_le.mpr h
          rw [← hmax]
          exact_mod_cast (by omega : max p.depth (Nat.clog 2 (Fintype.card Z)) +
            (18 * p.depth + 3 * Nat.clog 2 (n + 1) + 3) ≤
              19 * p.depth + (Nat.clog 2 (Fintype.card Z) + 3 * Nat.clog 2 (n + 1) + 3))
  · rw [← ecomplexity_ne_top_iff, not_not] at h
    simp [h]

/-- **[ChukhinKulikovMihajlinSmal2026], Corollary 1.4, for Boolean functions.** For `F` on
finite nonempty types with `|X|, |Y| ≤ 2ⁿ` and `k ≤ min {|X|, |Y|}`,
`CC(F) ≤ 19 · CC(OneOut_k(F)) + 3 ⌈log₂ (n + 1)⌉ + 4`. -/
theorem ecomplexityFun_le_mul_oneOut [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (F : X → Y → Bool) {n : ℕ} (hX : Fintype.card X ≤ 2 ^ n) (hY : Fintype.card Y ≤ 2 ^ n)
    (hkX : k ≤ Fintype.card X) (hkY : k ≤ Fintype.card Y) :
    ecomplexityFun F ≤
      19 * ecomplexity (Relation (k := k) fun x y z => F x y = z) Set.univ Set.univ +
        (3 * Nat.clog 2 (n + 1) + 4 : ℕ) := by
  have h := ecomplexity_le_mul_oneOut (R := fun x y z => F x y = z)
    (fun x y => ⟨_, rfl⟩) hX hY hkX hkY
  rwa [Fintype.card_bool, show Nat.clog 2 2 = 1 by simpa using Nat.clog_pow 2 1 one_lt_two,
    show 1 + 3 * Nat.clog 2 (n + 1) + 3 = 3 * Nat.clog 2 (n + 1) + 4 by ring] at h

end Cslib.Communication.OneOut
