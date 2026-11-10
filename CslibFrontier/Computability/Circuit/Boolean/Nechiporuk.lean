/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Formula
public import CslibFrontier.Foundations.Data.BitString.PartialAssignment
public import Mathlib.Data.Nat.Log
public import Mathlib.Logic.Function.Const
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.NAry
import Mathlib.Tactic.NormNum

/-!
# Nechiporuk's bound

**Nechiporuk's lemma**: a formula over any basis of fan-in at most two (such as the full binary
basis `B₂`, or the De Morgan basis) with `l ≥ 1` leaves labelled by bits of a set `Y` has at most
`16 ^ l / 4` subfunctions on `Y` (`four_mul_card_subfunctions_le`), and at most `2` if `l = 0`, so
always at most `2 · 16 ^ l` (`card_subfunctions_le`). Fixing the other bits turns every subformula
without leaves in `Y` into a constant, every gate with one such argument into a unary function of
the other, and leaves the `l - 1` binary gates with two arguments that read `Y`; each of these
computes one of the `16` binary Boolean functions.

Over disjoint blocks `Y₁, …, Y_k` this gives **Nechiporuk's bound** [Nechiporuk1966],
[Jukna, Section 6.5][Jukna2012]: a formula of leaf size `L` over a basis of fan-in at most two
computing `f` has `∏ᵢ |subfunctions f Yᵢ| ≤ 2 ^ (4 L + k)` (`prod_card_subfunctions_le`), that is
`∑ᵢ ⌈log₂ |subfunctions f Yᵢ|⌉ ≤ 4 L + k` (`sum_clog_card_subfunctions_le`). Unlike Khrapchenko's
bound, it holds for the full binary basis.

## Main results

* `Cslib.Circuits.Boolean.card_subfunctions_le`: Nechiporuk's lemma.
* `Cslib.Circuits.Boolean.prod_card_subfunctions_le`,
  `Cslib.Circuits.Boolean.sum_clog_card_subfunctions_le`: Nechiporuk's bound.

## References

* [E. I. Nechiporuk, *On a Boolean function*][Nechiporuk1966]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Finset Function BitString

variable {n : ℕ}

/-! ### Closing under unary functions -/

/-- The functions `u ∘ g` for `g ∈ S` and `u : Bool → Bool`. -/
private def unaryClosure (S : Finset (BooleanFunction n)) : Finset (BooleanFunction n) :=
  image₂ (fun (u : Bool → Bool) g => u ∘ g) univ S

variable {S T : Finset (BooleanFunction n)} {g : BooleanFunction n}

private theorem comp_mem_unaryClosure (u : Bool → Bool) (hg : g ∈ S) :
    u ∘ g ∈ unaryClosure S :=
  mem_image₂_of_mem (mem_univ u) hg

private theorem subset_unaryClosure (S : Finset (BooleanFunction n)) : S ⊆ unaryClosure S :=
  fun _ hg => comp_mem_unaryClosure id hg

private theorem unaryClosure_subset (h : S ⊆ unaryClosure T) : unaryClosure S ⊆ unaryClosure T := by
  intro g hg
  obtain ⟨u, -, g', hg', rfl⟩ := mem_image₂.1 hg
  obtain ⟨v, -, g'', hg'', rfl⟩ := mem_image₂.1 (h hg')
  exact comp_mem_unaryClosure (u ∘ v) hg''

private theorem card_unaryClosure_le (S : Finset (BooleanFunction n)) :
    #(unaryClosure S) ≤ 4 * #S := by
  refine (card_image₂_le _ _ _).trans_eq ?_
  rw [card_univ]
  rfl

/-- Unary functions of constants are the two constants. -/
private theorem card_unaryClosure_le_two (h : ∀ g ∈ S, IsConst g) : #(unaryClosure S) ≤ 2 := by
  have hsub : unaryClosure S ⊆ {fun _ => false, fun _ => true} := by
    intro g hg
    obtain ⟨u, -, g', hg', rfl⟩ := mem_image₂.1 hg
    obtain ⟨c, hc⟩ := isConst_iff_exists_forall_eq.1 (h g' hg')
    have h' : u ∘ g' = fun _ => u c := funext fun x => by simp [hc x]
    rw [h']
    cases u c <;> simp
  exact (card_le_card hsub).trans (card_le_two)

/-! ### Nechiporuk's lemma -/

variable {σ : Signature} {I : Interpretation σ Bool}

/-- The subfunctions of a formula with no leaf in `Y` are constant. -/
theorem isConst_of_mem_subfunctions {F : Formula σ n} {Y : Finset (Fin n)}
    (hF : F.leafSizeIn Y = 0) (hg : g ∈ subfunctions (F.eval I) Y) : IsConst g := by
  obtain ⟨z, rfl⟩ := mem_subfunctions.1 hg
  exact fun x y => Formula.eval_piecewise_eq_of_leafSizeIn_eq_zero hF I x y z

/-- A gate computing `φ` with one argument whose subfunctions on `Y` are constant has subfunctions
that are unary functions of those of its other argument. -/
private theorem subfunctions_subset_of_isConst (φ : Bool → Bool → Bool)
    {F G H : Formula σ n} {Y : Finset (Fin n)}
    (hF : ∀ x, F.eval I x = φ (G.eval I x) (H.eval I x))
    (hG : G.leafSizeIn Y = 0) :
    subfunctions (F.eval I) Y ⊆ unaryClosure (subfunctions (H.eval I) Y)
    := by
  intro g hg
  obtain ⟨z, rfl⟩ := mem_subfunctions.1 hg
  obtain ⟨c, hc⟩ := isConst_iff_exists_forall_eq.1
    (isConst_of_mem_subfunctions (I := I) hG (mem_subfunctions.2 ⟨z, rfl⟩))
  have : (fun x => F.eval I (Y.piecewise x z)) =
      φ c ∘ fun x => H.eval I (Y.piecewise x z) := funext fun x => by simp [hF, hc x]
  rw [this]
  exact comp_mem_unaryClosure _ (mem_subfunctions.2 ⟨z, rfl⟩)

/-- The step of Nechiporuk's lemma at a gate computing a binary operation `φ`. -/
private theorem four_mul_card_le_of_binary (φ : Bool → Bool → Bool) {F G H : Formula σ n}
    {Y : Finset (Fin n)}
    (hF : ∀ x, F.eval I x = φ (G.eval I x) (H.eval I x))
    (hl : F.leafSizeIn Y = G.leafSizeIn Y + H.leafSizeIn Y)
    (ihG : 4 * #(unaryClosure (subfunctions (G.eval I) Y)) ≤
      max 8 (16 ^ G.leafSizeIn Y))
    (ihH : 4 * #(unaryClosure (subfunctions (H.eval I) Y)) ≤
      max 8 (16 ^ H.leafSizeIn Y)) :
    4 * #(unaryClosure (subfunctions (F.eval I) Y)) ≤ max 8 (16 ^ F.leafSizeIn Y) := by
  by_cases ha : G.leafSizeIn Y = 0
  · rw [hl, ha, zero_add]
    exact (Nat.mul_le_mul_left 4 (card_le_card (unaryClosure_subset
      (subfunctions_subset_of_isConst φ hF ha)))).trans ihH
  by_cases hb : H.leafSizeIn Y = 0
  · rw [hl, hb, add_zero]
    exact (Nat.mul_le_mul_left 4 (card_le_card (unaryClosure_subset
      (subfunctions_subset_of_isConst (Function.swap φ) (fun x => hF x) hb)))).trans ihG
  have hsub : subfunctions (F.eval I) Y ⊆
      image₂ (fun g h x => φ (g x) (h x)) (subfunctions (G.eval I) Y)
        (subfunctions (H.eval I) Y) := fun g hg => by
    obtain ⟨z, rfl⟩ := mem_subfunctions.1 hg
    exact mem_image₂.2 ⟨_, mem_subfunctions.2 ⟨z, rfl⟩, _, mem_subfunctions.2 ⟨z, rfl⟩,
      funext fun x => (hF _).symm⟩
  have h16 {l : ℕ} (hl : l ≠ 0) : 8 ≤ 16 ^ l :=
    (Nat.pow_le_pow_right (by decide) (Nat.one_le_iff_ne_zero.2 hl)).trans' (by decide)
  rw [max_eq_right (h16 ha)] at ihG
  rw [max_eq_right (h16 hb)] at ihH
  have hcard := (card_le_card hsub).trans (card_image₂_le _ _ _)
  have hxy := Nat.mul_le_mul (card_le_card (subset_unaryClosure
    (subfunctions (G.eval I) Y))) (card_le_card (subset_unaryClosure
      (subfunctions (H.eval I) Y)))
  have hF' := card_unaryClosure_le (subfunctions (F.eval I) Y)
  refine le_max_of_le_right ?_
  calc 4 * #(unaryClosure (subfunctions (F.eval I) Y))
      ≤ (4 * #(unaryClosure (subfunctions (G.eval I) Y))) *
          (4 * #(unaryClosure (subfunctions (H.eval I) Y))) := by
        rw [Nat.mul_mul_mul_comm]
        omega
    _ ≤ 16 ^ G.leafSizeIn Y * 16 ^ H.leafSizeIn Y := Nat.mul_le_mul ihG ihH
    _ = 16 ^ F.leafSizeIn Y := by rw [hl, pow_add]

/-- The step of Nechiporuk's lemma at a gate of arity `k ≤ 2` computing `φ`. -/
private theorem four_mul_card_le_of_gate {k : ℕ} (hk : k ≤ 2) (φ : (Fin k → Bool) → Bool)
    {F : Formula σ n} {args : Fin k → Formula σ n} {Y : Finset (Fin n)}
    (hF : ∀ x, F.eval I x = φ fun j => (args j).eval I x)
    (hl : F.leafSizeIn Y = ∑ j, (args j).leafSizeIn Y) (h0 : F.leafSizeIn Y ≠ 0)
    (ih : ∀ j, 4 * #(unaryClosure (subfunctions ((args j).eval I) Y)) ≤
      max 8 (16 ^ (args j).leafSizeIn Y)) :
    4 * #(unaryClosure (subfunctions (F.eval I) Y)) ≤ max 8 (16 ^ F.leafSizeIn Y) :=
  match k, hk, φ, args, hF, hl, ih with
  | 0, _, _, _, _, hl, _ => absurd (by simpa using hl) h0
  | 1, _, φ, args, hF, hl, ih => by
    have hsub : subfunctions (F.eval I) Y ⊆ unaryClosure (subfunctions ((args 0).eval I) Y) :=
      fun g hg => by
        obtain ⟨z, rfl⟩ := mem_subfunctions.1 hg
        have : (fun x => F.eval I (Y.piecewise x z)) =
            (fun b => φ fun _ => b) ∘ fun x => (args 0).eval I (Y.piecewise x z) :=
          funext fun x => (hF _).trans (congrArg φ (funext fun j => by rw [Fin.fin_one_eq_zero j]))
        rw [this]
        exact comp_mem_unaryClosure _ (mem_subfunctions.2 ⟨z, rfl⟩)
    rw [hl, Fin.sum_univ_one]
    exact (Nat.mul_le_mul_left 4 (card_le_card (unaryClosure_subset hsub))).trans (ih 0)
  | 2, _, φ, args, hF, hl, ih =>
    four_mul_card_le_of_binary (fun b c => φ ![b, c])
      (fun x => (hF x).trans (congrArg φ (funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩))))
      (hl.trans (Fin.sum_univ_two _)) (ih 0) (ih 1)
  | _ + 3, hk, _, _, _, _, _ => absurd hk (by omega)

/-- The invariant behind Nechiporuk's lemma: closed under unary functions, the subfunctions on `Y`
of a formula with `l` leaves in `Y` number at most `2` if `l = 0` and `16 ^ l / 4` otherwise. -/
private theorem four_mul_card_unaryClosure_le (harity : ∀ op, σ.Arity op ≤ 2) (F : Formula σ n)
    (Y : Finset (Fin n)) :
    4 * #(unaryClosure (subfunctions (F.eval I) Y)) ≤ max 8 (16 ^ F.leafSizeIn Y) := by
  by_cases h0 : F.leafSizeIn Y = 0
  · have := card_unaryClosure_le_two (S := subfunctions (F.eval I) Y) fun g hg =>
      isConst_of_mem_subfunctions h0 hg
    exact (show 4 * _ ≤ 8 by omega).trans (le_max_left _ _)
  induction F with
  | input i =>
    have hi : i ∈ Y := by simpa using h0
    have : subfunctions ((Formula.input i).eval I) Y = {fun x => x i} := by
      ext g
      simp only [mem_subfunctions, Formula.eval_input, mem_singleton]
      exact ⟨fun ⟨z, hz⟩ => hz ▸ funext fun x => by simp [hi],
        fun hg => ⟨fun _ => false, hg ▸ funext fun x => by simp [hi]⟩⟩
    have h := card_unaryClosure_le (subfunctions ((Formula.input i).eval I) Y)
    rw [this, card_singleton] at h
    rw [this]
    refine le_max_of_le_right ?_
    simp only [Formula.leafSizeIn_input, hi, ↓reduceIte, pow_one]
    omega
  | gate op args ih =>
    refine four_mul_card_le_of_gate (harity op) (I op) (fun x => rfl) rfl h0 fun j => ?_
    by_cases hj : (args j).leafSizeIn Y = 0
    · have := card_unaryClosure_le_two (S := subfunctions ((args j).eval I) Y) fun g hg =>
        isConst_of_mem_subfunctions hj hg
      exact (show 4 * _ ≤ 8 by omega).trans (le_max_left _ _)
    · exact ih j hj

/-- **Nechiporuk's lemma**, refined constant: a formula over a basis of fan-in at most two with
`l ≥ 1` leaves labelled by bits of `Y` has at most `16 ^ l / 4` subfunctions on `Y`. -/
theorem four_mul_card_subfunctions_le (harity : ∀ op, σ.Arity op ≤ 2) (I : Interpretation σ Bool)
    (F : Formula σ n) {Y : Finset (Fin n)} (hl : F.leafSizeIn Y ≠ 0) :
    4 * #(subfunctions (F.eval I) Y) ≤ 16 ^ F.leafSizeIn Y := by
  have h := four_mul_card_unaryClosure_le (I := I) harity F Y
  rw [max_eq_right ((Nat.pow_le_pow_right (by decide) (Nat.one_le_iff_ne_zero.2 hl)).trans'
    (by decide))] at h
  exact (Nat.mul_le_mul_left 4 (card_le_card (subset_unaryClosure _))).trans h

/-- **Nechiporuk's lemma.** A formula over a basis of fan-in at most two with `l` leaves labelled by
bits of `Y` has at most `2 · 16 ^ l` subfunctions on `Y`. -/
theorem card_subfunctions_le (harity : ∀ op, σ.Arity op ≤ 2) (I : Interpretation σ Bool)
    (F : Formula σ n) (Y : Finset (Fin n)) :
    #(subfunctions (F.eval I) Y) ≤ 2 * 16 ^ F.leafSizeIn Y := by
  have h := four_mul_card_unaryClosure_le (I := I) harity F Y
  have hsub := card_le_card (subset_unaryClosure (subfunctions (F.eval I) Y))
  have hpow : 1 ≤ 16 ^ F.leafSizeIn Y := Nat.one_le_pow _ _ (by decide)
  have : max 8 (16 ^ F.leafSizeIn Y) ≤ 8 * 16 ^ F.leafSizeIn Y := max_le (by omega) (by omega)
  omega

private theorem two_mul_sixteen_pow (l : ℕ) : 2 * 16 ^ l = 2 ^ (4 * l + 1) := by
  rw [pow_succ, pow_mul, mul_comm]
  norm_num

/-- **Nechiporuk's bound.** If a formula of leaf size `L` over a basis of fan-in at most two
computes `f`, then for disjoint blocks `Y i` of bits, `i ∈ s`, the numbers of subfunctions of `f`
on the blocks have product at most `2 ^ (4 L + |s|)`. -/
theorem prod_card_subfunctions_le (harity : ∀ op, σ.Arity op ≤ 2) {f : BooleanFunction n}
    {F : Formula σ n} (hF : F.Computes I f) {ι : Type*} {s : Finset ι} {Y : ι → Finset (Fin n)}
    (hY : (s : Set ι).PairwiseDisjoint Y) :
    ∏ i ∈ s, #(subfunctions f (Y i)) ≤ 2 ^ (4 * F.leafSize + #s) := by
  rw [← Formula.computes_iff.1 hF]
  calc ∏ i ∈ s, #(subfunctions (F.eval I) (Y i))
      ≤ ∏ i ∈ s, 2 ^ (4 * F.leafSizeIn (Y i) + 1) :=
        prod_le_prod fun i _ =>
          (card_subfunctions_le harity I F (Y i)).trans_eq (two_mul_sixteen_pow _)
    _ = 2 ^ (4 * ∑ i ∈ s, F.leafSizeIn (Y i) + #s) := by
        rw [prod_pow_eq_pow_sum, sum_add_distrib, ← mul_sum, sum_const, smul_eq_mul, mul_one]
    _ ≤ 2 ^ (4 * F.leafSize + #s) := Nat.pow_le_pow_right (by decide) (by
        have := F.sum_leafSizeIn_le_leafSize hY
        omega)

/-- **Nechiporuk's bound**, logarithmic form: the binary logarithms, rounded up, of the numbers of
subfunctions on disjoint blocks add up to at most `4 L + |s|`. -/
theorem sum_clog_card_subfunctions_le (harity : ∀ op, σ.Arity op ≤ 2) {f : BooleanFunction n}
    {F : Formula σ n} (hF : F.Computes I f) {ι : Type*} {s : Finset ι} {Y : ι → Finset (Fin n)}
    (hY : (s : Set ι).PairwiseDisjoint Y) :
    ∑ i ∈ s, Nat.clog 2 #(subfunctions f (Y i)) ≤ 4 * F.leafSize + #s := by
  rw [← Formula.computes_iff.1 hF]
  calc ∑ i ∈ s, Nat.clog 2 #(subfunctions (F.eval I) (Y i))
      ≤ ∑ i ∈ s, (4 * F.leafSizeIn (Y i) + 1) := sum_le_sum fun i _ => Nat.clog_le_of_le_pow
        ((card_subfunctions_le harity I F (Y i)).trans_eq (two_mul_sixteen_pow _))
    _ = 4 * ∑ i ∈ s, F.leafSizeIn (Y i) + #s := by
        rw [sum_add_distrib, ← mul_sum, sum_const, smul_eq_mul, mul_one]
    _ ≤ 4 * F.leafSize + #s := by
        have := F.sum_leafSizeIn_le_leafSize hY
        omega

end Cslib.Circuits.Boolean
