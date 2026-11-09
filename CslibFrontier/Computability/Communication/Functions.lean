/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.FoolingSet
public import CslibFrontier.Foundations.Data.BitString.Basic
public import Mathlib.Data.Matrix.Mul
import CslibFrontier.Foundations.BooleanAnalysis.HadamardRectangles
import CslibFrontier.Foundations.Data.Code.Hadamard
import Mathlib.Tactic.Linarith

/-!
# Equality, greater-than, inner product and disjointness

Every Boolean function of Alice's `n` bits and Bob's input has a protocol with `n + 1` bits: Alice
sends her input and Bob announces the value (`Protocol.ecomplexityFun_le_succ`). Four classical
functions of two `n`-bit strings need all `n + 1` bits for `0 < n`
[Kushilevitz and Nisan, Chapter 1][KushilevitzNisan1997]:

* *equality* `x = y` (`equality`, `ecomplexity_equality`);
* *greater-than* `y < x`, reading bit strings as binary numerals (`greaterThan`,
  `ecomplexity_greaterThan`);
* the *inner product* `x ⬝ᵥ y` modulo two, the Hadamard code `BitString.hadamardCode`
  (`ecomplexity_dotProduct`);
* *disjointness* of the sets of positions where `x` and `y` are `true` (`disjointness`,
  `ecomplexity_disjointness`).

Equality, greater-than and disjointness have fooling sets of `2 ^ n` pairs: the diagonal pairs
`(x, x)` for equality and greater-than (`isFoolingSet_equality`, `isFoolingSet_greaterThan`) and
the complementary pairs `(x, !x)` for disjointness (`isFoolingSet_disjointness`). For the inner
product, a rectangle on which it is constant has at most `2 ^ n` entries
(`BitString.card_mul_le_two_pow_of_dotProduct_eq`, from Lindsey's lemma), while it is `false` on
`2 ^ (n - 1) (2 ^ n + 1)` pairs and `true` on `2 ^ (n - 1) (2 ^ n - 1)` pairs; the area bound then
forces more than `2 ^ n` leaves (`two_pow_lt_leafCount_of_run_eq_dotProduct`).

## Main definitions

* `Cslib.Communication.equality`, `Cslib.Communication.greaterThan`,
  `Cslib.Communication.disjointness`: equality, greater-than and disjointness.

## Main results

* `Cslib.Communication.ecomplexity_equality`, `Cslib.Communication.ecomplexity_greaterThan`,
  `Cslib.Communication.ecomplexity_dotProduct`, `Cslib.Communication.ecomplexity_disjointness`:
  equality, greater-than, inner product and disjointness of `n` bits need `n + 1` bits.

## References

* [E. Kushilevitz and N. Nisan, *Communication Complexity*][KushilevitzNisan1997]
-/

@[expose] public section

namespace Cslib.Communication

open Finset

variable {X Y Z : Type*} {n : ℕ}

/-! ### Equality and greater-than -/

/-- Equality: `equality x y` is `true` exactly when `x = y`. -/
def equality [DecidableEq X] (x y : X) : Bool :=
  decide (x = y)

/-- Greater-than: `greaterThan x y` is `true` exactly when `y < x`. -/
def greaterThan [LinearOrder X] (x y : X) : Bool :=
  decide (y < x)

/-- The diagonal pairs form a fooling set for equality with value `true`. -/
theorem isFoolingSet_equality [DecidableEq X] (s : Finset X) :
    IsFoolingSet equality true (s.image fun x => (x, x)) := by
  simp only [IsFoolingSet, mem_image]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    simp [equality]
  · rintro _ ⟨x, -, rfl⟩ _ ⟨x', -, rfl⟩ h -
    simpa [equality] using h

/-- For an injective map `e` into a linear order, the diagonal pairs form a fooling set for
greater-than after `e`, with value `false`. -/
theorem isFoolingSet_greaterThan {L : Type*} [LinearOrder L] [DecidableEq X] {e : X → L}
    (he : Function.Injective e) (s : Finset X) :
    IsFoolingSet (fun x y => greaterThan (e x) (e y)) false (s.image fun x => (x, x)) := by
  simp only [IsFoolingSet, mem_image]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    simp [greaterThan]
  · rintro _ ⟨x, -, rfl⟩ _ ⟨x', -, rfl⟩ h h'
    simp only [greaterThan, decide_eq_false_iff_not, not_lt] at h h'
    rw [he (le_antisymm h' h)]

/-- In a partial order, the diagonal pairs form a fooling set for `≤` with value `true`, by
antisymmetry. -/
theorem isFoolingSet_le [PartialOrder X] [DecidableLE X] [DecidableEq X] (s : Finset X) :
    IsFoolingSet (fun x y => decide (x ≤ y)) true (s.image fun x => (x, x)) := by
  simp only [IsFoolingSet, mem_image]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    simp
  · rintro _ ⟨x, -, rfl⟩ _ ⟨x', -, rfl⟩ h h'
    simp only [decide_eq_true_eq] at h h'
    rw [le_antisymm h h']

/-- **Equality on a finite set needs more than `log₂` of its size bits**: a protocol computing
equality on a set of at least two elements sends `d` bits with `|X| < 2 ^ d`. The exact cost,
`⌈log₂ |X|⌉ + 1`, is `ecomplexityFun_equality`. -/
theorem card_lt_two_pow_of_run_eq_equality [Fintype X] [DecidableEq X] (hX : 1 < Fintype.card X)
    {p : Protocol X X Bool} (hp : p.run = equality) : Fintype.card X < 2 ^ p.depth := by
  obtain ⟨x, y, hxy⟩ := Fintype.one_lt_card_iff.mp hX
  have h := (isFoolingSet_equality univ).card_lt_two_pow hp ⟨x, y, by simpa [equality] using hxy⟩
  rwa [card_image_of_injective _ fun x y h => congrArg Prod.fst h, card_univ] at h

/-- **Greater-than on a finite linear order needs more than `log₂` of its size bits**: a protocol
computing greater-than on a linear order of at least two elements sends `d` bits with
`|X| < 2 ^ d`. -/
private theorem card_lt_two_pow_of_run_eq_greaterThan [Fintype X] [LinearOrder X]
    (hX : 1 < Fintype.card X) {p : Protocol X X Bool} (hp : p.run = greaterThan) :
    Fintype.card X < 2 ^ p.depth := by
  obtain ⟨x, y, hxy⟩ := Fintype.one_lt_card_iff.mp hX
  have hz : ∃ x y : X, greaterThan x y ≠ false := by
    rcases hxy.lt_or_gt with h | h
    · exact ⟨y, x, by simpa [greaterThan] using h⟩
    · exact ⟨x, y, by simpa [greaterThan] using h⟩
  have h := (isFoolingSet_greaterThan Function.injective_id univ).card_lt_two_pow hp hz
  rwa [card_image_of_injective _ fun x y h => congrArg Prod.fst h, card_univ] at h

/-- **Equality of `n` bits needs `n + 1` bits**, for `0 < n`. This is the case of bit strings of
`ecomplexityFun_equality`, the exact cost of equality on any finite set. -/
theorem ecomplexity_equality (hn : 0 < n) :
    Protocol.ecomplexity (fun (x y : BitString n) b => equality x y = b) Set.univ Set.univ =
      n + 1 := by
  refine le_antisymm (Protocol.ecomplexityFun_le_succ _)
    ((isFoolingSet_equality univ).succ_le_ecomplexity ⟨fun _ => false, fun _ => true, ?_⟩ ?_)
  · simpa [equality] using fun h => Bool.false_ne_true (congrFun h ⟨0, hn⟩)
  · rw [card_image_of_injective _ fun x y h => congrArg Prod.fst h, card_univ, BitString.card]

/-- **Greater-than of `n`-bit numbers needs `n + 1` bits**, for `0 < n`: reading bit strings as
binary numerals (`BitString.equivFin`), deciding whether Alice's number exceeds Bob's needs
`n + 1` bits. -/
theorem ecomplexity_greaterThan (hn : 0 < n) :
    Protocol.ecomplexity (fun (x y : BitString n) b =>
        greaterThan (BitString.equivFin n x) (BitString.equivFin n y) = b) Set.univ Set.univ =
      n + 1 := by
  refine le_antisymm (Protocol.ecomplexityFun_le_succ _)
    ((isFoolingSet_greaterThan (BitString.equivFin n).injective univ).succ_le_ecomplexity
      ⟨(BitString.equivFin n).symm ⟨1, ?_⟩, (BitString.equivFin n).symm ⟨0, ?_⟩, ?_⟩ ?_)
  · exact Nat.one_lt_two_pow hn.ne'
  · exact Nat.two_pow_pos n
  · simp [greaterThan, Fin.lt_def]
  · rw [card_image_of_injective _ fun x y h => congrArg Prod.fst h, card_univ, BitString.card]

/-! ### Disjointness -/

variable {ι : Type*} [Fintype ι]

/-- Disjointness: `disjointness x y` is `true` exactly when no position is `true` in both `x` and
`y`, that is, when the sets of positions where `x` and `y` are `true` are disjoint. -/
def disjointness (x y : ι → Bool) : Bool :=
  decide (∀ i, (x i && y i) = false)

/-- The pairs `(x, !x)` form a fooling set for disjointness with value `true`. -/
theorem isFoolingSet_disjointness (s : Finset (ι → Bool)) :
    IsFoolingSet disjointness true (s.image fun x => (x, fun i => !x i)) := by
  simp only [IsFoolingSet, mem_image]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    simp [disjointness]
  · rintro _ ⟨x, -, rfl⟩ _ ⟨x', -, rfl⟩ h h'
    simp only [disjointness, decide_eq_true_eq] at h h'
    have hxx : x = x' := funext fun i => by
      have h₁ := h i
      have h₂ := h' i
      revert h₁ h₂
      cases x i <;> cases x' i <;> simp
    rw [hxx]

/-- **Disjointness of `n` bits needs `n + 1` bits**, for `0 < n`. -/
theorem ecomplexity_disjointness (hn : 0 < n) :
    Protocol.ecomplexity (fun (x y : BitString n) b => disjointness x y = b) Set.univ Set.univ =
      n + 1 := by
  refine le_antisymm (Protocol.ecomplexityFun_le_succ _)
    ((isFoolingSet_disjointness univ).succ_le_ecomplexity ⟨fun _ => true, fun _ => true, ?_⟩ ?_)
  · intro h
    simp only [disjointness, decide_eq_true_eq] at h
    exact absurd (h ⟨0, hn⟩) (by decide)
  · rw [card_image_of_injective _ fun x y h => congrArg Prod.fst h, card_univ, BitString.card]

/-! ### Inner product -/

/-- **The inner product needs more than `2 ^ k` leaves**: a protocol computing the inner product
modulo two of two `k`-bit strings, for `0 < k`, has more than `2 ^ k` leaves. -/
theorem two_pow_lt_leafCount_of_run_eq_dotProduct [Nonempty ι]
    {p : Protocol (ι → Bool) (ι → Bool) Bool} (hp : p.run = fun x y => x ⬝ᵥ y) :
    2 ^ Fintype.card ι < p.leafCount := by
  classical
  set N := 2 ^ Fintype.card ι with hN
  obtain ⟨M, hM⟩ : ∃ M, N = 2 * M :=
    ⟨2 ^ (Fintype.card ι - 1), by rw [hN, ← pow_succ', Nat.sub_add_cancel Fintype.card_pos]⟩
  have hK (b : Bool) (A B : Finset (ι → Bool)) (h : ∀ x ∈ A, ∀ y ∈ B, x ⬝ᵥ y = b) :
      #A * #B ≤ N :=
    BitString.card_mul_le_two_pow_of_dotProduct_eq A B b h
  have hT := Protocol.card_filter_le_mul hp true (hK true)
  have hF := Protocol.card_filter_le_mul hp false (hK false)
  set T := #{i | p.leafOutput i = true}
  set F := #{i | p.leafOutput i = false}
  have hleaves : T + F = p.leafCount := by
    have := card_filter_add_card_filter_not (s := univ) fun i => p.leafOutput i = true
    simpa [T, F] using this
  have hpairs : #{q : (ι → Bool) × (ι → Bool) | q.1 ⬝ᵥ q.2 = true} +
      #{q : (ι → Bool) × (ι → Bool) | q.1 ⬝ᵥ q.2 = false} = N * N := by
    have := card_filter_add_card_filter_not (s := univ)
      fun q : (ι → Bool) × (ι → Bool) => q.1 ⬝ᵥ q.2 = true
    simpa [Fintype.card_fun, hN] using this
  have hcount := BitString.two_mul_card_dotProduct_eq_true_add_two_pow (ι := ι)
  rw [← hN] at hcount
  have hNpos : 0 < N := Nat.two_pow_pos _
  have hT' : N ≤ 2 * T + 1 := Nat.le_of_mul_le_mul_right (by nlinarith) hNpos
  have hF' : N + 1 ≤ 2 * F := Nat.le_of_mul_le_mul_right (by nlinarith) hNpos
  omega

/-- **The inner product of `n` bits needs `n + 1` bits**, for `0 < n`. -/
theorem ecomplexity_dotProduct (hn : 0 < n) :
    Protocol.ecomplexity (fun (x y : BitString n) b => x ⬝ᵥ y = b) Set.univ Set.univ = n + 1 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine le_antisymm (Protocol.ecomplexityFun_le_succ _)
    (Protocol.le_ecomplexity_iff.mpr fun p hp => ?_)
  have h := (two_pow_lt_leafCount_of_run_eq_dotProduct (Protocol.solves_univ_iff.mp hp)).trans_le
    p.leafCount_le_two_pow_depth
  rw [Fintype.card_fin] at h
  exact_mod_cast (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp h

end Cslib.Communication
