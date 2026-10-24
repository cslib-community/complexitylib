/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Data.Nat.Bitwise.Sparse
public import Mathlib.Data.Fintype.Prod
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Collision-free shifts for fusion-tree multiplication

The multiplier in a fusion node moves its significant bits into a short interval.
Choosing the shifts must separate every cross term of the multiplication, not just
the diagonal terms which are retained. This module proves that such shifts exist.
Preprocessing is mathematical; no preprocessing-time or RAM-execution bound is asserted here.

## Main definitions

* `spreadShift`: a bounded residue shifted by a multiple of the collision modulus.

## Main results

* `exists_residue_shifts`: shifts below `r³` separating translates modulo `r³`.
* `exists_spread_shifts`: collision-free cross terms and ordered diagonal terms in a
  span of at most `2r⁴` bits.

## References

* [M. L. Fredman and D. E. Willard, *Surpassing the information theoretic bound
  with fusion trees*][FredmanWillard1993].
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.FusionTree

open scoped BigOperators

private theorem exists_residue_shifts_aux {r : ℕ} (hr : 0 < r)
    (b : Fin r → ZMod (r ^ 3)) :
    ∀ t, t ≤ r → ∃ m : Fin t → ZMod (r ^ 3),
      ∀ i j, i ≠ j → ∀ k l, b k + m i ≠ b l + m j := by
  let : NeZero (r ^ 3) := ⟨by positivity⟩
  intro t
  induction t with
  | zero => exact fun _ => ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  | succ t ih =>
    intro ht
    obtain ⟨m, hm⟩ := ih (by omega)
    let forbidden : Finset (ZMod (r ^ 3)) :=
      Finset.univ.image (fun p : Fin t × Fin r × Fin r => b p.2.1 + m p.1 - b p.2.2)
    have hc : forbidden.card < (Finset.univ : Finset (ZMod (r ^ 3))).card := by
      calc
        forbidden.card ≤ Fintype.card (Fin t × Fin r × Fin r) := Finset.card_image_le
        _ = t * (r * r) := by simp
        _ < r * (r * r) := Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
        _ = (Finset.univ : Finset (ZMod (r ^ 3))).card := by simp [pow_succ, Nat.mul_assoc]
    obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
    have ha' (i : Fin t) (k l : Fin r) : a ≠ b k + m i - b l := by
      intro he
      apply ha
      exact Finset.mem_image.mpr ⟨(i, k, l), Finset.mem_univ _, he.symm⟩
    refine ⟨Fin.snoc m a, ?_⟩
    refine Fin.lastCases ?_ (fun i => ?_)
    · refine Fin.lastCases ?_ (fun j => ?_)
      · intro hij
        exact (hij rfl).elim
      · intro _ k l
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        intro he
        apply ha' j l k
        rw [eq_sub_iff_add_eq]
        simpa only [add_comm] using he
    · refine Fin.lastCases ?_ (fun j => ?_)
      · intro _ k l
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        intro he
        apply ha' i k l
        rw [eq_sub_iff_add_eq]
        simpa only [add_comm] using he.symm
      · intro hij k l
        simp only [Fin.snoc_castSucc]
        exact hm i j (fun he => hij (congrArg Fin.castSucc he)) k l

/-- Choose `r` translates separated modulo `r³`. Positions may have equal residues:
only translates with different shift indices are required to be disjoint. -/
theorem exists_residue_shifts {r : ℕ} (hr : 0 < r) (b : Fin r → ℕ) :
    ∃ m : Fin r → ℕ, (∀ i, m i < r ^ 3) ∧
      ∀ i j, i ≠ j → ∀ k l,
        (b k + m i) % r ^ 3 ≠ (b l + m j) % r ^ 3 := by
  let : NeZero (r ^ 3) := ⟨by positivity⟩
  obtain ⟨m, hm⟩ := exists_residue_shifts_aux hr (fun i => (b i : ZMod (r ^ 3))) r le_rfl
  refine ⟨fun i => (m i).val, fun i => ZMod.val_lt _, ?_⟩
  intro i j hij k l he
  apply hm i j hij k l
  have hc := (ZMod.natCast_eq_natCast_iff' _ _ (r ^ 3)).mpr he
  simpa only [Nat.cast_add, ZMod.natCast_zmod_val] using hc

/-- Lift a residue by a multiple of `M`. Two modulus-sized slots per diagonal term
leave room for both the input position's residue and the chosen shift's residue. -/
def spreadShift (w M b i m : ℕ) : ℕ :=
  m + ((w - b) / M + 2 * i + 1) * M

/-- Adding a multiple of the collision modulus preserves a chosen shift's residue. -/
private theorem spreadShift_mod (w M b i m : ℕ) : spreadShift w M b i m % M = m % M := by
  simp [spreadShift]

/-- The `i`th diagonal term lies strictly between the endpoints of its two-slot interval. -/
private theorem spreadShift_bounds {w M b i m : ℕ} (hM : 0 < M) (hb : b ≤ w) (hm : m < M) :
    w + 2 * i * M < b + spreadShift w M b i m ∧
      b + spreadShift w M b i m < w + (2 * i + 2) * M := by
  have hdiv := Nat.div_add_mod (w - b) M
  have hmod := Nat.mod_lt (w - b) hM
  rw [Nat.mul_comm M] at hdiv
  simp only [spreadShift, Nat.add_mul, Nat.one_mul, Nat.mul_assoc] at *
  omega

/-- For distinct significant positions below `w`, all cross terms of the mask multiplication
are distinct, diagonal terms preserve their order, and every diagonal lies in an interval
of length `2r⁴`. This is an existence theorem for preprocessing, with no RAM-time claim. -/
theorem exists_spread_shifts {r w : ℕ} (hr : 0 < r) (b : Fin r → ℕ)
    (hb : Function.Injective b) (hw : ∀ i, b i ≤ w) :
    ∃ m : Fin r → ℕ,
      Function.Injective (fun p : Fin r × Fin r => b p.1 + m p.2) ∧
      StrictMono (fun i => b i + m i) ∧
      (∀ i, w < b i + m i ∧ b i + m i < w + 2 * r ^ 4) := by
  obtain ⟨a, ha, hsep⟩ := exists_residue_shifts hr b
  let m (i : Fin r) := spreadShift w (r ^ 3) (b i) i.val (a i)
  have hm (i : Fin r) :
      w + 2 * i.val * r ^ 3 < b i + m i ∧
        b i + m i < w + (2 * i.val + 2) * r ^ 3 :=
    spreadShift_bounds (by positivity) (hw i) (ha i)
  refine ⟨m, ?_, ?_, ?_⟩
  · intro p q hpq
    change b p.1 + m p.2 = b q.1 + m q.2 at hpq
    have hj : p.2 = q.2 := by
      by_contra hne
      apply hsep p.2 q.2 hne p.1 q.1
      have he := congrArg (fun n => n % r ^ 3) hpq
      rw [Nat.add_mod (b p.1) (m p.2), Nat.add_mod (b q.1) (m q.2)] at he
      dsimp only [m] at he
      rw [spreadShift_mod, spreadShift_mod] at he
      simpa only [← Nat.add_mod] using he
    rw [hj] at hpq
    have hi : p.1 = q.1 := hb (Nat.add_right_cancel hpq)
    exact Prod.ext hi hj
  · intro i j hij
    have hs : (2 * i.val + 2) * r ^ 3 ≤ 2 * j.val * r ^ 3 :=
      Nat.mul_le_mul_right _ (by omega)
    exact (hm i).2.trans_le ((Nat.add_le_add_left hs w).trans (hm j).1.le)
  · intro i
    have hs : (2 * i.val + 2) * r ^ 3 ≤ 2 * r ^ 4 := by
      calc
        (2 * i.val + 2) * r ^ 3 ≤ (2 * r) * r ^ 3 :=
          Nat.mul_le_mul_right _ (by omega)
        _ = 2 * r ^ 4 := by ring
    exact ⟨lt_of_le_of_lt (by omega) (hm i).1,
      (hm i).2.trans_le (Nat.add_le_add_left hs w)⟩

/-- A bit mask with precisely the supplied positions set, when they are distinct. -/
def positionMask {r : ℕ} (b : Fin r → ℕ) : ℕ := ∑ i, 2 ^ b i

/-- The set bits of a position mask are exactly its supplied positions. -/
theorem positionMask_testBit {r : ℕ} (b : Fin r → ℕ) (hb : Function.Injective b) (k : ℕ) :
    (positionMask b).testBit k = true ↔ ∃ i, b i = k := by
  simpa only [Bool.toNat_true, one_mul, Finset.mem_univ, true_and, positionMask] using
    Nat.testBit_sum_injective Finset.univ b
      (fun _ _ _ _ he => hb he) (fun _ => true) k

/-- A position mask fits in any width above all its distinct positions. -/
theorem positionMask_lt {r L : ℕ} (b : Fin r → ℕ) (hb : Function.Injective b)
    (hL : ∀ i, b i < L) : positionMask b < 2 ^ L := by
  simpa only [Bool.toNat_true, one_mul, positionMask] using
    Nat.sum_injective_lt_two_pow Finset.univ b
      (fun _ _ _ _ he => hb he) (fun _ => true) (fun i _ => hL i)

/-- Expand the masked product into all its binary cross terms. -/
private theorem maskedProduct_eq {r : ℕ} (b m : Fin r → ℕ) (hb : Function.Injective b) (x : ℕ) :
    (x &&& positionMask b) * positionMask m =
      ∑ p : Fin r × Fin r, (x.testBit (b p.1)).toNat * 2 ^ (b p.1 + m p.2) := by
  rw [positionMask, Nat.and_sum_two_pow b hb]
  simp only [positionMask, Fintype.sum_mul_sum, Fintype.sum_prod_type, pow_add, mul_assoc]

/-- No carries occur anywhere in a collision-free product. At every cross-term position,
the original significant bit is recovered exactly. -/
private theorem maskedProduct_testBit {r : ℕ} (b m : Fin r → ℕ)
    (h : Function.Injective (fun p : Fin r × Fin r => b p.1 + m p.2))
    (hb : Function.Injective b) (x : ℕ) (i j : Fin r) :
    ((x &&& positionMask b) * positionMask m).testBit (b i + m j) = x.testBit (b i) := by
  apply Bool.eq_iff_iff.mpr
  rw [maskedProduct_eq b m hb, Nat.testBit_sum_injective _ _
    (fun _ _ _ _ he => h he)]
  constructor
  · rintro ⟨p, _, hp, he⟩
    have he' : p = (i, j) := h he
    simpa only [he'] using hp
  · intro hx
    exact ⟨(i, j), Finset.mem_univ _, hx, rfl⟩

/-- A masked multiplication, right shift, and final mask retaining its diagonal terms.
This expression uses unbounded arithmetic; a RAM implementation must separately account
for the product's potentially multiple words. -/
def approximateSketch {r : ℕ} (w : ℕ) (b m : Fin r → ℕ) (x : ℕ) : ℕ :=
  (((x &&& positionMask b) * positionMask m) >>> w) &&&
    positionMask (fun i => b i + m i - w)

/-- Exact sketch compression, including every zero between the retained bits. The hypotheses
are satisfied by `exists_spread_shifts`; no word-RAM execution is asserted by this identity. -/
theorem approximateSketch_eq {r w : ℕ} (b m : Fin r → ℕ)
    (h : Function.Injective (fun p : Fin r × Fin r => b p.1 + m p.2))
    (hb : Function.Injective b) (hw : ∀ i, w ≤ b i + m i) (x : ℕ) :
    approximateSketch w b m x =
      ∑ i, (x.testBit (b i)).toNat * 2 ^ (b i + m i - w) := by
  have hf : Function.Injective (fun i => b i + m i - w) := by
    intro i j he
    change b i + m i - w = b j + m j - w at he
    have hd : b i + m i = b j + m j := by have := hw i; have := hw j; omega
    exact congrArg Prod.fst (h (show b (i, i).1 + m (i, i).2 =
      b (j, j).1 + m (j, j).2 from hd))
  apply Nat.eq_of_testBit_eq
  intro k
  apply Bool.eq_iff_iff.mpr
  rw [approximateSketch, Nat.testBit_land, Bool.and_eq_true,
    positionMask_testBit _ hf, Nat.testBit_sum_injective _ _
      (fun _ _ _ _ he => hf he)]
  constructor
  · rintro ⟨hp, i, hi⟩
    refine ⟨i, Finset.mem_univ _, ?_, hi⟩
    have he : w + k = b i + m i := by have := hw i; omega
    simpa only [Nat.testBit_shiftRight, he, maskedProduct_testBit b m h hb] using hp
  · rintro ⟨i, _, hx, hi⟩
    refine ⟨?_, i, hi⟩
    have he : w + k = b i + m i := by have := hw i; omega
    simpa only [Nat.testBit_shiftRight, he, maskedProduct_testBit b m h hb] using hx

end Cslib.Algorithms.Lean.FusionTree
