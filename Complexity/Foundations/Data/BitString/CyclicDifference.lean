/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Parity
public import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic.Abel

/-!
# Cyclic differences of Boolean tuples

The cyclic difference records the exclusive or of each coordinate and its successor, including
the last-to-first edge. This is the tuple operation in [KazdaKolmogorovRolinek2018], Definition 14
(arXiv v6, printed p. 0:6). Coordinates remain ordered; no symmetry of a relation is assumed.
The empty tuple is included, and every cyclic difference has even parity.

## Main definitions

* `Cslib.BitString.cyclicDifference`: neighboring exclusive ors around the coordinate cycle.
* `Cslib.BitString.cyclicIntegral`: prefix-sum inverse on even-parity tuples.
* `Cslib.BitString.IsSelfComplementary`, `Cslib.BitString.cyclicDifferenceRelation`: relational API.

## Main results

* `Cslib.BitString.cyclicDifference_not`: complementing a tuple preserves its differences.
* `Cslib.BitString.cyclicDifference_add`: cyclic differences are linear over the Boolean ring.
* `Cslib.BitString.parityOn_cyclicDifference`: every cyclic difference has even parity.
* `Cslib.BitString.cyclicDifference_eq_iff`: fibers consist of a tuple and its complement.
* `Cslib.BitString.exists_cyclicDifference_eq_iff`: image is exactly the even-parity tuples.
* `Cslib.BitString.mem_cyclicDifferenceRelation_iff`: recover a self-complementary relation.
-/

public section

namespace Cslib.BitString

/-- Exclusive ors of neighboring coordinates, with cyclic last-to-first adjacency. -/
@[expose] def cyclicDifference {n : ℕ} (x : Fin n → Bool) : Fin n → Bool :=
  fun i => x i ^^ x (finRotate n i)

/-- Cyclic differences are the sum of a tuple and its one-step cyclic shift. -/
theorem cyclicDifference_eq_add {n : ℕ} (x : Fin n → Bool) :
    cyclicDifference x = x + fun i => x (finRotate n i) := by
  funext i
  simp only [cyclicDifference, Pi.add_apply, Bool.add_eq_xor]

/-- Constant tuples have zero cyclic difference, including at arity zero. -/
theorem cyclicDifference_const (n : ℕ) (b : Bool) :
    cyclicDifference (fun _ : Fin n => b) = fun _ => false := by
  funext i
  cases b <;> rfl

/-- Complementary tuples have identical cyclic differences. -/
theorem cyclicDifference_not {n : ℕ} (x : Fin n → Bool) :
    cyclicDifference (fun i => !x i) = cyclicDifference x := by
  funext i
  change (!x i ^^ !x (finRotate n i)) = (x i ^^ x (finRotate n i))
  cases x i <;> cases x (finRotate n i) <;> rfl

/-- Taking cyclic differences is linear over the Boolean ring. -/
theorem cyclicDifference_add {n : ℕ} (x y : Fin n → Bool) :
    cyclicDifference (x + y) = cyclicDifference x + cyclicDifference y := by
  funext i
  simp only [cyclicDifference, Pi.add_apply, ← Bool.add_eq_xor]
  abel

/-- A cyclic difference has an even number of true coordinates. -/
theorem parityOn_cyclicDifference {n : ℕ} (x : Fin n → Bool) :
    parityOn Finset.univ (cyclicDifference x) = false := by
  have hrotate : parityOn Finset.univ (fun i => x (finRotate n i)) =
      parityOn Finset.univ x := by
    simp only [parityOn_eq_sum]
    exact (finRotate n).sum_comp _ _ (by intro i _; exact Finset.mem_univ i)
  rw [cyclicDifference_eq_add, parityOn_add, hrotate]
  simp

/-- Zero differences force a tuple to be constant. The empty tuple is included. -/
theorem cyclicDifference_eq_zero_iff {n : ℕ} (x : Fin n → Bool) :
    cyclicDifference x = (fun _ => false) ↔ ∃ b, x = fun _ => b := by
  constructor
  · intro h
    cases n with
    | zero => exact ⟨false, funext fun i => i.elim0⟩
    | succ n =>
      refine ⟨x 0, funext ?_⟩
      intro i
      induction i using Fin.induction with
      | zero => rfl
      | succ i ih =>
        have hi : finRotate (n + 1) i.castSucc = i.succ := finRotate_of_lt i.isLt
        have hb := congrFun h i.castSucc
        change (x i.castSucc ^^ x (finRotate (n + 1) i.castSucc)) = false at hb
        rw [hi] at hb
        have he : x i.succ = x i.castSucc := by
          cases ha : x i.castSucc <;> cases hc : x i.succ <;> simp_all
        exact he.trans ih
  · rintro ⟨b, rfl⟩
    exact cyclicDifference_const n b

/-- The only ambiguity in recovering a tuple from its cyclic differences is complementation. -/
theorem cyclicDifference_eq_iff {n : ℕ} (x y : Fin n → Bool) :
    cyclicDifference x = cyclicDifference y ↔ x = y ∨ x = fun i => !y i := by
  constructor
  · intro h
    have hz : cyclicDifference (x + y) = fun _ => false := by
      rw [cyclicDifference_add, h]
      funext i
      simp only [Pi.add_apply, Bool.add_eq_xor, Bool.xor_self]
    obtain ⟨b, hb⟩ := (cyclicDifference_eq_zero_iff (x + y)).mp hz
    cases b
    · left
      funext i
      have hi := congrFun hb i
      change (x i ^^ y i) = false at hi
      cases hx : x i <;> cases hy : y i <;> simp_all
    · right
      funext i
      have hi := congrFun hb i
      change (x i ^^ y i) = true at hi
      cases hx : x i <;> cases hy : y i <;> simp_all
  · rintro (rfl | rfl)
    · rfl
    · exact cyclicDifference_not y

/-- Recover a tuple with initial value zero by summing preceding cyclic differences. -/
@[expose] def cyclicIntegral {n : ℕ} (d : Fin n → Bool) : Fin n → Bool :=
  fun i => parityOn (Finset.univ.filter fun j => j.val < i.val) d

/-- The prefix sum changes by the bit at the newly included coordinate. -/
theorem cyclicIntegral_succ {n : ℕ} (d : Fin (n + 1) → Bool) (i : Fin n) :
    cyclicIntegral d i.succ = (d i.castSucc ^^ cyclicIntegral d i.castSucc) := by
  have hs : (Finset.univ.filter fun j : Fin (n + 1) => j.val < i.succ.val) =
      insert i.castSucc (Finset.univ.filter fun j => j.val < i.castSucc.val) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.ext_iff, Fin.val_succ, Fin.val_castSucc]
    omega
  unfold cyclicIntegral
  rw [hs, parityOn_insert (by simp)]

/-- The prefix sum starts at zero. -/
@[simp] theorem cyclicIntegral_zero {n : ℕ} (d : Fin (n + 1) → Bool) :
    cyclicIntegral d 0 = false := by
  simp [cyclicIntegral]

/-- Every even-parity tuple is the cyclic difference of its prefix-sum tuple. -/
theorem cyclicDifference_cyclicIntegral {n : ℕ} (d : Fin n → Bool)
    (hd : parityOn Finset.univ d = false) : cyclicDifference (cyclicIntegral d) = d := by
  cases n with
  | zero => exact funext fun i => i.elim0
  | succ n =>
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have hs : insert (Fin.last n)
          (Finset.univ.filter fun j : Fin (n + 1) => j.val < (Fin.last n).val) =
          Finset.univ := by
        ext j
        simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and,
          Fin.ext_iff, Fin.val_last, iff_true]
        have := j.isLt
        omega
      have hp := parityOn_insert (s := Finset.univ.filter fun j : Fin (n + 1) =>
        j.val < (Fin.last n).val) (i := Fin.last n) (by simp) d
      rw [hs, hd] at hp
      change (cyclicIntegral d (Fin.last n) ^^
        cyclicIntegral d (finRotate (n + 1) (Fin.last n))) = d (Fin.last n)
      rw [finRotate_last, cyclicIntegral_zero, Bool.xor_false]
      change false = (d (Fin.last n) ^^ cyclicIntegral d (Fin.last n)) at hp
      exact Bool.xor_right_inj.mp (hp.symm.trans (Bool.xor_self _).symm)
    · change (cyclicIntegral d j.castSucc ^^
        cyclicIntegral d (finRotate (n + 1) j.castSucc)) = d j.castSucc
      have hj : finRotate (n + 1) j.castSucc = j.succ := finRotate_of_lt j.isLt
      rw [hj, cyclicIntegral_succ]
      cases cyclicIntegral d j.castSucc <;> cases d j.castSucc <;> rfl

/-- The image of cyclic difference is exactly the even-parity tuples, including arity zero. -/
theorem exists_cyclicDifference_eq_iff {n : ℕ} (d : Fin n → Bool) :
    (∃ x, cyclicDifference x = d) ↔ parityOn Finset.univ d = false := by
  constructor
  · rintro ⟨x, rfl⟩
    exact parityOn_cyclicDifference x
  · intro hd
    exact ⟨cyclicIntegral d, cyclicDifference_cyclicIntegral d hd⟩

/-- Invariance of a Boolean relation under simultaneous complementation of all coordinates.
This is Definition 13 of [KazdaKolmogorovRolinek2018], with empty relations allowed. -/
@[expose] def IsSelfComplementary {ι : Type*} (R : Set (ι → Bool)) : Prop :=
  ∀ x, x ∈ R ↔ (fun i => !x i) ∈ R

/-- The relation of cyclic differences, retaining the original coordinate order. -/
@[expose] def cyclicDifferenceRelation {n : ℕ} (R : Set (Fin n → Bool)) :
    Set (Fin n → Bool) := cyclicDifference '' R

/-- Cyclic differences preserve nonemptiness of relations. -/
theorem cyclicDifferenceRelation_nonempty_iff {n : ℕ} (R : Set (Fin n → Bool)) :
    (cyclicDifferenceRelation R).Nonempty ↔ R.Nonempty :=
  Set.image_nonempty

/-- Every tuple of a cyclic-difference relation has even parity. -/
theorem parityOn_mem_cyclicDifferenceRelation {n : ℕ} {R : Set (Fin n → Bool)}
    {d : Fin n → Bool} (hd : d ∈ cyclicDifferenceRelation R) :
    parityOn Finset.univ d = false := by
  obtain ⟨x, _, rfl⟩ := hd
  exact parityOn_cyclicDifference x

/-- A self-complementary relation is recovered exactly from its cyclic differences. -/
theorem mem_cyclicDifferenceRelation_iff {n : ℕ} {R : Set (Fin n → Bool)}
    (hR : IsSelfComplementary R) (x : Fin n → Bool) :
    cyclicDifference x ∈ cyclicDifferenceRelation R ↔ x ∈ R := by
  constructor
  · rintro ⟨y, hy, he⟩
    rcases (cyclicDifference_eq_iff y x).mp he with rfl | rfl
    · exact hy
    · exact (hR x).mpr hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The preimage of any difference relation is self-complementary. -/
theorem isSelfComplementary_preimage_cyclicDifference {n : ℕ}
    (S : Set (Fin n → Bool)) : IsSelfComplementary (cyclicDifference ⁻¹' S) := by
  intro x
  change cyclicDifference x ∈ S ↔ cyclicDifference (fun i => !x i) ∈ S
  rw [cyclicDifference_not]

end Cslib.BitString
