/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Ordered.TupleBit

/-! # Arbitrary-base tuple BIT and its bounded radix arithmetic -/

@[expose] public section

namespace Cslib.Tests.OrderedTupleBit

open FirstOrder Language Structure Cslib.Logic.FO.Ordered

abbrev L : Language := Language.empty

instance {n : ℕ} : L.Structure (Fin n) := Language.emptyStructure
instance : Fact (2 ≤ 2) := ⟨by decide⟩
instance : Fact (2 ≤ 8) := ⟨by decide⟩
instance : Fact (2 ≤ 9) := ⟨by decide⟩
instance : Fact (2 ≤ 64) := ⟨by decide⟩

/-- The valid binary computation `2*3+3=9` needs an intermediate carry equal to the radix. -/
example :
    (Radix.affine L (.var (.inl 0)) (.var (.inl 1))
      (fun i => .var (.inr (0, i))) (fun i => .var (.inr (1, i)))
      (fun i => .var (.inr (2, i)))).Realize
    (Sum.elim (![2, 2] : Fin 2 → Fin 9)
      (fun p : Fin 3 × Fin 4 => (![![1, 1, 0, 0], ![1, 1, 0, 0], ![1, 0, 0, 1] ] p.1) p.2)) := by
  rw [Radix.realize_affine _ _ _ _ _ _ (by change 1 < 2; decide)
    (by change 2 ^ 3 < 9; decide)]
  decide

/-- A three-digit word has no output for `2*4=8`, including noncanonical output digits. -/
example (z : Fin 3 → Fin 9) :
    ¬(Radix.affine L (.var (.inl 0)) (.var (.inl 1))
      (fun i => .var (.inr (0, i))) (fun i => .var (.inr (1, i)))
      (fun i => .var (.inr (2, i)))).Realize
    (Sum.elim (![2, 2] : Fin 2 → Fin 9)
      (fun p : Fin 3 × Fin 3 => (![![0, 0, 1], ![0, 0, 0], z] p.1) p.2)) := by
  rw [Radix.realize_affine _ _ _ _ _ _ (by change 1 < 2; decide)
    (by change 2 ^ 3 < 9; decide)]
  rintro ⟨_, _, _, hz, he⟩
  change ∀ i, (z i).val < 2 at hz
  change 8 = Nat.ofDigits 2 (List.ofFn fun i => (z i).val) at he
  have := Nat.ofDigits_ofFn_lt Nat.one_lt_two (fun i => (z i).val) hz
  lia

/-- Scalar decoder nonzero-quotient rejection, empty-word arithmetic, minimum/small/large universe
`tupleBit` realizations, size-64 seven-digit binary cardinality, and leading-zero conversion. -/
example :
    ¬(Radix.decode L (.var (.inl 0)) (.var (.inl 1))
      (fun i => .var (.inr i))).Realize
      (Sum.elim (![2, 8] : Fin 2 → Fin 9) (![0, 0, 0] : Fin 3 → Fin 9)) ∧
    (Radix.affine L (.var 0) (.var 1) (fun i : Fin 0 => i.elim0)
      (fun i : Fin 0 => i.elim0) (fun i : Fin 0 => i.elim0)).Realize
      (![2, 2] : Fin 2 → Fin 9) ∧
    (tupleBit L 1).Realize
      (fun p : Fin 2 × Fin 1 => (![![1], ![0] ] p.1) p.2 : _ → Fin 2) ∧
    ¬(tupleBit L 1).Realize
      (fun p : Fin 2 × Fin 1 => (![![1], ![1] ] p.1) p.2 : _ → Fin 2) ∧
    (tupleBit L 2).Realize
      (fun p : Fin 2 × Fin 2 => (![![1, 0], ![0, 3] ] p.1) p.2 : _ → Fin 8) ∧
    (tupleBit L 3).Realize
      (fun p : Fin 2 × Fin 3 => (![![6, 2, 8], ![0, 1, 0] ] p.1) p.2 : _ → Fin 9) ∧
    (tupleBit L 2).Realize
      (fun p : Fin 2 × Fin 2 => (![![1, 2], ![0, 3] ] p.1) p.2 : _ → Fin 9) ∧
    (Radix.cardinality L (.var (.inl ()))
      (fun i => .var (.inr i))).Realize
      (Sum.elim (fun _ : Unit => (2 : Fin 64)) (![0, 0, 0, 0, 0, 0, 1] : Fin 7 → Fin 64)) ∧
    (tupleBit L 2).Realize
      (fun p : Fin 2 × Fin 2 => (![![1, 0], ![0, 6] ] p.1) p.2 : _ → Fin 64) ∧
    ¬(tupleBit L 3).Realize
      (fun p : Fin 2 × Fin 3 => (![![0, 0, 0], ![0, 0, 0] ] p.1) p.2 : _ → Fin 9) :=
  ⟨by rw [Radix.realize_decode _ _ _ _ (by decide)]; decide,
    by rw [Radix.realize_affine _ _ _ _ _ _ (by decide) (by decide)]; decide,
    by rw [realize_tupleBit]; decide,
    by rw [realize_tupleBit]; decide,
    by rw [realize_tupleBit]; decide,
    by rw [realize_tupleBit]; decide,
    by rw [realize_tupleBit]; decide,
    by rw [Radix.realize_cardinality _ _ _ (by decide) (by decide)]; decide,
    by rw [realize_tupleBit]; decide,
    by rw [realize_tupleBit]; decide⟩

/-- Maximum tuple indices are rejected, zero dimension is false, and relabeling retains rank
semantics. -/
example (x : Fin 2 → Fin 9) (v0 : Fin 2 × Fin 0 → Fin 9) (v : Fin 3 × Fin 2 → Fin 9) :
    ¬(tupleBit L 2).Realize (fun p => (![x, ![8, 8] ] p.1) p.2) ∧
    ¬(tupleBit L 0).Realize v0 ∧
    (((tupleBit L 2).relabel (fun p => (p.1.succ, p.2))).Realize v ↔
      (lexRank (fun i => v (1, i))).testBit (lexRank (fun i => v (2, i))) = true) := by
  refine ⟨?_, by simp [lexRank_apply], by rw [Formula.realize_relabel, realize_tupleBit]; rfl⟩
  apply not_realize_tupleBit_of_lt
  have hx := lexRank_lt x
  change lexRank x < 2 ^ 80
  exact lt_trans hx (by decide)

end Cslib.Tests.OrderedTupleBit
