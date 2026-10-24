/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Ordered.Tuple
public import Complexity.Logics.FirstOrder.Ordered.Radix.Bit

/-!
# Native BIT on arbitrary-base full tuples

Fixed-length radix words represent the ranks of both input tuples, including indices larger
than the source universe. The radix is a witnessed power of two with its cube in the source
universe. Seven radix digits represent the source cardinality; `7 * k` digits represent each
rank. Native word arithmetic converts the original base without modular overflow. A fixed
finite disjunction covers source sizes two through eight.

## Main definitions

* `Cslib.Logic.FO.Ordered.TupleBit.parameters`, `Cslib.Logic.FO.Ordered.TupleBit.radixFormula`,
  `Cslib.Logic.FO.Ordered.TupleBit.smallFormula`: binary-radix parameter conditions, the radix-word
  `BIT` formula for `n > 8`, and the finite disjunction for `2 ≤ n ≤ 8`.
* `Cslib.Logic.FO.Ordered.tupleBit`: native BIT on the full lexicographically numbered tuple
  universe. Its syntax depends on the dimension, never on the source cardinality.

## Main results

* `Cslib.Logic.FO.Ordered.realize_tupleBit`: exact BIT of natural-number lexicographic ranks.
* `Cslib.Logic.FO.Ordered.not_realize_tupleBit_of_lt`: rejection beyond the binary extent.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Remark 1.32 and Exercise 1.33(3).
  The source explicitly assumes the full tuple universe. The bounded radix-word construction
  here supplies that exercise's native numeric lifting; it makes no formula-size efficiency
  claim. Restricted tuple domains and numeric-preserving interpretation composition are separate
  obligations. Dimension zero is explicitly false, without claiming a canonical size-one target.
-/

@[expose] public section

namespace Cslib.Logic.FO.Ordered

open FirstOrder Language Structure

namespace TupleBit

private theorem ofDigits_rev {n k : ℕ} (x : Fin k → Fin n) :
    Nat.ofDigits n (List.ofFn fun i => (x i.rev).val) = lexRank x := by
  rw [Nat.ofDigits_ofFn_eq_sum, lexRank_eq_tupleIndex, tupleIndex_apply]
  rfl

/-- Parameter conditions for the binary radix `B = 2 ^ e` with `e ≥ 1` and `B ^ 3 < n`. -/
noncomputable def parameters (L : Language) {α : Type*}
    (e B : (language L).Term α) : (language L).Formula α :=
  le L (one L) e ⊓ powerOfTwo L B e ⊓ Formula.iExs (Fin 2)
    (mulEq L (B.relabel Sum.inl) (B.relabel Sum.inl) (.var (.inr 0)) ⊓
     mulEq L (.var (.inr 0)) (B.relabel Sum.inl) (.var (.inr 1)))

/-- Radix-word BIT formula for source sizes `n > 8`. -/
noncomputable def radixFormula (L : Language) (k : ℕ) :
    (language L).Formula (Fin 2 × Fin k) :=
  Formula.iExs (Fin 2 ⊕ (Fin 7 ⊕ (Fin 2 × Fin (7 * k)))) (
    let e : (language L).Term ((Fin 2 × Fin k) ⊕ _) := .var (.inr (.inl 0))
    let B := .var (.inr (.inl 1))
    let N := fun i : Fin 7 => Term.var (.inr (.inr (.inl i)))
    let X := fun i : Fin (7 * k) => Term.var (.inr (.inr (.inr (0, i))))
    let Y := fun i : Fin (7 * k) => Term.var (.inr (.inr (.inr (1, i))))
    parameters L e B ⊓ Radix.cardinality L B N ⊓
    Radix.convert L B N (fun i => .var (.inl (0, i.rev))) X ⊓
    Radix.convert L B N (fun i => .var (.inl (1, i.rev))) Y ⊓
    Radix.bitIndex L B e X Y)

variable {L : Language} {n : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)] {α : Type*}

private theorem realize_parameters (e B : (language L).Term α) (v : α → Fin n) :
    (parameters L e B).Realize v ↔
      0 < (e.realize v).val ∧ (B.realize v).val = 2 ^ (e.realize v).val ∧
      (B.realize v).val ^ 3 < n := by
  simp only [parameters, Formula.realize_inf, realize_le, realize_one_val,
    realize_powerOfTwo, Formula.realize_iExs, realize_mulEq, Term.realize_relabel,
    Term.realize_var, Function.comp_def, Sum.elim_inl, Sum.elim_inr, Fin.le_def, and_assoc]
  constructor
  · rintro ⟨he, hB, u, hs, hc⟩
    refine ⟨by lia, hB, ?_⟩
    have := (u 1).isLt
    nlinarith [show (B.realize v).val ^ 3 =
      (B.realize v).val * (B.realize v).val * (B.realize v).val by ring]
  · rintro ⟨he, hB, hc⟩
    have hpos : 0 < (B.realize v).val := hB ▸ Nat.two_pow_pos _
    have hs : (B.realize v).val ^ 2 < n := by
      have hle := Nat.pow_le_pow_right hpos (show 2 ≤ 3 by decide)
      exact lt_of_le_of_lt hle hc
    exact ⟨by lia, hB, ![⟨_, hs⟩, ⟨_, hc⟩], by dsimp; ring, by dsimp; ring⟩

private theorem radixFormula_sound {k : ℕ} (v : Fin 2 × Fin k → Fin n)
    (hf : (radixFormula L k).Realize v) :
    (lexRank (fun i => v (0, i))).testBit (lexRank (fun i => v (1, i))) = true := by
  simp only [radixFormula, Formula.realize_iExs, Formula.realize_inf, realize_parameters,
    Term.realize_var, Sum.elim_inr, and_assoc] at hf
  obtain ⟨w, he, hBe, hBn, hN, hX, hY, hb⟩ := hf
  let t (i : Fin 2) : (language L).Term
      ((Fin 2 × Fin k) ⊕ (Fin 2 ⊕ (Fin 7 ⊕ (Fin 2 × Fin (7 * k))))) :=
    .var (.inr (.inl i))
  have hB : 1 < (w (.inl 1)).val := by
    rw [hBe]
    exact one_lt_pow₀ (by decide) (by lia)
  rw [Radix.realize_cardinality (t 1) _ (Sum.elim v w) hB hBn] at hN
  simp only [t, Term.realize_var, Sum.elim_inr] at hN
  have hn : 1 ≤ Nat.ofDigits (w (.inl 1)).val
      (List.ofFn fun i => (w (.inr (.inl i))).val) := by
    rw [hN.2]
    have := Fact.out (p := 2 ≤ n)
    lia
  rw [Radix.realize_convert (t 1)
    (fun i => .var (.inr (.inr (.inl i)))) _ _ (Sum.elim v w) hB hBn hn] at hX hY
  simp only [t, Term.realize_var, Sum.elim_inr, Sum.elim_inl, hN.2,
    ofDigits_rev (fun i => v (0, i)), ofDigits_rev (fun i => v (1, i))] at hX hY
  rw [Radix.realize_bitIndex (t 1) (t 0)
    _ _ (Sum.elim v w) he hBe hBn hX.2.1 hY.2.1] at hb
  simpa only [t, Term.realize_var, Sum.elim_inr, ← hX.2.2, ← hY.2.2] using hb

private theorem radixFormula_complete {k : ℕ} (v : Fin 2 × Fin k → Fin n) (hn : 8 < n)
    (hb : (lexRank (fun i => v (0, i))).testBit (lexRank (fun i => v (1, i))) = true) :
    (radixFormula L k).Realize v := by
  obtain ⟨e, he, hc, hncap⟩ := Nat.exists_binary_radix hn
  let B := 2 ^ e
  have hB : 1 < B := one_lt_pow₀ (by decide) (by lia)
  have hbase := Nat.pow_le_pow_right (Nat.zero_lt_of_lt hB) (show 1 ≤ 3 by decide)
  have hBn : B < n := lt_of_le_of_lt (by simpa only [pow_one] using hbase) hc
  let bf : Fin n := ⟨B, hBn⟩
  let ef : Fin n := ⟨e, lt_trans Nat.lt_two_pow_self hBn⟩
  obtain ⟨N, hN, hNv⟩ := Radix.exists_word bf hncap
  have hcap (x : Fin k → Fin n) : lexRank x < B ^ (7 * k) := by
    calc lexRank x < n ^ k := lexRank_lt x
         _ ≤ (B ^ 7) ^ k := Nat.pow_le_pow_left (Nat.le_of_lt hncap) k
         _ = B ^ (7 * k) := (pow_mul B 7 k).symm
  obtain ⟨X, hX, hXv⟩ := Radix.exists_word bf (hcap fun i => v (0, i))
  obtain ⟨Y, hY, hYv⟩ := Radix.exists_word bf (hcap fun i => v (1, i))
  dsimp only [bf] at hNv hXv hYv
  let w : Fin 2 ⊕ (Fin 7 ⊕ (Fin 2 × Fin (7 * k))) → Fin n :=
    Sum.elim ![ef, bf] (Sum.elim N (fun p => (![X, Y] p.1) p.2))
  let t (i : Fin 2) : (language L).Term
      ((Fin 2 × Fin k) ⊕ (Fin 2 ⊕ (Fin 7 ⊕ (Fin 2 × Fin (7 * k))))) :=
    .var (.inr (.inl i))
  simp only [radixFormula, Formula.realize_iExs, Formula.realize_inf, and_assoc]
  refine ⟨w, ?_, ?_, ?_, ?_, ?_⟩
  · exact (realize_parameters (t 0) (t 1) (Sum.elim v w)).mpr ⟨he, rfl, hc⟩
  · exact (Radix.realize_cardinality (t 1) _ (Sum.elim v w) hB hc).mpr ⟨hN, hNv⟩
  · apply (Radix.realize_convert (t 1)
      (fun i => .var (.inr (.inr (.inl i)))) _ _ (Sum.elim v w) hB hc ?_).mpr
    · refine ⟨hN, hX, ?_⟩
      change Nat.ofDigits (Nat.ofDigits B (List.ofFn fun i => (N i).val))
        (List.ofFn fun i => (v (0, i.rev)).val) = Nat.ofDigits B (List.ofFn fun i => (X i).val)
      rw [hNv, ofDigits_rev (fun i => v (0, i)), hXv]
    · change 1 ≤ Nat.ofDigits B (List.ofFn fun i => (N i).val)
      rw [hNv]
      lia
  · apply (Radix.realize_convert (t 1)
      (fun i => .var (.inr (.inr (.inl i)))) _ _ (Sum.elim v w) hB hc ?_).mpr
    · refine ⟨hN, hY, ?_⟩
      change Nat.ofDigits (Nat.ofDigits B (List.ofFn fun i => (N i).val))
        (List.ofFn fun i => (v (1, i.rev)).val) = Nat.ofDigits B (List.ofFn fun i => (Y i).val)
      rw [hNv, ofDigits_rev (fun i => v (1, i)), hYv]
    · change 1 ≤ Nat.ofDigits B (List.ofFn fun i => (N i).val)
      rw [hNv]
      lia
  · apply (Radix.realize_bitIndex (t 1) (t 0)
      _ _ (Sum.elim v w) he rfl hc hX hY).mpr
    change (Nat.ofDigits B (List.ofFn fun i => (X i).val)).testBit
      (Nat.ofDigits B (List.ofFn fun i => (Y i).val)) = true
    simpa only [hXv, hYv] using hb

/-- Finite disjunction BIT formula for small source sizes `2 ≤ n ≤ 8`. -/
noncomputable def smallFormula (L : Language) (k : ℕ) :
    (language L).Formula (Fin 2 × Fin k) :=
  Formula.iSup fun a : Fin 7 => Formula.iSup fun x : Fin k → Fin (a.val + 2) =>
    Formula.iSup fun y : Fin k → Fin (a.val + 2) =>
      if (lexRank x).testBit (lexRank y) = true then
        natEq L (a.val + 1) (max L) ⊓
        (Formula.iInf fun i => natEq L (x i).val (.var (0, i))) ⊓
        (Formula.iInf fun i => natEq L (y i).val (.var (1, i)))
      else ⊥

private theorem smallFormula_sound {k : ℕ} (v : Fin 2 × Fin k → Fin n)
    (hf : (smallFormula L k).Realize v) :
    (lexRank (fun i => v (0, i))).testBit (lexRank (fun i => v (1, i))) = true := by
  simp only [smallFormula, Formula.realize_iSup] at hf
  obtain ⟨a, x, y, hf⟩ := hf
  split_ifs at hf with hb
  · simp only [Formula.realize_inf, Formula.realize_iInf, realize_natEq,
      realize_max_val, Term.realize_var, and_assoc] at hf
    obtain ⟨hn, hx, hy⟩ := hf
    have hn' : n = a.val + 2 := by have := Fact.out (p := 2 ≤ n); lia
    subst n
    have hx' : (fun i => v (0, i)) = x := funext fun i => Fin.ext (hx i)
    have hy' : (fun i => v (1, i)) = y := funext fun i => Fin.ext (hy i)
    simpa only [hx', hy'] using hb
  · exact False.elim hf

private theorem smallFormula_complete {k : ℕ} (v : Fin 2 × Fin k → Fin n) (hn : n ≤ 8)
    (hb : (lexRank (fun i => v (0, i))).testBit (lexRank (fun i => v (1, i))) = true) :
    (smallFormula L k).Realize v := by
  have hn2 := Fact.out (p := 2 ≤ n)
  let a : Fin 7 := ⟨n - 2, by lia⟩
  have ha : a.val + 2 = n := by dsimp [a]; lia
  let x (p : Fin 2) (i : Fin k) : Fin (a.val + 2) := (v (p, i)).cast ha.symm
  have hx (p : Fin 2) : lexRank (x p) = lexRank (fun i => v (p, i)) := by
    simp only [lexRank_apply, x, Fin.val_cast, ha]
  have hb' : (lexRank (x 0)).testBit (lexRank (x 1)) = true := by
    simpa only [hx] using hb
  simp only [smallFormula, Formula.realize_iSup]
  refine ⟨a, x 0, x 1, ?_⟩
  simp only [ite_eq_left hb', Formula.realize_inf, Formula.realize_iInf, realize_natEq,
    realize_max_val, Term.realize_var]
  exact ⟨⟨by lia, fun _ => rfl⟩, fun _ => rfl⟩

end TupleBit

/-- Native BIT of full-tuple lexicographic ranks, uniformly over every canonical `Fin n`, `n ≥ 2`.
The zero-dimensional formula is false; no canonical numeric structure on a singleton is claimed. -/
noncomputable def tupleBit (L : Language) (k : ℕ) :
    (language L).Formula (Fin 2 × Fin k) :=
  if k = 0 then ⊥ else TupleBit.smallFormula L k ⊔ TupleBit.radixFormula L k

variable {L : Language} {n k : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)]

/-- Exact rank semantics for all source sizes, including non-powers of two and high indices. -/
@[simp, fo_realize]
theorem realize_tupleBit (v : Fin 2 × Fin k → Fin n) :
    (tupleBit L k).Realize v ↔
      (lexRank (fun i => v (0, i))).testBit (lexRank (fun i => v (1, i))) = true := by
  by_cases hk : k = 0
  · subst k
    simp [tupleBit, lexRank_apply]
  · simp only [tupleBit, ite_eq_right hk, Formula.realize_sup]
    constructor
    · rintro (h | h)
      · exact TupleBit.smallFormula_sound v h
      · exact TupleBit.radixFormula_sound v h
    · intro hb
      by_cases hn : n ≤ 8
      · exact Or.inl (TupleBit.smallFormula_complete v hn hb)
      · exact Or.inr (TupleBit.radixFormula_complete v (by lia) hb)

/-- A bit index beyond the represented number's binary extent is rejected. -/
theorem not_realize_tupleBit_of_lt (v : Fin 2 × Fin k → Fin n)
    (h : lexRank (fun i => v (0, i)) < 2 ^ lexRank (fun i => v (1, i))) :
    ¬(tupleBit L k).Realize v := by
  intro hb
  have := Nat.ge_two_pow_of_testBit ((realize_tupleBit v).mp hb)
  lia

end Cslib.Logic.FO.Ordered
