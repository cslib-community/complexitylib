/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Ordered.Radix.Conversion
import CslibFrontier.Tactic.FirstOrder

/-!
# Cardinality words and full-word bit indices

The cardinality is obtained by adding one to a decoded maximum, without requiring the
cardinality itself to be a source element. Bit positions are compared as whole radix words;
neither the position nor a fixed chunk number must fit in one source element.

## Main definitions

* `Cslib.Logic.FO.Ordered.Radix.cardinality`: the source cardinality as a radix word.
* `Cslib.Logic.FO.Ordered.Radix.bitIndex`: read a bit at a word-valued index.

## Main results

* `Cslib.Logic.FO.Ordered.Radix.realize_cardinality`: exact cardinality, including its high digit.
* `Cslib.Logic.FO.Ordered.Radix.realize_bitIndex`: exact bit semantics and high-index rejection.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Exercise 1.33(3): the full-tuple
  application.
-/

@[expose] public section

namespace Cslib.Logic.FO.Ordered.Radix

open FirstOrder Language Structure

/-- Represent the source cardinality by decoding `max` and adding one in the word domain. -/
noncomputable def cardinality (L : Language) {α : Type*} {m : ℕ}
    (B : (language L).Term α) (N : Fin m → (language L).Term α) :
    (language L).Formula α := Formula.iExs (Fin 2 × Fin m)
  (decode L (B.relabel Sum.inl) (max L) (fun i => .var (.inr (0, i))) ⊓
   decode L (B.relabel Sum.inl) (one L) (fun i => .var (.inr (1, i))) ⊓
   affine L (B.relabel Sum.inl) (one L)
     (fun i => .var (.inr (0, i))) (fun i => .var (.inr (1, i)))
     (fun i => (N i).relabel Sum.inl))

/-- A fixed disjunction selects a chunk; base-one conversion builds its full index `r*e+b`. -/
noncomputable def bitIndex (L : Language) {α : Type*} {d : ℕ}
    (B e : (language L).Term α) (x y : Fin d → (language L).Term α) :
    (language L).Formula α := Formula.iSup fun r : Fin d => Formula.iExs Unit
  ((le L (e.relabel Sum.inl) (.var (.inr ()))).not ⊓
   bit L ((x r).relabel Sum.inl) (.var (.inr ())) ⊓
   convert L (B.relabel Sum.inl) (fun _ : Fin 1 => one L)
     (Fin.cons (.var (.inr ())) (fun _ : Fin r.val => e.relabel Sum.inl))
     (fun i => (y i).relabel Sum.inl))

variable {L : Language} {n : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)] {α : Type*}

/-- When `1 < B` and `B ^ 3` fits in the universe, `cardinality L B N` holds exactly when `N` is
a radix-`B` word whose value is the universe size `n`, including its high digit. -/
@[fo_realize]
theorem realize_cardinality {m : ℕ} (B : (language L).Term α)
    (N : Fin m → (language L).Term α) (v : α → Fin n)
    (hB : 1 < (B.realize v).val) (hBn : (B.realize v).val ^ 3 < n) :
    (cardinality L B N).Realize v ↔
      (∀ i, ((N i).realize v).val < (B.realize v).val) ∧
      Nat.ofDigits (B.realize v).val (List.ofFn fun i => ((N i).realize v).val) = n := by
  have ha (w : Fin 2 × Fin m → Fin n) b' x' y' z' :=
    realize_affine (d := m) (B.relabel Sum.inl) b' x' y' z' (Sum.elim v w)
      (by simpa only [Term.realize_relabel, Function.comp_def, Sum.elim_inl] using hB)
      (by simpa only [Term.realize_relabel, Function.comp_def, Sum.elim_inl] using hBn)
  have hd (w : Fin 2 × Fin m → Fin n) x' z' :=
    realize_decode (d := m) (B.relabel Sum.inl) x' z' (Sum.elim v w)
      (by simpa only [Term.realize_relabel, Function.comp_def, Sum.elim_inl] using
        Nat.le_of_lt hB)
  fo_simp [cardinality, ha, hd, Function.comp_def, Nat.one_mul, and_assoc]
  have hn := Fact.out (p := 2 ≤ n)
  constructor
  · rintro ⟨w, _, hmax, _, hone, _, _, _, hN, he⟩
    refine ⟨hN, ?_⟩
    rw [hmax, hone] at he
    exact he.symm.trans (show n - 1 + 1 = n by lia)
  · rintro ⟨hN, he⟩
    have hcap : n < (B.realize v).val ^ m := by
      simpa only [he] using Nat.ofDigits_ofFn_lt hB _ hN
    obtain ⟨M, hM, hMv⟩ := exists_word (B.realize v)
      (show n - 1 < (B.realize v).val ^ m by lia)
    obtain ⟨O, hO, hOv⟩ := exists_word (B.realize v)
      (show 1 < (B.realize v).val ^ m by lia)
    refine ⟨(fun p => (![M, O] p.1) p.2), hM, hMv, hO, hOv, Nat.le_of_lt hB,
      hM, hO, hN, ?_⟩
    change Nat.ofDigits _ (List.ofFn fun i => (M i).val) +
      Nat.ofDigits _ (List.ofFn fun i => (O i).val) = _
    rw [hMv, hOv, he]
    lia

/-- For a radix `B = 2 ^ e` with `0 < e` and `B ^ 3` in the universe, and radix-`B` words `x` and
`y`, `bitIndex L B e x y` holds exactly when bit `y` of `x` is set. -/
@[fo_realize]
theorem realize_bitIndex {d : ℕ} (B e : (language L).Term α)
    (x y : Fin d → (language L).Term α) (v : α → Fin n)
    (he : 0 < (e.realize v).val) (hBe : (B.realize v).val = 2 ^ (e.realize v).val)
    (hBn : (B.realize v).val ^ 3 < n)
    (hx : ∀ i, ((x i).realize v).val < (B.realize v).val)
    (hy : ∀ i, ((y i).realize v).val < (B.realize v).val) :
    (bitIndex L B e x y).Realize v ↔
      (Nat.ofDigits (B.realize v).val (List.ofFn fun i => ((x i).realize v).val)).testBit
        (Nat.ofDigits (B.realize v).val (List.ofFn fun i => ((y i).realize v).val)) = true := by
  have hB : 1 < (B.realize v).val := by
    rw [hBe]
    exact one_lt_pow₀ (by decide) (by lia)
  have hc (r : Fin d) (w : Unit → Fin n) :=
    realize_convert (B.relabel Sum.inl) (fun _ : Fin 1 => one L)
      (Fin.cons (.var (.inr ())) (fun _ : Fin r.val => e.relabel Sum.inl))
      (fun i => (y i).relabel Sum.inl) (Sum.elim v w)
      (by simpa only [Term.realize_relabel, Function.comp_def, Sum.elim_inl] using hB)
      (by simpa only [Term.realize_relabel, Function.comp_def, Sum.elim_inl] using hBn)
      (by simp)
  fo_simp [bitIndex, hc, Function.comp_def, List.ofFn_const, List.replicate_one,
    Nat.ofDigits_singleton, Nat.ofDigits_one, List.sum_replicate, smul_eq_mul,
    Nat.ofDigits_ofFn_succ, Fin.cons_zero, Fin.cons_succ, Nat.one_mul, Fin.le_def, not_le,
    and_assoc]
  rw [hBe, Nat.testBit_ofDigits_ofFn he _ (fun i => hBe ▸ hx i)]
  constructor
  · rintro ⟨r, w, hwe, hb, _, _, hi⟩
    refine ⟨r, ⟨(w ()).val, hwe⟩, ?_, hb⟩
    simpa only [← hBe, Nat.add_comm] using hi
  · rintro ⟨r, b, hi, hb⟩
    let w : Unit → Fin n := fun _ => ⟨b.val, lt_trans b.isLt (e.realize v).isLt⟩
    refine ⟨r, w, b.isLt, hb, hBe ▸ hB, (fun i => hBe ▸ hy i), ?_⟩
    simpa only [w, hBe, Nat.add_comm] using hi

end Cslib.Logic.FO.Ordered.Radix
