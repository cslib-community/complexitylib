/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Ordered.Radix.Multiplication

/-!
# Native conversion between scalar and word-valued radices

The input base is itself a fixed-length word, so it can represent the cardinality of the
source universe. Input scalars are evaluated least-significant-first by exact Horner equations.
They need not be smaller than that base; base one therefore also evaluates fixed scalar sums.

## Main definitions

* `Cslib.Logic.FO.Ordered.Radix.convert`: evaluate scalar digits in a word-valued input base.

## Main results

* `Cslib.Logic.FO.Ordered.Radix.realize_convert`: exact value semantics, including base one.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Exercise 1.33(3): the application to
  lexicographic tuple ranks.
-/

@[expose] public section

namespace Cslib.Logic.FO.Ordered.Radix

open FirstOrder Language Structure

/-- Evaluate a fixed scalar sequence in a word-valued base, using exact Horner arithmetic. -/
noncomputable def convert (L : Language) {α : Type*} {d m k : ℕ}
    (B : (language L).Term α) (N : Fin m → (language L).Term α)
    (x : Fin k → (language L).Term α) (z : Fin d → (language L).Term α) :
    (language L).Formula α := digits L B N ⊓ digits L B z ⊓
  Formula.iExs ((Fin (k + 1) ⊕ Fin 2 × Fin k) × Fin d)
    ((Formula.iInf fun j : Fin d =>
        (Term.var (.inr (.inl 0, j))).equal ((z j).relabel Sum.inl)) ⊓
     (Formula.iInf fun j : Fin d =>
        (Term.var (.inr (.inl (Fin.last k), j))).equal (zero L)) ⊓
     Formula.iInf fun i : Fin k =>
       decode L (B.relabel Sum.inl) ((x i).relabel Sum.inl)
         (fun j => .var (.inr (.inr (0, i), j))) ⊓
       multiply L (B.relabel Sum.inl) (fun j => .var (.inr (.inl i.succ, j)))
         (fun j => (N j).relabel Sum.inl) (fun j => .var (.inr (.inr (1, i), j))) ⊓
       affine L (B.relabel Sum.inl) (one L)
         (fun j => .var (.inr (.inr (1, i), j)))
         (fun j => .var (.inr (.inr (0, i), j)))
         (fun j => .var (.inr (.inl i.castSucc, j))))

variable {L : Language} {n : ℕ} [Fact (2 ≤ n)] [L.Structure (Fin n)] {α : Type*}

/-- When `1 < B`, `B ^ 3` fits in the universe and the word `N` is nonzero, `convert L B N x z`
holds exactly when `N` and `z` are radix-`B` words and the digits `x`, read in base `N`, have the
value of `z`. -/
@[fo_realize]
theorem realize_convert {d m k : ℕ} (B : (language L).Term α)
    (N : Fin m → (language L).Term α) (x : Fin k → (language L).Term α)
    (z : Fin d → (language L).Term α) (v : α → Fin n)
    (hB : 1 < (B.realize v).val) (hBn : (B.realize v).val ^ 3 < n)
    (hN : 1 ≤ Nat.ofDigits (B.realize v).val (List.ofFn fun i => ((N i).realize v).val)) :
    (convert L B N x z).Realize v ↔
      (∀ i, ((N i).realize v).val < (B.realize v).val) ∧
      (∀ i, ((z i).realize v).val < (B.realize v).val) ∧
      Nat.ofDigits
          (Nat.ofDigits (B.realize v).val (List.ofFn fun i => ((N i).realize v).val))
          (List.ofFn fun i => ((x i).realize v).val) =
        Nat.ofDigits (B.realize v).val (List.ofFn fun i => ((z i).realize v).val) := by
  have ha (w : ((Fin (k + 1) ⊕ Fin 2 × Fin k) × Fin d) → Fin n) b' x' y' z' :=
    realize_affine (d := d) (B.relabel Sum.inl) b' x' y' z' (Sum.elim v w)
      (by simpa only [Term.realize_relabel, Function.comp_def, Sum.elim_inl] using hB)
      (by simpa only [Term.realize_relabel, Function.comp_def, Sum.elim_inl] using hBn)
  have hm (w : ((Fin (k + 1) ⊕ Fin 2 × Fin k) × Fin d) → Fin n) x' y' z' :=
    realize_multiply (d := d) (m := m) (B.relabel Sum.inl) x' y' z' (Sum.elim v w)
      (by simpa only [Term.realize_relabel, Function.comp_def, Sum.elim_inl] using hB)
      (by simpa only [Term.realize_relabel, Function.comp_def, Sum.elim_inl] using hBn)
  have hd (w : ((Fin (k + 1) ⊕ Fin 2 × Fin k) × Fin d) → Fin n) x' z' :=
    realize_decode (d := d) (B.relabel Sum.inl) x' z' (Sum.elim v w)
      (by simpa only [Term.realize_relabel, Function.comp_def, Sum.elim_inl] using
        Nat.le_of_lt hB)
  simp only [convert, Formula.realize_inf, realize_digits, Formula.realize_iExs,
    Formula.realize_iInf, Formula.realize_equal, ha, hm, hd, Term.realize_var,
    Term.realize_relabel, Function.comp_def, Sum.elim_inl, Sum.elim_inr, Fin.ext_iff,
    realize_zero_val, realize_one_val, Nat.one_mul, and_assoc]
  constructor
  · rintro ⟨hNdigits, hz, w, hw0, hwe, hs⟩
    refine ⟨hNdigits, hz, ?_⟩
    let A := Nat.ofDigits (B.realize v).val (List.ofFn fun i => ((N i).realize v).val)
    let R := fun i : Fin (k + 1) => Nat.ofDigits (B.realize v).val
      (List.ofFn fun j => (w (.inl i, j)).val)
    have he : R (Fin.last k) = 0 := by simp [R, hwe]
    have hr : ∀ i : Fin k, R i.castSucc = ((x i).realize v).val + A * R i.succ := by
      intro i
      rcases hs i with ⟨_, hdi, _, _, _, hmi, _, _, _, _, hai⟩
      dsimp [A, R] at *
      rw [hdi, ← hmi] at hai
      simpa only [Nat.add_comm, Nat.mul_comm] using hai.symm
    exact (Nat.ofDigits_eq_of_quotients _ R he hr).trans (by simp only [R, hw0])
  · rintro ⟨hNdigits, hz, he⟩
    let A := Nat.ofDigits (B.realize v).val (List.ofFn fun i => ((N i).realize v).val)
    let V := Nat.ofDigits A (List.ofFn fun i => ((x i).realize v).val)
    have hV : V < (B.realize v).val ^ d := by
      simpa only [V, A, he] using Nat.ofDigits_ofFn_lt hB _ hz
    obtain ⟨q, hq0, hqe, hqb, hqs⟩ := Nat.exists_radix_quotients hN
      (fun i => ((x i).realize v).val)
    have hr (i : Fin (k + 1)) := exists_word (B.realize v) (lt_of_le_of_lt (hqb i) hV)
    choose R hR hRv using hr
    have hdigit (i : Fin k) : ((x i).realize v).val ≤ V := by
      have := hqs i
      have := hqb i.castSucc
      dsimp [V, A]
      lia
    have hdword (i : Fin k) := exists_word (B.realize v)
      (lt_of_le_of_lt (hdigit i) hV)
    choose D hD hDv using hdword
    have ht (i : Fin k) : ∃ w : Fin d → Fin n,
        (∀ j, (w j).val < (B.realize v).val) ∧
        Nat.ofDigits (B.realize v).val (List.ofFn fun j => (w j).val) = q i.succ * A := by
      apply exists_word (B.realize v)
      have := hqs i
      have := hqb i.castSucc
      dsimp [V, A] at *
      apply lt_of_le_of_lt (show q i.succ * Nat.ofDigits (B.realize v).val
        (List.ofFn fun i => ((N i).realize v).val) ≤
        Nat.ofDigits (Nat.ofDigits (B.realize v).val (List.ofFn fun i => ((N i).realize v).val))
          (List.ofFn fun i => ((x i).realize v).val) by nlinarith) hV
    choose T hT hTv using ht
    let w : ((Fin (k + 1) ⊕ Fin 2 × Fin k) × Fin d) → Fin n := fun p =>
      Sum.elim (fun i => R i p.2) (fun i => (![D i.2, T i.2] i.1) p.2) p.1
    refine ⟨hNdigits, hz, w, ?_, ?_, ?_⟩
    · have h := Nat.ofDigits_ofFn_inj hB (hR 0) hz
        (show Nat.ofDigits (B.realize v).val (List.ofFn fun j => (R 0 j).val) = _ by
          rw [hRv, hq0]
          exact he)
      exact fun j => congrFun h j
    · have h := Nat.ofDigits_ofFn_inj hB (hR (Fin.last k))
        (fun _ : Fin d => show 0 < (B.realize v).val by lia)
        (show Nat.ofDigits (B.realize v).val (List.ofFn fun j => (R (Fin.last k) j).val) =
            Nat.ofDigits (B.realize v).val (List.ofFn fun _ : Fin d => 0) by
          simp only [hRv, hqe, List.ofFn_const, Nat.ofDigits_replicate_zero])
      exact fun j => congrFun h j
    · intro i
      dsimp [w]
      refine ⟨hD i, hDv i, hR i.succ, hNdigits, hT i, ?_, Nat.le_of_lt hB,
        hT i, hD i, hR i.castSucc, ?_⟩
      · rw [hRv, hTv]
      · rw [hTv, hDv, hRv, hqs i]
        dsimp [A]
        ring

end Cslib.Logic.FO.Ordered.Radix
