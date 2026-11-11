/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.CSP.VariableElimination
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Rat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.TreeEval.Ary.IterativeEncoding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Ring

/-!
# Weight-cost, bit-length bounds, and encoded factor tables for variable elimination

This module analyses weight growth and binary representation cost of variable elimination
(`Cslib.Algorithms.Lean.CSP.eliminateOrder`) over integer (`ℤ`), rational (`ℚ`), and finite-field
(`ZMod p`) weights, together with concrete `enc_structure`-encoded factor table records:

* **Integers (`ℤ`):** Using a subtree step-and-multiplicity budget invariant along
  `eliminateOrder`, every intermediate table entry `z` and final contraction result satisfy
  `z.natAbs ≤ d ^ order.length * W ^ init.live.length`, avoiding doubly-exponential bit growth
  and keeping `encIntBin z` within `order.length * d.size + init.live.length * W.size + 3` bits
  (`natAbs_entry_eliminateOrder_le`, `length_encIntBin_entry_eliminateOrder_le`).
* **Finite fields (`ZMod p`, `NeZero p`):** Every intermediate entry remains below `p`, so
  `Cslib.TreeEval.Ary.Iter.encField p` uses at most `p.size` bits per entry and peak live bit
  memory across `order` is at most `peakLiveEntries d order init * p.size`
  (`liveFieldBits_eliminateOrder_le`).
* **Rationals (`ℚ`):** Direct fraction reduction satisfies `den (a + b) ≤ a.den * b.den`,
  `|num (a + b)| ≤ |a.num| * b.den + |b.num| * a.den`, and multiplicative step bounds on
  `elimBucketTable` (`rat_elimBucketTable_bounds`, bounded under `Turing.MultiTapeTM.encRat`).
  Clearing a positive common denominator `D_i ≤ D` per initial factor reduces rational
  elimination to integer elimination plus a single division by `∏ D_i ≤ D ^ M₀`
  (`result_eliminateOrder_ratScaled`), giving linear result bit-length under `encRat`
  (`length_encRat_cleared_result_le`).
* **Encoded records (`#4391`):** `NatFactorRecord`, `IntFactorRecord`, `RatFactorRecord`, and
  `ModFactorRecord` paired with `enc_structure` multi-tape encodings and conversions to
  `FactorTable`.

## Main definitions

* `Cslib.Algorithms.Lean.CSP.FactorTable.mapHom`,
  `Cslib.Algorithms.Lean.CSP.FactorTable.scale`: ring-homomorphism transport and factor scaling.
* `Cslib.Algorithms.Lean.CSP.NatFactorRecord`, `Cslib.Algorithms.Lean.CSP.IntFactorRecord`,
  `Cslib.Algorithms.Lean.CSP.RatFactorRecord`, `Cslib.Algorithms.Lean.CSP.ModFactorRecord`:
  documented monomorphic factor records with `enc_structure` encodings.

## Main results

* `Cslib.Algorithms.Lean.CSP.natAbs_entry_eliminateOrder_le`,
  `Cslib.Algorithms.Lean.CSP.length_encIntBin_entry_eliminateOrder_le`: integer weight and
  bit-length bounds across `eliminateOrder`.
* `Cslib.Algorithms.Lean.CSP.liveFieldBits_eliminateOrder_le`: finite-field bit-storage bound.
* `Cslib.Algorithms.Lean.CSP.rat_elimBucketTable_bounds`,
  `Cslib.Algorithms.Lean.CSP.result_eliminateOrder_ratScaled`,
  `Cslib.Algorithms.Lean.CSP.length_encRat_cleared_result_le`: rational elimination fraction and
  `encRat` bit-length bounds.
-/

public section

namespace Cslib.Algorithms.Lean.CSP

open Cslib.Logic.PL.CSP Turing.MultiTapeTM

/-! ### Binary bit-length helpers -/

section BitLengthHelpers

private theorem length_encNat_eq (n : ℕ) : (encNat n).length = n.size := by
  rw [encNat_apply, Nat.size_eq_bits_len]

/-- Binary size of a product is at most the sum of factor binary sizes. -/
theorem natSize_mul_le (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  by_cases ha : a = 0
  · subst ha; simp
  · by_cases hb : b = 0
    · subst hb; simp
    · rw [Nat.size_le]
      have ha_lt : a < 2 ^ a.size := Nat.lt_size_self a
      have hb_lt : b < 2 ^ b.size := Nat.lt_size_self b
      calc a * b < a * 2 ^ b.size := Nat.mul_lt_mul_of_pos_left hb_lt (Nat.pos_of_ne_zero ha)
        _ < 2 ^ a.size * 2 ^ b.size :=
            Nat.mul_lt_mul_of_pos_right ha_lt (Nat.pow_pos (by decide))
        _ = 2 ^ (a.size + b.size) := (pow_add 2 a.size b.size).symm

/-- Binary size of a power `a ^ k` is at most `k * a.size + 1`. -/
theorem natSize_pow_le (a k : ℕ) : (a ^ k).size ≤ k * a.size + 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      calc (a ^ k * a).size ≤ (a ^ k).size + a.size := natSize_mul_le _ _
        _ ≤ (k * a.size + 1) + a.size := Nat.add_le_add_right ih _
        _ = (k + 1) * a.size + 1 := by ring

/-- Exact encoded bit length of a rational under `Turing.MultiTapeTM.encRat`. -/
theorem length_encRat (q : ℚ) :
    (encRat q).length = 2 * (q.num.natAbs.size + 1) + 1 + q.den.size := by
  rw [encRat_apply, length_encPair, length_encIntBin, length_encNat_eq]

/-- Upper bound on `(encRat q).length` in terms of `|q.num|` and `q.den` binary sizes. -/
theorem length_encRat_le (q : ℚ) {A B : ℕ} (hnum : q.num.natAbs ≤ A) (hden : q.den ≤ B) :
    (encRat q).length ≤ 2 * A.size + B.size + 3 := by
  rw [length_encRat]
  have hn : q.num.natAbs.size ≤ A.size := Nat.size_le_size hnum
  have hd : q.den.size ≤ B.size := Nat.size_le_size hden
  omega

end BitLengthHelpers

/-! ### Integer (`ℤ`) weight growth and `encIntBin` bounds -/

section IntegerCost

variable {V : Type*}

private def IntBudgetFor (d W : ℕ) (f : FactorTable ℤ V) (b : ℕ × ℕ) : Prop :=
  ∀ z ∈ f.entries.toList, z.natAbs ≤ d ^ b.1 * W ^ b.2

private def IntBudgetInvariant [DecidableEq V] (d W M₀ k : ℕ) (s : ElimState ℤ V) : Prop :=
  ∃ (iso : ℕ) (buds : List (ℕ × ℕ)),
    List.Forall₂ (IntBudgetFor d W) s.live buds ∧
    s.scalar.natAbs ≤ d ^ iso ∧
    iso + (buds.map Prod.fst).sum ≤ k ∧
    (buds.map Prod.snd).sum ≤ M₀

private theorem prod_natAbs_le_of_forall₂ {d W : ℕ}
    {bucket : List (FactorTable ℤ V)} {buds : List (ℕ × ℕ)}
    (hb : List.Forall₂ (IntBudgetFor d W) bucket buds) (σ : V → ℕ) :
    ((bucket.map fun f => FactorTable.evalAt d f σ).prod).natAbs ≤
      d ^ (buds.map Prod.fst).sum * W ^ (buds.map Prod.snd).sum := by
  induction hb with
  | nil => simp
  | @cons f b fs bs hhead _ ih =>
      have hf : (FactorTable.evalAt d f σ).natAbs ≤ d ^ b.1 * W ^ b.2 := by
        rw [FactorTable.evalAt, Array.getD]
        split_ifs with hidx
        · exact hhead _ (Array.getElem_mem_toList hidx)
        · simp
      simp only [List.map_cons, List.prod_cons, Int.natAbs_mul, List.sum_cons, pow_add]
      calc (FactorTable.evalAt d f σ).natAbs *
              ((fs.map fun g => FactorTable.evalAt d g σ).prod).natAbs
          ≤ (d ^ b.1 * W ^ b.2) *
              (d ^ (bs.map Prod.fst).sum * W ^ (bs.map Prod.snd).sum) :=
            Nat.mul_le_mul hf ih
        _ = (d ^ b.1 * d ^ (bs.map Prod.fst).sum) *
              (W ^ b.2 * W ^ (bs.map Prod.snd).sum) := by ring

private theorem filter_forall₂ {α β : Type*} (p : α → Bool) {R : α → β → Prop} :
    ∀ {l : List α} {bs : List β}, List.Forall₂ R l bs →
      ∃ b₁ b₂ : List β,
        List.Forall₂ R (l.filter p) b₁ ∧
        List.Forall₂ R (l.filter fun a => !p a) b₂ ∧
        (∀ g : β → ℕ, (b₁.map g).sum + (b₂.map g).sum = (bs.map g).sum)
  | [], [], .nil => ⟨[], [], .nil, .nil, fun _ => rfl⟩
  | a :: l, x :: b, .cons hab hrest => by
      rcases filter_forall₂ p hrest with ⟨b₁, b₂, h₁, h₂, hsum⟩
      by_cases ha : p a = true
      · refine ⟨x :: b₁, b₂, ?_, ?_, ?_⟩
        · simpa [ha] using List.Forall₂.cons hab h₁
        · simpa [ha] using h₂
        · intro g
          simp only [List.map_cons, List.sum_cons]
          have := hsum g
          omega
      · refine ⟨b₁, x :: b₂, ?_, ?_, ?_⟩
        · simpa [ha] using h₁
        · simpa [ha] using List.Forall₂.cons hab h₂
        · intro g
          simp only [List.map_cons, List.sum_cons]
          have := hsum g
          omega

private theorem intBudgetInvariant_elimVar [DecidableEq V] {d W M₀ k : ℕ} (x : V)
    {s : ElimState ℤ V} (hs : IntBudgetInvariant d W M₀ k s) :
    IntBudgetInvariant d W M₀ (k + 1) (elimVar d x s) := by
  rcases hs with ⟨iso, buds, hforall, hiso, hfst, hsnd⟩
  by_cases hx : x ∈ s.remaining
  · rw [elimVar]
    simp only [hx, ↓reduceIte]
    split_ifs with hb
    · refine ⟨iso + 1, buds, hforall, ?_, by omega, hsnd⟩
      calc (s.scalar * (d : ℤ)).natAbs
          = s.scalar.natAbs * d := by simp [Int.natAbs_mul]
        _ ≤ d ^ iso * d := Nat.mul_le_mul_right d hiso
        _ = d ^ (iso + 1) := (pow_succ d iso).symm
    · let p := fun f : FactorTable ℤ V => decide (x ∈ f.scope)
      rcases filter_forall₂ p hforall with ⟨budsB, budsR, hB, hR, hsum⟩
      have hrest : (s.live.filter fun f => !p f) =
          s.live.filter fun f => decide (x ∉ f.scope) := by
        simp only [p, decide_not]
      rw [hrest] at hR
      let tNew := (budsB.map Prod.fst).sum + 1
      let mNew := (budsB.map Prod.snd).sum
      have hnew : IntBudgetFor d W (elimBucketTable d x (s.live.filter p)) (tNew, mNew) := by
        intro z hz
        simp only [elimBucketTable, Array.toList_ofFn, List.mem_ofFn] at hz
        rcases hz with ⟨idx, rfl⟩
        have hprod : ∀ a : Fin d,
            Int.natAbs ((List.map (fun f => FactorTable.evalAt d f fun v =>
              if v = x then a.1 else assignScope (bucketOutScope x (s.live.filter p))
                (lsbDecode d (bucketOutScope x (s.live.filter p)).length idx.1) v)
              (s.live.filter p)).prod) ≤
            d ^ (budsB.map Prod.fst).sum * W ^ (budsB.map Prod.snd).sum :=
          fun a => prod_natAbs_le_of_forall₂ hB _
        calc Int.natAbs (∑ a : Fin d, _)
            ≤ ∑ a : Fin d, Int.natAbs ((List.map (fun f => FactorTable.evalAt d f fun v =>
                if v = x then a.1 else assignScope (bucketOutScope x (s.live.filter p))
                  (lsbDecode d (bucketOutScope x (s.live.filter p)).length idx.1) v)
                (s.live.filter p)).prod) :=
              Int.natAbs_sum_le _ _
          _ ≤ ∑ _ : Fin d, d ^ (budsB.map Prod.fst).sum * W ^ (budsB.map Prod.snd).sum :=
              Finset.sum_le_sum fun a _ => hprod a
          _ = d * (d ^ (budsB.map Prod.fst).sum * W ^ (budsB.map Prod.snd).sum) := by
              simp [Finset.sum_const, smul_eq_mul]
          _ = d ^ tNew * W ^ mNew := by
              simp only [tNew, mNew, pow_succ']
              ring
      refine ⟨iso, (tNew, mNew) :: budsR, List.Forall₂.cons hnew hR, hiso, ?_, ?_⟩
      · have := hsum Prod.fst
        simp only [List.map_cons, List.sum_cons, tNew]
        omega
      · have := hsum Prod.snd
        simp only [List.map_cons, List.sum_cons, mNew]
        omega
  · simp only [elimVar, hx, ↓reduceIte]
    exact ⟨iso, buds, hforall, hiso, by omega, hsnd⟩

private theorem intBudgetInvariant_init [DecidableEq V] (d : ℕ) {W : ℕ}
    (factors : List (FactorTable ℤ V)) (declared : List V)
    (hinit : ∀ f ∈ factors, ∀ z ∈ f.entries.toList, z.natAbs ≤ W) :
    IntBudgetInvariant d W factors.length 0 (ElimState.ofFactors factors declared) := by
  refine ⟨0, factors.map (fun _ => (0, 1)), ?_, by simp [ElimState.ofFactors], by simp, ?_⟩
  · simp only [ElimState.ofFactors]
    clear declared
    induction factors with
    | nil => exact .nil
    | cons f fs ih =>
        refine List.Forall₂.cons ?_ (ih fun g hg => hinit g (by simp [hg]))
        intro z hz
        simpa [IntBudgetFor] using hinit f (by simp) z hz
  · simp

private theorem intBudgetInvariant_eliminateOrder [DecidableEq V] (d W M₀ : ℕ) :
    ∀ (order : List V) (k : ℕ) (s : ElimState ℤ V),
      IntBudgetInvariant d W M₀ k s →
      IntBudgetInvariant d W M₀ (k + order.length) (eliminateOrder d order s)
  | [], k, s, hs => by simpa [eliminateOrder] using hs
  | x :: xs, k, s, hs => by
      have hs' := intBudgetInvariant_elimVar x hs
      have hres := intBudgetInvariant_eliminateOrder d W M₀ xs (k + 1) (elimVar d x s) hs'
      simpa [eliminateOrder, Nat.add_assoc, Nat.add_comm 1 xs.length] using hres

private theorem natAbs_prod_entries_le {d W : ℕ} :
    ∀ {live : List (FactorTable ℤ V)} {buds : List (ℕ × ℕ)},
      List.Forall₂ (IntBudgetFor d W) live buds →
      (live.map fun (f : FactorTable ℤ V) => f.entries.getD 0 0).prod.natAbs ≤
        d ^ (buds.map Prod.fst).sum * W ^ (buds.map Prod.snd).sum
  | _, _, .nil => by simp
  | f :: fs, b :: bs, .cons hhead hrest => by
      have hf : (f.entries.getD 0 0).natAbs ≤ d ^ b.1 * W ^ b.2 := by
        rw [Array.getD]
        split_ifs with h0
        · exact hhead _ (Array.getElem_mem_toList h0)
        · simp
      have ih := natAbs_prod_entries_le hrest
      simp only [List.map_cons, List.prod_cons, Int.natAbs_mul, List.sum_cons, pow_add]
      calc (f.entries.getD 0 0).natAbs *
              (fs.map fun (g : FactorTable ℤ V) => g.entries.getD 0 0).prod.natAbs
          ≤ (d ^ b.1 * W ^ b.2) *
              (d ^ (bs.map Prod.fst).sum * W ^ (bs.map Prod.snd).sum) :=
            Nat.mul_le_mul hf ih
        _ = (d ^ b.1 * d ^ (bs.map Prod.fst).sum) *
              (W ^ b.2 * W ^ (bs.map Prod.snd).sum) := by ring

private theorem natAbs_result_of_intBudget [DecidableEq V] {d W M₀ k : ℕ} (hd : 0 < d)
    (hW : 0 < W) {s : ElimState ℤ V} (hs : IntBudgetInvariant d W M₀ k s) :
    s.result.natAbs ≤ d ^ k * W ^ M₀ := by
  rcases hs with ⟨iso, buds, hforall, hiso, hfst, hsnd⟩
  have hprod := natAbs_prod_entries_le hforall
  rw [ElimState.result, Int.natAbs_mul]
  calc s.scalar.natAbs * (s.live.map fun (f : FactorTable ℤ V) => f.entries.getD 0 0).prod.natAbs
      ≤ d ^ iso * (d ^ (buds.map Prod.fst).sum * W ^ (buds.map Prod.snd).sum) :=
        Nat.mul_le_mul hiso hprod
    _ = d ^ (iso + (buds.map Prod.fst).sum) * W ^ (buds.map Prod.snd).sum := by
        rw [pow_add, mul_assoc]
    _ ≤ d ^ k * W ^ M₀ :=
        Nat.mul_le_mul (Nat.pow_le_pow_right hd hfst) (Nat.pow_le_pow_right hW hsnd)

/-- Final `ℤ` scalar contraction result has magnitude at most
`d ^ order.length * W ^ factors.length`. -/
theorem natAbs_result_eliminateOrder_le [DecidableEq V] {d W : ℕ} (hd : 0 < d) (hW : 0 < W)
    (factors : List (FactorTable ℤ V)) (declared order : List V)
    (hinit : ∀ f ∈ factors, ∀ z ∈ f.entries.toList, z.natAbs ≤ W) :
    (eliminateOrder d order (ElimState.ofFactors factors declared)).result.natAbs ≤
      d ^ order.length * W ^ factors.length := by
  have hinv := intBudgetInvariant_eliminateOrder d W factors.length order 0 _
    (intBudgetInvariant_init d factors declared hinit)
  rw [Nat.zero_add] at hinv
  exact natAbs_result_of_intBudget hd hW hinv

private theorem exists_budget_of_forall₂ {V : Type*} {R : FactorTable ℤ V → ℕ × ℕ → Prop}
    {f : FactorTable ℤ V} :
    ∀ {l : List (FactorTable ℤ V)} {bs : List (ℕ × ℕ)}, List.Forall₂ R l bs → f ∈ l →
      ∃ b ∈ bs, R f b ∧ b.1 ≤ (bs.map Prod.fst).sum ∧ b.2 ≤ (bs.map Prod.snd).sum
  | _ :: _, b :: _, .cons hab hrest, hf => by
      rcases List.mem_cons.mp hf with rfl | hf
      · exact ⟨b, by simp, hab, by simp, by simp⟩
      · rcases exists_budget_of_forall₂ hrest hf with ⟨c, hcb, hRc, h1, h2⟩
        exact ⟨c, by simp [hcb], hRc, by simp; omega, by simp; omega⟩

/-- Every live `ℤ` entry produced at any step along `order` has magnitude at most
`d ^ order.length * W ^ factors.length`. -/
theorem natAbs_entry_eliminateOrder_le [DecidableEq V] {d W : ℕ} (hd : 0 < d) (hW : 0 < W)
    (factors : List (FactorTable ℤ V)) (declared order : List V)
    (hinit : ∀ f ∈ factors, ∀ z ∈ f.entries.toList, z.natAbs ≤ W)
    {f : FactorTable ℤ V}
    (hf : f ∈ (eliminateOrder d order (ElimState.ofFactors factors declared)).live)
    {z : ℤ} (hz : z ∈ f.entries.toList) :
    z.natAbs ≤ d ^ order.length * W ^ factors.length := by
  have hinv := intBudgetInvariant_eliminateOrder d W factors.length order 0 _
    (intBudgetInvariant_init d factors declared hinit)
  rw [Nat.zero_add] at hinv
  rcases hinv with ⟨iso, buds, hforall, _, hfst, hsnd⟩
  rcases exists_budget_of_forall₂ hforall hf with ⟨b, _, hb, hb1, hb2⟩
  exact le_trans (hb z hz) (Nat.mul_le_mul
    (Nat.pow_le_pow_right hd (le_trans hb1 (by omega)))
    (Nat.pow_le_pow_right hW (le_trans hb2 hsnd)))

/-- Every live `ℤ` entry throughout `order` has binary code length at most
`order.length * d.size + factors.length * W.size + 3` under `encIntBin`. -/
theorem length_encIntBin_entry_eliminateOrder_le [DecidableEq V] {d W : ℕ} (hd : 0 < d)
    (hW : 0 < W) (factors : List (FactorTable ℤ V)) (declared order : List V)
    (hinit : ∀ f ∈ factors, ∀ z ∈ f.entries.toList, z.natAbs ≤ W)
    {f : FactorTable ℤ V}
    (hf : f ∈ (eliminateOrder d order (ElimState.ofFactors factors declared)).live)
    {z : ℤ} (hz : z ∈ f.entries.toList) :
    (encIntBin z).length ≤ order.length * d.size + factors.length * W.size + 3 := by
  rw [length_encIntBin]
  have hz_le := natAbs_entry_eliminateOrder_le hd hW factors declared order hinit hf hz
  calc z.natAbs.size + 1
      ≤ (d ^ order.length * W ^ factors.length).size + 1 :=
        Nat.add_le_add_right (Nat.size_le_size hz_le) 1
    _ ≤ ((d ^ order.length).size + (W ^ factors.length).size) + 1 :=
        Nat.add_le_add_right (natSize_mul_le _ _) 1
    _ ≤ ((order.length * d.size + 1) + (factors.length * W.size + 1)) + 1 :=
        Nat.add_le_add_right (Nat.add_le_add (natSize_pow_le _ _) (natSize_pow_le _ _)) 1
    _ = order.length * d.size + factors.length * W.size + 3 := by omega

end IntegerCost

/-! ### Finite-field (`ZMod p`) weight and bit-storage bounds -/

section FiniteFieldCost

variable {V : Type*}

/-- Every entry of any factor table over `ZMod p` uses at most `p.size` bits under
`Cslib.TreeEval.Ary.Iter.encField p`. -/
theorem length_encField_entry_le (p : ℕ) [NeZero p] (y : ZMod p) :
    (Cslib.TreeEval.Ary.Iter.encField p y).length ≤ p.size :=
  Cslib.TreeEval.Ary.Iter.length_encField_le p y

/-- Peak encoded bit storage across all live `ZMod p` factor tables during `eliminateOrder` is
bounded by `peakLiveEntries d order init * p.size` and hence by the intermediate-scope table bound
times `p.size`. -/
theorem liveFieldBits_eliminateOrder_le [DecidableEq V] {d p : ℕ} [NeZero p] (hd : 0 < d)
    (order : List V) (init : ElimState (ZMod p) V) :
    (liveEntries (eliminateOrder d order init).live) * p.size ≤
      init.live.length * max (maxTableEntries init.live) (d ^ maxOutScopeLen d order init) *
        p.size := by
  have hpeak : liveEntries (eliminateOrder d order init).live ≤ peakLiveEntries d order init := by
    rw [peakLiveEntries]
    clear hd
    suffices h : ∀ (ord : List V) (s : ElimState (ZMod p) V) (acc : ℕ),
        liveEntries s.live ≤ acc →
        liveEntries (eliminateOrder d ord s).live ≤
          ((traceOrder d ord s).map ElimStepStats.liveEntriesAfter).foldl max acc by
      exact h order init (liveEntries init.live) le_rfl
    intro ord
    induction ord with
    | nil =>
        intro s acc hacc
        simpa [eliminateOrder, traceOrder] using hacc
    | cons x xs ih =>
        intro s acc hacc
        simp only [eliminateOrder, traceOrder, List.map_cons, List.foldl_cons]
        exact ih (elimVar d x s) (max acc (stepStats d x s).liveEntriesAfter) (by
          have heq : (stepStats d x s).liveEntriesAfter = liveEntries (elimVar d x s).live := by
            simp only [stepStats]
            split_ifs <;> rfl
          rw [heq]
          exact le_max_right _ _)
  exact Nat.mul_le_mul_right p.size (le_trans hpeak (peakLiveEntries_le hd order init))

end FiniteFieldCost

/-! ### Rational (`ℚ`) direct step bounds and denominator-cleared polynomial bounds -/

section RationalCost

private theorem natAbs_num_divInt_le (a : ℤ) {b : ℕ} (hb : 0 < b) :
    (Rat.divInt a b).num.natAbs ≤ a.natAbs := by
  by_cases ha : a = 0
  · subst ha; simp
  · have hb_ne : (b : ℤ) ≠ 0 := by omega
    have hdvd := Rat.num_dvd a hb_ne
    have hnat : (Rat.divInt a b).num.natAbs ∣ a.natAbs := Int.natAbs_dvd_natAbs.mpr hdvd
    exact Nat.le_of_dvd (Int.natAbs_pos.mpr ha) hnat

private theorem den_divInt_le (a : ℤ) {b : ℕ} (hb : 0 < b) :
    (Rat.divInt a b).den ≤ b := by
  have hdvd : (Rat.divInt a b).den ∣ b := Int.ofNat_dvd.mp (Rat.den_dvd a b)
  exact Nat.le_of_dvd hb hdvd

/-- Reduced rational multiplication bounds: `|(a * b).num| ≤ |a.num| * |b.num|` and
`(a * b).den ≤ a.den * b.den`. -/
theorem rat_mul_bounds (a b : ℚ) :
    (a * b).num.natAbs ≤ a.num.natAbs * b.num.natAbs ∧ (a * b).den ≤ a.den * b.den := by
  have hden_pos : 0 < a.den * b.den := Nat.mul_pos a.pos b.pos
  have heq : a * b = Rat.divInt (a.num * b.num) (a.den * b.den) := by
    conv_lhs => rw [← Rat.num_div_den a, ← Rat.num_div_den b]
    rw [div_mul_div_comm, ← Int.cast_mul, ← Nat.cast_mul, Rat.divInt_eq_div]
    norm_cast
  rw [heq]
  exact ⟨by simpa [Int.natAbs_mul] using natAbs_num_divInt_le (a.num * b.num) hden_pos,
    den_divInt_le _ hden_pos⟩

/-- Reduced rational addition bounds: `|(a + b).num| ≤ |a.num| * b.den + |b.num| * a.den` and
`(a + b).den ≤ a.den * b.den`. -/
theorem rat_add_bounds (a b : ℚ) :
    (a + b).num.natAbs ≤ a.num.natAbs * b.den + b.num.natAbs * a.den ∧
      (a + b).den ≤ a.den * b.den := by
  have hden_pos : 0 < a.den * b.den := Nat.mul_pos a.pos b.pos
  have ha0 : (a.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr a.den_nz
  have hb0 : (b.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr b.den_nz
  have heq : a + b = Rat.divInt (a.num * b.den + b.num * a.den) (a.den * b.den) := by
    conv_lhs => rw [← Rat.num_div_den a, ← Rat.num_div_den b]
    rw [div_add_div _ _ ha0 hb0, Rat.divInt_eq_div]
    push_cast
    rw [mul_comm (b.num : ℚ) (a.den : ℚ)]
  rw [heq]
  have hnum : (a.num * (b.den : ℤ) + b.num * (a.den : ℤ)).natAbs ≤
      a.num.natAbs * b.den + b.num.natAbs * a.den := by
    calc (a.num * (b.den : ℤ) + b.num * (a.den : ℤ)).natAbs
        ≤ (a.num * (b.den : ℤ)).natAbs + (b.num * (a.den : ℤ)).natAbs := Int.natAbs_add_le _ _
      _ = a.num.natAbs * b.den + b.num.natAbs * a.den := by simp [Int.natAbs_mul]
  exact ⟨le_trans (natAbs_num_divInt_le _ hden_pos) hnum, den_divInt_le _ hden_pos⟩

/-- Height and denominator bounds for a rational list product. -/
theorem rat_list_prod_bounds {A B : ℕ} :
    ∀ rs : List ℚ, (∀ r ∈ rs, r.num.natAbs ≤ A ∧ r.den ≤ B) →
      rs.prod.num.natAbs ≤ A ^ rs.length ∧ rs.prod.den ≤ B ^ rs.length
  | [], _ => by simp
  | r :: rs, h => by
      have hr := h r (by simp)
      have hrs := rat_list_prod_bounds rs fun y hy => h y (by simp [hy])
      rw [List.prod_cons, List.length_cons, pow_succ', pow_succ']
      rcases rat_mul_bounds r rs.prod with ⟨hn, hd⟩
      exact ⟨le_trans hn (Nat.mul_le_mul hr.1 hrs.1), le_trans hd (Nat.mul_le_mul hr.2 hrs.2)⟩

/-- Height and denominator bounds for a sum over `Finset.range c` of bounded rationals. -/
theorem rat_sum_finset_bounds {P Q : ℕ} (hQ : 1 ≤ Q) (f : ℕ → ℚ) :
    ∀ c : ℕ, (∀ i < c, (f i).num.natAbs ≤ P ∧ (f i).den ≤ Q) →
      (∑ i ∈ Finset.range c, f i).num.natAbs ≤ c * P * Q ^ (c - 1) ∧
        (∑ i ∈ Finset.range c, f i).den ≤ Q ^ c
  | 0, _ => by simp
  | 1, h => by
      have h0 := h 0 (by decide)
      simpa using h0
  | c + 2, h => by
      have ih := rat_sum_finset_bounds hQ f (c + 1) fun i hi => h i (by omega)
      have hlast := h (c + 1) (by omega)
      rw [Finset.sum_range_succ]
      rcases rat_add_bounds (∑ i ∈ Finset.range (c + 1), f i) (f (c + 1)) with ⟨hn, hd⟩
      have hden_le : (∑ i ∈ Finset.range (c + 1), f i).den * (f (c + 1)).den ≤ Q ^ (c + 2) := by
        rw [pow_succ Q (c + 1)]
        exact Nat.mul_le_mul ih.2 hlast.2
      have hnum_le : (∑ i ∈ Finset.range (c + 1), f i).num.natAbs * (f (c + 1)).den +
          (f (c + 1)).num.natAbs * (∑ i ∈ Finset.range (c + 1), f i).den ≤
          (c + 2) * P * Q ^ (c + 1) := by
        calc (∑ i ∈ Finset.range (c + 1), f i).num.natAbs * (f (c + 1)).den +
              (f (c + 1)).num.natAbs * (∑ i ∈ Finset.range (c + 1), f i).den
            ≤ ((c + 1) * P * Q ^ c) * Q + P * Q ^ (c + 1) :=
              Nat.add_le_add (Nat.mul_le_mul ih.1 hlast.2) (Nat.mul_le_mul hlast.1 ih.2)
          _ = (c + 1) * P * Q ^ (c + 1) + P * Q ^ (c + 1) := by
              rw [pow_succ Q c]; ring
          _ = (c + 2) * P * Q ^ (c + 1) := by ring
      exact ⟨le_trans hn hnum_le, le_trans hd hden_le⟩

/-- Single-step direct rational elimination bounds on `elimBucketTable d x bucket`. -/
theorem rat_elimBucketTable_bounds {V : Type*} [DecidableEq V] {d A B : ℕ} (hB : 1 ≤ B)
    (x : V) (bucket : List (FactorTable ℚ V))
    (hb : ∀ f ∈ bucket, ∀ q ∈ f.entries.toList, q.num.natAbs ≤ A ∧ q.den ≤ B)
    {q : ℚ} (hq : q ∈ (elimBucketTable d x bucket).entries.toList) :
    q.num.natAbs ≤ d * A ^ bucket.length * B ^ (bucket.length * (d - 1)) ∧
      q.den ≤ B ^ (bucket.length * d) := by
  simp only [elimBucketTable, Array.toList_ofFn, List.mem_ofFn] at hq
  rcases hq with ⟨idx, rfl⟩
  let term : ℕ → ℚ := fun i =>
    (bucket.map fun f => f.evalAt d fun v => if v = x then i else
      assignScope (bucketOutScope x bucket)
        (lsbDecode d (bucketOutScope x bucket).length idx.1) v).prod
  have hsum_eq : (∑ a : Fin d, term a.1) = ∑ i ∈ Finset.range d, term i :=
    Fin.sum_univ_eq_sum_range term d
  change (∑ a : Fin d, term a.1).num.natAbs ≤ _ ∧ (∑ a : Fin d, term a.1).den ≤ _
  rw [hsum_eq]
  have hQ : 1 ≤ B ^ bucket.length := Nat.one_le_pow _ _ hB
  have hterm : ∀ i : ℕ, i < d →
      (term i).num.natAbs ≤ A ^ bucket.length ∧ (term i).den ≤ B ^ bucket.length := by
    intro i _
    have hprod := rat_list_prod_bounds
      (bucket.map fun f => f.evalAt d fun v => if v = x then i else
        assignScope (bucketOutScope x bucket)
          (lsbDecode d (bucketOutScope x bucket).length idx.1) v)
      fun r hr => by
        rcases List.mem_map.mp hr with ⟨f, hf, rfl⟩
        rw [FactorTable.evalAt, Array.getD]
        split_ifs with hidx
        · exact hb f hf _ (Array.getElem_mem_toList hidx)
        · exact ⟨by simp, hB⟩
    simpa [term, List.length_map] using hprod
  have hs := rat_sum_finset_bounds hQ term d hterm
  rw [← pow_mul, ← pow_mul] at hs
  exact ⟨by simpa [mul_assoc] using hs.1, hs.2⟩

/-- Ring-homomorphism transport on factor tables (`entries.map φ`). -/
@[expose] def mapFactorHom {R S V : Type*} [Semiring R] [Semiring S] (φ : R →+* S)
    (f : FactorTable R V) : FactorTable S V :=
  { scope := f.scope, entries := f.entries.map φ }

/-- Uniform scaling of every entry of a factor table (`c * ·`). -/
@[expose] def scaleFactor {R V : Type*} [Mul R] (c : R) (f : FactorTable R V) :
    FactorTable R V :=
  { scope := f.scope, entries := f.entries.map (c * ·) }

/-- Ring-homomorphism transport on `ElimState`. -/
@[expose] def ElimState.mapHom {R S V : Type*} [Semiring R] [Semiring S] (φ : R →+* S)
    (s : ElimState R V) : ElimState S V :=
  { scalar := φ s.scalar, live := s.live.map (mapFactorHom φ), remaining := s.remaining }

private theorem array_map_getD_zero {α β : Type*} [Zero α] [Zero β]
    (g : α → β) (hg : g 0 = 0) (a : Array α) (i : ℕ) :
    (a.map g).getD i 0 = g (a.getD i 0) := by
  by_cases h : i < a.size
  · simp [Array.getD, h]
  · simp [Array.getD, h, hg]

private theorem evalAt_mapHom {R S V : Type*} [Semiring R] [Semiring S] (φ : R →+* S)
    (d : ℕ) (f : FactorTable R V) (σ : V → ℕ) :
    (mapFactorHom φ f).evalAt d σ = φ (f.evalAt d σ) :=
  array_map_getD_zero φ (map_zero φ) f.entries _

private theorem evalAt_scale {R V : Type*} [Semiring R] (c : R) (d : ℕ) (f : FactorTable R V)
    (σ : V → ℕ) : (scaleFactor c f).evalAt d σ = c * f.evalAt d σ :=
  array_map_getD_zero (c * ·) (mul_zero c) f.entries _

/-- Scaling a factor list entrywise multiplies `contractionOn` by the product of the scales. -/
theorem contractionOn_zipWith_scale {R V : Type*} [CommSemiring R] [DecidableEq V] (d : ℕ) :
    ∀ (scales : List R) (factors : List (FactorTable R V)) (declared : Finset V),
      scales.length = factors.length →
      FactorTable.contractionOn d (List.zipWith scaleFactor scales factors) declared =
        scales.prod * FactorTable.contractionOn d factors declared := by
  intro scales factors declared hlen
  rw [FactorTable.contractionOn, FactorTable.contractionOn, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hprod : ((List.zipWith scaleFactor scales factors).map fun f =>
      f.evalAt d fun v => if h : v ∈ declared then (σ ⟨v, h⟩).1 else 0).prod =
      scales.prod * (factors.map fun f =>
        f.evalAt d fun v => if h : v ∈ declared then (σ ⟨v, h⟩).1 else 0).prod := by
    induction scales generalizing factors with
    | nil =>
        cases factors with
        | nil => simp
        | cons _ _ => simp at hlen
    | cons c cs ih =>
        cases factors with
        | nil => simp at hlen
        | cons f fs =>
            simp only [List.length_cons, Nat.succ.injEq] at hlen
            simp only [List.zipWith_cons_cons, List.map_cons, List.prod_cons, evalAt_scale]
            rw [ih fs hlen]
            ring
  exact hprod

private theorem elimVar_mapHom {R S V : Type*} [Semiring R] [Semiring S] [DecidableEq V]
    (φ : R →+* S) (d : ℕ) (x : V) (s : ElimState R V) :
    (elimVar d x s).mapHom φ = elimVar d x (s.mapHom φ) := by
  by_cases hx : x ∈ s.remaining
  · simp only [elimVar, hx, ↓reduceIte, ElimState.mapHom]
    have hfilt (p : List V → Bool) :
        (s.live.map (mapFactorHom φ)).filter (fun f => p f.scope) =
        (s.live.filter fun f => p f.scope).map (mapFactorHom φ) :=
      List.filter_map
    simp only [hfilt (fun sc => decide (x ∈ sc)), hfilt (fun sc => decide (x ∉ sc)),
      List.isEmpty_map]
    split_ifs with hb
    · simp [map_mul, map_natCast]
    · simp only [List.map_cons]
      have hscope :
          bucketOutScope x ((s.live.filter fun f => decide (x ∈ f.scope)).map
            (mapFactorHom φ)) =
          bucketOutScope x (s.live.filter fun f => decide (x ∈ f.scope)) := by
        simp only [bucketOutScope, bucketJointScope, List.flatMap_map]
        rfl
      have htab : mapFactorHom φ
          (elimBucketTable d x (s.live.filter fun f => decide (x ∈ f.scope))) =
          elimBucketTable d x ((s.live.filter fun f => decide (x ∈ f.scope)).map
            (mapFactorHom φ)) := by
        rw [elimBucketTable, elimBucketTable, hscope]
        simp only [mapFactorHom]
        congr 1
        ext i hi₁ hi₂
        · simp
        · simp only [Array.getElem_map, Array.getElem_ofFn, map_sum, map_list_prod, List.map_map,
            Function.comp_def, evalAt_mapHom]
      rw [htab]
  · simp [elimVar, hx, ElimState.mapHom]

/-- `eliminateOrder` commutes with any ring homomorphism `φ : R →+* S`. -/
theorem eliminateOrder_mapHom {R S V : Type*} [Semiring R] [Semiring S] [DecidableEq V]
    (φ : R →+* S) (d : ℕ) :
    ∀ (order : List V) (s : ElimState R V),
      (eliminateOrder d order s).mapHom φ = eliminateOrder d order (s.mapHom φ)
  | [], _ => rfl
  | x :: xs, s => by
      rw [eliminateOrder, eliminateOrder, ← elimVar_mapHom, eliminateOrder_mapHom φ d xs]

private theorem result_mapHom {R S V : Type*} [Semiring R] [Semiring S] (φ : R →+* S)
    (s : ElimState R V) : (s.mapHom φ).result = φ s.result := by
  simp only [ElimState.result, ElimState.mapHom, map_mul, map_list_prod, List.map_map,
    Function.comp_def]
  congr 1
  congr 1
  refine List.map_congr_left fun f _ => ?_
  exact array_map_getD_zero φ (map_zero φ) f.entries 0

/-- Denominator-cleared rational variable elimination: scaling integer factor tables `factorsℤ`
by positive denominators `denoms` preserves the exact rational contraction modulo a single division
by `denoms.prod`. -/
theorem result_eliminateOrder_ratScaled {V : Type*} [DecidableEq V] (d : ℕ)
    (denoms : List ℕ) (factorsℤ : List (FactorTable ℤ V)) (declared order : List V)
    (hlen : denoms.length = factorsℤ.length)
    (hcover : declared.toFinset ⊆ order.toFinset) :
    let factorsℚ := List.zipWith (fun (D : ℕ) f =>
      scaleFactor ((D : ℚ)⁻¹) (mapFactorHom (Int.castRingHom ℚ) f)) denoms factorsℤ
    (eliminateOrder d order (ElimState.ofFactors factorsℚ declared)).result =
      ((eliminateOrder d order (ElimState.ofFactors factorsℤ declared)).result : ℚ) /
        (denoms.prod : ℚ) := by
  dsimp only
  rw [result_eliminateOrder_of_subset d (by simpa [ElimState.ofFactors] using hcover)]
  simp only [ElimState.eval, ElimState.ofFactors, one_mul]
  have hzip : List.zipWith (fun (D : ℕ) f =>
      scaleFactor ((D : ℚ)⁻¹) (mapFactorHom (Int.castRingHom ℚ) f)) denoms factorsℤ =
      List.zipWith scaleFactor (denoms.map fun D : ℕ => (D : ℚ)⁻¹)
        (factorsℤ.map (mapFactorHom (Int.castRingHom ℚ))) := by
    induction denoms generalizing factorsℤ with
    | nil => cases factorsℤ <;> simp at hlen ⊢
    | cons D Ds ih =>
        cases factorsℤ with
        | nil => simp at hlen
        | cons f fs =>
            rw [List.zipWith_cons_cons, List.map_cons, List.map_cons, List.zipWith_cons_cons,
              ih fs (by simpa using hlen)]
  rw [hzip, contractionOn_zipWith_scale d _ _ declared.toFinset (by simpa using hlen)]
  have hhom : FactorTable.contractionOn d (factorsℤ.map (mapFactorHom (Int.castRingHom ℚ)))
      declared.toFinset =
      ((eliminateOrder d order (ElimState.ofFactors factorsℤ declared)).result : ℚ) := by
    have hmap := result_mapHom (Int.castRingHom ℚ)
      (eliminateOrder d order (ElimState.ofFactors factorsℤ declared))
    rw [eliminateOrder_mapHom] at hmap
    have hinit : (ElimState.ofFactors factorsℤ declared).mapHom (Int.castRingHom ℚ) =
        ElimState.ofFactors (factorsℤ.map (mapFactorHom (Int.castRingHom ℚ))) declared := by
      simp [ElimState.ofFactors, ElimState.mapHom]
    rw [hinit,
      result_eliminateOrder_of_subset d (by simpa [ElimState.ofFactors] using hcover)] at hmap
    simpa [ElimState.eval, ElimState.ofFactors] using hmap
  rw [hhom]
  have hprod : (denoms.map fun D : ℕ => ((D : ℚ)⁻¹)).prod = (denoms.prod : ℚ)⁻¹ := by
    clear hlen hzip hhom
    induction denoms with
    | nil => simp
    | cons D Ds ih =>
        rw [List.map_cons, List.prod_cons, List.prod_cons, ih, Nat.cast_mul, mul_inv, mul_comm]
  rw [hprod, div_eq_mul_inv, mul_comm]
  simp [ElimState.ofFactors]

/-- Cleared-denominator rational contraction height and denominator bounds. -/
theorem rat_cleared_result_bounds {V : Type*} [DecidableEq V] {d W D : ℕ}
    (hd : 0 < d) (hW : 0 < W) (_hD : 0 < D)
    (denoms : List ℕ) (factorsℤ : List (FactorTable ℤ V)) (declared order : List V)
    (hlen : denoms.length = factorsℤ.length)
    (hDpos : ∀ q ∈ denoms, 0 < q)
    (hDle : ∀ q ∈ denoms, q ≤ D)
    (hWle : ∀ f ∈ factorsℤ, ∀ z ∈ f.entries.toList, z.natAbs ≤ W)
    (hcover : declared.toFinset ⊆ order.toFinset) :
    let factorsℚ := List.zipWith (fun (q : ℕ) f =>
      scaleFactor ((q : ℚ)⁻¹) (mapFactorHom (Int.castRingHom ℚ) f)) denoms factorsℤ
    let res : ℚ := (eliminateOrder d order (ElimState.ofFactors factorsℚ declared)).result
    res.num.natAbs ≤ d ^ order.length * W ^ factorsℤ.length ∧
      res.den ≤ D ^ factorsℤ.length := by
  dsimp only
  let z : ℤ := (eliminateOrder d order (ElimState.ofFactors factorsℤ declared)).result
  let P : ℕ := denoms.prod
  have hres :
      (eliminateOrder d order (ElimState.ofFactors (List.zipWith (fun (q : ℕ) f =>
        scaleFactor ((q : ℚ)⁻¹) (mapFactorHom (Int.castRingHom ℚ) f)) denoms factorsℤ)
        declared)).result = (z : ℚ) / (P : ℚ) :=
    result_eliminateOrder_ratScaled d denoms factorsℤ declared order hlen hcover
  rw [hres]
  have hPpos : 0 < P := by
    by_contra h0
    have hPe : P = 0 := by omega
    exact Nat.lt_irrefl 0 (hDpos 0 (List.prod_eq_zero_iff.mp hPe))
  have hPle : P ≤ D ^ factorsℤ.length := by
    rw [← hlen]
    clear hlen hWle hcover hPpos z hres
    induction denoms with
    | nil => simp [P]
    | cons q qs ih =>
        have hqs := ih (fun r hr => hDpos r (by simp [hr])) (fun r hr => hDle r (by simp [hr]))
        have hq := hDle q (by simp)
        simpa [P, pow_succ'] using Nat.mul_le_mul hq hqs
  have hmk : (z : ℚ) / (P : ℚ) = Rat.divInt z P := by
    rw [← Int.cast_natCast P, ← Rat.divInt_eq_div]
  rw [hmk]
  refine ⟨le_trans (natAbs_num_divInt_le z hPpos)
      (natAbs_result_eliminateOrder_le hd hW factorsℤ declared order hWle),
    le_trans (den_divInt_le z hPpos) hPle⟩

/-- Under cleared denominators, the `encRat` bit length of the final contraction result is linear
in `order.length` and `factorsℤ.length`. -/
theorem length_encRat_cleared_result_le {V : Type*} [DecidableEq V] {d W D : ℕ}
    (hd : 0 < d) (hW : 0 < W) (hD : 0 < D)
    (denoms : List ℕ) (factorsℤ : List (FactorTable ℤ V)) (declared order : List V)
    (hlen : denoms.length = factorsℤ.length)
    (hDpos : ∀ q ∈ denoms, 0 < q)
    (hDle : ∀ q ∈ denoms, q ≤ D)
    (hWle : ∀ f ∈ factorsℤ, ∀ z ∈ f.entries.toList, z.natAbs ≤ W)
    (hcover : declared.toFinset ⊆ order.toFinset) :
    let factorsℚ := List.zipWith (fun (q : ℕ) f =>
      scaleFactor ((q : ℚ)⁻¹) (mapFactorHom (Int.castRingHom ℚ) f)) denoms factorsℤ
    let res : ℚ := (eliminateOrder d order (ElimState.ofFactors factorsℚ declared)).result
    (encRat res).length ≤
      2 * (order.length * d.size + factorsℤ.length * W.size) + factorsℤ.length * D.size + 8 := by
  dsimp only
  rcases rat_cleared_result_bounds hd hW hD denoms factorsℤ declared order hlen hDpos hDle hWle
      hcover with ⟨hnum, hden⟩
  have hr :
      (encRat (eliminateOrder d order (ElimState.ofFactors
        (List.zipWith (fun (q : ℕ) f =>
          scaleFactor ((q : ℚ)⁻¹) (mapFactorHom (Int.castRingHom ℚ) f)) denoms factorsℤ)
        declared)).result).length ≤
      2 * (d ^ order.length * W ^ factorsℤ.length).size + (D ^ factorsℤ.length).size + 3 :=
    length_encRat_le _ hnum hden
  have h1 : (d ^ order.length * W ^ factorsℤ.length).size ≤
      order.length * d.size + factorsℤ.length * W.size + 2 :=
    le_trans (natSize_mul_le _ _)
      (by
        have ha := natSize_pow_le d order.length
        have hb := natSize_pow_le W factorsℤ.length
        omega)
  have h2 : (D ^ factorsℤ.length).size ≤ factorsℤ.length * D.size + 1 := natSize_pow_le D _
  omega

end RationalCost

/-! ### Documented encoded factor-table records (`enc_structure`) -/

section EncodedRecords

/-- Explicit natural-number factor table record with list-backed entries for multi-tape
encodings. -/
structure NatFactorRecord where
  /-- Ordered scope variable indices. -/
  scope : List ℕ
  /-- Table entries in LSB base-`d` order. -/
  entries : List ℕ
  deriving DecidableEq, Repr

/-- Explicit integer factor table record using sign-magnitude binary weights (`encIntBin`). -/
structure IntFactorRecord where
  /-- Ordered scope variable indices. -/
  scope : List ℕ
  /-- Integer table entries in LSB base-`d` order. -/
  entries : List ℤ
  deriving DecidableEq, Repr

/-- Explicit rational factor table record using reduced rational encodings (`encRat`). -/
structure RatFactorRecord where
  /-- Ordered scope variable indices. -/
  scope : List ℕ
  /-- Rational table entries in LSB base-`d` order. -/
  entries : List ℚ
  deriving DecidableEq, Repr

/-- Explicit modular factor table record over `ZMod modulus` with binary residue entries. -/
structure ModFactorRecord where
  /-- Modulus `p` (positive for `ZMod p`). -/
  modulus : ℕ
  /-- Ordered scope variable indices. -/
  scope : List ℕ
  /-- Residue table entries in LSB base-`d` order. -/
  entries : List ℕ
  deriving DecidableEq, Repr

enc_structure encNatFactorRecord : NatFactorRecord where
  scope : (encList encNat), entries : (encList encNat)

enc_structure encIntFactorRecord : IntFactorRecord where
  scope : (encList encNat), entries : (encList encIntBin)

enc_structure encRatFactorRecord : RatFactorRecord where
  scope : (encList encNat), entries : (encList encRat)

enc_structure encModFactorRecord : ModFactorRecord where
  modulus : encNat, scope : (encList encNat), entries : (encList encNat)

/-- Convert a `NatFactorRecord` into a `FactorTable ℕ ℕ`. -/
@[expose] def NatFactorRecord.toFactorTable (rec : NatFactorRecord) : FactorTable ℕ ℕ :=
  { scope := rec.scope, entries := rec.entries.toArray }

/-- Convert an `IntFactorRecord` into a `FactorTable ℤ ℕ`. -/
@[expose] def IntFactorRecord.toFactorTable (rec : IntFactorRecord) : FactorTable ℤ ℕ :=
  { scope := rec.scope, entries := rec.entries.toArray }

/-- Convert a `RatFactorRecord` into a `FactorTable ℚ ℕ`. -/
@[expose] def RatFactorRecord.toFactorTable (rec : RatFactorRecord) : FactorTable ℚ ℕ :=
  { scope := rec.scope, entries := rec.entries.toArray }

/-- Convert a `ModFactorRecord` into a `FactorTable (ZMod rec.modulus) ℕ`. -/
@[expose] def ModFactorRecord.toFactorTable (rec : ModFactorRecord) :
    FactorTable (ZMod rec.modulus) ℕ :=
  { scope := rec.scope, entries := (rec.entries.map fun k : ℕ => (k : ZMod rec.modulus)).toArray }

private theorem length_encList_nat_le (l : List ℕ) {B : ℕ} (h : ∀ x ∈ l, x.size ≤ B) :
    (encList encNat l).length ≤ l.length * (2 * B + 1) := by
  rw [length_encList]
  simp only [length_encNat_eq]
  revert h
  induction l with
  | nil => intro _; simp
  | cons v vs ih =>
      intro h
      have hv0 : v.size ≤ B := h v (by simp)
      have hvs := ih fun u hu => h u (by simp [hu])
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- Encoded bit length of an `IntFactorRecord` bounded by variable and entry bit lengths. -/
theorem length_encIntFactorRecord_le (rec : IntFactorRecord) {VBits WBits : ℕ}
    (hv : ∀ v ∈ rec.scope, v.size ≤ VBits)
    (hw : ∀ z ∈ rec.entries, z.natAbs.size + 1 ≤ WBits) :
    (encIntFactorRecord rec).length ≤
      2 * (rec.scope.length * (2 * VBits + 1)) + 1 + rec.entries.length * (2 * WBits + 1) := by
  rw [encIntFactorRecord_apply, length_encPair]
  dsimp only
  have hs := length_encList_nat_le rec.scope hv
  have he : (encList encIntBin rec.entries).length ≤ rec.entries.length * (2 * WBits + 1) := by
    rw [length_encList]
    simp only [length_encIntBin]
    clear hs hv
    revert hw
    induction rec.entries with
    | nil => intro _; simp
    | cons z zs ih =>
        intro hw
        have hz0 : z.natAbs.size + 1 ≤ WBits := hw z (by simp)
        have hzs := ih fun y hy => hw y (by simp [hy])
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
        omega
  omega

/-- Encoded bit length of a `RatFactorRecord` bounded by scope variable and `encRat` entry
lengths. -/
theorem length_encRatFactorRecord_le (rec : RatFactorRecord) {VBits RBits : ℕ}
    (hv : ∀ v ∈ rec.scope, v.size ≤ VBits)
    (hq : ∀ q ∈ rec.entries, (encRat q).length ≤ RBits) :
    (encRatFactorRecord rec).length ≤
      2 * (rec.scope.length * (2 * VBits + 1)) + 1 + rec.entries.length * (2 * RBits + 1) := by
  rw [encRatFactorRecord_apply, length_encPair]
  dsimp only
  have hs := length_encList_nat_le rec.scope hv
  have he : (encList encRat rec.entries).length ≤ rec.entries.length * (2 * RBits + 1) := by
    rw [length_encList]
    clear hs hv
    revert hq
    induction rec.entries with
    | nil => intro _; simp
    | cons q qs ih =>
        intro hq
        have hq0 := hq q (by simp)
        have hqs := ih fun y hy => hq y (by simp [hy])
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
        omega
  omega

/-- Encoded bit length of a `ModFactorRecord` bounded by modulus, scope variable, and residue bit
lengths. -/
theorem length_encModFactorRecord_le (rec : ModFactorRecord) {VBits : ℕ}
    (hv : ∀ v ∈ rec.scope, v.size ≤ VBits)
    (hw : ∀ k ∈ rec.entries, k < rec.modulus) :
    (encModFactorRecord rec).length ≤
      2 * rec.modulus.size + 1 + 2 * (rec.scope.length * (2 * VBits + 1)) + 1 +
        rec.entries.length * (2 * rec.modulus.size + 1) := by
  rw [encModFactorRecord_apply, length_encPair, length_encPair]
  dsimp only
  have hs := length_encList_nat_le rec.scope hv
  have he := length_encList_nat_le rec.entries fun k hk =>
    Nat.size_le_size (Nat.le_of_lt (hw k hk))
  rw [length_encNat_eq]
  omega

end EncodedRecords

end Cslib.Algorithms.Lean.CSP
