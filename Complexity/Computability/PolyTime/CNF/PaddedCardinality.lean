/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.PolyTime.CNF.CardinalityInterval
import all Complexity.Computability.PolyTime.CNF.IndependentDominationInterval

/-!
# Uniform functional cardinality blocks

The actual interval circuit uses at most 952(v+1) gates. Force unused slots to zero so independent
class tests share a uniform linear block layout without adding choices. Bounds remain binary and
are normalized by the existing generator. This is an implementation refinement for
[ChenJiangZhu2027], Theorem 7.3 / Appendix C.2 (PDF pp.25,32).
## Main results

* `formula_polytime`: actual binary circuit and padding writes.
* `eval_iff`: unique padded trace and exact original-input interval semantics.
* `bounds`: actual allocated indices, widths and linear clause volume.

-/

public section

namespace Cslib.Logic.PL.PaddedCardinality

open Turing.MultiTapeTM Cslib.Circuits.Boolean

/-- Linear gate allocation, including explicit functional zero padding. -/
@[expose] def capacity (n : ℕ) : ℕ := 952 * (n + 1)
/-- Count actual generated gates, not a supplied circuit-size budget. -/
@[expose] def used (x : CardinalityInterval.Input) : ℕ := (CardinalityInterval.generate x).1.length
/-- Explicit unit clauses uniquely determine all unused slots. -/
@[expose] def padding (x : CardinalityInterval.Input) : CNF ℕ :=
  let n := CardinalityInterval.declared x
  let gates := used x
  ((List.range (capacity n)).filter fun j => decide (gates ≤ j)).map fun j => [(n + j, false)]
/-- Actual functional size-test formula, including every allocated gate slot. -/
@[expose] def formula (x : CardinalityInterval.Input) : CNF ℕ :=
  CardinalityInterval.formula x ++ padding x
/-- Compute the full padded trace from the original selection word. -/
@[expose] def values {n : ℕ} (lo hi : ℕ) (x : Fin n → Bool) : Fin (n + capacity n) → Bool :=
  fun j => if h : j.val < n + (CardinalityInterval.circuit n lo hi).size then
    FunctionalCNF.wireValues (CardinalityInterval.circuit n lo hi) x ⟨j.val, h⟩ else false

private theorem used_polytime : ComputableInPolyTime used CardinalityInterval.encInput encUnary :=
  ((ComputableInPolyTime.length_list encGate).comp
    CardinalityInterval.generate_polytime.fst').of_enc_eq fun _ => rfl

/-- Binary writing of the actual circuit and every padding unit. -/
@[fun_prop] theorem formula_polytime : ComputableInPolyTime formula CardinalityInterval.encInput
    (encList (encList (encPair encNat encBool))) := by
  have hn : ComputableInPolyTime CardinalityInterval.declared CardinalityInterval.encInput
      encUnary := by unfold CardinalityInterval.declared CardinalityInterval.encInput; fun_prop
  have ha : ComputableInPolyTime (fun x => capacity (CardinalityInterval.declared x))
      CardinalityInterval.encInput encUnary := by unfold capacity; fun_prop
  have hpad : ComputableInPolyTime padding CardinalityInterval.encInput
      (encList (encList (encPair encNat encBool))) := by
    unfold padding
    have ht : ComputableInPolyTime (fun p : CardinalityInterval.Input × ℕ =>
        decide (used p.1 ≤ p.2)) (encPair CardinalityInterval.encInput encUnary) encBool := by
      have hl := used_polytime.comp (ComputableInPolyTime.fst CardinalityInterval.encInput encUnary)
      exact ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.unary_le.comp
        (hl.prod (ComputableInPolyTime.snd _ _)).tidy)
    have hf := ComputableInPolyTime.filterWithInput
      (test := fun x j => decide (used x ≤ j)) (ComputableInPolyTime.range.comp ha) ht
    have hu : ComputableInPolyTime (fun p : CardinalityInterval.Input × ℕ =>
        CardinalityInterval.declared p.1 + p.2) (encPair CardinalityInterval.encInput encUnary)
        encNat := ComputableInPolyTime.unary_to_binary.comp (by
      have h := hn.comp (ComputableInPolyTime.fst CardinalityInterval.encInput encUnary)
      fun_prop)
    have hw : ComputableInPolyTime (fun p : CardinalityInterval.Input × ℕ =>
        [(CardinalityInterval.declared p.1 + p.2, false)])
        (encPair CardinalityInterval.encInput encUnary) (encList (encPair encNat encBool)) :=
      ComputableInPolyTime.cons' (hu.prod (.const false)) (.const [])
    have hm := ComputableInPolyTime.mapWithInput
      (f := fun x j => [(CardinalityInterval.declared x + j, false)]) hf hw
    simpa only [Function.comp_def] using hm
  exact ComputableInPolyTime.listAppend' CardinalityInterval.formula_polytime hpad

/-- Padding preserves the original input bits exactly. -/
theorem values_input {n : ℕ} (lo hi : ℕ) (x : Fin n → Bool) (i : Fin n) :
    values lo hi x (Fin.castAdd (capacity n) i) = x i := by
  unfold values
  rw [dite_eq_left (by simp only [Fin.val_castAdd]; have := i.isLt; omega)]
  exact FunctionalCNF.wireValues_input _ _ i

/-- The generated code's gate count is the actual circuit size. -/
theorem used_eq (n lo hi : ℕ) : used (n, lo, hi) = (CardinalityInterval.circuit n lo hi).size := by
  simp only [used, CardinalityInterval.generate_eq]
  exact Cslib.Circuits.Circuit.length_code_fst _

/-- Every allocated bit is uniquely derived and the actual inclusive bounds hold. -/
theorem eval_iff {n : ℕ} (lo hi : ℕ) (x : Fin n → Bool)
    (y : Fin (n + capacity n) → Bool)
    (hin : ∀ i, y (Fin.castAdd (capacity n) i) = x i) :
    (formula (n, lo, hi)).eval (Function.extend Fin.val y (fun _ => false)) = true ↔
      y = values lo hi x ∧ lo ≤ Cslib.BitString.weight x ∧ Cslib.BitString.weight x ≤ hi := by
  let c := CardinalityInterval.circuit n lo hi
  let σ := Function.extend Fin.val y (fun _ => false)
  have hs : c.size ≤ capacity n := CardinalityInterval.size_circuit n lo hi
  have hy (i : Fin (n + capacity n)) : σ i.val = y i :=
    Fin.val_injective.extend_apply _ _ _
  have hf := FunctionalCNF.eval_write_iff c CardinalityInterval.wanted x σ
    (fun i => (hy (Fin.castAdd (capacity n) i)).trans (hin i))
  have hp : (padding (n, lo, hi)).eval σ = true ↔
      ∀ j : Fin (capacity n), c.size ≤ j.val → y (Fin.natAdd n j) = false := by
    simp only [padding, CNF.eval_eq_true_iff, List.forall_mem_map, List.mem_filter,
      List.mem_range, decide_eq_true_eq, and_imp, CardinalityInterval.declared, used_eq,
      Clause.eval_eq_true_iff, List.mem_singleton, exists_eq_left]
    constructor
    · intro h j hj
      exact (hy (Fin.natAdd n j)).symm.trans (h j.val j.isLt hj)
    · intro h j hj hg
      exact (hy (Fin.natAdd n ⟨j, hj⟩)).trans (h ⟨j, hj⟩ hg)
  have hF : (CardinalityInterval.formula (n, lo, hi)).eval σ = true ↔
      (∀ j : Fin (n + c.size), y ⟨j.val, by omega⟩ = FunctionalCNF.wireValues c x j) ∧
        lo ≤ Cslib.BitString.weight x ∧ Cslib.BitString.weight x ≤ hi := by
    change (FunctionalCNF.write (CardinalityInterval.payload (n, lo, hi))).eval σ = true ↔ _
    rw [CardinalityInterval.payload_eq]
    change (FunctionalCNF.write (FunctionalCNF.ofCircuit c CardinalityInterval.wanted)).eval σ =
      true ↔ _
    rw [hf, CardinalityInterval.circuit_accepts]
    apply and_congr
    · apply forall_congr'
      intro j
      rw [hy ⟨j.val, by omega⟩]
    · rfl
  change ((CardinalityInterval.formula (n, lo, hi)) ++ padding (n, lo, hi)).eval σ = true ↔ _
  rw [CNF.eval_append, Bool.and_eq_true, hF, hp]
  constructor
  · rintro ⟨⟨ht, hb⟩, hpad⟩
    refine ⟨?_, hb⟩
    funext j
    unfold values
    split_ifs with hj
    · exact ht ⟨j.val, hj⟩
    · have hn : n ≤ j.val := by omega
      have hjA : j.val - n < capacity n := by have := j.isLt; omega
      have he : Fin.natAdd n ⟨j.val - n, hjA⟩ = j := Fin.ext (by simp; omega)
      apply he ▸ hpad ⟨j.val - n, hjA⟩
      change c.size ≤ j.val - n
      change ¬ j.val < n + c.size at hj
      omega
  · rintro ⟨he, hb⟩
    refine ⟨⟨?_, hb⟩, ?_⟩
    · intro j
      rw [he]
      unfold values
      exact dite_eq_left j.isLt
    · intro j hj
      rw [he]
      unfold values
      apply dite_eq_right
      simp only [Fin.val_natAdd]
      change (CardinalityInterval.circuit n lo hi).size ≤ j.val at hj
      omega

/-- Actual allocated variables, widths, indices and linear clause volume. -/
theorem bounds (n lo hi : ℕ) :
    (formula (n, lo, hi)).length ≤ 2 + 2856 * (n + 1) + capacity n ∧
      ∀ c ∈ formula (n, lo, hi), c.length ≤ 3 ∧ ∀ l ∈ c, l.1 < n + capacity n := by
  have hs : (CardinalityInterval.circuit n lo hi).size ≤ capacity n :=
    CardinalityInterval.size_circuit n lo hi
  obtain ⟨hl, hb⟩ := CardinalityInterval.formula_bounds n lo hi
  constructor
  · have hp : (padding (n, lo, hi)).length ≤ capacity n := by
      simpa only [padding, List.length_map, CardinalityInterval.declared, List.length_range] using
        (List.length_filter_le _ (List.range (capacity n)))
    simp only [formula, List.length_append]
    omega
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact ⟨(hb c hc).1.le, fun l hl => ((hb c hc).2 l hl).trans_le (by omega)⟩
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
      refine ⟨by simp, ?_⟩
      intro l hl
      have he := List.mem_singleton.mp hl
      subst l
      have hlt := List.mem_range.mp (List.mem_filter.mp hj).1
      exact Nat.add_lt_add_left hlt n

end Cslib.Logic.PL.PaddedCardinality
