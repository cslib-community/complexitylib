/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.Classes.NP
public import Complexity.Computability.Complexity.Reduction.TruthTableVariants
import Complexity.Computability.Complexity.Classes.NP.Witness
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Closure of NP and coNP under truth-table reduction variants

`NP` is closed under polynomial-time disjunctive truth-table reductions
(`Cslib.Complexity.PolyTimeDTTReducible.mem_NP`): an `NP` witness for the disjunctive reduction
consists of an index `i < r a` and a witness `w` for the queried instance `q (a, i)`.

By duality (`Cslib.Complexity.polyTimeDTTReducible_iff_polyTimeCTTReducible_compl`), `coNP` is
closed under polynomial-time conjunctive truth-table reductions
(`Cslib.Complexity.PolyTimeCTTReducible.mem_coNP`).

Under the hypothesis that `NP = coNP`, each class is also closed under the dual reduction.

## Main results

* `Cslib.Complexity.PolyTimeDTTReducible.mem_NP`: `NP` is closed under disjunctive truth-table
  reductions.
* `Cslib.Complexity.PolyTimeCTTReducible.mem_coNP`: `coNP` is closed under conjunctive truth-table
  reductions.
* `Cslib.Complexity.PolyTimeCTTReducible.mem_NP_of_NP_eq_coNP`: under `NP = coNP`, `NP` is closed
  under conjunctive truth-table reductions.
* `Cslib.Complexity.PolyTimeDTTReducible.mem_coNP_of_NP_eq_coNP`: under `NP = coNP`, `coNP` is
  closed under disjunctive truth-table reductions.

## References

* [R. E. Ladner, N. A. Lynch, A. L. Selman, *A comparison of polynomial time
  reducibilities*][LadnerLynchSelman1975]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [C. H. Papadimitriou, *Computational Complexity*][Papadimitriou94]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}

private theorem computableInPolyTime_check_dtt
    {r : α → ℕ} {q : α × ℕ → β}
    (hr : ComputableInPolyTime r encA encUnary)
    (hq : ComputableInPolyTime q (encPair encA encUnary) encB)
    (pB : Polynomial ℕ)
    (VB : β × List Bool → Bool)
    (hVB : ComputableInPolyTime VB (encPair encB encBits) encBool) :
    ComputableInPolyTime
      (fun p : α × (ℕ × List Bool) =>
        decide (p.2.1 < r p.1) &&
        (decide (p.2.2.length = pB.eval (encB (q (p.1, p.2.1))).length) &&
        VB (q (p.1, p.2.1), p.2.2)))
      (encPair encA (encPair encUnary encBits)) encBool := by
  have ha : ComputableTidilyInPolyTime (fun p : α × (ℕ × List Bool) => p.1)
      (encPair encA (encPair encUnary encBits)) encA :=
    ComputableTidilyInPolyTime.fst encA (encPair encUnary encBits)
  have hp2 : ComputableTidilyInPolyTime (fun p : α × (ℕ × List Bool) => p.2)
      (encPair encA (encPair encUnary encBits)) (encPair encUnary encBits) :=
    ComputableTidilyInPolyTime.snd encA (encPair encUnary encBits)
  have hi : ComputableTidilyInPolyTime (fun p : α × (ℕ × List Bool) => p.2.1)
      (encPair encA (encPair encUnary encBits)) encUnary :=
    (ComputableTidilyInPolyTime.fst encUnary encBits).comp hp2
  have hw : ComputableTidilyInPolyTime (fun p : α × (ℕ × List Bool) => p.2.2)
      (encPair encA (encPair encUnary encBits)) encBits :=
    (ComputableTidilyInPolyTime.snd encUnary encBits).comp hp2
  have hai : ComputableTidilyInPolyTime (fun p : α × (ℕ × List Bool) => (p.1, p.2.1))
      (encPair encA (encPair encUnary encBits)) (encPair encA encUnary) :=
    ha.prod hi
  have h_cond1 : ComputableTidilyInPolyTime (fun p : α × (ℕ × List Bool) => decide (p.2.1 < r p.1))
      (encPair encA (encPair encUnary encBits)) encBool :=
    ComputableTidilyInPolyTime.unary_lt.comp (hi.prod (hr.tidy.comp ha))
  have hq_eval : ComputableTidilyInPolyTime (fun p : α × (ℕ × List Bool) => q (p.1, p.2.1))
      (encPair encA (encPair encUnary encBits)) encB :=
    hq.tidy.comp hai
  have hw_len : ComputableTidilyInPolyTime (fun p : α × (ℕ × List Bool) => p.2.2.length)
      (encPair encA (encPair encUnary encBits)) encUnary :=
    ComputableTidilyInPolyTime.length_bits.comp hw
  have htarget_len : ComputableTidilyInPolyTime
      (fun p : α × (ℕ × List Bool) => pB.eval (encB (q (p.1, p.2.1))).length)
      (encPair encA (encPair encUnary encBits)) encUnary :=
    (ComputableTidilyInPolyTime.unary_eval pB).comp
      ((ComputableTidilyInPolyTime.encoding_length encB).comp hq_eval)
  have h_cond2 : ComputableTidilyInPolyTime
      (fun p : α × (ℕ × List Bool) =>
        decide (p.2.2.length = pB.eval (encB (q (p.1, p.2.1))).length))
      (encPair encA (encPair encUnary encBits)) encBool :=
    (ComputableTidilyInPolyTime.decide_eq encUnary).comp (hw_len.prod htarget_len)
  have h_cond3 : ComputableTidilyInPolyTime
      (fun p : α × (ℕ × List Bool) => VB (q (p.1, p.2.1), p.2.2))
      (encPair encA (encPair encUnary encBits)) encBool :=
    hVB.tidy.comp (hq_eval.prod hw)
  exact .of_tidy (ComputableTidilyInPolyTime.bool_and' h_cond1
    (ComputableTidilyInPolyTime.bool_and' h_cond2 h_cond3))

/-- **NP is closed under polynomial-time disjunctive truth-table reductions.** -/
theorem PolyTimeDTTReducible.mem_NP {L : Set α} {B : Set β}
    (h : PolyTimeDTTReducible encA encB L B) (hB : B ∈ NP encB) :
    L ∈ NP encA := by
  obtain ⟨r, q, hr, hq, hL⟩ := h
  obtain ⟨pB, VB, hVB, hVspec⟩ := hB
  let R : α → (ℕ × List Bool) → Prop := fun a p =>
    p.1 < r a ∧ p.2.length = pB.eval (encB (q (a, p.1))).length ∧ VB (q (a, p.1), p.2) = true
  let check : α × (ℕ × List Bool) → Bool := fun p =>
    decide (p.2.1 < r p.1) &&
    (decide (p.2.2.length = pB.eval (encB (q (p.1, p.2.1))).length) &&
    VB (q (p.1, p.2.1), p.2.2))
  have hcheck : ComputableInPolyTime check (encPair encA (encPair encUnary encBits)) encBool :=
    computableInPolyTime_check_dtt hr hq pB VB hVB
  have hR : ∀ a b, check (a, b) = true ↔ R a b := by
    intro a ⟨i, w⟩
    simp [check, R, Bool.and_eq_true]
  let r' : β → ℕ := fun b => pB.eval (encB b).length
  have hr' : ComputableInPolyTime r' encB encUnary := by
    exact (ComputableInPolyTime.unary_eval pB).comp (ComputableInPolyTime.encoding_length encB)
  let bound : α → ℕ := fun a =>
    2 * r a + 1 + ((List.range (r a)).flatMap fun i => List.range (r' (q (a, i)))).length
  have hbound : ComputableInPolyTime bound encA encUnary := by
    dsimp only [bound]
    have hsum : ComputableInPolyTime
        (fun a => ((List.range (r a)).flatMap fun i => List.range (r' (q (a, i)))).length)
        encA encUnary := by
      fun_prop
    fun_prop
  obtain ⟨p, hp⟩ := hbound.polyBounded.exists_polynomial
  have hmem : {a | ∃ b, R a b} ∈ NP encA := by
    refine mem_NP_of_witness (p := p) (Decoder.pair Decoder.unary Decoder.bits)
      hcheck hR (fun a b hb => ?_)
    refine ⟨b, hb, ?_⟩
    obtain ⟨i, w⟩ := b
    dsimp [R] at hb
    obtain ⟨hi, hwlen, -⟩ := hb
    have hlen_enc : (encPair encUnary encBits (i, w)).length = 2 * i + 1 + w.length := by
      simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply]
    rw [hlen_enc]
    have hsum : r' (q (a, i)) ≤
        ((List.range (r a)).flatMap fun j => List.range (r' (q (a, j)))).length := by
      simp only [List.length_flatMap, List.length_range]
      exact List.le_sum_of_mem (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    have hle_bound : 2 * i + 1 + w.length ≤ bound a := by
      dsimp [bound, r'] at hsum ⊢
      rw [hwlen]
      omega
    exact hle_bound.trans (hp a)
  have heq : {a | ∃ b, R a b} = L := by
    ext a
    simp only [Set.mem_ofPred_eq, hL a]
    constructor
    · rintro ⟨⟨i, w⟩, hi, hwlen, hwV⟩
      refine ⟨i, hi, ?_⟩
      rw [hVspec (q (a, i))]
      exact ⟨w, hwlen, hwV⟩
    · rintro ⟨i, hi, hqB⟩
      rw [hVspec (q (a, i))] at hqB
      obtain ⟨w, hwlen, hwV⟩ := hqB
      exact ⟨(i, w), hi, hwlen, hwV⟩
  rwa [heq] at hmem

/-- **coNP is closed under polynomial-time conjunctive truth-table reductions.** -/
theorem PolyTimeCTTReducible.mem_coNP {L : Set α} {B : Set β}
    (h : PolyTimeCTTReducible encA encB L B) (hB : B ∈ coNP encB) :
    L ∈ coNP encA := by
  change Lᶜ ∈ NP encA
  change Bᶜ ∈ NP encB at hB
  have h_dual := polyTimeDTTReducible_iff_polyTimeCTTReducible_compl
    (encA := encA) (encB := encB) (L := Lᶜ) (B := Bᶜ)
  rw [compl_compl, compl_compl] at h_dual
  have hdtt : PolyTimeDTTReducible encA encB Lᶜ Bᶜ := h_dual.mpr h
  exact hdtt.mem_NP hB

/-- Under `NP = coNP`, `NP` is closed under polynomial-time conjunctive truth-table reductions. -/
theorem PolyTimeCTTReducible.mem_NP_of_NP_eq_coNP
    (hNP : ∀ {γ : Type} (encC : γ ↪ List Bool), NP encC = coNP encC)
    {L : Set α} {B : Set β} (h : PolyTimeCTTReducible encA encB L B) (hB : B ∈ NP encB) :
    L ∈ NP encA := by
  have hBco : B ∈ coNP encB := by
    rw [← hNP encB]
    exact hB
  have hLco : L ∈ coNP encA := h.mem_coNP hBco
  rwa [← hNP encA] at hLco

/-- Under `NP = coNP`, `coNP` is closed under polynomial-time disjunctive truth-table reductions. -/
theorem PolyTimeDTTReducible.mem_coNP_of_NP_eq_coNP
    (hNP : ∀ {γ : Type} (encC : γ ↪ List Bool), NP encC = coNP encC)
    {L : Set α} {B : Set β} (h : PolyTimeDTTReducible encA encB L B) (hB : B ∈ coNP encB) :
    L ∈ coNP encA := by
  have hBNP : B ∈ NP encB := by
    rw [hNP encB]
    exact hB
  have hLNP : L ∈ NP encA := h.mem_NP hBNP
  rwa [hNP encA] at hLNP

end Cslib.Complexity
