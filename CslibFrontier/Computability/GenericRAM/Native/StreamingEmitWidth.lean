/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.GenericRAM.Native.StreamingEmitBounds
import all CslibFrontier.Computability.GenericRAM.Native.StreamingEmitBounds
import all CslibFrontier.Computability.GenericRAM.Native.StreamingEmit
import all CslibFrontier.Computability.GenericRAM.Native.StreamingFoldBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Per-width bounds for small-state record writers

The actual emitter certificate is reused unchanged. Polynomial callbacks receive
one state and one record. Derived state/record wire bounds and input/output wire
bounds therefore give a linear record-count factor, without a polynomial in an
entire list or a sum of callback workspaces used as peak space.

## Main results

* `emitFold_width`: derived per-width bit time and every-prefix workspace.
-/

public section
namespace Cslib.GenericRAM.NativeCertificate
open Turing.MultiTapeTM

/-- Normalize the installed emitter from physical prefix widths. The hypotheses concern
encoded values, not desired callback running times or a missing implementation. -/
theorem emitFold_width {σ α β : Type} (es : σ ↪ List Bool) (ea : α ↪ List Bool)
    (eb : β ↪ List Bool) (next : σ → α → σ) (emit : σ → α → List β)
    (hn : ComputableInPolyTime (fun q => next q.1 q.2) (encPair es ea) es)
    (he : ComputableInPolyTime (fun q => emit q.1 q.2) (encPair es ea) (encList eb))
    (B : σ × List α → ℕ) (V : ℕ → ℕ) (hv : Cslib.PolynomiallyBounded V) (mv : Monotone V)
    (state : ∀ input j, j ≤ input.2.length →
      (es (streamState input.1 (fun q => next q.1 q.2) input.2 j)).length ≤ B input)
    (record : ∀ input row, row ∈ input.2 → (ea row).length ≤ B input)
    (inputWire : ∀ input, (encPair es (encList ea) input).length ≤
      (input.2.length + 1) * V (B input))
    (outputWire : ∀ input, (encList eb (emitFold next emit input.1 input.2)).length ≤
      (input.2.length + 1) * V (B input)) :
    ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
      ComputableInO (fun input => emitFold next emit input.1 input.2)
        (encPair es (encList ea)) (encList eb)
        (fun input => (input.2.length + 1) * P (B input))
        (fun input => (input.2.length + 1) * P (B input)) := by
  let nm := NativeCertificate.ofPolyTime hn
  let em := NativeCertificate.ofPolyTime he
  obtain ⟨N, hpN, mN, hN⟩ := exists_mono_poly
    ((NativeCertificate.ofPolyTime_isPolynomial hn).1.add
      (NativeCertificate.ofPolyTime_isPolynomial hn).2)
  obtain ⟨E, hpE, mE, hE⟩ := exists_mono_poly
    ((NativeCertificate.ofPolyTime_isPolynomial he).1.add
      (NativeCertificate.ofPolyTime_isPolynomial he).2)
  let machine := emitFoldCertificate es ea eb next emit nm em
  obtain ⟨K, bound⟩ := emitFoldCertificate_bounds es ea eb next emit nm em
  let Q := fun b => 2*V b+N (3*b+1)+E (3*b+1)+10*b+10
  let P := fun b => (K+1)*Q b
  have hp : Cslib.PolynomiallyBounded P := by dsimp only [P, Q]; fun_prop
  have mp : Monotone P := by
    intro a b hab
    have := mv hab
    have := mN (by omega : 3*a+1 ≤ 3*b+1)
    have := mE (by omega : 3*a+1 ≤ 3*b+1)
    apply Nat.mul_le_mul_left
    dsimp only [Q]
    omega
  have budgets (input : σ × List α) :
      emitTimeBudget es ea eb next emit nm em input ≤ (input.2.length + 1) * Q (B input) ∧
      emitSpaceBudget es ea eb next emit nm em input ≤ (input.2.length + 1) * Q (B input) := by
    let b := B input
    let st := fun j => streamState input.1 (fun q => next q.1 q.2) input.2 j
    have sw : foldStateWidth es (fun (_ : Unit) => next) ((), input) ≤ b := by
      apply Finset.sup_le
      intro j hj
      exact state input j (by have := Finset.mem_range.mp hj; omega)
    have rw : streamRecordLength ea input.2 ≤ b := listMax_le (record input)
    have cb (j : ℕ) (hj : j < input.2.length) :
        nm.time (st j, input.2[j])+nm.space (st j, input.2[j])+
        em.time (st j, input.2[j])+em.space (st j, input.2[j]) ≤ N (3*b+1)+E (3*b+1) := by
      have wire : (encPair es ea (st j, input.2[j])).length ≤ 3*b+1 := by
        have hs := state input j hj.le
        have hr := record input input.2[j] (List.getElem_mem hj)
        rw [length_encPair]
        dsimp only [st, b]
        omega
      have n := (hN _).trans (mN wire)
      have e := (hE _).trans (mE wire)
      change nm.time _+nm.space _ ≤ _ at n
      change em.time _+em.space _ ≤ _ at e
      omega
    have sums : (∑ j ∈ Finset.range input.2.length, if h : j < input.2.length then
        nm.time (st j, input.2[j])+em.time (st j, input.2[j])+(ea input.2[j]).length else 0) ≤
        input.2.length*(N (3*b+1)+E (3*b+1)+b) := by
      have h := Finset.sum_le_sum (s := Finset.range input.2.length)
        (f := fun j => if h : j < input.2.length then
          nm.time (st j, input.2[j])+em.time (st j, input.2[j])+(ea input.2[j]).length else 0)
        (g := fun _ => N (3*b+1)+E (3*b+1)+b) (fun j hj => by
          have hj' := Finset.mem_range.mp hj
          rw [dite_eq_left hj']
          have := cb j hj'
          have := record input input.2[j] (List.getElem_mem hj')
          omega)
      simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id] using h
    have spaces : (Finset.range input.2.length).sup (fun j => if h : j < input.2.length then
        nm.space (st j, input.2[j])+em.space (st j, input.2[j]) else 0) ≤ N (3*b+1)+E (3*b+1) := by
      apply Finset.sup_le
      intro j hj
      rw [dite_eq_left (Finset.mem_range.mp hj)]
      have := cb j (Finset.mem_range.mp hj)
      omega
    have copies := Nat.mul_le_mul_left (input.2.length+1) sw
    have hi := inputWire input
    have ho := outputWire input
    have nonneg := Nat.zero_le (input.2.length*(N (3*b+1)+E (3*b+1)))
    constructor
    · dsimp only [emitTimeBudget, Q]
      change _ ≤ (input.2.length + 1) * (2*V b+N (3*b+1)+E (3*b+1)+10*b+10)
      nlinarith only [sums, copies, hi, rw, Nat.zero_le (input.2.length*V b)]
    · dsimp only [emitSpaceBudget, Q]
      change _ ≤ (input.2.length + 1) * (2*V b+N (3*b+1)+E (3*b+1)+10*b+10)
      nlinarith only [spaces, hi, ho, sw, rw, nonneg]
  refine ⟨P, hp, mp, machine.computes.mono_le (fun input => ?_) (fun input => ?_)⟩
  · have h := (bound input).1.trans (Nat.mul_le_mul_left K (budgets input).1)
    dsimp only [P]
    nlinarith only [h, Nat.zero_le ((input.2.length + 1) * Q (B input))]
  · have h := (bound input).2.trans (Nat.mul_le_mul_left K (budgets input).2)
    dsimp only [P]
    nlinarith only [h, Nat.zero_le ((input.2.length + 1) * Q (B input))]

end Cslib.GenericRAM.NativeCertificate
