/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.GenericRAM.Native.StreamingEmit
public import CslibFrontier.Computability.GenericRAM.Native.StreamingFoldBounds
import all CslibFrontier.Computability.GenericRAM.Native.StreamingEmit
import all CslibFrontier.Computability.GenericRAM.Native.StreamingFoldBounds
import all CslibFrontier.Computability.GenericRAM.Native.Combinators

/-!
# Cumulative resources of the installed stateful emitter

Bound the unchanged encoded emitter by actual callback sums and workspace maxima.
Time sums token wires, including variable-size groups, rather than multiplying
maximum token size by the number of tokens. Every prefix state, framing, input,
output and callback temporary is charged.

## Main definitions

* `emitTimeBudget`, `emitSpaceBudget`: cumulative clock and simultaneous workspace budgets.

## Main results

* `emitFoldCertificate_bounds`: resource envelopes for the installed uniform machine.
-/

public section
namespace Cslib.GenericRAM.NativeCertificate
open Turing.MultiTapeTM

/-- Actual callback clocks and token wires, plus input and all prefix-state copies. -/
def emitTimeBudget {σ α β : Type} (es : σ ↪ List Bool) (ea : α ↪ List Bool)
    (eb : β ↪ List Bool) (next : σ → α → σ) (emit : σ → α → List β)
    (nm : NativeCertificate (fun q : σ × α => next q.1 q.2) (encPair es ea) es)
    (em : NativeCertificate (fun q : σ × α => emit q.1 q.2) (encPair es ea) (encList eb))
    (input : σ × List α) : ℕ :=
  let (initial, rows) := input
  (encPair es (encList ea) input).length+
    (∑ j ∈ Finset.range rows.length, if h : j < rows.length then
      nm.time (streamState initial (fun q => next q.1 q.2) rows j, rows[j])+
      em.time (streamState initial (fun q => next q.1 q.2) rows j, rows[j])+
      (ea rows[j]).length else 0)+
    (rows.length+1)*(foldStateWidth es (fun (_ : Unit) => next) ((), input)+1)+
    streamRecordLength ea rows+1

/-- Callback workspace maximum, all prefix states, and materialized input/output wires.
Running time and total allocation are not substituted for simultaneous space. -/
def emitSpaceBudget {σ α β : Type} (es : σ ↪ List Bool) (ea : α ↪ List Bool)
    (eb : β ↪ List Bool) (next : σ → α → σ) (emit : σ → α → List β)
    (nm : NativeCertificate (fun q : σ × α => next q.1 q.2) (encPair es ea) es)
    (em : NativeCertificate (fun q : σ × α => emit q.1 q.2) (encPair es ea) (encList eb))
    (input : σ × List α) : ℕ :=
  let (initial, rows) := input
  (encPair es (encList ea) input).length+
    (Finset.range rows.length).sup (fun j => if h : j < rows.length then
      nm.space (streamState initial (fun q => next q.1 q.2) rows j, rows[j])+
      em.space (streamState initial (fun q => next q.1 q.2) rows j, rows[j]) else 0)+
    foldStateWidth es (fun (_ : Unit) => next) ((), input)+streamRecordLength ea rows+
    (encList eb (emitFold next emit initial rows)).length+1

/-- One fixed multiplier bounds the actual installed emitter, independently of token sizes,
visited states and emitted populations. Both empty streams and all execution prefixes count. -/
theorem emitFoldCertificate_bounds {σ α β : Type} (es : σ ↪ List Bool)
    (ea : α ↪ List Bool) (eb : β ↪ List Bool) (next : σ → α → σ) (emit : σ → α → List β)
    (nextMachine : NativeCertificate (fun q : σ × α => next q.1 q.2) (encPair es ea) es)
    (emitMachine : NativeCertificate (fun q : σ × α => emit q.1 q.2)
      (encPair es ea) (encList eb)) :
    ∃ K : ℕ, ∀ input,
      (emitFoldCertificate es ea eb next emit nextMachine emitMachine).time input ≤
          K*emitTimeBudget es ea eb next emit nextMachine emitMachine input ∧
        (emitFoldCertificate es ea eb next emit nextMachine emitMachine).space input ≤
          K*emitSpaceBudget es ea eb next emit nextMachine emitMachine input := by
  delta emitFoldCertificate
  extract_lets enext framed decoded argument nm em N hn encoded E he finishProof F hf
    st R Q B kernel C hk T S realizes
  let L := 100*(N+E+1)
  let K := 100*(C+1)*(F+L+1)
  refine ⟨K, ?_⟩
  rintro ⟨initial, rows⟩
  let input := (initial, rows)
  let sw := foldStateWidth es (fun (_ : Unit) => next) ((), input)
  let aw := streamRecordLength ea rows
  let clocks := fun j => if h : j < rows.length then
    nextMachine.time (st input j, rows[j])+emitMachine.time (st input j, rows[j])+
      (ea rows[j]).length else 0
  let spaces := fun j => if h : j < rows.length then
    nextMachine.space (st input j, rows[j])+emitMachine.space (st input j, rows[j]) else 0
  let sumTime := ∑ j ∈ Finset.range rows.length, clocks j
  let maxSpace := (Finset.range rows.length).sup spaces
  have nL : N ≤ L := by dsimp only [L]; omega
  have eL : E ≤ L := by dsimp only [L]; omega
  have state (j : ℕ) (hj : j ≤ rows.length) : (es (st input j)).length ≤ sw := by
    dsimp only [sw, foldStateWidth, input, st, streamState]
    exact Finset.le_sup (f := fun j =>
      (es ((rows.take j).foldl next initial)).length)
      (Finset.mem_range.mpr (by omega : j < rows.length+1))
  have rowBound (j : ℕ) (hj : j < rows.length) :
      R input j ≤ L*(clocks j+sw+1) := by
    have s₁ := state j (by omega)
    have s₂ := state (j+1) (by omega)
    dsimp only [R, clocks]
    rw [dite_eq_left hj, dite_eq_left hj]
    dsimp only [nm, em, argument, framed, decoded, enext, NativeCertificate.comp,
      NativeCertificate.prod, NativeCertificate.fst, NativeCertificate.snd,
      NativeCertificate.post, NativeCertificate.linear, Function.comp_def, id_eq]
    simp only [length_encPair, encFramed_apply, length_frame]
    have a := Nat.mul_le_mul_right (nextMachine.time (st input j, rows[j])) nL
    have b := Nat.mul_le_mul_right (emitMachine.time (st input j, rows[j])) eL
    have coeff : 20*(N+E+1) ≤ L := by dsimp only [L]; omega
    have extra : N*(4*(es (st input j)).length+6*(ea rows[j]).length+6)+
        E*(4*(es (st input j)).length+6*(ea rows[j]).length+6)+
        (es (st input j)).length+(es (st input (j+1))).length+
        (2*(ea rows[j]).length+1)+1 ≤ L*((ea rows[j]).length+sw+1) := by
      have hn : 4*(es (st input j)).length+6*(ea rows[j]).length+6 ≤
          10*((ea rows[j]).length+sw+1) := by omega
      have x := Nat.mul_le_mul_left N hn
      have y := Nat.mul_le_mul_left E hn
      have z : (es (st input j)).length+(es (st input (j+1))).length+
          (2*(ea rows[j]).length+1)+1 ≤ 10*((ea rows[j]).length+sw+1) := by omega
      have scaled := Nat.mul_le_mul_right ((ea rows[j]).length+sw+1) coeff
      nlinarith only [x, y, z, scaled]
    dsimp only [input] at a b extra ⊢
    nlinarith only [a, b, extra]
  have sumBound : (∑ j ∈ Finset.range rows.length, R input j) ≤
      L*(sumTime+rows.length*(sw+1)) := by
    have h := Finset.sum_le_sum (fun j hj => rowBound j (Finset.mem_range.mp hj))
    calc
      (∑ j ∈ Finset.range rows.length, R input j) ≤
          L*(sumTime+rows.length*sw+rows.length) := by
        simpa only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_range, nsmul_eq_mul, Nat.cast_id, Nat.mul_one, sumTime] using h
      _ = L*(sumTime+rows.length*(sw+1)) := by ring
  have maxBound : Q input ≤ L*(maxSpace+sw+aw+1) := by
    dsimp only [Q, input]
    apply Finset.sup_le
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have current := state j (by omega)
    have token : (ea rows[j]).length ≤ aw :=
      le_listMax (f := fun row => (ea row).length) (List.getElem_mem hj')
    have callback : spaces j ≤ maxSpace := Finset.le_sup hj
    dsimp only [spaces] at callback
    rw [dite_eq_left hj'] at callback
    rw [dite_eq_left hj']
    dsimp only [nm, em, argument, framed, decoded, enext, NativeCertificate.comp,
      NativeCertificate.prod, NativeCertificate.fst, NativeCertificate.snd,
      NativeCertificate.post, NativeCertificate.linear, Function.comp_def, id_eq]
    simp only [length_encPair, encFramed_apply, length_frame]
    have inner : 4*(es (st input j)).length+6*(ea rows[j]).length+6 ≤ 10*(sw+aw+1) := by omega
    have x := Nat.mul_le_mul_left N inner
    have y := Nat.mul_le_mul_left E inner
    have actual := Nat.add_le_add (Nat.mul_le_mul_left N callback)
      (Nat.mul_le_mul_left E callback)
    dsimp only [input] at x y actual ⊢
    dsimp only [L]
    nlinarith only [x, y, actual,
      Nat.zero_le (N*emitMachine.space (st input j, rows[j])),
      Nat.zero_le (E*nextMachine.space (st input j, rows[j]))]
  have buffer : B input ≤ sw+2*aw+1 := by
    have token : streamRecordLength (encFramed ea) rows ≤ 2*aw+1 := by
      apply listMax_le
      intro row hr
      have h := le_listMax (f := fun row => (ea row).length) hr
      change (ea row).length ≤ aw at h
      simp only [encFramed_apply, length_frame]
      omega
    change sw+streamRecordLength (encFramed ea) rows ≤ sw+2*aw+1
    omega
  have stateCopies : sw+1 ≤ (rows.length+1)*(sw+1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  constructor
  · let V := (encPair es (encList ea) input).length+sumTime+
      (rows.length+1)*(sw+1)+aw+1
    change C*(2*F+2+(encPair es (encList ea) input).length+
      (∑ j ∈ Finset.range rows.length, R input j)+B input+1) ≤ K*V
    have vPos : 1 ≤ V := by dsimp only [V]; omega
    have copyLe : rows.length*(sw+1) ≤ (rows.length+1)*(sw+1) :=
      Nat.mul_le_mul_right (sw+1) (Nat.le_succ rows.length)
    have core : sumTime+rows.length*(sw+1) ≤ V := by dsimp only [V]; omega
    have wire : (encPair es (encList ea) input).length ≤ V := by dsimp only [V]; omega
    have storage : B input ≤ 2*V := by dsimp only [V]; omega
    have callbacks := sumBound.trans (Nat.mul_le_mul_left L core)
    have offset := Nat.mul_le_mul_left (2*F+3) vPos
    have inner : 2*F+2+(encPair es (encList ea) input).length+
        (∑ j ∈ Finset.range rows.length, R input j)+B input+1 ≤ (L+2*F+6)*V := by
      nlinarith only [callbacks, offset, wire, storage]
    have coeff : C*(L+2*F+6) ≤ K := by
      dsimp only [K]
      nlinarith [Nat.zero_le (C*L), Nat.zero_le (C*F)]
    exact (Nat.mul_le_mul_left C inner).trans
      (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right V coeff)
  · let V := (encPair es (encList ea) input).length+maxSpace+sw+aw+
      (encList eb (emitFold next emit initial rows)).length+1
    change C*(0+Q input+B input+1)+
      (encList eb (emitFold next emit initial rows)).length ≤ K*V
    have vPos : 1 ≤ V := by dsimp only [V]; omega
    have core : maxSpace+sw+aw+1 ≤ V := by dsimp only [V]; omega
    have storage : B input ≤ 2*V := by dsimp only [V]; omega
    have output : (encList eb (emitFold next emit initial rows)).length ≤ V := by
      dsimp only [V]; omega
    have callbacks := maxBound.trans (Nat.mul_le_mul_left L core)
    have inner : 0+Q input+B input+1 ≤ (L+3)*V := by
      nlinarith only [callbacks, storage, vPos]
    have coeff : C*(L+3)+1 ≤ K := by
      dsimp only [K]
      nlinarith [Nat.zero_le (C*L), Nat.zero_le (C*F)]
    have scaled := Nat.mul_le_mul_left C inner
    have final := Nat.mul_le_mul_right V coeff
    nlinarith only [scaled, final, output]

end Cslib.GenericRAM.NativeCertificate
