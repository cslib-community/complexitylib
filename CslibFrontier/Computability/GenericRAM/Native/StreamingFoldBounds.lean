/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.GenericRAM.Native.StreamingFold
import all CslibFrontier.Computability.GenericRAM.Native.StreamingFold
import all CslibFrontier.Computability.GenericRAM.Native.Combinators

/-!
# Resource envelopes for the installed encoded fold

Expose the installed fold certificate's summed callback time and maximum callback
workspace, with captured parameters, every prefix state, framing, input and output
charged. The fixed multiplier is chosen before the runtime input. The machine and
its existing allowance fields are unchanged.

## Main definitions

* `foldStateWidth`: maximum encoded evolving state at every prefix, including endpoints.
* `foldTimeBudget`, `foldSpaceBudget`: callback sums/maxima and explicit copy/frame budgets.

## Main results

* `foldlStream_bounds`: resource envelopes for the actual installed certificate.
-/

public section
namespace Cslib.GenericRAM.NativeCertificate
open Turing.MultiTapeTM

/-- Maximum evolving-state wire at every prefix of this actual fold. -/
def foldStateWidth {π σ α : Type} (es : σ ↪ List Bool) (step : π → σ → α → σ)
    (input : π × (σ × List α)) : ℕ :=
  let (parameter, (initial, rows)) := input
  (Finset.range (rows.length+1)).sup
    (fun j => (es ((rows.take j).foldl (step parameter) initial)).length)

/-- Sum of actual callback clocks, with all captured-state/token copies and input framing. -/
def foldTimeBudget {π σ α : Type} (ep : π ↪ List Bool) (es : σ ↪ List Bool)
    (ea : α ↪ List Bool) (step : π → σ → α → σ)
    (body : NativeCertificate (fun q : (π × σ) × α => step q.1.1 q.1.2 q.2)
      (encPair (encPair ep es) ea) es) (input : π × (σ × List α)) : ℕ :=
  let (parameter, (initial, rows)) := input
  (encPair ep (encPair es (encList ea)) input).length +
    (∑ j ∈ Finset.range rows.length, if h : j < rows.length then
      body.time ((parameter, (rows.take j).foldl (step parameter) initial), rows[j]) else 0) +
    (rows.length+1)*((ep parameter).length+foldStateWidth es step input+
      streamRecordLength ea rows+1)+1

/-- Maximum actual callback workspace, charging all prefix states, input and output wires.
No total running time or sum of callback workspaces is substituted for simultaneous space. -/
def foldSpaceBudget {π σ α : Type} (ep : π ↪ List Bool) (es : σ ↪ List Bool)
    (ea : α ↪ List Bool) (step : π → σ → α → σ)
    (body : NativeCertificate (fun q : (π × σ) × α => step q.1.1 q.1.2 q.2)
      (encPair (encPair ep es) ea) es) (input : π × (σ × List α)) : ℕ :=
  let (parameter, (initial, rows)) := input
  (encPair ep (encPair es (encList ea)) input).length +
    (Finset.range rows.length).sup (fun j => if h : j < rows.length then
      body.space ((parameter, (rows.take j).foldl (step parameter) initial), rows[j]) else 0) +
    (ep parameter).length+foldStateWidth es step input+streamRecordLength ea rows+1

/-- The original installed fold has these envelopes with one fixed multiplier, independent
of input length, visited states, callback outcomes and early-exit parking. -/
theorem foldlStream_bounds {π σ α : Type} (ep : π ↪ List Bool) (es : σ ↪ List Bool)
    (ea : α ↪ List Bool) (step : π → σ → α → σ)
    (body : NativeCertificate (fun q : (π × σ) × α => step q.1.1 q.1.2 q.2)
      (encPair (encPair ep es) ea) es) :
    ∃ K : ℕ, ∀ input,
      (foldlStream ep es ea step body).time input ≤ K*foldTimeBudget ep es ea step body input ∧
      (foldlStream ep es ea step body).space input ≤
        K*foldSpaceBudget ep es ea step body input := by
  delta foldlStream
  extract_lets estate enext next raw lifted framed decoded argument hn cN hN finishProof cF hF
    emptyProof cE hE st stateEq R Q B kernel C hk T S realizes machine ei original
  let L := 100*(cN+cE+cF+1)
  let K := 100*(C+1)*(L+1)
  refine ⟨K, ?_⟩
  rintro ⟨parameter, initial, rows⟩
  let input := (parameter, (initial, rows))
  let swapped := ((parameter, initial), rows)
  let stateWidth := foldStateWidth es step input
  let rowWidth := streamRecordLength ea rows
  let W := (ep parameter).length+stateWidth+rowWidth+1
  let callbacks := fun j => if h : j < rows.length then
    body.time ((parameter, (rows.take j).foldl (step parameter) initial), rows[j]) else 0
  let spaces := fun j => if h : j < rows.length then
    body.space ((parameter, (rows.take j).foldl (step parameter) initial), rows[j]) else 0
  let sumTime := ∑ j ∈ Finset.range rows.length, callbacks j
  let maxSpace := (Finset.range rows.length).sup spaces
  let inputWidth := (ei input).length
  have lN : cN ≤ L := by dsimp only [L]; omega
  have lE : cE ≤ L := by dsimp only [L]; omega
  have lF : cF ≤ L := by dsimp only [L]; omega
  have lPos : 1 ≤ L := by dsimp only [L]; omega
  have wPos : 1 ≤ W := by dsimp only [W]; omega
  have state (j : ℕ) (hj : j ≤ rows.length) :
      (es ((rows.take j).foldl (step parameter) initial)).length ≤ stateWidth := by
    dsimp only [stateWidth, foldStateWidth, input]
    exact Finset.le_sup (f := fun k =>
      (es ((rows.take k).foldl (step parameter) initial)).length)
      (Finset.mem_range.mpr (show j < rows.length+1 by omega))
  have token (j : ℕ) (hj : j < rows.length) : (ea rows[j]).length ≤ rowWidth :=
    le_listMax (f := fun row => (ea row).length) (List.getElem_mem hj)
  have estateBound (j : ℕ) (hj : j ≤ rows.length) :
      (estate (st swapped j)).length+1 ≤ 3*W := by
    have h := state j hj
    dsimp only [estate, st, swapped]
    rw [length_encPair]
    dsimp only [W]
    omega
  have rowBound (j : ℕ) (hj : j < rows.length) :
      R swapped j ≤ L*(callbacks j+W) := by
    have s₁ := state j (by omega)
    have s₂ := state (j+1) (by omega)
    have r := token j hj
    dsimp only [R, swapped]
    rw [dite_eq_left hj]
    dsimp only [callbacks]
    rw [dite_eq_left hj]
    dsimp only [argument, lifted, raw, framed, decoded, NativeCertificate.prod,
      NativeCertificate.fst, NativeCertificate.snd, NativeCertificate.post,
      NativeCertificate.comp, NativeCertificate.linear, Function.comp_def, id_eq,
      enext, estate, st, swapped]
    simp only [length_encPair, encFramed_apply, length_frame]
    have coefficient : 20*cN+2*cE+20 ≤ L := by dsimp only [L]; omega
    have main := Nat.mul_le_mul lN (Nat.le_refl
      (body.time ((parameter, (rows.take j).foldl (step parameter) initial), rows[j])))
    have frames : cN*(12*(ep parameter).length+6*
          (es ((rows.take j).foldl (step parameter) initial)).length+7*(ea rows[j]).length+13)+
        (2*cE+2)+4*(ep parameter).length+
          (es ((rows.take j).foldl (step parameter) initial)).length+
          (es ((rows.take (j+1)).foldl (step parameter) initial)).length+
          2*(ea rows[j]).length+4 ≤ L*W := by
      have inner : 12*(ep parameter).length+6*
          (es ((rows.take j).foldl (step parameter) initial)).length+7*(ea rows[j]).length+13 ≤
            20*W := by dsimp only [W]; omega
      have mul := Nat.mul_le_mul_left cN inner
      have rest : (2*cE+2)+4*(ep parameter).length+
          (es ((rows.take j).foldl (step parameter) initial)).length+
          (es ((rows.take (j+1)).foldl (step parameter) initial)).length+
          2*(ea rows[j]).length+4 ≤ (2*cE+20)*W := by
        have hc := Nat.mul_le_mul_left (2*cE+20) wPos
        dsimp only [W] at *
        nlinarith only [s₁, s₂, r, hc]
      have total := Nat.add_le_add mul rest
      nlinarith only [total, Nat.mul_le_mul_right W coefficient]
    nlinarith only [main, frames]
  have sumBound : (∑ j ∈ Finset.range rows.length, R swapped j) ≤
      L*(sumTime+rows.length*W) := by
    have h := Finset.sum_le_sum (fun j hj => rowBound j (Finset.mem_range.mp hj))
    simpa only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, Nat.cast_id, sumTime] using h
  have maxBound : Q swapped ≤ L*(maxSpace+W) := by
    apply Finset.sup_le
    intro j hj
    have hj' : j < rows.length := Finset.mem_range.mp hj
    have s := state j (by omega)
    have r := token j hj'
    have callback : spaces j ≤ maxSpace := Finset.le_sup hj
    dsimp only [Q, swapped]
    rw [dite_eq_left hj']
    dsimp only [spaces] at callback
    rw [dite_eq_left hj'] at callback
    dsimp only [argument, lifted, raw, framed, decoded, NativeCertificate.prod,
      NativeCertificate.fst, NativeCertificate.snd, NativeCertificate.post,
      NativeCertificate.comp, NativeCertificate.linear, Function.comp_def, id_eq,
      enext, estate, st, swapped]
    simp only [length_encPair, encFramed_apply, length_frame]
    have inner : 12*(ep parameter).length+6*
        (es ((rows.take j).foldl (step parameter) initial)).length+7*(ea rows[j]).length+13 ≤
          20*W := by dsimp only [W]; omega
    have sum := Nat.mul_le_mul_left cN (Nat.add_le_add callback inner)
    have coefficient : 20*cN ≤ L := by dsimp only [L]; omega
    have c₁ := Nat.mul_le_mul_right maxSpace lN
    have c₂ := Nat.mul_le_mul_right W coefficient
    nlinarith only [sum, c₁, c₂]
  have stateBudget : B swapped ≤ 5*W := by
    have states : (Finset.range (rows.length+1)).sup
        (fun j => (estate (st swapped j)).length) ≤ 3*W := by
      apply Finset.sup_le
      intro j hj
      exact (Nat.le_add_right _ _).trans (estateBound j (by have := Finset.mem_range.mp hj; omega))
    have tokens : streamRecordLength (encFramed ea) rows ≤ 2*rowWidth+1 := by
      apply listMax_le
      intro row hr
      have h := le_listMax (f := fun row => (ea row).length) hr
      change (ea row).length ≤ rowWidth at h
      simp only [encFramed_apply, length_frame]
      omega
    change (Finset.range (rows.length+1)).sup
      (fun j => (estate (st swapped j)).length)+streamRecordLength (encFramed ea) rows ≤ _
    dsimp only [W]
    omega
  have swappedWire : (encPair estate (encList ea) swapped).length ≤ 3*inputWidth := by
    dsimp only [estate, swapped, inputWidth, ei, input]
    rw [length_encPair, length_encPair, length_encPair, length_encPair]
    dsimp only
    omega
  have last := estateBound rows.length (Nat.le_refl _)
  have finish : cF*((estate (st swapped rows.length)).length+1) ≤ 3*L*W :=
    (Nat.mul_le_mul lF last).trans_eq (by ring)
  have output : (es (rows.foldl (step parameter) initial)).length ≤ W := by
    have h := state rows.length (Nat.le_refl _)
    rw [List.take_length] at h
    dsimp only [W]; omega
  constructor
  · change (inputWidth+inputWidth+inputWidth)+T swapped ≤
      K*(inputWidth+sumTime+(rows.length+1)*W+1)
    dsimp only [T]
    have nW : W ≤ (rows.length+1)*W := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    have inner := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add finish swappedWire) sumBound)
      stateBudget
    have bound : cF*((estate (st swapped rows.length)).length+1)+
        (encPair estate (encList ea) swapped).length+
        (∑ j ∈ Finset.range rows.length, R swapped j)+B swapped+1 ≤
          10*L*(inputWidth+sumTime+(rows.length+1)*W+1) := by
      have hI := Nat.mul_le_mul_left inputWidth lPos
      have hW := Nat.mul_le_mul_left W lPos
      nlinarith only [inner, hI, hW, nW, lPos]
    have scaled := Nat.mul_le_mul_left C bound
    have base := Nat.mul_le_mul_left (inputWidth+sumTime+(rows.length+1)*W+1)
      (by dsimp only [K]; nlinarith : 10*C*L+3 ≤ K)
    nlinarith only [scaled, base]
  · change (inputWidth+inputWidth+inputWidth)+
      (S swapped+(es (rows.foldl (step parameter) initial)).length) ≤
        K*foldSpaceBudget ep es ea step body input
    have normalized : foldSpaceBudget ep es ea step body input = inputWidth+maxSpace+W := by
      change inputWidth+maxSpace+(ep parameter).length+stateWidth+rowWidth+1 =
        inputWidth+maxSpace+((ep parameter).length+stateWidth+rowWidth+1)
      omega
    rw [normalized]
    dsimp only [S]
    have inner := Nat.add_le_add (Nat.add_le_add finish maxBound) stateBudget
    have bound : cF*((estate (st swapped rows.length)).length+1)+Q swapped+B swapped+1 ≤
        10*L*(inputWidth+maxSpace+W) := by
      have hI := Nat.mul_le_mul_left inputWidth lPos
      have hW := Nat.mul_le_mul_left W lPos
      nlinarith only [inner, hI, hW, wPos, lPos]
    have scaled := Nat.mul_le_mul_left C bound
    have base := Nat.mul_le_mul_left (inputWidth+maxSpace+W)
      (by dsimp only [K]; nlinarith : 10*C*L+4 ≤ K)
    nlinarith only [scaled, base, output]

end Cslib.GenericRAM.NativeCertificate
