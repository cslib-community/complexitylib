/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.GenericRAM.Native.StreamingFoldBounds
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.MinMax
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Containers
import all CslibFrontier.Computability.GenericRAM.Native.StreamingFoldBounds
import all CslibFrontier.Computability.GenericRAM.Native.Combinators
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Foundations.Data.List.Fold
import Mathlib.Data.List.Fold

/-!
# One-pass maximum of binary pair minima

A scalar accumulator retains the maximum of the pair minima read so far.
The installed streaming fold charges every prefix, binary comparison, input,
control and output. No remaining list is passed to the arithmetic callback.

## Main results

* `run_eq_listMax`: exact maximum, with zero for an empty stream.
* `run_computable`: linear record count times a polynomial in maximum record width.
-/

public section
namespace Turing.MultiTapeTM.PairMaxMin
open Cslib.GenericRAM

private def step (s : ℕ) (row : ℕ × ℕ) : ℕ := max s (min row.1 row.2)

/-- Read each binary pair once; retain only the current maximum of its minima. -/
def run (rows : List (ℕ × ℕ)) : ℕ := rows.foldl step 0

/-- Width of one physical binary pair, including framing and a constant margin. -/
def width (rows : List (ℕ × ℕ)) : ℕ := streamRecordLength (encPair encNat encNat) rows+1

/-- The empty stream returns zero; every other result is the maximum pair minimum. -/
theorem run_eq_listMax (rows : List (ℕ × ℕ)) : run rows = listMax (fun r => min r.1 r.2) rows := by
  rw [run, show step = fun s row => max s (min row.1 row.2) from rfl,
    ← List.foldl_map, List.foldl_eq_foldr]
  rfl

private theorem state_bound (rows : List (ℕ × ℕ)) (j : ℕ) (hj : j ≤ rows.length) :
    (encNat ((rows.take j).foldl step 0)).length ≤ width rows := by
  apply List.foldl_take_invariant rows step 0
    (fun _ s => (encNat s).length ≤ width rows) (by simp [width]) ?_ j hj
  intro i hi s hs
  have hr := le_listMax (f := fun r => (encPair encNat encNat r).length) (List.getElem_mem hi)
  have first : (encNat rows[i].1).length ≤ width rows := by
    change (encPair encNat encNat rows[i]).length ≤
      streamRecordLength (encPair encNat encNat) rows at hr
    simp only [length_encPair] at hr
    dsimp only [width]
    omega
  have smaller := length_encNat_mono (Nat.min_le_left rows[i].1 rows[i].2)
  dsimp only [step]
  rcases le_total s (min rows[i].1 rows[i].2) with h | h
  · rw [Nat.max_eq_right h]
    exact smaller.trans first
  · rw [Nat.max_eq_left h]
    exact hs

/-- Actual uniform bit execution with small scalar state and per-width arithmetic costs.
The input and all callback/control tapes are included in every-prefix workspace. -/
theorem run_computable : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ComputableInO run encNatPairList encNat
      (fun rows => (rows.length+1)*P (width rows))
      (fun rows => (rows.length+1)*P (width rows)) := by
  let e := NativeCertificate.encFoldStep encBool encNat (encPair encNat encNat)
  have hs : ComputableInPolyTime
      (fun q : (Bool × ℕ) × (ℕ × ℕ) => step q.1.2 q.2) e encNat := by
    unfold step
    fun_prop
  let body := NativeCertificate.ofPolyTime hs
  obtain ⟨Q, hpQ, mQ, hQ⟩ := exists_mono_poly_cert hs
  let original : NativeCertificate (id : List (ℕ × ℕ) → _) encNatPairList encNatPairList :=
    .linear (.of_eq (fun _ => rfl))
  let setup := (NativeCertificate.const (ei := encNatPairList) (em := encBool) false).prod
    ((NativeCertificate.const (ei := encNatPairList) (em := encNat) 0).prod original)
  let machine := (NativeCertificate.foldlStream encBool encNat (encPair encNat encNat)
    (fun _ => step) body).comp setup
  obtain ⟨K, hk⟩ := NativeCertificate.foldlStream_bounds encBool encNat
    (encPair encNat encNat) (fun _ => step) body
  let P := fun b => 10*b+10+K*(Q (3*b+7)+20*b+20)
  have hp : Cslib.PolynomiallyBounded P := by dsimp only [P]; fun_prop
  have mp : Monotone P := by
    intro a b h
    have hq := mQ (by omega : 3*a+7 ≤ 3*b+7)
    dsimp only [P]
    exact Nat.add_le_add (by omega) (Nat.mul_le_mul_left K (by omega))
  have estimates (rows : List (ℕ × ℕ)) :
      machine.time rows ≤ (rows.length+1)*P (width rows) ∧
      machine.space rows ≤ (rows.length+1)*P (width rows) := by
    let B := width rows
    have records : ∀ row ∈ rows, (encPair encNat encNat row).length ≤ B := by
      intro row hr
      have := le_listMax (f := fun r => (encPair encNat encNat r).length) hr
      change (encPair encNat encNat row).length ≤
        streamRecordLength (encPair encNat encNat) rows at this
      dsimp only [B, width]
      omega
    have wire := length_encList_le (encPair encNat encNat) rows records
    have states : NativeCertificate.foldStateWidth encNat (fun (_ : Bool) => step)
        (false, (0, rows)) ≤ B := by
      apply Finset.sup_le
      intro j hj
      exact state_bound rows j (by have := Finset.mem_range.mp hj; omega)
    have callbacks (j : ℕ) (hj : j < rows.length) :
        body.time ((false, (rows.take j).foldl step 0), rows[j]) ≤ Q (3*B+7) ∧
        body.space ((false, (rows.take j).foldl step 0), rows[j]) ≤ Q (3*B+7) := by
      have s := state_bound rows j hj.le
      have r := records rows[j] (List.getElem_mem hj)
      have bound : (e ((false, (rows.take j).foldl step 0), rows[j])).length ≤ 3*B+7 := by
        simp only [e, NativeCertificate.encFoldStep, length_encPair, encBool_apply,
          List.length_singleton]
        dsimp only [B] at *
        simp only [length_encPair] at r
        omega
      exact ⟨(hQ _).1.trans (mQ bound), (hQ _).2.trans (mQ bound)⟩
    have sum : (∑ j ∈ Finset.range rows.length, if h : j < rows.length then
        body.time ((false, (rows.take j).foldl step 0), rows[j]) else 0) ≤
        rows.length*Q (3*B+7) := by
      calc
        _ ≤ ∑ _j ∈ Finset.range rows.length, Q (3*B+7) := by
          apply Finset.sum_le_sum
          intro j hj
          rw [dite_eq_left (Finset.mem_range.mp hj)]
          exact (callbacks j (Finset.mem_range.mp hj)).1
        _ = _ := by simp
    have peak : (Finset.range rows.length).sup (fun j => if h : j < rows.length then
        body.space ((false, (rows.take j).foldl step 0), rows[j]) else 0) ≤ Q (3*B+7) := by
      apply Finset.sup_le
      intro j hj
      rw [dite_eq_left (Finset.mem_range.mp hj)]
      exact (callbacks j (Finset.mem_range.mp hj)).2
    have rwid : streamRecordLength (encPair encNat encNat) rows ≤ B := by
      dsimp only [B, width]
      omega
    have wt : NativeCertificate.foldTimeBudget encBool encNat (encPair encNat encNat)
        (fun _ => step) body (false, (0, rows)) ≤
        (rows.length+1)*(Q (3*B+7)+20*B+20) := by
      simp only [NativeCertificate.foldTimeBudget, length_encPair, encBool_apply,
        List.length_singleton, show (encNat 0).length = 0 from rfl]
      have copied := Nat.mul_le_mul_left (rows.length+1) states
      have tokens := Nat.mul_le_mul_left (rows.length+1) rwid
      nlinarith only [wire, sum, copied, tokens]
    have ws : NativeCertificate.foldSpaceBudget encBool encNat (encPair encNat encNat)
        (fun _ => step) body (false, (0, rows)) ≤
        (rows.length+1)*(Q (3*B+7)+20*B+20) := by
      simp only [NativeCertificate.foldSpaceBudget, length_encPair, encBool_apply,
        List.length_singleton, show (encNat 0).length = 0 from rfl]
      nlinarith only [wire, peak, states, rwid, Nat.zero_le (rows.length*Q (3*B+7))]
    have h := hk (false, (0, rows))
    constructor <;>
      simp only [machine, setup, NativeCertificate.comp, NativeCertificate.prod,
        NativeCertificate.const, NativeCertificate.linear, original, id_eq, Function.comp_def]
    · have total := Nat.mul_le_mul_left K wt
      dsimp only [P, B] at wire h total ⊢
      nlinarith only [wire, h.1, total]
    · have total := Nat.mul_le_mul_left K ws
      dsimp only [P, B] at wire h total ⊢
      nlinarith only [wire, h.2, total]
  exact ⟨P, hp, mp, machine.computes.mono_le (fun rows => (estimates rows).1)
    (fun rows => (estimates rows).2)⟩

end Turing.MultiTapeTM.PairMaxMin
