/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORSortedQuarterMachine
public import CslibFrontier.Cryptanalysis.AddXNORCounterPull
import all CslibFrontier.Cryptanalysis.AddXNORSortedQuarterMachine
import all CslibFrontier.Cryptanalysis.AddXNORCounterPull
import all CslibFrontier.Cryptanalysis.AddXNORClasses
import all CslibFrontier.Computability.GenericRAM.Native.Combinators

/-!
# Generated initial reachable-state counters

The actual uniform state-range generator writes every key, and a scalar callback
writes one at the seed and zero elsewhere. No initial table is supplied as advice.
This is the initial counter table for the DP in [WangLvShenZhang2027], Lemma 8,
PDF pp. 21–22; it also initializes the inverse DP at its prescribed target.

## Main definitions

* `record`, `run`: generate every numeric state with its zero/one indicator.

## Main results

* `run_words`: the exact original-seed singleton counter table.
* `run_computable`: uniform initialization bit time and charged peak workspace.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.CounterInitialization
open Turing.MultiTapeTM Cslib.GenericRAM

/-- Unary state width and binary initial seed or inverse target. -/
abbrev Input := ℕ × ℕ

/-- Frame the unary width before the unframed binary seed/target. -/
abbrev encoding : Input ↪ List Bool := encPair encUnary encNat

/-- Every generated state has a physical zero/one counter, including unreachable states. -/
def record (input : Input) (key : ℕ) : ℕ × ℕ :=
  let (width, seed) := input
  (key, if key = seed % 2^width then 1 else 0)

/-- Enumerate all keys by the existing uniform binary-doubling machine. -/
def run (input : Input) : List (ℕ × ℕ) :=
  let (width, _) := input
  (SortedQuarterMachine.indices width).map (record input)

/-- Exact original-input singleton counters in numeric state order, including width zero. -/
theorem run_words {m : ℕ} (s : BitVec m) :
    run (m, s.toNat) = CounterPull.graph (WordTable.classCounters [] s).read := by
  apply List.ext_getElem
  · simp [run, SortedQuarterMachine.indices_eq_range, CounterPull.graph]
  · intro i hi hj
    simp only [run, SortedQuarterMachine.indices_eq_range, List.getElem_map,
      List.getElem_range, record, CounterPull.graph, List.getElem_ofFn]
    simp [WordTable.classCounters, WordTable.countRun, WordTable.indicators_read,
      WordTable.point_read, ← BitVec.toNat_inj, Nat.mod_eq_of_lt s.isLt, eq_comm]

private theorem emit_polyTime : ComputableInPolyTime
    (fun q : Input × ℕ => [record q.1 q.2]) (encPair encoding encNat) encNatPairList := by
  have row : ComputableInPolyTime (fun q : Input × ℕ => record q.1 q.2)
      (encPair encoding encNat) (encPair encNat encNat) := by
    unfold record
    fun_prop
  have single : ComputableTidilyInPolyTime (fun r : ℕ × ℕ => [r])
      (encPair encNat encNat) encNatPairList := .of_linear (.of_frame (fun _ => by simp))
  exact single.computableInPolyTime.comp row

/-- Complete initialization bit time and peak workspace. The exponential generator, scalar
seed reduction, materialized indices and initialized table are all charged explicitly. -/
theorem run_computable : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ComputableInO run encoding encNatPairList
      (fun input => 2^input.1 * P ((encoding input).length+1))
      (fun input => 2^input.1 * P ((encoding input).length+1)) := by
  obtain ⟨Q, hq, mq, hgen⟩ := SortedQuarterMachine.indices_computable
  obtain ⟨A, ha, ma, hmap⟩ := ComputableInO.flatMap_stream emit_polyTime
  let original : NativeCertificate (id : Input → Input) encoding encoding :=
    .linear (.of_eq (fun _ => rfl))
  have prepare := original.computes.prod (hgen.comp original.fst.computes)
  have actual := (hmap.comp prepare).of_enc_eq (g := run) (encC := encNatPairList)
    (fun _ => by simp only [run, List.map_eq_flatMap]; rfl)
  let P := fun b => (b+1)*Q (b+1)+2*A (2*b+1)+10*b+10
  have hp : Cslib.PolynomiallyBounded P := by dsimp only [P]; fun_prop
  have mp : Monotone P := by
    intro a b hab
    have hq := Nat.mul_le_mul (by omega : a+1 ≤ b+1) (mq (by omega : a+1 ≤ b+1))
    have ha := ma (by omega : 2*a+1 ≤ 2*b+1)
    dsimp only [P]
    omega
  refine ⟨P, hp, mp, actual.mono_le (fun input => ?_) (fun input => ?_)⟩
  all_goals
    rcases input with ⟨m, seed⟩
    let I := 2*(encUnary m).length+1+(encNat seed).length
    have mI : m ≤ I := by
      dsimp only [I]
      simp only [encUnary_apply, List.length_replicate]
      omega
    obtain ⟨hlen, hmax, hwire⟩ := SortedQuarterMachine.indices_wire m
    have genBound := mq (by omega : m+1 ≤ (I+1)+1)
    have mapBound := ma (by
      change I+streamRecordLength encNat (SortedQuarterMachine.indices m)+1 ≤ 2*(I+1)+1
      omega)
    have genTime := Nat.mul_le_mul
      (Nat.mul_le_mul_right (2^m) (by omega : m+1 ≤ I+2)) genBound
    have positive := Nat.two_pow_pos m
    have mapTime := Nat.mul_le_mul
      (by omega : 2^m+1 ≤ 2*2^m) mapBound
    have copies := Nat.mul_le_mul_left I (show 1 ≤ 2^m by omega)
    have wireBound := hwire.trans (Nat.mul_le_mul_left (2^m)
      (by omega : 2*m+1 ≤ 2*I+1))
    simp only [NativeCertificate.linear_time, NativeCertificate.linear_space,
      NativeCertificate.fst_time, NativeCertificate.fst_space, original, id_eq, Function.comp_def,
      hlen]
    dsimp only [P]
    simp only [encoding, length_encPair, streamFilterWidth]
    dsimp only [I] at genTime mapTime wireBound copies genBound
    nlinarith only [genTime, mapTime, wireBound, copies, positive,
      Nat.mul_le_mul_left (2^m) genBound]

end Cslib.Cryptanalysis.AddXNOR.CounterInitialization
