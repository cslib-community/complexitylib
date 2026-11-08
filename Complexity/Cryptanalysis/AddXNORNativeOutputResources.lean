/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORNativeGlobalResources
public import Complexity.Cryptanalysis.AddXNOROutputCodec
import all Complexity.Cryptanalysis.AddXNOROutputCodec
import all Complexity.Cryptanalysis.AddXNORNativeOutput
import all Complexity.Cryptanalysis.AddXNORNativeGlobalResources
import all Complexity.Cryptanalysis.AddXNORNativeGlobalLayout
import all Complexity.Cryptanalysis.AddXNORNativeGlobalTime
import all Complexity.Cryptanalysis.AddXNORNativeDissection
import all Complexity.Cryptanalysis.AddXNORNativeClassCounts
import all Complexity.Cryptanalysis.AddXNORNativeOrientedSearch

/-!
# Original-input dissection with charged native witness output

Append the actual native serializer to the already proved fixed dissection.
The output is a represented array, not an uncharged mathematical observation of
registers. Construction, orientation, output length, bit order and witness
correctness are all derived from original operands. Time adds `7*q+53` native
instructions and one halt; every compiled prefix adds the same conservative
linear allowance to the proved computed-balance occupied-memory bound. The
original derived physical width also admits all output addresses and values.

`OutputCodec.decoder` is a concrete zero-work-tape Turing machine converting the
encoded returned word array to an optional raw bit witness. This separate linear
bit stage does not simulate the core RAM memory accesses. Source multitape time,
encoded input/header and uniform program generation remain open.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Driver

open Cslib.WordRAM Quarter

/-- The fixed native dissection followed by its real output stores. -/
@[expose] def dissectionOutput {W m p a b c d : ℕ} (L : SearchLayout W m p a b c d)
    (K : CounterLayout L) (s t : BitVec m) : Code .standard 40 :=
  .seq (dissection L K s t) (Output.program L.D a b c d)

/-- Adding serialization retains a fixed graph, with one further instruction for halt. -/
theorem dissectionOutput_size {W m p a b c d : ℕ} (L : SearchLayout W m p a b c d)
    (K : CounterLayout L) (s t : BitVec m) : (dissectionOutput L K s t).size = 1108 := by
  simp only [dissectionOutput, Code.size, dissection_size, Output.program_size]

/-- A linear instruction and store allowance for materializing the output array. -/
def outputTime (a b c d : ℕ) : ℕ := 7 * (a + b + c + d) + 53

/-- The original logarithmic word width also admits the complete output interval. -/
theorem compact_output_fits (m p a b c d : ℕ) :
    Fits (globalWidth m p a b c d)
      ((compactSearchLayout m p a b c d).D + (a + b + c + d) + 6) := by
  apply (layoutLimit_fits m p a b c d).of_le
  rw [compactSearchLayout_dictionary]
  dsimp only [layoutLimit]
  have hm := Nat.two_pow_pos m
  have hp := Nat.two_pow_pos p
  have ha := Nat.two_pow_pos a
  have hb := Nat.two_pow_pos b
  have hc := Nat.two_pow_pos c
  have hd := Nat.two_pow_pos d
  have hab := Nat.two_pow_pos (a + b)
  have hcd := Nat.two_pow_pos (c + d)
  omega

/-- Complete original-input list-valued native execution with charged serialization,
actual witness soundness, computed balance and simultaneous support at every compiled
prefix. No supplied output, completion, resource or witness-correctness premise is used. -/
theorem original_output_resources {m p : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s t : BitVec m) :
    let W := globalWidth m p as.length bs.length cs.length ds.length
    let L := compactSearchLayout m p as.length bs.length cs.length ds.length
    let K := compactCounterLayout m p as.length bs.length cs.length ds.length
    let x : Data 40 := Data.init (quarterInput as bs cs ds)
    ∃ out : Option (List Bool), ∃ y n ts,
      n ≤ globalTime p as.length bs.length cs.length ds.length +
        outputTime as.length bs.length cs.length ds.length ∧
      TraceExec W (dissectionOutput L K s t) x y n ts ∧
      ExecutesList W ((dissectionOutput L K s t).program Output.result) ⟨0, x⟩
        (OutputCodec.encode out) (n + 1) ∧
      outputList y.mem (y.regs Output.result) = OutputCodec.encode out ∧
      (out = none ↔ ¬Solvable ((as ++ bs) ++ (cs ++ ds)) s t) ∧
      (∀ ops, out = some ops → ops.length = totalLength as bs cs ds ∧
        eval (ops.zip ((as ++ bs) ++ (cs ++ ds))) s = t) ∧
      y.regs balance = computedBalance (p := p) as bs cs ds s t ∧
      (∀ k u, k ≤ n → Runs W ((dissectionOutput L K s t).program Output.result) ⟨0, x⟩ u k →
        u.data.SupportLe (peakCells p as.length bs.length cs.length ds.length
          (computedBalance (p := p) as bs cs ds s t) +
          outputTime as.length bs.length cs.length ds.length) ∧ u.data.Bounded W) ∧
      (∀ addr v, Probe.read addr v ∈ ts ∨ Probe.write addr v ∈ ts → Fits W addr ∧ Fits W v) ∧
      OutputCodec.decoder.toTM.ComputesInTimeAndSpace
        (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encNat
          (outputList y.mem (y.regs Output.result)))
        (Turing.MultiTapeTM.encOption Turing.MultiTapeTM.encBits out)
        (6 * totalLength as bs cs ds + 9) 0 := by
  dsimp only
  obtain ⟨raw, hpre, hsuf⟩ := quarterInput_raw (p := p) as bs cs ds
  obtain ⟨fit, load⟩ := compactSearchLayout_fits m p as.length bs.length cs.length ds.length
  obtain ⟨u, _, core, hit, miss, sound, mu, _⟩ :=
    dissection_global_exec hp as bs cs ds s t _ _ _ raw hpre hsuf fit load
  have start : (Data.init (quarterInput as bs cs ds) : Data 40).Bounded
      (globalWidth m p as.length bs.length cs.length ds.length) :=
    Data.Bounded.init (quarterInput_fits (p := p) as bs cs ds)
  have ubounded := core.execWithin.bounded start
  obtain ⟨y, output, list, pointer, live, _⟩ := Output.exec u ubounded
    (compact_output_fits m p as.length bs.length cs.length ds.length)
  let out : Option (List Bool) := if u.regs tag = 0 then none
    else some (Output.operators as.length bs.length cs.length ds.length u)
  have actualOutput : outputList y.mem (y.regs Output.result) = OutputCodec.encode out := by
    rw [pointer, list, OutputCodec.native_output]
  have finalMu : y.regs balance = computedBalance (p := p) as bs cs ds s t :=
    (live _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))).trans mu
  have event : (∃ g : BitVec p, PackedClassSolution as bs cs ds s t g) ↔
      Solvable ((as ++ bs) ++ (cs ++ ds)) s t :=
    (exists_congr (fun g => packedClassSolution_iff_meets hp as bs cs ds s t g)).trans
      (Dissection.exists_meets_iff hp as bs cs ds s t)
  have absent : out = none ↔ ¬Solvable ((as ++ bs) ++ (cs ++ ds)) s t := by
    dsimp only [out]
    rw [ite_eq_iff]
    simp only [and_true, reduceCtorEq, and_false, or_false]
    exact miss.trans (not_congr event)
  have witness (ops : List Bool) (h : out = some ops) :
      ops.length = totalLength as bs cs ds ∧ eval (ops.zip ((as ++ bs) ++ (cs ++ ds))) s = t := by
    have tag : u.regs tag ≠ 0 := by
      intro hz
      simp only [out, hz, ↓reduceIte, reduceCtorEq] at h
    have eqops : Output.operators as.length bs.length cs.length ds.length u = ops := by
      simpa only [out, tag, ↓reduceIte, Option.some.injEq] using h
    rw [← eqops]
    exact ⟨Output.operators_length _ _ _ _ _, by rw [Output.operators_zip]; exact sound tag⟩
  have space := output.stores.space core.finish
  have all := (core.mono le_rfl (Nat.le_add_right _
    (7 * (as.length + bs.length + cs.length + ds.length) + 53))).seq space
  obtain ⟨n, hn, he, hs⟩ := all
  obtain ⟨ts, trace⟩ := he.exists_trace
  refine ⟨out, y, n, ts, hn, trace, ?_, actualOutput, absent, witness, finalMu, ?_,
    trace.probe_bounded start, ?_⟩
  · simpa only [actualOutput, dissectionOutput] using he.executesList Output.result
  · intro k z hk hz
    have support := hs.prefix Output.result hz hk
    rw [dissectionSpace_eq_peakCells] at support
    exact ⟨support, hz.bounded start⟩
  · have length : out.elim 0 List.length ≤ totalLength as bs cs ds := by
      cases hout : out with
      | none => exact Nat.zero_le _
      | some ops => exact (witness ops hout).1.le
    have tm := OutputCodec.decoder_computes_linear out
    rw [actualOutput]
    have result : OutputCodec.decoder.toTM.ComputesInTimeAndSpace (OutputCodec.wire out)
        (Turing.MultiTapeTM.encOption Turing.MultiTapeTM.encBits out)
        (6 * totalLength as bs cs ds + 9) 0 :=
      ⟨tm.1, tm.2.1.mono (by omega), tm.2.2⟩
    simpa only [OutputCodec.wire] using result

end Cslib.Cryptanalysis.AddXNOR.Native.Driver
