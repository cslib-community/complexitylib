/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORNativeGlobalLayout
import all Complexity.Cryptanalysis.AddXNORNativeGlobalLayout
import all Complexity.Cryptanalysis.AddXNORNativeGlobalTime
import all Complexity.Cryptanalysis.AddXNORNativeDissection
import all Complexity.Cryptanalysis.AddXNORNativeClassCounts
import all Complexity.Cryptanalysis.AddXNORNativeOrientedSearch

/-!
# Original-input native dissection time and simultaneous peak space

The fixed native program constructs both counter tables, computes their balance,
selects either actual class construction, streams the opposite side, releases the
dictionary on hits and misses, and controls the outer loop. Every continuing
compiled prefix has a simultaneous occupied-cell bound in the computed balance.
The bound resets at each empty-dictionary boundary; historical allocations and
class means are not used as a peak-space surrogate.

This supplies standard WordRAM resource components of [WangLvShenZhang2027],
Lemma 8/Theorem 7, PDF pp. 21–22. The source split has quarter lengths
`k, k, k, q - 3*k` and `p ≤ k`. All lengths and `p` are explicit below. The bound
charges native preprocessing, projection, arrays, dictionary construction/release,
both search directions, loop control and halt. Four packed witness words reside
in the charged register bank. Decoding them is a mathematical output observer;
a native variable-length output serializer is not supplied.

This is not the source sorted-list multitape bit algorithm. Input placement is
RAM initialization; seeds, lengths and width remain scalar program parameters.
The program graph is fixed, while encoded immediates and a uniform header decoder
remain separate. Multiplying occupied words by physical width accounts for word
contents, not for an implementation or bit-time simulation of random access.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Driver

open Cslib.WordRAM Quarter

/-- Simultaneously occupied memory words. The counter work is charged once;
the lifetime allowance uses the largest actual smaller class, not a class mean. -/
def peakCells (p a b c d μ : ℕ) : ℕ :=
  1 + 2 * (a + b + c + d) + 2 * (b + c) + 6 * 2 ^ p + 6 * (2 ^ a + 2 ^ d) +
    prepareTime p (a + b) (c + d) +
    workFactor (a + b + c + d) * (quarterWork p a b c d + μ)

/-- For the source split the simultaneous word bound is polynomial in total
operand count times the quarter enumeration plus the actual computed balance. -/
theorem peakCells_quarters {p k r μ : ℕ} (hp : p ≤ k) :
    peakCells p k k k (k + r) μ ≤ 1000 * (4 * k + r + 1) * (2 ^ (k + r) + μ) := by
  let E := 2 ^ (k + r)
  let C := workFactor (k + k + k + (k + r))
  have hN : 2 ^ p ≤ E := Nat.pow_le_pow_right (by decide) (by omega)
  have hK : 2 ^ k ≤ E := Nat.pow_le_pow_right (by decide) (by omega)
  have hE : 0 < E := Nat.two_pow_pos _
  have hQ : quarterWork p k k k (k + r) ≤ 5 * E := by
    dsimp only [quarterWork, E] at *; omega
  have hprep := prepareTime_le p (k + k) (k + (k + r))
  have hc : workFactor ((k + k) + (k + (k + r))) = C := by
    dsimp [C, workFactor]; omega
  rw [hc] at hprep
  have hpre := hprep.trans (Nat.mul_le_mul_left C hN)
  have hwork := Nat.mul_le_mul_left C (Nat.add_le_add_right hQ μ)
  have hbase : 1 + 2 * (k + k + k + (k + r)) + 2 * (k + k) +
      6 * 2 ^ p + 6 * (2 ^ k + 2 ^ (k + r)) ≤ (3 * (4 * k + r) + 19) * E := by
    dsimp only [E] at *
    nlinarith only [hN, hK, hE]
  dsimp only [peakCells]
  change _ + C * (quarterWork p k k k (k + r) + μ) ≤ _
  calc
    _ ≤ (3 * (4 * k + r) + 19) * E + C * E + C * (5 * E + μ) := by
      nlinarith only [hbase, hpre, hwork]
    _ ≤ _ := by
      dsimp only [E] at hE
      dsimp only [C, workFactor, E]
      nlinarith

/-- The abstract lifetime bound specializes to the actual compact physical layout. -/
theorem dissectionSpace_eq_peakCells {m p : ℕ}
    (as bs cs ds : List (BitVec m)) (s t : BitVec m) :
    dissectionSpace (p := p)
        (compactSearchLayout m p as.length bs.length cs.length ds.length).D as bs cs ds s t =
      peakCells p as.length bs.length cs.length ds.length
        (computedBalance (p := p) as bs cs ds s t) := by
  simp only [dissectionSpace, compactSearchLayout_dictionary, lifetimeStores,
    totalLength, peakCells]

/-- Standard initialized original-input execution, full global work and every
compiled prefix's simultaneous support, including unread input cells. Address
and word-fit conclusions follow from the constructed layout and input, not from
an assumed global resource invariant. Early exit, empty quarters, `p = 0` and
collisions are all admitted. -/
theorem original_resources {m p : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s t : BitVec m) :
    let W := globalWidth m p as.length bs.length cs.length ds.length
    let L := compactSearchLayout m p as.length bs.length cs.length ds.length
    let K := compactCounterLayout m p as.length bs.length cs.length ds.length
    let x : Data 40 := Data.init (quarterInput as bs cs ds)
    ∃ y n ts,
      n ≤ globalTime p as.length bs.length cs.length ds.length ∧
      TraceExec W (dissection L K s t) x y n ts ∧
      Executes W ((dissection L K s t).program tag) ⟨0, x⟩ (y.regs tag) (n + 1) ∧
      (y.regs tag ≠ 0 ↔ Solvable ((as ++ bs) ++ (cs ++ ds)) s t) ∧
      (y.regs tag = 0 ↔ ¬Solvable ((as ++ bs) ++ (cs ++ ds)) s t) ∧
      (y.regs tag ≠ 0 → eval (witness as bs cs ds y) s = t) ∧
      y.regs balance = computedBalance (p := p) as bs cs ds s t ∧
      (∀ k u, k ≤ n → Runs W ((dissection L K s t).program tag) ⟨0, x⟩ u k →
        u.data.SupportLe (peakCells p as.length bs.length cs.length ds.length
          (computedBalance (p := p) as bs cs ds s t)) ∧ u.data.Bounded W) ∧
      (∀ a v, Probe.read a v ∈ ts ∨ Probe.write a v ∈ ts → Fits W a ∧ Fits W v) := by
  dsimp only
  obtain ⟨raw, hpre, hsuf⟩ := quarterInput_raw (p := p) as bs cs ds
  obtain ⟨fit, load⟩ := compactSearchLayout_fits m p as.length bs.length cs.length ds.length
  obtain ⟨y, _, space, hit, miss, sound, balance, _⟩ :=
    dissection_global_exec hp as bs cs ds s t _ _ _ raw hpre hsuf fit load
  obtain ⟨n, hn, he, hs⟩ := space
  obtain ⟨ts, trace⟩ := he.exists_trace
  have bounded : (Data.init (quarterInput as bs cs ds) : Data 40).Bounded
      (globalWidth m p as.length bs.length cs.length ds.length) :=
    Data.Bounded.init (quarterInput_fits (p := p) as bs cs ds)
  have event : (∃ g : BitVec p, PackedClassSolution as bs cs ds s t g) ↔
      Solvable ((as ++ bs) ++ (cs ++ ds)) s t :=
    (exists_congr (fun g => packedClassSolution_iff_meets hp as bs cs ds s t g)).trans
      (Dissection.exists_meets_iff hp as bs cs ds s t)
  refine ⟨y, n, ts, hn, trace, he.executes tag, hit.trans event,
    miss.trans (not_congr event), sound, balance, ?_,
    trace.probe_bounded bounded⟩
  intro k u hk hu
  have hsupport := hs.prefix tag hu hk
  rw [dissectionSpace_eq_peakCells] at hsupport
  exact ⟨hsupport, hu.bounded bounded⟩

end Cslib.Cryptanalysis.AddXNOR.Native.Driver
