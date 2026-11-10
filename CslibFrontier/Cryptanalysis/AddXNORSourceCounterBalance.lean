/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORCounterBalanceScan
import all CslibFrontier.Cryptanalysis.AddXNORCounterBalanceScan
import all CslibFrontier.Cryptanalysis.AddXNORSourceCounterCounts
import all CslibFrontier.Cryptanalysis.AddXNORCounterDP
import all CslibFrontier.Cryptanalysis.AddXNORClasses
import all CslibFrontier.Computability.GenericRAM.Native.Combinators
import Mathlib.Data.List.OfFn

/-!
# Source balance from the actual all-count prepass

Project the original full-width half chains, execute both counter DPs, align the
numeric-key arrays and reduce their binary minima into the balance scalar.
No count/balance table, execution conclusion or runtime bound is input.

## Main results

* `run_words`: exact maximum of the two actual projected counter populations.
* `source_certificate`: actual quarter-time bit execution and every-prefix workspace.

This realizes the balance computation in [WangLvShenZhang2027], Theorem 7,
PDF pp. 21–22. `DPDissection` installs this prepass before the approved search.
`BalanceCompatibility` identifies the returned scalar with the search envelope's balance.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.SourceCounterBalance
open Turing.MultiTapeTM Cslib.GenericRAM

/-- Source preparation computes the actual capped class depth. -/
def depth (input : Source.Input) : ℕ :=
  let (((_, p), _), _) := Source.prepare input
  p

private theorem depth_polyTime : ComputableInPolyTime depth Source.encoding encUnary := by
  have projection : ComputableInPolyTime
      (fun q : ProgramGeneration.Source => q.1.1.2) ProgramGeneration.sourceEncoding encUnary := by
    fun_prop
  exact projection.comp Source.prepare_polyTime

/-- Scalar balance after the original-input DP count prepass and the actual tagged scan. -/
def run (input : Source.Input) : ℕ :=
  CounterBalanceScan.run (depth input, SourceCounterCounts.run input)

/-- The original source tape drives one uniform native prepass; all count arrays are released
by its scalar output. Actual preparation, sorting, pairing and scalar/control tapes are charged. -/
noncomputable def runCertificate : NativeCertificate run Source.encoding encNat :=
  CounterBalanceScan.runCertificate.comp
    ((NativeCertificate.ofPolyTime depth_polyTime).prod SourceCounterCounts.runCertificate)

private theorem depth_words {m : ℕ} (p : ℕ) (a : BitVec m) (tail : List (BitVec m)) :
    depth (Source.ofWords p a tail) = min p (min m (tail.length/4)) := by
  simp [depth, Source.prepare_ofWords, ProgramGeneration.originalSource]

/-- The scalar comes from both actual DP tables, including every residual suffix operand. -/
theorem run_words {m : ℕ} (p : ℕ) (a : BitVec m) (tail : List (BitVec m)) :
    let d := min p (min m (tail.length/4))
    let left := (SourceCounterCounts.forwardOperands tail).map (BitVec.setWidth d)
    let right := (SourceCounterCounts.backwardOperands tail).map (BitVec.setWidth d)
    run (Source.ofWords p a tail) = Finset.univ.sup (fun g : BitVec d =>
      min ((WordTable.classCounters left (a.setWidth d)).read g)
        ((WordTable.backwardCounters right ((0 : BitVec m).setWidth d)).read g)) := by
  rw [run, depth_words, SourceCounterCounts.run_words, CounterBalanceScan.run_graphs]

/-- Exact source balance, deriving all class populations from the original half chains. -/
theorem run_eq_classBalance {m : ℕ} (p : ℕ) (a : BitVec m) (tail : List (BitVec m)) :
    let d := min p (min m (tail.length/4))
    let left := SourceCounterCounts.forwardOperands tail
    let right := SourceCounterCounts.backwardOperands tail
    run (Source.ofWords p a tail) = classBalance d
      (fun i : Fin left.length => left[i.val]) (fun i : Fin right.length => right[i.val]) a 0 := by
  rw [run_words]
  have dm : min p (min m (tail.length/4)) ≤ m :=
    (Nat.min_le_right _ _).trans (Nat.min_le_left _ _)
  have h := WordTable.computed_balance dm
    (fun i : Fin (SourceCounterCounts.forwardOperands tail).length =>
      (SourceCounterCounts.forwardOperands tail)[i.val])
    (fun i : Fin (SourceCounterCounts.backwardOperands tail).length =>
      (SourceCounterCounts.backwardOperands tail)[i.val]) a 0
  simpa only [List.ofFn_getElem_eq_map, WordTable.maxMin_eq_sup] using h

/-- The faster original-input scalar balance prepass has an actual uniform quarter-time and
peak-space certificate, including count arrays and every internal bit-machine temporary. -/
theorem source_certificate : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ∀ m p (a : BitVec m) (tail : List (BitVec m)),
      runCertificate.time (Source.ofWords p a tail) ≤
        2^(tail.length/4)*P ((Source.encoding (Source.ofWords p a tail)).length+1) ∧
      runCertificate.space (Source.ofWords p a tail) ≤
        2^(tail.length/4)*P ((Source.encoding (Source.ofWords p a tail)).length+1) := by
  obtain ⟨A, hpA, mA, hA⟩ := CounterBalanceScan.runCertificate_bounds
  obtain ⟨Q, hpQ, mQ, hQ⟩ := SourceCounterCounts.quarter_certificate
  obtain ⟨R, hpR, mR, hR⟩ := exists_mono_poly_cert depth_polyTime
  let P := fun I => Q I+R I+A (2*I+2)
  have hp : Cslib.PolynomiallyBounded P := by dsimp only [P]; fun_prop
  have mp : Monotone P := fun _ _ h => Nat.add_le_add
    (Nat.add_le_add (mQ h) (mR h)) (mA (by omega))
  refine ⟨P, hp, mp, ?_⟩
  intro m p a tail
  let input := Source.ofWords p a tail
  let I := (Source.encoding input).length
  let d := min p (min m (tail.length/4))
  let left := (SourceCounterCounts.forwardOperands tail).map (BitVec.setWidth d)
  let right := (SourceCounterCounts.backwardOperands tail).map (BitVec.setWidth d)
  have halfLengths : left.length ≤ tail.length ∧ right.length ≤ tail.length := by
    have h := congrArg List.length (Source.quarters_append tail)
    change (SourceCounterCounts.forwardOperands tail ++
      SourceCounterCounts.backwardOperands tail).length = tail.length at h
    rw [List.length_append] at h
    dsimp only [left, right]
    simp only [List.length_map]
    omega
  have counter (as : List (BitVec d)) (seed : BitVec d) (inv : Bool)
      (len : as.length ≤ tail.length) (s : BitVec d) :
      Nat.size ((if inv then WordTable.backwardCounters as seed
        else WordTable.classCounters as seed).read s) ≤ tail.length+1 :=
    (CounterDP.counter_size as seed inv s).trans (by omega)
  have hf (s : BitVec d) : Nat.size ((WordTable.classCounters left (a.setWidth d)).read s) ≤
      tail.length+1 := counter left _ false halfLengths.1 s
  have hb (s : BitVec d) : Nat.size ((WordTable.backwardCounters right
      ((0 : BitVec m).setWidth d)).read s) ≤ tail.length+1 := counter right _ true halfLengths.2 s
  have scan := hA _ _ hf hb
  have dm : d ≤ m := (Nat.min_le_right _ _).trans (Nat.min_le_left _ _)
  have inputSize : m+tail.length ≤ 2*I := by
    have h := length_le_length_encList encNat ((a::tail).map BitVec.toNat)
    simp only [List.length_map, List.length_cons] at h
    simp only [I, input, Source.encoding, Source.ofWords, length_encPair,
      encUnary_apply, List.length_replicate]
    omega
  have scalar := Nat.mul_le_mul_left (2^d) (mA (by omega : d+(tail.length+1)+1 ≤ 2*(I+1)+2))
  have power := Nat.pow_le_pow_right (by decide : 1 ≤ 2)
    (show d ≤ tail.length/4 from (Nat.min_le_right _ _).trans (Nat.min_le_right _ _))
  have scaled := Nat.mul_le_mul_right (A (2*(I+1)+2)) power
  have prep := hR input
  have prepBound := mR (Nat.le_succ I)
  have copied := Nat.mul_le_mul_left (R (I+1))
    (show 1 ≤ 2^(tail.length/4) from Nat.one_le_two_pow)
  have counts := hQ m p a tail
  constructor <;>
    simp only [runCertificate, NativeCertificate.comp, NativeCertificate.prod,
      depth_words, SourceCounterCounts.run_words]
  · dsimp only [P]
    nlinarith only [scan.1, scalar, scaled, prep.1, prepBound, copied, counts.1]
  · dsimp only [P]
    nlinarith only [scan.2, scalar, scaled, prep.2, prepBound, copied, counts.2]

end Cslib.Cryptanalysis.AddXNOR.SourceCounterBalance
