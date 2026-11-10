/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORCounterDPResources
import all CslibFrontier.Cryptanalysis.AddXNORCounterDPResources
import all CslibFrontier.Computability.GenericRAM.Native.Combinators
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Full-width input projection and reachable-state counting

The machine reads the original full-width seed/target and operand tape, computes
its capped low-bit depth, projects every word by binary remainder, then executes
the approved complete counter DP. Projection, materialization and readback are
charged. The input is not an already-projected instance or a supplied table.

## Main definitions

* `prepare`: actual original-to-projected input transformation.
* `runCertificate`: uniform projection followed by the installed counter DP.

## Main results

* `prepare_words`, `run_classes`: exact original low-bit class counts in both directions.
* `source_certificate`: actual bit time and every-prefix workspace, including projection.

This composes the low-bit counting route of [WangLvShenZhang2027], Lemma 8,
PDF pp. 21–22. The source quarter/balance-prepass composition is separate.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.CounterProjection
open Turing.MultiTapeTM Cslib.GenericRAM

/-- Requested unary low-bit depth and the original direction/full-width chain. -/
abbrev Input := ℕ × CounterDP.Input

/-- Frame the unary requested depth before the direction/full-width original-input encoding. -/
abbrev encoding : Input ↪ List Bool := encPair encUnary CounterDP.encoding

/-- Runtime class depth, capped by the original physical word width. -/
def depth (input : Input) : ℕ :=
  let (requested, (_, ((width, _), _))) := input
  min requested width

/-- Project the original seed/target and every original operand inside the machine. -/
def prepare (input : Input) : CounterDP.Input :=
  let (_, (inverse, ((_, seed), operands))) := input
  let p := depth input
  let modulus := 2^p
  (inverse, ((p, seed % modulus), operands.map (· % modulus)))

/-- Execute projection and the original-input forward/reverse counter DP. -/
def run (input : Input) : List (ℕ × ℕ) := CounterDP.run (prepare input)

/-- Original words carry their full physical width; no projected words are endpoint inputs. -/
def ofWords {m : ℕ} (p : ℕ) (inverse : Bool) (seed : BitVec m)
    (operands : List (BitVec m)) : Input :=
  (p, CounterDP.ofWords inverse seed operands)

/-- The actual modular map uses the existing binary-arithmetic and map-with-input machines. -/
theorem prepare_polyTime : ComputableInPolyTime prepare encoding CounterDP.encoding := by
  have hd : ComputableInPolyTime depth encoding encUnary := by unfold depth; fun_prop
  have modulus := ComputableInPolyTime.binary_pow' (.const 2) hd
  have seed : ComputableInPolyTime (fun q : Input => q.2.2.1.2) encoding encNat := by fun_prop
  have operands : ComputableInPolyTime (fun q : Input => q.2.2.2) encoding
      (encList encNat) := by fun_prop
  have reduced := ComputableInPolyTime.binary_mod.comp (seed.prod modulus)
  have row : ComputableTidilyInPolyTime
      (fun q : Input × ℕ => q.2 % 2^(depth q.1)) (encPair encoding encNat) encNat :=
    (ComputableInPolyTime.binary_mod.comp
      ((ComputableInPolyTime.snd encoding encNat).prod
        (modulus.comp (ComputableInPolyTime.fst encoding encNat)))).tidy
  have mapped := operands.tidy.mapWithInput (encB := encNat)
    (f := fun input a => a % 2^(depth input)) row
  have direction : ComputableInPolyTime (fun q : Input => q.2.1) encoding encBool := by fun_prop
  exact (direction.prod ((hd.prod reduced).prod mapped.computableInPolyTime)).of_enc_eq
    (encD := CounterDP.encoding) (fun _ => rfl)

/-- Scalar preprocessing charges the original tape and every projected intermediate value. -/
noncomputable def prepareCertificate : NativeCertificate prepare encoding CounterDP.encoding :=
  .ofPolyTime prepare_polyTime

/-- One fixed machine projects the runtime input, then executes the complete counting DP. -/
noncomputable def runCertificate : NativeCertificate run encoding encNatPairList :=
  CounterDP.runCertificate.comp prepareCertificate

/-- Actual projection equals the typed low-bit instance, at every requested depth. -/
theorem prepare_words {m : ℕ} (p : ℕ) (inverse : Bool) (seed : BitVec m)
    (as : List (BitVec m)) :
    prepare (ofWords p inverse seed as) = CounterDP.ofWords inverse
      (seed.setWidth (min p m)) (as.map (BitVec.setWidth (min p m))) := by
  simp [prepare, ofWords, depth, CounterDP.ofWords, BitVec.toNat_setWidth, List.map_map,
    Function.comp_def]

/-- The complete output tape contains exactly every original low-bit class population.
Only the source's admitted projection depth is assumed, never a projected input/count table. -/
theorem run_classes {m p n : ℕ} (hp : p ≤ m) (as : Fin n → BitVec m)
    (seed : BitVec m) (inverse : Bool) :
    run (ofWords p inverse seed (List.ofFn as)) = List.ofFn (fun g : Fin (2^p) =>
      (g.val, if inverse then backwardClassCount p as seed (BitVec.ofFin g)
        else forwardClassCount p as seed (BitVec.ofFin g))) := by
  rw [run, prepare_words, Nat.min_eq_left hp, CounterDP.run_words]
  simp only [List.map_ofFn, CounterPull.graph]
  apply congrArg List.ofFn
  funext g
  cases inverse
  · exact congrArg (fun n => (g.val, n))
      (WordTable.projected_classCounters hp as seed (BitVec.ofFin g))
  · exact congrArg (fun n => (g.val, n))
      (WordTable.projected_backwardCounters hp as seed (BitVec.ofFin g))

/-- The actual projected-input machine has source-derived bit time and charged peak workspace.
The polynomial is in the original full-width encoded input; no scalar projection cost is hidden.
The depth cap is derived by the program, so the resource theorem needs no depth restriction. -/
theorem source_certificate : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ∀ m p (as : List (BitVec m)) (seed : BitVec m) (inverse : Bool),
      runCertificate.time (ofWords p inverse seed as) ≤
        2^(min p m)*P ((encoding (ofWords p inverse seed as)).length+1) ∧
      runCertificate.space (ofWords p inverse seed as) ≤
        2^(min p m)*P ((encoding (ofWords p inverse seed as)).length+1) := by
  obtain ⟨Q, hpQ, mQ, hQ⟩ := CounterDP.source_certificate
  obtain ⟨R, hpR, mR, hR⟩ := exists_mono_poly
    ((NativeCertificate.ofPolyTime_isPolynomial prepare_polyTime).1.add
      (NativeCertificate.ofPolyTime_isPolynomial prepare_polyTime).2)
  let P := fun b => R b+Q (2*b+1)
  have hp : Cslib.PolynomiallyBounded P := by dsimp only [P]; fun_prop
  have mp : Monotone P := by
    intro a b h
    exact Nat.add_le_add (mR h) (mQ (by omega))
  refine ⟨P, hp, mp, ?_⟩
  intro m p as seed inverse
  let input := ofWords p inverse seed as
  let I := (encoding input).length
  have mI : m ≤ I := by
    simp only [I, input, ofWords, CounterDP.ofWords, CounterDP.encoding,
      SortedQuarterMachine.encoding, length_encPair, encUnary_apply, List.length_replicate,
      encBool_apply, List.length_singleton]
    omega
  have nI : as.length ≤ I := by
    have hl := length_le_length_encList encNat (as.map BitVec.toNat)
    simp only [List.length_map] at hl
    simp only [I, input, ofWords, CounterDP.ofWords, CounterDP.encoding,
      SortedQuarterMachine.encoding, length_encPair]
    omega
  have scalar : min p m+(as.map (BitVec.setWidth (min p m))).length+1 ≤ 2*(I+1)+1 := by
    rw [List.length_map]
    omega
  have dp := hQ (min p m) (as.map (BitVec.setWidth (min p m)))
    (seed.setWidth (min p m)) inverse
  have prep := (hR input).trans (mR (Nat.le_succ I))
  change prepareCertificate.time input+prepareCertificate.space input ≤ R (I+1) at prep
  have positive : 1 ≤ 2^(min p m) := Nat.one_le_two_pow
  have copied := Nat.mul_le_mul_left (R (I+1)) positive
  have counter := Nat.mul_le_mul_left (2^(min p m)) (mQ scalar)
  constructor <;>
    simp only [runCertificate, NativeCertificate.comp, prepare_words]
  · dsimp only [P]
    nlinarith only [dp.1, counter, prep, copied]
  · dsimp only [P]
    nlinarith only [dp.2, counter, prep, copied]

end Cslib.Cryptanalysis.AddXNOR.CounterProjection
