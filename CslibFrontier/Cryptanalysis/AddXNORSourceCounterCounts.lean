/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORCounterProjection
public import CslibFrontier.Cryptanalysis.AddXNORSource
import all CslibFrontier.Cryptanalysis.AddXNORCounterProjection
import all CslibFrontier.Cryptanalysis.AddXNORSource
import all CslibFrontier.Cryptanalysis.AddXNORProgramGeneration
import all CslibFrontier.Cryptanalysis.AddXNORBitInput
import all CslibFrontier.Computability.GenericRAM.Native.Combinators

/-!
# Both low-bit count tables from the original source instance

Compute the source cut, capped depth, first-operand seed and zero target from the
original full-width operand tape. Project and execute both actual counter DPs
before generating any full-state class list. Both dense count arrays and all
preparation/projection/DP/output temporaries are charged simultaneously.

## Main definitions

* `task`: one original half-chain, selected before projection and counting.
* `runCertificate`: actual full-width preparation and both low-bit count machines.

## Main results

* `task_words`, `run_words`, `side_classes`: exact original class counts in both directions.
* `source_certificate`: $O^*(2^d)$ bit time/peak space for computed depth `d`.
* `quarter_certificate`: $O^*(2^k)$ before full-state class enumeration, since `d ≤ k`.

Source: [WangLvShenZhang2027], Lemma 8/Theorem 7, PDF pp. 21–22.
The scalar balance scan and installation into the dissection solver remain separate.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.SourceCounterCounts
open Turing.MultiTapeTM Cslib.GenericRAM

/-- The two dense keyed count arrays; these contain counters, not full-state class lists. -/
abbrev Counts := List (ℕ × ℕ) × List (ℕ × ℕ)

/-- Frame the forward array before the unframed backward array, using existing list encodings. -/
abbrev countEncoding : Counts ↪ List Bool := encPair encNatPairList encNatPairList

private def select (source : ProgramGeneration.Source) (inverse : Bool) : CounterProjection.Input :=
  let (((width, p), (seed, target)), ((first, second), (third, fourth))) := source
  (p, (inverse, ((width, if inverse then target else seed),
    if inverse then third ++ fourth else first ++ second)))

/-- Select the actual forward prefix or inverse suffix from the original source input. -/
def task (input : Source.Input) (inverse : Bool) : CounterProjection.Input :=
  select (Source.prepare input) inverse

/-- Scalar source preparation, quarter concatenation and direction selection are actual machines. -/
theorem task_polyTime (inverse : Bool) : ComputableInPolyTime (fun input => task input inverse)
    Source.encoding CounterProjection.encoding := by
  have selected : ComputableInPolyTime (fun source => select source inverse)
      ProgramGeneration.sourceEncoding CounterProjection.encoding := by
    unfold select
    cases inverse <;> fun_prop
  exact selected.comp Source.prepare_polyTime

/-- All original scalar/cut/operand materialization is charged before a projected table exists. -/
noncomputable def taskCertificate (inverse : Bool) : NativeCertificate
    (fun input => task input inverse) Source.encoding CounterProjection.encoding :=
  .ofPolyTime (task_polyTime inverse)

/-- Execute the projected DP on the original selected half-chain. -/
def side (input : Source.Input) (inverse : Bool) : List (ℕ × ℕ) :=
  CounterProjection.run (task input inverse)

/-- Forward and backward count arrays, computed without enumerating either half space. -/
def run (input : Source.Input) : Counts := (side input false, side input true)

/-- One uniform machine for actual source preparation, projection and both count tables. -/
noncomputable def runCertificate : NativeCertificate run Source.encoding countEncoding :=
  (CounterProjection.runCertificate.comp (taskCertificate false)).prod
    (CounterProjection.runCertificate.comp (taskCertificate true))

/-- The source forward half, in original operator order. -/
def forwardOperands {α : Type} (tail : List α) : List α :=
  let ((first, second), _) := Source.quarters tail
  first ++ second

/-- The complete source suffix, including the residual fourth-quarter operands. -/
def backwardOperands {α : Type} (tail : List α) : List α :=
  let (_, (third, fourth)) := Source.quarters tail
  third ++ fourth

/-- Exact source-half input before its actual modular projection. The first operand is the
forward seed; the inverse target is zero; the last quarter includes every residual operand. -/
theorem task_words {m : ℕ} (p : ℕ) (a : BitVec m) (tail : List (BitVec m)) (inverse : Bool) :
    task (Source.ofWords p a tail) inverse =
      CounterProjection.ofWords (min p (min m (tail.length/4))) inverse
        (if inverse then 0 else a)
        (if inverse then backwardOperands tail else forwardOperands tail) := by
  cases inverse <;>
    simp [task, select, Source.prepare_ofWords, CounterProjection.ofWords, CounterDP.ofWords,
      ProgramGeneration.originalSource, BitInput.words, List.map_append,
      forwardOperands, backwardOperands]

/-- Output tape semantics, retaining all projected states and multiplicities for both halves. -/
theorem run_words {m : ℕ} (p : ℕ) (a : BitVec m) (tail : List (BitVec m)) :
    let d := min p (min m (tail.length/4))
    let left := (forwardOperands tail).map (BitVec.setWidth d)
    let right := (backwardOperands tail).map (BitVec.setWidth d)
    run (Source.ofWords p a tail) =
      (CounterPull.graph (WordTable.classCounters left (a.setWidth d)).read,
        CounterPull.graph (WordTable.backwardCounters right ((0 : BitVec m).setWidth d)).read) := by
  have dm : min p (min m (tail.length/4)) ≤ m :=
    (Nat.min_le_right _ _).trans (Nat.min_le_left _ _)
  simp only [run, side, task_words, CounterProjection.run]
  rw [CounterProjection.prepare_words, Nat.min_eq_left dm,
    CounterProjection.prepare_words, Nat.min_eq_left dm]
  simp only [CounterDP.run_words, Bool.false_eq_true, ite_false, ite_true]

/-- Every output counter is the original full-width half-chain's actual low-bit class size.
The semantic class populations are derived from the executed projection/DP route. -/
theorem side_classes {m : ℕ} (p : ℕ) (a : BitVec m) (tail : List (BitVec m))
    (inverse : Bool) :
    let d := min p (min m (tail.length/4))
    let half := if inverse then backwardOperands tail else forwardOperands tail
    let seed := if inverse then 0 else a
    side (Source.ofWords p a tail) inverse = List.ofFn (fun g : Fin (2^d) =>
      (g.val, if inverse then backwardClassCount d (fun i : Fin half.length => half[i.val])
        seed (BitVec.ofFin g)
        else forwardClassCount d (fun i : Fin half.length => half[i.val])
          seed (BitVec.ofFin g))) := by
  dsimp only
  rw [side, task_words]
  have dm : min p (min m (tail.length/4)) ≤ m :=
    (Nat.min_le_right _ _).trans (Nat.min_le_left _ _)
  have h := CounterProjection.run_classes dm
    (fun i : Fin (if inverse then backwardOperands tail else forwardOperands tail).length =>
      (if inverse then backwardOperands tail else forwardOperands tail)[i.val])
    (if inverse then 0 else a) inverse
  simpa only [List.ofFn_getElem] using h

/-- Both installed count machines have a source-derived exponential factor only in computed
projection depth, with polynomial overhead in the actual full-width original input wire. -/
theorem source_certificate : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ∀ m p (a : BitVec m) (tail : List (BitVec m)),
      runCertificate.time (Source.ofWords p a tail) ≤
        2^(min p (min m (tail.length/4)))*
          P ((Source.encoding (Source.ofWords p a tail)).length+1) ∧
      runCertificate.space (Source.ofWords p a tail) ≤
        2^(min p (min m (tail.length/4)))*
          P ((Source.encoding (Source.ofWords p a tail)).length+1) := by
  obtain ⟨Q, hpQ, mQ, hQ⟩ := CounterProjection.source_certificate
  have estimate (inverse : Bool) : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
      ∀ m p (a : BitVec m) (tail : List (BitVec m)),
        (CounterProjection.runCertificate.comp (taskCertificate inverse)).time
          (Source.ofWords p a tail) ≤
            2^(min p (min m (tail.length/4)))*P
              ((Source.encoding (Source.ofWords p a tail)).length+1) ∧
        (CounterProjection.runCertificate.comp (taskCertificate inverse)).space
          (Source.ofWords p a tail) ≤
            2^(min p (min m (tail.length/4)))*P
              ((Source.encoding (Source.ofWords p a tail)).length+1) := by
    obtain ⟨R, hpR, mR, hR⟩ := exists_mono_poly
      ((NativeCertificate.ofPolyTime_isPolynomial (task_polyTime inverse)).1.add
        (NativeCertificate.ofPolyTime_isPolynomial (task_polyTime inverse)).2)
    obtain ⟨L, hpL, mL, hL⟩ := exists_mono_poly (task_polyTime inverse).polyBounded_length
    let P := fun b => R b+Q (L b+1)
    have hp : Cslib.PolynomiallyBounded P := by dsimp only [P]; fun_prop
    have mp : Monotone P := fun _ _ h => Nat.add_le_add (mR h)
      (mQ (Nat.add_le_add_right (mL h) 1))
    refine ⟨P, hp, mp, ?_⟩
    intro m p a tail
    let input := Source.ofWords p a tail
    let d := min p (min m (tail.length/4))
    let words := if inverse then backwardOperands tail else forwardOperands tail
    let seed := if inverse then (0 : BitVec m) else a
    have dp := hQ m d words seed inverse
    have dm : d ≤ m := (Nat.min_le_right _ _).trans (Nat.min_le_left _ _)
    rw [Nat.min_eq_left dm] at dp
    have ht := (hR input).trans (mR (Nat.le_succ (Source.encoding input).length))
    have hl := (hL input).trans (mL (Nat.le_succ (Source.encoding input).length))
    have scalar := Nat.mul_le_mul_left (2^d) (mQ (Nat.add_le_add_right hl 1))
    have copied := Nat.mul_le_mul_left (R ((Source.encoding input).length+1))
      (show 1 ≤ 2^d from Nat.one_le_two_pow)
    change (taskCertificate inverse).time input+(taskCertificate inverse).space input ≤ _ at ht
    rw [task_words] at hl scalar
    constructor <;> simp only [NativeCertificate.comp, task_words]
    · dsimp only [P]
      nlinarith only [dp.1, scalar, ht, copied]
    · dsimp only [P]
      nlinarith only [dp.2, scalar, ht, copied]
  obtain ⟨A, hpA, mA, hA⟩ := estimate false
  obtain ⟨B, hpB, mB, hB⟩ := estimate true
  refine ⟨fun b => A b+B b, hpA.add hpB, mA.add mB, fun m p a tail => ?_⟩
  have hf := hA m p a tail
  have hb := hB m p a tail
  exact ⟨(Nat.add_le_add hf.1 hb.1).trans_eq (by ring),
    (Nat.add_le_add hf.2 hb.2).trans_eq (by ring)⟩

/-- Before any full-state class list is produced, both all-count tables fit the source quarter
clock and peak workspace. The capped depth, rather than a supplied runtime inequality, gives it. -/
theorem quarter_certificate : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ∀ m p (a : BitVec m) (tail : List (BitVec m)),
      runCertificate.time (Source.ofWords p a tail) ≤
        2^(tail.length/4)*P ((Source.encoding (Source.ofWords p a tail)).length+1) ∧
      runCertificate.space (Source.ofWords p a tail) ≤
        2^(tail.length/4)*P ((Source.encoding (Source.ofWords p a tail)).length+1) := by
  obtain ⟨P, hp, mp, bound⟩ := source_certificate
  refine ⟨P, hp, mp, fun m p a tail => ?_⟩
  have power := Nat.pow_le_pow_right (by decide : 1 ≤ 2)
    (show min p (min m (tail.length/4)) ≤ tail.length/4 from
      (Nat.min_le_right _ _).trans (Nat.min_le_right _ _))
  have scaled := Nat.mul_le_mul_right
    (P ((Source.encoding (Source.ofWords p a tail)).length+1)) power
  exact ⟨(bound m p a tail).1.trans scaled, (bound m p a tail).2.trans scaled⟩

end Cslib.Cryptanalysis.AddXNOR.SourceCounterCounts
