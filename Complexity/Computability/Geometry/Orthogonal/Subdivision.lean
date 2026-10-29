/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Foundations.Geometry.Orthogonal.Subdivision
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Primitives
public import Complexity.Computability.Geometry.Orthogonal.Encoding
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Native polynomial-time bounded orthogonal subdivision

Coordinates use the existing binary integer encoding. The per-segment step budget is unary;
enumerating an unbounded binary-coordinate segment can require exponentially many output points.
`subdivideWithin_eq_subdivide` recovers the full geometric subdivision when its budget suffices.

## Main definitions

Uses the point and route encodings from `Orthogonal.Encoding`.

## Main results

* `Cslib.Orthogonal.computableInPolyTime_subdivideWithin`: native plain polynomial-time
  computation of bounded subdivision with binary coordinates and unary budget.

## References

This bounded compiler is an original construction.
-/

@[expose] public section

namespace Cslib.Orthogonal

open Turing.MultiTapeTM

private theorem computable_length :
    ComputableInPolyTime (fun p : Point × Point => length p.1 p.2)
      (encPair encPoint encPoint) encNat := by
  unfold length encPoint
  fun_prop

private theorem computable_direction :
    ComputableInPolyTime (fun p : Point × Point => direction p.1 p.2)
      (encPair encPoint encPoint) encPoint := by
  unfold direction encPoint
  fun_prop

attribute [local fun_prop] computable_length computable_direction

private theorem computable_advance :
    ComputableInPolyTime (fun p : (Point × Point) × ℕ =>
      p.1.1 + p.2 • direction p.1.1 p.1.2)
      (encPair (encPair encPoint encPoint) encUnary) encPoint := by
  have hn : ComputableInPolyTime
      (fun p : (Point × Point) × ℕ => (p.2 : ℤ))
      (encPair (encPair encPoint encPoint) encUnary) encIntBin :=
    ComputableInPolyTime.intBin_natCast.comp
      (ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd _ _))
  have hd : ComputableInPolyTime
      (fun p : (Point × Point) × ℕ => direction p.1.1 p.1.2)
      (encPair (encPair encPoint encPoint) encUnary) encPoint := by fun_prop
  have h : ComputableInPolyTime (fun p : (Point × Point) × ℕ =>
      (p.1.1.1 + (p.2 : ℤ) * (direction p.1.1 p.1.2).1,
        p.1.1.2 + (p.2 : ℤ) * (direction p.1.1 p.1.2).2))
      (encPair (encPair encPoint encPoint) encUnary) encPoint := by
    unfold encPoint at *
    fun_prop
  exact h

attribute [local fun_prop] computable_advance

private theorem computable_consecutivePairs :
    ComputableInPolyTime List.consecutivePairs encRoute (encList (encPair encPoint encPoint)) := by
  unfold List.consecutivePairs encRoute
  fun_prop

private theorem computable_last :
    ComputableInPolyTime (fun r : Route => r.getLast?.toList) encRoute encRoute := by
  simp only [List.getLast?_eq_head?_reverse, ← List.take_one]
  unfold encRoute
  fun_prop

attribute [local fun_prop] computable_consecutivePairs computable_last

private theorem computable_prefix :
    ComputableInPolyTime (fun p : ℕ × (Point × Point) =>
      (List.range (min p.1 (length p.2.1 p.2.2))).map
        fun i => p.2.1 + i • direction p.2.1 p.2.2)
      (encPair encUnary (encPair encPoint encPoint)) encRoute := by
  have hcap : ComputableInPolyTime (fun p : ℕ × (Point × Point) =>
      min p.1 (length p.2.1 p.2.2))
      (encPair encUnary (encPair encPoint encPoint)) encUnary := by
    simpa only [Function.comp_def] using
      ComputableInPolyTime.binary_min_unary.comp
        ((ComputableInPolyTime.fst encUnary (encPair encPoint encPoint)).prod
          (computable_length.comp (ComputableInPolyTime.snd encUnary (encPair encPoint encPoint))))
  have hrange := ComputableInPolyTime.range.comp' hcap
  have hadv : ComputableInPolyTime (fun p : (ℕ × (Point × Point)) × ℕ =>
      p.1.2.1 + p.2 • direction p.1.2.1 p.1.2.2)
      (encPair (encPair encUnary (encPair encPoint encPoint)) encUnary) encPoint := by
    have hp := ComputableInPolyTime.fst (encPair encUnary (encPair encPoint encPoint)) encUnary
    have hi := ComputableInPolyTime.snd (encPair encUnary (encPair encPoint encPoint)) encUnary
    simpa only [Function.comp_def] using computable_advance.comp (hp.snd'.prod hi)
  unfold encRoute
  exact ComputableInPolyTime.mapWithInput hrange hadv

/-- Bounded unit enumeration is polynomial-time with binary coordinates and a unary budget.
No orthogonality assumption is needed for the computational certificate. Geometric correctness
for a sufficient budget is `subdivideWithin_eq_subdivide`. -/
@[fun_prop]
theorem computableInPolyTime_subdivideWithin :
    ComputableInPolyTime (fun p : ℕ × Route => subdivideWithin p.1 p.2)
      (encPair encUnary encRoute) encRoute := by
  have hedges := computable_consecutivePairs.comp' (ComputableInPolyTime.snd encUnary encRoute)
  have hproj : ComputableInPolyTime (fun p : (ℕ × Route) × (Point × Point) => (p.1.1, p.2))
      (encPair (encPair encUnary encRoute) (encPair encPoint encPoint))
      (encPair encUnary (encPair encPoint encPoint)) := by fun_prop
  have hflat : ComputableInPolyTime (fun p : ℕ × Route =>
      p.2.consecutivePairs.flatMap fun e => (List.range (min p.1 (length e.1 e.2))).map
        fun i => e.1 + i • direction e.1 e.2) (encPair encUnary encRoute) encRoute := by
    unfold encRoute
    exact ComputableInPolyTime.flatMapWithInput (encB := encPoint)
      (f := fun (p : ℕ × Route) (e : Point × Point) =>
        (List.range (min p.1 (length e.1 e.2))).map
        fun i => e.1 + i • direction e.1 e.2) hedges (computable_prefix.comp' hproj)
  have hlast := computable_last.comp' (ComputableInPolyTime.snd encUnary encRoute)
  simpa only [subdivideWithin, min_comm, Function.comp_def, encRoute] using
    ComputableInPolyTime.listAppend' hflat hlast

end Cslib.Orthogonal
