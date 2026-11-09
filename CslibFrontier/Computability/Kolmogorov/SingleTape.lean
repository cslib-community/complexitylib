/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Kolmogorov.MultiTape
public import CslibFrontier.Computability.Machines.Turing.MultiTape.SingleTape
public import CslibFrontier.Computability.Machines.Turing.SingleTape.Partrec

/-!
# Description methods of single-tape Turing machines (`SingleTapeTM`, `TM0`, `TM1`)

A binary single-tape Turing machine `tm : SingleTapeTM Bool` (or a finitely supported Mathlib
`TM0.Machine` or `TM1.Stmt` program) defines a description method for binary strings: a program
`p : List Bool` is placed on the tape as `BiTape.mk₁ p`, the clock counts steps, and once `tm`
reaches `none` with the tape in standard output form `BiTape.mk₁ x`, it outputs `x`
(`ofSingleTapeTM`, `ofTM0`, `ofTM1`).

Using `Turing.MultiTapeTM.ofSingleTapeTM` and
`Turing.MultiTapeTM.computesInTimeAndSpace_ofSingleTapeTM_of_input`, every single-tape description
method `ofSingleTapeTM tm` is simulated by the 1-work-tape multi-tape description method
`ofMultiTapeTM (MultiTapeTM.ofSingleTapeTM tm)` with **zero program overhead** (`compile := id`)
and linear time overhead `3 * |p| + 2 * t + 6` (`singleTapeSimulation`).

Furthermore, `tm.eval` is partial recursive (`Cslib.Turing.SingleTapeTM.partrec_eval`), so mapping
any computable decoder `dec : List Bool → ℕ` over `ofSingleTapeTM tm`, `ofTM0 M S hs`, or
`ofTM1 M S hs` yields a partial recursive description method (`isPartrec_ofSingleTapeTM_map`,
`isPartrec_ofTM0_map`, `isPartrec_ofTM1_map`). By the invariance theorem
(`isAdditivelyOptimal_universal`), `universal` is at most an additive constant worse than any
single-tape Turing machine.

## Main definitions

* `Cslib.Kolmogorov.DescriptionMethod.ofSingleTapeTM`: the description method of a `SingleTapeTM`.
* `Cslib.Kolmogorov.DescriptionMethod.ofTM0`: the description method of a finitely supported
  Mathlib `TM0.Machine`.
* `Cslib.Kolmogorov.DescriptionMethod.ofTM1`: the description method of a finitely supported
  Mathlib `TM1` program.
* `Cslib.Kolmogorov.DescriptionMethod.singleTapeSimulation`: simulation of `ofSingleTapeTM tm` by
  `ofMultiTapeTM (MultiTapeTM.ofSingleTapeTM tm)` with 0 program overhead and `3 * |p| + 2 * t + 6`
  time overhead.
* `Cslib.Kolmogorov.DescriptionMethod.tm0Simulation`: simulation of `ofTM0 M S hs` by a multi-tape
  Turing machine with 0 program overhead and `3 * |p| + 2 * t + 6` time overhead.

## Main results

* `Cslib.Kolmogorov.DescriptionMethod.mem_ofSingleTapeTM_runFor_iff`: a program outputs `x` within
  `t` steps under `ofSingleTapeTM tm` iff `tm.OutputsWithinTime p x t`.
* `Cslib.Kolmogorov.DescriptionMethod.ofSingleTapeTM_produces_iff`: a program describes `x` under
  `ofSingleTapeTM tm` iff `tm.Outputs p x`.
* `Cslib.Kolmogorov.DescriptionMethod.ofTM0_produces_iff`: a program describes `x` under
  `ofTM0 M S hs` iff `StateTransition.eval (TM0.step M)` halts with
  `BiTape.equivTape (BiTape.mk₁ x)`.
* `Cslib.Kolmogorov.DescriptionMethod.ecomplexity_ofMultiTapeTM_ofSingleTapeTM_le`,
  `Cslib.Kolmogorov.DescriptionMethod.etimeBoundedComplexity_ofMultiTapeTM_ofSingleTapeTM_le`:
  plain and time-bounded complexity transfer from `SingleTapeTM` to `MultiTapeTM`.
* `Cslib.Kolmogorov.DescriptionMethod.isPartrec_ofSingleTapeTM_map`,
  `Cslib.Kolmogorov.DescriptionMethod.exists_ecomplexity_universal_le_ofSingleTapeTM`: partial
  recursiveness and additive optimality of `universal` over `SingleTapeTM` (and `TM0` / `TM1`).

## References

* [M. Li, P. Vitányi, *An Introduction to Kolmogorov Complexity and Its
  Applications*][LiVitanyi2019]
-/

@[expose] public section

namespace Cslib.Kolmogorov.DescriptionMethod

open Cslib.Turing _root_.Turing

variable (tm : SingleTapeTM Bool)

/-- The description method of a binary single-tape Turing machine `tm : SingleTapeTM Bool`: on
program `p`, after `t` steps, outputs `x` if `tm` has halted with `BiTape.mk₁ x` on its tape. -/
def ofSingleTapeTM : DescriptionMethod (List Bool) where
  run p := ⟨tm.runFor p, fun t _ hx => tm.runFor_mono p t.le_succ hx⟩

variable {tm} {p x : List Bool} {t : ℕ}

/-- A program outputs `x` within `t` steps under `ofSingleTapeTM tm` iff
`tm.OutputsWithinTime p x t`. -/
theorem mem_ofSingleTapeTM_runFor_iff :
    x ∈ ((ofSingleTapeTM tm).run p).runFor t ↔ tm.OutputsWithinTime p x t :=
  tm.mem_runFor_iff

/-- A program describes `x` under `ofSingleTapeTM tm` iff `tm.Outputs p x`. -/
@[simp]
theorem ofSingleTapeTM_produces_iff :
    (ofSingleTapeTM tm).Produces p x ↔ tm.Outputs p x := by
  rw [← tm.mem_eval_iff_outputs]
  exact produces_iff_exists_mem_runFor.trans
    (Nat.rfindOpt_mono (fun ht h => tm.runFor_mono p ht h)).symm

theorem ecomplexity_ofSingleTapeTM_le (h : tm.Outputs p x) :
    (ofSingleTapeTM tm).ecomplexity x ≤ p.length :=
  ecomplexity_le_length (ofSingleTapeTM_produces_iff.mpr h)

theorem etimeBoundedComplexity_ofSingleTapeTM_le (h : tm.OutputsWithinTime p x t) :
    (ofSingleTapeTM tm).etimeBoundedComplexity t x ≤ p.length :=
  etimeBoundedComplexity_le_length (mem_ofSingleTapeTM_runFor_iff.mpr h)

/-! ### Description methods of Mathlib's `TM0` and `TM1` -/

/-- The description method of a finitely supported Mathlib `TM0.Machine (Option Bool) Λ`. -/
def ofTM0 {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (M : TM0.Machine (Option Bool) Λ) (S : Finset Λ) (hs : TM0.Supports M S) :
    DescriptionMethod (List Bool) :=
  ofSingleTapeTM (SingleTapeTM.ofTM0 M S hs)

theorem mem_ofTM0_runFor_succ_iff {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    {M : TM0.Machine (Option Bool) Λ} {S : Finset Λ} {hs : TM0.Supports M S} :
    x ∈ ((ofTM0 M S hs).run p).runFor (t + 1) ↔
      ∃ q_f, Relation.RelatesWithinSteps (fun a b => b ∈ TM0.step M a)
        (TM0.init (p.map some)) ⟨q_f, BiTape.equivTape (BiTape.mk₁ x)⟩ t ∧
        TM0.step M ⟨q_f, BiTape.equivTape (BiTape.mk₁ x)⟩ = none := by
  rw [ofTM0, mem_ofSingleTapeTM_runFor_iff, SingleTapeTM.outputsWithinTime_ofTM0_iff]

@[simp]
theorem ofTM0_produces_iff {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    {M : TM0.Machine (Option Bool) Λ} {S : Finset Λ} {hs : TM0.Supports M S} :
    (ofTM0 M S hs).Produces p x ↔
      ∃ q_f, (⟨q_f, BiTape.equivTape (BiTape.mk₁ x)⟩ : TM0.Cfg (Option Bool) Λ) ∈
        StateTransition.eval (TM0.step M) (TM0.init (p.map some)) := by
  rw [ofTM0, ofSingleTapeTM_produces_iff, SingleTapeTM.outputs_ofTM0_iff]

/-- The description method of a finitely supported Mathlib `TM1` statement table. -/
noncomputable def ofTM1 {Λ σ : Type} [Inhabited Λ] [Inhabited σ] [Fintype σ]
    (M : Λ → TM1.Stmt (Option Bool) Λ σ) (S : Finset Λ) (hs : TM1.Supports M S) :
    DescriptionMethod (List Bool) :=
  ofSingleTapeTM (SingleTapeTM.ofTM1 M S hs)

/-! ### Simulation of `ofSingleTapeTM` and `ofTM0` by `ofMultiTapeTM` -/

/-- Every single-tape description method `ofSingleTapeTM tm` is simulated by the 1-work-tape
multi-tape description method `ofMultiTapeTM (MultiTapeTM.ofSingleTapeTM tm)` with zero program
overhead (`compile := id`) and linear time overhead `3 * |p| + 2 * t + 6`. -/
def singleTapeSimulation (tm : SingleTapeTM Bool) :
    Simulation (ofSingleTapeTM tm) (ofMultiTapeTM (MultiTapeTM.ofSingleTapeTM tm)) 0
      fun n t => 3 * n + 2 * t + 6 where
  compile := id
  length_compile_le _ := le_rfl
  mem_runFor_compile {p t x} hx := by
    have hout := mem_ofSingleTapeTM_runFor_iff.mp hx
    have hcomp := MultiTapeTM.computesInTimeAndSpace_ofSingleTapeTM_of_input tm hout
    exact mem_ofMultiTapeTM_runFor_iff.mpr ⟨hcomp.2.1, hcomp.1⟩

/-- Plain Kolmogorov complexity under `MultiTapeTM.ofSingleTapeTM tm` is at most that under `tm`. -/
theorem ecomplexity_ofMultiTapeTM_ofSingleTapeTM_le (tm : SingleTapeTM Bool) (x : List Bool) :
    (ofMultiTapeTM (MultiTapeTM.ofSingleTapeTM tm)).ecomplexity x ≤
      (ofSingleTapeTM tm).ecomplexity x := by
  simpa using (singleTapeSimulation tm).ecomplexity_le x

/-- Time-bounded Kolmogorov complexity transfer from `SingleTapeTM` to `MultiTapeTM`: a description
of length at most `k` running in `t` single-tape steps gives a multi-tape description of length at
most `k` running in `3 * k + 2 * t + 6` steps. -/
theorem etimeBoundedComplexity_ofMultiTapeTM_ofSingleTapeTM_le
    (tm : SingleTapeTM Bool) {t k : ℕ} {x : List Bool}
    (h : (ofSingleTapeTM tm).etimeBoundedComplexity t x ≤ k) :
    (ofMultiTapeTM (MultiTapeTM.ofSingleTapeTM tm)).etimeBoundedComplexity
      (3 * k + 2 * t + 6) x ≤ k := by
  simpa using (singleTapeSimulation tm).etimeBoundedComplexity_le_of_le
    (fun _ _ hn => by dsimp only; omega) h

/-- Every `TM0` description method `ofTM0 M S hs` is simulated by a 1-work-tape `MultiTapeTM` with
zero program overhead and linear time overhead `3 * |p| + 2 * t + 6`. -/
def tm0Simulation {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (M : TM0.Machine (Option Bool) Λ) (S : Finset Λ) (hs : TM0.Supports M S) :
    Simulation (ofTM0 M S hs)
      (ofMultiTapeTM (MultiTapeTM.ofSingleTapeTM (SingleTapeTM.ofTM0 M S hs))) 0
      fun n t => 3 * n + 2 * t + 6 :=
  singleTapeSimulation (SingleTapeTM.ofTM0 M S hs)

/-! ### Partial recursiveness and optimality of `universal` over `SingleTapeTM`, `TM0`, `TM1` -/

/-- For every `tm : SingleTapeTM Bool` and computable decoder `dec : List Bool → ℕ`, mapping `dec`
over `ofSingleTapeTM tm` yields a partial recursive description method. -/
theorem isPartrec_ofSingleTapeTM_map (tm : SingleTapeTM Bool)
    {dec : List Bool → ℕ} (hdec : Computable dec) :
    ((ofSingleTapeTM tm).map dec).IsPartrec :=
  IsPartrec.of_partrec_eval tm.partrec_eval (fun _ _ => by simp) hdec

/-- For every finitely supported `TM0.Machine (Option Bool) Λ` and computable decoder
`dec : List Bool → ℕ`, mapping `dec` over `ofTM0 M S hs` yields a partial recursive description
method. -/
theorem isPartrec_ofTM0_map {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (M : TM0.Machine (Option Bool) Λ) (S : Finset Λ) (hs : TM0.Supports M S)
    {dec : List Bool → ℕ} (hdec : Computable dec) :
    ((ofTM0 M S hs).map dec).IsPartrec :=
  isPartrec_ofSingleTapeTM_map (SingleTapeTM.ofTM0 M S hs) hdec

/-- For every finitely supported `TM1` statement table and computable decoder
`dec : List Bool → ℕ`, mapping `dec` over `ofTM1 M S hs` yields a partial recursive description
method. -/
theorem isPartrec_ofTM1_map {Λ σ : Type} [Inhabited Λ] [Inhabited σ] [Fintype σ]
    (M : Λ → TM1.Stmt (Option Bool) Λ σ) (S : Finset Λ) (hs : TM1.Supports M S)
    {dec : List Bool → ℕ} (hdec : Computable dec) :
    ((ofTM1 M S hs).map dec).IsPartrec :=
  isPartrec_ofSingleTapeTM_map (SingleTapeTM.ofTM1 M S hs) hdec

/-- **Optimality of `universal` over single-tape Turing machines**: for every
`tm : SingleTapeTM Bool` and computable decoder `dec : List Bool → ℕ`, `universal` is at most an
additive constant worse than `ofSingleTapeTM tm`. -/
theorem exists_ecomplexity_universal_le_ofSingleTapeTM (tm : SingleTapeTM Bool)
    {dec : List Bool → ℕ} (hdec : Computable dec) :
    ∃ c : ℕ, ∀ x : List Bool,
      universal.ecomplexity (dec x) ≤ (ofSingleTapeTM tm).ecomplexity x + c :=
  exists_ecomplexity_universal_le_of_partrec_eval tm.partrec_eval (fun _ _ => by simp) hdec

/-- Using `Nat.bits` and `List.foldr Nat.bit 0`, `universal` is at most an additive constant worse
than any `tm : SingleTapeTM Bool` on binary representations of natural numbers. -/
theorem exists_ecomplexity_universal_le_ofSingleTapeTM_bits (tm : SingleTapeTM Bool) :
    ∃ c : ℕ, ∀ n : ℕ,
      universal.ecomplexity n ≤ (ofSingleTapeTM tm).ecomplexity n.bits + c := by
  obtain ⟨c, hc⟩ :=
    exists_ecomplexity_universal_le_ofSingleTapeTM tm Primrec.list_foldr_nat_bit.to_comp
  refine ⟨c, fun n => ?_⟩
  simpa [Nat.foldr_bit_bits] using hc n.bits

end Cslib.Kolmogorov.DescriptionMethod
