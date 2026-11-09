/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Kolmogorov.Invariance
public import CslibFrontier.Computability.Kolmogorov.Partrec
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Partrec
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Run
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Id

/-!
# Description methods of multi-tape Turing machines

A deterministic multi-tape Turing machine over the binary alphabet is a description method: a
program is an input of the machine, the clock counts steps, and the output of a program is the
contents of the output tape once the machine has halted. Its complexity `C_tm(x)` is the length of
a shortest input on which `tm` computes `x`, and `C_tm^t(x)` that of a shortest input on which `tm`
computes `x` within `t` steps.

When the state space is finite, `tm.eval` is partial recursive (`Turing.MultiTapeTM.partrec_eval`),
so mapping any computable decoder `dec : List Bool → ℕ` over `ofMultiTapeTM tm` yields a partial
recursive description method (`isPartrec_ofMultiTapeTM_map`). By the invariance theorem
(`isAdditivelyOptimal_universal`), `universal` is at most an additive constant worse than any
finite-state multi-tape Turing machine (`exists_ecomplexity_universal_le_ofMultiTapeTM`).

## Main definitions

* `Cslib.Kolmogorov.DescriptionMethod.ofMultiTapeTM`: the description method of a machine.
* `Cslib.Kolmogorov.DescriptionMethod.literalSimulation`: a machine computing the identity
  simulates the literal description method.

## Main results

* `Cslib.Kolmogorov.DescriptionMethod.ofMultiTapeTM_produces_iff`: a program describes `x`
  exactly when the machine computes `x` from it.
* `Cslib.Kolmogorov.DescriptionMethod.mem_ofMultiTapeTM_runFor_iff`: a program describes `x` within
  `t` steps exactly when the machine computes `x` from it and halts within `t` steps.
* `Cslib.Kolmogorov.DescriptionMethod.etimeBoundedComplexity_ofMultiTapeTM_le`: an input from which
  the machine computes `x` within `t` steps bounds `C_tm^t(x)`.
* `Cslib.Kolmogorov.DescriptionMethod.exists_simulation_literal`: some machine simulates the
  literal description method.
* `Cslib.Kolmogorov.DescriptionMethod.isPartrec_ofMultiTapeTM_map`: mapping a computable decoder
  over the description method of a finite-state multi-tape machine is partial recursive.
* `Cslib.Kolmogorov.DescriptionMethod.exists_ecomplexity_universal_le_ofMultiTapeTM`: `universal`
  is at most an additive constant worse than any finite-state multi-tape machine.

## References

* [M. Li, P. Vitányi, *An Introduction to Kolmogorov Complexity and Its
  Applications*][LiVitanyi2019]
-/

@[expose] public section

namespace Cslib.Kolmogorov.DescriptionMethod

open Turing

variable {k : ℕ} {State : Type*} (tm : MultiTapeTM k Bool State)

/-- The description method of a deterministic multi-tape Turing machine over the binary alphabet:
the program `p` is the input, and after `t` steps its output is the contents of the output tape if
the machine has halted. -/
noncomputable def ofMultiTapeTM : DescriptionMethod (List Bool) where
  run p := ⟨tm.runFor p, fun t _ hx => tm.runFor_mono p t.le_succ hx⟩

variable {tm} {p x : List Bool} {t : ℕ}

theorem mem_ofMultiTapeTM_runFor_iff_halted :
    x ∈ ((ofMultiTapeTM tm).run p).runFor t ↔
      (tm.runFrom (tm.initCfg p) t).Halted ∧ (tm.runFrom (tm.initCfg p) t).output = x :=
  tm.mem_runFor_iff

/-- A program describes `x` exactly when the machine computes `x` from it. -/
@[simp]
theorem ofMultiTapeTM_produces_iff : (ofMultiTapeTM tm).Produces p x ↔ tm.Computes p x :=
  produces_iff_exists_mem_runFor.trans (exists_congr fun _ => mem_ofMultiTapeTM_runFor_iff_halted)

/-- A program describes `x` within `t` steps exactly when the machine computes `x` from it and
halts within `t` steps. -/
theorem mem_ofMultiTapeTM_runFor_iff :
    x ∈ ((ofMultiTapeTM tm).run p).runFor t ↔ tm.RunsInTime p t ∧ tm.Computes p x := by
  constructor
  · intro h
    exact ⟨MultiTapeTM.runsInTime_iff_halted.mpr (mem_ofMultiTapeTM_runFor_iff_halted.mp h).1,
      ofMultiTapeTM_produces_iff.mp (.of_mem_runFor h)⟩
  · rintro ⟨ht, hx⟩
    have hmem : (tm.runFrom (tm.initCfg p) t).output ∈ ((ofMultiTapeTM tm).run p).runFor t :=
      mem_ofMultiTapeTM_runFor_iff_halted.mpr ⟨MultiTapeTM.runsInTime_iff_halted.mp ht, rfl⟩
    rwa [(Produces.of_mem_runFor hmem).unique (ofMultiTapeTM_produces_iff.mpr hx)] at hmem

theorem ecomplexity_ofMultiTapeTM_le (h : tm.Computes p x) :
    (ofMultiTapeTM tm).ecomplexity x ≤ p.length :=
  ecomplexity_le_length (ofMultiTapeTM_produces_iff.mpr h)

/-- An input from which the machine computes `x` within `t` steps bounds the time-bounded
complexity `C_tm^t(x)`. -/
theorem etimeBoundedComplexity_ofMultiTapeTM_le (ht : tm.RunsInTime p t) (h : tm.Computes p x) :
    (ofMultiTapeTM tm).etimeBoundedComplexity t x ≤ p.length :=
  etimeBoundedComplexity_le_length (mem_ofMultiTapeTM_runFor_iff.mpr ⟨ht, h⟩)

/-! ### A machine simulating the literal method -/

/-- From a computation of the identity, a simulation of the literal description method with one
extra step. -/
def literalSimulation
    (h : tm.ComputesFunInTimeAndSpace (Function.Embedding.refl _) (Function.Embedding.refl _) id
      (fun p => p.length + 1) (fun _ => 0)) :
    Simulation literal (ofMultiTapeTM tm) 0 fun _ t => t + 1 where
  compile := id
  length_compile_le _ := le_rfl
  mem_runFor_compile {p t x} hpx := by
    obtain ⟨hp, rfl⟩ := mem_literal_runFor.mp hpx
    exact mem_ofMultiTapeTM_runFor_iff.mpr ⟨(h p).2.1.mono (Nat.succ_le_succ hp), (h p).1⟩

/-- Some machine with finitely many states simulates the literal description method with one extra
step, so under it every string `x` has complexity at most `|x|` within `|x| + 1` steps. -/
theorem exists_simulation_literal :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
      Nonempty (Simulation literal (ofMultiTapeTM tm) 0 fun _ t => t + 1) :=
  let ⟨k, State, hfin, tm, h⟩ := MultiTapeTM.computableInTimeAndSpace_id
    (enc := Function.Embedding.refl (List Bool))
  ⟨k, State, hfin, tm, ⟨literalSimulation h⟩⟩

/-! ### Partial recursiveness and optimality of `universal` over `MultiTapeTM` -/

/-- For every finite-state binary `MultiTapeTM` and computable decoder `dec : List Bool → ℕ`,
mapping `dec` over `ofMultiTapeTM tm` yields a partial recursive description method. -/
theorem isPartrec_ofMultiTapeTM_map {State : Type} [Finite State]
    (tm : MultiTapeTM k Bool State) {dec : List Bool → ℕ} (hdec : Computable dec) :
    ((ofMultiTapeTM tm).map dec).IsPartrec :=
  IsPartrec.of_partrec_eval tm.partrec_eval (fun _ _ => by simp) hdec

/-- **Optimality of `universal` over finite-state multi-tape Turing machines**: for every
finite-state binary `MultiTapeTM` and computable decoder `dec : List Bool → ℕ`, `universal` is at
most an additive constant worse than `ofMultiTapeTM tm`. -/
theorem exists_ecomplexity_universal_le_ofMultiTapeTM {State : Type} [Finite State]
    (tm : MultiTapeTM k Bool State) {dec : List Bool → ℕ} (hdec : Computable dec) :
    ∃ c : ℕ, ∀ x : List Bool,
      universal.ecomplexity (dec x) ≤ (ofMultiTapeTM tm).ecomplexity x + c :=
  exists_ecomplexity_universal_le_of_partrec_eval tm.partrec_eval (fun _ _ => by simp) hdec

/-- Using `Nat.bits` and `List.foldr Nat.bit 0`, `universal` is at most an additive constant worse
than any finite-state binary `MultiTapeTM` on binary representations of natural numbers. -/
theorem exists_ecomplexity_universal_le_ofMultiTapeTM_bits {State : Type} [Finite State]
    (tm : MultiTapeTM k Bool State) :
    ∃ c : ℕ, ∀ n : ℕ,
      universal.ecomplexity n ≤ (ofMultiTapeTM tm).ecomplexity n.bits + c := by
  obtain ⟨c, hc⟩ :=
    exists_ecomplexity_universal_le_ofMultiTapeTM tm Primrec.list_foldr_nat_bit.to_comp
  refine ⟨c, fun n => ?_⟩
  simpa [Nat.foldr_bit_bits] using hc n.bits

end Cslib.Kolmogorov.DescriptionMethod
