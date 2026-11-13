/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.InputPrefix
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Sublinear native time is constant

A native deterministic machine receives no separate input length. If it halts uniformly on
all inputs within a clock `p n`, and some width `N` satisfies `p N ≤ N`, its runtime is globally
bounded. Every longer input follows its `N`-symbol prefix; a finite maximum over the shorter
lengths handles all remaining inputs. Thus every uniform `o(n)` clock collapses to a constant.
No finiteness assumption on the machine's alphabet or control is needed for this run theorem.

For computability, the input encoding must be the identity on all bit words. An arbitrary
encoding may have invalid prefixes, on which its certificate imposes no runtime bound. The
computability result preserves the original outputs and independent space bound.

This formalizes Goldreich's January 2007 draft Exercise 4.3 (`r2.pdf`, PDF35/printed151)
[Goldreich2007DraftR2], in the native sequential-input model. It does not apply to a model
that supplies the input length for free or permits random access to the input.

## Main results

* `Turing.MultiTapeTM.exists_uniform_time_of_fast_length`: one fast width suffices for a
  uniformly clocked total machine.
* `Turing.MultiTapeTM.exists_uniform_time_of_isLittleO`: a sublinear clock gives constant time.
* `Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_const_time_of_isLittleO`: the computability
  consequence on raw bit words, with the original space bound.
-/

public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {tm : MultiTapeTM k Symbol State} {p : ℕ → ℕ}

/-- A total length-clocked machine which halts on every word of some width before it could
read beyond that word has a global constant runtime. The uniform clock on shorter lengths
is essential; a fast width alone does not establish totality on those inputs. -/
theorem exists_uniform_time_of_fast_length (h : ∀ x, tm.RunsInTime x (p x.length))
    {N : ℕ} (hN : p N ≤ N) : ∃ C, ∀ x, tm.RunsInTime x C := by
  let C := (Finset.range (N + 1)).sup p
  have hC (n : ℕ) (hn : n ≤ N) : p n ≤ C :=
    Finset.le_sup (Finset.mem_range.mpr (by omega))
  refine ⟨C, fun x => ?_⟩
  by_cases hx : x.length ≤ N
  · exact (h x).mono (hC _ hx)
  · have hlen : (x.take N).length = N := by rw [List.length_take, Nat.min_eq_left (by omega)]
    have hp : tm.RunsInTime (x.take N) (p N) := by simpa only [hlen] using h (x.take N)
    have hext := runsInTime_append (y := x.drop N) (by simpa only [hlen] using hN) hp
    rw [List.take_append_drop] at hext
    exact hext.mono (hC N le_rfl)

/-- A uniform sublinear worst-case clock gives a global constant runtime, since the input
length is not supplied separately to the machine. -/
theorem exists_uniform_time_of_isLittleO (h : ∀ x, tm.RunsInTime x (p x.length))
    (hp : (fun n : ℕ => (p n : ℝ)) =o[Filter.atTop] (fun n : ℕ => (n : ℝ))) :
    ∃ C, ∀ x, tm.RunsInTime x C := by
  obtain ⟨N, hN⟩ := (hp.bound (by norm_num : (0 : ℝ) < 1 / 2)).exists
  have hN' : p N ≤ N := by
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)] at hN
    exact_mod_cast (show (p N : ℝ) ≤ N by nlinarith)
  exact exists_uniform_time_of_fast_length h hN'

/-- On all raw bit words, a sublinear-time computation can use a constant clock while
preserving its computed function, machine and independent workspace bound. -/
theorem ComputableInTimeAndSpace.exists_const_time_of_isLittleO {β : Type*}
    {f : List Bool → β} {encOut : β ↪ List Bool} {s : List Bool → ℕ}
    (hf : ComputableInTimeAndSpace f encBits encOut (fun x => p x.length) s)
    (hp : (fun n : ℕ => (p n : ℝ)) =o[Filter.atTop] (fun n : ℕ => (n : ℝ))) :
    ∃ C, ComputableInTimeAndSpace f encBits encOut (fun _ => C) s := by
  obtain ⟨k, State, hfinite, tm, htm⟩ := hf
  obtain ⟨C, hC⟩ := exists_uniform_time_of_isLittleO (tm := tm)
    (fun x => (htm x).2.1) hp
  exact ⟨C, k, State, hfinite, tm, fun x => ⟨(htm x).1, hC x, (htm x).2.2⟩⟩

end Turing.MultiTapeTM
