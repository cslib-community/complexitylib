/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Frame
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
public import Cslib.Computability.Machines.Turing.MultiTape.ConfigBound
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
import Complexity.Computability.Machines.Turing.MultiTape.HaltsAt
import Complexity.Foundations.Data.Nat.Log
import Complexity.Foundations.Data.Nat.PolynomialBound.Log
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Id

/-!
# Logarithmic space on deterministic machines

Space is upstream's measure (`Turing.MultiTapeNTM.RunPath.space`): the number of distinct
work-tape cells visited by the heads, summed over the work tapes. The read-only input tape and the
write-only, append-only output tape are not charged, so a machine may read an input, and emit an
output, much longer than its workspace [Sipser, Section 8.4][Sipser2013].

`Turing.MultiTapeTM.ComputableInLogSpace f encIn encOut` asks for one machine with a binary
alphabet and finitely many states that computes `f` within space `c * (Nat.log2 n + 1)` on
encoded inputs of length `n`, for a constant `c`, and halts. These are the functions computable
in logarithmic space [Arora and Barak, Section 4.3][AroraBarak09]; the summand `1` keeps the
bound positive on inputs of length at most one, where each work tape still costs a cell.

No time bound is imposed, because one follows. A machine never repeats the part of its
configuration it can still read, the input head position and the storage (`Turing.Cfg.core`),
before it halts: the next core depends only on the current one. So a machine that halts within
space `s` halts within `(n + 2) * storageBound Bool State k s` steps
(`Turing.MultiTapeTM.haltsAt_le_card`), by upstream's count of storages. Under a logarithmic
space bound this is polynomial in `n`, so logspace functions are computable in polynomial time
and have polynomially long values
(`Turing.MultiTapeTM.ComputableInLogSpace.exists_polyBounded_time`,
`Turing.MultiTapeTM.ComputableInLogSpace.polyBounded_length`). This is the time bound of the
inclusion `DSPACE(s) ⊆ DTIME(2 ^ O(s))` of cslib pull request #767
(`ComputesInTimeAndSpace.truncate` there), stated for the current machine API.

Composition is in
`Complexity/Computability/Machines/Turing/MultiTape/Complexity/LogSpace/Composition/Recompute.lean`.
It is kept apart because its machine is built from the universal machine; this file does not
depend on that machine.

## Main definitions

* `Turing.MultiTapeTM.ComputableInLogSpace`: computability in logarithmic space.

## Main results

* `Turing.MultiTapeTM.haltsAt_le_card`: a halting machine within space `s` halts within
  `(n + 2) * storageBound Symbol State k s` steps.
* `Turing.MultiTapeTM.ComputableInLogSpace.exists_polyBounded_time`: logspace computations take
  polynomial time.
* `Turing.MultiTapeTM.ComputableInLogSpace.polyBounded_length`: logspace functions have
  polynomially long values.
* `Turing.MultiTapeTM.ComputableInLogSpace.id`, `Turing.MultiTapeTM.ComputableInLogSpace.const`,
  `Turing.MultiTapeTM.ComputableInLogSpace.of_finite`,
  `Turing.MultiTapeTM.ComputableInLogSpace.congr`,
  `Turing.MultiTapeTM.ComputableInLogSpace.of_eq`: logspace functions in zero space and congruence.
* `Turing.MultiTapeTM.ComputableInLogSpace.computableInPolyTime`,
  `Turing.MultiTapeTM.ComputableInLogSpace.computableTidilyInPolyTime`: logspace functions are
  computable in polynomial time.
* `ComputableInLogSpace` is registered with `fun_prop`, with the inclusion in polynomial time as
  a one-way transition.
* `Turing.MultiTapeTM.Transducer.computableInLogSpace`: functions computed by finite-state
  transducers are computable in logarithmic space.
* `Turing.MultiTapeTM.polyBounded_log`: logarithmic bounds are polynomially bounded.
* `Turing.MultiTapeTM.computableInLogSpace_frame`: framing an encoded input uses zero work space.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.4][Sipser2013]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 4.3][AroraBarak09]
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-! ### Halting within the number of cores -/

section Halting

variable {k : ℕ} {Symbol State : Type*} {tm : MultiTapeTM k Symbol State} {input : List Symbol}

/-- Runs from configurations with equal cores keep equal cores, since a step does not read the
output. -/
theorem core_runFrom_eq_of_core_eq {c₁ c₂ : Cfg k Symbol State input} (h : c₁.core = c₂.core)
    (m : ℕ) : (tm.runFrom c₁ m).core = (tm.runFrom c₂ m).core := by
  induction m with
  | zero => exact h
  | succ m ih =>
    rw [runFrom_succ, runFrom_succ]
    generalize tm.runFrom c₁ m = d₁ at ih ⊢
    generalize tm.runFrom c₂ m = d₂ at ih ⊢
    rcases d₁ with ⟨q₁, i₁, w₁, p₁, out₁⟩
    rcases d₂ with ⟨q₂, i₂, w₂, p₂, out₂⟩
    simp only [Cfg.core, Cfg.storage, Prod.mk.injEq, Storage.mk.injEq] at ih
    obtain ⟨rfl, rfl, rfl, rfl⟩ := ih
    cases q₁ with
    | none => rw [step_of_halt rfl, step_of_halt rfl]; rfl
    | some q => rw [step_of_state rfl, step_of_state rfl]; rfl

/-- **A halting machine halts within the number of its cores.** Before it halts, a machine within
space `s` repeats no core (input head position and storage), since from a repeated core it would
never halt; so it halts within `(n + 2) * storageBound Symbol State k s` steps on an input of
length `n`. -/
theorem haltsAt_le_card [Fintype Symbol] [Fintype State] {s u : ℕ}
    (hs : tm.RunsInSpace input s) (hu : tm.HaltsAt (tm.initCfg input) u) :
    u ≤ (input.length + 2) * storageBound Symbol State k s := by
  classical
  let core := fun t => (tm.runFrom (tm.initCfg input) t).core
  -- a core repeated before halting would repeat at the halting step
  have hne : ∀ i j, i < j → j < u → core i ≠ core j := by
    intro i j hij hj hcore
    have hshift := core_runFrom_eq_of_core_eq (tm := tm) hcore (u - j)
    rw [← runFrom_add, ← runFrom_add, show j + (u - j) = u by omega] at hshift
    have hstate := congrArg (fun c => c.2.state) hshift
    exact hu.not_halted (show i + (u - j) < u by omega) (hstate.trans hu.halted)
  have hinj : Set.InjOn core (Finset.range u : Set ℕ) := by
    intro i hi j hj hcore
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    rcases lt_trichotomy i j with hlt | heq | hgt
    · exact absurd hcore (hne i j hlt hj)
    · exact heq
    · exact absurd hcore.symm (hne j i hgt hi)
  have hsub : (((Finset.range u).image core : Finset _) : Set _).encard ≤
      (Set.range core).encard := Set.encard_le_encard fun _ hx => by
    obtain ⟨t, -, rfl⟩ := Finset.mem_coe.mp hx |> Finset.mem_image.mp
    exact ⟨t, rfl⟩
  rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injOn hinj,
    Finset.card_range] at hsub
  -- every core of the run is the core at the end of a computation path
  have hpath : (Set.range core).encard ≤
      (Set.range fun p : tm.ComputationPath input => p.last.core).encard :=
    Set.encard_le_encard (Set.range_subset_iff.2 fun t => ⟨.ofDeterministic tm input t, rfl⟩)
  exact_mod_cast (hsub.trans hpath).trans (tm.encard_cores_le hs)

/-- A machine that halts on `input` within space `s` does so within
`(n + 2) * storageBound Symbol State k s` steps, with the same output. -/
theorem ComputesInTimeAndSpace.of_card [Fintype Symbol] [Fintype State] {output : List Symbol}
    {t s : ℕ} (h : tm.ComputesInTimeAndSpace input output t s) :
    tm.ComputesInTimeAndSpace input output
      ((input.length + 2) * storageBound Symbol State k s) s := by
  obtain ⟨u, -, hu⟩ := exists_haltsAt_of_runsInTime h.2.1
  refine ⟨h.1, runsInTime_iff_halted.mpr ?_, h.2.2⟩
  rw [hu.runFrom_eq (haltsAt_le_card h.2.2 hu)]
  exact hu.halted

end Halting

/-! ### Computability in logarithmic space -/

variable {α β γ : Type} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool}

/-- `f` is computable in logarithmic space: some machine with a binary alphabet and finitely many
states computes `f` with respect to `encIn` and `encOut`, halting, within space
`c * (Nat.log2 n + 1)` on encoded inputs of length `n`, for a constant `c`. The input and the
output are not charged. -/
def ComputableInLogSpace (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) : Prop :=
  ∃ t c, ComputableInTimeAndSpace f encIn encOut t fun a => c * (Nat.log2 (encIn a).length + 1)

/-- The logarithmic bounds `c * (log₂ n + 1)` are polynomially bounded
(`Cslib.polynomiallyBounded_mul_log2_add_one`). -/
theorem polyBounded_log {δ : Type*} (size : δ → ℕ) (c : ℕ) :
    PolyBounded size fun a => c * (Nat.log2 (size a) + 1) :=
  .of_polynomiallyBounded size (Cslib.polynomiallyBounded_mul_log2_add_one c)

/-- The number of cores under a logarithmic space bound is polynomial. -/
private theorem card_le_of_log (State : Type*) [Fintype State] (k c : ℕ) :
    ∃ A d, ∀ n, (n + 2) * storageBound Bool State k (c * (Nat.log2 n + 1)) ≤ A * (n + 1) ^ d := by
  refine ⟨2 * storageBoundBase Bool State k * 2 ^ (storageBoundExp Bool k * c),
    storageBoundExp Bool k * c + 1, fun n => ?_⟩
  set e := storageBoundExp Bool k * c
  have hpow : 2 ^ (storageBoundExp Bool k * (c * (Nat.log2 n + 1))) ≤ 2 ^ e * (n + 1) ^ e :=
    calc 2 ^ (storageBoundExp Bool k * (c * (Nat.log2 n + 1))) = (2 ^ (Nat.log2 n + 1)) ^ e := by
          rw [← pow_mul]
          congr 1
          simp only [e]
          ring
      _ ≤ (2 * (n + 1)) ^ e := Nat.pow_le_pow_left (Nat.two_pow_log2_succ_le n) e
      _ = 2 ^ e * (n + 1) ^ e := mul_pow ..
  calc (n + 2) * storageBound Bool State k (c * (Nat.log2 n + 1))
      ≤ (2 * (n + 1)) * (storageBoundBase Bool State k * (2 ^ e * (n + 1) ^ e)) :=
        Nat.mul_le_mul (by omega) ((storageBound_le_base_mul_pow _).trans
          (Nat.mul_le_mul_left _ hpow))
    _ = _ := by ring

/-- **Logspace computations take polynomial time.** -/
theorem ComputableInLogSpace.exists_polyBounded_time {f : α → β}
    (h : ComputableInLogSpace f encIn encMid) :
    ∃ t c, PolyBounded (fun a => (encIn a).length) t ∧
      ComputableInTimeAndSpace f encIn encMid t fun a => c * (Nat.log2 (encIn a).length + 1) := by
  obtain ⟨t, c, k, State, _, tm, htm⟩ := h
  let := Fintype.ofFinite State
  obtain ⟨A, d, hcard⟩ := card_le_of_log State k c
  exact ⟨_, c, .of_forall_le A d fun a => hcard (encIn a).length, k, State, inferInstance, tm,
    fun a => (htm a).of_card⟩

/-- **Logspace functions have polynomially long values**, since a machine emits at most one
symbol per step. -/
theorem ComputableInLogSpace.polyBounded_length {f : α → β}
    (h : ComputableInLogSpace f encIn encMid) :
    PolyBounded (fun a => (encIn a).length) fun a => (encMid (f a)).length := by
  obtain ⟨t, c, ht, k, State, _, tm, htm⟩ := h.exists_polyBounded_time
  refine ht.mono fun a => ?_
  obtain ⟨u, hu_le, hu⟩ := exists_haltsAt_of_runsInTime (htm a).2.1
  rw [← output_haltsAt (htm a).1 hu]
  exact (tm.length_output_runFrom_le _ u).trans (by simpa [MultiTapeNTM.initCfg] using hu_le)

/-- **Logspace functions are computable in polynomial time**, tidily. -/
theorem ComputableInLogSpace.computableTidilyInPolyTime {f : α → β}
    (h : ComputableInLogSpace f encIn encMid) : ComputableTidilyInPolyTime f encIn encMid := by
  obtain ⟨t, c, ht, hf⟩ := h.exists_polyBounded_time
  obtain ⟨c', hc'⟩ := hf.exists_computableTidilyInTimeAndSpace
  have hlog := polyBounded_log (fun a => (encIn a).length) c
  exact ⟨_, _, (((PolyBounded.const 2).mul ht).add ((PolyBounded.const 3).mul hlog)).add
    (.const c'),
    (PolyBounded.const c').mul (hlog.add (.const 1)), hc'⟩

/-- **Logspace functions are computable in polynomial time.** -/
theorem ComputableInLogSpace.computableInPolyTime {f : α → β}
    (h : ComputableInLogSpace f encIn encMid) : ComputableInPolyTime f encIn encMid :=
  let ⟨_, _, ⟨t, ht, htb⟩, ⟨s, hs, hsb⟩, h⟩ := h.computableTidilyInPolyTime
  ⟨t, s, ht, hs, (h.mono htb hsb).computableInTimeAndSpace⟩

/-- The identity is computable in logarithmic space, indeed in zero space. -/
theorem ComputableInLogSpace.id : ComputableInLogSpace (fun a : α => a) encIn encIn :=
  ⟨_, 0, computableInTimeAndSpace_id.mono (fun _ => le_rfl) fun _ => Nat.zero_le _⟩

/-- A function whose encoded values agree with those of a logspace function is computable in
logarithmic space, by the same machine. -/
theorem ComputableInLogSpace.congr {f : α → β} {g : α → γ}
    (hf : ComputableInLogSpace f encIn encMid) (h : ∀ a, encOut (g a) = encMid (f a)) :
    ComputableInLogSpace g encIn encOut := by
  obtain ⟨t, c, k, State, hS, tm, htm⟩ := hf
  refine ⟨t, c, k, State, hS, tm, fun a => ?_⟩
  rw [h a]
  exact htm a

/-- A function pointwisely equal to a logspace function is computable in logarithmic space, by the
same machine. -/
theorem ComputableInLogSpace.congr_fun {f g : α → β}
    (hf : ComputableInLogSpace f encIn encMid) (h : ∀ a, g a = f a) :
    ComputableInLogSpace g encIn encMid :=
  hf.congr fun a => congrArg encMid (h a)

/-- A function whose encoded values equal its encoded arguments is computable in logarithmic
space, indeed in zero space. -/
theorem ComputableInLogSpace.of_eq {f : α → β} (h : ∀ a, encMid (f a) = encIn a) :
    ComputableInLogSpace f encIn encMid :=
  ComputableInLogSpace.id.congr h

/-- Constant functions are computable in logarithmic space, indeed in zero space. -/
theorem ComputableInLogSpace.const (b : β) : ComputableInLogSpace (fun _ : α => b) encIn encMid :=
  let ⟨_, h⟩ := computableInTimeAndSpace_of_const (encIn := encIn) (encOut := encMid) b
  ⟨_, 0, h.mono (fun _ => le_rfl) fun _ => Nat.zero_le _⟩

/-- Functions on a finite type are computable in logarithmic space, indeed in zero space. -/
theorem ComputableInLogSpace.of_finite [Finite α] (f : α → β) :
    ComputableInLogSpace f encIn encMid :=
  let ⟨_, h⟩ := computableInTimeAndSpace_of_finite (encIn := encIn) (encOut := encMid) f
  ⟨_, 0, h.mono (fun _ => le_rfl) fun _ => Nat.zero_le _⟩

/-! ### Automation

`ComputableInLogSpace` is a `fun_prop` predicate. The identity and constants are its core rules
here. Its composition rule is registered in
`Complexity/Computability/Machines/Turing/MultiTape/Complexity/LogSpace/Composition/Recompute.lean`,
so `fun_prop` needs that module to decompose a goal; pairing, projections, case distinctions and
word operations are registered in
`Complexity/Computability/Machines/Turing/MultiTape/Complexity/LogSpace/Words.lean`, and the
counter-program primitives in
`Complexity/Computability/Machines/Turing/MultiTape/Complexity/LogSpace/CounterProgram/Words.lean`.
The inclusion in polynomial time is a one-way transition rule: a logspace certificate closes a
plain polynomial-time goal, and there is no rule back, so the search has no cycle. -/

attribute [fun_prop] ComputableInLogSpace ComputableInLogSpace.id ComputableInLogSpace.const
  ComputableInLogSpace.computableInPolyTime

/-- **A function computed by a finite-state transducer is computable in logarithmic space**: the
transducer runs without work tapes. -/
theorem Transducer.computableInLogSpace {Q : Type} [Finite Q] (τ : Transducer Bool Q)
    {α β : Type} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {f : α → β}
    (hf : ∀ a, encOut (f a) = τ.run τ.q₀ (encIn a)) : ComputableInLogSpace f encIn encOut :=
  ⟨_, 0, (τ.computableTidilyInTimeAndSpace hf).computableInTimeAndSpace.mono (fun _ => le_rfl)
    fun _ => Nat.zero_le _⟩

/-- **Framing an encoded instance** takes no work space. -/
theorem computableInLogSpace_frame {α : Type} (enc : α ↪ List Bool) :
    ComputableInLogSpace (fun a => enc a) enc (encFramed encBits) :=
  Encodings.frameT.computableInLogSpace fun a => by
    rw [encFramed_apply, encBits_apply, Encodings.frameT_run]

end Turing.MultiTapeTM
