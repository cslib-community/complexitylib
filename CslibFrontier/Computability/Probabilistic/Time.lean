/-
Copyright (c) 2026 Karn Seth, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.Parameter
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Closed
import CslibFrontier.Computability.Probabilistic.PPT.Clock
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Composition
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.QueryTake
import CslibFrontier.Computability.Machines.Turing.MultiTape.Deterministic
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.EncLen

/-!
# Explicit-time intrinsically halting probabilistic realizations

`Cslib.Probability.ComputesInTimeOn input output t program` asserts that one finite-control
fair-coin machine realizes `program` across all inputs `a` within `t a` steps and has actually
reached a halting state (`final.tapes.state = none`) on every supported execution at step `t a`.

Requiring actual halting rather than clock-cutoff fuel makes monotonicity in the step schedule
(`ComputesInTimeOn.mono`) hold unconditionally for arbitrary functions `t₁ ≤ t₂`, without requiring
`t₂` to be computable, and makes sequential monadic composition (`ComputesInTimeOn.bind`) incur an
explicit machine-independent step bound `2 * t₁ a + t₂' a + 4`. Together with the clock compiler of
`CslibFrontier.Computability.Probabilistic.PPT.Clock`, uniform strict polynomial time (`IsPPTOn` and
`IsPPT`) is equivalent to `ComputesInTimeOn` / `ComputesInTime` under a polynomially bounded step
schedule (`isPPTOn_iff_exists_polyBounded_computesInTimeOn`,
`isPPT_iff_exists_polyBounded_computesInTime`).

## Main definitions

* `Cslib.Probability.ComputesInTimeOn`: uniform halting fair-coin realization within an explicit
  step schedule on encoded inputs.
* `Cslib.Probability.ComputesInTime`: uniform halting fair-coin realization parameterized by a
  unary security parameter and auxiliary input length.

## Main results

* `Cslib.Probability.ComputesInTimeOn.mono`: unconditional step-schedule monotonicity.
* `Cslib.Probability.ComputesInTimeOn.congr`, `Cslib.Probability.ComputesInTimeOn.length_le`:
  distributional congruence and supported output-length bound `≤ t a`.
* `Cslib.Probability.ComputesInTimeOn.uniform_bool`: drawing a fair bit in `1` step.
* `Turing.MultiTapeTM.ComputableInTimeAndSpace.computesInTimeOn`: plain deterministic computations
  lift with exact step bound `t`.
* `Cslib.Probability.ComputesInTimeOn.bind`, `.preprocess`, `.map`: quantitative composition with
  explicit step bounds.
* `Cslib.Probability.isPPTOn_iff_exists_polyBounded_computesInTimeOn`,
  `Cslib.Probability.isPPT_iff_exists_polyBounded_computesInTime`: equivalence with `IsPPTOn` and
  `IsPPT`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 7.
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Section 3.11.
-/

public section

namespace Cslib.Probability

open Turing.MultiTapeTM

/-- One finite fair-coin machine realizes the encoded program within `t a` steps on every input `a`
and has halted on every supported configuration at step `t a`. -/
@[expose] def ComputesInTimeOn {α β : Type} (input : α ↪ List Bool) (output : β ↪ List Bool)
    (t : α → ℕ) (program : α → ProbComp β) : Prop :=
  ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : Turing.MultiTapePTM k Bool State),
    ∀ a, (ProbComp.eval (program a)).map output =
      ProbComp.eval (machine.runClosed (t a) (input a)) ∧
      ∀ final ∈ (ProbComp.eval (machine.runConfigFrom (ProbComp.uniform Bool) Empty.elim
        (t a) (machine.initialConfig (input a)))).support,
        final.tapes.state = none

/-- Uniform halting fair-coin realization on a unary security parameter and auxiliary bit string,
indexed by `(n, aux.length)`. -/
@[expose] def ComputesInTime {β : Type} (output : β ↪ List Bool) (t : ℕ → ℕ → ℕ)
    (program : ℕ → List Bool → ProbComp β) : Prop :=
  ComputesInTimeOn (encPair encUnary encBits) output
    (fun input => t input.1 input.2.length) (fun input => program input.1 input.2)

namespace ComputesInTimeOn

variable {α β γ : Type} {input : α ↪ List Bool} {middle : β ↪ List Bool}
  {output : γ ↪ List Bool} {t t₁ t₂ : α → ℕ} {program program' : α → ProbComp γ}

/-- Enlarging the step schedule preserves halting realization, without requiring the larger
schedule to be computable. -/
theorem mono (h : ComputesInTimeOn input output t₁ program) (hle : ∀ a, t₁ a ≤ t₂ a) :
    ComputesInTimeOn input output t₂ program := by
  obtain ⟨k, State, hfinite, machine, hmachine⟩ := h
  refine ⟨k, State, hfinite, machine, fun a => ?_⟩
  obtain ⟨hout, hhalt⟩ := hmachine a
  have hcfg : ProbComp.eval (machine.runClosedConfigFrom (t₂ a) (machine.initialConfig (input a))) =
      ProbComp.eval (machine.runClosedConfigFrom (t₁ a) (machine.initialConfig (input a))) :=
    machine.eval_runClosedConfigFrom_eq_of_halted (machine.initialConfig (input a)) (hle a) hhalt
  refine ⟨hout.trans (machine.eval_runClosed_eq_of_halted (input a) (hle a) hhalt).symm, ?_⟩
  intro final hfinal
  change final ∈ (ProbComp.eval
    (machine.runClosedConfigFrom (t₂ a) (machine.initialConfig (input a)))).support at hfinal
  rw [hcfg] at hfinal
  exact hhalt final hfinal

/-- Distributional equality preserves the realizing machine and step schedule. -/
theorem congr (h : ComputesInTimeOn input output t program)
    (heq : ∀ a, ProbComp.eval (program a) = ProbComp.eval (program' a)) :
    ComputesInTimeOn input output t program' := by
  obtain ⟨k, State, hfinite, machine, hmachine⟩ := h
  refine ⟨k, State, hfinite, machine, fun a => ?_⟩
  obtain ⟨hout, hhalt⟩ := hmachine a
  exact ⟨(congrArg (PMF.map output) (heq a)).symm.trans hout, hhalt⟩

/-- Every supported encoded output has length at most the step budget `t a`. -/
theorem length_le (h : ComputesInTimeOn input output t program) (a : α) {result : γ}
    (hresult : result ∈ (ProbComp.eval (program a)).support) :
    (output result).length ≤ t a := by
  obtain ⟨k, State, _, machine, hmachine⟩ := h
  have hmap : output result ∈ ((ProbComp.eval (program a)).map output).support :=
    (PMF.mem_support_map_iff output (ProbComp.eval (program a)) (output result)).mpr
      ⟨result, hresult, rfl⟩
  rw [(hmachine a).1] at hmap
  exact machine.length_output_eval_runClosed_le (t a) (input a) (output result) hmap

/-- Sampling one fair bit takes `1` step on any input encoding. -/
theorem uniform_bool (input : α ↪ List Bool) :
    ComputesInTimeOn input encBool (fun _ => 1) (fun _ => ProbComp.uniform Bool) := by
  refine ⟨0, Unit, inferInstance, Turing.MultiTapePTM.coinMachine (Operation := Empty), fun a => ?_⟩
  have hcfg : ProbComp.eval
      ((Turing.MultiTapePTM.coinMachine (Operation := Empty)).runConfigFrom
        (ProbComp.uniform Bool) Empty.elim 1
        ((Turing.MultiTapePTM.coinMachine (Operation := Empty)).initialConfig (input a))) =
      (ProbComp.eval (ProbComp.uniform Bool)).map fun bit =>
        ((Turing.MultiTapePTM.coinMachine (Operation := Empty)).initialConfig (input a)).step
          { inputTape := 0, workTapes := Fin.elim0, output := some bit, state := none }
          (fun _ => none) (fun _ => 0) := by
    simp [Turing.MultiTapePTM.runConfigFrom, Turing.MultiTapeMachine.runConfigFrom,
      Turing.MultiTapeMachine.initialConfig, Turing.Cfg.init,
      Turing.MultiTapePTM.coinMachine, PMF.map]
  refine ⟨?_, ?_⟩
  · rw [Turing.MultiTapePTM.runClosed_eq_map, ProbComp.eval_map]
    change _ = PMF.map (fun final => final.tapes.output)
      (ProbComp.eval ((Turing.MultiTapePTM.coinMachine (Operation := Empty)).runConfigFrom
        (ProbComp.uniform Bool) Empty.elim 1
        ((Turing.MultiTapePTM.coinMachine (Operation := Empty)).initialConfig (input a))))
    rw [hcfg, PMF.map_comp]
    rfl
  · rw [hcfg]
    intro final hfinal
    obtain ⟨bit, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
    rfl

/-- Sequence two halting probabilistic realizations, charging `2 * t₁ a + t₂' a + 4` steps where
`t₂' a` upper-bounds `t₂` across supported intermediate outputs of `first a`. -/
theorem bind {first : α → ProbComp β} {second : β → ProbComp γ}
    {t₂ : β → ℕ} {t₂' : α → ℕ}
    (hfirst : ComputesInTimeOn input middle t₁ first)
    (hsecond : ComputesInTimeOn middle output t₂ second)
    (ht₂ : ∀ a b, b ∈ (ProbComp.eval (first a)).support → t₂ b ≤ t₂' a) :
    ComputesInTimeOn input output (fun a => 2 * t₁ a + t₂' a + 4)
      (fun a => do
        let b ← first a
        second b) := by
  obtain ⟨k₁, State₁, hfin₁, m₁, hm₁⟩ := hfirst
  obtain ⟨k₂, State₂, hfin₂, m₂, hm₂⟩ := hsecond
  refine ⟨k₂ + k₁ + 2, _, inferInstance, m₂.comp m₁ true, fun a => ?_⟩
  obtain ⟨hout₁, hhalt₁⟩ := hm₁ a
  have hmem_word : ∀ word ∈ (ProbComp.eval (m₁.runClosed (t₁ a) (input a))).support,
      ∃ b ∈ (ProbComp.eval (first a)).support, middle b = word := by
    intro word hword
    rw [← hout₁] at hword
    exact (PMF.mem_support_map_iff _ _ _).mp hword
  have hhalt₂ : ∀ word ∈ (ProbComp.eval (m₁.runClosed (t₁ a) (input a))).support,
      ∀ final ∈ (ProbComp.eval
        (m₂.runClosedConfigFrom (t₂' a) (m₂.initialConfig word))).support,
        final.tapes.state = none := by
    intro word hword final hfinal
    obtain ⟨b, hb, rfl⟩ := hmem_word word hword
    rw [m₂.eval_runClosedConfigFrom_eq_of_halted _ (ht₂ a b hb) (hm₂ b).2] at hfinal
    exact (hm₂ b).2 final hfinal
  have hstep : 2 * t₁ a + t₂' a + 4 = t₁ a + (t₁ a + 4 + t₂' a) := by omega
  dsimp only
  rw [hstep]
  refine ⟨?_, Turing.MultiTapePTM.comp_halted m₁ m₂ true (input a) (t₁ a) (t₂' a) hhalt₁ hhalt₂⟩
  rw [Turing.MultiTapePTM.eval_comp m₁ m₂ true (input a) (t₁ a) (t₂' a) hhalt₁ hhalt₂,
    ProbComp.eval_bind, PMF.map_bind]
  change (ProbComp.eval (first a)).bind (fun b => (ProbComp.eval (second b)).map output) =
    (ProbComp.eval (m₁.runClosed (t₁ a) (input a))).bind
      (fun word => ProbComp.eval (m₂.runClosed (t₂' a) word))
  rw [← hout₁, PMF.bind_map]
  refine PMF.bind_congr_on_support _ _ _ fun b hb => ?_
  dsimp only [Function.comp_def]
  rw [m₂.eval_runClosed_eq_of_halted (middle b) (ht₂ a b hb) (hm₂ b).2]
  exact (hm₂ b).1

/-- A polynomially bounded halting schedule gives a uniform strict PPT certificate. -/
theorem isPPTOn (ht : PolyBounded (fun a => (input a).length) t)
    (h : ComputesInTimeOn input output t program) :
    IsPPTOn input output program := by
  obtain ⟨c, d, hle⟩ := ht.exists_le
  obtain ⟨k, State, hfinite, machine, hmachine⟩ := h.mono hle
  exact ⟨k, State, hfinite, machine, c, d, fun a => (hmachine a).1⟩

end ComputesInTimeOn

/-- A program returning its declared encoding has the same explicit-time halting certificates. -/
theorem computesInTimeOn_iff_encoded {α β : Type} {input : α ↪ List Bool}
    {output : β ↪ List Bool} {t : α → ℕ} {program : α → ProbComp β} :
    ComputesInTimeOn input output t program ↔
      ComputesInTimeOn input encBits t (fun a => output <$> program a) := by
  simp only [ComputesInTimeOn, ProbComp.eval_map, encBits, Function.Embedding.coe_refl, PMF.map_id]

end Cslib.Probability

/-- Lift a plain deterministic time-and-space computation to a fair-coin halting realization with
the exact same step bound `t`. -/
theorem Turing.MultiTapeTM.ComputableInTimeAndSpace.computesInTimeOn {α β : Type}
    {input : α ↪ List Bool} {output : β ↪ List Bool} {f : α → β} {t s : α → ℕ}
    (h : ComputableInTimeAndSpace f input output t s) :
    Cslib.Probability.ComputesInTimeOn input output t (fun a => pure (f a)) := by
  obtain ⟨k, State, hfinite, tm, htm⟩ := h
  refine ⟨k, State, hfinite, Turing.MultiTapePTM.ofDeterministic tm, fun a => ?_⟩
  obtain ⟨⟨u, hu, hout⟩, htime, -⟩ := htm a
  have hhalt : (tm.runFrom (tm.initCfg (input a)) (t a)).state = none :=
    Turing.MultiTapeTM.runsInTime_iff_halted.mp htime
  have heq : tm.runFrom (tm.initCfg (input a)) u = tm.runFrom (tm.initCfg (input a)) (t a) := by
    rcases le_total u (t a) with hut | htu
    · exact (tm.runFrom_eq_of_halt _ hut hu).symm
    · exact tm.runFrom_eq_of_halt _ htu hhalt
  refine ⟨?_, ?_⟩
  · rw [Cslib.ProbComp.eval_pure, PMF.pure_map,
      Turing.MultiTapePTM.eval_runClosed_ofDeterministic, ← heq, hout]
  · intro final hfinal
    change final ∈ (Cslib.ProbComp.eval
      ((Turing.MultiTapePTM.ofDeterministic tm).runClosedConfigFrom (t a)
        ((Turing.MultiTapePTM.ofDeterministic tm).initialConfig (input a)))).support at hfinal
    rw [Turing.MultiTapePTM.eval_runClosedConfigFrom_ofDeterministic,
      PMF.mem_support_pure_iff] at hfinal
    rw [hfinal]
    exact hhalt

namespace Cslib.Probability

open Turing.MultiTapeTM

/-- Deterministically prepare the input of an explicit-time halting probabilistic program. -/
theorem ComputesInTimeOn.preprocess {α β γ : Type} {input : α ↪ List Bool}
    {middle : β ↪ List Bool} {output : γ ↪ List Bool}
    {tp : β → ℕ} {tf sf : α → ℕ} {program : β → ProbComp γ} {prepare : α → β}
    (hprogram : ComputesInTimeOn middle output tp program)
    (hprepare : ComputableInTimeAndSpace prepare input middle tf sf) :
    ComputesInTimeOn input output (fun a => 2 * tf a + tp (prepare a) + 4)
      (fun a => program (prepare a)) := by
  refine (hprepare.computesInTimeOn.bind hprogram ?_).congr fun a => by simp
  intro a b hb
  rw [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hb
  rw [hb]

/-- Deterministically postprocess every sampled result of an explicit-time halting program. -/
theorem ComputesInTimeOn.map {α β γ : Type} {input : α ↪ List Bool}
    {middle : β ↪ List Bool} {output : γ ↪ List Bool}
    {tp tf' : α → ℕ} {tf sf : β → ℕ} {program : α → ProbComp β} {f : β → γ}
    (hprogram : ComputesInTimeOn input middle tp program)
    (hf : ComputableInTimeAndSpace f middle output tf sf)
    (htf : ∀ a b, b ∈ (ProbComp.eval (program a)).support → tf b ≤ tf' a) :
    ComputesInTimeOn input output (fun a => 2 * tp a + tf' a + 4)
      (fun a => f <$> program a) := by
  simpa only [bind_pure_comp] using hprogram.bind hf.computesInTimeOn htf

/-- Postprocess with a deterministic length-indexed bound under a monotone step function, using
`hprogram.length_le` to bound the intermediate encoded word length by `tp a`. -/
theorem ComputesInTimeOn.map_ofLength {α β γ : Type} {input : α ↪ List Bool}
    {middle : β ↪ List Bool} {output : γ ↪ List Bool}
    {tp : α → ℕ} {tf sf : ℕ → ℕ} {program : α → ProbComp β} {f : β → γ}
    (hprogram : ComputesInTimeOn input middle tp program)
    (hf : ComputableInTimeAndSpaceOfLength f middle output tf sf)
    (hmono : Monotone tf) :
    ComputesInTimeOn input output (fun a => 2 * tp a + tf (tp a) + 4)
      (fun a => f <$> program a) :=
  hprogram.map hf fun a _ hb => hmono (hprogram.length_le a hb)

/-- **Uniform strict PPT is equivalent to halting realization under a polynomially bounded step
schedule.** The forward direction compiles the clocked witness via `IsPPTOn.exists_halting_machine`;
the backward direction pads the halting schedule via `ComputesInTimeOn.mono`. -/
theorem isPPTOn_iff_exists_polyBounded_computesInTimeOn {α β : Type}
    {input : α ↪ List Bool} {output : β ↪ List Bool} {program : α → ProbComp β} :
    IsPPTOn input output program ↔
      ∃ t, PolyBounded (fun a => (input a).length) t ∧
        ComputesInTimeOn input output t program := by
  constructor
  · intro h
    obtain ⟨k, State, hfinite, machine, c, d, hout, hhalt⟩ := h.exists_halting_machine
    exact ⟨fun a => c * ((input a).length + 1) ^ d,
      PolyBounded.of_forall_le c d (fun _ => le_rfl),
      k, State, hfinite, machine, fun a => ⟨hout a, hhalt (input a)⟩⟩
  · rintro ⟨t, ht, hcomp⟩
    exact hcomp.isPPTOn ht

namespace ComputesInTime

variable {β : Type} {output : β ↪ List Bool} {t t₁ t₂ : ℕ → ℕ → ℕ}
  {program program' : ℕ → List Bool → ProbComp β}

/-- Expose the underlying `ComputesInTimeOn` certificate on `encPair encUnary encBits`. -/
theorem on (h : ComputesInTime output t program) :
    ComputesInTimeOn (encPair encUnary encBits) output
      (fun input => t input.1 input.2.length) (fun input => program input.1 input.2) := h

/-- Enlarging a parameterized step schedule preserves halting realization unconditionally. -/
theorem mono (h : ComputesInTime output t₁ program) (hle : ∀ n m, t₁ n m ≤ t₂ n m) :
    ComputesInTime output t₂ program :=
  h.on.mono fun input => hle input.1 input.2.length

/-- Distributional equality preserves parameterized halting realization. -/
theorem congr (h : ComputesInTime output t program)
    (heq : ∀ n aux, ProbComp.eval (program n aux) = ProbComp.eval (program' n aux)) :
    ComputesInTime output t program' :=
  h.on.congr fun input => heq input.1 input.2

/-- Every supported encoded output on `(n, aux)` has length at most `t n aux.length`. -/
theorem length_le (h : ComputesInTime output t program) (n : ℕ) (aux : List Bool) {result : β}
    (hresult : result ∈ (ProbComp.eval (program n aux)).support) :
    (output result).length ≤ t n aux.length :=
  h.on.length_le (n, aux) hresult

/-- A polynomially bounded parameterized halting schedule gives `IsPPT`. -/
theorem isPPT (ht : PolyBounded (fun p : ℕ × ℕ => p.1 + p.2) (Function.uncurry t))
    (h : ComputesInTime output t program) :
    IsPPT output program := by
  refine IsPPTOn.isPPT (h.on.isPPTOn ?_)
  refine ht.comp (g := fun input : ℕ × List Bool => (input.1, input.2.length)) ?_
  refine PolyBounded.of_forall_le 1 1 fun input => ?_
  enc_len [pow_one, one_mul]

end ComputesInTime

/-- **Parameterized uniform strict PPT is equivalent to `ComputesInTime` under a polynomially
bounded schedule in `n + aux.length`.** -/
theorem isPPT_iff_exists_polyBounded_computesInTime {β : Type}
    {output : β ↪ List Bool} {program : ℕ → List Bool → ProbComp β} :
    IsPPT output program ↔
      ∃ t : ℕ → ℕ → ℕ,
        PolyBounded (fun p : ℕ × ℕ => p.1 + p.2) (Function.uncurry t) ∧
        ComputesInTime output t program := by
  constructor
  · intro h
    obtain ⟨t₀, ht₀, hcomp⟩ := isPPTOn_iff_exists_polyBounded_computesInTimeOn.mp h.on
    obtain ⟨c, d, hle⟩ := ht₀.exists_le
    refine ⟨fun n m => c * 2 ^ d * (n + m + 1) ^ d,
      PolyBounded.of_forall_le (c * 2 ^ d) d (fun p => le_rfl), ?_⟩
    refine hcomp.mono fun input => (hle input).trans ?_
    have hsize : (encPair encUnary encBits input).length + 1 ≤
        2 * (input.1 + input.2.length + 1) := by
      enc_len
    calc c * ((encPair encUnary encBits input).length + 1) ^ d
        ≤ c * (2 * (input.1 + input.2.length + 1)) ^ d :=
          Nat.mul_le_mul_left c (Nat.pow_le_pow_left hsize d)
      _ = c * 2 ^ d * (input.1 + input.2.length + 1) ^ d := by
          rw [Nat.mul_pow, ← Nat.mul_assoc]
  · rintro ⟨t, ht, hcomp⟩
    exact hcomp.isPPT ht

end Cslib.Probability
