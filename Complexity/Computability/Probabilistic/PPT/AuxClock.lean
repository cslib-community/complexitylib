/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.PrefixLocality
public import Complexity.Computability.Probabilistic.Oracle.Composition
public import Complexity.Computability.Probabilistic.PPT.Composition
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.QueryBounds
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Basic

/-!
# Probabilistic polynomial-time programs clocked in a designated primary input

In auxiliary-input cryptography (such as Goldreich's definition of auxiliary-input zero knowledge),
a probabilistic machine receives a primary input `a : α` together with an arbitrary, potentially
unbounded auxiliary input word `z : List Bool` on its input tape `encPair input encBits (a, z) =
frame (input a) ++ z`, while its polynomial step bound `c * ((input a).length + 1) ^ d` is a
function of the primary input length `(input a).length` alone.

`IsPPTWithAux` and `IsOraclePPTWithAux` capture this machine contract for closed and oracle
probabilistic programs. Because `frame (input a)` is self-delimiting (`unframe (frame (input a) ++
z) = input a`), a machine can recover the primary input length from the combined input tape without
scanning `z`. Generalizing `IsTidyOraclePPTOn.runOracle` to any polynomial-time computable clock
therefore shows that every `IsOraclePPTWithAux` (resp. `IsPPTWithAux`) program is automatically a
standard `IsOraclePPTOn` (resp. `IsPPTOn`) program on `encPair input encBits`. Moreover, by the
input-tape prefix-locality theorem (`runOracle_append_take` / `runClosed_append_take`), a run of
`T = c * ((input a).length + 1) ^ d` steps on `frame (input a) ++ z` depends only on `z.take T`.

## Main definitions

* `Cslib.Probability.IsPPTWithAux`: closed uniform strict PPT clocked in the primary input.
* `Cslib.Probability.IsOraclePPTWithAux`: oracle uniform strict PPT clocked in the primary input.

## Main results

* `Cslib.Probability.IsTidyOraclePPTOn.runOracle_of_clock`: any finite-control oracle machine run
  under a polynomial-time computable clock `clock : List Bool → ℕ` is a clean phase.
* `Cslib.Probability.IsPPTWithAux.of_machine`,
  `Cslib.Probability.IsOraclePPTWithAux.of_machine`: explicit finite-control machine constructors.
* `Cslib.Probability.IsOraclePPTWithAux.isOraclePPTOn`,
  `Cslib.Probability.IsPPTWithAux.isPPTOn`: prefix-clocked programs are standard `IsOraclePPTOn`
  and `IsPPTOn` programs on `encPair input encBits`.
* `Cslib.Probability.computableInPolyTime_take_aux`,
  `Cslib.Probability.IsPPTOn.take_aux`,
  `Cslib.Probability.IsOraclePPTOn.take_aux`: truncating the auxiliary input to length
  `c * ((input a).length + 1) ^ d` preserves `IsPPTOn` and `IsOraclePPTOn`.
* `Cslib.Probability.IsOraclePPTWithAux.exists_run_interpret_take`,
  `Cslib.Probability.IsPPTWithAux.exists_eval_take`: a prefix-clocked program on `(a, z)` has the
  exact same semantics as on `(a, z.take m)` for every `m ≥ c * ((input a).length + 1) ^ d`.
-/

@[expose] public section

namespace Cslib.Probability

open _root_.Turing _root_.Turing.MultiTapeMachine _root_.Turing.MultiTapeTM
  _root_.Turing.MultiTapePTM

variable {Operation α β : Type} [DecidableEq Operation]
  {input : α ↪ List Bool} {output : β ↪ List Bool}

private theorem pmf_eq_of_map_eq {γ δ : Type*} {f : γ → δ} (hf : Function.Injective f)
    {p q : PMF γ} (h : p.map f = q.map f) : p = q := by
  classical
  ext x
  have hiff (a : γ) : (f x = f a) ↔ (x = a) := hf.eq_iff
  have hfx := congrFun (congrArg DFunLike.coe h) (f x)
  simpa [PMF.map_apply, hiff] using hfx

/-- Every clocked run of a finite-control oracle machine under a polynomial-time computable clock
`clock : List Bool → ℕ` is a clean phase. -/
theorem IsTidyOraclePPTOn.runOracle_of_clock {k : ℕ} {Control : Type}
    [Finite Operation] [Finite Control]
    (machine : _root_.Turing.MultiTapePTM k Bool Control Operation)
    {clock : List Bool → ℕ} (hclock : ComputableInPolyTime clock encBits encUnary) :
    IsTidyOraclePPTOn encBits encBits
      (fun word : List Bool => machine.runOracle (clock word) word) := by
  let _ := Fintype.ofFinite Operation
  obtain ⟨cf, hconfigurationSize⟩ :=
    length_encFiniteConfig_le (k := k) (State := Control) (Oracle := Operation)
  have hclockPoly : PolyBounded (fun word => (encBits word).length) clock := by
    simpa only [encUnary_apply, List.length_replicate] using hclock.polyBounded_length
  have hstart : ComputableInPolyTime
      (fun word => FiniteConfig.init (k := k) (Oracle := Operation) machine.initial word)
      encBits encFiniteConfig := by fun_prop
  let step (word : List Bool) (cfg : FiniteConfig k Bool Control Operation) :
      WordOracleComp Operation (FiniteConfig k Bool Control Operation) :=
    machine.finiteStep (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
      (fun op query => List.take (clock word) <$> ProbOracleComp.query (op, query)) cfg
  have hstep : IsTidyOraclePPTOn (encPair encBits encFiniteConfig) encFiniteConfig
      (fun pair => step pair.1 pair.2) :=
    (IsTidyOraclePPTOn.finiteStep machine).preprocess
      (prepare := fun pair : List Bool × FiniteConfig k Bool Control Operation =>
        (clock pair.1, pair.2)) (by fun_prop)
  have hloop := (IsTidyOraclePPTOn.iterateWith_spec hclock hstart hstep
    (fun word i cfg => FiniteConfig.SpaceBound word.length i (clock word) cfg)
    (fun word => FiniteConfig.spaceBound_init _ _ _)
    (by
      intro word i cfg _ hcfg next hnext
      cases hstate : cfg.tapes.state with
      | none =>
        simp only [step, MultiTapeMachine.finiteStep, hstate] at hnext
        exact (OracleComp.eq_of_mem_supportWith_pure hnext) ▸
          hcfg.mono le_rfl (Nat.le_succ i) le_rfl
      | some control =>
        simp only [step, MultiTapeMachine.finiteStep, hstate] at hnext
        obtain ⟨action, _, hnext⟩ := OracleComp.mem_supportWith_bind_iff.mp hnext
        cases action with
        | step action symbol move =>
          exact (OracleComp.eq_of_mem_supportWith_pure hnext) ▸ hcfg.step action symbol move
        | query channel control =>
          obtain ⟨answer, hanswer, hnext⟩ := OracleComp.mem_supportWith_bind_iff.mp hnext
          obtain ⟨reply, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hanswer
          exact (OracleComp.eq_of_mem_supportWith_pure hnext) ▸
            hcfg.receive channel control _ (List.length_take_le _ _))
    (size := fun word => cf * (word.length + clock word + clock word + 1))
    ((PolyBounded.const cf).mul
      (((PolyBounded.self.add hclockPoly).add hclockPoly).add (.const 1)))
    (fun word i cfg hi hcfg => (hconfigurationSize _ _ _ cfg hcfg).trans
      (Nat.mul_le_mul_left cf (by lia)))).1
  refine (hloop.map (by fun_prop : ComputableInPolyTime
    (fun cfg : FiniteConfig k Bool Control Operation => cfg.tapes.output)
    encFiniteConfig encBits)).congr fun word State oracle s => ?_
  rw [← finiteRunFrom_take_runOracle]
  rfl

/-- **Closed uniform strict PPT clocked in the primary input.** One finite fair-coin machine runs
on the pair encoding `encPair input encBits (a, z) = frame (input a) ++ z`, clocked by a polynomial
`c * ((input a).length + 1) ^ d` in the primary input length `(input a).length` alone. -/
def IsPPTWithAux {α β : Type} (input : α ↪ List Bool) (output : β ↪ List Bool)
    (program : α → List Bool → ProbComp β) : Prop :=
  ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : Turing.MultiTapePTM k Bool State)
    (c d : ℕ), ∀ a z, (ProbComp.eval (program a z)).map output =
      ProbComp.eval (machine.runClosed (c * ((input a).length + 1) ^ d)
        (encPair input encBits (a, z)))

/-- **Oracle uniform strict PPT clocked in the primary input.** One finite oracle fair-coin machine
runs on `encPair input encBits (a, z) = frame (input a) ++ z`, clocked by a polynomial
`c * ((input a).length + 1) ^ d` in `(input a).length` alone, preserving the full joint output and
external oracle state for every stateful handler. -/
def IsOraclePPTWithAux {Operation α β : Type} [DecidableEq Operation]
    (input : α ↪ List Bool) (output : β ↪ List Bool)
    (program : α → List Bool → WordOracleComp Operation β) : Prop :=
  Finite Operation ∧ ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
    (machine : Turing.MultiTapePTM k Bool Control Operation) (c d : ℕ),
    ∀ a z (State : Type) (oracle : Operation × List Bool → StateT State PMF (List Bool)) s,
      (OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (output <$> program a z)).run s =
      (OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (machine.runOracle (c * ((input a).length + 1) ^ d)
            (encPair input encBits (a, z)))).run s

/-- A fixed finite-control closed machine and polynomial clock in the primary input supply an
`IsPPTWithAux` certificate directly. -/
theorem IsPPTWithAux.of_machine {k : ℕ} {State : Type} [Finite State]
    (machine : Turing.MultiTapePTM k Bool State) (c d : ℕ) :
    IsPPTWithAux input encBits
      (fun a z =>
        machine.runClosed (c * ((input a).length + 1) ^ d) (encPair input encBits (a, z))) := by
  refine ⟨k, State, inferInstance, machine, c, d, fun a z => ?_⟩
  simp only [encBits, Function.Embedding.coe_refl, PMF.map_id]

/-- Distributional equality preserves `IsPPTWithAux`. -/
theorem IsPPTWithAux.congr {program program' : α → List Bool → ProbComp β}
    (h : IsPPTWithAux input output program)
    (heq : ∀ a z, ProbComp.eval (program a z) = ProbComp.eval (program' a z)) :
    IsPPTWithAux input output program' := by
  obtain ⟨k, State, hfinite, machine, c, d, h⟩ := h
  exact ⟨k, State, hfinite, machine, c, d, fun a z =>
    (congrArg (PMF.map output) (heq a z)).symm.trans (h a z)⟩

/-- A fixed finite-control oracle machine and polynomial clock in the primary input supply an
`IsOraclePPTWithAux` certificate directly. -/
theorem IsOraclePPTWithAux.of_machine [Finite Operation] {k : ℕ} {Control : Type} [Finite Control]
    (machine : Turing.MultiTapePTM k Bool Control Operation) (c d : ℕ) :
    IsOraclePPTWithAux input encBits
      (fun a z =>
        machine.runOracle (c * ((input a).length + 1) ^ d) (encPair input encBits (a, z))) := by
  refine ⟨inferInstance, k, Control, inferInstance, machine, c, d, fun a z State oracle s => ?_⟩
  simp only [encBits, Function.Embedding.coe_refl, id_map]

/-- Equality of the complete stateful semantics preserves `IsOraclePPTWithAux`. -/
theorem IsOraclePPTWithAux.congr {program program' : α → List Bool → WordOracleComp Operation β}
    (h : IsOraclePPTWithAux input output program)
    (heq : ∀ a z (State : Type) (oracle : Operation × List Bool → StateT State PMF (List Bool)) s,
      (OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (program a z)).run s =
      (OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (program' a z)).run s) :
    IsOraclePPTWithAux input output program' := by
  obtain ⟨hops, k, Control, hfinite, machine, c, d, h⟩ := h
  refine ⟨hops, k, Control, hfinite, machine, c, d, fun a z State oracle s => ?_⟩
  simpa only [OracleComp.interpret_map, StateT.run_map, heq] using h a z State oracle s

/-- Every `IsOraclePPTWithAux` program is a standard `IsOraclePPTOn` program on
`encPair input encBits`: the machine recovers `(input a).length` by unframing the self-delimiting
first component `frame (input a)` without reading `z`. -/
theorem IsOraclePPTWithAux.isOraclePPTOn {program : α → List Bool → WordOracleComp Operation β}
    (h : IsOraclePPTWithAux input output program) :
    IsOraclePPTOn (encPair input encBits) output (fun (a, z) => program a z) := by
  obtain ⟨hops, k, Control, hfinite, machine, c, d, h⟩ := h
  let clock (word : List Bool) : ℕ := c * ((unframe word).length + 1) ^ d
  have hclock : ComputableInPolyTime clock encBits encUnary := by
    dsimp only [clock]
    fun_prop
  have htidy : IsTidyOraclePPTOn (encPair input encBits) encBits
      (fun (a, z) => output <$> program a z) := by
    refine ((IsTidyOraclePPTOn.runOracle_of_clock machine hclock).preprocess
      (ComputableInPolyTime.of_eq (encOut := encBits)
        (f := encPair input encBits) fun _ => rfl)).congr fun (a, z) State oracle s => ?_
    have hunframe : clock (encPair input encBits (a, z)) = c * ((input a).length + 1) ^ d := by
      simp [clock, encPair_apply, unframe_frame_append]
    rw [hunframe, ← h a z State oracle s]
  exact IsOraclePPTOn.iff_encoded.mpr htidy.isOraclePPTOn

/-- Closed `IsPPTWithAux` programs lift to `IsOraclePPTWithAux` with no external operations. -/
theorem IsPPTWithAux.isOraclePPTWithAux {program : α → List Bool → ProbComp β}
    [Finite Operation] (h : IsPPTWithAux input output program) :
    IsOraclePPTWithAux (Operation := Operation) input output
      (fun a z => ProbOracleComp.sample (program a z)) := by
  obtain ⟨k, State, hfinite, machine, c, d, h⟩ := h
  refine ⟨inferInstance, k, State, hfinite, MultiTapePTM.ofClosed machine, c, d,
    fun a z OracleState oracle s => ?_⟩
  rw [MultiTapePTM.run_interpret_runOracle_ofClosed, ← h a z, ← ProbOracleComp.sample_map,
    ProbOracleComp.run_interpret_sample, ProbComp.eval_map]

/-- Every `IsPPTWithAux` program is a standard `IsPPTOn` program on `encPair input encBits`. -/
theorem IsPPTWithAux.isPPTOn {program : α → List Bool → ProbComp β}
    (h : IsPPTWithAux input output program) :
    IsPPTOn (encPair input encBits) output (fun (a, z) => program a z) :=
  (h.isOraclePPTWithAux (Operation := Empty)).isOraclePPTOn.isPPTOn

/-- Truncating the auxiliary input word `z` to a polynomial in the primary input length
`(input a).length` is computable in plain polynomial time on `encPair input encBits`. -/
@[fun_prop]
theorem computableInPolyTime_take_aux (input : α ↪ List Bool) (c d : ℕ) :
    ComputableInPolyTime
      (fun p : α × List Bool => (p.1, p.2.take (c * ((input p.1).length + 1) ^ d)))
      (encPair input encBits) (encPair input encBits) := by
  have hlen : ComputableInPolyTime (fun p : α × List Bool => (input p.1).length)
      (encPair input encBits) encUnary :=
    (ComputableInPolyTime.encoding_length input).comp (.fst input encBits)
  fun_prop

/-- Truncating the auxiliary input of a standard `IsPPTOn` program to a polynomial in the primary
input length preserves `IsPPTOn`. -/
theorem IsPPTOn.take_aux {program : α → List Bool → ProbComp β}
    (h : IsPPTOn (encPair input encBits) output (fun (a, z) => program a z)) (c d : ℕ) :
    IsPPTOn (encPair input encBits) output
      (fun (a, z) => program a (z.take (c * ((input a).length + 1) ^ d))) :=
  h.preprocess (computableInPolyTime_take_aux input c d)

/-- Truncating the auxiliary input of a standard `IsOraclePPTOn` program to a polynomial in the
primary input length preserves `IsOraclePPTOn`. -/
theorem IsOraclePPTOn.take_aux {program : α → List Bool → WordOracleComp Operation β}
    (h : IsOraclePPTOn (encPair input encBits) output (fun (a, z) => program a z)) (c d : ℕ) :
    IsOraclePPTOn (encPair input encBits) output
      (fun (a, z) => program a (z.take (c * ((input a).length + 1) ^ d))) :=
  h.preprocess' (computableInPolyTime_take_aux input c d)

/-- **Prefix truncation for `IsPPTWithAux`.** A closed program clocked in `a` produces the exact
same output distribution on `(a, z.take m)` as on `(a, z)` whenever `m` is at least its polynomial
clock `c * ((input a).length + 1) ^ d`. -/
theorem IsPPTWithAux.exists_eval_take {program : α → List Bool → ProbComp β}
    (h : IsPPTWithAux input output program) :
    ∃ c d : ℕ, ∀ (a : α) (z : List Bool) {m : ℕ},
      c * ((input a).length + 1) ^ d ≤ m →
      ProbComp.eval (program a (z.take m)) = ProbComp.eval (program a z) := by
  obtain ⟨k, State, hfinite, machine, c, d, h⟩ := h
  refine ⟨c, d, fun a z {m} hm => pmf_eq_of_map_eq output.injective ?_⟩
  rw [h a (z.take m), h a z]
  simp only [encPair_apply, encBits, Function.Embedding.coe_refl, id]
  rw [machine.runClosed_append_take_of_le hm]

/-- **Prefix truncation for `IsOraclePPTWithAux`.** An oracle program clocked in `a` produces the
exact same joint distribution of `(result, finalState)` on `(a, z.take m)` as on `(a, z)` under
every stateful oracle handler whenever `m ≥ c * ((input a).length + 1) ^ d`. -/
theorem IsOraclePPTWithAux.exists_run_interpret_take
    {program : α → List Bool → WordOracleComp Operation β}
    (h : IsOraclePPTWithAux input output program) :
    ∃ c d : ℕ, ∀ (a : α) (z : List Bool) {m : ℕ},
      c * ((input a).length + 1) ^ d ≤ m →
      ∀ (State : Type) (oracle : Operation × List Bool → StateT State PMF (List Bool)) (s : State),
        (OracleComp.interpret
          (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
            (program a (z.take m))).run s =
        (OracleComp.interpret
          (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
            (program a z)).run s := by
  obtain ⟨_, k, Control, hfinite, machine, c, d, h⟩ := h
  refine ⟨c, d, fun a z {m} hm State oracle s => ?_⟩
  have hinj : Function.Injective (fun p : β × State => (output p.1, p.2)) := by
    intro ⟨b₁, s₁⟩ ⟨b₂, s₂⟩ heq
    simp only [Prod.mk.injEq] at heq
    exact Prod.ext (output.injective heq.1) heq.2
  apply pmf_eq_of_map_eq hinj
  have h₁ := h a (z.take m) State oracle s
  have h₂ := h a z State oracle s
  simp only [OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map] at h₁ h₂
  rw [h₁, h₂]
  simp only [encPair_apply, encBits, Function.Embedding.coe_refl, id]
  rw [machine.runOracle_append_take_of_le hm]

end Cslib.Probability
