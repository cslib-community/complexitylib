/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Oracle
public import Complexity.Computability.Complexity.Reduction
public import Complexity.Computability.Probabilistic.Oracle.Composition
import Complexity.Computability.Complexity.Classes.Oracle.QueryBit
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Cslib.Foundations.Data.Polynomial.Monotone

/-!
# Closure properties of the oracle classes

Polynomial time relative to an oracle composes with polynomial-time pre- and postprocessing
(`Cslib.Complexity.ComputableInPolyTimeWithOracle.preprocess`,
`Cslib.Complexity.ComputableInPolyTimeWithOracle.map`), through the compositional rules of strict
oracle PPT. One request decides the oracle language itself
(`Cslib.Complexity.computableInPolyTimeWithOracle_mem`): the request is copied onto the query
buffer, and only the first bit of the reply is read (`Cslib.Complexity.queryBit`).

Hence `P` relative to `A` contains `A` and lies inside `NP` relative to `A`, and both classes are
closed under polynomial-time many-one reductions of the problem
(`Cslib.Complexity.PolyTimeReducible.mem_PWithOracle`,
`Cslib.Complexity.PolyTimeReducible.mem_NPWithOracle`). For `NP` the certificates are padded to a
polynomial of the instance length, and the verifier reads only the prefix of the length the
reduced instance requires.

## Main results

* `Cslib.Complexity.ComputableInPolyTimeWithOracle.preprocess`,
  `Cslib.Complexity.ComputableInPolyTimeWithOracle.map`,
  `Cslib.Complexity.ComputableInPolyTimeWithOracle.map_with`: pre- and postprocessing.
* `Cslib.Complexity.ComputableInPolyTimeWithOracle.prod`: retain two oracle results.
* `Cslib.Complexity.PolyTimeOracleProgram.of_query`: one polynomial-time request decides membership
  in every admissible oracle language.
* `Cslib.Complexity.computableInPolyTimeWithOracle_mem`, `Cslib.Complexity.mem_PWithOracle_self`:
  one request decides the oracle language.
* `Cslib.Complexity.PWithOracle_subset_NPWithOracle`.
* `Cslib.Complexity.PolyTimeReducible.mem_PWithOracle`,
  `Cslib.Complexity.PolyTimeReducible.mem_NPWithOracle`: closure under polynomial-time many-one
  reductions.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Probability _root_.Turing.MultiTapeTM

variable {α β γ : Type} {A : Set (List Bool)} {input : α ↪ List Bool} {middle : β ↪ List Bool}
  {output : γ ↪ List Bool}

namespace ComputableInPolyTimeWithOracle

/-- Polynomial-time preprocessing of the argument. -/
theorem preprocess {f : β → γ} {g : α → β} (hf : ComputableInPolyTimeWithOracle A f middle output)
    (hg : Turing.MultiTapeTM.ComputableInPolyTime g input middle) :
    ComputableInPolyTimeWithOracle A (fun a => f (g a)) input output :=
  let ⟨program, hprogram, heq⟩ := hf
  ⟨fun a => program (g a), hprogram.preprocess' hg, fun a => heq (g a)⟩

/-- Polynomial-time postprocessing of the result, which may also use the argument. -/
theorem map_with {f : α → β} {g : α → β → γ}
    (hf : ComputableInPolyTimeWithOracle A f input middle)
    (hg : Turing.MultiTapeTM.ComputableInPolyTime (fun pair => g pair.1 pair.2)
      (encPair input middle) output) :
    ComputableInPolyTimeWithOracle A (fun a => g a (f a)) input output := by
  obtain ⟨program, hprogram, heq⟩ := hf
  refine ⟨fun a => g a <$> program a, ?_, fun a => ?_⟩
  · simpa only [OracleComp.interpret_map] using hprogram.map_with' hg
  · rw [OracleComp.interpret_map, heq]
    rfl

/-- Polynomial-time postprocessing of the result. -/
theorem map {f : α → β} {g : β → γ} (hf : ComputableInPolyTimeWithOracle A f input middle)
    (hg : Turing.MultiTapeTM.ComputableInPolyTime g middle output) :
    ComputableInPolyTimeWithOracle A (fun a => g (f a)) input output := by
  obtain ⟨program, hprogram, heq⟩ := hf
  refine ⟨fun a => g <$> program a, ?_, fun a => ?_⟩
  · simpa only [OracleComp.interpret_map] using hprogram.map' hg
  · rw [OracleComp.interpret_map, heq]
    rfl

/-- Compute two results sequentially against the same oracle, retaining both outputs. -/
theorem prod {f : α → β} {g : α → γ}
    (hf : ComputableInPolyTimeWithOracle A f input middle)
    (hg : ComputableInPolyTimeWithOracle A g input output) :
    ComputableInPolyTimeWithOracle A (fun a => (f a, g a)) input (encPair middle output) := by
  obtain ⟨first, hfirst, hfirst_eq⟩ := hf
  obtain ⟨second, hsecond, hsecond_eq⟩ := hg
  refine ⟨fun a => do
    let b ← first a
    (fun c => (b, c)) <$> second a, ?_, fun a => ?_⟩
  · simp only [OracleComp.interpret_bind, OracleComp.interpret_map]
    exact hfirst.bind_with ((hsecond.preprocess'
      (ComputableInPolyTime.fst input middle)).map_with'
      (((ComputableInPolyTime.snd input middle).comp (.fst _ _)).prod (.snd _ _)))
  · simp only [OracleComp.interpret_bind, OracleComp.interpret_map, hfirst_eq, hsecond_eq]
    rfl

end ComputableInPolyTimeWithOracle

open Classical in
/-- One polynomial-time request `req a` to the oracle language decides whether `req a ∈ A` against
every admissible oracle language `A`. -/
theorem PolyTimeOracleProgram.of_query {req : α → List Bool} {input : α ↪ List Bool}
    {Admissible : Set (List Bool) → Prop} {Spec : (α → Bool) → Prop}
    (hreq : ComputableInPolyTime req input encBits)
    (hSpec : ∀ A : Set (List Bool), Admissible A → Spec (fun a => decide (req a ∈ A))) :
    PolyTimeOracleProgram input encBool Admissible Spec :=
  ⟨fun a => queryBit (req a), isOraclePPTOn_queryBit hreq, fun A hA => by
    simpa only [interpret_queryBit] using hSpec A hA⟩

open Classical in
/-- **One request decides the oracle language.** The word is copied onto the query buffer and
the first bit of the reply is read. -/
theorem computableInPolyTimeWithOracle_mem (A : Set (List Bool)) :
    ComputableInPolyTimeWithOracle A (fun w => decide (w ∈ A)) encBits encBool := by
  rw [computableInPolyTimeWithOracle_iff_polyTimeOracleProgram]
  exact PolyTimeOracleProgram.of_query (req := id) ComputableInPolyTime.id' fun _ hA => hA ▸ rfl

/-- **`P` relative to `A` contains `A`.** -/
theorem mem_PWithOracle_self (A : Set (List Bool)) : A ∈ PWithOracle A encBits := by
  classical
  exact ⟨_, computableInPolyTimeWithOracle_mem A, fun w => decide_eq_true_iff.symm⟩

/-- **`P` relative to `A` lies inside `NP` relative to `A`**: a decider ignores the empty
certificate. -/
theorem PWithOracle_subset_NPWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) :
    PWithOracle A enc ⊆ NPWithOracle A enc := fun _ ⟨f, hf, h⟩ =>
  ⟨0, fun aw => f aw.1, hf.preprocess (ComputableInPolyTime.fst enc encBits),
    fun a => by
    simp only [Polynomial.eval_zero, List.length_eq_zero_iff, exists_eq_left, h]⟩

/-- **`P` relative to an oracle is closed under polynomial-time many-one reductions.** -/
theorem PolyTimeReducible.mem_PWithOracle {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {L : Set α} {L' : Set β} (h : PolyTimeReducible encA encB L L')
    (hL' : L' ∈ PWithOracle A encB) : L ∈ PWithOracle A encA :=
  let ⟨g, hg, hL⟩ := h
  let ⟨f, hf, hL'⟩ := hL'
  ⟨fun a => f (g a), hf.preprocess hg, fun a => (hL a).trans (hL' (g a))⟩

/-- **`NP` relative to an oracle is closed under polynomial-time many-one reductions.** The
certificates are padded to a polynomial of the instance length; the verifier reads the prefix of
the length required by the reduced instance. -/
theorem PolyTimeReducible.mem_NPWithOracle {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {L : Set α} {L' : Set β} (h : PolyTimeReducible encA encB L L')
    (hL' : L' ∈ NPWithOracle A encB) : L ∈ NPWithOracle A encA := by
  obtain ⟨g, hg, hL⟩ := h
  obtain ⟨p, V, hV, hL'⟩ := hL'
  obtain ⟨r, hlen⟩ := hg.polyBounded_length.exists_polynomial
  -- the certificate length of the reduced instance, as a polynomial of the instance length
  set q : Polynomial ℕ := p.comp r with hq
  have hpq (a : α) : p.eval (encB (g a)).length ≤ q.eval (encA a).length := by
    rw [hq, Polynomial.eval_comp]
    exact p.eval_mono (hlen a)
  refine ⟨q, fun aw => V (g aw.1, aw.2.take (p.eval (encB (g aw.1)).length)),
    hV.preprocess (f := V) (g := fun aw : α × List Bool =>
      (g aw.1, aw.2.take (p.eval (encB (g aw.1)).length))) (by fun_prop), fun a => ?_⟩
  rw [hL a, hL' (g a)]
  constructor
  · rintro ⟨w, hw, hV⟩
    refine ⟨w ++ List.replicate (q.eval (encA a).length - w.length) false, ?_, ?_⟩
    · rw [List.length_append, List.length_replicate, hw]
      exact Nat.add_sub_cancel' (hw ▸ hpq a)
    · simpa [← hw] using hV
  · rintro ⟨w, hw, hV⟩
    refine ⟨w.take (p.eval (encB (g a)).length), ?_, hV⟩
    rw [List.length_take, hw]
    exact Nat.min_eq_left (hpq a)

end Cslib.Complexity
