/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.Classes.Oracle.Closure
public import Complexity.Computability.Complexity.Classes.P
public import Complexity.Computability.Complexity.Reduction
public import Complexity.Computability.Complexity.Reduction.Turing

/-!
# Polynomial-time Turing autoreducibility

A set `A` is **polynomial-time Turing autoreducible** if it can be decided in polynomial time
by an oracle machine that never queries its own input (Ambos-Spies 1984; Buhrman et al. 2000;
[Ladner, Lynch and Selman][LadnerLynchSelman1975]).

## Main definitions

* `Cslib.Complexity.PolyTimeTuringAutoreducible`: polynomial-time Turing autoreducibility of an
  encoded language `A`.

## Main results

* `Cslib.Complexity.PolyTimeTuringAutoreducible.polyTimeTuringReducible`: an autoreduction is in
  particular a Turing reduction of `A` to `A`.
* `Cslib.Complexity.polyTimeTuringAutoreducible_bits_iff`: simplified characterization for bitstring
  languages with `encBits`.
* `Cslib.Complexity.polyTimeTuringAutoreducible_of_polyTimeReducible_fixedPointFree`: every
  fixed-point-free polynomial-time many-one reduction of `A` to `A` induces a polynomial-time
  Turing autoreduction.
* `Cslib.Complexity.mem_P.polyTimeTuringAutoreducible`: every language `A ∈ P` is unconditionally
  polynomial-time Turing autoreducible (via a 0-query program). This sharply contrasts with
  many-one autoreducibility, where singleton and co-singleton languages in `P` are strictly
  not many-one autoreducible.

## References

* [R. E. Ladner, N. A. Lynch, A. L. Selman, *A comparison of polynomial time
  reducibilities*][LadnerLynchSelman1975]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Probability
open Turing.MultiTapeTM

variable {α : Type} {encA : α ↪ List Bool} {A : Set α}

/-- `A` is polynomial-time Turing autoreducible: some deterministic polynomial-time oracle program
decides `A` relative to the oracle for `A` without ever querying its own input. -/
def PolyTimeTuringAutoreducible (encA : α ↪ List Bool) (A : Set α) : Prop :=
  ∃ program : α → WordQueryComp Unit Bool,
    IsOraclePPTOn encA encBool (fun a => OracleComp.interpret ProbOracleComp.query (program a)) ∧
    (∀ a, ∀ q ∈ OracleComp.queriesWith (languageOracle (encA '' A)) (program a), q.2 ≠ encA a) ∧
    ∀ a, a ∈ A ↔ OracleComp.interpret (m := Id) (languageOracle (encA '' A)) (program a) = true

/-- A polynomial-time Turing autoreduction is in particular a polynomial-time Turing reduction of
`A` to `A`. -/
theorem PolyTimeTuringAutoreducible.polyTimeTuringReducible
    (h : PolyTimeTuringAutoreducible encA A) : PolyTimeTuringReducible encA encA A A := by
  obtain ⟨program, hPPT, _, hdec⟩ := h
  exact ⟨fun a => OracleComp.interpret (m := Id) (languageOracle (encA '' A)) (program a),
    ⟨program, hPPT, fun _ => rfl⟩, hdec⟩

/-- On bitstring languages with the default encoding `encBits`, the no-self-query condition
simply requires `q.2 ≠ a`. -/
theorem polyTimeTuringAutoreducible_bits_iff {B : Set (List Bool)} :
    PolyTimeTuringAutoreducible encBits B ↔
      ∃ program : List Bool → WordQueryComp Unit Bool,
        IsOraclePPTOn encBits encBool
          (fun a => OracleComp.interpret ProbOracleComp.query (program a)) ∧
        (∀ a, ∀ q ∈ OracleComp.queriesWith (languageOracle B) (program a), q.2 ≠ a) ∧
        ∀ a, a ∈ B ↔ OracleComp.interpret (m := Id) (languageOracle B) (program a) = true := by
  have : encBits '' B = B := Set.image_id B
  simp only [PolyTimeTuringAutoreducible, this, encBits_apply]

open Classical in
/-- Every fixed-point-free polynomial-time many-one reduction of `A` to `A` induces a
polynomial-time Turing autoreduction. -/
theorem polyTimeTuringAutoreducible_of_polyTimeReducible_fixedPointFree
    {f : α → α} (hf : ComputableInPolyTime f encA encA) (hne : ∀ a, f a ≠ a)
    (hA : ∀ a, a ∈ A ↔ f a ∈ A) : PolyTimeTuringAutoreducible encA A := by
  refine ⟨fun a => (fun reply => decide (reply = [true])) <$>
    (List.take 1 <$> OracleComp.query ((), encA (f a))), ?_, fun a q hq => ?_, fun a => ?_⟩
  · simp only [OracleComp.interpret_map, OracleComp.interpret_query]
    exact (IsOraclePPTOn.query_take () hf.tidy (limit := fun _ => 1) (by fun_prop)).map
      (by fun_prop)
  · simp only [OracleComp.queriesWith_map, OracleComp.queriesWith_query,
      List.mem_singleton] at hq
    subst hq
    exact fun h_eq => hne a (encA.injective h_eq)
  · change a ∈ A ↔
      decide (List.take 1 (languageOracle (encA '' A) ((), encA (f a))) = [true]) = true
    rw [languageOracle_apply]
    have hmem : a ∈ A ↔ encA (f a) ∈ encA '' A := by
      rw [hA a, encA.injective.mem_set_image]
    rw [hmem]
    cases hc : decide (encA (f a) ∈ encA '' A)
    · have : encA (f a) ∉ encA '' A := decide_eq_false_iff_not.mp hc
      simp [this]
    · have : encA (f a) ∈ encA '' A := decide_eq_true_iff.mp hc
      simp [this]

/-- **Every problem in `P` is polynomial-time Turing autoreducible.** The decider makes zero
oracle queries, so the no-self-query condition is vacuously satisfied. -/
theorem mem_P.polyTimeTuringAutoreducible
    (hA : A ∈ P encA) : PolyTimeTuringAutoreducible encA A := by
  obtain ⟨f, hf, h_dec⟩ := hA
  refine ⟨fun a => pure (f a), ?_, fun a q hq => ?_, fun a => ?_⟩
  · exact hf.tidy.isOraclePPTOn (Operation := Unit)
  · simp only [OracleComp.queriesWith_pure, List.not_mem_nil] at hq
  · simp only [OracleComp.interpret_pure]
    exact h_dec a

end Cslib.Complexity
