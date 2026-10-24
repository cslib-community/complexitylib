/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Oracle.Closure
public import Complexity.Computability.Complexity.Classes.Space
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
import Complexity.Computability.Complexity.Classes.Oracle.Deterministic
import Complexity.Computability.Complexity.Classes.Space.Closure
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.Simulation
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain

/-!
# Polynomial time relative to an oracle in polynomial space

Relative to an oracle language decided within polynomial space, polynomial time and
nondeterministic polynomial time are within polynomial space [Arora and Barak, Theorem
3.7][AroraBarak09]: `NP^A ⊆ NPSPACE = PSPACE` for `A ∈ PSPACE`.

A computation in polynomial time relative to `A` is the clocked run, with every coin fixed to
`false`, of a finite oracle machine (`Cslib.Probability.IsOraclePPTOn.exists_fin_run_pure_false`).
The run is simulated instruction by instruction, answering each query with the decider of `A` on
the request, which is no longer than the clock
(`Turing.MultiTapePTM.exists_computableTidilyInO_run`).
So the space is polynomial, while the time charges the decider of `A` once per instruction
(`Cslib.Complexity.ComputableInPolyTimeWithOracle.exists_computableInO`,
`Cslib.Complexity.PWithOracle_subset_PSPACE`).

For `NP` relative to `A`, `Cslib.Complexity.mem_PSPACE_of_isVerifier` and
`Cslib.Complexity.NPWithOracle_subset_PSPACE` follow from closure of `PSPACE` under polynomially
bounded existential quantification (`Cslib.Complexity.setOf_exists_mem_PSPACE`).

## Main results

* `Cslib.Complexity.exists_computableInO_of_mem_PSPACE`,
  `Cslib.Complexity.mem_PSPACE_of_computableInO`: `PSPACE` in terms of computability within
  explicit bounds.
* `Cslib.Complexity.mem_PSPACE_of_isVerifier`: certificate search within polynomial space.
* `Cslib.Complexity.ComputableInPolyTimeWithOracle.exists_computableInO`: polynomial time
  relative to an oracle in `PSPACE` is within polynomial space.
* `Cslib.Complexity.PWithOracle_subset_PSPACE`, `Cslib.Complexity.NPWithOracle_subset_PSPACE`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

variable {α β : Type} {enc : α ↪ List Bool}

/-! ### `PSPACE` through explicit time and space bounds -/

/-- A problem in `PSPACE` has a decider within explicit bounds, the space polynomial in the
length of the encoded instance. -/
theorem exists_computableInO_of_mem_PSPACE {L : Set α} (hL : L ∈ PSPACE enc) :
    ∃ T S, PolyBounded (fun a => (enc a).length) S ∧
      ∃ f : α → Bool, Turing.MultiTapeTM.ComputableInO f enc encBool T S ∧ ∀ a, a ∈ L ↔ f a =
        true :=
  let ⟨f, T, S, hf, hS, hL⟩ := mem_PSPACE_iff_computableInO.mp hL
  ⟨T, S, hS, f, hf, hL⟩

/-- A decider within polynomial space puts a problem in `PSPACE`. -/
theorem mem_PSPACE_of_computableInO {L : Set α} {f : α → Bool} {T S : α → ℕ}
    (hf : Turing.MultiTapeTM.ComputableInO f enc encBool T S)
      (hS : PolyBounded (fun a => (enc a).length) S)
    (hL : ∀ a, a ∈ L ↔ f a = true) : L ∈ PSPACE enc :=
  mem_PSPACE_iff_computableInO.mpr ⟨f, T, S, hf, hS, hL⟩

/-! ### Certificate search -/

/-- **Certificate search in polynomial space.** A problem with a verifier decidable within
polynomial space and certificates of polynomial length is in `PSPACE`, by closure of `PSPACE` under
polynomially bounded existential quantification (`Cslib.Complexity.setOf_exists_mem_PSPACE`). -/
theorem mem_PSPACE_of_isVerifier {p : Polynomial ℕ} {V : α × List Bool → Bool} {L : Set α}
    {T S : α × List Bool → ℕ}
      (hV : Turing.MultiTapeTM.ComputableInO V (encPair enc encBits) encBool T S)
    (hS : PolyBounded (fun x => (encPair enc encBits x).length) S) (hL : IsVerifier enc p V L) :
    L ∈ PSPACE enc := by
  have hB : {x | V x = true} ∈ PSPACE (encPair enc encBits) :=
    mem_PSPACE_of_computableInO hV hS fun _ => Iff.rfl
  have hℓ : Turing.MultiTapeTM.ComputableInPolyTime (fun a : α => p.eval (enc a).length) enc
      encUnary :=
    (Turing.MultiTapeTM.ComputableInPolyTime.unary_eval p).comp (.encoding_length enc)
  have hEq : L = {x | ∃ w : List Bool, w.length = p.eval (enc x).length ∧
      (x, w) ∈ {x : α × List Bool | V x = true}} :=
    Set.ext fun a => hL a
  exact hEq ▸ setOf_exists_mem_PSPACE hB hℓ

/-! ### Oracles in polynomial space -/

open Classical in
/-- **Oracle polynomial time within polynomial space.** Relative to an oracle language in
`PSPACE`, a function computable in polynomial time relative to it is computable within space
polynomial in the length of the encoded input. -/
theorem ComputableInPolyTimeWithOracle.exists_computableInO {A : Set (List Bool)}
    {f : α → β} {output : β ↪ List Bool} (hA : A ∈ PSPACE encBits)
    (hf : ComputableInPolyTimeWithOracle A f enc output) :
    ∃ T S, PolyBounded (fun a => (enc a).length) S ∧ ComputableInO f enc output T S := by
  obtain ⟨TA, SA, hSA, g, hg, hgA⟩ := exists_computableInO_of_mem_PSPACE hA
  have hg' : g = fun w => decide (w ∈ A) := funext fun w =>
    Bool.eq_iff_iff.mpr ⟨fun h => decide_eq_true ((hgA w).mpr h),
      fun h => (hgA w).mp (of_decide_eq_true h)⟩
  subst hg'
  obtain ⟨program, hcert, hprogram⟩ := hf
  obtain ⟨k, m, machine, c, d, hrun⟩ := hcert.exists_fin_run_pure_false
  obtain ⟨T, S, hS, h⟩ := machine.exists_computableTidilyInO_run (input := enc) hg.tidy
    (by simpa [encBits] using hSA) c d
  refine ⟨T, S, hS, .of_tidy <| h.of_enc_eq fun a => ?_⟩
  rw [← hprogram a, ← hrun a (languageOracle A)]
  rfl

/-- **`P` relative to an oracle in `PSPACE` is within `PSPACE`.** -/
theorem PWithOracle_subset_PSPACE {A : Set (List Bool)} (hA : A ∈ PSPACE encBits) :
    PWithOracle A enc ⊆ PSPACE enc := fun _ ⟨_, hf, hL⟩ =>
  let ⟨_, _, hS, h⟩ := hf.exists_computableInO hA
  mem_PSPACE_of_computableInO h hS hL

/-- **`NP` relative to an oracle in `PSPACE` is within `PSPACE`** [Arora and Barak, Theorem
3.7][AroraBarak09]: the verifier runs within polynomial space, and its certificates are searched
within polynomial space. -/
theorem NPWithOracle_subset_PSPACE {A : Set (List Bool)} (hA : A ∈ PSPACE encBits) :
    NPWithOracle A enc ⊆ PSPACE enc := fun _ ⟨_, _, hV, hL⟩ =>
  let ⟨_, _, hS, h⟩ := hV.exists_computableInO hA
  mem_PSPACE_of_isVerifier h hS hL

end Cslib.Complexity
