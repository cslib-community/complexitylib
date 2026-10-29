/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.NP
public import Complexity.Computability.Complexity.Classes.P
public import Complexity.Computability.Complexity.Classes.PCP
import Complexity.Computability.Complexity.Classes.PCP.NP
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure

/-!
# PCP without randomness

A PCP verifier (`Cslib.Complexity.PCPVerifier`) that uses no random bits reads the same positions
of the proof on every run, and soundness forces it to reject every proof of a non-member. The
classes with zero randomness are therefore classes of deterministic verification
[Arora and Barak, Chapter 11][AroraBarak09]:

* With no queries either, the verdict depends on the instance alone, so `PCP(0, 0) = P`
  (`Cslib.Complexity.PCP_zero_zero`). Since more randomness and more queries give larger classes,
  `P ⊆ PCP(r, q)` for all `r` and `q`.
* With polynomially many queries, the verifier can read a whole `NP` certificate, so
  `NP ⊆ PCP(0, poly)` (`Cslib.Complexity.exists_mem_PCP_zero_of_mem_NP`). Conversely, a
  verifier using no random bits uses at most logarithmically many, so `PCP(0, q) ⊆ NP` for every
  `q` (`Cslib.Complexity.PCP_log_subset_NP`), and `NP = PCP(0, poly)`
  (`Cslib.Complexity.mem_NP_iff_exists_PCP_zero`).

## Main results

* `Cslib.Complexity.PCP_zero_zero`: `PCP(0, 0) = P`.
* `Cslib.Complexity.P_subset_PCP`: `P ⊆ PCP(r, q)`.
* `Cslib.Complexity.exists_mem_PCP_zero_of_mem_NP`, `Cslib.Complexity.mem_NP_iff_exists_PCP_zero`:
  `NP = PCP(0, poly)`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}


/-- **`PCP(0, 0) = P`**: a verifier with no random bits and no queries decides by its verdict on
the instance alone. -/
theorem PCP_zero_zero : PCP (fun _ => 0) (fun _ => 0) enc = P enc := by
  ext A
  constructor
  · rintro ⟨V, c, d, ⟨-, -, hv⟩, hcoins, hqs, hcomp, hsound⟩
    simp only [mul_zero, nonpos_iff_eq_zero] at hcoins hqs
    refine ⟨fun a => V.verdict ((a, []), []), ?_, fun a => ?_⟩
    · exact hv.comp (g := fun a : α => ((a, ([] : List Bool)), ([] : List Bool))) (by fun_prop)
    · -- with no random bits there are no queries, so the verdict ignores the proof
      have key (π : List Bool) : V.accepts a π [] = V.verdict ((a, []), []) := by
        have h0 : V.queries (a, []) = [] :=
          List.eq_nil_of_length_eq_zero (hqs a [] (by simp [hcoins a]))
        simp [PCPVerifier.accepts, h0, PCPVerifier.answers]
      constructor
      · intro ha
        obtain ⟨π, hπ⟩ := hcomp a ha
        change V.verdict ((a, []), []) = true
        rw [← key π]
        exact hπ [] (by simp [hcoins a])
      · intro hv'
        by_contra ha
        have := hsound a ha []
        rw [hcoins a, acceptCount_zero] at this
        simp [key, hv'] at this
  · rintro ⟨f, hf, hA⟩
    refine ⟨⟨fun _ => 0, fun _ => [], fun x => f x.1.1⟩, 0, 0, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · exact ComputableInPolyTime.const _
    · exact ComputableInPolyTime.const _
    · exact hf.comp ((ComputableInPolyTime.fst enc encBits).comp
        (ComputableInPolyTime.fst (encPair enc encBits) encBits))
    · intro a
      simp
    · intro a ρ _
      simp
    · intro a ha
      refine ⟨[], fun ρ _ => ?_⟩
      simpa [PCPVerifier.accepts] using (hA a).mp ha
    · intro a ha π
      have hfa : f a = false := by simpa [hA a] using ha
      rw [acceptCount_zero]
      simp [PCPVerifier.accepts, hfa]

/-- **`P ⊆ PCP(r, q)`** for all `r` and `q`. -/
theorem P_subset_PCP (r q : ℕ → ℕ) : P enc ⊆ PCP r q enc :=
  PCP_zero_zero (enc := enc) ▸
    (PCP_mono_randomness fun _ => Nat.zero_le _).trans (PCP_mono_queries fun _ => Nat.zero_le _)

/-- **`NP ⊆ PCP(0, poly)`**: with no random bits, the verifier queries the first `p(n)` positions
of the proof, where `n` is the length of the encoded instance and `p(n)` the length of the
certificates, and runs the `NP` verifier on the bits read. -/
theorem exists_mem_PCP_zero_of_mem_NP {A : Set α} (hA : A ∈ NP enc) :
    ∃ k : ℕ, A ∈ PCP (fun _ => 0) (fun n => (n + 1) ^ k) enc := by
  obtain ⟨p, V, hV, hver⟩ := mem_NP.mp hA
  obtain ⟨c, k, hle⟩ := polynomiallyBounded_iff_le.mp (PolynomiallyBounded.polynomial_eval p)
  refine ⟨k, ⟨fun _ => 0, fun x => List.range (p.eval (enc x.1).length),
    fun y => V (y.1.1, y.2)⟩, 0, c, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact ComputableInPolyTime.const _
  · -- `x ↦ range (p (|enc x.1|))`, built in unary and converted elementwise to binary
    have h1 : ComputableInPolyTime (fun x : α × List Bool => p.eval (enc x.1).length)
        (encPair enc encBits) encUnary :=
      (ComputableInPolyTime.unary_eval p).comp
        ((ComputableInPolyTime.encoding_length enc).comp (ComputableInPolyTime.fst enc encBits))
    simpa [Function.comp_def] using
      (ComputableInPolyTime.map ComputableInPolyTime.unary_to_binary).comp
        (ComputableInPolyTime.range.comp h1)
  · exact hV.comp (((ComputableInPolyTime.fst enc encBits).comp
      (ComputableInPolyTime.fst (encPair enc encBits) encBits)).pair
      (ComputableInPolyTime.snd (encPair enc encBits) encBits))
  · intro a
    simp
  · intro a ρ _
    simpa using hle (enc a).length
  · intro a ha
    obtain ⟨w, hw, hVw⟩ := (hver a).mp ha
    refine ⟨w, fun ρ _ => ?_⟩
    simp only [PCPVerifier.accepts]
    rw [← hw, PCPVerifier.answers_range_length]
    exact hVw
  · intro a ha π
    have hrej : V (a, PCPVerifier.answers π (List.range (p.eval (enc a).length))) = false := by
      by_contra h
      exact ha ((hver a).mpr ⟨PCPVerifier.answers π (List.range (p.eval (enc a).length)),
        by simp [PCPVerifier.answers], Bool.not_eq_false _ ▸ h⟩)
    rw [acceptCount_zero]
    simp [PCPVerifier.accepts, hrej]

/-- **`NP = PCP(0, poly)`**: a problem is in `NP` exactly when it has a polynomial-time PCP
verifier using no random bits and polynomially many queries. -/
theorem mem_NP_iff_exists_PCP_zero {A : Set α} :
    A ∈ NP enc ↔ ∃ k : ℕ, A ∈ PCP (fun _ => 0) (fun n => (n + 1) ^ k) enc :=
  ⟨exists_mem_PCP_zero_of_mem_NP, fun ⟨_, hk⟩ =>
    (PCP_mono_randomness (fun _ => Nat.zero_le _)).trans (PCP_log_subset_NP _) hk⟩

end Cslib.Complexity
