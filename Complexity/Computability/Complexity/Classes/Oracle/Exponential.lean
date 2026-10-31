/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.EXP
public import Complexity.Computability.Complexity.Classes.Oracle
import Complexity.Computability.Complexity.Classes.Oracle.Closure
import Complexity.Computability.Complexity.Reduction
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Internal.NormalForm
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.RunsWords
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Tidy
import Complexity.Computability.Probabilistic.Oracle.Normalization

/-!
# Exponential time relative to an oracle language

`E` relative to an oracle language `A` is decided by a deterministic oracle machine within time
`2 ^ O(n)`; its requests may therefore be exponentially long
[Williams, p. 2, footnote 5][Williams2010]. The certificate `Cslib.Probability.IsOracleExpTimeOn`
is `Cslib.Probability.IsOraclePPTOn` with the polynomial clock `c * (n + 1) ^ d` replaced by the
clock `c * 2 ^ (d * n)`: one finite-control machine reproduces the program's complete interaction
with every stateful oracle, charging the construction of each request and the reading of each
reply. As in `IsOraclePPTOn`, the run is cut off at the clock, which is a fixed function of the
input length.

`Cslib.Complexity.ComputableInExpTimeWithOracle` and `Cslib.Complexity.EWithOracle` relativize `E`
exactly as `Cslib.Complexity.ComputableInPolyTimeWithOracle` and `Cslib.Complexity.PWithOracle`
relativize `P`, and `Cslib.Complexity.ENP` is the union of `EWithOracle A` over the oracle
languages `A` in `NP`.

Both `E` and `P` relative to `A` lie inside `E` relative to `A`
(`Cslib.Complexity.E_subset_EWithOracle`, `Cslib.Complexity.PWithOracle_subset_EWithOracle`). The
*preprocessing rule* `Cslib.Complexity.preimage_mem_EWithOracle` composes a deterministic
preparation within time `O(2 ^ (d * n))` with a problem in `P` relative to `A` on the prepared
instances. Its typical use is padding: a polynomial-time algorithm with an oracle, run on an
exponentially padded instance, is an exponential-time algorithm with that oracle. The preparation
phase is a tidy normal form of the deterministic machine, and the oracle phase a clean realization
of the polynomial-time certificate (`Cslib.Probability.IsOraclePPTOn.isTidyOraclePPTOn`); the two
are sequenced by `Turing.MultiTapePTM.ComputesTidily.comp`, which charges the intermediate word.

## Main definitions

* `Cslib.Probability.IsOracleExpTimeOn`: realization by one machine within a clock `2 ^ O(n)`.
* `Cslib.Complexity.ComputableInExpTimeWithOracle`: exponential time relative to an oracle.
* `Cslib.Complexity.EWithOracle`: `E` relative to an oracle language.
* `Cslib.Complexity.ENP`: `E ^ NP`.

## Main results

* `Cslib.Probability.IsOraclePPTOn.isOracleExpTimeOn`: a polynomial clock is an exponential one.
* `Cslib.Probability.IsOraclePPTOn.preprocess_exp`: exponential-time deterministic preparation,
  then a strict oracle PPT program.
* `Cslib.Complexity.ComputableInPolyTimeWithOracle.computableInExpTimeWithOracle`,
  `Cslib.Complexity.ComputableInPolyTimeWithOracle.comp_computableInO`.
* `Cslib.Complexity.E_subset_EWithOracle`, `Cslib.Complexity.PWithOracle_subset_EWithOracle`,
  `Cslib.Complexity.preimage_mem_EWithOracle`.
* `Cslib.Complexity.E_subset_ENP`, `Cslib.Complexity.PWithOracle_subset_ENP`,
  `Cslib.Complexity.NP_subset_ENP`.

## References

* [R. Williams, *Improving exhaustive search implies superpolynomial lower bounds*][Williams2010]
-/

@[expose] public section

namespace Cslib

namespace Probability

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapePTM

/-- One finite machine and an exponential clock `c * 2 ^ (d * n)` in the input length `n` preserve
the full interaction with every shared stateful oracle: `Cslib.Probability.IsOraclePPTOn` with the
polynomial clock replaced by `2 ^ O(n)`. The oracle's computation is external; request
construction and reply access are ordinary machine work. -/
def IsOracleExpTimeOn {Operation α β : Type} [DecidableEq Operation]
    (input : α ↪ List Bool) (output : β ↪ List Bool)
    (program : α → WordOracleComp Operation β) : Prop :=
  Finite Operation ∧ ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
    (machine : Turing.MultiTapePTM k Bool Control Operation) (c d : ℕ),
    ∀ a (State : Type) (oracle : Operation × List Bool → StateT State PMF (List Bool)) s,
      (OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (output <$> program a)).run s =
      (OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (machine.runOracle (c * 2 ^ (d * (input a).length)) (input a))).run s

namespace IsOracleExpTimeOn

variable {Operation α β : Type} [DecidableEq Operation]
  {input : α ↪ List Bool} {output : β ↪ List Bool}

/-- A machine computing the encoded program as a clean phase within time `c * 2 ^ (d * n)` is a
certificate. -/
private theorem of_computesTidily [Finite Operation] {k : ℕ} {Control : Type} [Finite Control]
    {program : α → WordOracleComp Operation β}
    (machine : Turing.MultiTapePTM k Bool Control Operation) (c d : ℕ) {time : α → ℕ}
    (htime : ∀ a, time a ≤ c * 2 ^ (d * (input a).length))
    (h : ∀ a, machine.ComputesTidily (input a) (time a) (output <$> program a)) :
    IsOracleExpTimeOn input output program :=
  ⟨inferInstance, k, Control, inferInstance, machine, c, d, fun a _ oracle s =>
    (((h a).mono (htime a)).runOracle oracle s).symm⟩

end IsOracleExpTimeOn

variable {Operation α β γ : Type} [DecidableEq Operation]
  {input : α ↪ List Bool} {middle : β ↪ List Bool} {output : γ ↪ List Bool}

/-- `n + 1 ≤ 2 ^ n`, raised to the power `d`. -/
private theorem succ_pow_le_two_pow_mul (n d : ℕ) : (n + 1) ^ d ≤ 2 ^ (d * n) := by
  rw [Nat.pow_mul']
  exact Nat.pow_le_pow_left Nat.lt_two_pow_self d

/-- **A polynomial clock is an exponential clock.** The clean realization of a strict oracle PPT
certificate keeps its result once it halts, so its polynomial clock can be raised to
`c * 2 ^ (d * n)`. -/
theorem IsOraclePPTOn.isOracleExpTimeOn {program : α → WordOracleComp Operation γ}
    (h : IsOraclePPTOn input output program) : IsOracleExpTimeOn input output program := by
  obtain ⟨hops, k, Control, hfinite, machine, c, d, hmachine⟩ := h.isTidyOraclePPTOn
  exact IsOracleExpTimeOn.of_computesTidily machine c d
    (fun a => Nat.mul_le_mul_left c (succ_pow_le_two_pow_mul _ d)) hmachine

/-- Arithmetic for `preprocess_exp`: the two phases and the charged intermediate word fit in one
exponential clock. -/
private theorem preprocess_exp_bound (C c₂ d₂ X : ℕ) (hX : 1 ≤ X) :
    5 * (C * (X + 1)) + c₂ * (C * (X + 1) + 1) ^ d₂ + 9 ≤
      (5 * (2 * C) + c₂ * (2 * C + 1) ^ d₂ + 9) * X ^ (d₂ + 1) := by
  have hX1 : X ≤ X ^ (d₂ + 1) := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ X ^ (d₂ + 1) := Nat.pow_le_pow_right hX (by omega)
  have hXd : X ^ d₂ ≤ X ^ (d₂ + 1) := Nat.pow_le_pow_right hX (by omega)
  have h1 : 1 ≤ X ^ (d₂ + 1) := Nat.one_le_pow _ _ hX
  have hpow : (C * (X + 1) + 1) ^ d₂ ≤ (2 * C + 1) ^ d₂ * X ^ (d₂ + 1) := by
    calc (C * (X + 1) + 1) ^ d₂ ≤ ((2 * C + 1) * X) ^ d₂ :=
          Nat.pow_le_pow_left (by nlinarith) d₂
      _ = (2 * C + 1) ^ d₂ * X ^ d₂ := Nat.mul_pow _ _ _
      _ ≤ (2 * C + 1) ^ d₂ * X ^ (d₂ + 1) := Nat.mul_le_mul_left _ hXd
  have hlin : 5 * (C * (X + 1)) ≤ 5 * (2 * C) * X ^ (d₂ + 1) := by
    have := Nat.mul_le_mul_left (2 * C) hX1
    nlinarith
  have hc : c₂ * (C * (X + 1) + 1) ^ d₂ ≤ c₂ * (2 * C + 1) ^ d₂ * X ^ (d₂ + 1) := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ hpow
  nlinarith

/-- **Exponential-time preparation, then a strict oracle PPT program.** If `prepare` is
computable within time `O(2 ^ (d * n))` and `program` is strict oracle PPT on the prepared
instances, the composite is realized within time `2 ^ O(n)`. The prepared word may be
exponentially long; the polynomial clock of `program` is then exponential in `n`. -/
theorem IsOraclePPTOn.preprocess_exp {program : β → WordOracleComp Operation γ}
    {prepare : α → β} {S : α → ℕ} {d : ℕ}
    (hprogram : IsOraclePPTOn middle output program)
    (hprepare : ComputableInO prepare input middle (fun a => 2 ^ (d * (input a).length)) S) :
    IsOracleExpTimeOn input output (fun a => program (prepare a)) := by
  classical
  obtain ⟨hops, k₂, Control₂, hfinite₂, target, c₂, d₂, htarget⟩ := hprogram.isTidyOraclePPTOn
  obtain ⟨C, ⟨k₁, State₁, hfinite₁, tm, htm⟩, -⟩ := Internal.NormalForm.inO hprepare
  let source : MultiTapePTM k₁ Bool State₁ Operation := ofDeterministic tm
  let firstTime : α → ℕ := fun a => C * (2 ^ (d * (input a).length) + 1)
  have hsource (a : α) : source.ComputesTidily (input a) (firstTime a)
      (pure (middle (prepare a))) :=
    ComputesTidily.of_deterministic (htm a)
  let continuation : List Bool → WordOracleComp Operation (List Bool) :=
    Function.extend middle (fun b => output <$> program b) (fun _ => pure [])
  have hcontinuation (b : β) : continuation (middle b) = output <$> program b :=
    middle.injective.extend_apply _ _ b
  refine IsOracleExpTimeOn.of_computesTidily (target.tidyComp source true)
    (5 * (2 * C) + c₂ * (2 * C + 1) ^ d₂ + 9) (d * (d₂ + 1))
    (time := fun a => 5 * firstTime a + c₂ * (firstTime a + 1) ^ d₂ + 9)
    (fun a => ?_) (fun a => ?_)
  · refine (preprocess_exp_bound C c₂ d₂ _
      (Nat.one_le_two_pow (n := d * (input a).length))).trans (le_of_eq ?_)
    rw [← Nat.pow_mul]
    congr 2
    ring
  · have hcomp := (hsource a).comp true (prog₂ := continuation)
      (t₂ := c₂ * (firstTime a + 1) ^ d₂)
      (fun word State oracle s s' hword => by
        have hlen := (hsource a).length_output_le oracle s hword
        simp only [OracleComp.interpret_pure, StateT.run_pure, PMF.monad_pure_eq_pure,
          PMF.mem_support_pure_iff, Prod.mk.injEq] at hword
        obtain ⟨rfl, -⟩ := hword
        rw [hcontinuation]
        exact (htarget (prepare a)).mono (Nat.mul_le_mul_left c₂
          (Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) d₂)))
    simpa only [pure_bind, hcontinuation] using hcomp

end Probability

namespace Complexity

open Probability Turing.MultiTapeTM

variable {α β γ : Type}

/-- `f` is computable in exponential time relative to the oracle language `A`: a deterministic
word-query program computes `f` against `A`, and one finite machine under one clock
`c * 2 ^ (d * n)` realizes the program against every stateful oracle, charging request
construction and reply access. This is `Cslib.Complexity.ComputableInPolyTimeWithOracle` with the
clock `2 ^ O(n)`. -/
def ComputableInExpTimeWithOracle (A : Set (List Bool)) (f : α → β) (input : α ↪ List Bool)
    (output : β ↪ List Bool) : Prop :=
  ∃ program : α → WordQueryComp Unit β,
    IsOracleExpTimeOn input output
        (fun a => OracleComp.interpret ProbOracleComp.query (program a)) ∧
      ∀ a, OracleComp.interpret (m := Id) (languageOracle A) (program a) = f a

/-- **Polynomial time relative to `A` is exponential time relative to `A`.** -/
theorem ComputableInPolyTimeWithOracle.computableInExpTimeWithOracle {A : Set (List Bool)}
    {f : α → β} {input : α ↪ List Bool} {output : β ↪ List Bool}
    (h : ComputableInPolyTimeWithOracle A f input output) :
    ComputableInExpTimeWithOracle A f input output :=
  let ⟨program, hcert, hf⟩ := h
  ⟨program, hcert.isOracleExpTimeOn, hf⟩

/-- **Exponential-time preparation, then polynomial time relative to `A`.** -/
theorem ComputableInPolyTimeWithOracle.comp_computableInO {A : Set (List Bool)} {g : β → γ}
    {prepare : α → β} {input : α ↪ List Bool} {middle : β ↪ List Bool} {output : γ ↪ List Bool}
    {S : α → ℕ} {d : ℕ} (hg : ComputableInPolyTimeWithOracle A g middle output)
    (hprepare : ComputableInO prepare input middle (fun a => 2 ^ (d * (input a).length)) S) :
    ComputableInExpTimeWithOracle A (g ∘ prepare) input output :=
  let ⟨program, hcert, hg⟩ := hg
  ⟨fun a => program (prepare a), hcert.preprocess_exp hprepare, fun a => hg (prepare a)⟩

/-- The problems decidable in time `2 ^ O(n)` relative to the oracle language `A`, with respect to
the encoding `enc` of instances: `Cslib.Complexity.E` with an oracle, defined like
`Cslib.Complexity.PWithOracle`. -/
def EWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) : Set (Set α) :=
  {L | ∃ f : α → Bool, ComputableInExpTimeWithOracle A f enc encBool ∧ ∀ a, a ∈ L ↔ f a = true}

theorem mem_EWithOracle {A : Set (List Bool)} {enc : α ↪ List Bool} {L : Set α} :
    L ∈ EWithOracle A enc ↔ ∃ f : α → Bool,
      ComputableInExpTimeWithOracle A f enc encBool ∧ ∀ a, a ∈ L ↔ f a = true :=
  Iff.rfl

/-- **`E ^ NP`**: the problems decidable in time `2 ^ O(n)` relative to some oracle language in
`NP` [Williams, p. 2, footnote 5][Williams2010]. The requests may have length `2 ^ O(n)`. -/
def ENP (enc : α ↪ List Bool) : Set (Set α) :=
  ⋃ A ∈ NP encBits, EWithOracle A enc

theorem mem_ENP {enc : α ↪ List Bool} {L : Set α} :
    L ∈ ENP enc ↔ ∃ A ∈ NP encBits, L ∈ EWithOracle A enc := by
  simp only [ENP, Set.mem_iUnion, exists_prop]

/-- `P` relative to `A` lies inside `E` relative to `A`. -/
theorem PWithOracle_subset_EWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) :
    PWithOracle A enc ⊆ EWithOracle A enc := fun _ ⟨f, hf, h⟩ =>
  ⟨f, hf.computableInExpTimeWithOracle, h⟩

/-- **The preprocessing rule.** If `prepare` is computable within time `O(2 ^ (d * n))` and `M` is
in `P` relative to `A`, then the problem of whether the prepared instance is in `M` is in `E`
relative to `A`. -/
theorem preimage_mem_EWithOracle {A : Set (List Bool)} {enc : α ↪ List Bool}
    {middle : β ↪ List Bool} {M : Set β} {prepare : α → β} {S : α → ℕ} {d : ℕ}
    (hM : M ∈ PWithOracle A middle)
    (hprepare : ComputableInO prepare enc middle (fun a => 2 ^ (d * (enc a).length)) S) :
    prepare ⁻¹' M ∈ EWithOracle A enc :=
  let ⟨g, hg, hM⟩ := hM
  ⟨g ∘ prepare, hg.comp_computableInO hprepare, fun a => hM (prepare a)⟩

/-- **`E` lies inside `E` relative to every oracle**: a deterministic machine makes no request. -/
theorem E_subset_EWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) :
    E enc ⊆ EWithOracle A enc := by
  intro L hL
  obtain ⟨k, c₁, c₂, s, hL⟩ := mem_E_iff.mp hL
  obtain ⟨f, hf, hfL⟩ := decidableInTimeAndSpace_iff.mp hL
  have hO : ComputableInO f enc encBool (fun a => 2 ^ (k * (enc a).length))
      (fun a => 2 ^ (k * (enc a).length) + s (enc a).length) := by
    refine ⟨c₁ + c₂ + 1, hf.mono (fun a => ?_) (fun a => ?_), fun a => ?_⟩
    · change c₁ * 2 ^ (k * (enc a).length) + c₂ ≤
        (c₁ + c₂ + 1) * (2 ^ (k * (enc a).length) + 1)
      rw [Nat.mul_add, Nat.mul_one]
      exact Nat.add_le_add (Nat.mul_le_mul_right _ (by omega)) (by omega)
    · change s (enc a).length ≤
        (c₁ + c₂ + 1) * (2 ^ (k * (enc a).length) + s (enc a).length + 1)
      exact ((Nat.le_add_left _ _).trans (Nat.le_succ _)).trans
        (Nat.le_mul_of_pos_left _ (by omega))
    · simp only [encBool_apply, List.length_singleton]
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (Nat.succ_ne_zero _))
  have h := preimage_mem_EWithOracle (A := A) (M := {b : Bool | b = true})
    (prepare := f) (P_subset_PWithOracle A encBool ⟨id, ComputableInPolyTime.id', fun _ =>
      Iff.rfl⟩) hO
  have hL' : L = f ⁻¹' {b : Bool | b = true} := Set.ext fun a => hfL a
  rwa [hL']

/-- `E` lies inside `E ^ NP`. -/
theorem E_subset_ENP (enc : α ↪ List Bool) : E enc ⊆ ENP enc := fun _ hL =>
  mem_ENP.mpr ⟨∅, P_subset_NP empty_mem_P, E_subset_EWithOracle ∅ enc hL⟩

/-- `P` relative to a language in `NP` lies inside `E ^ NP`. -/
theorem PWithOracle_subset_ENP {A : Set (List Bool)} (hA : A ∈ NP encBits) (enc : α ↪ List Bool) :
    PWithOracle A enc ⊆ ENP enc := fun _ hL =>
  mem_ENP.mpr ⟨A, hA, PWithOracle_subset_EWithOracle A enc hL⟩

/-- `NP` lies inside `E ^ NP`: one request decides an `NP` language. -/
theorem NP_subset_ENP : NP encBits ⊆ ENP encBits := fun A hA =>
  PWithOracle_subset_ENP hA encBits (mem_PWithOracle_self A)

end Complexity

end Cslib
