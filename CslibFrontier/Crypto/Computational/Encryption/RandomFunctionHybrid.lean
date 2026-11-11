/-
Copyright (c) 2026 Karn Seth, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.PRF.Finite
public import CslibFrontier.Foundations.Data.BitString.Basic
public import CslibFrontier.Languages.Probabilistic.Oracle.Interaction
public import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Crypto.Game.UntilBad
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.RandomOracle.Probabilistic
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Tactic.Linarith

/-!
# Lazy-vs-Fresh Random Function Hybrid and Game-Hop Utilities

Shared random-function hybrid machinery for block-cipher modes of operation (such as OFB and CTR):
replaces a lazily sampled random function (`PRF.idealGame`) by fresh independent uniform sampling
(`freshStep`) up to the repetition bad event that an oracle query hits a previously sampled input.

## Main definitions

* `Cslib.Crypto.FlagState`, `Cslib.Crypto.FlagState.repeated`: association list of queried
  `BitString n` pairs paired with a Boolean repetition flag and its named accessor.
* `Cslib.Crypto.lazyStep`: lazy random-function handler that returns cached outputs on repeats and
  latches the repetition flag.
* `Cslib.Crypto.freshStep`: fresh uniform random-function handler that always samples uniformly and
  latches the repetition flag on repeats.

## Main results

* `Cslib.Crypto.idealGame_eq_runWith_lazyStep`: `PRF.idealGame` equals running `lazyStep` from
  `([], false)`.
* `Cslib.Crypto.advantage_lazy_fresh_le`: the advantage between `lazyStep` and `freshStep` is at
  most the bad-flag probability under `freshStep`.
* `Cslib.Crypto.advantage_idealGame_freshStep_le`: the advantage between `PRF.idealGame` and
  `freshStep` is at most the bad-flag probability under `freshStep`.
* `Cslib.Crypto.snd_eq_of_mem_support_lift`, `Cslib.Crypto.toOuterMeasure_lift_eq_zero`: lifted
  private-coin support and zero-bad-event lemmas.
* `Cslib.Crypto.advantage_le_two`, `Cslib.Crypto.advantage_le_four`: two-step and four-step
  triangle-inequality bounds for `Game.advantage`.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020],
  Section 3.6.3 (Theorem 3.33).
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Chapter 4.
-/

public section

namespace Cslib.Crypto

open Cslib.Probability
open OracleComp (sumHandler)
open scoped ENNReal NNReal

variable {n : ℕ}

/-- A lazily sampled random-function table and a flag recording a repeated input. -/
abbrev FlagState (n : ℕ) : Type := List (BitString n × BitString n) × Bool

/-- Whether a `FlagState` has recorded a repeated oracle input. -/
abbrev FlagState.repeated (s : FlagState n) : Bool := s.2

/-- Lazy sampling of a uniform function: a cached input returns its cached value and raises the
flag, and a new input draws a uniform value. -/
@[expose]
noncomputable def lazyStep (x : BitString n) : StateT (FlagState n) PMF (BitString n) :=
  fun s => match s.1.lookup x with
    | some y => PMF.pure (y, (s.1, true))
    | none => (PMF.uniformOfFintype (BitString n)).map fun u => (u, ((x, u) :: s.1, s.2))

/-- Fresh sampling of a uniform function: every input draws a new uniform value, and a repeated
input raises the flag. -/
@[expose]
noncomputable def freshStep (x : BitString n) : StateT (FlagState n) PMF (BitString n) :=
  fun s => (PMF.uniformOfFintype (BitString n)).map fun u =>
    (u, ((x, u) :: s.1, s.2 || (s.1.lookup x).isSome))

/-- Lifting a state-free `PMF` into `StateT` preserves the state on the entire support. -/
theorem snd_eq_of_mem_support_lift {α σ : Type} {p : PMF α} {s : σ} {z : α × σ}
    (hz : z ∈ ((StateT.lift p : StateT σ PMF α) s).support) : z.2 = s := by
  simp only [StateT.lift, Probability.PMF.monad_bind_eq_bind,
    Probability.PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hz
  obtain ⟨_, -, rfl⟩ := hz
  rfl

/-- Lifting a state-free `PMF` from a non-bad state hits a bad state with zero outer measure. -/
theorem toOuterMeasure_lift_eq_zero {α σ : Type} {bad : σ → Prop} (p : PMF α) (s : σ)
    (hs : ¬bad s) : ((StateT.lift p : StateT σ PMF α) s).toOuterMeasure {x | bad x.2} = 0 := by
  rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
  intro x hx hbad
  exact hs ((snd_eq_of_mem_support_lift hx) ▸ hbad)

private theorem prop_of_mem_support_map {α β : Type} {p : PMF α} {f : α → β} {z : β}
    (hz : z ∈ (p.map f).support) {P : β → Prop} (h : ∀ a, P (f a)) : P z := by
  obtain ⟨a, -, rfl⟩ := (PMF.mem_support_map_iff f p z).1 hz
  exact h a

private theorem flag_of_mem_support_pure {y : BitString n}
    {c : List (BitString n × BitString n)} {z : BitString n × FlagState n}
    (hz : z ∈ (PMF.pure (y, (c, true))).support) : z.2.2 = true := by
  rw [PMF.mem_support_pure_iff] at hz
  subst hz
  rfl

private theorem lazyStep_map_fst (x : BitString n) (s : FlagState n) :
    (lazyStep x s).map (fun (a, s') => (a, s'.1)) =
      memoize (fun _ => PMF.uniformOfFintype (BitString n)) x s.1 := by
  unfold lazyStep
  cases h : s.1.lookup x with
  | some y =>
    rw [memoize_of_some _ _ _ _ h]
    simp only [PMF.pure_map, Probability.PMF.monad_pure_eq_pure]
  | none =>
    rw [memoize_of_none _ _ _ h]
    simp only [PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind,
      Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure]

private theorem runWith_memoize_eq {α : Type}
    (program : ProbOracleComp (fun _ : BitString n => BitString n) α) :
    (ProbOracleComp.runWith (memoize fun _ => PMF.uniformOfFintype (BitString n)) program
      []).map Prod.fst =
      (ProbOracleComp.runWith lazyStep program ([], false)).map Prod.fst := by
  rw [← ProbOracleComp.runWith_map_state lazyStep
    (memoize fun _ => PMF.uniformOfFintype (BitString n)) Prod.fst lazyStep_map_fst program
    ([], false), PMF.map_comp]
  exact congrArg (fun f => PMF.map f _) (funext fun ⟨_, _⟩ => rfl)

private theorem identicalUntilBad_lazyStep_freshStep :
    OracleComp.IdenticalUntilBad
      (sumHandler (fun i => StateT.lift (ProbComp.unifOracle i)) (lazyStep (n := n)))
      (sumHandler (fun i => StateT.lift (ProbComp.unifOracle i)) (freshStep (n := n)))
      (fun s : FlagState n => s.2 = true) where
  agree q s _ a s' hs' := by
    cases q with
    | inl i => rfl
    | inr x =>
      change lazyStep x s (a, s') = freshStep x s (a, s')
      simp only [lazyStep, freshStep]
      cases h : s.1.lookup x with
      | none => simp only [Option.isSome_none, Bool.or_false]
      | some y =>
        simp only [Option.isSome_some, Bool.or_true]
        have h1 : (PMF.pure (y, (s.1, true)) : PMF (BitString n × FlagState n)) (a, s') = 0 :=
          (PMF.apply_eq_zero_iff _ _).2 fun hz => hs' (flag_of_mem_support_pure hz)
        have h2 : ((PMF.uniformOfFintype (BitString n)).map fun u =>
            (u, ((x, u) :: s.1, true))) (a, s') = 0 :=
          (PMF.apply_eq_zero_iff _ _).2 fun hz =>
            hs' (prop_of_mem_support_map hz (P := fun z => z.2.2 = true) fun _ => rfl)
        rw [h1, h2]
  absorb_first q s hs x hx := by
    have hs' : s.2 = true := hs
    cases q with
    | inl i =>
      rw [snd_eq_of_mem_support_lift hx]
      exact hs
    | inr y =>
      change x ∈ (lazyStep y s).support at hx
      simp only [lazyStep] at hx
      split at hx
      · exact flag_of_mem_support_pure hx
      · exact prop_of_mem_support_map hx (P := fun z => z.2.2 = true) fun _ => hs'
  absorb_second q s hs x hx := by
    have hs' : s.2 = true := hs
    cases q with
    | inl i =>
      rw [snd_eq_of_mem_support_lift hx]
      exact hs
    | inr y =>
      change x ∈ (freshStep y s).support at hx
      exact prop_of_mem_support_map hx (P := fun z => z.2.2 = true) fun _ => by simp [hs']

/-- `PRF.idealGame` against a uniform random function on `BitString n` equals the output of
`ProbOracleComp.runWith lazyStep program ([], false)`. -/
theorem idealGame_eq_runWith_lazyStep (program : PRF.Adversary (BitString n) (BitString n)) :
    PRF.idealGame program = (ProbOracleComp.runWith lazyStep program ([], false)).map Prod.fst := by
  rw [← runWith_memoize_eq]
  have h := RandomOracle.interpret_prob_eq_memoize
    (fun _ : BitString n => PMF.uniformOfFintype (BitString n)) program
  rw [← h]
  simp only [PRF.idealGame, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbOracleComp.eval_interpret, ProbComp.eval_pure, PMF.pi_uniformOfFintype,
    Probability.PMF.monad_bind_eq_bind]

/-- The advantage between `lazyStep` and `freshStep` is bounded by the probability of raising the
repetition flag under `freshStep`. -/
theorem advantage_lazy_fresh_le (program : PRF.Adversary (BitString n) (BitString n)) :
    (Game.advantage ((ProbOracleComp.runWith lazyStep program ([], false)).map Prod.fst)
        ((ProbOracleComp.runWith freshStep program ([], false)).map Prod.fst) : ℝ) ≤
      ((ProbOracleComp.runWith freshStep program ([], false)).toOuterMeasure
        {x | x.2.repeated = true}).toReal := by
  have h := identicalUntilBad_lazyStep_freshStep.advantage_le program ([], false)
    fun x => PMF.pure x.1
  rw [identicalUntilBad_lazyStep_freshStep.bad_eq] at h
  exact h

/-- The advantage between `PRF.idealGame` and fresh independent sampling `freshStep` is bounded by
the probability of raising the repetition flag under `freshStep`. -/
theorem advantage_idealGame_freshStep_le (program : PRF.Adversary (BitString n) (BitString n)) :
    (Game.advantage (PRF.idealGame program)
        ((ProbOracleComp.runWith freshStep program ([], false)).map Prod.fst) : ℝ) ≤
      ((ProbOracleComp.runWith freshStep program ([], false)).toOuterMeasure
        {x | x.2.repeated = true}).toReal := by
  rw [idealGame_eq_runWith_lazyStep]
  exact advantage_lazy_fresh_le program

/-- Two-hop triangle inequality for real-valued `Game.advantage`. -/
theorem advantage_le_two (g₀ g₁ g₂ : Game) :
    (Game.advantage g₀ g₂ : ℝ) ≤ Game.advantage g₀ g₁ + Game.advantage g₂ g₁ := by
  rw [Game.advantage_comm g₂ g₁]
  exact_mod_cast Game.advantage_triangle g₀ g₁ g₂

/-- Four-hop symmetric triangle inequality for real-valued `Game.advantage`. -/
theorem advantage_le_four (g₀ g₁ g₂ g₃ g₄ : Game) :
    (Game.advantage g₀ g₄ : ℝ) ≤
      Game.advantage g₀ g₁ + Game.advantage g₁ g₂ + Game.advantage g₃ g₂ +
        Game.advantage g₄ g₃ := by
  have h₁ : (Game.advantage g₀ g₄ : ℝ) ≤ Game.advantage g₀ g₁ + Game.advantage g₁ g₄ := by
    exact_mod_cast Game.advantage_triangle g₀ g₁ g₄
  have h₂ : (Game.advantage g₁ g₄ : ℝ) ≤ Game.advantage g₁ g₂ + Game.advantage g₂ g₄ := by
    exact_mod_cast Game.advantage_triangle g₁ g₂ g₄
  have h₃ : (Game.advantage g₂ g₄ : ℝ) ≤ Game.advantage g₃ g₂ + Game.advantage g₄ g₃ :=
    (advantage_le_two g₂ g₃ g₄).trans_eq (by rw [Game.advantage_comm g₂ g₃, add_comm])
  linarith

end Cslib.Crypto
