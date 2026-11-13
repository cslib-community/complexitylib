/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Lifting.Dangerous
public import CslibFrontier.Foundations.Data.Finset.BigHalf
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A density-preserving simulation step

This implements the five operations of CFKMP §4.1 for a single transmitted bit: remove unsafe
inputs, retain a larger message fiber, restore the speaker's density, query the restored
coordinates, and condition the other source on the answers. Iteration must group same-speaker
bits into alternating rounds, or insert dummy alternating
steps, to avoid repeatedly spending the listener's density slack.
Safety is an explicit hypothesis;
this module does not assume an unproved bound on dangerous values.

The step works for any Boolean gadget and every answer to its queries. It retains nonempty
sources, the speaker's message, the prescribed gadget outputs, and the two residual densities.
Its product-size bound is the multiplicative form of the loss used in amortizing query cost.
-/

public section

namespace Cslib.Communication.Lifting

open Finset

variable {n m : ℕ}

/-- The data produced by a single simulation step. `speaker` is the source sending the bit;
`listener` is the other source, so the same data apply when the players swap roles. -/
structure DensityStep (n m : ℕ) where
  /-- The transmitted bit selected by the simulator. -/
  message : Bool
  /-- The coordinates queried in this step. -/
  queried : Finset (Fin n)
  /-- The retained speaker inputs. -/
  speaker : Finset (Fin n → Fin m)
  /-- Listener inputs retained for each possible assignment of query answers. -/
  listener : (Fin n → Bool) → Finset (Fin n → Fin m)
  /-- The common values of the speaker on queried coordinates. -/
  assignment : Fin n → Fin m

/-- Correctness and cardinality invariants of one step, uniformly over every query answer. -/
structure DensityStep.Valid (st : DensityStep n m) (g : Fin m → Fin m → Bool)
    (τ σ : ℝ) (F : Finset (Fin n)) (X Y : Finset (Fin n → Fin m))
    (send : (Fin n → Fin m) → Bool) : Prop where
  /-- Only free coordinates are queried. -/
  queried_subset : st.queried ⊆ F
  /-- Speaker inputs are only removed. -/
  speaker_subset : st.speaker ⊆ X
  /-- Listener inputs are only removed. -/
  listener_subset : ∀ answer, st.listener answer ⊆ Y
  /-- The retained speaker set is nonempty. -/
  speaker_nonempty : st.speaker.Nonempty
  /-- Every query answer has a nonempty listener fiber. -/
  listener_nonempty : ∀ answer, (st.listener answer).Nonempty
  /-- All retained speaker inputs send the selected message. -/
  message_eq : ∀ x ∈ st.speaker, send x = st.message
  /-- Queried coordinates are fixed on the speaker side. -/
  fixed : ∀ x ∈ st.speaker, ∀ i ∈ st.queried, x i = st.assignment i
  /-- Both sources give the queried gadget outputs. -/
  output_eq : ∀ answer, ∀ x ∈ st.speaker, ∀ y ∈ st.listener answer, ∀ i ∈ st.queried,
    g (x i) (y i) = answer i
  /-- The speaker's density is restored. -/
  speaker_dense : IsDense τ (F \ st.queried) st.speaker
  /-- The listener retains the target residual density. -/
  listener_dense : ∀ answer, IsDense σ (F \ st.queried) (st.listener answer)
  /-- Safe filtering and message selection lose at most two bits. -/
  speaker_card : (#X : ℝ) ≤ 4 * #st.speaker * τ ^ #st.queried
  /-- A query answer loses at most its length plus one bit on the listener side. -/
  listener_card : ∀ answer, (#Y : ℝ) ≤ 2 ^ (#st.queried + 1) * #(st.listener answer)
  /-- Product-size accounting for subsequent amortization. -/
  volume : ∀ answer, (#X : ℝ) * #Y ≤
    8 * (2 * τ) ^ #st.queried * #st.speaker * #(st.listener answer)
  /-- The resulting listener set depends only on answers to queried coordinates. -/
  locality : ∀ a b, (∀ i ∈ st.queried, a i = b i) → st.listener a = st.listener b

open scoped Classical in
/-- Every query answer admits a density-preserving simulation step if at least half of the
speaker's inputs are safe. This is a conditional simulation lemma, not the rare-danger theorem.
The source's target densities are represented by `τ = 2^(δb)` and `σ = 2^((δ-ε)b)`. -/
theorem exists_densityStep (g : Fin m → Fin m → Bool) (τ σ : ℝ)
    (F : Finset (Fin n)) (X Y : Finset (Fin n → Fin m))
    (send : (Fin n → Fin m) → Bool)
    (hτ : 0 < τ) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hsafe : (#X : ℝ) ≤ 2 * #(X.filter (IsSafe g σ F Y))) :
    ∃ st : DensityStep n m, st.Valid g τ σ F X Y send := by
  classical
  let safe := X.filter (IsSafe g σ F Y)
  let b := bigHalf safe send
  let W := safe.filter fun x => send x = b
  have hhalf : (#safe : ℝ) ≤ 2 * #W := card_le_two_mul_card_filter_bigHalf safe send
  have hXpos : (0 : ℝ) < #X := by exact_mod_cast card_pos.mpr hX
  have hW : W.Nonempty := by
    apply card_pos.mp
    have : (0 : ℝ) < #W := by dsimp [safe] at hhalf; linarith
    exact_mod_cast this
  obtain ⟨I, α, hIF, hP, hPW, hfixed, hdense, hcard⟩ := exists_dense_agreeOn hτ F hW
  let P := agreeOn W I α
  obtain ⟨x, hx⟩ := hP
  have hxW := hPW hx
  have hxSafe : IsSafe g σ F Y x := (mem_filter.mp (mem_filter.mp hxW).1).2
  let Q := fun answer => gadgetFiber g Y I x answer
  have hQ (answer) : (Q answer).Nonempty := hxSafe.fiber_nonempty hY hIF answer
  have hXcard : (#X : ℝ) ≤ 4 * #P * τ ^ #I := by
    change (#W : ℝ) ≤ #P * τ ^ #I at hcard
    change (#X : ℝ) ≤ 2 * #safe at hsafe
    linarith
  have hYcard (answer) : (#Y : ℝ) ≤ 2 ^ (#I + 1) * #(Q answer) :=
    hxSafe.nonleaking I hIF answer
  refine ⟨⟨b, I, P, Q, α⟩, hIF, ?_, (fun answer => gadgetFiber_subset _ _ _ _ answer), ?_, hQ,
    ?_, hfixed, ?_, hdense, (fun answer => hxSafe.dense I hIF answer), hXcard, hYcard, ?_, ?_⟩
  · exact hPW.trans ((filter_subset _ _).trans (filter_subset _ _))
  · exact ⟨x, hx⟩
  · intro x' hx'
    exact (mem_filter.mp (hPW hx')).2
  · intro answer x' hx' y hy i hi
    have heq : x' i = x i := (hfixed x' hx' i hi).trans (hfixed x hx i hi).symm
    rw [heq]
    exact (mem_gadgetFiber.mp hy).2 i hi
  · intro answer
    have hprod := mul_le_mul hXcard (hYcard answer) (by positivity : (0 : ℝ) ≤ #Y)
      (by positivity : (0 : ℝ) ≤ 4 * #P * τ ^ #I)
    calc
      _ ≤ (4 * #P * τ ^ #I) * (2 ^ (#I + 1) * #(Q answer)) := hprod
      _ = _ := by rw [pow_succ, mul_pow]; ring
  · intro a b hab
    ext y
    simp only [Q, mem_gadgetFiber]
    constructor
    · rintro ⟨hy, hg⟩
      exact ⟨hy, fun i hi => (hg i hi).trans (hab i hi)⟩
    · rintro ⟨hy, hg⟩
      exact ⟨hy, fun i hi => (hg i hi).trans (hab i hi).symm⟩

end Cslib.Communication.Lifting
