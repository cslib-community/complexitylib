/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.IterateWhile
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Loop.Space
import CslibFrontier.Languages.Probabilistic.Oracle.Support

/-!
# Workspace bound for iterating a probabilistic machine

Provides the exact polynomial workspace bound for `iterateWhile` via the repeat-until-blank loop.
-/

public section

namespace Turing.MultiTapePTM

open Cslib Cslib.Probability MultiTapeMachine MultiTapeTM IterateWhile

variable {k : ℕ} {State : Type} {x : List Bool}

public theorem RunsInSpace.iterateWhile {tm : MultiTapePTM k Bool State Empty} (mark : Bool)
    {r t L : ℕ} {w₀ : List Bool}
    {step : List Bool → ProbOracleComp (fun _ : Empty × List Bool => List Bool) (List Bool)}
    (invariant : ℕ → List Bool → Prop) (hbase : invariant 0 w₀)
    (hround : ∀ n < r, ∀ w, invariant n w → tm.ComputesTidily w t (step w))
    (hpreserve : ∀ n < r, ∀ w, invariant n w →
      ∀ (OracleState : Type) (oracle : Empty × List Bool → StateT OracleState PMF (List Bool))
        (s s' : OracleState) (w' : List Bool),
        (w', s') ∈ (ProbOracleComp.runWith oracle (step w)
            s).support → invariant (n + 1) w' ∧ w' ≠ [])
    (hlast : ∀ w, invariant r w → tm.ComputesTidily w t (pure []))
    (hlength : ∀ n ≤ r, ∀ w, invariant n w → w.length ≤ L) :
    (tm.iterateWhile mark).toNTM.RunsInSpace w₀
      ((k + 1 + 2) * (2 * (t + 10 * L + 22) + 1)) := by
  let step' (p : List Bool × List Bool) :
      ProbOracleComp (fun _ : Empty × List Bool => List Bool) (List Bool × List Bool) :=
    (fun v' => (p.2, v')) <$> step p.2
  let last (p : List Bool × List Bool) :
      ProbOracleComp (fun _ : Empty × List Bool => List Bool) (List Bool × List Bool) :=
    pure (p.2, [])
  let inv (n : ℕ) (p : List Bool × List Bool) : Prop := invariant n p.2 ∧ p.1.length ≤ L
  have hpres : ∀ n < r, ∀ p, inv n p →
      ∀ (OracleState : Type) (oracle : Empty × List Bool → StateT OracleState PMF (List Bool))
        (st st' : OracleState) (p' : List Bool × List Bool),
        (p', st') ∈ (ProbOracleComp.runWith oracle (step' p) st).support →
        inv (n + 1) p' ∧ words (k := k) p'.1 p'.2 (nextTape k) ≠ [] := by
    intro n hn p hp _ oracle st st' p' hp'
    simp only [step', ProbOracleComp.runWith_map, PMF.mem_support_map_iff] at hp'
    obtain ⟨⟨w', st''⟩, hw', heq⟩ := hp'
    rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
    obtain ⟨hinv, hne⟩ := hpreserve n hn p.2 hp.1 _ oracle st st'' w' hw'
    exact ⟨⟨hinv, hlength n hn.le p.2 hp.1⟩, by simpa only [words_next] using hne⟩
  have hfinal : ∀ (OracleState : Type)
      (oracle : Empty × List Bool → StateT OracleState PMF (List Bool))
      (s s' : OracleState) (p : List Bool × List Bool),
      (p, s') ∈ (ProbOracleComp.runWith oracle (OracleComp.iterate r step' ([], w₀) >>= last)
          s).support →
      p.2 = [] ∧ p.1.length ≤ L := by
    intro _ oracle s s' p hp
    rw [ProbOracleComp.runWith_bind] at hp
    obtain ⟨⟨mid, s₁⟩, hmid, hp⟩ := (PMF.mem_support_bind_iff _ _ _).mp hp
    simp only [last, ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hp
    obtain ⟨rfl, -⟩ := hp
    have hmidInv := OracleComp.iterate_invariant inv (⟨hbase, Nat.zero_le L⟩ : inv 0 ([], w₀))
      (fun n p hn hp p' hp' => by
        obtain ⟨_, oracle', st, st', hp'⟩ := ProbOracleComp.mem_support_iff_exists.mp hp'
        exact (hpres n hn p hp _ oracle' st st' p' hp').1)
      mid (ProbOracleComp.mem_support_of_mem oracle hmid)
    exact ⟨rfl, hlength r le_rfl mid.2 hmidInv.1⟩
  have hbound := runsInSpace_toNTM_seq_repeatUntilBlank
    (first := ofDeterministic (prepareRound (k := k) mark)) (body := tm.iterateWhileRound mark) (lastM := ofDeterministic (finish (k := k) mark))
    (t₁ := 3 * 0 + 6 * L + 16) (t := t + 10 * L + 22) (t₂ := 5 * L + 11) (rounds := r) (s₀ := ([], w₀))
    (ws := fun q => words q.1 q.2)
    (hfirst := (RunsWords.of_transformsTapes (Operation := Empty) (transformsTapes_prepareRound (k := k) mark [] w₀) (hP := rfl) (hQ := fun _ _ h => h) (ws' := words (k := k) w₀ []) (emitted := [])).mono (time' := 3 * 0 + 6 * L + 16)
      (by have := hlength 0 (by omega) w₀ hbase; omega))
    (nextTape k)
    words_injective
    inv (⟨hbase, Nat.zero_le L⟩ : inv 0 ([], w₀))
    (fun n hn p hp => by
      have hl : ∀ (OracleState : Type)
          (oracle : Empty × List Bool → StateT OracleState PMF (List Bool))
          (s : OracleState) (w' : List Bool) (s' : OracleState),
          (w', s') ∈ (ProbOracleComp.runWith oracle (step p.2) s).support → w'.length ≤ L :=
        fun _ oracle s w' s' hw' =>
          hlength (n + 1) hn w' (hpreserve n hn p.2 hp.1 _ oracle s s' w' hw').1
      have hround' := (RunsWords.iterateWhileRound (x := w₀) mark (vp := p.1)
        (hround n hn p.2 hp.1) hl []).of_map (fun v' => (p.2, v'))
        (fun q => words q.1 q.2) (fun _ => [])
      have := hp.2
      have := hlength n hn.le p.2 hp.1
      exact hround'.mono (by omega))
    (fun p hp => by
      have hround' := (RunsWords.iterateWhileRound (x := w₀) mark (vp := p.1) (l := 0)
        (hlast p.2 hp.1) (fun _ _ _ w' _ hw' => by
          simp only [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hw'
          simp [hw'.1]) []).of_map (fun v' => (p.2, v'))
        (fun q => words q.1 q.2) (fun _ => [])
      rw [map_pure] at hround'
      have := hp.2
      have := hlength r le_rfl p.2 hp.1
      exact hround'.mono (by omega))
    hpres
    (fun p _ _ _ _ _ p' hp' => by
      simp only [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hp'
      rw [hp'.1]
      exact words_next _ _)
    (fun _ oracle s s' p hp => by
      obtain ⟨hnil, hlen⟩ := hfinal _ oracle s s' p hp
      exact (RunsWords.of_transformsTapes (Operation := Empty) (transformsTapes_finish (k := k) mark p.1)
        (hP := congrArg (words p.1) hnil) (hQ := fun _ _ h => h) (ws' := fun _ => []) (emitted := p.1)).mono (time' := 5 * L + 11) (by omega))
  exact hbound.mono (by
    have : max (3 * 0 + 6 * L + 16) (max (t + 10 * L + 22) (5 * L + 11)) = t + 10 * L + 22 := by omega
    omega)

end Turing.MultiTapePTM
