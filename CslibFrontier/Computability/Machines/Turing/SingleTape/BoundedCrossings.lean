/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.SingleTape.CrossingSequence
public import Mathlib.Computability.DFA
import Mathlib.Computability.MyhillNerode
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Set.Finite.Powerset

/-!
# Bounded crossing sequences force regularity

If a deterministic single-tape machine `Cslib.Turing.SingleTapeTM` decides a language within time
`T`, answering under the head, and every crossing sequence at a boundary inside the input has
length at most `K`, then the language is regular.

The proof is Hennie's cut-and-paste argument combined with the Myhill–Nerode theorem
(`Language.IsRegular.of_finite_range_leftQuotient`). To a nonempty word `u` attach its tag: the
set of pairs (crossing sequence at the boundary after `u`, scanned symbol at the halt) over the
runs on all extensions `u ++ v`. Two nonempty words with the same tag have the same left
quotient: given `v`, pick `v'` with `u' ++ v'` giving the same crossing sequence as `u ++ v`, and
splice `u'` with `v` using `cut_and_paste_run`. The spliced run scans the symbol of the run on
`u ++ v` or that of the run on `u' ++ v'`, and both equal the one recorded in the tag. Tags are
sets of pairs drawn from a finite set, so there are finitely many left quotients.

Pighizzini proves a related criterion for nondeterministic machines as [Pighizzini2009, Theorem 1]
and calls it probably folklore; his proof builds a finite automaton whose states are the bounded
crossing sequences. The hypotheses are incomparable with the ones here: his bound covers every
boundary, including those in the blank region, but only the accepting computations, while the
bound here covers only the boundaries inside the input, on every input. Here the machine is
deterministic and the automaton comes from Myhill–Nerode instead.

## Main results

* `Cslib.Turing.SingleTapeTM.isRegular_of_crossings_le`: bounded crossing sequences at the
  boundaries `1, …, |w|` imply `Language.IsRegular`.

## References

* [F. C. Hennie, *One-tape, off-line Turing machine computations*][Hennie1965]
* [G. Pighizzini, *Nondeterministic one-tape off-line Turing machines and their time
  complexity*][Pighizzini2009]
-/

public section

open Cslib Cslib.Turing

namespace Cslib.Turing.SingleTapeTM

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] {tm : SingleTapeTM Symbol}
  {α : Type*} {ι : α → Symbol} {L : Language α} {yes : Symbol} {T : ℕ → ℕ}

variable (tm ι T) in
/-- The tag of `u`: the crossing sequences at the boundary after `u`, paired with the scanned
symbol at the halt, over the runs on all extensions `u ++ v`. -/
private def crossingTag (u : List α) : Set (List (Option tm.State) × Option Symbol) :=
  {p | ∃ v : List α,
    (tm.absInit ((u ++ v).map ι)).crossings (u.length : ℤ) (T (u ++ v).length) = p.1 ∧
      ((tm.absInit ((u ++ v).map ι)).run (T (u ++ v).length)).scanned = p.2}

/-- Nonempty words with the same tag have the same left quotient. -/
private lemma leftQuotient_eq_of_crossingTag_eq (hdec : tm.DecidesByHeadInTime ι L yes T)
    {u u' : List α} (hu : u ≠ []) (hu' : u' ≠ [])
    (h : crossingTag tm ι T u = crossingTag tm ι T u') :
    L.leftQuotient u = L.leftQuotient u' := by
  ext v
  rw [Language.mem_leftQuotient, Language.mem_leftQuotient]
  have hmem : ((tm.absInit ((u ++ v).map ι)).crossings (u.length : ℤ) (T (u ++ v).length),
      ((tm.absInit ((u ++ v).map ι)).run (T (u ++ v).length)).scanned) ∈ crossingTag tm ι T u :=
    ⟨v, rfl, rfl⟩
  rw [h] at hmem
  obtain ⟨v', hc, hs⟩ := hmem
  obtain ⟨h1, hy1⟩ := hdec.absRun (u ++ v)
  obtain ⟨h2, -⟩ := hdec.absRun (u' ++ v')
  obtain ⟨h3, hy3⟩ := hdec.absRun (u' ++ v)
  simp only [List.map_append] at h1 h2 h3 hy1 hy3 hc hs
  have hx : (tm.absInit (u'.map ι ++ v'.map ι)).crossings (u'.map ι).length
      (T (u' ++ v').length) =
      (tm.absInit (u.map ι ++ v.map ι)).crossings (u.map ι).length (T (u ++ v).length) := by
    rw [List.length_map, List.length_map]
    exact hc
  have hne : u'.map ι = [] ↔ u.map ι = [] := by
    simp only [List.map_eq_nil_iff]
    exact ⟨fun h' => (hu' h').elim, fun h' => (hu h').elim⟩
  obtain ⟨hC, -, -, hhead⟩ := cut_and_paste_run hne h2 h1 hx
  rw [AbsCfg.run_eq_of_halted _ hC h3] at hhead
  have hscan : ((tm.absInit (u'.map ι ++ v.map ι)).run (T (u' ++ v).length)).scanned =
      ((tm.absInit (u.map ι ++ v.map ι)).run (T (u ++ v).length)).scanned := by
    rcases hhead with h' | h'
    · rw [h', hs]
    · exact h'
  rw [← hy1, ← hy3, hscan]

/-- **Bounded crossing sequences force regularity** (Hennie's cut-and-paste with
Myhill–Nerode). If `tm` decides `L` within time `T`, answering under the head, and on every input
`w` the crossing sequence at every boundary `1 ≤ b ≤ |w|` during the first `T |w|` steps has length
at most `K`, then `L` is regular. -/
theorem isRegular_of_crossings_le (hdec : tm.DecidesByHeadInTime ι L yes T) (K : ℕ)
    (hK : ∀ (w : List α) (b : ℕ), 1 ≤ b → b ≤ w.length →
      ((tm.absInit (w.map ι)).crossings (b : ℤ) (T w.length)).length ≤ K) :
    L.IsRegular := by
  classical
  apply Language.IsRegular.of_finite_range_leftQuotient
  let A : Set (List (Option tm.State) × Option Symbol) :=
    {l : List (Option tm.State) | l.length ≤ K} ×ˢ Set.univ
  have hA : A.Finite := (List.finite_length_le _ K).prod Set.finite_univ
  let g : Set (List (Option tm.State) × Option Symbol) → Language α := fun t =>
    if h : ∃ u, u ≠ [] ∧ crossingTag tm ι T u = t then L.leftQuotient h.choose else L
  refine ((hA.finite_subsets.image g).insert L).subset ?_
  rintro _ ⟨u, rfl⟩
  by_cases hu : u = []
  · subst hu
    exact Set.mem_insert _ _
  · refine Set.mem_insert_of_mem _ ⟨crossingTag tm ι T u, fun p hp => ?_, ?_⟩
    · obtain ⟨v, hc, -⟩ := hp
      refine ⟨?_, Set.mem_univ _⟩
      rw [← hc]
      exact hK (u ++ v) u.length (List.length_pos_iff.mpr hu) (by simp)
    · have h : ∃ u', u' ≠ [] ∧ crossingTag tm ι T u' = crossingTag tm ι T u := ⟨u, hu, rfl⟩
      simp only [g]
      rw [dite_eq_left_of_eq_true (eq_true h)]
      exact leftQuotient_eq_of_crossingTag_eq hdec h.choose_spec.1 hu h.choose_spec.2

end Cslib.Turing.SingleTapeTM
