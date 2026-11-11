/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.InductiveCounting.Semantics
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph

/-!
# Feeding the compact native graph to inductive counting

The local configuration edge test already rejects vertices beyond the ambient bound of its radix.
Consequently restricting the graph to this bound changes no edge. A radix is *closed* on an input
when no vertex reachable in its graph overflows (`Turing.InductiveCounting.Closed`): then every
reachable view of the source fits the radix, and the counting controller's safety property for
the accepting vertices is exactly nonacceptance by the source
(`Turing.InductiveCounting.safe_iff_not_accepts`). No space bound of the source is used for this;
a space bound only shows that large radices are closed
(`Turing.InductiveCounting.closed_of_runsInSpace`).

## Main definitions

* `Turing.InductiveCounting.graphEdge`, `Turing.InductiveCounting.graphOverflow`,
  `Turing.InductiveCounting.graphAccepting`: the local tests on an actual input.
* `Turing.InductiveCounting.startRadix`: the first radix tried.
* `Turing.InductiveCounting.Closed`: no reachable vertex overflows.

## Main results

* `Turing.InductiveCounting.closed_iff_fits`: a closed radix represents every reachable view.
* `Turing.InductiveCounting.safe_iff_not_accepts`: native nonacceptance as graph safety.
* `Turing.InductiveCounting.closed_of_runsInSpace`: a space bound closes large radices.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.6][Sipser2013]
* [N. Immerman, *Nondeterministic Space Is Closed under Complementation*][Immerman1988]
-/

@[expose] public section

namespace Turing.InductiveCounting

open MultiTapeNTM.ConfigurationGraph

variable {k : ℕ} {State : Type} [Fintype State]
  (ntm : MultiTapeNTM k Bool State) (B : ℕ) (input : List Bool)

/-- The Boolean edge test obtained by supplying the one actual input symbol requested by the
compact graph. The operational query machine supplies this symbol without storing `input`. -/
noncomputable def graphEdge (u v : ℕ) : Bool :=
  edgeWithSymbol ntm B input.length u v input[queryIndex (k := k) B u]?

/-- The overflow test on the actual input. -/
noncomputable def graphOverflow (u : ℕ) : Bool :=
  overflow ntm B input.length u input[queryIndex (k := k) B u]?

variable (k State) in
/-- The accepting halted vertices; no input symbol is needed. -/
noncomputable def graphAccepting (u : ℕ) : Bool :=
  bad (k := k) (State := State) B input.length u

/-- Both endpoints of every accepted local edge are below the ambient bound. -/
theorem graphEdge_bounds {u v : ℕ} (h : graphEdge ntm B input u v = true) :
    u < vertexBound (k := k) B ∧ v < vertexBound (k := k) B :=
  lt_vertexBound_of_edgeWithSymbol h

/-- The controller's explicit vertex guards remove no compact configuration edge. -/
theorem boundedGraph_eq :
    Cslib.InductiveCounting.Graph (vertexBound (k := k) B) (graphEdge ntm B input) =
      Edge ntm B input := by
  funext u v
  apply propext
  constructor
  · exact fun h => h.2.2
  · intro h
    exact ⟨(graphEdge_bounds ntm B input h).1, (graphEdge_bounds ntm B input h).2, h⟩

variable (State) in
/-- The first radix tried: above every input position and every finite tag. -/
def startRadix (n : ℕ) : ℕ := (n + 2) * 2 ^ (Fintype.card (Option State) + 2)

theorem le_startRadix (n : ℕ) : n + 2 ≤ startRadix State n :=
  Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)

theorem card_lt_startRadix (n : ℕ) : Fintype.card (Option State) + 3 < startRadix State n := by
  have hm : 2 ^ (Fintype.card (Option State) + 2) ≤ startRadix State n :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hp : 2 ^ (Fintype.card (Option State) + 2) = 4 * 2 ^ Fintype.card (Option State) := by
    rw [pow_add]
    ring
  have h2 := Nat.lt_two_pow_self (n := Fintype.card (Option State))
  omega

variable {ntm B input}

/-- The initial view fits every radix above the finite tags. -/
theorem fits_init (hB : Fintype.card (Option State) + 1 < B) :
    Fits B (registers (ntm.initView input)) := by
  have hc := (Fintype.equivFin (Option State) (some ntm.q₀)).isLt
  intro i
  cases i with
  | inputPos => change 1 < B; omega
  | control => exact hc.trans (by omega)
  | output | head _ | left _ | right _ => change 0 < B; omega

/-- The start vertex lies below the ambient bound of every radix above the finite tags. -/
theorem startID_lt (hB : Fintype.card (Option State) + 1 < B) :
    startID ntm B < vertexBound (k := k) B := by
  have h := vertexID_lt (fits_init (ntm := ntm) (input := []) hB)
  rwa [vertexID_init] at h

variable (ntm B input) in
/-- A radix is closed on an input when no vertex reachable in its graph overflows. -/
def Closed : Prop :=
  Cslib.InductiveCounting.Safe (vertexBound (k := k) B) (startID ntm B) (graphEdge ntm B input)
    (graphOverflow ntm B input)

/-- **A closed radix represents every reachable view**, and conversely. -/
theorem closed_iff_fits (hB : Fintype.card (Option State) + 1 < B) :
    Closed ntm B input ↔ ∀ v, Relation.ReflTransGen ntm.ViewStep (ntm.initView input) v →
      Fits B (registers v) := by
  rw [Closed, Cslib.InductiveCounting.Safe, boundedGraph_eq]
  constructor
  · intro h
    refine fits_of_not_overflow (fits_init hB) fun u hu ho => ?_
    have := h u hu
    rw [graphOverflow] at this
    rw [Overflow, this] at ho
    exact Bool.false_ne_true ho
  · intro h u hu
    exact Bool.eq_false_iff.mpr (not_overflow_of_fits h u hu)

/-- On a closed radix, the controller's safety property for the accepting vertices is exactly the
absence of an accepting native computation path. -/
theorem safe_iff_not_accepts (hB : Fintype.card (Option State) + 1 < B)
    (hc : Closed ntm B input) :
    Cslib.InductiveCounting.Safe (vertexBound (k := k) B) (startID ntm B)
      (graphEdge ntm B input) (graphAccepting k State B input) ↔ ¬ ntm.Accepts input := by
  rw [Cslib.InductiveCounting.Safe, boundedGraph_eq,
    accepts_iff_reachable_bad ((closed_iff_fits hB).mp hc)]
  constructor
  · intro h ⟨u, hu, hb⟩
    have hf : graphAccepting k State B input u = false := h u hu
    rw [graphAccepting, hb] at hf
    exact Bool.false_ne_true hf.symm
  · intro h u hu
    exact Bool.eq_false_iff.mpr fun hb => h ⟨u, hu, hb⟩

/-- A larger radix of a closed one is closed. -/
theorem Closed.mono {B' : ℕ} (hB : Fintype.card (Option State) + 1 < B) (hBB : B ≤ B')
    (hc : Closed ntm B input) : Closed ntm B' input :=
  (closed_iff_fits (hB.trans_le hBB)).mpr fun v hv i =>
    ((closed_iff_fits hB).mp hc v hv i).trans_le hBB

/-- **A space bound closes large radices**: those above the input positions, the finite tags and
the stack codes of the visited cells. -/
theorem closed_of_runsInSpace {S : ℕ} (hs : ntm.RunsInSpace input S)
    (hn : input.length + 2 ≤ B) (hB : Fintype.card (Option State) + 3 < B)
    (hstack : 3 ^ (4 * S + 1) ≤ B) : Closed ntm B input :=
  (closed_iff_fits (by omega)).mpr fun _ hv =>
    fits_of_runsInSpace_of_le hs hn (by omega) (by omega) hstack hv

end Turing.InductiveCounting
