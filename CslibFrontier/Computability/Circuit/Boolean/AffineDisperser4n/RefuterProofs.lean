/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.Step
public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n
public import CslibFrontier.Computability.Complexity.Problems.XORSAT.Dense
public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.Refuter
public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.RefuterAffineRep
public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.RefuterSearch
import all CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.Refuter

/-!
# Correctness of the `4n - 10d` refuter

Every step chosen by `chooseStep?` is a step of gate elimination adding no gate, or a preparatory
operation removing a gate or lowering the auxiliary inputs of the minimal gate (`RefuterStep`). In
either case `refuterMeasure` decreases, so `refuterLoop` reaches a terminal state, preserving the
potential invariant `ΔW ≤ 10 Δa`. With `C.size + 10 * d < 4 * n`, the terminal state still has
`d < a`, and `findCounterexample` succeeds (`RefuterSearch.lean`).

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser4n.applyStep_valid`: one refuter step.
* `Cslib.Circuits.Boolean.AffineDisperser4n.refuterLoop_valid`: the refuter loop.
* `Cslib.Circuits.Boolean.AffineDisperser4n.refute_correct`: `refute` finds a disagreeing input
  for any circuit of size `< 4n - 10d` and any `d`-affine disperser.

The `poly(n, 2^d)` running time of the refuter is not formalized.
-/

public section

namespace Cslib.Circuits.Boolean.AffineDisperser4n

open Cslib.Circuits.Boolean.AffineDisperserCore
open Cslib.Circuits.Boolean.AffineDisperserCore.State
open Cslib.Circuits.Boolean.SemiCircuit
open Cslib.Complexity.XORSAT.Dense Cslib.Circuits Cslib.BitString
open Finset AffineDisperserCore State

variable {n : ℕ} {f : BooleanFunction n}


/-! ### Searches -/

private theorem find?_sort_eq_some {s : Finset ℕ} {p : ℕ → Bool} {x : ℕ}
    (h : (s.sort (· ≤ ·)).find? p = some x) : x ∈ s ∧ p x = true :=
  ⟨(Finset.mem_sort (· ≤ ·)).1 (List.mem_of_find?_eq_some h), List.find?_some h⟩

private theorem find?_sort_eq_none {s : Finset ℕ} {p : ℕ → Bool}
    (h : (s.sort (· ≤ ·)).find? p = none) : ∀ x ∈ s, p x = false := fun x hx => by
  have := List.find?_eq_none.1 h x ((Finset.mem_sort (· ≤ ·)).2 hx)
  simpa using this

private theorem findSome?_sort_eq_some {α : Type*} {s : Finset ℕ} {g : ℕ → Option α} {b : α}
    (h : (s.sort (· ≤ ·)).findSome? g = some b) : ∃ x ∈ s, g x = some b := by
  obtain ⟨x, hx, hgx⟩ := List.exists_of_findSome?_eq_some h
  exact ⟨x, (Finset.mem_sort (· ≤ ·)).1 hx, hgx⟩

private theorem findSome?_sort_eq_none {α : Type*} {s : Finset ℕ} {g : ℕ → Option α}
    (h : (s.sort (· ≤ ·)).findSome? g = none) : ∀ x ∈ s, g x = none := fun x hx =>
  List.findSome?_eq_none_iff.1 h x ((Finset.mem_sort (· ≤ ·)).2 hx)

/-- `isDegenerate` decides `Gate.Degenerate`. -/
theorem isDegenerate_iff (g : Gate) : isDegenerate g = true ↔ g.Degenerate := by
  obtain ⟨op, l, r⟩ := g
  unfold isDegenerate Gate.Degenerate
  cases l <;> cases r <;> simp

/-! ### Pairs and children -/

private theorem findPair_eq_some {S : State n} {p : ℕ} {pr : ZeroPair}
    (h : findPair S p = some pr) : pr ∈ S.pairs ∧ pr.Contains p :=
  findPair_spec h

private theorem exists_findPair {S : State n} (hS : S.Valid f) {p : ℕ} (hp : S.Paired p) :
    ∃ pr, findPair S p = some pr := by
  obtain ⟨pr, hpr, hc⟩ := hp
  exact Option.isSome_iff_exists.1 (findPair_isSome hS hpr hc)

/-- In a valid state, a parameter for which `findPair` finds nothing is unpaired. -/
theorem findPair_eq_none {S : State n} (hS : S.Valid f) {p : ℕ} (h : findPair S p = none) :
    ¬ S.Paired p := fun hp => by
  obtain ⟨pr, hpr⟩ := exists_findPair hS hp
  rw [h] at hpr
  cases hpr

/-- The children listed by `getChildren`. -/
theorem mem_getChildren {S : State n} {p : ℕ} {N : ℕ ⊕ ℕ} :
    N ∈ getChildren S p ↔ N ∈ S.children p := by
  unfold getChildren
  rcases N with J | e
  · simp only [List.mem_append, List.mem_filterMap, Finset.mem_sort]
    constructor
    · rintro (⟨J', hJ', hJ⟩ | ⟨e', he', he⟩)
      · split_ifs at hJ with h_mem
        · cases hJ; exact h_mem
      · simp at he
    · intro h
      exact Or.inl ⟨J, ((SemiCircuit.inl_mem_children _).1 h).1, by simp [h]⟩
  · simp only [List.mem_append, List.mem_filterMap, Finset.mem_sort]
    constructor
    · rintro (⟨J', hJ', hJ⟩ | ⟨e', he', he⟩)
      · simp at hJ
      · split_ifs at he with h_mem
        · cases he; exact h_mem
    · intro h
      exact Or.inr ⟨e, ((SemiCircuit.inr_mem_children _).1 h).1, by simp [h]⟩

/-- `getChildren` lists each child once. -/
theorem nodup_getChildren (S : State n) (p : ℕ) : (getChildren S p).Nodup := by
  unfold getChildren
  refine List.nodup_append.2 ⟨?_, ?_, ?_⟩
  · refine (Finset.sort_nodup _ _).filterMap fun J J' N h h' => ?_
    simp only [Option.mem_def, Option.ite_none_right_eq_some, Option.some.injEq] at h h'
    rw [← h.2] at h'
    exact (Sum.inl_injective h'.2).symm
  · refine (Finset.sort_nodup _ _).filterMap fun e e' N h h' => ?_
    simp only [Option.mem_def, Option.ite_none_right_eq_some, Option.some.injEq] at h h'
    rw [← h.2] at h'
    exact (Sum.inr_injective h'.2).symm
  · intro N h1 N' h2 heq
    simp only [List.mem_filterMap, Option.ite_none_right_eq_some, Option.some.injEq] at h1 h2
    obtain ⟨_, _, _, rfl⟩ := h1
    obtain ⟨_, _, _, rfl⟩ := h2
    cases heq

/-- The number of listed children is the degree. -/
theorem length_getChildren (S : State n) (p : ℕ) : (getChildren S p).length = S.deg p := by
  rw [← List.toFinset_card_of_nodup (nodup_getChildren S p)]
  unfold SemiCircuit.deg
  congr 1
  ext N
  rw [List.mem_toFinset, mem_getChildren]

/-- A parameter of degree at least `1` has a listed child. -/
theorem exists_getChildren_cons {S : State n} {p : ℕ} (h : 1 ≤ S.deg p) :
    ∃ N l, getChildren S p = N :: l := by
  rcases hl : getChildren S p with _ | ⟨N, l⟩
  · have := length_getChildren S p
    rw [hl] at this
    simp at this
    omega
  · exact ⟨N, l, rfl⟩

/-- A parameter of degree at least `2` has two listed children. -/
theorem exists_getChildren_cons_cons {S : State n} {p : ℕ} (h : 2 ≤ S.deg p) :
    ∃ N₁ N₂ l, getChildren S p = N₁ :: N₂ :: l := by
  rcases hl : getChildren S p with _ | ⟨N₁, _ | ⟨N₂, l⟩⟩
  · have := length_getChildren S p
    rw [hl] at this
    simp at this
    omega
  · have := length_getChildren S p
    rw [hl] at this
    simp at this
    omega
  · exact ⟨N₁, N₂, l, rfl⟩


/-! ### The step chosen -/

/-- None of the deletions `(D1)`–`(D4)` and no move applies. -/
def NoDeletion (S : State n) : Prop :=
  findD1 S = none ∧ findD2 S = none ∧ findD3 S = none ∧ findD4 S = none ∧ findMovable S = none

/-- What `chooseStep? S = some c` records about the searches. -/
def ChoiceSpec (S : State n) (u : ℕ) : StepChoice → Prop
  | .deleteConstantGate J => findD1 S = some J
  | .deleteDeadGate J => findD1 S = none ∧ findD2 S = some J
  | .deleteShortEqn e => findD1 S = none ∧ findD2 S = none ∧ findD3 S = some e
  | .deleteUnitParam x e =>
    findD1 S = none ∧ findD2 S = none ∧ findD3 S = none ∧ findD4 S = some (x, e)
  | .moveAffine J =>
    findD1 S = none ∧ findD2 S = none ∧ findD3 S = none ∧ findD4 S = none ∧
      findMovable S = some J
  | .degeneratePair p => NoDeletion S ∧ findDegeneratePair S = some p
  | .partnersShareChild p =>
    NoDeletion S ∧ findDegeneratePair S = none ∧ findPartnersShareChild S = some p
  | .pairInSystem p =>
    NoDeletion S ∧ findDegeneratePair S = none ∧ findPartnersShareChild S = none ∧
      findPairInSystem S = some p
  | .andOnPair G p =>
    NoDeletion S ∧ findDegeneratePair S = none ∧ findPartnersShareChild S = none ∧
      findPairInSystem S = none ∧ findAndOnPair S = some (G, p)
  | .swapAuxIn G =>
    NoDeletion S ∧ findDegeneratePair S = none ∧ findPartnersShareChild S = none ∧
      findPairInSystem S = none ∧ findAndOnPair S = none ∧
      ∃ hne : S.gates.Nonempty, G = S.gates.min' hne ∧ 0 < S.auxIn G
  | .pairCreation G =>
    NoDeletion S ∧ findDegeneratePair S = none ∧ findPartnersShareChild S = none ∧
      findPairInSystem S = none ∧ findAndOnPair S = none ∧
      ∃ hne : S.gates.Nonempty, G = S.gates.min' hne ∧ S.auxIn G = 0 ∧ u ≠ G

/-- Inversion of `chooseStep?`. -/
theorem chooseStep?_spec {S : State n} {c : StepChoice} (h : chooseStep? S = some c) :
    ∃ u, S.out.arg = .node u ∧ u ∉ S.params ∧ ChoiceSpec S u c := by
  unfold chooseStep? at h
  rcases hout : S.out.arg with b | u
  · simp [hout] at h
  simp only [hout] at h
  refine ⟨u, rfl, ?_⟩
  by_cases hu : u ∈ S.params
  · simp [hu] at h
  refine ⟨hu, ?_⟩
  simp only [hu, ite_false] at h
  rcases h1 : findD1 S with _ | J
  · rcases h2 : findD2 S with _ | J
    · rcases h3 : findD3 S with _ | e
      · rcases h4 : findD4 S with _ | ⟨x, e⟩
        · rcases h5 : findMovable S with _ | J
          · have hN : NoDeletion S := ⟨h1, h2, h3, h4, h5⟩
            rcases h6 : findDegeneratePair S with _ | p
            · rcases h7 : findPartnersShareChild S with _ | p
              · rcases h8 : findPairInSystem S with _ | p
                · rcases h9 : findAndOnPair S with _ | ⟨G, p⟩
                  · simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9] at h
                    split_ifs at h with hne hpos hug
                    · cases h
                      exact ⟨hN, h6, h7, h8, h9, hne, rfl, hpos⟩
                    · cases h
                      exact ⟨hN, h6, h7, h8, h9, hne, rfl, by omega, hug⟩
                  · simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, Option.some.injEq] at h
                    subst h
                    exact ⟨hN, h6, h7, h8, h9⟩
                · simp only [h1, h2, h3, h4, h5, h6, h7, h8, Option.some.injEq] at h
                  subst h
                  exact ⟨hN, h6, h7, h8⟩
              · simp only [h1, h2, h3, h4, h5, h6, h7, Option.some.injEq] at h
                subst h
                exact ⟨hN, h6, h7⟩
            · simp only [h1, h2, h3, h4, h5, h6, Option.some.injEq] at h
              subst h
              exact ⟨hN, h6⟩
          · simp only [h1, h2, h3, h4, h5, Option.some.injEq] at h
            subst h
            exact ⟨h1, h2, h3, h4, h5⟩
        · simp only [h1, h2, h3, h4, Option.some.injEq] at h
          subst h
          exact ⟨h1, h2, h3, h4⟩
      · simp only [h1, h2, h3, Option.some.injEq] at h
        subst h
        exact ⟨h1, h2, h3⟩
    · simp only [h1, h2, Option.some.injEq] at h
      subst h
      exact ⟨h1, h2⟩
  · simp only [h1, Option.some.injEq] at h
    subst h
    exact h1

/-! ### Consequences of failed searches -/

private theorem findD1_eq_some {S : State n} {J : ℕ} (h : findD1 S = some J) :
    J ∈ S.gates ∧ (S.gate J).Degenerate := by
  obtain ⟨hJ, hd⟩ := find?_sort_eq_some h
  exact ⟨hJ, (isDegenerate_iff _).1 hd⟩

private theorem findD1_eq_none {S : State n} (h : findD1 S = none) :
    ∀ J ∈ S.gates, ¬ (S.gate J).Degenerate := fun J hJ hd => by
  have := find?_sort_eq_none h J hJ
  rw [(isDegenerate_iff _).2 hd] at this
  cases this

private theorem findD2_eq_some {S : State n} {J : ℕ} (h : findD2 S = some J) :
    J ∈ S.gates ∧ (∀ K ∈ S.gates, ¬ (S.gate K).Reads J) ∧ ¬ S.out.Reads J := by
  obtain ⟨hJ, hd⟩ := find?_sort_eq_some h
  simp only [decide_eq_true_eq] at hd
  exact ⟨hJ, hd.1, hd.2⟩

private theorem findD2_eq_none {S : State n} (h : findD2 S = none) :
    ∀ J ∈ S.gates, (∃ K ∈ S.gates, (S.gate K).Reads J) ∨ S.out.Reads J := fun J hJ => by
  have := find?_sort_eq_none h J hJ
  simp only [decide_eq_false_iff_not, not_and, not_not] at this
  by_cases hK : ∃ K ∈ S.gates, (S.gate K).Reads J
  · exact Or.inl hK
  · push Not at hK
    exact Or.inr (this hK)

private theorem findD3_eq_some {S : State n} {e : ℕ} (h : findD3 S = some e) :
    e ∈ S.eqns ∧ (S.eqn e).terms.card ≤ 2 := by
  obtain ⟨he, hd⟩ := find?_sort_eq_some h
  exact ⟨he, by simpa using hd⟩

private theorem findD3_eq_none {S : State n} (h : findD3 S = none) :
    ∀ e ∈ S.eqns, 2 < (S.eqn e).terms.card := fun e he => by
  have := find?_sort_eq_none h e he
  simp only [decide_eq_false_iff_not, not_le] at this
  exact this

private theorem findD4_eq_some {S : State n} {x e : ℕ} (h : findD4 S = some (x, e)) :
    x ∈ S.unpaired ∧ ¬ S.out.Reads x ∧ e ∈ S.eqns ∧ S.children x = {.inr e} := by
  obtain ⟨x', hx', hg⟩ := findSome?_sort_eq_some h
  split_ifs at hg with hout
  obtain ⟨e', he', hg'⟩ := findSome?_sort_eq_some hg
  split_ifs at hg' with hch
  cases hg'
  exact ⟨hx', hout, he', hch⟩

private theorem findD4_eq_none {S : State n} (h : findD4 S = none) :
    ∀ x ∈ S.unpaired, ¬ S.out.Reads x → ∀ e ∈ S.eqns, S.children x ≠ {.inr e} :=
  fun x hx hout e he hch => by
    have := findSome?_sort_eq_none h x hx
    have hout' : ¬ S.out.arg = .node x := hout
    simp only [hout', ite_false] at this
    have := findSome?_sort_eq_none this e he
    simp [hch] at this

private theorem findMovable_eq_some {S : State n} {J : ℕ} (h : findMovable S = some J) :
    J ∈ S.gates ∧ IsAffineOp (S.gate J).op ∧ ∀ i, (S.gate J).Reads i → i ∉ S.gates := by
  obtain ⟨hJ, hd⟩ := find?_sort_eq_some h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hd
  obtain ⟨⟨haff, hl⟩, hr⟩ := hd
  refine ⟨hJ, haff, fun i hi hig => ?_⟩
  rcases hi with hi | hi
  · rw [hi] at hl; simp [isGate, hig] at hl
  · rw [hi] at hr; simp [isGate, hig] at hr

private theorem findMovable_eq_none {S : State n} (h : findMovable S = none) :
    ∀ J ∈ S.gates, IsAffineOp (S.gate J).op → isGate S (S.gate J).left = true ∨
      isGate S (S.gate J).right = true := fun J hJ haff => by
  have := find?_sort_eq_none h J hJ
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, Bool.not_eq_false'] at this
  tauto

private theorem findDegeneratePair_eq_some {S : State n} {p : ℕ}
    (h : findDegeneratePair S = some p) :
    S.Paired p ∧ (S.deg p = 0 ∨ 2 ≤ S.deg p) := by
  obtain ⟨-, hd⟩ := find?_sort_eq_some h
  simpa using hd

private theorem findDegeneratePair_eq_none {S : State n} (hS : S.Valid f)
    (h : findDegeneratePair S = none) : ¬ S.DegeneratePair := by
  intro hdp
  obtain ⟨p, hp, hd⟩ := hdp
  have := find?_sort_eq_none h p (hS.mem_params_of_paired hp)
  simp only [decide_eq_false_iff_not] at this
  exact this ⟨hp, hd⟩

private theorem findPartnersShareChild_eq_some {S : State n} {p : ℕ}
    (h : findPartnersShareChild S = some p) :
    ∃ pr ∈ S.pairs, pr.fst = p ∧ (S.children pr.fst ∩ S.children pr.snd).Nonempty := by
  obtain ⟨-, hd⟩ := find?_sort_eq_some h
  simpa using hd

private theorem findPartnersShareChild_eq_none {S : State n} (hS : S.Valid f)
    (h : findPartnersShareChild S = none) : ¬ S.PartnersShareChild := by
  intro hpsc
  obtain ⟨pr, hpr, hsh⟩ := hpsc
  have := find?_sort_eq_none h pr.fst (hS.pair_mem pr hpr).1
  simp only [decide_eq_false_iff_not] at this
  exact this ⟨pr, hpr, rfl, hsh⟩

private theorem findPairInSystem_eq_some {S : State n} {p : ℕ} (h : findPairInSystem S = some p) :
    S.Paired p ∧ ∃ e ∈ S.eqns, p ∈ (S.eqn e).terms := by
  obtain ⟨-, hd⟩ := find?_sort_eq_some h
  simpa using hd

private theorem findPairInSystem_eq_none {S : State n} (hS : S.Valid f)
    (h : findPairInSystem S = none) {p e : ℕ} (he : e ∈ S.eqns)
    (hpe : p ∈ (S.eqn e).terms) : ¬ S.Paired p := fun hp => by
  have := find?_sort_eq_none h p (hS.mem_params_of_paired hp)
  simp only [decide_eq_false_iff_not] at this
  exact this ⟨hp, e, he, hpe⟩

private theorem findAndOnPair_eq_some {S : State n} {G p : ℕ} (h : findAndOnPair S = some (G, p)) :
    G ∈ S.gates ∧ ¬ IsAffineOp (S.gate G).op ∧ S.Paired p ∧ ∃ w, p ≠ w ∧ p ∈ S.params ∧
      w ∈ S.params ∧ (S.gate G).Reads p ∧ (S.gate G).Reads w ∧ otherArg (S.gate G) p = w := by
  obtain ⟨G', hG', hg⟩ := findSome?_sort_eq_some h
  split_ifs at hg with hna
  rcases hl : (S.gate G').left with _ | p'
  · simp [hl] at hg
  rcases hr : (S.gate G').right with _ | w'
  · simp [hl, hr] at hg
  simp only [hl, hr] at hg
  split_ifs at hg with hc hp hw
  · cases hg
    refine ⟨hG', hna, hp, w', hc.1, hc.2.1, hc.2.2, Or.inl hl, Or.inr hr, ?_⟩
    simp [otherArg, hl, hr]
  · cases hg
    refine ⟨hG', hna, hw, p', fun h => hc.1 h.symm, hc.2.2, hc.2.1, Or.inr hr, Or.inl hl, ?_⟩
    simp only [otherArg, hl, hr]
    exact ite_eq_right hc.1

private theorem findAndOnPair_eq_none {S : State n} (h : findAndOnPair S = none) {G p w : ℕ}
    (hG : G ∈ S.gates) (hna : ¬ IsAffineOp (S.gate G).op) (hl : (S.gate G).left = .node p)
    (hr : (S.gate G).right = .node w) (hpw : p ≠ w) (hp : p ∈ S.params) (hw : w ∈ S.params) :
    ¬ S.Paired p ∧ ¬ S.Paired w := by
  have := findSome?_sort_eq_none h G hG
  simp only [hna, not_false_eq_true, ite_true, hl, hr] at this
  simp only [hpw, hp, hw, ne_eq, not_false_eq_true, and_self, ite_true] at this
  split_ifs at this with h1 h2
  exact ⟨h1, h2⟩


/-! ### Steps of the refuter -/

private theorem auxArg_le_one (S : State n) (a : Arg) : S.auxArg a ≤ 1 := by
  cases a with
  | const b => simp [auxArg]
  | node x =>
    simp only [auxArg]
    split_ifs <;> omega

private theorem minAuxIn_le (S : State n) :
    (if h : S.gates.Nonempty then S.auxIn (S.gates.min' h) else 0) ≤ 2 := by
  split_ifs with h
  · unfold auxIn
    have := auxArg_le_one S (S.gate (S.gates.min' h)).left
    have := auxArg_le_one S (S.gate (S.gates.min' h)).right
    omega
  · omega

/-- A step of the refuter: a gate-elimination step adding no gate, or a preparatory operation
that removes a gate or keeps the gates and lowers the auxiliary inputs of the minimal gate. -/
def RefuterStep (f : BooleanFunction n) (S S' : State n) : Prop :=
  (Step f S S' ∧ S'.gates ⊆ S.gates) ∨
  (Preparation f S S' ∧ (S'.gates.card < S.gates.card ∨
    (S'.gates = S.gates ∧ ∃ hne : S.gates.Nonempty,
      auxIn S' (S.gates.min' hne) < S.auxIn (S.gates.min' hne))))

private theorem min'_congr {s t : Finset ℕ} (h : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    s.min' hs = t.min' ht := by
  subst h
  rfl

/-- A refuter step lowers `refuterMeasure`, keeps validity, does not increase `a`, and satisfies
`ΔW ≤ 10 Δa`. -/
theorem RefuterStep.spec {S S' : State n} (h : RefuterStep f S S') :
    refuterMeasure S' < refuterMeasure S ∧ S'.Valid f ∧ S'.W + 10 * S.a ≤ S.W + 10 * S'.a ∧
      S'.a ≤ S.a := by
  have h1 := minAuxIn_le S
  have h2 := minAuxIn_le S'
  rcases h with ⟨hs, hg⟩ | ⟨hp, hg | ⟨hg, hne, haux⟩⟩
  · have hcard := Finset.card_le_card hg
    have hpot := hs.potential
    rw [config_ca] at hpot
    refine ⟨?_, hs.valid, hpot, hs.a_le⟩
    unfold refuterMeasure
    have := hs.lt
    have := hs.a_le
    omega
  · have ha := hp.a_eq
    refine ⟨?_, hp.valid, ?_, ha.le⟩
    · unfold refuterMeasure
      have := hp.m_eq
      have := hp.s_eq
      omega
    · have := hp.W_le
      omega
  · have ha := hp.a_eq
    refine ⟨?_, hp.valid, ?_, ha.le⟩
    · unfold refuterMeasure
      have hne' : S'.gates.Nonempty := hg ▸ hne
      rw [dite_eq_left hne, dite_eq_left hne', min'_congr hg hne' hne, hg]
      have := hp.m_eq
      have := hp.s_eq
      omega
    · have := hp.W_le
      omega

/-! #### Deletions and moves -/

private theorem refuterStep_deleteConstantGate {S : State n} (hS : S.Valid f) {J : ℕ}
    (h : findD1 S = some J) : RefuterStep f S (applyStep S (.deleteConstantGate J)) := by
  obtain ⟨hJ, hd⟩ := findD1_eq_some h
  exact Or.inl ⟨Reduction.step_of_delete (hS.reduction_deleteConstraint (N := .inl J) ⟨hJ, hd⟩) hS,
    S.deleteConstraint_gates_subset _⟩

private theorem refuterStep_deleteDeadGate {S : State n} (hS : S.Valid f) {J : ℕ}
    (h : findD2 S = some J) : RefuterStep f S (applyStep S (.deleteDeadGate J)) := by
  obtain ⟨hJ, hK, hout⟩ := findD2_eq_some h
  refine Or.inl ⟨Reduction.step_of_delete (hS.reduction_deleteGate (ℓ := Lit.const false)
    ⟨hJ, (fun _ h => by cases h), Or.inr ⟨hK, hout⟩⟩ (fun _ h => by cases h)) hS, ?_⟩
  change (S.deleteGate J (Lit.const false)).gates ⊆ S.gates
  rw [deleteGate_gates]
  exact Finset.erase_subset _ _

private theorem refuterStep_deleteShortEqn {S : State n} (hS : S.Valid f) {e : ℕ}
    (h : findD3 S = some e) : RefuterStep f S (applyStep S (.deleteShortEqn e)) := by
  obtain ⟨he, hcard⟩ := findD3_eq_some h
  exact Or.inl ⟨Reduction.step_of_delete (hS.reduction_deleteConstraint (N := .inr e)
    ⟨he, hcard⟩) hS, S.deleteConstraint_gates_subset _⟩

/-- The auxiliary variable chosen by `unitDelete`. -/
private theorem unitDelete_eq {S : State n} (hS : S.Valid f) {x e : ℕ} (hx : x ∈ S.params)
    (he : e ∈ S.eqns) (hxe : x ∈ (S.eqn e).terms) :
    ∃ Q ∈ S.aux, x ∈ (findAffineRep S Q).2 ∧ unitDelete S x e =
      (S.swap x Q (findAffineRep S Q).1 (findAffineRep S Q).2).dropEqn e x := by
  obtain ⟨Q₀, hQ₀, c₀, T₀, haff₀, hxT₀⟩ :=
    SemiCircuit.exists_affineIn_of_mem_terms hS.wf hx he hxe
  rcases hf : (S.aux.sort (· ≤ ·)).find? (fun Q => decide (x ∈ (findAffineRep S Q).2)) with
    _ | Q
  · exfalso
    have := find?_sort_eq_none hf Q₀ hQ₀
    have hT := (SemiCircuit.AffineIn.unique (C := S.toSemiCircuit) hS.wf
      (findAffineRep_spec hS.wf hQ₀) haff₀).2
    simp only [decide_eq_false_iff_not] at this
    exact this (hT ▸ hxT₀)
  · obtain ⟨hQ, hxQ⟩ := find?_sort_eq_some hf
    simp only [decide_eq_true_eq] at hxQ
    refine ⟨Q, hQ, hxQ, ?_⟩
    unfold unitDelete
    rw [hf]

private theorem refuterStep_unitDelete {S : State n} (hS : S.Valid f) {x e : ℕ}
    (hx : x ∈ S.unpaired) (hout : ¬ S.out.Reads x) (hcx : S.children x = {.inr e}) :
    RefuterStep f S (unitDelete S x e) := by
  obtain ⟨he, hxe⟩ := (SemiCircuit.inr_mem_children _).1
    (by rw [hcx]; exact Finset.mem_singleton_self _)
  obtain ⟨Q, hQ, hxQ, heq⟩ := unitDelete_eq hS (mem_unpaired.1 hx).1 he hxe
  rw [heq]
  obtain ⟨hS', hm, hs, hq, ha, hW⟩ :=
    Valid.unitDelete hS hx hcx hout hQ (findAffineRep_spec hS.wf hQ) hxQ
  exact Or.inl ⟨⟨hS', by omega, by omega, by omega, by rw [config_ca, ha]; omega⟩, subset_rfl⟩

private theorem refuterStep_moveAffine {S : State n} (hS : S.Valid f) {J : ℕ}
    (h : findMovable S = some J) : RefuterStep f S (applyStep S (.moveAffine J)) := by
  obtain ⟨hJ, haff, hin⟩ := findMovable_eq_some h
  obtain ⟨hprep, hlt⟩ := Valid.preparation_moveAffine hS hJ haff hin
  exact Or.inr ⟨hprep, Or.inl hlt⟩

/-! #### Pair cases -/

private theorem refuterStep_degeneratePair {S : State n} (hS : S.Valid f) {p : ℕ}
    (h : findDegeneratePair S = some p) :
    RefuterStep f S (applyStep S (.degeneratePair p)) := by
  obtain ⟨hp, hdeg⟩ := findDegeneratePair_eq_some h
  obtain ⟨pr, hpr⟩ := exists_findPair hS hp
  obtain ⟨hprm, hprp⟩ := findPair_eq_some hpr
  simp only [applyStep, hpr]
  by_cases h0 : S.deg p = 0
  · rw [ite_eq_left h0]
    exact Or.inl ⟨Valid.step_degeneratePair_zero hS hprm hprp h0, subset_rfl⟩
  · rw [ite_eq_right h0]
    obtain ⟨N₁, N₂, l, hl⟩ := exists_getChildren_cons_cons (S := S) (p := p) (by omega)
    have hnd := nodup_getChildren S p
    have hN₁ : N₁ ∈ S.children p := mem_getChildren.1 (by rw [hl]; simp)
    have hN₂ : N₂ ∈ S.children p := mem_getChildren.1 (by rw [hl]; simp)
    rw [hl] at hnd ⊢
    have hne : N₁ ≠ N₂ := fun he => by simp [he] at hnd
    exact Or.inl ⟨Valid.step_degeneratePair_two hS hprm hprp hN₁ hN₂ hne,
      (deleteConstraint_gates_subset _ _).trans (deleteConstraint_gates_subset _ _)⟩

private theorem partnersShareChildStep_gates_subset (S : State n) (pr : ZeroPair)
    (H : ℕ ⊕ ℕ) : (S.partnersShareChildStep pr H).gates ⊆ S.gates := by
  rcases H with G | e
  · simp only [partnersShareChildStep]
    split_ifs <;> exact Finset.erase_subset _ _
  · exact deleteConstraint_gates_subset _ _

private theorem refuterStep_partnersShareChild {S : State n} (hS : S.Valid f) {p : ℕ}
    (hD3 : findD3 S = none) (hDP : findDegeneratePair S = none)
    (h : findPartnersShareChild S = some p) :
    RefuterStep f S (applyStep S (.partnersShareChild p)) := by
  have hndeg := findDegeneratePair_eq_none hS hDP
  obtain ⟨pr, hpr, hfst, H, hH⟩ := findPartnersShareChild_eq_some h
  obtain ⟨hHp, hHr⟩ := Finset.mem_inter.1 hH
  have hp : S.Paired p := ⟨pr, hpr, Or.inl hfst⟩
  obtain ⟨pr', hpr'⟩ := exists_findPair hS hp
  obtain ⟨hprm', hprp'⟩ := findPair_eq_some hpr'
  obtain rfl : pr' = pr := hS.pair_unique hprm' hpr hprp' (Or.inl hfst)
  subst hfst
  have hdeg := Paired.deg_eq_one hndeg hp
  obtain ⟨N, l, hl⟩ := exists_getChildren_cons (S := S) (p := pr'.fst) (by omega)
  have hN : N ∈ S.children pr'.fst := mem_getChildren.1 (by rw [hl]; simp)
  have hNH : N = H := by
    have hc := AffineDisperserCore.State.children_eq_singleton hdeg.le hHp
    rw [hc, Finset.mem_singleton] at hN
    exact hN
  subst hNH
  simp only [applyStep, hpr', hl]
  exact Or.inl ⟨Valid.step_partnersShareChild_of hS (findD3_eq_none hD3) hndeg hprm' hHp hHr,
    partnersShareChildStep_gates_subset _ _ _⟩

private theorem refuterStep_pairInSystem {S : State n} (hS : S.Valid f) {u p : ℕ}
    (hout : S.out.arg = .node u) (hu : u ∉ S.params) (hDP : findDegeneratePair S = none)
    (hPSC : findPartnersShareChild S = none) (h : findPairInSystem S = some p) :
    RefuterStep f S (applyStep S (.pairInSystem p)) := by
  have hndeg := findDegeneratePair_eq_none hS hDP
  have hnsh := findPartnersShareChild_eq_none hS hPSC
  obtain ⟨hp, e, he, hpe⟩ := findPairInSystem_eq_some h
  obtain ⟨pr, hpr⟩ := exists_findPair hS hp
  obtain ⟨hprm, hprp⟩ := findPair_eq_some hpr
  have hrp : S.Paired (pr.partner p) := ⟨pr, hprm, pr.contains_partner hprp⟩
  obtain ⟨Hr, l, hl⟩ := exists_getChildren_cons (S := S) (p := pr.partner p)
    (by rw [Paired.deg_eq_one hndeg hrp])
  have hHr : Hr ∈ S.children (pr.partner p) := mem_getChildren.1 (by rw [hl]; simp)
  have hdegp := Paired.deg_eq_one hndeg hp
  have hcp : S.children p = {.inr e} :=
    AffineDisperserCore.State.children_eq_singleton hdegp.le
      ((SemiCircuit.inr_mem_children _).2 ⟨he, hpe⟩)
  have hgp : getChildren S p = [.inr e] := by
    obtain ⟨N, l', hl'⟩ := exists_getChildren_cons (S := S) (p := p) (by omega)
    have hlen := length_getChildren S p
    rw [hl', hdegp] at hlen
    have hl'0 : l' = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst hl'0
    have hN : N ∈ S.children p := mem_getChildren.1 (by rw [hl']; simp)
    rw [hcp, Finset.mem_singleton] at hN
    rw [hl', hN]
  have hpout : ¬ S.out.Reads p := fun hr => by
    have : S.out.arg = .node p := hr
    rw [hout] at this
    cases this
    exact hu (hS.mem_params_of_paired hp)
  obtain ⟨hS₂, hpunp, hch, h0, hne0⟩ :=
    Valid.step_pairInSystem_of hS hndeg hnsh hprm hprp he hpe hpout hHr
  simp only [applyStep, hpr, hl, hgp]
  split_ifs with hd
  · exact Or.inl ⟨h0 hd, deleteConstraint_gates_subset _ _⟩
  · set S₂ := (S.fixConst (pr.partner p) (pr.partnerBias p)).deleteConstraint Hr with hS₂def
    obtain ⟨N, hN⟩ : (S₂.children p).Nonempty :=
      Finset.card_pos.1 (Nat.pos_of_ne_zero hd)
    have hNe := Finset.mem_singleton.1 (hch hN)
    subst hNe
    obtain ⟨he₂, hpe₂⟩ := (SemiCircuit.inr_mem_children _).1 hN
    obtain ⟨Q, hQ, hpQ, heq⟩ := unitDelete_eq hS₂ (mem_unpaired.1 hpunp).1 he₂ hpe₂
    rw [heq]
    exact Or.inl ⟨hne0 hd Q _ _ hQ (findAffineRep_spec hS₂.wf hQ) hpQ,
      deleteConstraint_gates_subset _ _⟩

/-- `fixArg g w` fixes the argument `w` of a non-affine gate to a value making it constant. -/
private theorem fixArg_spec {g : Gate} (hg : ¬ IsAffineOp g.op) {a w : ℕ} (haw : a ≠ w)
    (hargs : (g.left = .node a ∧ g.right = .node w) ∨ (g.left = .node w ∧ g.right = .node a))
    (val : ℕ → Bool) (hw : val w = (fixArg g w).1) : g.eval val = (fixArg g w).2 := by
  obtain ⟨α, β, γ, H⟩ := exists_and_form hg
  rcases hargs with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · simp only [fixArg, hr, ite_true] at hw ⊢
    rw [Gate.eval_of_args hl hr, hw]
    have hβ : β = !decide (g.op false false = g.op true false) := by
      rw [H false false, H true false]
      cases α <;> cases β <;> cases γ <;> rfl
    have H2 : g.op false β = γ := by
      rw [H]
      cases α <;> cases β <;> cases γ <;> rfl
    rw [←hβ]
    rw [H, H2]
    cases α <;> cases β <;> cases γ <;> cases val a <;> rfl
  · have hr' : g.right ≠ .node w := by rw [hr]; simpa using haw
    simp only [fixArg, hr', ite_false] at hw ⊢
    rw [Gate.eval_of_args hl hr, hw]
    have hα : α = !decide (g.op false false = g.op false true) := by
      rw [H false false, H false true]
      cases α <;> cases β <;> cases γ <;> rfl
    have H2 : g.op α false = γ := by
      rw [H]
      cases α <;> cases β <;> cases γ <;> rfl
    rw [←hα]
    rw [H, H2]
    cases α <;> cases β <;> cases γ <;> cases val a <;> rfl

private theorem andOnPairStep_gates_subset (S : State n) (G : ℕ) (pr : ZeroPair) (p w : ℕ)
    (prw : Option ZeroPair) (b c : Bool) (Hr : ℕ ⊕ ℕ) :
    (S.andOnPairStep G pr p w prw b c Hr).gates ⊆ S.gates := by
  unfold andOnPairStep
  refine (deleteConstraint_gates_subset _ _).trans ?_
  rw [deleteGate_gates]
  refine (Finset.erase_subset _ _).trans ?_
  rcases prw with _ | q
  · exact subset_rfl
  · dsimp only
    split_ifs <;> exact subset_rfl

private theorem refuterStep_andOnPair {S : State n} (hS : S.Valid f) {G p : ℕ}
    (hDP : findDegeneratePair S = none) (hPSC : findPartnersShareChild S = none)
    (h : findAndOnPair S = some (G, p)) : RefuterStep f S (applyStep S (.andOnPair G p)) := by
  have hndeg := findDegeneratePair_eq_none hS hDP
  have hnsh := findPartnersShareChild_eq_none hS hPSC
  obtain ⟨hG, hna, hp, w, hpw, hppar, hwpar, hGp, hGw, hw⟩ := findAndOnPair_eq_some h
  obtain ⟨pr, hpr⟩ := exists_findPair hS hp
  obtain ⟨hprm, hprp⟩ := findPair_eq_some hpr
  have hrp : S.Paired (pr.partner p) := ⟨pr, hprm, pr.contains_partner hprp⟩
  obtain ⟨Hr, l, hl⟩ := exists_getChildren_cons (S := S) (p := pr.partner p)
    (by rw [Paired.deg_eq_one hndeg hrp])
  have hHr : Hr ∈ S.children (pr.partner p) := mem_getChildren.1 (by rw [hl]; simp)
  simp only [applyStep, hpr, hl, hw]
  exact Or.inl ⟨Valid.step_andOnPair_of hS hndeg hnsh hG hprm hprp hwpar hpw hGp hGw
    (fun h => findPair_eq_none hS h) (fun q h => findPair_eq_some h)
    (fixArg_spec hna hpw (Gate.args_of_reads hpw hGp hGw)) hHr,
    andOnPairStep_gates_subset _ _ _ _ _ _ _ _ _⟩

/-! #### The minimal gate -/

/-- A non-degenerate gate reads two distinct internal values. -/
private theorem exists_args_of_not_degenerate {g : Gate} (hg : ¬ g.Degenerate) :
    ∃ u v, g.left = .node u ∧ g.right = .node v ∧ u ≠ v := by
  unfold Gate.Degenerate at hg
  push Not at hg
  obtain ⟨hl, hr, hne⟩ := hg
  rcases hgl : g.left with c | u
  · exact absurd hgl (hl c)
  rcases hgr : g.right with c | v
  · exact absurd hgr (hr c)
  refine ⟨u, v, rfl, rfl, fun he => hne ?_⟩
  rw [hgl, hgr, he]

private theorem refuterStep_swapAuxIn {S : State n} (hS : S.Valid f) (hD1 : findD1 S = none)
    (hPIS : findPairInSystem S = none) (hne : S.gates.Nonempty)
    (hpos : 0 < S.auxIn (S.gates.min' hne)) :
    RefuterStep f S (applyStep S (.swapAuxIn (S.gates.min' hne))) := by
  set G := S.gates.min' hne with hGdef
  have hG : G ∈ S.gates := Finset.min'_mem _ _
  obtain ⟨u, v, hl, hr, huv⟩ := exists_args_of_not_degenerate (findD1_eq_none hD1 G hG)
  obtain ⟨a, b, hab, hGa, hGb, ha, hargs⟩ : ∃ a b, a ≠ b ∧ (S.gate G).Reads a ∧
      (S.gate G).Reads b ∧ a ∈ S.aux ∧ auxArgs S (S.gate G) = some (a, b) := by
    unfold auxIn at hpos
    rw [hl, hr] at hpos
    by_cases hua : u ∈ S.aux
    · exact ⟨u, v, huv, Or.inl hl, Or.inr hr, hua, by simp [auxArgs, hl, hr, hua]⟩
    · have hva : v ∈ S.aux := by
        by_contra hva
        simp [auxArg, hua, hva] at hpos
      exact ⟨v, u, huv.symm, Or.inr hr, Or.inl hl, hva, by simp [auxArgs, hl, hr, hua, hva]⟩
  have haff := findAffineRep_spec hS.wf ha
  simp only [applyStep, hargs]
  by_cases hsub : (findAffineRep S a).2 ⊆ {b}
  · rw [ite_eq_left hsub]
    refine Or.inl ⟨Valid.step_deleteGate_affineIn hS hG hab hGa hGb haff hsub, ?_⟩
    rw [deleteGate_gates]
    exact Finset.erase_subset _ _
  · rw [ite_eq_right hsub]
    obtain ⟨y, hyT, hyb⟩ : ∃ y ∈ (findAffineRep S a).2, y ≠ b := by
      by_contra hc
      push Not at hc
      exact hsub fun y hy => Finset.mem_singleton.2 (hc y hy)
    have hypar := haff.1 hyT
    obtain ⟨e, he, hye⟩ :=
      haff.mem_terms hS.wf (fun hp => hS.wf.notMem_aux_of_mem_params hp ha) hyT
    have hyunp : y ∈ S.unpaired := mem_unpaired.2 ⟨hypar, findPairInSystem_eq_none hS hPIS he hye⟩
    rcases hf : ((findAffineRep S a).2.sort (· ≤ ·)).find?
        (fun y => decide (y ≠ b ∧ y ∈ S.unpaired)) with _ | y'
    · exfalso
      have := find?_sort_eq_none hf y hyT
      simp [hyb, hyunp] at this
    · obtain ⟨hy'T, hy'⟩ := find?_sort_eq_some hf
      simp only [decide_eq_true_eq] at hy'
      obtain ⟨hprep, hgeq, hlt⟩ :=
        Valid.preparation_swap_auxIn_of hS hne hab hGa hGb ha haff hy'T hy'.1 hy'.2
      exact Or.inr ⟨hprep, Or.inr ⟨hgeq, hne, hlt⟩⟩

private theorem refuterStep_pairCreation {S : State n} (hS : S.Valid f) {u : ℕ}
    (hout : S.out.arg = .node u) (hN : NoDeletion S) (hAOP : findAndOnPair S = none)
    (hne : S.gates.Nonempty) (haux : S.auxIn (S.gates.min' hne) = 0)
    (huG : u ≠ S.gates.min' hne) :
    RefuterStep f S (applyStep S (.pairCreation (S.gates.min' hne))) := by
  obtain ⟨hD1, hD2, -, -, hMov⟩ := hN
  set G := S.gates.min' hne with hGdef
  obtain ⟨hG, hmin⟩ := Valid.minGate_reads hS hne
  obtain ⟨t₁, t₂, hl, hr, htne⟩ := exists_args_of_not_degenerate (findD1_eq_none hD1 G hG)
  have hnotaux : t₁ ∉ S.aux ∧ t₂ ∉ S.aux := by
    unfold auxIn at haux
    rw [hl, hr] at haux
    constructor <;> intro hm <;> simp [auxArg, hm] at haux
  have hpar : ∀ t, (S.gate G).Reads t → t ∉ S.aux → t ∈ S.params := fun t ht hta => by
    have hlive := hS.wf.reads_live G hG t ht
    simp only [SemiCircuit.live, Finset.mem_union] at hlive
    rcases hlive with (hp | ha) | hg
    · exact hp
    · exact absurd ha hta
    · exact absurd hg (hmin t ht)
  have ht₁ := hpar t₁ (Or.inl hl) hnotaux.1
  have ht₂ := hpar t₂ (Or.inr hr) hnotaux.2
  have hna : ¬ IsAffineOp (S.gate G).op := fun haff => by
    rcases findMovable_eq_none hMov G hG haff with h | h
    · rw [hl] at h
      simp [isGate, hmin t₁ (Or.inl hl)] at h
    · rw [hr] at h
      simp [isGate, hmin t₂ (Or.inr hr)] at h
  obtain ⟨hu₁, hu₂⟩ := findAndOnPair_eq_none hAOP hG hna hl hr htne ht₁ ht₂
  obtain ⟨K, hK, hKr⟩ : ∃ K ∈ S.gates, (S.gate K).Reads G := by
    rcases findD2_eq_none hD2 G hG with hK | hK
    · exact hK
    · exact absurd (Arg.node.inj (hout.symm.trans hK)) huG
  have hKG : K ≠ G := fun he => hS.not_reads_self hK (he ▸ hKr)
  rcases hf : (S.gates.sort (· ≤ ·)).find? (fun K => decide (K ≠ G ∧ (S.gate K).Reads G)) with
    _ | K'
  · exfalso
    have := find?_sort_eq_none hf K hK
    simp [hKG, hKr] at this
  obtain ⟨hK', hK'r⟩ := find?_sort_eq_some hf
  simp only [decide_eq_true_eq] at hK'r
  simp only [applyStep, hl, hr, hf]
  refine Or.inl ⟨Valid.step_pairCreation_of hS hG htne (Or.inl hl) (Or.inr hr)
    (mem_unpaired.2 ⟨ht₁, hu₁⟩) (mem_unpaired.2 ⟨ht₂, hu₂⟩)
    (fun val => by rw [Gate.eval_of_args hl hr]; exact and_form_spec hna _ _) hK' hK'r.2,
    (deleteConstraint_gates_subset _ _).trans ?_⟩
  rw [deleteGate_gates]
  exact Finset.erase_subset _ _

/-- Every choice of `chooseStep?` is a refuter step. -/
theorem refuterStep_applyStep {S : State n} (hS : S.Valid f) {c : StepChoice}
    (h : chooseStep? S = some c) : RefuterStep f S (applyStep S c) := by
  obtain ⟨u, hout, hu, hc⟩ := chooseStep?_spec h
  cases c with
  | deleteConstantGate J => exact refuterStep_deleteConstantGate hS hc
  | deleteDeadGate J => exact refuterStep_deleteDeadGate hS hc.2
  | deleteShortEqn e => exact refuterStep_deleteShortEqn hS hc.2.2
  | deleteUnitParam x e =>
    obtain ⟨hx, hxout, -, hcx⟩ := findD4_eq_some hc.2.2.2
    exact refuterStep_unitDelete hS hx hxout hcx
  | moveAffine J => exact refuterStep_moveAffine hS hc.2.2.2.2
  | degeneratePair p => exact refuterStep_degeneratePair hS hc.2
  | partnersShareChild p => exact refuterStep_partnersShareChild hS hc.1.2.2.1 hc.2.1 hc.2.2
  | pairInSystem p => exact refuterStep_pairInSystem hS hout hu hc.2.1 hc.2.2.1 hc.2.2.2
  | andOnPair G p => exact refuterStep_andOnPair hS hc.2.1 hc.2.2.1 hc.2.2.2.2
  | swapAuxIn G =>
    obtain ⟨hN, -, -, hPIS, -, hne, rfl, hpos⟩ := hc
    exact refuterStep_swapAuxIn hS hN.1 hPIS hne hpos
  | pairCreation G =>
    obtain ⟨hN, -, -, -, hAOP, hne, rfl, haux, huG⟩ := hc
    exact refuterStep_pairCreation hS hout hN hAOP hne haux huG

/-! ### Main theorems -/

/-- Every step chosen by the refuter lowers `refuterMeasure`, keeps validity, does not increase
`a`, and satisfies `ΔW ≤ 10 Δa`. -/
theorem applyStep_valid {n} {f : BooleanFunction n} {S : State n} (hS : S.Valid f)
    (choice : StepChoice) (hchoice : chooseStep? S = some choice) :
    refuterMeasure (applyStep S choice) < refuterMeasure S ∧
    (applyStep S choice).Valid f ∧
    (applyStep S choice).W + 10 * S.a ≤ S.W + 10 * (applyStep S choice).a ∧
    (applyStep S choice).a ≤ S.a :=
  (refuterStep_applyStep hS hchoice).spec

/-- Running the refuter loop from a valid state with fuel at least `refuterMeasure S` ends in a
terminal valid state, with `ΔW ≤ 10 Δa` and `a` not increased. -/
theorem refuterLoop_valid {n} {f : BooleanFunction n} {S : State n}
    (hS : S.Valid f) (fuel : ℕ) (hfuel : refuterMeasure S ≤ fuel) :
    chooseStep? (refuterLoop S fuel) = none ∧
    (refuterLoop S fuel).Valid f ∧
    (refuterLoop S fuel).W + 10 * S.a ≤ S.W + 10 * (refuterLoop S fuel).a ∧
    (refuterLoop S fuel).a ≤ S.a := by
  induction fuel generalizing S with
  | zero =>
    have hnone : chooseStep? S = none := by
      rcases hc : chooseStep? S with _ | c
      · rfl
      · have := (refuterStep_applyStep hS hc).spec.1
        omega
    exact ⟨hnone, hS, le_rfl, le_rfl⟩
  | succ k ih =>
    rcases hc : chooseStep? S with _ | c
    · simp only [refuterLoop, hc]
      exact ⟨by simp, hS, le_rfl, le_rfl⟩
    · obtain ⟨hlt, hS', hpot, ha⟩ := (refuterStep_applyStep hS hc).spec
      obtain ⟨h1, h2, h3, h4⟩ := ih hS' (by omega)
      simp only [refuterLoop, hc]
      exact ⟨h1, h2, by omega, by omega⟩

/-- The refuter finds an input on which a circuit of size `< 4n - 10d` disagrees with a
`d`-affine disperser. -/
theorem refute_correct {n d : ℕ} (C : Circuit (fullSignature 2 Bool) n 1)
    (f : BitString n → Bool) (hf : IsAffineDisperser f d)
    (hC : C.size + 10 * d < 4 * n) :
    C.eval fullInterpretation (@refute n d C f) 0 ≠ f (@refute n d C f) := by
  have hinit : (initialState C).Valid (fun x => C.eval fullInterpretation x 0) :=
    initialState_valid fun x => by
      ext i
      rw [Fin.eq_zero i]
      rfl
  obtain ⟨hterm, hval, hpot, -⟩ :=
    refuterLoop_valid hinit (refuterMeasure (initialState C)) le_rfl
  have ha : d < (refuterLoop (initialState C) (refuterMeasure (initialState C))).a := by
    have := initialState_a C
    have := initialState_W_le C
    omega
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (findCounterexample_isSome C f hf hval hterm ha
    fun u hu => findAffineRep_spec hval.wf hu)
  have hr : @refute n d C f = x := by
    unfold refute
    simp only [hx]
  rw [hr]
  exact findCounterexample_spec C f _ hx

end Cslib.Circuits.Boolean.AffineDisperser4n
