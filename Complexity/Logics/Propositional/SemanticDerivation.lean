/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.DagProtocol
public import Complexity.Computability.Communication.Operations

/-!
# Feasible interpolation for semantic derivations

A *semantic derivation* [Krajíček, Definition 4.1][Krajicek1997] is a sequence of sets of truth
assignments in which every set is an initial set or contains the intersection of two earlier ones.
Translating each line to its set of models turns a refutation in a sound line-based proof system
whose rules have at most two premises, such as resolution or cutting planes, into a semantic
derivation of `∅` with the same number of lines.

Split the variables into shared variables `X` and private variables `Y` and `Z`, take initial sets
`𝒜` depending only on `X ⊕ Y` and `ℬ` depending only on `X ⊕ Z`, and view them as cylinders on
`X ⊕ (Y ⊕ Z)` (`SemanticDerivation.leftCylinder`, `SemanticDerivation.rightCylinder`). Krajíček's
interpolation theorem [Krajíček, Theorem 5.1][Krajicek1997] says that if a semantic derivation of
`∅` from these cylinders has `k` lines, each of communication complexity at most `t`, then a circuit
with `k · 2 ^ O(t)` gates separates the shared parts of the models of `𝒜` from those of `ℬ`. The
two players, Alice holding a model `(u, q)` of `𝒜` and Bob a model `(v, r)` of `ℬ`, walk backwards
through the derivation along lines falsified by the mixed assignment `(v, q, r)`, starting from `∅`.
Such a walk cannot stop at a derived line, and it cannot reach a `ℬ`-cylinder, which `(v, r)`
satisfies. So it ends at an `𝒜`-cylinder satisfied by `(u, q)` and falsified by `(v, q)`, where
the players find a coordinate `i` with `u i ≠ v i`. This is a dag-like protocol for the
Karchmer–Wigderson game (`Cslib.Communication.DagProtocol`), and such protocols give circuits
(`Cslib.Communication.DagProtocol.Solves.exists_circuit`).

## Main definitions

* `Cslib.Logic.PL.IsSemanticDerivation`, `Cslib.Logic.PL.IsSemanticRefutation`: semantic
  derivations [Krajíček, Definition 4.1][Krajicek1997].
* `Cslib.Logic.PL.SemanticDerivation.commComplexity`,
  `Cslib.Logic.PL.SemanticDerivation.monotoneCommComplexity`: the communication complexity `CC` and
  the monotone communication complexity `MCC_U` of a set of assignments
  [Krajíček, Definition 4.3][Krajicek1997].

## Main results

* `Cslib.Logic.PL.IsSemanticDerivation.mem_of_forall_mem`,
  `Cslib.Logic.PL.IsSemanticRefutation.not_exists_forall_mem`: soundness.
* `Cslib.Logic.PL.IsSemanticRefutation.exists_dagProtocol`: the protocol of the proof, with
  communication `2 t` and one inner node per line, under hypotheses weaker than `CC ≤ t`.
* `Cslib.Logic.PL.IsSemanticRefutation.exists_circuit`,
  `Cslib.Logic.PL.IsSemanticRefutation.exists_monotone_circuit`: the resulting separating circuits.
* `Cslib.Logic.PL.IsSemanticRefutation.exists_circuit_of_commComplexity_le`,
  `Cslib.Logic.PL.IsSemanticRefutation.exists_monotone_circuit_of_monotoneCommComplexity_le`:
  **Krajíček's interpolation theorem for semantic derivations**
  [Krajíček, Theorem 5.1][Krajicek1997]. A refutation with `k` lines of communication complexity
  at most `t` gives a separating circuit with at most `(k · 2 ^ (2 t) + 1) · 2 ^ (2 t + 1)` gates,
  and a monotone one under the monotonicity condition.
* `Cslib.Logic.PL.IsSemanticRefutation.lt_of_forall_lt_size`: the transfer of monotone circuit
  lower bounds to lower bounds on the number of lines.

## Implementation notes

* Lines are sets of assignments `W → Bool`. Besides initial sets and the semantic rule, a line may
  be `Set.univ`, so that axioms of a proof system, such as `x ≥ 0` in cutting planes, can be the
  first line of a derivation; Definition 4.1 has no axioms. A refutation contains `∅` somewhere.
* Alice's and Bob's inputs are a model `(u, q)` of `𝒜` and a model `(v, r)` of `ℬ`; in
  Definition 4.3 these are `(u, q_u)` and `(v, r_v)`. The protocol fixes witnesses `q` for `u` and
  `r` for `v` (`Classical.choice`), so it is non-uniform, like the circuit it yields.
* The protocol is a simplification of the one in the proof of Theorem 5.1. That protocol may stop
  at any line where exactly one of `(u, q, r)` and `(v, q, r)` lies; this one always continues to an
  `𝒜`-cylinder, where `(u, q, r)` lies. So it decides membership of `(v, q, r)` (task 2 of
  Definition 4.3) at every line, finds a coordinate (task 3) only at `𝒜`-cylinders, and never
  decides membership of `(u, q, r)` (task 1). Each node sends at most `2 t` bits, and the main
  theorem `IsSemanticRefutation.exists_dagProtocol` assumes bounds only on these two tasks, which
  is weaker than `CC ≤ t`. In the monotone case the second outcome of task 4, some `u' ≥ u` with
  `(u', q, r)` outside the line, cannot occur at an `𝒜`-cylinder when the models of `𝒜` are
  upward closed, so task 4 too is needed only there.
* The `2 n` nodes of the proof labelled `uᵢ = 1 ∧ vᵢ = 0` or `uᵢ = 0 ∧ vᵢ = 1` are answer leaves of
  the dag-like protocol and are not counted, so the circuit bound counts only the `k` lines. The
  constants are those of `DagProtocol.Solves.exists_circuit` for communication `2 t`.
* Only the monotone case with respect to `U` (the `𝒜` side) is stated; Theorem 5.1 also has the
  dual case with respect to `V`.

## References

* [J. Krajíček, *Interpolation theorems, lower bounds for proof systems, and independence results
  for bounded arithmetic*][Krajicek1997]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Communication Cslib.Circuits

variable {W : Type*} {k : ℕ}

/-- A **semantic derivation** from the initial sets `init` [Krajíček, Definition 4.1][Krajicek1997]:
a sequence of `k` sets of points in which every set is an initial set, the whole space, or contains
the intersection of two earlier sets. -/
def IsSemanticDerivation (init : Set (Set W)) (D : Fin k → Set W) : Prop :=
  ∀ j, D j ∈ init ∨ D j = Set.univ ∨ ∃ i₁ i₂ : Fin k, i₁ < j ∧ i₂ < j ∧ D i₁ ∩ D i₂ ⊆ D j

/-- A **semantic refutation** from the initial sets `init`: a semantic derivation containing the
empty set. Its length `k` is the number of lines. -/
def IsSemanticRefutation (init : Set (Set W)) (D : Fin k → Set W) : Prop :=
  IsSemanticDerivation init D ∧ ∃ j, D j = ∅

/-- **Soundness of semantic derivations.** A point lying in every initial set lies in every line.
-/
theorem IsSemanticDerivation.mem_of_forall_mem {init : Set (Set W)} {D : Fin k → Set W}
    (hD : IsSemanticDerivation init D) {w : W} (hw : ∀ S ∈ init, w ∈ S) (j : Fin k) : w ∈ D j := by
  induction j using WellFoundedLT.induction with
  | _ j ih =>
    rcases hD j with h | h | ⟨i₁, i₂, h₁, h₂, h⟩
    · exact hw _ h
    · rw [h]
      exact Set.mem_univ w
    · exact h ⟨ih i₁ h₁, ih i₂ h₂⟩

/-- A semantic refutation certifies that no point lies in every initial set. -/
theorem IsSemanticRefutation.not_exists_forall_mem {init : Set (Set W)} {D : Fin k → Set W}
    (hD : IsSemanticRefutation init D) : ¬ ∃ w, ∀ S ∈ init, w ∈ S := by
  rintro ⟨w, hw⟩
  obtain ⟨j, hj⟩ := hD.2
  have := hD.1.mem_of_forall_mem hw j
  rw [hj] at this
  exact this

namespace SemanticDerivation

variable {X Y Z : Type*}

/-- The **cylinder** on `X ⊕ (Y ⊕ Z)` over a set of assignments to `X ⊕ Y`: the assignments whose
restriction to `X ⊕ Y` lies in `S`. Krajíček writes `Ã`. -/
def leftCylinder (S : Set (X ⊕ Y → Bool)) : Set (X ⊕ (Y ⊕ Z) → Bool) :=
  (· ∘ Sum.map id Sum.inl) ⁻¹' S

/-- The **cylinder** on `X ⊕ (Y ⊕ Z)` over a set of assignments to `X ⊕ Z`: the assignments whose
restriction to `X ⊕ Z` lies in `S`. Krajíček writes `B̃`. -/
def rightCylinder (S : Set (X ⊕ Z → Bool)) : Set (X ⊕ (Y ⊕ Z) → Bool) :=
  (· ∘ Sum.map id Sum.inr) ⁻¹' S

/-- The initial sets of a semantic refutation of `𝒜 ∪ ℬ`: the cylinders over the sets in `𝒜` and
those over the sets in `ℬ`. -/
def initSets (𝒜 : Set (Set (X ⊕ Y → Bool))) (ℬ : Set (Set (X ⊕ Z → Bool))) :
    Set (Set (X ⊕ (Y ⊕ Z) → Bool)) :=
  leftCylinder '' 𝒜 ∪ rightCylinder '' ℬ

theorem mem_leftCylinder {S : Set (X ⊕ Y → Bool)} {a : X → Bool} {y : Y → Bool}
    {z : Z → Bool} : Sum.elim a (Sum.elim y z) ∈ leftCylinder S ↔ Sum.elim a y ∈ S := by
  have : Sum.elim a (Sum.elim y z) ∘ Sum.map id Sum.inl = Sum.elim a y := by
    funext w
    cases w <;> rfl
  rw [leftCylinder, Set.mem_preimage, this]

theorem mem_rightCylinder {S : Set (X ⊕ Z → Bool)} {a : X → Bool} {y : Y → Bool}
    {z : Z → Bool} : Sum.elim a (Sum.elim y z) ∈ rightCylinder S ↔ Sum.elim a z ∈ S := by
  have : Sum.elim a (Sum.elim y z) ∘ Sum.map id Sum.inr = Sum.elim a z := by
    funext w
    cases w <;> rfl
  rw [rightCylinder, Set.mem_preimage, this]

/-- The **models** of a family of sets of assignments to `X ⊕ Y`, as pairs of assignments to `X`
and to `Y`: those lying in every set of the family. -/
def Models (𝒮 : Set (Set (X ⊕ Y → Bool))) : Set ((X → Bool) × (Y → Bool)) :=
  {p | ∀ S ∈ 𝒮, Sum.elim p.1 p.2 ∈ S}

/-- Alice, holding `a = (u, q)`, and Bob, holding `b = (v, r)`: the assignment `(u, q, r)` lies in
`D`. This is task 1 of [Krajíček, Definition 4.3][Krajicek1997]. -/
def MemLeft (D : Set (X ⊕ (Y ⊕ Z) → Bool)) (a : (X → Bool) × (Y → Bool))
    (b : (X → Bool) × (Z → Bool)) : Prop :=
  Sum.elim a.1 (Sum.elim a.2 b.2) ∈ D

/-- Alice, holding `a = (u, q)`, and Bob, holding `b = (v, r)`: the assignment `(v, q, r)` lies in
`D`. This is task 2 of [Krajíček, Definition 4.3][Krajicek1997]. -/
def MemRight (D : Set (X ⊕ (Y ⊕ Z) → Bool)) (a : (X → Bool) × (Y → Bool))
    (b : (X → Bool) × (Z → Bool)) : Prop :=
  Sum.elim b.1 (Sum.elim a.2 b.2) ∈ D

/-- The relation solved by a protocol whose Boolean output **decides** `P`. -/
def Decides {α β : Type*} (P : α → β → Prop) (a : α) (b : β) (z : Bool) : Prop :=
  z = true ↔ P a b

/-- The **search problem** at an initial set `S` of `𝒜`: if `(u, q)` lies in `S` and `(v, q)` does
not, the answer is a coordinate `i` with `R u v i`, such as `u i ≠ v i` (`DiffersAt`) or
`u i = 1 ∧ v i = 0` (`ExceedsAt`). Answers are optional, and `none` is allowed when the promise
fails. -/
def Search (S : Set (X ⊕ Y → Bool)) (R : (X → Bool) → (X → Bool) → X → Prop)
    (a : (X → Bool) × (Y → Bool)) (b : (X → Bool) × (Z → Bool)) (o : Option X) : Prop :=
  Sum.elim a.1 a.2 ∈ S → Sum.elim b.1 a.2 ∉ S → ∃ i ∈ o, R a.1 b.1 i

section Construction

variable {𝒜 : Set (Set (X ⊕ Y → Bool))} {ℬ : Set (Set (X ⊕ Z → Bool))}
  {D : Fin k → Set (X ⊕ (Y ⊕ Z) → Bool)} {R : (X → Bool) → (X → Bool) → X → Prop} {t : ℕ}
  {mp : Fin k → Protocol ((X → Bool) × (Y → Bool)) ((X → Bool) × (Z → Bool)) Bool}
  {sp : Fin k → Protocol ((X → Bool) × (Y → Bool)) ((X → Bool) × (Z → Bool)) (Option X)}

/-- Alice's witness: an assignment `q` with `(u, q)` a model of `𝒜`, if there is one. -/
private noncomputable def witnessLeft (𝒜 : Set (Set (X ⊕ Y → Bool))) (u : X → Bool) :
    Y → Bool :=
  Classical.epsilon fun q => (u, q) ∈ Models 𝒜

private theorem witnessLeft_mem {u : X → Bool} (h : ∃ q, (u, q) ∈ Models 𝒜) :
    (u, witnessLeft 𝒜 u) ∈ Models 𝒜 :=
  Classical.epsilon_spec h

/-- Bob's witness: an assignment `r` with `(v, r)` a model of `ℬ`, if there is one. -/
private noncomputable def witnessRight (ℬ : Set (Set (X ⊕ Z → Bool))) (v : X → Bool) :
    Z → Bool :=
  Classical.epsilon fun r => (v, r) ∈ Models ℬ

private theorem witnessRight_mem {v : X → Bool} (h : ∃ r, (v, r) ∈ Models ℬ) :
    (v, witnessRight ℬ v) ∈ Models ℬ :=
  Classical.epsilon_spec h

open Classical in
/-- The tree protocol at line `j`, on models `(u, q)` of `𝒜` and `(v, r)` of `ℬ`. The players
decide whether `(v, q, r)` lies in `D j` with `mp j`, and answer `none` if it does. Otherwise, at a
derived line they decide whether `(v, q, r)` lies in the first premise and move to a premise that
does not contain it; at an `𝒜`-cylinder they find a coordinate with `sp j`; at any other line they
answer `none`. -/
private noncomputable def nodeStep (𝒜 : Set (Set (X ⊕ Y → Bool)))
    (D : Fin k → Set (X ⊕ (Y ⊕ Z) → Bool))
    (mp : Fin k → Protocol ((X → Bool) × (Y → Bool)) ((X → Bool) × (Z → Bool)) Bool)
    (sp : Fin k → Protocol ((X → Bool) × (Y → Bool)) ((X → Bool) × (Z → Bool)) (Option X))
    (j : Fin k) :
    Protocol ((X → Bool) × (Y → Bool)) ((X → Bool) × (Z → Bool)) (Option (Fin j ⊕ X)) :=
  if h : ∃ i₁ i₂ : Fin k, i₁ < j ∧ i₂ < j ∧ D i₁ ∩ D i₂ ⊆ D j then
    (mp j).bind fun b => bif b then .output none else
      (mp h.choose).bind fun b' => .output (some (.inl (bif b'
        then ⟨h.choose_spec.choose, h.choose_spec.choose_spec.2.1⟩
        else ⟨h.choose, h.choose_spec.choose_spec.1⟩)))
  else if ∃ S ∈ 𝒜, leftCylinder S = D j then
    (mp j).bind fun b => bif b then .output none else (sp j).map (Option.map .inr)
  else .output none

/-- On models of `𝒜` and `ℬ`, the tree protocol at line `j` answers `none` exactly when `(v, q, r)`
lies in `D j`, and otherwise names an earlier line not containing `(v, q, r)` or a coordinate
related by `R`. -/
private theorem nodeStep_spec (hD : IsSemanticDerivation (initSets 𝒜 ℬ) D)
    (hmp : ∀ j, (mp j).Solves (Decides (MemRight (D j))) (Models 𝒜) (Models ℬ))
    (hsp : ∀ j, (∃ S ∈ 𝒜, leftCylinder S = D j) →
      ∃ S ∈ 𝒜, leftCylinder S = D j ∧ (sp j).Solves (Search S R) (Models 𝒜) (Models ℬ))
    {a : (X → Bool) × (Y → Bool)} {b : (X → Bool) × (Z → Bool)} (ha : a ∈ Models 𝒜)
    (hb : b ∈ Models ℬ) (j : Fin k) :
    ((nodeStep 𝒜 D mp sp j).run a b = none ↔ MemRight (D j) a b) ∧
      ∀ s, (nodeStep 𝒜 D mp sp j).run a b = some s →
        s.elim (fun i => ¬ MemRight (D (Fin.castLE j.isLt.le i)) a b) (R a.1 b.1) := by
  have hm : ∀ i, (mp i).run a b = true ↔ MemRight (D i) a b := fun i => hmp i a ha b hb
  unfold nodeStep
  split_ifs with h hA
  · obtain ⟨h₁, h₂, hsub⟩ := h.choose_spec.choose_spec
    simp only [Protocol.run_bind]
    cases hj : (mp j).run a b
    · have hnj : ¬ MemRight (D j) a b := by rw [← hm, hj]; exact Bool.false_ne_true
      simp only [Bool.cond_false, Protocol.run_bind, Protocol.run_output, reduceCtorEq, hnj,
        true_and, Option.some.injEq]
      rintro s rfl
      cases hi : (mp h.choose).run a b
      · simp only [Bool.cond_false, Sum.elim_inl, Fin.castLE_mk, Fin.eta]
        rw [← hm, hi]
        exact Bool.false_ne_true
      · simp only [Bool.cond_true, Sum.elim_inl, Fin.castLE_mk, Fin.eta]
        exact fun h' => hnj (hsub ⟨(hm _).1 hi, h'⟩)
    · simp only [Bool.cond_true, Protocol.run_output, (hm j).1 hj, reduceCtorEq, false_imp_iff,
        implies_true, and_self]
  · obtain ⟨S, hS, hSD, hsol⟩ := hsp j hA
    simp only [Protocol.run_bind]
    cases hj : (mp j).run a b
    · have hnj : ¬ MemRight (D j) a b := by rw [← hm, hj]; exact Bool.false_ne_true
      have hnS : Sum.elim b.1 a.2 ∉ S := by
        rwa [MemRight, ← hSD, mem_leftCylinder] at hnj
      obtain ⟨i, hi, hR⟩ := hsol a ha b hb (ha S hS) hnS
      rw [Option.mem_def] at hi
      simp only [Bool.cond_false, Protocol.run_map, hi, Option.map_some, reduceCtorEq, hnj,
        Option.some.injEq, true_and]
      rintro s rfl
      exact hR
    · simp only [Bool.cond_true, Protocol.run_output, (hm j).1 hj, reduceCtorEq, false_imp_iff,
        implies_true, and_self]
  · have hmem : MemRight (D j) a b := by
      rcases hD j with (⟨S, hS, hSD⟩ | ⟨S, hS, hSD⟩) | huniv | hder
      · exact absurd ⟨S, hS, hSD⟩ hA
      · rw [MemRight, ← hSD, mem_rightCylinder]
        exact hb S hS
      · rw [MemRight, huniv]
        exact Set.mem_univ _
      · exact absurd hder h
    simp only [Protocol.run_output, hmem, reduceCtorEq, false_imp_iff, implies_true, and_self]

/-- The dag-like protocol of the proof of [Krajíček, Theorem 5.1][Krajicek1997]: one inner node
per line, the source at the line `D j₀ = ∅`, and the tree protocols `nodeStep` run on the inputs
completed by the witnesses. -/
private noncomputable def semanticProtocol (𝒜 : Set (Set (X ⊕ Y → Bool)))
    (ℬ : Set (Set (X ⊕ Z → Bool))) (D : Fin k → Set (X ⊕ (Y ⊕ Z) → Bool))
    (mp : Fin k → Protocol ((X → Bool) × (Y → Bool)) ((X → Bool) × (Z → Bool)) Bool)
    (sp : Fin k → Protocol ((X → Bool) × (Y → Bool)) ((X → Bool) × (Z → Bool)) (Option X))
    (j₀ : Fin k) : DagProtocol (X → Bool) (X → Bool) X k where
  step j := (nodeStep 𝒜 D mp sp j).comap (fun u => (u, witnessLeft 𝒜 u))
    (fun v => (v, witnessRight ℬ v))
  root := .inl j₀

private theorem semanticProtocol_solves {j₀ : Fin k}
    (hD : IsSemanticDerivation (initSets 𝒜 ℬ) D) (hj₀ : D j₀ = ∅)
    (hmp : ∀ j, (mp j).Solves (Decides (MemRight (D j))) (Models 𝒜) (Models ℬ))
    (hsp : ∀ j, (∃ S ∈ 𝒜, leftCylinder S = D j) →
      ∃ S ∈ 𝒜, leftCylinder S = D j ∧ (sp j).Solves (Search S R) (Models 𝒜) (Models ℬ)) :
    (semanticProtocol 𝒜 ℬ D mp sp j₀).Solves R {u | ∃ q, (u, q) ∈ Models 𝒜}
      {v | ∃ r, (v, r) ∈ Models ℬ} := by
  have hspec := fun u (hu : ∃ q, (u, q) ∈ Models 𝒜) v (hv : ∃ r, (v, r) ∈ Models ℬ) =>
    nodeStep_spec (R := R) hD hmp hsp (witnessLeft_mem hu) (witnessRight_mem hv)
  refine ⟨fun u hu v hv => ?_, fun j u hu v hv s hs => ?_⟩
  · simp only [semanticProtocol, DagProtocol.consistent_inl, Protocol.run_comap, ne_eq,
      (hspec u hu v hv j₀).1, MemRight, hj₀, Set.mem_empty_iff_false, not_false_eq_true]
  · simp only [semanticProtocol, Protocol.run_comap] at hs
    have := (hspec u hu v hv j).2 s hs
    rcases s with i | x
    · simp only [semanticProtocol, DagProtocol.node_inl, DagProtocol.consistent_inl,
        Protocol.run_comap, ne_eq, (hspec u hu v hv _).1]
      exact this
    · exact this

private theorem depth_semanticProtocol_le {j₀ : Fin k} (hmp : ∀ j, (mp j).depth ≤ t)
    (hsp : ∀ j, (sp j).depth ≤ t) : (semanticProtocol 𝒜 ℬ D mp sp j₀).depth ≤ 2 * t := by
  refine Finset.sup_le fun j _ => ?_
  simp only [semanticProtocol, Protocol.depth_comap]
  unfold nodeStep
  split_ifs
  · refine (Protocol.depth_bind_le (d := t) fun b => ?_).trans (by have := hmp j; omega)
    cases b
    · exact (Protocol.depth_bind_le (d := 0) fun _ => le_rfl).trans (by simpa using hmp _)
    · simp
  · refine (Protocol.depth_bind_le (d := t) fun b => ?_).trans (by have := hmp j; omega)
    cases b
    · simpa using hsp j
    · simp
  · simp

end Construction

end SemanticDerivation

open SemanticDerivation

variable {X Y Z : Type*} {𝒜 : Set (Set (X ⊕ Y → Bool))} {ℬ : Set (Set (X ⊕ Z → Bool))}
  {D : Fin k → Set (X ⊕ (Y ⊕ Z) → Bool)} {t : ℕ}

/-- **The protocol of Krajíček's interpolation theorem** [Krajíček, Theorem 5.1][Krajicek1997].
Let `D` be a semantic refutation with `k` lines of the cylinders over `𝒜` and `ℬ`. Suppose that on
models `(u, q)` of `𝒜` and `(v, r)` of `ℬ`, deciding whether `(v, q, r)` lies in a line takes at
most `t` bits, and at every line that is the cylinder over some `S ∈ 𝒜`, finding a coordinate `i`
with `R u v i` when `(u, q) ∈ S` and `(v, q) ∉ S` takes at most `t` bits. Then a dag-like protocol
with `k` inner nodes and communication at most `2 t` solves `R` on the shared parts of the models.
-/
theorem IsSemanticRefutation.exists_dagProtocol {R : (X → Bool) → (X → Bool) → X → Prop}
    (hD : IsSemanticRefutation (initSets 𝒜 ℬ) D)
    (hmem : ∀ j, Protocol.ecomplexity (Decides (MemRight (D j))) (Models 𝒜) (Models ℬ) ≤ t)
    (hsearch : ∀ j, ∀ S ∈ 𝒜, leftCylinder S = D j →
      Protocol.ecomplexity (Search S R) (Models 𝒜) (Models ℬ) ≤ t) :
    ∃ P : DagProtocol (X → Bool) (X → Bool) X k, P.depth ≤ 2 * t ∧
      P.Solves R {u | ∃ q, (u, q) ∈ Models 𝒜} {v | ∃ r, (v, r) ∈ Models ℬ} := by
  obtain ⟨hder, j₀, hj₀⟩ := hD
  choose mp hmp hmpd using fun j => Protocol.ecomplexity_le_iff.1 (hmem j)
  have : ∀ j, ∃ p : Protocol ((X → Bool) × (Y → Bool)) ((X → Bool) × (Z → Bool)) (Option X),
      p.depth ≤ t ∧ ((∃ S ∈ 𝒜, leftCylinder S = D j) →
        ∃ S ∈ 𝒜, leftCylinder S = D j ∧ p.Solves (Search S R) (Models 𝒜) (Models ℬ)) := by
    intro j
    by_cases hA : ∃ S ∈ 𝒜, leftCylinder S = D j
    · obtain ⟨S, hS, hSD⟩ := hA
      obtain ⟨p, hp, hd⟩ := Protocol.ecomplexity_le_iff.1 (hsearch j S hS hSD)
      exact ⟨p, hd, fun _ => ⟨S, hS, hSD, hp⟩⟩
    · exact ⟨.output none, by simp, fun h => absurd h hA⟩
  choose sp hspd hsp using this
  exact ⟨semanticProtocol 𝒜 ℬ D mp sp j₀, depth_semanticProtocol_le hmpd hspd,
    semanticProtocol_solves hder hj₀ hmp hsp⟩

/-- `(k · 2 ^ d + 1) · 2 ^ (d + 1)` is monotone in `d`. -/
private theorem size_bound_mono {d e : ℕ} (h : d ≤ e) :
    (k * 2 ^ d + 1) * 2 ^ (d + 1) ≤ (k * 2 ^ e + 1) * 2 ^ (e + 1) := by
  have h₁ : 2 ^ d ≤ 2 ^ e := Nat.pow_le_pow_right Nat.two_pos h
  have h₂ : 2 ^ (d + 1) ≤ 2 ^ (e + 1) := Nat.pow_le_pow_right Nat.two_pos (by omega)
  exact Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left k h₁) 1) h₂

/-- **Interpolation for semantic refutations.** Under the hypotheses of
`IsSemanticRefutation.exists_dagProtocol` for `DiffersAt`, a circuit with at most
`(k · 2 ^ (2 t) + 1) · 2 ^ (2 t + 1)` gates is true on the shared part of every model of `𝒜` and
false on the shared part of every model of `ℬ`. -/
theorem IsSemanticRefutation.exists_circuit {n : ℕ} {𝒜 : Set (Set (Fin n ⊕ Y → Bool))}
    {ℬ : Set (Set (Fin n ⊕ Z → Bool))} {D : Fin k → Set (Fin n ⊕ (Y ⊕ Z) → Bool)}
    (hD : IsSemanticRefutation (initSets 𝒜 ℬ) D)
    (hmem : ∀ j, Protocol.ecomplexity (Decides (MemRight (D j))) (Models 𝒜) (Models ℬ) ≤ t)
    (hsearch : ∀ j, ∀ S ∈ 𝒜, leftCylinder S = D j →
      Protocol.ecomplexity (Search S DiffersAt) (Models 𝒜) (Models ℬ) ≤ t) :
    ∃ C : Circuit Boolean.signature n 1,
      C.size ≤ (k * 2 ^ (2 * t) + 1) * 2 ^ (2 * t + 1) ∧
      (∀ u q, (u, q) ∈ Models 𝒜 → C.eval Boolean.interpretation u 0 = true) ∧
      ∀ v r, (v, r) ∈ Models ℬ → C.eval Boolean.interpretation v 0 = false := by
  obtain ⟨P, hd, hP⟩ := hD.exists_dagProtocol hmem hsearch
  obtain ⟨C, hsize, hU, hV⟩ := hP.exists_circuit
  exact ⟨C, hsize.trans (size_bound_mono hd), fun u q h => hU u ⟨q, h⟩,
    fun v r h => hV v ⟨r, h⟩⟩

/-- **Monotone interpolation for semantic refutations.** Under the hypotheses of
`IsSemanticRefutation.exists_dagProtocol` for `ExceedsAt`, a monotone circuit with at most
`(k · 2 ^ (2 t) + 1) · 2 ^ (2 t + 1)` gates is true on the shared part of every model of `𝒜` and
false on the shared part of every model of `ℬ`. -/
theorem IsSemanticRefutation.exists_monotone_circuit {n : ℕ} {𝒜 : Set (Set (Fin n ⊕ Y → Bool))}
    {ℬ : Set (Set (Fin n ⊕ Z → Bool))} {D : Fin k → Set (Fin n ⊕ (Y ⊕ Z) → Bool)}
    (hD : IsSemanticRefutation (initSets 𝒜 ℬ) D)
    (hmem : ∀ j, Protocol.ecomplexity (Decides (MemRight (D j))) (Models 𝒜) (Models ℬ) ≤ t)
    (hsearch : ∀ j, ∀ S ∈ 𝒜, leftCylinder S = D j →
      Protocol.ecomplexity (Search S ExceedsAt) (Models 𝒜) (Models ℬ) ≤ t) :
    ∃ C : Circuit Monotone.signature n 1,
      C.size ≤ (k * 2 ^ (2 * t) + 1) * 2 ^ (2 * t + 1) ∧
      (∀ u q, (u, q) ∈ Models 𝒜 → C.eval Monotone.interpretation u 0 = true) ∧
      ∀ v r, (v, r) ∈ Models ℬ → C.eval Monotone.interpretation v 0 = false := by
  obtain ⟨P, hd, hP⟩ := hD.exists_dagProtocol hmem hsearch
  obtain ⟨C, hsize, hU, hV⟩ := hP.exists_monotone_circuit
  exact ⟨C, hsize.trans (size_bound_mono hd), fun u q h => hU u ⟨q, h⟩,
    fun v r h => hV v ⟨r, h⟩⟩

/-- **Lower bounds on the number of lines from monotone circuit lower bounds.** If every monotone
circuit that is true on the shared parts of the models of `𝒜` and false on those of `ℬ` has more
than `L` gates, then a semantic refutation with `k` lines satisfying the hypotheses of
`IsSemanticRefutation.exists_monotone_circuit` has `L < (k · 2 ^ (2 t) + 1) · 2 ^ (2 t + 1)`. -/
theorem IsSemanticRefutation.lt_of_forall_lt_size {n L : ℕ} {𝒜 : Set (Set (Fin n ⊕ Y → Bool))}
    {ℬ : Set (Set (Fin n ⊕ Z → Bool))} {D : Fin k → Set (Fin n ⊕ (Y ⊕ Z) → Bool)}
    (hD : IsSemanticRefutation (initSets 𝒜 ℬ) D)
    (hmem : ∀ j, Protocol.ecomplexity (Decides (MemRight (D j))) (Models 𝒜) (Models ℬ) ≤ t)
    (hsearch : ∀ j, ∀ S ∈ 𝒜, leftCylinder S = D j →
      Protocol.ecomplexity (Search S ExceedsAt) (Models 𝒜) (Models ℬ) ≤ t)
    (hL : ∀ C : Circuit Monotone.signature n 1,
      (∀ u q, (u, q) ∈ Models 𝒜 → C.eval Monotone.interpretation u 0 = true) →
      (∀ v r, (v, r) ∈ Models ℬ → C.eval Monotone.interpretation v 0 = false) → L < C.size) :
    L < (k * 2 ^ (2 * t) + 1) * 2 ^ (2 * t + 1) := by
  obtain ⟨C, hsize, hU, hV⟩ := hD.exists_monotone_circuit hmem hsearch
  exact (hL C hU hV).trans_le hsize

/-! ### Krajíček's communication complexity of a set of assignments -/

namespace SemanticDerivation

/-- The **communication complexity** `CC(D)` of a set of assignments to `X ⊕ (Y ⊕ Z)`
[Krajíček, Definition 4.3][Krajicek1997]: the largest number of bits that Alice, holding
`(u, q)`, and Bob, holding `(v, r)`, need in the worst case to decide whether `(u, q, r) ∈ D`
(task 1), to decide whether `(v, q, r) ∈ D` (task 2), and to find `i` with `u i ≠ v i` when exactly
one of them lies in `D` (task 3). -/
noncomputable def commComplexity (D : Set (X ⊕ (Y ⊕ Z) → Bool)) : ℕ∞ :=
  max (max (Protocol.ecomplexity (Decides (MemLeft D)) Set.univ Set.univ)
    (Protocol.ecomplexity (Decides (MemRight D)) Set.univ Set.univ))
    (Protocol.ecomplexity (fun (a : (X → Bool) × (Y → Bool)) (b : (X → Bool) × (Z → Bool))
        (i : X) => ¬ (MemLeft D a b ↔ MemRight D a b) → a.1 i ≠ b.1 i) Set.univ Set.univ)

/-- The **monotone communication complexity** `MCC_U(D)` of a set of assignments
[Krajíček, Definition 4.3][Krajicek1997]: the larger of `CC(D)` and the number of bits needed,
when `(u, q, r) ∈ D` and `(v, q, r) ∉ D`, to either find `i` with `u i = 1` and `v i = 0` (answer
`some i`) or learn that `(u', q, r) ∉ D` for some `u' ≥ u` (answer `none`) (task 4). -/
noncomputable def monotoneCommComplexity (D : Set (X ⊕ (Y ⊕ Z) → Bool)) : ℕ∞ :=
  max (commComplexity D)
    (Protocol.ecomplexity (fun (a : (X → Bool) × (Y → Bool)) (b : (X → Bool) × (Z → Bool))
        (o : Option X) => MemLeft D a b → ¬ MemRight D a b →
      o.elim (∃ u', a.1 ≤ u' ∧ ¬ MemLeft D (u', a.2) b) fun i => a.1 i = true ∧ b.1 i = false)
      Set.univ Set.univ)

theorem ecomplexity_memRight_le_commComplexity (D : Set (X ⊕ (Y ⊕ Z) → Bool)) :
    Protocol.ecomplexity (Decides (MemRight D)) Set.univ Set.univ ≤ commComplexity D :=
  (le_max_right _ _).trans (le_max_left _ _)

theorem commComplexity_le_monotoneCommComplexity (D : Set (X ⊕ (Y ⊕ Z) → Bool)) :
    commComplexity D ≤ monotoneCommComplexity D :=
  le_max_left _ _

end SemanticDerivation

/-- **Krajíček's interpolation theorem for semantic derivations**
[Krajíček, Theorem 5.1][Krajicek1997]. If a semantic refutation of the cylinders over `𝒜` and `ℬ`
has `k` lines, each of communication complexity at most `t`, then a circuit with at most
`(k · 2 ^ (2 t) + 1) · 2 ^ (2 t + 1)` gates is true on the shared part of every model of `𝒜` and
false on the shared part of every model of `ℬ`. -/
theorem IsSemanticRefutation.exists_circuit_of_commComplexity_le {n : ℕ}
    {𝒜 : Set (Set (Fin n ⊕ Y → Bool))} {ℬ : Set (Set (Fin n ⊕ Z → Bool))}
    {D : Fin k → Set (Fin n ⊕ (Y ⊕ Z) → Bool)} (hD : IsSemanticRefutation (initSets 𝒜 ℬ) D)
    (hcc : ∀ j, commComplexity (D j) ≤ t) :
    ∃ C : Circuit Boolean.signature n 1,
      C.size ≤ (k * 2 ^ (2 * t) + 1) * 2 ^ (2 * t + 1) ∧
      (∀ u q, (u, q) ∈ Models 𝒜 → C.eval Boolean.interpretation u 0 = true) ∧
      ∀ v r, (v, r) ∈ Models ℬ → C.eval Boolean.interpretation v 0 = false := by
  refine hD.exists_circuit (fun j => ?_) fun j S hS hSD => ?_
  · exact (Protocol.ecomplexity_mono (Set.subset_univ _) (Set.subset_univ _)).trans
      ((ecomplexity_memRight_le_commComplexity _).trans (hcc j))
  · obtain ⟨p, hp, hd⟩ := Protocol.ecomplexity_le_iff.1
      (((le_max_right _ _).trans (hcc j) :) :)
    have hs : (p.map some).Solves (Search S DiffersAt) (Models 𝒜) (Models ℬ) := by
      intro a _ b _ h₁ h₂
      refine ⟨p.run a b, by simp, hp a trivial b trivial fun h => ?_⟩
      rw [MemLeft, MemRight, ← hSD, mem_leftCylinder, mem_leftCylinder] at h
      exact h₂ (h.1 h₁)
    exact (Protocol.ecomplexity_le_depth hs).trans (by simpa using hd)

/-- **Krajíček's monotone interpolation theorem for semantic derivations**
[Krajíček, Theorem 5.1][Krajicek1997]. Suppose that the models of `𝒜` are upward closed in the
shared variables: if `(u, q)` is a model and `u ≤ u'`, then so is `(u', q)`. If a semantic
refutation of the cylinders over `𝒜` and `ℬ` has `k` lines, each of monotone communication
complexity `MCC_U` at most `t`, then a monotone circuit with at most
`(k · 2 ^ (2 t) + 1) · 2 ^ (2 t + 1)` gates is true on the shared part of every model of `𝒜` and
false on the shared part of every model of `ℬ`. -/
theorem IsSemanticRefutation.exists_monotone_circuit_of_monotoneCommComplexity_le {n : ℕ}
    {𝒜 : Set (Set (Fin n ⊕ Y → Bool))} {ℬ : Set (Set (Fin n ⊕ Z → Bool))}
    {D : Fin k → Set (Fin n ⊕ (Y ⊕ Z) → Bool)} (hD : IsSemanticRefutation (initSets 𝒜 ℬ) D)
    (hmono : ∀ u u' q, (u, q) ∈ Models 𝒜 → u ≤ u' → (u', q) ∈ Models 𝒜)
    (hmcc : ∀ j, monotoneCommComplexity (D j) ≤ t) :
    ∃ C : Circuit Monotone.signature n 1,
      C.size ≤ (k * 2 ^ (2 * t) + 1) * 2 ^ (2 * t + 1) ∧
      (∀ u q, (u, q) ∈ Models 𝒜 → C.eval Monotone.interpretation u 0 = true) ∧
      ∀ v r, (v, r) ∈ Models ℬ → C.eval Monotone.interpretation v 0 = false := by
  refine hD.exists_monotone_circuit (fun j => ?_) fun j S hS hSD => ?_
  · exact (Protocol.ecomplexity_mono (Set.subset_univ _) (Set.subset_univ _)).trans
      ((ecomplexity_memRight_le_commComplexity _).trans
        ((commComplexity_le_monotoneCommComplexity _).trans (hmcc j)))
  · obtain ⟨p, hp, hd⟩ := Protocol.ecomplexity_le_iff.1 (((le_max_right _ _).trans (hmcc j) :) :)
    refine (Protocol.ecomplexity_le_depth (p := p) ?_).trans (by exact_mod_cast hd)
    intro a ha b _ h₁ h₂
    have hl : MemLeft (D j) a b := by rw [MemLeft, ← hSD, mem_leftCylinder]; exact h₁
    have hr : ¬ MemRight (D j) a b := by rw [MemRight, ← hSD, mem_leftCylinder]; exact h₂
    have := hp a trivial b trivial hl hr
    cases ho : p.run a b with
    | none =>
      rw [ho] at this
      obtain ⟨u', hu', hn⟩ := this
      refine absurd ?_ hn
      rw [MemLeft, ← hSD, mem_leftCylinder]
      exact hmono a.1 u' a.2 ha hu' S hS
    | some i =>
      rw [ho] at this
      exact ⟨i, rfl, this⟩

end Cslib.Logic.PL
