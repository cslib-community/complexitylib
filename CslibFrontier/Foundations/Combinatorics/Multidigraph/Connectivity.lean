/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.List.Chain
import Mathlib.Data.Fintype.Card

/-!
# Directed paths and arc cuts in multidigraphs

Pure graph-theoretic notions for arc-disjoint Menger's theorem in directed multigraphs
`src tgt : E → V` (matching `Cslib.Multidigraph` in `Arborescence.lean` and `BEST.lean`, where
parallel arcs and self-loops are permitted):

* `Cslib.Multidigraph.IsDipath`: simple directed `s`–`t` paths as lists of arcs `q : List E`
  whose visited vertices `s :: q.map tgt` are duplicate-free.
* `Cslib.Multidigraph.IsArcCut`: an arc set `C : Finset E` meeting every `s`–`t` path.
* `Cslib.Multidigraph.outArcs`: the cut `δ^out(S)` of arcs leaving a vertex set `S`.
* `Cslib.Multidigraph.isArcCut_outArcs` and
  `Cslib.Multidigraph.card_le_card_of_disjoint_of_isArcCut`: cut certificate and weak duality.

## Main definitions

* `Cslib.Multidigraph.IsDipath`, `Cslib.Multidigraph.IsArcCut`, `Cslib.Multidigraph.outArcs`.

## Main results

* `Cslib.Multidigraph.isArcCut_outArcs`: `outArcs src tgt S` is an `s`–`t` arc cut when `s ∈ S`,
  `t ∉ S`.
* `Cslib.Multidigraph.card_le_card_of_disjoint_of_isArcCut`: weak duality for pairwise
  arc-disjoint `s`–`t` paths.

## References

* [K. Menger, *Zur allgemeinen Kurventheorie*][Menger1927]
* [A. Schrijver, *A Course in Combinatorial Optimization*][Schrijver2017], §4.1, Corollary 4.1b
-/

public section

namespace Cslib.Multidigraph

variable {V E : Type*} (src tgt : E → V)

/-- `q` is a simple directed `s`–`t` path of arcs in the multidigraph `src tgt : E → V`: each arc
ends where the next begins, the path starts at `s` and ends at `t`, and the visited vertex list
`s :: q.map tgt` is duplicate-free. -/
@[expose] def IsDipath (s t : V) (q : List E) : Prop :=
  q.IsChain (fun a b => tgt a = src b) ∧
    (s :: q.map tgt).Nodup ∧
    (∀ e ∈ q.head?, src e = s) ∧
    (q = [] → s = t) ∧
    ∀ e ∈ q.getLast?, tgt e = t

instance instDecidableIsDipath [DecidableEq V] (s t : V) (q : List E) :
    Decidable (IsDipath src tgt s t q) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- `C` is an `s`–`t` arc cut in the multidigraph `src tgt`: every simple directed `s`–`t` path
uses an arc of `C`. -/
@[expose] def IsArcCut (s t : V) (C : Finset E) : Prop :=
  ∀ q, IsDipath src tgt s t q → ∃ e ∈ q, e ∈ C

/-- The arcs of the multidigraph `src tgt` leaving a vertex set `S` (`δ^out(S)`). -/
@[expose] def outArcs [Fintype E] [DecidableEq V] (S : Finset V) : Finset E :=
  Finset.univ.filter fun e => src e ∈ S ∧ tgt e ∉ S

theorem mem_outArcs [Fintype E] [DecidableEq V] {S : Finset V} {e : E} :
    e ∈ outArcs src tgt S ↔ src e ∈ S ∧ tgt e ∉ S := by
  simp [outArcs]

private theorem exists_boundary_mem_arcList {S : V → Prop} :
    ∀ {q : List E} {s t : V}, q.IsChain (fun a b => tgt a = src b) →
      (∀ e ∈ q.head?, src e = s) → (q = [] → s = t) → (∀ e ∈ q.getLast?, tgt e = t) →
      S s → ¬ S t → ∃ e ∈ q, S (src e) ∧ ¬ S (tgt e)
  | [], s, t, _, _, hnil, _, hSs, hSt => absurd (hnil rfl ▸ hSs) hSt
  | [e], s, t, _, hhd, _, hlt, hSs, hSt => by
    have hs := hhd e (by simp)
    have ht := hlt e (by simp)
    exact ⟨e, List.mem_cons_self, hs ▸ hSs, ht ▸ hSt⟩
  | e₁ :: e₂ :: rest, s, t, hchain, hhd, _, hlt, hSs, hSt => by
    rw [List.isChain_cons_cons] at hchain
    have hs : src e₁ = s := hhd e₁ (by simp)
    by_cases hy : S (tgt e₁)
    · obtain ⟨e, he, hbd⟩ := exists_boundary_mem_arcList (q := e₂ :: rest) (s := tgt e₁) (t := t)
        hchain.2 (fun e h => (Option.some.inj (List.head?_cons ▸ h)).symm ▸ hchain.1.symm)
        (fun h => by simp at h) (fun x hx => hlt x (by simpa using hx)) hy hSt
      exact ⟨e, List.mem_cons_of_mem e₁ he, hbd⟩
    · exact ⟨e₁, List.mem_cons_self, hs ▸ hSs, hy⟩

/-- `outArcs src tgt S` is an `s`–`t` arc cut whenever `s ∈ S` and `t ∉ S`. -/
theorem isArcCut_outArcs [Fintype E] [DecidableEq V] {s t : V} {S : Finset V}
    (hs : s ∈ S) (ht : t ∉ S) : IsArcCut src tgt s t (outArcs src tgt S) := by
  rintro q ⟨hchain, _, hhd, hnil, hlt⟩
  obtain ⟨e, he, heS, heS'⟩ :=
    exists_boundary_mem_arcList src tgt hchain hhd hnil hlt hs ht
  exact ⟨e, he, (mem_outArcs src tgt).mpr ⟨heS, heS'⟩⟩

/-- **Weak duality for arc-disjoint paths in a multidigraph**: `k` pairwise arc-disjoint simple
`s`–`t` paths require at least `k` arcs in every `s`–`t` arc cut. -/
theorem card_le_card_of_disjoint_of_isArcCut {s t : V} {k : ℕ} {Q : Fin k → List E}
    (hQ : ∀ i, IsDipath src tgt s t (Q i))
    (hdisj : Pairwise fun i j => (Q i).Disjoint (Q j))
    {C : Finset E} (hC : IsArcCut src tgt s t C) : k ≤ C.card := by
  choose e he heC using fun i => hC (Q i) (hQ i)
  have hinj : Function.Injective fun i => (⟨e i, heC i⟩ : C) := by
    intro i j hij
    by_contra hne
    have heq : e i = e j := congrArg Subtype.val hij
    exact hdisj hne (he i) (heq ▸ he j)
  simpa using Fintype.card_le_of_injective _ hinj

end Cslib.Multidigraph
