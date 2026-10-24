/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Fusion.Basic
public import Complexity.Computability.Circuit.Monotone.Set
public import Mathlib.Order.Hom.Bounded

/-!
# Semifilter covers of monotone set constructions

A semifilter is a monotone predicate on sets accepting the full set and rejecting the empty
set. Mathlib's `BoundedOrderHom (Set U) Prop` supplies exactly this structure. Intersection
closure is not required: accepting two sets need not imply accepting their intersection.

For a target set and supplied input sets, witnesses consist of a target point and an admissible
semifilter on the target complement. The semifilter accepts every restricted input containing
the point. A pair cover defeats all such witnesses: each witness accepts both members of some
pair but rejects their intersection. The admissibility predicate supports both unrestricted
semifilters and the complementary-set condition `Semifilter.IsUltra`.

Every native monotone circuit producing the target at a designated output yields a pair cover
whose length is exactly its number of AND gates. Constants and OR gates contribute no pairs;
repeated and unused AND gates remain charged. The circuit may have other outputs. Empty witness
classes admit empty covers, so positive lower bounds require a nontrivial combinatorial argument.
The set interpretation and cover extraction are mathematical constructions, with no claim of
efficient execution on an encoding of arbitrary sets.

## Main definitions

* `Cslib.Circuits.Fusion.Semifilter`, `Cslib.Circuits.Fusion.Semifilter.PreservesPair`: a bounded
  order map from sets to propositions, and preservation of a pair under intersection.
* `Cslib.Circuits.Fusion.Atom.andPair?`: the argument pair of an AND atom restricted along a map.
* `Cslib.Circuits.Fusion.SemifilterWitness`,
  `Cslib.Circuits.Fusion.SemifilterWitness.predicate`: an admissible observation of a target point
  and its reference-to-observation predicate.
* `Cslib.Circuits.Fusion.PairCover`, `Cslib.Circuits.Fusion.PairCover.pad`,
  `Cslib.Circuits.Fusion.PairCover.ofCircuit`,
  `Cslib.Circuits.Fusion.PairCover.ofSourceRefinement`: a list of intersection pairs defeating all
  witnesses, padding, extraction from a circuit, and transport along source refinement.
* `Cslib.Circuits.Fusion.pairCoverComplexity`: the minimum pair count, or infinity.

## Main results

* `Cslib.Circuits.Fusion.PairCover.length_ofCircuit`: extraction preserves the exact AND count.
* `Cslib.Circuits.Fusion.pairCoverComplexity_le_of_sourceRefinement`: pointwise source
  refinement transfers cover lower bounds without changing the pair list.
* `Cslib.Circuits.Fusion.pairCoverComplexity_le_cost`: cover complexity bounds every construction.
* `Cslib.Circuits.Fusion.pairCoverComplexity_le_ecomplexityFrom`: the bound for native source
  complexity.

## References

* Adapted from LowerBound/Fusion/Semifilter.lean in
  [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*][Schlesinger2026Algebraic].
-/

@[expose] public section

namespace Cslib.Circuits.Fusion

universe u v

/-- A nontrivial upward-closed family of sets, written as its membership predicate.
This imposes no intersection-closure condition. -/
abbrev Semifilter (U : Type u) := BoundedOrderHom (Set U) Prop

/-- A semifilter accepts the full set `Set.univ`. -/
@[simp] theorem Semifilter.apply_univ {U : Type u} (F : Semifilter U) : F Set.univ :=
  (map_top F).mpr trivial

/-- A semifilter rejects the empty set `∅`. -/
@[simp] theorem Semifilter.not_apply_empty {U : Type u} (F : Semifilter U) : ¬ F ∅ :=
  (map_bot F).mp

/-- Every set or its complement is accepted. At least one is required; both may be accepted. -/
def Semifilter.IsUltra {U : Type u} (F : Semifilter U) : Prop :=
  ∀ s : Set U, F s ∨ F sᶜ

/-- Accepting both members of this pair implies accepting their intersection. -/
def Semifilter.PreservesPair {U : Type u} (F : Semifilter U) (p : Set U × Set U) : Prop :=
  F p.1 → F p.2 → F (p.1 ∩ p.2)

/-- Restrict the two arguments of an AND atom along a carrier map. Other gates yield no pair. -/
def Atom.andPair? {U : Type u} {V : Type v} (a : Atom Monotone.signature (Set U))
    (f : V → U) : Option (Set V × Set V) :=
  match a with
  | ⟨.and, args⟩ => some (f ⁻¹' args 0, f ⁻¹' args 1)
  | _ => none

/-- Reference membership in one tuple implies observation of the result on another tuple,
provided the observation preserves its AND pair. No subset relation between tuples is needed. -/
theorem Atom.semifilter_of_mem {U : Type u} {V : Type v}
    (a : Atom Monotone.signature (Set U)) (f : V → U) (x : U) (F : Semifilter V)
    (hp : ∀ p, a.andPair? f = some p → F.PreservesPair p)
    (args : Fin (Monotone.signature.Arity a.op) → Set U)
    (hs : ∀ i, x ∈ args i → F (f ⁻¹' a.arguments i)) :
    x ∈ Monotone.setInterpretation U a.op args →
      F (f ⁻¹' Monotone.setInterpretation U a.op a.arguments) := by
  rcases a with ⟨op, values⟩
  cases op with
  | const b =>
    cases b
    · exact fun hx => hx.elim
    · exact fun _ => F.apply_univ
  | and => exact fun hx => hp _ rfl (hs 0 hx.1) (hs 1 hx.2)
  | or =>
    intro hx
    rcases hx with h | h
    · exact F.monotone (fun _ h => Or.inl h) (hs 0 h)
    · exact F.monotone (fun _ h => Or.inr h) (hs 1 h)

/-- A semifilter preserves the reference-to-observation predicate when it preserves the AND pair.
Constants and unions preserve that predicate without any extra assumption. -/
theorem Atom.preserves_semifilter {U : Type u} {V : Type v}
    (a : Atom Monotone.signature (Set U)) (f : V → U) (x : U) (F : Semifilter V)
    (hp : ∀ p, a.andPair? f = some p → F.PreservesPair p) :
    a.Preserves (Monotone.setInterpretation U) (fun s => x ∈ s → F (f ⁻¹' s)) :=
  a.semifilter_of_mem f x F hp a.arguments

/-- A target point and an admissible semifilter accepting the inputs containing that point. -/
structure SemifilterWitness {U : Type u} {n : ℕ} (target : Set U)
    (input : Fin n → Set U) (admissible : Semifilter ↥(targetᶜ) → Prop := fun _ => True) where
  /-- Distinguished target point. -/
  point : target
  /-- Observation of sets outside the target. -/
  filter : Semifilter ↥(targetᶜ)
  /-- The observation belongs to the chosen class. -/
  admissible_filter : admissible filter
  /-- Every supplied set containing the point is accepted after restriction. -/
  above : ∀ i, point.val ∈ input i → filter (Subtype.val ⁻¹' input i)

variable {U : Type u} {n m : ℕ} {target : Set U} {input : Fin n → Set U}

/-- Reference membership implies acceptance by the observation outside the target. -/
def SemifilterWitness.predicate {admissible : Semifilter ↥(targetᶜ) → Prop}
    (w : SemifilterWitness target input admissible) (s : Set U) : Prop :=
  w.point.val ∈ s → w.filter (Subtype.val ⁻¹' s)

/-- The target contains the reference point but has empty restriction to its complement. -/
theorem SemifilterWitness.not_predicate_target {admissible : Semifilter ↥(targetᶜ) → Prop}
    (w : SemifilterWitness target input admissible) :
    ¬ w.predicate target := by
  intro h
  exact w.filter.not_apply_empty
    (w.filter.monotone (fun x hx => (x.property hx).elim) (h w.point.property))

/-- A finite list of pairs defeating every admissible observation of a target point.
Repetitions are retained and charged separately. -/
structure PairCover {U : Type u} {n : ℕ} (target : Set U) (input : Fin n → Set U)
    (admissible : Semifilter ↥(targetᶜ) → Prop := fun _ => True) where
  /-- The intersection pairs, all over the target complement. -/
  pairs : List (Set ↥(targetᶜ) × Set ↥(targetᶜ))
  /-- Every witness fails to preserve some listed pair. -/
  isCover : ∀ w : SemifilterWitness target input admissible,
    ¬ ∀ p ∈ pairs, w.filter.PreservesPair p

/-- Padding by empty pairs preserves a cover. -/
def PairCover.pad {admissible : Semifilter ↥(targetᶜ) → Prop}
    (c : PairCover target input admissible) (t : ℕ) : PairCover target input admissible where
  pairs := c.pairs ++ List.replicate (t - c.pairs.length) (∅, ∅)
  isCover w hp := c.isCover w (fun p hp' => hp p (List.mem_append_left _ hp'))

/-- Padding reaches any requested larger length exactly. -/
theorem PairCover.length_pad {admissible : Semifilter ↥(targetᶜ) → Prop}
    (c : PairCover target input admissible) {t : ℕ} (h : c.pairs.length ≤ t) :
    (c.pad t).pairs.length = t := by
  simp only [PairCover.pad, List.length_append, List.length_replicate]
  lia

/-- Extract the AND pairs from a native circuit producing the target at a chosen output. -/
def PairCover.ofCircuit (c : Circuit Monotone.signature n m) (input : Fin n → Set U)
    (o : Fin m) (hc : c.eval (Monotone.setInterpretation U) input o = target)
    (admissible : Semifilter ↥(targetᶜ) → Prop := fun _ => True) :
    PairCover target input admissible where
  pairs := (List.ofFn (programAtoms c.program (Monotone.setInterpretation U) input)).filterMap
    (fun a => a.andPair? Subtype.val)
  isCover w hp := by
    have hcover := programAtoms_isCover c.program (Monotone.setInterpretation U)
      (fun w : SemifilterWitness target input admissible => w.predicate) input
      (fun w => w.above) (fun w => ⟨c.outputs o, hc ▸ w.not_predicate_target⟩)
    apply hcover w
    intro i
    apply Atom.preserves_semifilter _ Subtype.val w.point.val w.filter
    intro p heq
    apply hp p
    exact List.mem_filterMap.mpr ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, heq⟩

/-- Filtering semantic atoms for AND pairs preserves their total AND weight. -/
theorem length_andPairs {V : Type v} (atoms : List (Atom Monotone.signature (Set U)))
    (f : V → U) :
    (atoms.filterMap fun a => a.andPair? f).length =
      (atoms.map fun a => Monotone.andCost a.op).sum := by
  induction atoms with
  | nil => rfl
  | cons a atoms ih =>
    rcases a with ⟨op, args⟩
    simp only [Atom.andPair?, Monotone.andCost] at ih
    cases op <;> simp [Atom.andPair?, Monotone.andCost, ih, Nat.add_comm]

/-- The extracted pair count is exactly the AND-gate count, including unused gates. -/
@[simp] theorem PairCover.length_ofCircuit (c : Circuit Monotone.signature n m)
    (input : Fin n → Set U) (o : Fin m)
    (hc : c.eval (Monotone.setInterpretation U) input o = target)
    (admissible : Semifilter ↥(targetᶜ) → Prop := fun _ => True) :
    (PairCover.ofCircuit c input o hc admissible).pairs.length =
      c.program.cost Monotone.andCost := by
  rw [PairCover.ofCircuit, length_andPairs, List.map_ofFn, List.sum_ofFn, Program.cost_eq_sum]
  rfl

/-- The minimum pair-cover length, or infinity if no finite cover exists. -/
noncomputable def pairCoverComplexity (target : Set U) (input : Fin n → Set U)
    (admissible : Semifilter ↥(targetᶜ) → Prop := fun _ => True) : ℕ∞ :=
  ⨅ c : PairCover target input admissible, (c.pairs.length : ℕ∞)

/-- Every cover gives an upper bound on minimum pair-cover complexity. -/
theorem pairCoverComplexity_le {admissible : Semifilter ↥(targetᶜ) → Prop}
    (c : PairCover target input admissible) :
    pairCoverComplexity target input admissible ≤ c.pairs.length := iInf_le _ c

/-- A lower bound on cover complexity is exactly a bound for every finite pair cover. -/
theorem le_pairCoverComplexity_iff {admissible : Semifilter ↥(targetᶜ) → Prop} {k : ℕ∞} :
    k ≤ pairCoverComplexity target input admissible ↔
      ∀ c : PairCover target input admissible, k ≤ c.pairs.length := le_iInf_iff

/-- Every finite bound on the cover infimum is attained by a cover within that bound. -/
theorem pairCoverComplexity_le_iff {admissible : Semifilter ↥(targetᶜ) → Prop} {t : ℕ} :
    pairCoverComplexity target input admissible ≤ t ↔
      ∃ c : PairCover target input admissible, c.pairs.length ≤ t := by
  constructor
  · intro h
    have hne := ne_top_of_le_ne_top (ENat.natCast_ne_top t) h
    have : Nonempty (PairCover target input admissible) := ENat.iInf_natCast_ne_top.mp hne
    obtain ⟨c, hc⟩ := ENat.exists_eq_iInf
      (fun c : PairCover target input admissible => (c.pairs.length : ℕ∞))
    exact ⟨c, by exact_mod_cast hc.trans_le h⟩
  · rintro ⟨c, hc⟩
    exact (pairCoverComplexity_le c).trans (by exact_mod_cast hc)

/-- Any lower bound on pair-cover length transfers to the AND count of a constructing circuit. -/
theorem pairCover_lowerBound {admissible : Semifilter ↥(targetᶜ) → Prop} {k : ℕ}
    (hbound : ∀ c : PairCover target input admissible, k ≤ c.pairs.length)
    (c : Circuit Monotone.signature n m) (o : Fin m)
    (hc : c.eval (Monotone.setInterpretation U) input o = target) :
    k ≤ c.program.cost Monotone.andCost := by
  simpa only [PairCover.length_ofCircuit] using hbound (PairCover.ofCircuit c input o hc admissible)

/-- Pair-cover complexity lower-bounds the AND count of every constructing circuit. -/
theorem pairCoverComplexity_le_cost (c : Circuit Monotone.signature n m) (input : Fin n → Set U)
    (o : Fin m) (hc : c.eval (Monotone.setInterpretation U) input o = target)
    (admissible : Semifilter ↥(targetᶜ) → Prop := fun _ => True) :
    pairCoverComplexity target input admissible ≤ c.program.cost Monotone.andCost := by
  simpa only [PairCover.length_ofCircuit] using
    pairCoverComplexity_le (PairCover.ofCircuit c input o hc admissible)

/-- A pair-cover bound at an actual source assignment bounds native supplied-source complexity. -/
theorem pairCoverComplexity_le_ecomplexityFrom {X : Type v} (sources : X → Fin n → Set U)
    (target : X → Fin m → Set U) (x : X) (o : Fin m)
    (admissible : Semifilter ↥((target x o)ᶜ) → Prop := fun _ => True) :
    pairCoverComplexity (target x o) (sources x) admissible ≤
      ecomplexityFrom (Monotone.setInterpretation U) Monotone.andCost target sources :=
  le_ecomplexityFrom_iff.mpr fun c hc =>
    pairCoverComplexity_le_cost c (sources x) o (congrFun (hc x) o) admissible

/-- A cover remains a cover when every accepted source of the old problem contains an accepted
source of the new problem. The pair list and admissibility predicate are unchanged. -/
def PairCover.ofSourceRefinement {U : Type*} {n m : ℕ} {target : Set U}
    {input : Fin n → Set U} {input' : Fin m → Set U}
    {admissible : Semifilter ↥(targetᶜ) → Prop}
    (c : PairCover target input admissible)
    (h : ∀ x ∈ target, ∀ i, x ∈ input i → ∃ j, x ∈ input' j ∧ input' j ⊆ input i) :
    PairCover target input' admissible where
  pairs := c.pairs
  isCover w := c.isCover {
    point := w.point
    filter := w.filter
    admissible_filter := w.admissible_filter
    above := fun i hi => by
      obtain ⟨j, hj, hsub⟩ := h w.point.val w.point.property i hi
      exact w.filter.monotone (fun _ hx => hsub hx) (w.above j hj) }

/-- Pointwise source refinement gives a lower bound on pair-cover complexity. -/
theorem pairCoverComplexity_le_of_sourceRefinement {U : Type*} {n m : ℕ} {target : Set U}
    {input : Fin n → Set U} {input' : Fin m → Set U}
    (admissible : Semifilter ↥(targetᶜ) → Prop)
    (h : ∀ x ∈ target, ∀ i, x ∈ input i → ∃ j, x ∈ input' j ∧ input' j ⊆ input i) :
    pairCoverComplexity target input' admissible ≤ pairCoverComplexity target input admissible :=
  le_iInf fun c => pairCoverComplexity_le (c.ofSourceRefinement h)

end Cslib.Circuits.Fusion
