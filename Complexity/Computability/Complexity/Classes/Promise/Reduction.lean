/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Promise.Basic
public import Complexity.Computability.Complexity.Problems.SAT
public import Complexity.Computability.Complexity.Reduction
public import Mathlib.Basic.Real.Basic
import Complexity.Computability.Complexity.Classes.NP.Witness
import Complexity.Computability.Complexity.CookLevin.Completeness

/-!
# Deterministic reductions of promise problems and gap problems

Hardness of approximation is stated through **gap problems** [Arora and Barak, Chapter
11][AroraBarak09]. For a maximization objective `val`, the gap problem `gapMax val c s` is the
promise problem whose yes-instances have value at least `c` and whose no-instances have value at
most `s`, below `c`. When this gap problem is NP-hard, the maximization problem is **NP-hard to
approximate** within every ratio better than `s / c`: an algorithm estimating `val` from below
within such a ratio would tell the two kinds of instances apart.

Reductions between promise problems are the polynomial-time many-one reductions of
`Cslib.Complexity.PolyTimeReducible`, required to map yes-instances to yes-instances and
no-instances to no-instances; on decision problems they are exactly those reductions
(`PromiseProblem.polyTimeReducible_ofSet_iff`). Between gap problems they are the
**gap-preserving reductions** used to transfer inapproximability from one problem to another.
A promise problem is NP-hard when every problem in `NP` reduces to it; for decision problems this
is `Cslib.Complexity.NPHard` (`PromiseProblem.npHard_ofSet_iff`). An NP-hard promise problem solved
in polynomial time gives `P = NP` (`PromiseProblem.NPHard.P_eq_NP_of_mem_PromiseP`).

Reductions of promise problems are Karp reductions in the sense of Goldreich's survey
[Goldreich2006]: one function serves for every instance in the promise. This is stronger than
asking every problem separating the yes-instances from the no-instances to be NP-hard, which
`PromiseProblem.NPHard.npHard_of_subset` derives.

Probabilistic promise classes are defined with their decision specializations: `PromiseBPP` in
`Complexity.Computability.Complexity.Classes.BPP`, and `PromiseRP` and `PromiseCoRP` in
`Complexity.Computability.Complexity.Classes.RP`. Their PPT characterizations live in
`Complexity.Computability.Complexity.Classes.Promise.Probabilistic`, and randomized one-sided
reductions (`RPReducible`, `RPReducibleWithError`) live in
`Complexity.Computability.Complexity.Classes.Promise.Randomized`.

## Main definitions

* `Cslib.Complexity.PromiseProblem.PolyTimeReducible`: polynomial-time reductions of promise
  problems, which between gap problems are the gap-preserving reductions.
* `Cslib.Complexity.PromiseProblem.NPHard`: every problem in `NP` reduces to the promise problem.
* `Cslib.Complexity.PromiseProblem.gapMax`, `Cslib.Complexity.PromiseProblem.gapMin`: the gap
  problems of a maximization and of a minimization objective.
* `Cslib.Complexity.PromiseProblem.restrict`: a promise problem restricted to a set of instances.

## Main results

* `Cslib.Complexity.PromiseProblem.polyTimeReducible_ofSet_iff`,
  `Cslib.Complexity.PromiseProblem.npHard_ofSet_iff`: on decision problems, the notions are
  `Cslib.Complexity.PolyTimeReducible` and `Cslib.Complexity.NPHard`.
* `Cslib.Complexity.PromiseProblem.PolyTimeReducible.refl`,
  `Cslib.Complexity.PromiseProblem.PolyTimeReducible.trans`,
  `Cslib.Complexity.PromiseProblem.PolyTimeReducible.of_subset`,
  `Cslib.Complexity.PromiseProblem.NPHard.trans`,
  `Cslib.Complexity.PromiseProblem.NPHard.mono`: reflexivity, composition and monotonicity of
  promise reductions and NP-hardness.
* `Cslib.Complexity.PromiseProblem.PolyTimeReducible.mem_PromiseP`,
  `Cslib.Complexity.PromiseProblem.PolyTimeReducible.mem_PromiseNP`,
  `Cslib.Complexity.PromiseProblem.PolyTimeReducible.exists_polyTimeReducible`: closure of
  `PromiseP` and `PromiseNP` under deterministic reductions.
* `Cslib.Complexity.PromiseProblem.npHard_of_polyTimeReducible_SAT`: a reduction from `SAT`
  proves NP-hardness, by the Cook–Levin theorem.
* `Cslib.Complexity.PromiseProblem.NPHard.npHard_of_subset`,
  `Cslib.Complexity.PromiseProblem.NPHard.NP_subset_P_of_mem_PromiseP`,
  `Cslib.Complexity.PromiseProblem.NPHard.P_eq_NP_of_mem_PromiseP`,
  `Cslib.Complexity.PromiseProblem.NPHard.notMem_PromiseP`: consequences of NP-hardness for
  separating languages and `P` vs `NP`.
* `Cslib.Complexity.PromiseProblem.mem_no_gapMax_of_lt`,
  `Cslib.Complexity.PromiseProblem.mem_no_gapMin_of_lt`: characterization of no-instances of gap
  problems when the soundness and completeness thresholds are strictly separated.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Chapter 11][AroraBarak09]
* [S. Even, A. Selman, Y. Yacobi, *The complexity of promise problems with applications to
  public-key cryptography*][EvenSelmanYacobi1984]
* [O. Goldreich, *On promise problems: a survey*][Goldreich2006]
-/

@[expose] public section

namespace Cslib.Complexity.PromiseProblem

open Turing.MultiTapeTM

variable {α β γ : Type*} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
  {X : PromiseProblem α} {Y Y' : PromiseProblem β} {Z : PromiseProblem γ}

/-! ### Reductions -/

/-- A **polynomial-time reduction of promise problems** from `X` to `Y`: a function computable in
polynomial time with respect to `encA` and `encB` mapping the yes-instances of `X` to yes-instances
of `Y` and its no-instances to no-instances of `Y`. Instances outside the promise of `X` may go
anywhere. Between gap problems these are the gap-preserving reductions. -/
def PolyTimeReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool) (X : PromiseProblem α)
    (Y : PromiseProblem β) : Prop :=
  ∃ f : α → β, ComputableInPolyTime f encA encB ∧ Set.MapsTo f X.yes Y.yes ∧
    Set.MapsTo f X.no Y.no

/-- On decision problems, reductions of promise problems are polynomial-time reductions. -/
theorem polyTimeReducible_ofSet_iff {A : Set α} {B : Set β} :
    PolyTimeReducible encA encB (ofSet A) (ofSet B) ↔ Complexity.PolyTimeReducible encA encB A B :=
  exists_congr fun _ => and_congr_right fun _ =>
    ⟨fun ⟨hyes, hno⟩ _ => ⟨fun ha => hyes ha, fun hfa => by_contra fun ha => hno ha hfa⟩,
      fun h => ⟨fun a ha => (h a).1 ha, fun a ha hfa => ha ((h a).2 hfa)⟩⟩

/-- Every promise problem reduces to itself. -/
@[refl]
theorem PolyTimeReducible.refl (encA : α ↪ List Bool) (X : PromiseProblem α) :
    PolyTimeReducible encA encA X X :=
  ⟨id, ComputableInPolyTime.id', Set.mapsTo_id _, Set.mapsTo_id _⟩

/-- Reductions of promise problems compose. -/
@[trans]
theorem PolyTimeReducible.trans (hXY : PolyTimeReducible encA encB X Y)
    (hYZ : PolyTimeReducible encB encC Y Z) : PolyTimeReducible encA encC X Z :=
  let ⟨f, hf, hyes, hno⟩ := hXY
  let ⟨g, hg, hyes', hno'⟩ := hYZ
  ⟨g ∘ f, hg.comp hf, hyes'.comp hyes, hno'.comp hno⟩

/-- A promise problem reduces, by the identity, to any problem with more yes-instances and more
no-instances: enlarging the promise can only make a problem harder. -/
theorem PolyTimeReducible.of_subset (hyes : Y.yes ⊆ Y'.yes) (hno : Y.no ⊆ Y'.no) :
    PolyTimeReducible encB encB Y Y' :=
  ⟨id, ComputableInPolyTime.id', fun _ h => hyes h, fun _ h => hno h⟩

/-- **`PromiseP` is closed under reductions.** -/
theorem PolyTimeReducible.mem_PromiseP (h : PolyTimeReducible encA encB X Y)
    (hY : Y ∈ PromiseP encB) : X ∈ PromiseP encA := by
  obtain ⟨f, hf, hyes, hno⟩ := h
  obtain ⟨g, hg, hgyes, hgno⟩ := mem_PromiseP_iff.1 hY
  exact mem_PromiseP_iff.2 ⟨g ∘ f, hg.comp hf, fun a ha => hgyes _ (hyes ha),
    fun a ha => hgno _ (hno ha)⟩

/-- A reduction of promise problems restricts to a polynomial-time reduction between the problems
that separate them: for every problem `B` containing the yes-instances of `Y` and no no-instance,
its preimage separates `X` and reduces to `B`. -/
theorem PolyTimeReducible.exists_polyTimeReducible (h : PolyTimeReducible encA encB X Y)
    {B : Set β} (hyes : Y.yes ⊆ B) (hno : Disjoint B Y.no) :
    ∃ A : Set α, X.yes ⊆ A ∧ Disjoint A X.no ∧ Complexity.PolyTimeReducible encA encB A B := by
  obtain ⟨f, hf, hfyes, hfno⟩ := h
  refine ⟨f ⁻¹' B, fun a ha => hyes (hfyes ha), Set.disjoint_left.2 fun a ha ha' =>
    Set.disjoint_left.1 hno ha (hfno ha'), f, hf, fun _ => Iff.rfl⟩

section PromiseNP

variable {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
  {X : PromiseProblem α} {Y : PromiseProblem β}

/-- **`PromiseNP` is closed under polynomial-time reductions.** -/
theorem PolyTimeReducible.mem_PromiseNP (h : PolyTimeReducible encA encB X Y)
    (hY : Y ∈ PromiseNP encB) : X ∈ PromiseNP encA := by
  obtain ⟨B, hB, hyes, hno⟩ := hY
  obtain ⟨A, hAyes, hAno, hAB⟩ := h.exists_polyTimeReducible hyes hno
  exact ⟨A, _root_.Cslib.Complexity.PolyTimeReducible.mem_NP hAB hB, hAyes, hAno⟩

end PromiseNP

/-! ### NP-hardness -/

/-- A promise problem is **NP-hard** when every problem in `NP`, with any encoding of its
instances, reduces to it: some polynomial-time function maps its members to yes-instances and its
non-members to no-instances. This is `HardUnder` for `PolyTimeReducible` from `ofSet`. -/
def NPHard (encB : β ↪ List Bool) (Y : PromiseProblem β) : Prop :=
  HardUnder (fun enc A Y => PolyTimeReducible enc encB (ofSet A) Y) @NP Y

/-- NP-hardness of a promise problem is hardness for `NP` under `PolyTimeReducible` from `ofSet`. -/
theorem npHard_iff_hardUnder :
    NPHard encB Y ↔ HardUnder (fun enc A Y => PolyTimeReducible enc encB (ofSet A) Y) @NP Y :=
  Iff.rfl

/-- On decision problems, NP-hardness as a promise problem is `Cslib.Complexity.NPHard`. -/
theorem npHard_ofSet_iff {B : Set β} : NPHard encB (ofSet B) ↔ Complexity.NPHard encB B :=
  ⟨fun h _ enc A hA => polyTimeReducible_ofSet_iff.1 (h enc A hA),
    fun h _ enc A hA => polyTimeReducible_ofSet_iff.2 (h enc A hA)⟩

/-- NP-hardness transfers along reductions. -/
theorem NPHard.trans (hX : NPHard encA X) (h : PolyTimeReducible encA encB X Y) : NPHard encB Y :=
  HardUnder.trans (fun _ _ h' h'' => h'.trans h'') hX h

/-- Enlarging the promise preserves NP-hardness. -/
theorem NPHard.mono (hY : NPHard encB Y) (hyes : Y.yes ⊆ Y'.yes) (hno : Y.no ⊆ Y'.no) :
    NPHard encB Y' :=
  hY.trans (.of_subset hyes hno)

/-- **A reduction from `SAT` proves NP-hardness**, by the Cook–Levin theorem. -/
theorem npHard_of_polyTimeReducible_SAT (h : PolyTimeReducible encCNF encB (ofSet SAT) Y) :
    NPHard encB Y :=
  NPHard.trans (npHard_ofSet_iff.2 CookLevin.SAT_npHard) h

/-- Every problem separating the yes-instances of an NP-hard promise problem from its
no-instances is NP-hard. -/
theorem NPHard.npHard_of_subset (hY : NPHard encB Y) {B : Set β} (hyes : Y.yes ⊆ B)
    (hno : Disjoint B Y.no) : Complexity.NPHard encB B :=
  npHard_ofSet_iff.1 (hY.trans (.of_subset hyes (Set.subset_compl_iff_disjoint_left.2 hno)))

/-- If an NP-hard promise problem is solved in polynomial time, then `NP ⊆ P` for every encoding
of instances. -/
theorem NPHard.NP_subset_P_of_mem_PromiseP (hY : NPHard encB Y) (h : Y ∈ PromiseP encB)
    {α : Type} (enc : α ↪ List Bool) : NP enc ⊆ P enc :=
  fun A hA => ofSet_mem_PromiseP.1 ((hY enc A hA).mem_PromiseP h)

/-- **An NP-hard promise problem solved in polynomial time gives `P = NP`**, for every encoding
of instances. -/
theorem NPHard.P_eq_NP_of_mem_PromiseP (hY : NPHard encB Y) (h : Y ∈ PromiseP encB)
    {α : Type} (enc : α ↪ List Bool) : P enc = NP enc :=
  P_subset_NP.antisymm (hY.NP_subset_P_of_mem_PromiseP h enc)

/-- If `P ≠ NP` for some encoding, no NP-hard promise problem is solved in polynomial time. -/
theorem NPHard.notMem_PromiseP (hY : NPHard encB Y) {α : Type} {enc : α ↪ List Bool}
    (h : P enc ≠ NP enc) : Y ∉ PromiseP encB :=
  fun hP => h (hY.P_eq_NP_of_mem_PromiseP hP enc)

/-! ### Gap problems -/

/-- The **gap problem** of a maximization objective `val`, with completeness threshold `c` and
soundness threshold `s`: the yes-instances have value at least `c`, the no-instances value at most
`s`, below `c`. The thresholds may depend on the instance; an instance with `c x ≤ s x` is not a
no-instance, so that the two sets are disjoint. -/
def gapMax (val c s : α → ℝ) : PromiseProblem α where
  yes := {x | c x ≤ val x}
  no := {x | val x ≤ s x ∧ s x < c x}
  disjoint := Set.disjoint_left.2 fun _ hyes hno => (hno.1.trans_lt hno.2).not_ge hyes

variable {val c s : α → ℝ} {x : α}

@[simp]
theorem mem_yes_gapMax : x ∈ (gapMax val c s).yes ↔ c x ≤ val x :=
  Iff.rfl

@[simp]
theorem mem_no_gapMax : x ∈ (gapMax val c s).no ↔ val x ≤ s x ∧ s x < c x :=
  Iff.rfl

/-- With a strictly smaller soundness threshold, the no-instances are those of value at most
`s`. -/
theorem mem_no_gapMax_of_lt (h : s x < c x) : x ∈ (gapMax val c s).no ↔ val x ≤ s x :=
  and_iff_left h

/-- The **gap problem** of a minimization objective `val`, with completeness threshold `c` and
soundness threshold `s`: the yes-instances have value at most `c`, the no-instances value at least
`s`, above `c`. The thresholds may depend on the instance; an instance with `s x ≤ c x` is not a
no-instance, so that the two sets are disjoint. -/
def gapMin (val c s : α → ℝ) : PromiseProblem α where
  yes := {x | val x ≤ c x}
  no := {x | s x ≤ val x ∧ c x < s x}
  disjoint := Set.disjoint_left.2 fun _ hyes hno => (hyes.trans_lt hno.2).not_ge hno.1

@[simp]
theorem mem_yes_gapMin : x ∈ (gapMin val c s).yes ↔ val x ≤ c x :=
  Iff.rfl

@[simp]
theorem mem_no_gapMin : x ∈ (gapMin val c s).no ↔ s x ≤ val x ∧ c x < s x :=
  Iff.rfl

/-- With a strictly larger soundness threshold, the no-instances are those of value at least
`s`. -/
theorem mem_no_gapMin_of_lt (h : c x < s x) : x ∈ (gapMin val c s).no ↔ s x ≤ val x :=
  and_iff_left h

/-- The promise problem `Q` with its promise restricted to the instances in `S`. -/
def restrict (Q : PromiseProblem α) (S : Set α) : PromiseProblem α where
  yes := Q.yes ∩ S
  no := Q.no ∩ S
  disjoint := Q.disjoint.mono Set.inter_subset_left Set.inter_subset_left

@[simp]
theorem yes_restrict (Q : PromiseProblem α) (S : Set α) : (Q.restrict S).yes = Q.yes ∩ S :=
  rfl

@[simp]
theorem no_restrict (Q : PromiseProblem α) (S : Set α) : (Q.restrict S).no = Q.no ∩ S :=
  rfl

end Cslib.Complexity.PromiseProblem
