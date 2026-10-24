/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.NP
public import Complexity.Computability.Complexity.Classes.P
public import Complexity.Computability.Complexity.Reduction.ManyOne
public import Complexity.Computability.Machines.Turing.MultiTape.Halting.Reduction

/-!
# Polynomial-time many-one reductions

`PolyTimeReducible encA encB A B`: a function computable in polynomial time with respect to the
encodings `encA` and `encB` maps instances of `A` to instances of `B`, preserving membership [Arora
and Barak, Definition 2.7][AroraBarak09]. It is, by definition, the many-one reducibility
`Cslib.Complexity.ManyOneReducibleBy` by maps computable in polynomial time
(`Cslib.Complexity.polyTimeReducible_iff_manyOneReducibleBy`), and its preorder and complement
lemmas are instances of the core's. Its body is kept as the `∃` statement, so that the
admissibility goal of an anonymous constructor is `ComputableInPolyTime f encA encB` itself, as
`fun_prop` expects. The checked client in `ComplexityTests.NPCompleteness` supplies plain decider,
verifier and reduction certificates, then transfers IndependentSet hardness to Clique.

A class of problems is given, as `NP` or `coNP`, by a set of problems for every type of instances
and every encoding of them. A problem `B` is hard for such a class `C` when every problem in `C`,
with any encoding of its instances, reduces to `B` (`PolyTimeHard C encB B`), and complete when it
also belongs to `C` (`PolyTimeComplete C encB B`), the instances of `Cslib.Complexity.HardUnder`
and `Cslib.Complexity.CompleteUnder` for `PolyTimeReducible`. The second conjunct of
`PolyTimeComplete` is stated as `PolyTimeHard`, so that its projection keeps the `PolyTimeHard`
API. `NPHard`, `NPComplete`, `coNPHard`
and `coNPComplete` are the instances for `NP` and `coNP`. When the problems of a class `D` are the
complements of those of `C`, the complement of a `C`-complete problem is `D`-complete
(`PolyTimeComplete.compl`).

Hardness quantifies over problems whose instances live in `Type`, with every encoding of instances.
Instances of complexity-theoretic problems are finite objects encoded as words, so this loses
nothing: a problem in a higher universe is equivalent, through its encoding, to the problem of
recognising the encodings of its members.

Mathlib's `ManyOneReducible` (`Mathlib/Computability/Reduce.lean`) is the computable, not the
polynomial-time, reducibility, and is stated for `Primcodable` types; it is not reused here.

## Finding a proved NP-complete problem

The declarations below give the exact problems, encodings and hypotheses; follow their source
module to import a result. Names in this table are relative to `Cslib.Complexity`. For example,
import `Complexity.Computability.Complexity.Problems.Clique` to use `Clique_npComplete` and
`polyTimeReducible_IndependentSet_Clique`. Cook–Levin's `CookLevin.SAT_npHard` reduces every NP
problem to SAT. These are navigation tables, not an exhaustive list of reductions or classes.

| Problem | NP-completeness declaration |
| --- | --- |
| CNF satisfiability (Cook–Levin) | `CookLevin.SAT_npComplete` |
| At most three literals per clause | `ThreeSAT_npComplete` |
| Exactly three literals, repetitions allowed | `ExactThreeSAT_npComplete` |
| Boolean circuit satisfiability | `CircuitSAT_npComplete` |
| Independent set | `IndependentSet_npComplete` |
| Clique | `Clique_npComplete` |
| Vertex cover | `VertexCover_npComplete` |
| Three-colorability | `ThreeColoring_npComplete` |
| Fixed `k`-colorability, `3 ≤ k` | `KColoring_npComplete` |
| Directed Hamiltonian path, specified endpoints | `DirHamPath_npComplete` |
| Directed Hamiltonian cycle | `DirHamCycle_npComplete` |
| Undirected Hamiltonian path, specified endpoints | `HamPath_npComplete` |
| Undirected Hamiltonian cycle | `HamCycle_npComplete` |
| Subset sum | `SubsetSum_npComplete` |
| Partition | `Partition_npComplete` |
| Knapsack | `Knapsack_npComplete` |
| Zero-one integer programming | `ZeroOneIP_npComplete` |
| Traveling salesperson | `TSP_npComplete` |

| Source → target | Reduction declaration |
| --- | --- |
| SAT → ThreeSAT | `polyTimeReducible_SAT_ThreeSAT` |
| ThreeSAT → ExactThreeSAT | `polyTimeReducible_ThreeSAT_ExactThreeSAT` |
| SAT → CircuitSAT | `SAT.polyTimeReducible_CircuitSAT` |
| SAT → IndependentSet | `polyTimeReducible_SAT_IndependentSet` |
| IndependentSet → Clique | `polyTimeReducible_IndependentSet_Clique` |
| IndependentSet → VertexCover | `polyTimeReducible_IndependentSet_VertexCover` |
| SAT → ThreeColoring | `polyTimeReducible_SAT_ThreeColoring` |
| ThreeSAT → ThreeColoring | `polyTimeReducible_ThreeSAT_ThreeColoring` |
| SAT → KColoring `k`, for `3 ≤ k` | `polyTimeReducible_SAT_KColoring` |
| SAT → DirHamPath | `polyTimeReducible_SAT_DirHamPath` |
| ThreeSAT → DirHamPath | `polyTimeReducible_ThreeSAT_DirHamPath` |
| SAT → DirHamCycle | `polyTimeReducible_SAT_DirHamCycle` |
| DirHamPath → HamPath | `polyTimeReducible_DirHamPath_HamPath` |
| DirHamCycle → HamCycle | `polyTimeReducible_DirHamCycle_HamCycle` |
| ThreeSAT → SubsetSum | `polyTimeReducible_ThreeSAT_SubsetSum` |
| SubsetSum → Partition | `polyTimeReducible_SubsetSum_Partition` |
| SubsetSum → Knapsack | `polyTimeReducible_SubsetSum_Knapsack` |
| SubsetSum → ZeroOneIP | `polyTimeReducible_SubsetSum_ZeroOneIP` |
| ThreeSAT → ZeroOneIP | `polyTimeReducible_ThreeSAT_ZeroOneIP` |
| HamCycle → TSP | `polyTimeReducible_HamCycle_TSP` |

## Main definitions

* `Cslib.Complexity.PolyTimeReducible`.
* `Cslib.Complexity.PolyTimeHard`, `Cslib.Complexity.PolyTimeComplete`: hardness and completeness
  for a class.
* `Cslib.Complexity.NPHard`, `Cslib.Complexity.NPComplete`.
* `Cslib.Complexity.coNPHard`, `Cslib.Complexity.coNPComplete`.

## Main results

* `Cslib.Complexity.P_subset_NP`, `Cslib.Complexity.P_subset_coNP`: `P` is contained in `NP` and
  in `coNP`.
* `Cslib.Complexity.NPComplete.P_eq_NP_of_mem_P`, `Cslib.Complexity.NPComplete.mem_P_iff`: an
  `NP`-complete problem is in `P` exactly when `P = NP` for every encoding.
* `Cslib.Complexity.NPComplete.mem_P_iff_mem_P`: two `NP`-complete problems are both in `P` or
  both outside it.
* `Cslib.Complexity.PolyTimeReducible.refl`, `Cslib.Complexity.PolyTimeReducible.trans`:
  polynomial-time reducibility is a preorder.
* `Cslib.Complexity.PolyTimeReducible.mem_P`: `P` is closed under polynomial-time reductions.
* `Cslib.Complexity.PolyTimeHard.trans`, `Cslib.Complexity.NPHard.trans`,
  `Cslib.Complexity.coNPHard.trans`: hardness transfers along polynomial-time reductions.
* `Cslib.Complexity.PolyTimeReducible.compl`: a reduction between problems is one between their
  complements.
* `Cslib.Complexity.PolyTimeHard.compl`, `Cslib.Complexity.PolyTimeComplete.compl`: complements of
  hard and complete problems.
* `Cslib.Complexity.NPHard.compl`, `Cslib.Complexity.coNPHard.compl`,
  `Cslib.Complexity.NPComplete.compl`, `Cslib.Complexity.coNPComplete.compl`: complements exchange
  hardness and completeness for `NP` and `coNP`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α β : Type*}

/-- `A` reduces to `B` in polynomial time: some `f`, computable in polynomial time with respect to
`encA` and `encB`, satisfies `a ∈ A ↔ f a ∈ B`. This is `ManyOneReducibleBy` for the maps computable
in polynomial time (`polyTimeReducible_iff_manyOneReducibleBy`).

Construct a proof as `⟨f, by fun_prop, h⟩`, where `h` proves the membership equivalence for every
source instance. Write `f` with certified Boolean, list and arithmetic operations, including
`decide` of connectives, (in)equalities and list membership; unfold local definitions so
`fun_prop` or `polytime` can see them. Cost and correctness are separate obligations: automation
does not prove `h`. See the checked graph-complement example in `ComplexityTests.NPCompleteness`.
-/
def PolyTimeReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool) (A : Set α) (B : Set β) :
    Prop :=
  ∃ f : α → β, ComputableInPolyTime f encA encB ∧ ∀ a, a ∈ A ↔ f a ∈ B

/-- Polynomial-time reducibility is many-one reducibility by the maps computable in polynomial
time. -/
theorem polyTimeReducible_iff_manyOneReducibleBy {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {A : Set α} {B : Set β} :
    PolyTimeReducible encA encB A B ↔ ManyOneReducibleBy (ComputableInPolyTime · encA encB) A B :=
  Iff.rfl

/-- `B` is hard for the class `C` under polynomial-time many-one reductions: every problem in `C`,
with any encoding of its instances, reduces to `B`. This is `HardUnder` for `PolyTimeReducible`. -/
def PolyTimeHard (C : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)) (encB : β ↪ List Bool)
    (B : Set β) : Prop :=
  HardUnder (fun enc => PolyTimeReducible enc encB) @C B

/-- `B` is complete for the class `C` under polynomial-time many-one reductions: it is in `C` and
every problem in `C` reduces to it. This is `CompleteUnder` for `PolyTimeReducible`
(`polyTimeComplete_iff_completeUnder`), with its second conjunct stated as `PolyTimeHard`. -/
def PolyTimeComplete {β : Type} (C : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α))
    (encB : β ↪ List Bool) (B : Set β) : Prop :=
  B ∈ C encB ∧ PolyTimeHard C encB B

/-- Polynomial-time hardness is hardness under `PolyTimeReducible`. -/
theorem polyTimeHard_iff_hardUnder {C : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)}
    {encB : β ↪ List Bool} {B : Set β} :
    PolyTimeHard C encB B ↔ HardUnder (fun enc => PolyTimeReducible enc encB) @C B :=
  Iff.rfl

/-- Polynomial-time completeness is completeness under `PolyTimeReducible`. -/
theorem polyTimeComplete_iff_completeUnder {β : Type}
    {C : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)} {encB : β ↪ List Bool} {B : Set β} :
    PolyTimeComplete C encB B ↔ CompleteUnder (fun enc => PolyTimeReducible enc encB) @C encB B :=
  Iff.rfl

/-- Every problem in `NP`, with any encoding of its instances, reduces to `B`. -/
abbrev NPHard (encB : β ↪ List Bool) (B : Set β) : Prop := PolyTimeHard @NP encB B

/-- `B` is in `NP` and every problem in `NP` reduces to it. -/
abbrev NPComplete {β : Type} (encB : β ↪ List Bool) (B : Set β) : Prop :=
  PolyTimeComplete @NP encB B

/-- Every problem in `coNP`, with any encoding of its instances, reduces to `B`. -/
abbrev coNPHard (encB : β ↪ List Bool) (B : Set β) : Prop := PolyTimeHard @coNP encB B

/-- `B` is in `coNP` and every problem in `coNP` reduces to it. -/
abbrev coNPComplete {β : Type} (encB : β ↪ List Bool) (B : Set β) : Prop :=
  PolyTimeComplete @coNP encB B

/-- Hardness for the class `NP` is `NPHard`. -/
theorem polyTimeHard_NP_iff {encB : β ↪ List Bool} {B : Set β} :
    PolyTimeHard @NP encB B ↔ NPHard encB B := Iff.rfl

/-- Completeness for the class `NP` is `NPComplete`. -/
theorem polyTimeComplete_NP_iff {β : Type} {encB : β ↪ List Bool} {B : Set β} :
    PolyTimeComplete @NP encB B ↔ NPComplete encB B := Iff.rfl

/-- Hardness for the class `coNP` is `coNPHard`. -/
theorem polyTimeHard_coNP_iff {encB : β ↪ List Bool} {B : Set β} :
    PolyTimeHard @coNP encB B ↔ coNPHard encB B := Iff.rfl

/-- Completeness for the class `coNP` is `coNPComplete`. -/
theorem polyTimeComplete_coNP_iff {β : Type} {encB : β ↪ List Bool} {B : Set β} :
    PolyTimeComplete @coNP encB B ↔ coNPComplete encB B := Iff.rfl

variable {γ : Type*} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
  {A : Set α} {B : Set β} {C : Set γ}

/-- Every problem reduces to itself in polynomial time by the identity function. -/
@[refl]
theorem PolyTimeReducible.refl (encA : α ↪ List Bool) (A : Set α) :
    PolyTimeReducible encA encA A A :=
  ManyOneReducibleBy.refl ComputableInPolyTime.id' A

/-- Polynomial-time many-one reductions compose. -/
@[trans]
theorem PolyTimeReducible.trans (hAB : PolyTimeReducible encA encB A B)
    (hBC : PolyTimeReducible encB encC B C) : PolyTimeReducible encA encC A C :=
  ManyOneReducibleBy.trans (fun _ _ hf hg => hg.comp hf) hAB hBC

/-- **`P` is closed under polynomial-time reductions.** -/
theorem PolyTimeReducible.mem_P (hAB : PolyTimeReducible encA encB A B) (hB : B ∈ P encB) :
    A ∈ P encA :=
  ManyOneReducibleBy.trans (C := {true}) (fun _ _ hf hg => hg.comp hf) hAB hB

/-- A reduction from `A` to `B` is also a reduction from `Aᶜ` to `Bᶜ`. -/
theorem PolyTimeReducible.compl (h : PolyTimeReducible encA encB A B) :
    PolyTimeReducible encA encB Aᶜ Bᶜ :=
  ManyOneReducibleBy.compl h

/-- If polynomial-time reductions preserve membership from `D` to `C`, they also preserve
membership in the complement classes `{B | Bᶜ ∈ D}` and `{A | Aᶜ ∈ C}`. -/
theorem PolyTimeReducible.mem_compl {C : Set (Set α)} {D : Set (Set β)}
    (hCD : ∀ {A : Set α} {B : Set β}, PolyTimeReducible encA encB A B → B ∈ D → A ∈ C)
    (h : PolyTimeReducible encA encB A B) (hB : Bᶜ ∈ D) : Aᶜ ∈ C :=
  ManyOneReducibleBy.mem_compl hCD h hB

/-- A polynomial-time reduction is a mapping reduction. -/
theorem PolyTimeReducible.mappingReducible (h : PolyTimeReducible encA encB A B) :
    MappingReducible encA encB A B :=
  ManyOneReducibleBy.mono (fun _ hf => hf.tidy.isComputable) h

section Hardness

variable {𝒞 𝒟 : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)}

/-- Hardness transfers along a polynomial-time reduction. -/
theorem PolyTimeHard.trans (hB : PolyTimeHard 𝒞 encB B) (hBC : PolyTimeReducible encB encC B C) :
    PolyTimeHard 𝒞 encC C :=
  HardUnder.trans (fun _ _ h h' => h.trans h') hB hBC

/-- If the complement of every problem in `𝒟` is in `𝒞`, the complement of a `𝒞`-hard problem is
`𝒟`-hard. -/
theorem PolyTimeHard.compl (h𝒟𝒞 : ∀ {α : Type} (enc : α ↪ List Bool) (A : Set α), A ∈ 𝒟 enc →
    Aᶜ ∈ 𝒞 enc) (hB : PolyTimeHard 𝒞 encB B) : PolyTimeHard 𝒟 encB Bᶜ :=
  HardUnder.compl (fun _ _ h => h.compl) h𝒟𝒞 hB

/-- If the problems in `𝒟` are exactly the complements of the problems in `𝒞`, the complement of
a `𝒞`-complete problem is `𝒟`-complete. -/
theorem PolyTimeComplete.compl {β : Type} {encB : β ↪ List Bool} {B : Set β}
    (h𝒟𝒞 : ∀ {α : Type} (enc : α ↪ List Bool) (A : Set α), A ∈ 𝒟 enc ↔ Aᶜ ∈ 𝒞 enc)
    (hB : PolyTimeComplete 𝒞 encB B) : PolyTimeComplete 𝒟 encB Bᶜ :=
  CompleteUnder.compl (fun _ _ h => h.compl) h𝒟𝒞 hB

end Hardness

/-- `NP`-hardness transfers along a polynomial-time reduction. -/
theorem NPHard.trans (hA : NPHard encA A) (hAB : PolyTimeReducible encA encB A B) :
    NPHard encB B :=
  PolyTimeHard.trans hA hAB

/-- `coNP`-hardness transfers along a polynomial-time reduction. -/
theorem coNPHard.trans (hA : coNPHard encA A) (hAB : PolyTimeReducible encA encB A B) :
    coNPHard encB B :=
  PolyTimeHard.trans hA hAB

/-- The complement of an `NP`-hard problem is `coNP`-hard. -/
theorem NPHard.compl (h : NPHard encB B) : coNPHard encB Bᶜ :=
  PolyTimeHard.compl (fun _ _ hA => hA) h

/-- The complement of a `coNP`-hard problem is `NP`-hard. -/
theorem coNPHard.compl (h : coNPHard encB B) : NPHard encB Bᶜ :=
  PolyTimeHard.compl (fun _ _ hA => by simpa [mem_coNP] using hA) h

/-- The complement of an `NP`-complete problem is `coNP`-complete. -/
theorem NPComplete.compl {β : Type} {encB : β ↪ List Bool} {B : Set β} (h : NPComplete encB B) :
    coNPComplete encB Bᶜ :=
  PolyTimeComplete.compl (fun _ _ => Iff.rfl) h

/-- The complement of a `coNP`-complete problem is `NP`-complete. -/
theorem coNPComplete.compl {β : Type} {encB : β ↪ List Bool} {B : Set β}
    (h : coNPComplete encB B) : NPComplete encB Bᶜ :=
  PolyTimeComplete.compl (fun _ _ => by simp [mem_coNP]) h

/-! ### `P` and `NP`-complete problems -/

/-- **`P ⊆ NP`**: a decider is a verifier ignoring its certificate. -/
theorem P_subset_NP {α : Type} {enc : α ↪ List Bool} : P enc ⊆ NP enc :=
  fun _ ⟨f, hf, hA⟩ => ⟨0, fun x => f x.1, hf.comp (ComputableInPolyTime.fst enc encBits),
    fun a => (hA a).trans ⟨fun h => ⟨[], by simp, h⟩, fun ⟨_, _, h⟩ => h⟩⟩

/-- **`P ⊆ coNP`**: `P` is closed under complement. -/
theorem P_subset_coNP {α : Type} {enc : α ↪ List Bool} : P enc ⊆ coNP enc :=
  fun _ hA => P_subset_NP (compl_mem_P hA)

/-- **An `NP`-complete problem in `P` gives `P = NP`**, for every encoding of instances: every
problem in `NP` reduces to it, and `P` is closed under polynomial-time reductions. -/
theorem NPComplete.P_eq_NP_of_mem_P {β : Type} {encB : β ↪ List Bool} {B : Set β}
    (hB : NPComplete encB B) (h : B ∈ P encB) {α : Type} (enc : α ↪ List Bool) :
    P enc = NP enc :=
  P_subset_NP.antisymm fun A hA => (hB.2 enc A hA).mem_P h

/-- **An `NP`-complete problem is in `P` exactly when `P = NP`**, for every encoding of
instances. -/
theorem NPComplete.mem_P_iff {β : Type} {encB : β ↪ List Bool} {B : Set β}
    (hB : NPComplete encB B) : B ∈ P encB ↔ ∀ {α : Type} (enc : α ↪ List Bool), P enc = NP enc :=
  ⟨fun h _ enc => hB.P_eq_NP_of_mem_P h enc, fun h => h encB ▸ hB.1⟩

/-- Two `NP`-complete problems are both in `P` or both outside it. -/
theorem NPComplete.mem_P_iff_mem_P {β γ : Type} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    {B : Set β} {C : Set γ} (hB : NPComplete encB B) (hC : NPComplete encC C) :
    B ∈ P encB ↔ C ∈ P encC :=
  hB.mem_P_iff.trans hC.mem_P_iff.symm

end Cslib.Complexity
