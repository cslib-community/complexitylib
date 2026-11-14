/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.FiniteVariable.Infinitary
public import CslibFrontier.Logics.FirstOrder.ZeroOneLaw.BinomialRandomGraph
public import CslibFrontier.Logics.FirstOrder.ZeroOneLaw.Relational
import CslibFrontier.Logics.FirstOrder.FiniteVariable.ColorRefinement
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.Basic

/-!
# The Kolaitis–Vardi `0-1` law for `L^k_{∞ω}`

**Theorem** (Kolaitis–Vardi 1992 [KolaitisVardi1992]). Fix a variable bound `k : ℕ`.
1. **Simple graphs (`G(n, p)` for constant `0 < p < 1`).** For every closed formula `φ` of the
   infinitary `k`-variable logic `L^k_{∞ω}` (`φ.freeVars = ∅`, at any index universe `w` and even
   of unbounded quantifier depth), the probability that the binomial random graph `G(Fin n, p)`
   satisfies `φ` converges as `n → ∞` either to `0` or to `1`. The limit is `1` if and only if `φ`
   holds in the Rado graph, and is therefore independent of `p`.
2. **Finite relational vocabularies.** Let `L` be a finite relational language with no nullary
   relation symbols, and fix constant probabilities `0 < p R < 1` for each relation symbol `R`. For
   every closed `L^k_{∞ω}` formula `φ`, the probability that `bernoulliStructure p n` (and in
   particular `uniformStructure n`) satisfies `φ` converges as `n → ∞` either to `0` or to `1`,
   independently of `p`.

The pebble-game mechanism replaces logical compactness in Fagin's first-order proof: moving one of
`k` pebbles leaves at most `k - 1` placed pebbles fixed, so any two structures satisfying all
`< k`-extension axioms admit `PartialIsoOn` as a `k`-pebble back-and-forth invariant
(`IsPebbleBackAndForth`). Because there are only finitely many `< k`-extension axioms over a finite
relational vocabulary, their conjunction holds with probability tending to `1` as `n → ∞`. Every
nonempty structure satisfying that finite conjunction is `L^k_{∞ω}`-equivalent to the Rado graph
(respectively to any model of `Relational.extensionTheory L`), transferring truth of `φ` regardless
of its quantifier depth.

As an illustration beyond first-order logic, graph connectivity is definable in `L^3_{∞ω}`
(`connectedInfinitary`, of unbounded quantifier depth) and holds in the Rado graph, so
`G(Fin n, p)` is connected with probability tending to `1`
(`tendsto_binomialRandom_real_connected`).

## Main definitions

* `Cslib.Logic.FO.RealizeInfinitary`: satisfaction of an `L^k_{∞ω}` formula at all `k`-tuples.
* `Cslib.Logic.FO.infinitaryProb`: probability that a random structure satisfies an `L^k_{∞ω}`
  formula.
* `Cslib.Logic.FO.graph.SatisfiesInfinitary`: satisfaction of an `L^k_{∞ω}` graph formula by a
  simple graph.

## Main results

* `Cslib.Logic.FO.graph.isPebbleBackAndForth_of_satisfies_extensionAxiom_lt`: `< k`-extension axioms
  make `PartialIsoOn Language.graph` a `k`-pebble back-and-forth invariant on simple graphs.
* `Cslib.Logic.FO.graph.binomialRandom_infinitary_zero_one_law`,
  `Cslib.Logic.FO.graph.randomGraph_infinitary_zero_one_law`: the Kolaitis–Vardi `0-1` law for
  `G(Fin n, p)` (`0 < p < 1`) and `G(n, 1/2)`.
* `Cslib.Logic.FO.graph.tendsto_binomialRandom_real_infinitary_one_iff_radoGraph`,
  `Cslib.Logic.FO.graph.tendsto_binomialRandom_real_infinitary_zero_iff_radoGraph`: the almost-sure
  `L^k_{∞ω}` theory of `G(Fin n, p)` is the `L^k_{∞ω}` theory of the Rado graph, independent of `p`.
* `Cslib.Logic.FO.graph.tendsto_binomialRandom_real_connected`: `G(Fin n, p)` is connected with
  probability tending to `1`.
* `Cslib.Logic.FO.Relational.isPebbleBackAndForth_of_hasExtension_lt`: `< k`-extension axioms make
  `PartialIsoOn L` a `k`-pebble back-and-forth invariant over any language.
* `Cslib.Logic.FO.Relational.bernoulliStructure_infinitary_zero_one_law`,
  `Cslib.Logic.FO.Relational.uniformStructure_infinitary_zero_one_law`: the Kolaitis–Vardi `0-1`
  law for `bernoulliStructure p n` (`0 < p R < 1`) and `uniformStructure n`.
* `Cslib.Logic.FO.Relational.tendsto_infinitaryProb_bernoulliStructure_one_iff_model`,
  `Cslib.Logic.FO.Relational.tendsto_infinitaryProb_bernoulliStructure_zero_iff_model`: model
  characterizations of asymptotic probability `1` and `0` via `extensionTheory L`.

## References

* [Ph. G. Kolaitis and M. Y. Vardi, *Infinitary logic and 0-1 laws*][KolaitisVardi1992]
* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Chapters 11–12.
-/

public section

open FirstOrder Language Structure MeasureTheory ProbabilityTheory unitInterval Filter
open scoped SimpleGraph

namespace Cslib.Logic.FO

universe w u v

section GeneralTransfer

variable {L : Language.{u, v}}

/-- An `L`-structure `M` satisfies an `L^k_{∞ω}` formula `φ` universally if `φ` holds under every
pebble assignment `Fin k → M`. When `φ.freeVars = ∅`, all pebble assignments agree
(`realizeInfinitary_iff_realize`). -/
def RealizeInfinitary {M : Type*} [L.Structure M] {k : ℕ}
    (φ : FiniteVariable.InfinitaryFormula.{w, u, v} L k) : Prop :=
  ∀ a : Fin k → M, φ.Realize a

/-- The probability that a random `L`-structure drawn from `μ` satisfies `φ`. -/
noncomputable def infinitaryProb {α : Type*} (μ : PMF (L.Structure α)) {k : ℕ}
    (φ : FiniteVariable.InfinitaryFormula.{w, u, v} L k) : ℝ :=
  structProb μ fun S => @RealizeInfinitary L α S k φ

theorem infinitaryProb_def {α : Type*} (μ : PMF (L.Structure α)) {k : ℕ}
    (φ : FiniteVariable.InfinitaryFormula.{w, u, v} L k) :
    infinitaryProb μ φ = structProb μ fun S => @RealizeInfinitary L α S k φ := by
  rw [infinitaryProb]

/-- A closed `L^k_{∞ω}` formula (`φ.freeVars = ∅`) holds universally in `M` iff it holds at any
given pebble assignment `a : Fin k → M`. -/
theorem realizeInfinitary_iff_realize {M : Type*} [L.Structure M] {k : ℕ}
    {φ : FiniteVariable.InfinitaryFormula.{w, u, v} L k} (hφ : φ.freeVars = ∅) (a : Fin k → M) :
    RealizeInfinitary (M := M) φ ↔ φ.Realize a :=
  ⟨fun h => h a, fun ha a' =>
    (φ.realize_congr fun i hi => by rw [hφ] at hi; exact hi.elim).2 ha⟩

/-- On a nonempty structure, universal satisfaction of a closed `L^k_{∞ω}` formula commutes with
negation. -/
theorem realizeInfinitary_not {M : Type*} [L.Structure M] [Nonempty M] {k : ℕ}
    {φ : FiniteVariable.InfinitaryFormula.{w, u, v} L k} (hφ : φ.freeVars = ∅) :
    RealizeInfinitary (M := M) φ.not ↔ ¬RealizeInfinitary (M := M) φ := by
  let a : Fin k → M := fun _ => Classical.arbitrary M
  have hnot : φ.not.freeVars = ∅ := by
    simp only [FiniteVariable.InfinitaryFormula.freeVars_not, hφ]
  rw [realizeInfinitary_iff_realize hnot a, FiniteVariable.InfinitaryFormula.realize_not,
    realizeInfinitary_iff_realize hφ a]

theorem infinitaryProb_not {α : Type*} [Nonempty α] (μ : PMF (L.Structure α)) {k : ℕ}
    {φ : FiniteVariable.InfinitaryFormula.{w, u, v} L k} (hφ : φ.freeVars = ∅) :
    infinitaryProb μ φ.not = 1 - infinitaryProb μ φ := by
  have heq : (fun S : L.Structure α => @RealizeInfinitary L α S k φ.not) =
      fun S => ¬@RealizeInfinitary L α S k φ :=
    funext fun S => propext (@realizeInfinitary_not L α S _ k φ hφ)
  rw [infinitaryProb_def, infinitaryProb_def, heq, structProb_not]

/-- A `k`-pebble back-and-forth invariant relating `(∅, a, b)` transfers every closed `L^k_{∞ω}`
formula between `M` and `N`. -/
theorem realizeInfinitary_iff_of_isPebbleBackAndForth {M N : Type*} [L.Structure M]
    [L.Structure N] {k : ℕ} {Inv : Set (Fin k) → (Fin k → M) → (Fin k → N) → Prop}
    (hInv : IsPebbleBackAndForth L Inv) {a : Fin k → M} {b : Fin k → N} (hab : Inv ∅ a b)
    {φ : FiniteVariable.InfinitaryFormula.{w, u, v} L k} (hφ : φ.freeVars = ∅) :
    RealizeInfinitary (M := M) φ ↔ RealizeInfinitary (M := N) φ := by
  rw [realizeInfinitary_iff_realize hφ a, realizeInfinitary_iff_realize hφ b]
  exact hInv.realize_infinitaryFormula_iff hab (by rw [hφ])

/-- **Measure-independent infinitary transfer (probability `1`).** If a finite set `T₀` of
first-order sentences holds with probability tending to `1` under `μ n`, and every nonempty finite
model of `T₀` is `k`-pebble back-and-forth equivalent to `M₀` from `∅`, then every closed
`L^k_{∞ω}` formula true in `M₀` holds under `μ n` with probability tending to `1`. -/
theorem tendsto_infinitaryProb_one_of_finset (μ : ∀ n, PMF (L.Structure (Fin n)))
    (T₀ : Finset L.Sentence)
    (hT₀ : ∀ ψ ∈ T₀, Tendsto (fun n => sentenceProb (μ n) ψ) atTop (nhds 1))
    {M₀ : Type*} [L.Structure M₀] {k : ℕ}
    (hbf : ∀ n (_ : Nonempty (Fin n)) (S : L.Structure (Fin n)),
      (∀ ψ ∈ T₀, @Sentence.Realize L (Fin n) S ψ) →
        ∃ (Inv : Set (Fin k) → (Fin k → Fin n) → (Fin k → M₀) → Prop)
          (a : Fin k → Fin n) (b : Fin k → M₀),
          @IsPebbleBackAndForth L (Fin n) M₀ S _ k Inv ∧ Inv ∅ a b)
    {φ : FiniteVariable.InfinitaryFormula.{w, u, v} L k} (hφ : φ.freeVars = ∅)
    (hM₀ : RealizeInfinitary (M := M₀) φ) :
    Tendsto (fun n => infinitaryProb (μ n) φ) atTop (nhds 1) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_structProb_forall_finset μ T₀ hT₀) tendsto_const_nhds ?_
    (Eventually.of_forall fun n => structProb_le_one _ _)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine structProb_mono fun S hS => ?_
  let _ := S
  obtain ⟨Inv, a, b, hInv, hab⟩ := hbf n hne S hS
  exact (realizeInfinitary_iff_of_isPebbleBackAndForth hInv hab hφ).2 hM₀

/-- **Measure-independent infinitary transfer (probability `0`).** Under the same hypotheses with
`M₀` nonempty, every closed `L^k_{∞ω}` formula false in `M₀` holds under `μ n` with probability
tending to `0`. -/
theorem tendsto_infinitaryProb_zero_of_finset (μ : ∀ n, PMF (L.Structure (Fin n)))
    (T₀ : Finset L.Sentence)
    (hT₀ : ∀ ψ ∈ T₀, Tendsto (fun n => sentenceProb (μ n) ψ) atTop (nhds 1))
    {M₀ : Type*} [L.Structure M₀] [Nonempty M₀] {k : ℕ}
    (hbf : ∀ n (_ : Nonempty (Fin n)) (S : L.Structure (Fin n)),
      (∀ ψ ∈ T₀, @Sentence.Realize L (Fin n) S ψ) →
        ∃ (Inv : Set (Fin k) → (Fin k → Fin n) → (Fin k → M₀) → Prop)
          (a : Fin k → Fin n) (b : Fin k → M₀),
          @IsPebbleBackAndForth L (Fin n) M₀ S _ k Inv ∧ Inv ∅ a b)
    {φ : FiniteVariable.InfinitaryFormula.{w, u, v} L k} (hφ : φ.freeVars = ∅)
    (hM₀ : ¬RealizeInfinitary (M := M₀) φ) :
    Tendsto (fun n => infinitaryProb (μ n) φ) atTop (nhds 0) := by
  have hnot_fv : φ.not.freeVars = ∅ := by
    simp only [FiniteVariable.InfinitaryFormula.freeVars_not, hφ]
  have hnot_M₀ : RealizeInfinitary (M := M₀) φ.not := (realizeInfinitary_not hφ).2 hM₀
  have h1 := tendsto_infinitaryProb_one_of_finset μ T₀ hT₀ hbf hnot_fv hnot_M₀
  have hsub := h1.const_sub 1
  simp only [sub_self] at hsub
  refine hsub.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [infinitaryProb_not (μ n) hφ, sub_sub_cancel]

/-- **Measure-independent `0-1` law for `L^k_{∞ω}`.** -/
theorem infinitary_zero_one_law_of_finset (μ : ∀ n, PMF (L.Structure (Fin n)))
    (T₀ : Finset L.Sentence)
    (hT₀ : ∀ ψ ∈ T₀, Tendsto (fun n => sentenceProb (μ n) ψ) atTop (nhds 1))
    {M₀ : Type*} [L.Structure M₀] [Nonempty M₀] {k : ℕ}
    (hbf : ∀ n (_ : Nonempty (Fin n)) (S : L.Structure (Fin n)),
      (∀ ψ ∈ T₀, @Sentence.Realize L (Fin n) S ψ) →
        ∃ (Inv : Set (Fin k) → (Fin k → Fin n) → (Fin k → M₀) → Prop)
          (a : Fin k → Fin n) (b : Fin k → M₀),
          @IsPebbleBackAndForth L (Fin n) M₀ S _ k Inv ∧ Inv ∅ a b)
    {φ : FiniteVariable.InfinitaryFormula.{w, u, v} L k} (hφ : φ.freeVars = ∅) :
    Tendsto (fun n => infinitaryProb (μ n) φ) atTop (nhds 0) ∨
      Tendsto (fun n => infinitaryProb (μ n) φ) atTop (nhds 1) := by
  by_cases hM₀ : RealizeInfinitary (M := M₀) φ
  · exact Or.inr (tendsto_infinitaryProb_one_of_finset μ T₀ hT₀ hbf hφ hM₀)
  · exact Or.inl (tendsto_infinitaryProb_zero_of_finset μ T₀ hT₀ hbf hφ hM₀)

/-- Under a `0-1` law for `L^k_{∞ω}`, a property whose probability tends neither to `0` nor to `1`
agrees on all large structures with no closed `L^k_{∞ω}` formula. -/
theorem not_exists_infinitaryFormula_of_not_tendsto (μ : ∀ n, PMF (L.Structure (Fin n))) {k : ℕ}
    (hzo : ∀ φ : FiniteVariable.InfinitaryFormula.{w, u, v} L k, φ.freeVars = ∅ →
      Tendsto (fun n => infinitaryProb (μ n) φ) atTop (nhds 0) ∨
        Tendsto (fun n => infinitaryProb (μ n) φ) atTop (nhds 1))
    (P : ∀ n, L.Structure (Fin n) → Prop)
    (h0 : ¬Tendsto (fun n => structProb (μ n) (P n)) atTop (nhds 0))
    (h1 : ¬Tendsto (fun n => structProb (μ n) (P n)) atTop (nhds 1)) :
    ¬∃ φ : FiniteVariable.InfinitaryFormula.{w, u, v} L k, φ.freeVars = ∅ ∧
      ∀ᶠ n in atTop, ∀ S : L.Structure (Fin n), @RealizeInfinitary L (Fin n) S k φ ↔ P n S := by
  rintro ⟨φ, hφ, hev⟩
  have heq : (fun n => infinitaryProb (μ n) φ) =ᶠ[atTop] fun n => structProb (μ n) (P n) := by
    filter_upwards [hev] with n hn
    rw [infinitaryProb_def,
      show (fun S => @RealizeInfinitary L (Fin n) S k φ) = P n from funext fun S => propext (hn S)]
  rcases hzo φ hφ with h | h
  · exact h0 (h.congr' heq)
  · exact h1 (h.congr' heq)

/-- Enumerates the distinct elements `{b j | j ∈ S ∧ j ≠ i}` on the target side of a partial
isomorphism `PartialIsoOn L S a b` as an injective tuple `x : Fin m → N` of length `m < k`,
together with the matching source tuple `y : Fin m → M`. -/
private theorem exists_distinct_pebble_enum {M N : Type*} [L.Structure M] [L.Structure N] {k : ℕ}
    {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N} (h : PartialIsoOn L S a b) (i : Fin k) :
    ∃ (m : ℕ) (_ : m < k) (x : Fin m → N) (y : Fin m → M) (pos : ∀ j ∈ S, j ≠ i → Fin m),
      Function.Injective x ∧
      ∀ (j : Fin k) (hj : j ∈ S) (hne : j ≠ i),
        x (pos j hj hne) = b j ∧ y (pos j hj hne) = a j := by
  classical
  let S' : Finset (Fin k) := Finset.univ.filter fun j => j ∈ S ∧ j ≠ i
  have hS'_sub : S' ⊆ Finset.univ.erase i := fun j hj => by
    simp only [S', Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact Finset.mem_erase.2 ⟨hj.2, Finset.mem_univ j⟩
  have hS'_lt : S'.card < k :=
    calc S'.card ≤ (Finset.univ.erase i).card := Finset.card_le_card hS'_sub
      _ < (Finset.univ : Finset (Fin k)).card :=
          Finset.card_erase_lt_of_mem (Finset.mem_univ i)
      _ = k := Finset.card_fin k
  let B : Finset N := S'.image b
  let m : ℕ := B.card
  have hm : m < k := Finset.card_image_le.trans_lt hS'_lt
  let e : Fin m ≃ B := B.equivFin.symm
  let x : Fin m → N := fun t => (e t).1
  have hx : Function.Injective x := Subtype.val_injective.comp e.injective
  let idx : Fin m → Fin k := fun t => (Finset.mem_image.1 (e t).2).choose
  have hidx_spec : ∀ t : Fin m, idx t ∈ S' ∧ b (idx t) = x t :=
    fun t => (Finset.mem_image.1 (e t).2).choose_spec
  let y : Fin m → M := fun t => a (idx t)
  let pos : ∀ j ∈ S, j ≠ i → Fin m := fun j hj hne =>
    e.symm ⟨b j, Finset.mem_image_of_mem b (Finset.mem_filter.2 ⟨Finset.mem_univ j, hj, hne⟩)⟩
  refine ⟨m, hm, x, y, pos, hx, fun j hj hne => ?_⟩
  have hxp : x (pos j hj hne) = b j := congrArg Subtype.val (e.apply_symm_apply _)
  have hidxS : idx (pos j hj hne) ∈ S := (Finset.mem_filter.1 (hidx_spec (pos j hj hne)).1).2.1
  refine ⟨hxp, (h.eq_iff (idx (pos j hj hne)) hidxS j hj).2
    ((hidx_spec (pos j hj hne)).2.trans hxp)⟩

end GeneralTransfer

/-! ### Simple graphs and `G(Fin n, p)` -/

namespace graph

/-- A simple graph `G` satisfies an `L^k_{∞ω}` formula `φ` in the language of graphs if
`G.structure` satisfies `φ` at every `k`-tuple of vertices. -/
def SatisfiesInfinitary {V : Type*} (G : SimpleGraph V) {k : ℕ}
    (φ : FiniteVariable.InfinitaryFormula.{w, 0, 0} Language.graph k) : Prop :=
  @RealizeInfinitary Language.graph V G.structure k φ

theorem satisfiesInfinitary_iff_realize {V : Type*} (G : SimpleGraph V) {k : ℕ}
    {φ : FiniteVariable.InfinitaryFormula.{w, 0, 0} Language.graph k} (hφ : φ.freeVars = ∅)
    (a : Fin k → V) :
    SatisfiesInfinitary G φ ↔ (letI := G.structure; φ.Realize a) := by
  let _ := G.structure
  exact realizeInfinitary_iff_realize hφ a

theorem satisfiesInfinitary_not {V : Type*} [Nonempty V] (G : SimpleGraph V) {k : ℕ}
    {φ : FiniteVariable.InfinitaryFormula.{w, 0, 0} Language.graph k} (hφ : φ.freeVars = ∅) :
    SatisfiesInfinitary G φ.not ↔ ¬SatisfiesInfinitary G φ := by
  let _ := G.structure
  exact realizeInfinitary_not hφ

theorem randomGraphProb_satisfiesInfinitary_eq (n : ℕ) {k : ℕ}
    (φ : FiniteVariable.InfinitaryFormula.{w, 0, 0} Language.graph k) :
    randomGraphProb n (fun G => SatisfiesInfinitary G φ) =
      infinitaryProb (randomGraphStructure n) φ :=
  randomGraphProb_structure_eq n fun S => @RealizeInfinitary Language.graph (Fin n) S k φ

/-- **Forth step for `< k` pebbles on simple graphs.** If `H` satisfies all `< k`-extension axioms,
any partial isomorphism of placed pebbles from `G` to `H` extends across any single-pebble move on
`G`. -/
private theorem forth_partialIsoOn_of_satisfies_extensionAxiom_lt {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) {k : ℕ}
    (hH : ∀ m < k, ∀ s : Fin m → Bool, Satisfies H (extensionAxiom m s))
    {S : Set (Fin k)} {a : Fin k → V} {b : Fin k → W}
    (h : letI := G.structure; letI := H.structure; PartialIsoOn Language.graph S a b)
    (i : Fin k) (c : V) :
    ∃ d : W, letI := G.structure; letI := H.structure;
      PartialIsoOn Language.graph (insert i S) (Function.update a i c) (Function.update b i d) := by
  classical
  let _ := G.structure
  let _ := H.structure
  by_cases hmem : ∃ j ∈ S, j ≠ i ∧ a j = c
  · obtain ⟨j₀, hj₀S, -, haj₀⟩ := hmem
    exact ⟨b j₀, PartialIsoOn.update_of_mem h hj₀S haj₀⟩
  · push Not at hmem
    obtain ⟨m, hm, x, y, pos, hx, hpos⟩ := exists_distinct_pebble_enum h i
    let s : Fin m → Bool := fun t => decide (G.Adj c (y t))
    obtain ⟨d, hd_ne, hd_adj⟩ :=
      (satisfies_extensionAxiom_iff H m s).1 (hH m hm s) x hx
    have hd_fresh : ∀ j ∈ S, j ≠ i → d ≠ b j :=
      fun j hj hne hdb => hd_ne (pos j hj hne) (hdb.trans (hpos j hj hne).1.symm)
    have hj_adj : ∀ j ∈ S, j ≠ i → (G.Adj c (a j) ↔ H.Adj d (b j)) := by
      intro j hj hne
      have hadj := hd_adj (pos j hj hne)
      simp only [s, decide_eq_true_iff, (hpos j hj hne).1, (hpos j hj hne).2] at hadj
      exact hadj.symm
    refine ⟨d, (partialIsoOn_graph_iff (G := G) (H := H)).2 ?_⟩
    intro r hr q hq
    refine ⟨h.update_eq_iff_of_fresh hmem hd_fresh hr hq, ?_⟩
    by_cases hri : r = i <;> by_cases hqi : q = i
    · subst hri; subst hqi
      simp only [Function.update_self, SimpleGraph.irrefl]
    · subst hri
      have hqS : q ∈ S := (Set.mem_insert_iff.1 hq).resolve_left hqi
      simp only [Function.update_self, Function.update_of_ne hqi]
      exact hj_adj q hqS hqi
    · subst hqi
      have hrS : r ∈ S := (Set.mem_insert_iff.1 hr).resolve_left hri
      simp only [Function.update_self, Function.update_of_ne hri]
      exact ⟨fun hadj => ((hj_adj r hrS hri).1 hadj.symm).symm,
        fun hadj => ((hj_adj r hrS hri).2 hadj.symm).symm⟩
    · have hrS : r ∈ S := (Set.mem_insert_iff.1 hr).resolve_left hri
      have hqS : q ∈ S := (Set.mem_insert_iff.1 hq).resolve_left hqi
      simp only [Function.update_of_ne hri, Function.update_of_ne hqi]
      exact (((partialIsoOn_graph_iff (G := G) (H := H)).1 h) r hrS q hqS).2

/-- **`< k`-extension axioms yield a `k`-pebble back-and-forth invariant on simple graphs**
([KolaitisVardi1992]). If both `G` and `H` satisfy all `< k`-extension axioms, then
`PartialIsoOn Language.graph` is an `IsPebbleBackAndForth` invariant between `G` and `H`. -/
theorem isPebbleBackAndForth_of_satisfies_extensionAxiom_lt {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) {k : ℕ}
    (hG : ∀ m < k, ∀ s : Fin m → Bool, Satisfies G (extensionAxiom m s))
    (hH : ∀ m < k, ∀ s : Fin m → Bool, Satisfies H (extensionAxiom m s)) :
    letI := G.structure
    letI := H.structure
    IsPebbleBackAndForth Language.graph
      (PartialIsoOn Language.graph (M := V) (N := W) (k := k)) := by
  let _ := G.structure
  let _ := H.structure
  refine ⟨fun h => h, fun h i c => forth_partialIsoOn_of_satisfies_extensionAxiom_lt G H hH h i c,
    fun h i d => ?_⟩
  obtain ⟨c, hc⟩ := forth_partialIsoOn_of_satisfies_extensionAxiom_lt H G hG h.symm i d
  exact ⟨c, hc.symm⟩

/-- Every nonempty simple graph satisfying all `< k`-extension axioms agrees with the Rado graph on
every closed `L^k_{∞ω}` formula (at any index universe `w` and any quantifier depth). -/
theorem satisfiesInfinitary_iff_radoGraph_of_extensionAxiom_lt {V : Type*} [Nonempty V]
    (G : SimpleGraph V) {k : ℕ}
    (hG : ∀ m < k, ∀ s : Fin m → Bool, Satisfies G (extensionAxiom m s))
    {φ : FiniteVariable.InfinitaryFormula.{w, 0, 0} Language.graph k} (hφ : φ.freeVars = ∅) :
    SatisfiesInfinitary G φ ↔ SatisfiesInfinitary SimpleGraph.radoGraph φ := by
  let _ := G.structure
  let _ := SimpleGraph.radoGraph.structure
  have hInv := isPebbleBackAndForth_of_satisfies_extensionAxiom_lt G SimpleGraph.radoGraph hG
    fun m _ s => satisfies_extensionAxiom_radoGraph m s
  let a : Fin k → V := fun _ => Classical.arbitrary V
  let b : Fin k → ℕ := fun _ => 0
  exact realizeInfinitary_iff_of_isPebbleBackAndForth hInv (partialIsoOn_empty a b) hφ

private noncomputable def graphExtensionSentence (k : ℕ) : Language.graph.Sentence :=
  BoundedFormula.iInf fun q : (m : Fin k) × (Fin m.1 → Bool) => extensionAxiom q.1.1 q.2

private theorem satisfies_graphExtensionSentence_iff {V : Type*} (G : SimpleGraph V) (k : ℕ) :
    Satisfies G (graphExtensionSentence k) ↔
      ∀ m < k, ∀ s : Fin m → Bool, Satisfies G (extensionAxiom m s) := by
  let _ := G.structure
  change @BoundedFormula.Realize Language.graph V G.structure Empty 0
      (graphExtensionSentence k) default default ↔ _
  simp only [graphExtensionSentence, BoundedFormula.realize_iInf, Sigma.forall]
  refine ⟨fun h m hm s => h ⟨m, hm⟩ s, fun h ⟨m, hm⟩ s => h m hm s⟩

private theorem tendsto_binomialRandom_real_forall_extensionAxiom_lt {p : I}
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (k : ℕ) :
    Tendsto (fun n => G(Fin n, p).real
      {G | ∀ m < k, ∀ s : Fin m → Bool, Satisfies G (extensionAxiom m s)}) atTop (nhds 1) := by
  have hrado : Satisfies SimpleGraph.radoGraph (graphExtensionSentence k) :=
    (satisfies_graphExtensionSentence_iff SimpleGraph.radoGraph k).2
      fun m _ s => satisfies_extensionAxiom_radoGraph m s
  have h1 := (tendsto_binomialRandom_real_one_iff_radoGraph hp0 hp1 (graphExtensionSentence k)).2
    hrado
  refine h1.congr fun n => ?_
  congr 1
  ext G
  exact satisfies_graphExtensionSentence_iff G k

/-- If a closed `L^k_{∞ω}` formula `φ` holds in the Rado graph, then it holds in `G(Fin n, p)` with
probability tending to `1` for every constant `0 < p < 1`. -/
theorem tendsto_binomialRandom_real_infinitary_one_of_radoGraph {p : I} (hp0 : 0 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) {k : ℕ}
    {φ : FiniteVariable.InfinitaryFormula.{w, 0, 0} Language.graph k} (hφ : φ.freeVars = ∅)
    (hrado : SatisfiesInfinitary SimpleGraph.radoGraph φ) :
    Tendsto (fun n => G(Fin n, p).real {G | SatisfiesInfinitary G φ}) atTop (nhds 1) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_binomialRandom_real_forall_extensionAxiom_lt hp0 hp1 k) tendsto_const_nhds ?_
    (Eventually.of_forall fun _ => (measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine measureReal_mono fun G hG => ?_
  exact (satisfiesInfinitary_iff_radoGraph_of_extensionAxiom_lt G hG hφ).2 hrado

/-- If a closed `L^k_{∞ω}` formula `φ` fails in the Rado graph, then it holds in `G(Fin n, p)` with
probability tending to `0` for every constant `0 < p < 1`. -/
theorem tendsto_binomialRandom_real_infinitary_zero_of_not_radoGraph {p : I} (hp0 : 0 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) {k : ℕ}
    {φ : FiniteVariable.InfinitaryFormula.{w, 0, 0} Language.graph k} (hφ : φ.freeVars = ∅)
    (hrado : ¬SatisfiesInfinitary SimpleGraph.radoGraph φ) :
    Tendsto (fun n => G(Fin n, p).real {G | SatisfiesInfinitary G φ}) atTop (nhds 0) := by
  have hnot_fv : φ.not.freeVars = ∅ := by
    simp only [FiniteVariable.InfinitaryFormula.freeVars_not, hφ]
  have hnot_rado : SatisfiesInfinitary SimpleGraph.radoGraph φ.not :=
    (satisfiesInfinitary_not SimpleGraph.radoGraph hφ).2 hrado
  have h1 := tendsto_binomialRandom_real_infinitary_one_of_radoGraph hp0 hp1 hnot_fv hnot_rado
  have hsub := h1.const_sub 1
  simp only [sub_self] at hsub
  refine hsub.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hset : {G : SimpleGraph (Fin n) | SatisfiesInfinitary G φ.not} =
      {G : SimpleGraph (Fin n) | SatisfiesInfinitary G φ}ᶜ :=
    Set.ext fun G => by
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, satisfiesInfinitary_not G hφ]
  rw [hset, probReal_compl_eq_one_sub (Set.toFinite _).measurableSet, sub_sub_cancel]

/-- **The Kolaitis–Vardi `0-1` law for `G(Fin n, p)`** ([KolaitisVardi1992]). For every constant
`0 < p < 1` and every closed `L^k_{∞ω}` formula `φ` in the language of graphs, the probability that
`G(Fin n, p)` satisfies `φ` tends to `0` or to `1` as `n → ∞`. -/
theorem binomialRandom_infinitary_zero_one_law {p : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {k : ℕ} {φ : FiniteVariable.InfinitaryFormula.{w, 0, 0} Language.graph k}
    (hφ : φ.freeVars = ∅) :
    Tendsto (fun n => G(Fin n, p).real {G | SatisfiesInfinitary G φ}) atTop (nhds 0) ∨
      Tendsto (fun n => G(Fin n, p).real {G | SatisfiesInfinitary G φ}) atTop (nhds 1) := by
  by_cases hrado : SatisfiesInfinitary SimpleGraph.radoGraph φ
  · exact Or.inr (tendsto_binomialRandom_real_infinitary_one_of_radoGraph hp0 hp1 hφ hrado)
  · exact Or.inl (tendsto_binomialRandom_real_infinitary_zero_of_not_radoGraph hp0 hp1 hφ hrado)

/-- **Characterization of the almost-sure `L^k_{∞ω}` theory of `G(Fin n, p)`**
([KolaitisVardi1992]). For constant `0 < p < 1`, a closed `L^k_{∞ω}` formula holds in `G(Fin n, p)`
with probability tending to `1` if and only if it holds in the Rado graph. -/
theorem tendsto_binomialRandom_real_infinitary_one_iff_radoGraph {p : I} (hp0 : 0 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) {k : ℕ}
    {φ : FiniteVariable.InfinitaryFormula.{w, 0, 0} Language.graph k} (hφ : φ.freeVars = ∅) :
    Tendsto (fun n => G(Fin n, p).real {G | SatisfiesInfinitary G φ}) atTop (nhds 1) ↔
      SatisfiesInfinitary SimpleGraph.radoGraph φ := by
  refine ⟨fun h1 => ?_, tendsto_binomialRandom_real_infinitary_one_of_radoGraph hp0 hp1 hφ⟩
  by_contra hnot
  exact zero_ne_one (tendsto_nhds_unique
    (tendsto_binomialRandom_real_infinitary_zero_of_not_radoGraph hp0 hp1 hφ hnot) h1)

/-- For constant `0 < p < 1`, a closed `L^k_{∞ω}` formula holds in `G(Fin n, p)` with probability
tending to `0` if and only if it fails in the Rado graph. -/
theorem tendsto_binomialRandom_real_infinitary_zero_iff_radoGraph {p : I} (hp0 : 0 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) {k : ℕ}
    {φ : FiniteVariable.InfinitaryFormula.{w, 0, 0} Language.graph k} (hφ : φ.freeVars = ∅) :
    Tendsto (fun n => G(Fin n, p).real {G | SatisfiesInfinitary G φ}) atTop (nhds 0) ↔
      ¬SatisfiesInfinitary SimpleGraph.radoGraph φ := by
  refine ⟨fun h0 hrado => ?_,
    tendsto_binomialRandom_real_infinitary_zero_of_not_radoGraph hp0 hp1 hφ⟩
  exact zero_ne_one (tendsto_nhds_unique h0
    (tendsto_binomialRandom_real_infinitary_one_of_radoGraph hp0 hp1 hφ hrado))

private noncomputable def halfProb : I := ⟨1 / 2, by norm_num, by norm_num⟩

private theorem coe_halfProb : (halfProb : ℝ) = 1 / 2 := rfl

/-- **The Kolaitis–Vardi `0-1` law for the uniform random graph `G(n, 1/2)`**
([KolaitisVardi1992]). -/
theorem randomGraph_infinitary_zero_one_law {k : ℕ}
    {φ : FiniteVariable.InfinitaryFormula.{w, 0, 0} Language.graph k} (hφ : φ.freeVars = ∅) :
    Tendsto (fun n => randomGraphProb n fun G => SatisfiesInfinitary G φ) atTop (nhds 0) ∨
      Tendsto (fun n => randomGraphProb n fun G => SatisfiesInfinitary G φ) atTop (nhds 1) := by
  have h0 : 0 < (halfProb : ℝ) := by rw [coe_halfProb]; norm_num
  have h1 : (halfProb : ℝ) < 1 := by rw [coe_halfProb]; norm_num
  simpa only [binomialRandom_real_eq_randomGraphProb coe_halfProb] using
    binomialRandom_infinitary_zero_one_law h0 h1 hφ

/-- A closed `L^k_{∞ω}` formula holds almost surely in `G(n, 1/2)` iff it holds in the Rado
graph. -/
theorem tendsto_randomGraphProb_infinitary_one_iff_radoGraph {k : ℕ}
    {φ : FiniteVariable.InfinitaryFormula.{w, 0, 0} Language.graph k} (hφ : φ.freeVars = ∅) :
    Tendsto (fun n => randomGraphProb n fun G => SatisfiesInfinitary G φ) atTop (nhds 1) ↔
      SatisfiesInfinitary SimpleGraph.radoGraph φ := by
  have h0 : 0 < (halfProb : ℝ) := by rw [coe_halfProb]; norm_num
  have h1 : (halfProb : ℝ) < 1 := by rw [coe_halfProb]; norm_num
  simpa only [binomialRandom_real_eq_randomGraphProb coe_halfProb] using
    tendsto_binomialRandom_real_infinitary_one_iff_radoGraph h0 h1 hφ

/-- A closed `L^k_{∞ω}` formula holds almost never in `G(n, 1/2)` iff it fails in the Rado graph. -/
theorem tendsto_randomGraphProb_infinitary_zero_iff_radoGraph {k : ℕ}
    {φ : FiniteVariable.InfinitaryFormula.{w, 0, 0} Language.graph k} (hφ : φ.freeVars = ∅) :
    Tendsto (fun n => randomGraphProb n fun G => SatisfiesInfinitary G φ) atTop (nhds 0) ↔
      ¬SatisfiesInfinitary SimpleGraph.radoGraph φ := by
  have h0 : 0 < (halfProb : ℝ) := by rw [coe_halfProb]; norm_num
  have h1 : (halfProb : ℝ) < 1 := by rw [coe_halfProb]; norm_num
  simpa only [binomialRandom_real_eq_randomGraphProb coe_halfProb] using
    tendsto_binomialRandom_real_infinitary_zero_iff_radoGraph h0 h1 hφ

/-- **Independence of `p` for `L^k_{∞ω}`.** For constant `0 < p < 1`, a closed `L^k_{∞ω}` formula
holds almost surely in `G(Fin n, p)` if and only if it holds almost surely in `G(n, 1/2)`. -/
theorem tendsto_binomialRandom_real_infinitary_one_iff_tendsto_randomGraphProb {p : I}
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) {k : ℕ}
    {φ : FiniteVariable.InfinitaryFormula.{w, 0, 0} Language.graph k} (hφ : φ.freeVars = ∅) :
    Tendsto (fun n => G(Fin n, p).real {G | SatisfiesInfinitary G φ}) atTop (nhds 1) ↔
      Tendsto (fun n => randomGraphProb n fun G => SatisfiesInfinitary G φ) atTop (nhds 1) := by
  rw [tendsto_binomialRandom_real_infinitary_one_iff_radoGraph hp0 hp1 hφ,
    tendsto_randomGraphProb_infinitary_one_iff_radoGraph hφ]

/-- For constant `0 < p < 1`, a graph property whose probability in `G(Fin n, p)` tends neither to
`0` nor to `1` agrees on all sufficiently large graphs with no closed `L^k_{∞ω}` formula. -/
theorem not_exists_infinitaryFormula_of_not_tendsto_binomialRandom {p : I} (hp0 : 0 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (k : ℕ) (P : ∀ n, SimpleGraph (Fin n) → Prop)
    (h0 : ¬Tendsto (fun n => G(Fin n, p).real {G | P n G}) atTop (nhds 0))
    (h1 : ¬Tendsto (fun n => G(Fin n, p).real {G | P n G}) atTop (nhds 1)) :
    ¬∃ φ : FiniteVariable.InfinitaryFormula.{w, 0, 0} Language.graph k, φ.freeVars = ∅ ∧
      ∀ᶠ n in atTop, ∀ G : SimpleGraph (Fin n), SatisfiesInfinitary G φ ↔ P n G := by
  rintro ⟨φ, hφ, hev⟩
  have heq : (fun n => G(Fin n, p).real {G | SatisfiesInfinitary G φ}) =ᶠ[atTop]
      fun n => G(Fin n, p).real {G | P n G} := by
    filter_upwards [hev] with n hn
    congr 1
    ext G
    exact hn G
  rcases binomialRandom_infinitary_zero_one_law hp0 hp1 hφ with h | h
  · exact h0 (h.congr' heq)
  · exact h1 (h.congr' heq)

/-! #### Application: almost-sure connectivity of `G(Fin n, p)` via `L^3_{∞ω}` -/

/-- The Rado graph is connected (in fact of diameter at most `2`): any two vertices share a common
neighbour by the `2`-element extension property. -/
theorem radoGraph_connected : SimpleGraph.radoGraph.Connected := by
  refine ⟨fun u v => ?_⟩
  obtain ⟨z, -, -, hz⟩ := SimpleGraph.radoGraph_exists_adj (A := {u, v}) (B := ∅)
    (Finset.disjoint_empty_right _)
  have hzu : SimpleGraph.radoGraph.Adj z u := hz.1 u (Finset.mem_insert_self u {v})
  have hzv : SimpleGraph.radoGraph.Adj z v :=
    hz.1 v (Finset.mem_insert_of_mem (Finset.mem_singleton_self v))
  exact hzu.symm.reachable.trans hzv.reachable

/-- **Almost-sure connectivity of `G(Fin n, p)` as a consequence of the `L^3_{∞ω}` `0-1` law.**
Although connectivity is not first-order definable, it is defined on nonempty graphs by the closed
`L^3_{∞ω}` formula `connectedInfinitary` of unbounded quantifier rank and holds in the Rado graph,
so `G(Fin n, p)` is connected with probability tending to `1` for every constant `0 < p < 1`. -/
theorem tendsto_binomialRandom_real_connected {p : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Tendsto (fun n => G(Fin n, p).real {G | G.Connected}) atTop (nhds 1) := by
  let φ : FiniteVariable.InfinitaryFormula.{0, 0, 0} Language.graph 3 :=
    FiniteVariable.connectedInfinitary
  have hφ : φ.freeVars = ∅ := FiniteVariable.freeVars_connectedInfinitary
  have hrado : SatisfiesInfinitary SimpleGraph.radoGraph φ := by
    rw [satisfiesInfinitary_iff_realize SimpleGraph.radoGraph hφ (fun _ => 0)]
    exact (FiniteVariable.realize_connectedInfinitary_iff_connected
      SimpleGraph.radoGraph (fun _ => 0)).2 radoGraph_connected
  have h1 := tendsto_binomialRandom_real_infinitary_one_of_radoGraph hp0 hp1 hφ hrado
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  congr 1
  ext G
  simp only [Set.mem_ofPred_eq]
  have h0 : Fin n := ⟨0, hn⟩
  rw [satisfiesInfinitary_iff_realize G hφ (fun _ => h0)]
  exact FiniteVariable.realize_connectedInfinitary_iff_connected G (fun _ => h0)

end graph

/-! ### Finite relational vocabularies (`bernoulliStructure` and `uniformStructure`) -/

namespace Relational

variable {L : Language.{u, v}}

/-- **Forth step for `< k` pebbles over any language.** If `N` satisfies all `< k`-extension
properties (`HasExtension N p` for `m < k`), then any partial isomorphism of placed pebbles from
`M` to `N` extends across any single-pebble move on `M`. -/
private theorem forth_partialIsoOn_of_hasExtension_lt {M N : Type*} [L.Structure M]
    [L.Structure N] {k : ℕ} (hN : ∀ m < k, ∀ p : NewAtom L m → Bool, HasExtension N p)
    {S : Set (Fin k)} {a : Fin k → M} {b : Fin k → N} (h : PartialIsoOn L S a b)
    (i : Fin k) (c : M) :
    ∃ d : N, PartialIsoOn L (insert i S) (Function.update a i c) (Function.update b i d) := by
  classical
  by_cases hmem : ∃ j ∈ S, j ≠ i ∧ a j = c
  · obtain ⟨j₀, hj₀S, -, haj₀⟩ := hmem
    exact ⟨b j₀, PartialIsoOn.update_of_mem h hj₀S haj₀⟩
  · push Not at hmem
    obtain ⟨m, hm, x, y, pos, hx, hpos⟩ := exists_distinct_pebble_enum h i
    let p : NewAtom L m → Bool := fun atom =>
      decide (RelMap atom.symbol.2 ((Fin.cons c y : Fin (m + 1) → M) ∘ atom.args))
    obtain ⟨d, hd_ne, hd_rel⟩ := hN m hm p x hx
    have hd_fresh : ∀ j ∈ S, j ≠ i → d ≠ b j :=
      fun j hj hne hdb => hd_ne (pos j hj hne) (hdb.trans (hpos j hj hne).1.symm)
    refine ⟨d, ⟨fun r hr q hq => h.update_eq_iff_of_fresh hmem hd_fresh hr hq,
      fun {l} R f hf => ?_⟩⟩
    by_cases hall : ∀ q, f q ≠ i
    · have hfS : ∀ q, f q ∈ S := fun q => (Set.mem_insert_iff.1 (hf q)).resolve_left (hall q)
      have ha_eq : Function.update a i c ∘ f = a ∘ f :=
        funext fun q => by simp only [Function.comp_apply, Function.update_of_ne (hall q)]
      have hb_eq : Function.update b i d ∘ f = b ∘ f :=
        funext fun q => by simp only [Function.comp_apply, Function.update_of_ne (hall q)]
      rw [ha_eq, hb_eq]
      exact h.relMap_iff R f hfS
    · push Not at hall
      obtain ⟨q₀, hq₀⟩ := hall
      have hfS : ∀ q, f q ≠ i → f q ∈ S :=
        fun q hne => (Set.mem_insert_iff.1 (hf q)).resolve_left hne
      let τ : Fin l → Fin (m + 1) := fun q =>
        if hq : f q = i then 0 else (pos (f q) (hfS q hq) hq).succ
      have hτ0 : (0 : Fin (m + 1)) ∈ Set.range τ := ⟨q₀, by simp only [τ, hq₀, ↓reduceDIte]⟩
      let atom : NewAtom L m := ⟨⟨⟨l, R⟩, τ⟩, hτ0⟩
      have ha_eq : Function.update a i c ∘ f = (Fin.cons c y : Fin (m + 1) → M) ∘ τ := by
        funext q
        by_cases hq : f q = i
        · simp only [Function.comp_apply, τ, hq, ↓reduceDIte, Function.update_self,
            Fin.cons_zero]
        · simp only [Function.comp_apply, τ, hq, ↓reduceDIte, Function.update_of_ne hq,
            Fin.cons_succ, (hpos (f q) (hfS q hq) hq).2]
      have hb_eq : Function.update b i d ∘ f = (Fin.cons d x : Fin (m + 1) → N) ∘ τ := by
        funext q
        by_cases hq : f q = i
        · simp only [Function.comp_apply, τ, hq, ↓reduceDIte, Function.update_self,
            Fin.cons_zero]
        · simp only [Function.comp_apply, τ, hq, ↓reduceDIte, Function.update_of_ne hq,
            Fin.cons_succ, (hpos (f q) (hfS q hq) hq).1]
      rw [ha_eq, hb_eq]
      have hrel := hd_rel atom
      simp only [p, atom, decide_eq_true_iff] at hrel
      exact hrel.symm

/-- **`< k`-extension axioms yield a `k`-pebble back-and-forth invariant over any language**
([KolaitisVardi1992]). If both `M` and `N` satisfy `HasExtension` for all arities `m < k`, then
`PartialIsoOn L` is an `IsPebbleBackAndForth` invariant between `M` and `N`. -/
theorem isPebbleBackAndForth_of_hasExtension_lt {M N : Type*} [L.Structure M] [L.Structure N]
    {k : ℕ} (hM : ∀ m < k, ∀ p : NewAtom L m → Bool, HasExtension M p)
    (hN : ∀ m < k, ∀ p : NewAtom L m → Bool, HasExtension N p) :
    IsPebbleBackAndForth L (PartialIsoOn L (M := M) (N := N) (k := k)) := by
  refine ⟨fun h => h, fun h i c => forth_partialIsoOn_of_hasExtension_lt hN h i c, fun h i d => ?_⟩
  obtain ⟨c, hc⟩ := forth_partialIsoOn_of_hasExtension_lt hM h.symm i d
  exact ⟨c, hc.symm⟩

/-- Without nullary relation symbols, any two nonempty structures satisfying all `< k`-extension
properties agree on every closed `L^k_{∞ω}` formula. -/
theorem realizeInfinitary_iff_of_hasExtension_lt [IsEmpty (L.Relations 0)] {M N : Type*}
    [L.Structure M] [L.Structure N] [Nonempty M] [Nonempty N] {k : ℕ}
    (hM : ∀ m < k, ∀ p : NewAtom L m → Bool, HasExtension M p)
    (hN : ∀ m < k, ∀ p : NewAtom L m → Bool, HasExtension N p)
    {φ : FiniteVariable.InfinitaryFormula.{w, u, v} L k} (hφ : φ.freeVars = ∅) :
    RealizeInfinitary (M := M) φ ↔ RealizeInfinitary (M := N) φ := by
  let a : Fin k → M := fun _ => Classical.arbitrary M
  let b : Fin k → N := fun _ => Classical.arbitrary N
  exact realizeInfinitary_iff_of_isPebbleBackAndForth
    (isPebbleBackAndForth_of_hasExtension_lt hM hN) (partialIsoOn_empty a b) hφ

section FiniteRelational

variable [L.IsRelational] [Finite (Σ l, L.Relations l)] [IsEmpty (L.Relations 0)]

omit [L.IsRelational] [IsEmpty (L.Relations 0)] in
private noncomputable def relationalExtensionFinset (k : ℕ) : Finset L.Sentence := by
  classical
  let _ : Finite ((m : Fin k) × (NewAtom L m.1 → Bool)) := inferInstance
  let _ : Fintype ((m : Fin k) × (NewAtom L m.1 → Bool)) := Fintype.ofFinite _
  exact Finset.univ.image fun q : (m : Fin k) × (NewAtom L m.1 → Bool) =>
    extensionAxiom q.1.1 q.2

omit [L.IsRelational] [IsEmpty (L.Relations 0)] in
private theorem mem_relationalExtensionFinset {k : ℕ} {ψ : L.Sentence} :
    ψ ∈ relationalExtensionFinset (L := L) k ↔
      ∃ (m : Fin k) (p : NewAtom L m.1 → Bool), extensionAxiom m.1 p = ψ := by
  classical
  simp only [relationalExtensionFinset, Finset.mem_image, Finset.mem_univ, true_and, Sigma.exists]

omit [L.IsRelational] in
private theorem backAndForth_of_relationalExtensionFinset {M₀ : Type*} [L.Structure M₀]
    [M₀ ⊨ extensionTheory L] {k : ℕ} (n : ℕ) (_hne : Nonempty (Fin n))
    (S : L.Structure (Fin n))
    (hS : ∀ ψ ∈ relationalExtensionFinset (L := L) k, @Sentence.Realize L (Fin n) S ψ) :
    ∃ (Inv : Set (Fin k) → (Fin k → Fin n) → (Fin k → M₀) → Prop)
      (a : Fin k → Fin n) (b : Fin k → M₀),
      @IsPebbleBackAndForth L (Fin n) M₀ S _ k Inv ∧ Inv ∅ a b := by
  let _ := S
  have : Infinite M₀ := infinite_of_model_extensionTheory (L := L)
  have hS_ext : ∀ m < k, ∀ p : NewAtom L m → Bool, HasExtension (Fin n) p := by
    intro m hm p
    exact (realize_extensionAxiom p).1
      (hS (extensionAxiom m p) (mem_relationalExtensionFinset.2 ⟨⟨m, hm⟩, p, rfl⟩))
  have hM₀_ext : ∀ m < k, ∀ p : NewAtom L m → Bool, HasExtension M₀ p :=
    fun m _ p => (model_extensionTheory_iff.1 ‹M₀ ⊨ extensionTheory L›) m p
  let a : Fin k → Fin n := fun _ => Classical.arbitrary (Fin n)
  let b : Fin k → M₀ := fun _ => Classical.arbitrary M₀
  exact ⟨PartialIsoOn L, a, b, isPebbleBackAndForth_of_hasExtension_lt hS_ext hM₀_ext,
    partialIsoOn_empty a b⟩

omit [IsEmpty (L.Relations 0)] in
private theorem tendsto_relationalExtensionFinset_uniform {k : ℕ}
    {ψ : L.Sentence} (hψ : ψ ∈ relationalExtensionFinset (L := L) k) :
    Tendsto (fun n => sentenceProb (uniformStructure n) ψ) atTop (nhds 1) := by
  obtain ⟨m, q, rfl⟩ := mem_relationalExtensionFinset.1 hψ
  exact tendsto_sentenceProb_extensionAxiom m.1 q

omit [IsEmpty (L.Relations 0)] in
private theorem tendsto_relationalExtensionFinset_bernoulli
    {p : (Σ l, L.Relations l) → I} (hp : ∀ R, 0 < (p R : ℝ) ∧ (p R : ℝ) < 1) {k : ℕ}
    {ψ : L.Sentence} (hψ : ψ ∈ relationalExtensionFinset (L := L) k) :
    Tendsto (fun n => sentenceProb (bernoulliStructure p n) ψ) atTop (nhds 1) := by
  obtain ⟨m, q, rfl⟩ := mem_relationalExtensionFinset.1 hψ
  exact tendsto_sentenceProb_bernoulliStructure_extensionAxiom hp m.1 q

/-- **The Kolaitis–Vardi `0-1` law for `uniformStructure n`** over a finite relational vocabulary
without nullary relation symbols ([KolaitisVardi1992]). For every closed `L^k_{∞ω}` formula `φ`,
the probability that a uniform random `L`-structure on `Fin n` satisfies `φ` tends to `0` or to
`1` as `n → ∞`. -/
theorem uniformStructure_infinitary_zero_one_law {k : ℕ}
    {φ : FiniteVariable.InfinitaryFormula.{w, u, v} L k} (hφ : φ.freeVars = ∅) :
    Tendsto (fun n => infinitaryProb (uniformStructure n) φ) atTop (nhds 0) ∨
      Tendsto (fun n => infinitaryProb (uniformStructure n) φ) atTop (nhds 1) := by
  obtain ⟨M₀⟩ := isSatisfiable_extensionTheory (L := L)
  have : Infinite M₀ := infinite_of_model_extensionTheory (L := L)
  exact infinitary_zero_one_law_of_finset uniformStructure
    (relationalExtensionFinset (L := L) k)
    (fun _ hψ => tendsto_relationalExtensionFinset_uniform hψ)
    (backAndForth_of_relationalExtensionFinset (M₀ := M₀)) hφ

/-- **The Kolaitis–Vardi `0-1` law for `bernoulliStructure p n`** over a finite relational
vocabulary without nullary relation symbols ([KolaitisVardi1992]). For constant probabilities
`0 < p R < 1` per relation symbol and every closed `L^k_{∞ω}` formula `φ`, the probability that
`bernoulliStructure p n` satisfies `φ` tends to `0` or to `1` as `n → ∞`. -/
theorem bernoulliStructure_infinitary_zero_one_law {p : (Σ l, L.Relations l) → I}
    (hp : ∀ R, 0 < (p R : ℝ) ∧ (p R : ℝ) < 1) {k : ℕ}
    {φ : FiniteVariable.InfinitaryFormula.{w, u, v} L k} (hφ : φ.freeVars = ∅) :
    Tendsto (fun n => infinitaryProb (bernoulliStructure p n) φ) atTop (nhds 0) ∨
      Tendsto (fun n => infinitaryProb (bernoulliStructure p n) φ) atTop (nhds 1) := by
  obtain ⟨M₀⟩ := isSatisfiable_extensionTheory (L := L)
  have : Infinite M₀ := infinite_of_model_extensionTheory (L := L)
  exact infinitary_zero_one_law_of_finset (bernoulliStructure p)
    (relationalExtensionFinset (L := L) k)
    (fun _ hψ => tendsto_relationalExtensionFinset_bernoulli hp hψ)
    (backAndForth_of_relationalExtensionFinset (M₀ := M₀)) hφ

/-- A closed `L^k_{∞ω}` formula holds almost surely in `bernoulliStructure p n` (`0 < p R < 1`) iff
it holds in any model `M₀` of `extensionTheory L`. -/
theorem tendsto_infinitaryProb_bernoulliStructure_one_iff_model {M₀ : Type*} [L.Structure M₀]
    [M₀ ⊨ extensionTheory L] {p : (Σ l, L.Relations l) → I}
    (hp : ∀ R, 0 < (p R : ℝ) ∧ (p R : ℝ) < 1) {k : ℕ}
    {φ : FiniteVariable.InfinitaryFormula.{w, u, v} L k} (hφ : φ.freeVars = ∅) :
    Tendsto (fun n => infinitaryProb (bernoulliStructure p n) φ) atTop (nhds 1) ↔
      RealizeInfinitary (M := M₀) φ := by
  have : Infinite M₀ := infinite_of_model_extensionTheory (L := L)
  refine ⟨fun h1 => ?_, fun hM₀ => tendsto_infinitaryProb_one_of_finset (bernoulliStructure p)
    (relationalExtensionFinset (L := L) k)
    (fun _ hψ => tendsto_relationalExtensionFinset_bernoulli hp hψ)
    (backAndForth_of_relationalExtensionFinset (M₀ := M₀)) hφ hM₀⟩
  by_contra hnot
  exact zero_ne_one (tendsto_nhds_unique
    (tendsto_infinitaryProb_zero_of_finset (bernoulliStructure p)
      (relationalExtensionFinset (L := L) k)
      (fun _ hψ => tendsto_relationalExtensionFinset_bernoulli hp hψ)
      (backAndForth_of_relationalExtensionFinset (M₀ := M₀)) hφ hnot) h1)

/-- A closed `L^k_{∞ω}` formula holds almost surely in `uniformStructure n` iff it holds in any
model `M₀` of `extensionTheory L`. -/
theorem tendsto_infinitaryProb_uniformStructure_one_iff_model {M₀ : Type*} [L.Structure M₀]
    [M₀ ⊨ extensionTheory L] {k : ℕ}
    {φ : FiniteVariable.InfinitaryFormula.{w, u, v} L k} (hφ : φ.freeVars = ∅) :
    Tendsto (fun n => infinitaryProb (uniformStructure n) φ) atTop (nhds 1) ↔
      RealizeInfinitary (M := M₀) φ := by
  have : Infinite M₀ := infinite_of_model_extensionTheory (L := L)
  refine ⟨fun h1 => ?_, fun hM₀ => tendsto_infinitaryProb_one_of_finset uniformStructure
    (relationalExtensionFinset (L := L) k)
    (fun _ hψ => tendsto_relationalExtensionFinset_uniform hψ)
    (backAndForth_of_relationalExtensionFinset (M₀ := M₀)) hφ hM₀⟩
  by_contra hnot
  exact zero_ne_one (tendsto_nhds_unique
    (tendsto_infinitaryProb_zero_of_finset uniformStructure
      (relationalExtensionFinset (L := L) k)
      (fun _ hψ => tendsto_relationalExtensionFinset_uniform hψ)
      (backAndForth_of_relationalExtensionFinset (M₀ := M₀)) hφ hnot) h1)

/-- A closed `L^k_{∞ω}` formula holds almost never in `bernoulliStructure p n` (`0 < p R < 1`) iff
it fails in any model `M₀` of `extensionTheory L`. -/
theorem tendsto_infinitaryProb_bernoulliStructure_zero_iff_model {M₀ : Type*} [L.Structure M₀]
    [M₀ ⊨ extensionTheory L] {p : (Σ l, L.Relations l) → I}
    (hp : ∀ R, 0 < (p R : ℝ) ∧ (p R : ℝ) < 1) {k : ℕ}
    {φ : FiniteVariable.InfinitaryFormula.{w, u, v} L k} (hφ : φ.freeVars = ∅) :
    Tendsto (fun n => infinitaryProb (bernoulliStructure p n) φ) atTop (nhds 0) ↔
      ¬RealizeInfinitary (M := M₀) φ := by
  have : Infinite M₀ := infinite_of_model_extensionTheory (L := L)
  refine ⟨fun h0 hM₀ => ?_,
    fun hnot => tendsto_infinitaryProb_zero_of_finset (bernoulliStructure p)
      (relationalExtensionFinset (L := L) k)
      (fun _ hψ => tendsto_relationalExtensionFinset_bernoulli hp hψ)
      (backAndForth_of_relationalExtensionFinset (M₀ := M₀)) hφ hnot⟩
  exact zero_ne_one (tendsto_nhds_unique h0
    (tendsto_infinitaryProb_one_of_finset (bernoulliStructure p)
      (relationalExtensionFinset (L := L) k)
      (fun _ hψ => tendsto_relationalExtensionFinset_bernoulli hp hψ)
      (backAndForth_of_relationalExtensionFinset (M₀ := M₀)) hφ hM₀))

/-- A closed `L^k_{∞ω}` formula holds almost never in `uniformStructure n` iff it fails in any
model `M₀` of `extensionTheory L`. -/
theorem tendsto_infinitaryProb_uniformStructure_zero_iff_model {M₀ : Type*} [L.Structure M₀]
    [M₀ ⊨ extensionTheory L] {k : ℕ}
    {φ : FiniteVariable.InfinitaryFormula.{w, u, v} L k} (hφ : φ.freeVars = ∅) :
    Tendsto (fun n => infinitaryProb (uniformStructure n) φ) atTop (nhds 0) ↔
      ¬RealizeInfinitary (M := M₀) φ := by
  have : Infinite M₀ := infinite_of_model_extensionTheory (L := L)
  refine ⟨fun h0 hM₀ => ?_,
    fun hnot => tendsto_infinitaryProb_zero_of_finset uniformStructure
      (relationalExtensionFinset (L := L) k)
      (fun _ hψ => tendsto_relationalExtensionFinset_uniform hψ)
      (backAndForth_of_relationalExtensionFinset (M₀ := M₀)) hφ hnot⟩
  exact zero_ne_one (tendsto_nhds_unique h0
    (tendsto_infinitaryProb_one_of_finset uniformStructure
      (relationalExtensionFinset (L := L) k)
      (fun _ hψ => tendsto_relationalExtensionFinset_uniform hψ)
      (backAndForth_of_relationalExtensionFinset (M₀ := M₀)) hφ hM₀))

/-- **Independence of `p` for relational `L^k_{∞ω}`.** For constant probabilities `0 < p R < 1`,
a closed `L^k_{∞ω}` formula holds almost surely in `bernoulliStructure p n` iff it holds almost
surely in `uniformStructure n`. -/
theorem tendsto_infinitaryProb_bernoulliStructure_one_iff_uniformStructure
    {p : (Σ l, L.Relations l) → I} (hp : ∀ R, 0 < (p R : ℝ) ∧ (p R : ℝ) < 1) {k : ℕ}
    {φ : FiniteVariable.InfinitaryFormula.{w, u, v} L k} (hφ : φ.freeVars = ∅) :
    Tendsto (fun n => infinitaryProb (bernoulliStructure p n) φ) atTop (nhds 1) ↔
      Tendsto (fun n => infinitaryProb (uniformStructure n) φ) atTop (nhds 1) := by
  obtain ⟨M₀⟩ := isSatisfiable_extensionTheory (L := L)
  rw [tendsto_infinitaryProb_bernoulliStructure_one_iff_model (M₀ := M₀) hp hφ,
    tendsto_infinitaryProb_uniformStructure_one_iff_model (M₀ := M₀) hφ]

/-- **Parity of the number of elements is not definable in `L^k_{∞ω}`** over any finite relational
vocabulary without nullary relation symbols: no closed `L^k_{∞ω}` formula agrees with `Even n` on
all sufficiently large structures. -/
theorem not_exists_infinitaryFormula_even_card (k : ℕ) :
    ¬∃ φ : FiniteVariable.InfinitaryFormula.{w, u, v} L k, φ.freeVars = ∅ ∧
      ∀ᶠ n in atTop, ∀ S : L.Structure (Fin n), @RealizeInfinitary L (Fin n) S k φ ↔ Even n :=
  not_exists_infinitaryFormula_of_not_tendsto uniformStructure
    (fun _ hφ => uniformStructure_infinitary_zero_one_law hφ) (fun n _ => Even n)
    (not_tendsto_structProb_even uniformStructure 0)
    (not_tendsto_structProb_even uniformStructure 1)

end FiniteRelational

end Relational

end Cslib.Logic.FO
