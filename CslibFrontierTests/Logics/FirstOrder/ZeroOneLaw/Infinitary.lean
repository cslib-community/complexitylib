/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Logics.FirstOrder.ZeroOneLaw.Infinitary

/-!
# Tests for the Kolaitis–Vardi `0-1` Law for `L^k_{∞ω}`

Covers:
1. **Unbounded-rank `L^3_{∞ω}` sentences on `G(Fin n, 1/3)` and `G(n, 1/2)`:**
   `connectedInfinitary` holds with probability tending to `1` and its negation ("disconnected")
   with probability tending to `0`, plus independence of `p` and non-definability of `Even n` in
   `L^k_{∞ω}` on graphs.
2. **Boundary counterexamples (`p = 0` and `p = 1`) for `L^3_{∞ω}`:**
   `G(Fin n, 0)` is disconnected for all `n ≥ 2` (`probability = 0`, refuting the Rado-graph
   characterization of `connectedInfinitary` at `p = 0`), and `G(Fin n, 1)` has no non-adjacent
   distinct pair (`probability = 0`, refuting the Rado-graph characterization at `p = 1`).
3. **General multi-arity finite relational vocabularies (`bernoulliStructure` and
   `uniformStructure`):**
   A relational vocabulary `HyperColorLang` with a unary predicate (`1/4`) and a ternary relation
   (`3/5`), plus a nullary-relation counterexample showing `[IsEmpty (L.Relations 0)]` is needed
   even at `k = 0`.
-/

open FirstOrder Language Structure Cslib.Logic.FO Cslib.Logic.FO.FiniteVariable
open Cslib.Logic.FO.graph MeasureTheory unitInterval Filter
open scoped SimpleGraph
open SimpleGraph (radoGraph)

namespace CslibFrontierTests.Logics.FirstOrder.ZeroOneLaw.Infinitary

/-! ### 1. `G(Fin n, 1/3)` and `G(n, 1/2)` on unbounded-rank `L^3_{∞ω}` sentences -/

/-- Constant probability `1/3 ∈ [0, 1]`. -/
noncomputable def third : I := ⟨1 / 3, by norm_num, by norm_num⟩

theorem third_pos : 0 < (third : ℝ) := by
  change (0 : ℝ) < 1 / 3
  norm_num

theorem third_lt_one : (third : ℝ) < 1 := by
  change (1 / 3 : ℝ) < 1
  norm_num

/-- `connectedInfinitary` (`L^3_{∞ω}`, unbounded quantifier depth) holds in `G(Fin n, 1/3)` with
probability tending to `1`. -/
example :
    Tendsto (fun n => G(Fin n, third).real
      {G | SatisfiesInfinitary G
        (connectedInfinitary : InfinitaryFormula.{0, 0, 0} Language.graph 3)})
      atTop (nhds 1) := by
  rw [tendsto_binomialRandom_real_infinitary_one_iff_radoGraph third_pos third_lt_one
    freeVars_connectedInfinitary,
    satisfiesInfinitary_iff_realize radoGraph freeVars_connectedInfinitary (fun _ => 0)]
  exact (realize_connectedInfinitary_iff_connected radoGraph (fun _ => 0)).2 radoGraph_connected

/-- `connectedInfinitary.not` ("disconnected") holds in `G(Fin n, 1/3)` with probability tending
to `0`. -/
example :
    Tendsto (fun n => G(Fin n, third).real
      {G | SatisfiesInfinitary G
        (connectedInfinitary : InfinitaryFormula.{0, 0, 0} Language.graph 3).not})
      atTop (nhds 0) := by
  have hfv : (connectedInfinitary : InfinitaryFormula.{0, 0, 0} Language.graph 3).not.freeVars =
      ∅ := by
    simp only [InfinitaryFormula.freeVars_not, freeVars_connectedInfinitary]
  rw [tendsto_binomialRandom_real_infinitary_zero_iff_radoGraph third_pos third_lt_one hfv,
    satisfiesInfinitary_not radoGraph freeVars_connectedInfinitary, not_not,
    satisfiesInfinitary_iff_realize radoGraph freeVars_connectedInfinitary (fun _ => 0)]
  exact (realize_connectedInfinitary_iff_connected radoGraph (fun _ => 0)).2 radoGraph_connected

/-- Direct graph-property form: `G(Fin n, 1/3)` is connected with probability tending to `1`. -/
example : Tendsto (fun n => G(Fin n, third).real {G | G.Connected}) atTop (nhds 1) :=
  tendsto_binomialRandom_real_connected third_pos third_lt_one

/-- `G(n, 1/2)` satisfies `connectedInfinitary` with probability tending to `1`. -/
example :
    Tendsto (fun n => randomGraphProb n fun G =>
      SatisfiesInfinitary G (connectedInfinitary : InfinitaryFormula.{0, 0, 0} Language.graph 3))
      atTop (nhds 1) := by
  rw [tendsto_randomGraphProb_infinitary_one_iff_radoGraph freeVars_connectedInfinitary,
    satisfiesInfinitary_iff_realize radoGraph freeVars_connectedInfinitary (fun _ => 0)]
  exact (realize_connectedInfinitary_iff_connected radoGraph (fun _ => 0)).2 radoGraph_connected

/-- Parity of `n` is not definable in `L^k_{∞ω}` on graphs for any `k` (even on all large `n`). -/
example (k : ℕ) :
    ¬∃ φ : InfinitaryFormula.{0, 0, 0} Language.graph k, φ.freeVars = ∅ ∧
      ∀ᶠ n in atTop, ∀ G : SimpleGraph (Fin n), SatisfiesInfinitary G φ ↔ Even n := by
  have hval : ∀ n, G(Fin n, third).real {G : SimpleGraph (Fin n) | Even n} =
      if Even n then 1 else 0 := fun n => by
    by_cases hn : Even n
    · simp only [hn, Set.ofPred_true, probReal_univ, ↓reduceIte]
    · simp only [hn, Set.ofPred_false, measureReal_empty, ↓reduceIte]
  have hnot : ∀ c : ℝ, ¬Tendsto (fun n => G(Fin n, third).real {G | Even n}) atTop (nhds c) := by
    intro c hc
    have hev : Tendsto (fun m : ℕ => 2 * m) atTop atTop := tendsto_id.const_mul_atTop' two_pos
    have hodd : Tendsto (fun m : ℕ => 2 * m + 1) atTop atTop :=
      tendsto_atTop_mono (fun m => Nat.le_succ (2 * m)) hev
    have h1 := hc.comp hev
    have h0 := hc.comp hodd
    simp only [Function.comp_def, hval, even_two_mul, Nat.not_even_two_mul_add_one,
      ↓reduceIte] at h1 h0
    exact one_ne_zero ((tendsto_const_nhds_iff.1 h1).trans (tendsto_const_nhds_iff.1 h0).symm)
  exact not_exists_infinitaryFormula_of_not_tendsto_binomialRandom third_pos third_lt_one k
    (fun n _ => Even n) (hnot 0) (hnot 1)

/-! ### 2. Negative controls at `p = 0` and `p = 1` -/

/-- At `p = 0`, `G(Fin n, 0)` is the edgeless graph `⊥`, which is disconnected for every `n ≥ 2`;
hence `connectedInfinitary` has probability `0` for all `n ≥ 2` even though it holds in `radoGraph`.
The hypothesis `0 < p` in `tendsto_binomialRandom_real_infinitary_one_iff_radoGraph` is needed. -/
theorem binomialRandom_zero_not_connected {n : ℕ} (hn : 2 ≤ n) :
    G(Fin n, 0).real
      {G | SatisfiesInfinitary G
        (connectedInfinitary : InfinitaryFormula.{0, 0, 0} Language.graph 3)} = 0 := by
  rw [SimpleGraph.binomialRandom_zero, Measure.dirac_real_apply, Set.indicator_of_notMem]
  rw [Set.mem_ofPred_eq, satisfiesInfinitary_iff_realize _ freeVars_connectedInfinitary
    (fun _ => ⟨0, by omega⟩), realize_connectedInfinitary_iff_connected]
  intro hconn
  have hreach := hconn.preconnected ⟨0, by omega⟩ ⟨1, by omega⟩
  rw [SimpleGraph.reachable_bot] at hreach
  exact Fin.ne_of_val_ne Nat.zero_ne_one hreach

example :
    ¬(Tendsto (fun n => G(Fin n, 0).real
        {G | SatisfiesInfinitary G
          (connectedInfinitary : InfinitaryFormula.{0, 0, 0} Language.graph 3)}) atTop (nhds 1) ↔
      SatisfiesInfinitary radoGraph
        (connectedInfinitary : InfinitaryFormula.{0, 0, 0} Language.graph 3)) := by
  intro hiff
  have hrado : SatisfiesInfinitary radoGraph
      (connectedInfinitary : InfinitaryFormula.{0, 0, 0} Language.graph 3) := by
    rw [satisfiesInfinitary_iff_realize radoGraph freeVars_connectedInfinitary (fun _ => 0)]
    exact (realize_connectedInfinitary_iff_connected radoGraph (fun _ => 0)).2 radoGraph_connected
  have h0 : Tendsto (fun n => G(Fin n, 0).real
      {G | SatisfiesInfinitary G
        (connectedInfinitary : InfinitaryFormula.{0, 0, 0} Language.graph 3)}) atTop (nhds 0) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop 2] with n hn
      exact (binomialRandom_zero_not_connected hn).symm)
  exact zero_ne_one (tendsto_nhds_unique h0 (hiff.2 hrado))

/-- Closed `L^2_{∞ω}` sentence asserting two distinct non-adjacent vertices: `∃ x₀ ∃ x₁ (x₀ ≠ x₁ ∧
¬Adj x₀ x₁)`. -/
def existsNonAdj : InfinitaryFormula.{0, 0, 0} Language.graph 2 :=
  .ex 0 (.ex 1 ((InfinitaryFormula.equal 0 1).not ⊓ (InfinitaryFormula.rel adj ![0, 1]).not))

theorem freeVars_existsNonAdj : existsNonAdj.freeVars = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro i hi
  simp only [existsNonAdj, InfinitaryFormula.freeVars_ex, InfinitaryFormula.freeVars_min,
    InfinitaryFormula.freeVars_not, InfinitaryFormula.freeVars_equal,
    InfinitaryFormula.freeVars_rel, Set.mem_sdiff, Set.mem_singleton_iff] at hi
  fin_cases i <;> simp at hi

/-- At `p = 1`, `G(Fin n, 1)` is the complete graph `⊤`, so `existsNonAdj` has probability `0` for
every `n ≥ 1`, even though it holds in `radoGraph` (e.g. vertices `0` and `2`). -/
example :
    ¬(Tendsto (fun n => G(Fin n, 1).real {G | SatisfiesInfinitary G existsNonAdj}) atTop (nhds 1) ↔
      SatisfiesInfinitary radoGraph existsNonAdj) := by
  intro hiff
  have hrado : SatisfiesInfinitary radoGraph existsNonAdj := by
    rw [satisfiesInfinitary_iff_realize radoGraph freeVars_existsNonAdj (fun _ => 0)]
    let _ := radoGraph.structure
    simp only [existsNonAdj, InfinitaryFormula.realize_ex, InfinitaryFormula.realize_min,
      InfinitaryFormula.realize_not, InfinitaryFormula.realize_equal,
      InfinitaryFormula.realize_rel]
    refine ⟨0, 2, ?_, ?_⟩
    · simp only [Function.update_self, Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
      decide
    · change ¬radoGraph.Adj 0 2
      decide
  have h0 : Tendsto (fun n => G(Fin n, 1).real {G | SatisfiesInfinitary G existsNonAdj})
      atTop (nhds 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    symm
    rw [SimpleGraph.binomialRandom_one, Measure.dirac_real_apply, Set.indicator_of_notMem]
    rw [Set.mem_ofPred_eq, satisfiesInfinitary_iff_realize _ freeVars_existsNonAdj
        (fun _ => ⟨0, hn⟩)]
    let _ := (⊤ : SimpleGraph (Fin n)).structure
    simp only [existsNonAdj, InfinitaryFormula.realize_ex, InfinitaryFormula.realize_min,
      InfinitaryFormula.realize_not, InfinitaryFormula.realize_equal,
      InfinitaryFormula.realize_rel]
    rintro ⟨u, v, huv, hnotadj⟩
    simp only [Function.update_self, Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)] at huv
    exact hnotadj ((SimpleGraph.top_adj u v).2 huv)
  exact zero_ne_one (tendsto_nhds_unique h0 (hiff.2 hrado))

/-! ### 3. Multi-arity finite relational vocabularies and nullary counterexample -/

/-- Relation symbols of `HyperColorLang`: one unary predicate and one ternary relation. -/
inductive HyperColorRel : ℕ → Type
  | color : HyperColorRel 1
  | hyper : HyperColorRel 3
  deriving DecidableEq

/-- A finite relational language with unary and ternary relations and no nullary relations. -/
abbrev HyperColorLang : Language.{0, 0} where
  Functions _ := Empty
  Relations := HyperColorRel

instance : HyperColorLang.IsRelational := fun _ => inferInstanceAs (IsEmpty Empty)

instance : IsEmpty (HyperColorLang.Relations 0) := ⟨fun r => nomatch r⟩

instance : Finite (Σ l, HyperColorLang.Relations l) :=
  Finite.of_surjective
    (fun b : Bool => if b then ⟨1, HyperColorRel.color⟩ else ⟨3, HyperColorRel.hyper⟩)
    (fun ⟨_, r⟩ => by
      cases r with
      | color => exact ⟨true, rfl⟩
      | hyper => exact ⟨false, rfl⟩)

/-- Distinct per-symbol probabilities `1/4` (unary) and `3/5` (ternary) for `HyperColorLang`. -/
noncomputable def symbolProbs : (Σ l, HyperColorLang.Relations l) → I
  | ⟨1, .color⟩ => ⟨1 / 4, by norm_num, by norm_num⟩
  | ⟨3, .hyper⟩ => ⟨3 / 5, by norm_num, by norm_num⟩

theorem symbolProbs_mem (R : Σ l, HyperColorLang.Relations l) :
    0 < (symbolProbs R : ℝ) ∧ (symbolProbs R : ℝ) < 1 := by
  rcases R with ⟨_, r⟩
  cases r <;> (simp only [symbolProbs]; norm_num)

/-- Kolaitis–Vardi `0-1` law for `HyperColorLang` under `bernoulliStructure` with distinct
per-symbol probabilities `1/4` and `3/5`, plus independence from `p` and non-definability of
`Even n`. -/
example (k : ℕ) (φ : InfinitaryFormula.{0, 0, 0} HyperColorLang k) (hφ : φ.freeVars = ∅) :
    (Tendsto (fun n => infinitaryProb (bernoulliStructure symbolProbs n) φ) atTop (nhds 0) ∨
      Tendsto (fun n => infinitaryProb (bernoulliStructure symbolProbs n) φ) atTop (nhds 1)) ∧
    (Tendsto (fun n => infinitaryProb (bernoulliStructure symbolProbs n) φ) atTop (nhds 1) ↔
      Tendsto (fun n => infinitaryProb (uniformStructure n) φ) atTop (nhds 1)) ∧
    (Tendsto (fun n => infinitaryProb (bernoulliStructure symbolProbs n) φ) atTop (nhds 0) ↔
      Tendsto (fun n => infinitaryProb (uniformStructure n) φ) atTop (nhds 0)) := by
  obtain ⟨M₀⟩ := Relational.isSatisfiable_extensionTheory (L := HyperColorLang)
  exact ⟨Relational.bernoulliStructure_infinitary_zero_one_law symbolProbs_mem hφ,
    Relational.tendsto_infinitaryProb_bernoulliStructure_one_iff_uniformStructure
      symbolProbs_mem hφ,
    (Relational.tendsto_infinitaryProb_bernoulliStructure_zero_iff_model (M₀ := M₀)
      symbolProbs_mem hφ).trans
      (Relational.tendsto_infinitaryProb_uniformStructure_zero_iff_model (M₀ := M₀) hφ).symm⟩

example (k : ℕ) :
    ¬∃ φ : InfinitaryFormula.{0, 0, 0} HyperColorLang k, φ.freeVars = ∅ ∧
      ∀ᶠ n in atTop,
        ∀ S : HyperColorLang.Structure (Fin n),
          @RealizeInfinitary HyperColorLang (Fin n) S k φ ↔ Even n :=
  Relational.not_exists_infinitaryFormula_even_card k

/-- Negative control: with a nullary relation symbol `flag`, even at `k = 0` the closed atomic
`L^0_{∞ω}` formula `.rel flag Fin.elim0` has constant probability `1/3` under
`bernoulliStructure (fun _ => third) n`, so the `0-1` law fails without
`[IsEmpty (L.Relations 0)]`. -/
inductive NullaryRel : ℕ → Type
  | flag : NullaryRel 0
  deriving DecidableEq

/-- Relational language whose single relation symbol is nullary. -/
abbrev NullaryLang : Language.{0, 0} where
  Functions _ := Empty
  Relations := NullaryRel

instance : NullaryLang.IsRelational := fun _ => inferInstanceAs (IsEmpty Empty)

instance : Finite (Σ l, NullaryLang.Relations l) :=
  Finite.of_surjective (fun _ : Unit => ⟨0, NullaryRel.flag⟩)
    (fun ⟨_, r⟩ => by cases r; exact ⟨(), rfl⟩)

/-- Closed `L^0_{∞ω}` sentence asserting the nullary relation `flag`. -/
def flagInfinitary : InfinitaryFormula.{0, 0, 0} NullaryLang 0 :=
  .rel NullaryRel.flag Fin.elim0

theorem infinitaryProb_flagInfinitary (n : ℕ) :
    infinitaryProb (bernoulliStructure (L := NullaryLang) (fun _ => third) n) flagInfinitary =
      1 / 3 := by
  have heq : (fun S : NullaryLang.Structure (Fin n) =>
      @RealizeInfinitary NullaryLang (Fin n) S 0 flagInfinitary) =
      fun S => @RelMap NullaryLang (Fin n) S 0 NullaryRel.flag Fin.elim0 := by
    funext S
    let _ := S
    rw [propext (realizeInfinitary_iff_realize (Set.eq_empty_of_isEmpty _) Fin.elim0)]
    simp only [flagInfinitary, InfinitaryFormula.realize_rel]
    have hcomp : (Fin.elim0 : Fin 0 → Fin n) ∘ Fin.elim0 = Fin.elim0 :=
      funext fun i => Fin.elim0 i
    rw [hcomp]
  rw [infinitaryProb_def, heq]
  exact structProb_bernoulliStructure_relMap (L := NullaryLang) (fun _ => third)
    NullaryRel.flag Fin.elim0

example :
    ¬(Tendsto (fun n => infinitaryProb (bernoulliStructure (L := NullaryLang) (fun _ => third) n)
        flagInfinitary) atTop (nhds 0) ∨
      Tendsto (fun n => infinitaryProb (bernoulliStructure (L := NullaryLang) (fun _ => third) n)
        flagInfinitary) atTop (nhds 1)) := by
  simp only [infinitaryProb_flagInfinitary, tendsto_const_nhds_iff]
  norm_num

end CslibFrontierTests.Logics.FirstOrder.ZeroOneLaw.Infinitary
