/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (redo of the withdrawn cslib PR #1101; needs #1067 and
-- `PolynomialBound/Closure`)

public import Complexity.Computability.Circuit.Boolean.PPoly
public import Complexity.Computability.Machines.Turing.MultiTape.Feature

/-!
# Circuits simulating multi-tape machines

The run of a multi-tape machine over `Bool` on inputs of length `n` is simulated by a circuit,
time step by time step. At each step `t` the circuit holds the *basic features*
(`Turing.MultiTapeTM.Feature`) of the configuration: the control state, the input head, the work
heads and the work cells within the window `|z| ≤ T`, and the view of the output. From them it
derives the symbols read and the situation of the step, and from the terms of the step equations
(`Turing.MultiTapeTM.Feature.stepTerms`) each basic feature at time `t + 1` with a constant number
of gates. Running for `T` steps takes `O(T · (n + T))` gates
[Sipser, Theorem 9.30][Sipser2013].

The language of the inputs on which the machine has written `[true]` after `T n` steps is
therefore in `P/poly` whenever `T` is polynomially bounded (`acceptedWithin_mem_PPoly`); this is
the core of `P ⊆ P/poly` [Arora and Barak, Theorem 6.6][AroraBarak09].

## Main definitions

* `Cslib.Circuits.Boolean.MachineSimulation.featureFn`: a feature at time `t`, as a Boolean
  function of the input.
* `Cslib.Circuits.Boolean.MachineSimulation.acceptedWithin`: the inputs on which the output after
  `T n` steps is `[true]`.

## Main results

* `Cslib.Circuits.Boolean.MachineSimulation.synthesis_step`: one step, from the basic features at
  time `t` to those at time `t + 1`.
* `Cslib.Circuits.Boolean.MachineSimulation.synthesis_basic`: the basic features at every time
  `t ≤ T`, from the inputs.
* `Cslib.Circuits.Boolean.MachineSimulation.acceptedWithin_mem_PPoly`.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 9.3][Sipser2013]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.1][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.MachineSimulation

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Feature

variable {k : ℕ} {State : Type} (tm : MultiTapeTM k Bool State) {n : ℕ}

/-- The configuration of `tm` after `t` steps on the input `x`. -/
noncomputable def cfgAt (t : ℕ) (x : Fin n → Bool) : Cfg k Bool State (List.ofFn x) :=
  tm.runFrom (tm.initCfg (List.ofFn x)) t

theorem cfgAt_succ (t : ℕ) (x : Fin n → Bool) : cfgAt tm (t + 1) x = tm.step (cfgAt tm t x) :=
  runFrom_succ _ _

/-- A work head is within `t` cells of the origin after `t` steps. -/
private theorem abs_workTapePos_cfgAt_le (t : ℕ) (x : Fin n → Bool) (i : Fin k) :
    |(cfgAt tm t x).workTapePos i| ≤ t :=
  abs_workTapePos_runFrom_le _ t i

variable [DecidableEq State]

/-- A feature of the configuration after `t` steps, as a Boolean function of the input. -/
noncomputable def featureFn (t : ℕ) (φ : Feature k State) : BooleanFunction n :=
  fun x => decide (φ.Holds (cfgAt tm t x))

omit [DecidableEq State] in
/-- The input symbol at position `j` is `s`, as a Boolean function of the input. -/
private def inputIs (j : ℕ) (s : Option Bool) : BooleanFunction n :=
  fun x => decide (inputAt (List.ofFn x) j = s)

private theorem featureFn_eq_true {t : ℕ} {φ : Feature k State} {x : Fin n → Bool} :
    featureFn tm t φ x = true ↔ φ.Holds (cfgAt tm t x) :=
  decide_eq_true_iff

theorem featureFn_eq_false {t : ℕ} {φ : Feature k State} {x : Fin n → Bool} :
    featureFn tm t φ x = false ↔ ¬φ.Holds (cfgAt tm t x) :=
  decide_eq_false_iff_not

/-! ### Feature sets -/

section Sets

variable [Fintype State]

/-- The basic features within the window `|z| ≤ T`, for inputs of length `n`
(`Turing.MultiTapeTM.Feature.basic`). -/
noncomputable def basicFeatures (n T : ℕ) : Finset (Feature k State) := (Feature.basic n T).toFinset

/-- A bound on the number of basic features. -/
def featureCount (n T k : ℕ) (State : Type) [Fintype State] : ℕ :=
  (Fintype.card State + 1) + (n + 2) + k * (2 * T + 1) + k * (2 * T + 1) * 3 + 4

private theorem card_basicFeatures_le (n T : ℕ) :
    (basicFeatures (k := k) (State := State) n T).card ≤ featureCount n T k State :=
  (List.toFinset_card_le _).trans (length_basic n T).le

variable {T : ℕ}

theorem state_mem_basicFeatures (q : Option State) :
    Feature.state q ∈ basicFeatures (k := k) n T :=
  List.mem_toFinset.2 (state_mem_basic q)

theorem inPos_mem_basicFeatures {j : ℕ} (hj : j < n + 2) :
    (Feature.inPos j : Feature k State) ∈ basicFeatures n T :=
  List.mem_toFinset.2 (inPos_mem_basic hj)

theorem head_mem_basicFeatures (i : Fin k) {z : ℤ} (hz : |z| ≤ T) :
    (Feature.head i z : Feature k State) ∈ basicFeatures n T :=
  List.mem_toFinset.2 (head_mem_basic i hz)

theorem cell_mem_basicFeatures (i : Fin k) {z : ℤ} (hz : |z| ≤ T) (s : Option Bool) :
    (Feature.cell i z s : Feature k State) ∈ basicFeatures n T :=
  List.mem_toFinset.2 (cell_mem_basic i hz s)

theorem out_mem_basicFeatures (o : OutView) :
    (Feature.out o : Feature k State) ∈ basicFeatures n T :=
  List.mem_toFinset.2 (out_mem_basic o)

/-- The basic features at time `t`, as Boolean functions of the input. -/
noncomputable def basicAt (T t : ℕ) : Set (BooleanFunction n) :=
  featureFn tm t '' ↑(basicFeatures (k := k) (State := State) n T)

/-- The symbols read at time `t`, as Boolean functions of the input. -/
noncomputable def readsAt (t : ℕ) : Set (BooleanFunction n) :=
  featureFn tm t '' {φ | (∃ i s, φ = Feature.read i s) ∨ ∃ s, φ = Feature.inRead s}

/-- The situations at time `t`, as Boolean functions of the input. -/
noncomputable def sitsAt (t : ℕ) : Set (BooleanFunction n) :=
  Set.range fun y => featureFn tm t (.sit y)

/-- What is available for the third phase of a step: the inputs, the basic features, the symbols
read and the situations. -/
noncomputable def stepSources (T t : ℕ) : Set (BooleanFunction n) :=
  inputs n ∪ basicAt tm T t ∪ (readsAt tm t ∪ sitsAt tm t)

theorem featureFn_mem_basicAt {t : ℕ} {φ : Feature k State} (h : φ ∈ basicFeatures n T) :
    featureFn (n := n) tm t φ ∈ basicAt tm T t :=
  Set.mem_image_of_mem _ h

theorem featureFn_mem_stepSources {t : ℕ} {φ : Feature k State} (h : φ ∈ basicFeatures n T) :
    featureFn (n := n) tm t φ ∈ stepSources tm T t :=
  Or.inl (Or.inr (featureFn_mem_basicAt tm h))

theorem sit_mem_stepSources {t : ℕ} (y : Situation k State) :
    featureFn (n := n) tm t (.sit y) ∈ stepSources tm T t :=
  Or.inr (Or.inr ⟨y, rfl⟩)

end Sets

/-! ### One step -/

section Step

variable [Fintype State] {T t : ℕ}

omit [DecidableEq State] [Fintype State] in
/-- An input symbol, or a constant, costs at most one gate. -/
private theorem synthesis_inputIs (j : ℕ) (b : Option Bool) :
    Synthesis interpretation (inputs n) {inputIs j b} 1 := by
  by_cases hj : j = 0 ∨ n < j
  · refine Synthesis.of_forall_eq_const (decide (none = b)) fun x => ?_
    rcases hj with rfl | hj
    · rfl
    · simp only [inputIs, inputAt, show j ≠ 0 by omega, ite_false]
      rw [List.getElem?_eq_none (by rw [List.length_ofFn]; omega)]
  · push Not at hj
    have hidx : j - 1 < n := by omega
    have hinput : ∀ x : Fin n → Bool, inputIs j b x = decide (some (x ⟨j - 1, hidx⟩) = b) := by
      intro x
      simp only [inputIs, inputAt, show j ≠ 0 by omega, ite_false, List.getElem?_ofFn]
      rw [dite_eq_left hidx]
    have hx : Synthesis interpretation (inputs n) {fun x : Fin n → Bool => x ⟨j - 1, hidx⟩} 0 :=
      Synthesis.of_mem ⟨⟨j - 1, hidx⟩, rfl⟩
    rcases b with _ | (_ | _)
    · exact Synthesis.of_forall_eq_const false fun x => by rw [hinput]; simp
    · exact Synthesis.congr_iff hx.not fun x => by rw [hinput]; simp
    · exact Synthesis.congr_iff (hx.mono Set.Subset.rfl Set.Subset.rfl (Nat.zero_le 1))
        fun x => by rw [hinput]; simp

/-- The symbol read by a work head, from the heads and cells in the window. -/
private theorem synthesis_read (ht : t ≤ T) (i : Fin k) (s : Option Bool) :
    Synthesis interpretation (inputs n ∪ basicAt tm T t) {featureFn tm t (.read i s)}
      ((2 * T + 1) * 2 + 1) := by
  obtain ⟨g, hg, hsyn⟩ := Synthesis.exists_exists_mem (s := inputs n ∪ basicAt tm T t) (window T)
    (fun z x => featureFn tm t (.head i z) x && featureFn tm t (.cell i z s) x) (c := 1)
    (card_window T).le fun z hz =>
      (Synthesis.of_mem (Or.inr (featureFn_mem_basicAt tm
        (head_mem_basicFeatures i (mem_window_iff_abs_le.1 hz))))).and
      (Synthesis.of_mem (Or.inr (featureFn_mem_basicAt tm
        (cell_mem_basicFeatures i (mem_window_iff_abs_le.1 hz) s))))
  refine Synthesis.congr_iff hsyn fun x => ?_
  rw [hg, featureFn_eq_true,
    holds_read_iff ((abs_workTapePos_cfgAt_le tm t x i).trans (by exact_mod_cast ht))]
  simp only [Bool.and_eq_true, featureFn_eq_true]

/-- The symbol read by the input head, from its position and the input bits. -/
private theorem synthesis_inRead (s : Option Bool) :
    Synthesis interpretation (inputs n ∪ basicAt tm T t) {featureFn tm t (.inRead s)}
      ((n + 2) * 3 + 1) := by
  obtain ⟨g, hg, hsyn⟩ := Synthesis.exists_exists_mem (s := inputs n ∪ basicAt tm T t)
    (Finset.range (n + 2)) (fun j x => featureFn tm t (.inPos j) x && inputIs j s x) (c := 2)
    (Finset.card_range _).le fun j hj =>
      (Synthesis.of_mem (Or.inr (featureFn_mem_basicAt tm
        (inPos_mem_basicFeatures (Finset.mem_range.1 hj))))).and
      ((synthesis_inputIs j s).mono Set.subset_union_left Set.Subset.rfl le_rfl)
  refine Synthesis.congr_iff hsyn fun x => ?_
  rw [hg, featureFn_eq_true, holds_inRead_iff, List.length_ofFn]
  simp only [Bool.and_eq_true, featureFn_eq_true, inputIs, decide_eq_true_eq]

/-- The cost of the first phase of a step. -/
def readsCost (n k T : ℕ) : ℕ := k * 3 * ((2 * T + 1) * 2 + 1) + 3 * ((n + 2) * 3 + 1)

/-- Phase 1: the symbols read, from the basic features and the inputs. -/
private theorem synthesis_reads (ht : t ≤ T) :
    Synthesis interpretation (inputs n ∪ basicAt tm T t) (readsAt tm t) (readsCost n k T) := by
  have hw := Synthesis.biUnion (I := interpretation) (s := inputs n ∪ basicAt tm T t)
    (Finset.univ : Finset (Fin k × Option Bool)) (fun p => {featureFn tm t (.read p.1 p.2)})
    (fun _ => (2 * T + 1) * 2 + 1) fun p _ => synthesis_read tm ht p.1 p.2
  have hi := Synthesis.biUnion (I := interpretation) (s := inputs n ∪ basicAt tm T t)
    (Finset.univ : Finset (Option Bool)) (fun s => {featureFn tm t (.inRead s)})
    (fun _ => (n + 2) * 3 + 1) fun s _ => synthesis_inRead tm s
  refine (hw.union hi).mono Set.Subset.rfl ?_ (le_of_eq ?_)
  · rintro f ⟨φ, ⟨i, s, rfl⟩ | ⟨s, rfl⟩, rfl⟩
    · exact Or.inl (Set.mem_biUnion (x := (i, s)) (Finset.mem_univ _) rfl)
    · exact Or.inr (Set.mem_biUnion (x := s) (Finset.mem_univ _) rfl)
  · simp [readsCost, Fintype.card_option]

/-- The indicator of a situation, from the state and the symbols read. -/
private theorem synthesis_sit (y : Situation k State) :
    Synthesis interpretation (inputs n ∪ basicAt tm T t ∪ readsAt tm t)
      {featureFn tm t (.sit y)} (k + 3) := by
  have hread : ∀ φ, ((∃ i s, φ = Feature.read i s) ∨ ∃ s, φ = Feature.inRead s) →
      featureFn tm t φ ∈ inputs n ∪ basicAt tm T t ∪ readsAt tm t :=
    fun φ hφ => Or.inr (Set.mem_image_of_mem _ hφ)
  obtain ⟨g, hg, hsyn⟩ := Synthesis.exists_forall_mem
    (s := inputs n ∪ basicAt tm T t ∪ readsAt tm t) (Finset.univ : Finset (Fin k))
    (fun i x => featureFn tm t (.read i (y.2.2 i)) x) (c := 0) (m := k) (by simp)
    fun i _ => Synthesis.of_mem (hread _ (Or.inl ⟨i, _, rfl⟩))
  have h := ((Synthesis.of_mem (Or.inl (Or.inr (featureFn_mem_basicAt tm
    (state_mem_basicFeatures (some y.1)))))).and
    (Synthesis.of_mem (hread (.inRead y.2.1) (Or.inr ⟨_, rfl⟩)))).and hsyn
  refine (Synthesis.congr_iff h fun x => ?_).mono Set.Subset.rfl Set.Subset.rfl (by omega)
  rw [featureFn_eq_true, holds_sit_iff]
  simp only [Bool.and_eq_true, hg, featureFn_eq_true, Finset.mem_univ, true_implies, and_assoc]

/-- Phase 2: every situation indicator. -/
private theorem synthesis_sits :
    Synthesis interpretation (inputs n ∪ basicAt tm T t ∪ readsAt tm t) (sitsAt tm t)
      (Fintype.card (Situation k State) * (k + 3)) := by
  refine (Synthesis.biUnion (I := interpretation) (Finset.univ : Finset (Situation k State))
    (fun y => {featureFn tm t (.sit y)}) (fun _ => k + 3) fun y _ =>
      synthesis_sit tm y).mono Set.Subset.rfl ?_ (by simp)
  rintro f ⟨y, rfl⟩
  exact Set.mem_biUnion (x := y) (Finset.mem_univ _) rfl

/-! #### Phase 3: the next configuration -/

/-- The budget for one basic feature of the next configuration: its step equation has at most
`4 |Situation| + 2` terms (`Turing.MultiTapeTM.Feature.length_stepTerms_le`), each of at most three
literals. -/
def featureCost (k : ℕ) (State : Type) [Fintype State] : ℕ :=
  (4 * Fintype.card (Situation k State) + 2) * (2 * 3 + 2) + 1

/-- Every basic feature of the next configuration, from the terms of its step equation. -/
private theorem synthesis_next (ht : t ≤ T) {φ : Feature k State} (hφ : φ ∈ basicFeatures n T) :
    Synthesis interpretation (stepSources tm T t) {featureFn (n := n) tm (t + 1) φ}
      (featureCost k State) := by
  have hφ' := List.mem_toFinset.1 hφ
  let D : List (List (BooleanFunction n × Bool)) :=
    (stepTerms tm n T φ).map fun c => c.map fun l => (featureFn tm t l.1, l.2)
  have hw : ∀ c ∈ D, c.length ≤ 3 := by
    intro c hc
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
    simpa using length_le_three_of_mem_stepTerms tm hc'
  have hD : ∀ c ∈ D, ∀ l ∈ c, l.1 ∈ stepSources tm T t := by
    intro c hc l hl
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
    rcases mem_basic_of_mem_stepTerms tm hφ' hc' hl' with hb | ⟨y, hy⟩
    · exact featureFn_mem_stepSources tm (List.mem_toFinset.2 hb)
    · rw [hy]
      exact sit_mem_stepSources tm y
  refine (Synthesis.congr_iff (Synthesis.any_all_literal hw hD) fun x => ?_).mono
    Set.Subset.rfl Set.Subset.rfl ?_
  · rw [featureFn_eq_true, cfgAt_succ, holds_step_iff_exists_stepTerms tm List.length_ofFn
      (fun i => (abs_workTapePos_cfgAt_le tm t x i).trans (by exact_mod_cast ht)) hφ']
    have hlit (l : Feature k State × Bool) :
        featureFn tm t l.1 x = l.2 ↔ (l.1.Holds (cfgAt tm t x) ↔ l.2 = true) := by
      rw [featureFn]
      cases l.2 <;> simp
    simp only [D, List.any_eq_true, List.all_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨_, hc, h⟩
      obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
      exact ⟨c', hc', fun l hl => (hlit l).1 (h _ (List.mem_map_of_mem hl))⟩
    · rintro ⟨c, hc, h⟩
      refine ⟨_, List.mem_map_of_mem hc, fun l' hl' => ?_⟩
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hl'
      exact (hlit l).2 (h l hl)
  · have := length_stepTerms_le tm (n := n) (T := T) φ
    simp only [D, List.length_map, featureCost]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ this) _

/-- Phase 3: all basic features of the next configuration. -/
private theorem synthesis_nexts (ht : t ≤ T) :
    Synthesis interpretation (stepSources (n := n) tm T t) (basicAt tm T (t + 1))
      (featureCount n T k State * featureCost k State) := by
  refine (Synthesis.biUnion (I := interpretation) (basicFeatures n T)
    (fun φ => {featureFn (n := n) tm (t + 1) φ}) (fun _ => featureCost k State)
    fun φ hφ => synthesis_next tm ht hφ).mono Set.Subset.rfl ?_ ?_
  · rintro f ⟨φ, hφ, rfl⟩
    exact Set.mem_biUnion hφ rfl
  · rw [Finset.sum_const, Nat.nsmul_eq_mul]
    exact Nat.mul_le_mul_right _ (card_basicFeatures_le n T)

/-- The cost of one step of the simulation. -/
def stepCost (n T k : ℕ) (State : Type) [Fintype State] : ℕ :=
  readsCost n k T + Fintype.card (Situation k State) * (k + 3) +
    featureCount n T k State * featureCost k State

/-- **One step of the simulation**: the basic features at time `t + 1`, from those at time `t`. -/
theorem synthesis_step (ht : t ≤ T) :
    Synthesis interpretation (inputs n ∪ basicAt tm T t) (basicAt tm T (t + 1))
      (stepCost n T k State) :=
  ((synthesis_reads tm ht).comp (synthesis_sits (T := T) tm)).trans (synthesis_nexts tm ht)

end Step

/-! ### The whole run -/

section Run

variable [Fintype State] {T : ℕ}

/-- The basic features at time `0`, which do not depend on the input. -/
private theorem synthesis_basic_zero :
    Synthesis interpretation (inputs n) (basicAt tm T 0) (featureCount n T k State) := by
  have h0 : ∀ x : Fin n → Bool, cfgAt tm 0 x = tm.initCfg (List.ofFn x) := fun _ => rfl
  refine (Synthesis.biUnion (I := interpretation) (basicFeatures n T)
    (fun φ => {featureFn (n := n) tm 0 φ}) (fun _ => 1) fun φ hφ => ?_).mono Set.Subset.rfl ?_ ?_
  · rcases mem_basic.1 (List.mem_toFinset.1 hφ) with ⟨q, rfl⟩ | ⟨j, -, rfl⟩ | ⟨i, z, -, rfl⟩ |
      ⟨i, z, b, -, rfl⟩ | ⟨o, rfl⟩
    · exact Synthesis.of_forall_eq_const (decide (some tm.q₀ = q)) fun x => by
        simp [featureFn, h0, eq_comm]
    · exact Synthesis.of_forall_eq_const (decide (1 = j)) fun x => by
        simp [featureFn, h0, eq_comm]
    · exact Synthesis.of_forall_eq_const (decide (0 = z)) fun x => by
        simp [featureFn, h0, eq_comm]
    · exact Synthesis.of_forall_eq_const (decide (none = b)) fun x => by
        simp [featureFn, h0, eq_comm]
    · exact Synthesis.of_forall_eq_const (decide (OutView.empty = o)) fun x => by
        simp [featureFn, h0, eq_comm, OutView.ofList]
  · rintro f ⟨φ, hφ, rfl⟩
    exact Set.mem_biUnion hφ rfl
  · rw [Finset.sum_const, Nat.nsmul_eq_mul, mul_one]
    exact card_basicFeatures_le n T

/-- **The simulation**: the basic features at every time `t ≤ T`, from the inputs. -/
theorem synthesis_basic : ∀ t ≤ T,
    Synthesis interpretation (inputs n) (basicAt tm T t)
      (featureCount n T k State + t * stepCost n T k State)
  | 0, _ => by simpa using synthesis_basic_zero (T := T) tm
  | t + 1, ht => by
    have := (synthesis_basic t (by omega)).trans (synthesis_step tm (by omega))
    rwa [Nat.add_mul, one_mul, ← Nat.add_assoc]

/-- The total cost of simulating `T` steps on inputs of length `n`. -/
private def simulationCost (n T k : ℕ) (State : Type) [Fintype State] : ℕ :=
  featureCount n T k State + T * stepCost n T k State

omit [DecidableEq State] in
/-- The simulation cost is polynomially bounded when the number of steps is. -/
private theorem polynomiallyBounded_simulationCost {T : ℕ → ℕ} (hT : PolynomiallyBounded T) :
    PolynomiallyBounded fun n => simulationCost n (T n) k State := by
  simp only [simulationCost, featureCount, stepCost, readsCost, featureCost]
  fun_prop

end Run

/-- The inputs on which `tm` has written `[true]` after `T n` steps, on inputs of length `n`. -/
noncomputable def acceptedWithin (T : ℕ → ℕ) : Language Bool :=
  Language.ofSlices fun n => featureFn tm (T n) (.out (.one true))

/-- An input is accepted within `T` steps when the machine has written `[true]` by then. -/
theorem mem_acceptedWithin_iff (T : ℕ → ℕ) (w : List Bool) :
    w ∈ acceptedWithin tm T ↔
      OutView.ofList (tm.runFrom (tm.initCfg w) (T w.length)).output = .one true := by
  rw [acceptedWithin, Language.mem_ofSlices, featureFn_eq_true, Feature.holds_out, cfgAt,
    congrArg (fun u => OutView.ofList (tm.runFrom (tm.initCfg u) (T w.length)).output)
      (List.ext_getElem (by simp) fun i _ _ => by simp : List.ofFn (w[·]) = w)]

/-- **Machines with polynomial running time have polynomial circuits.** The inputs on which a
machine has written `[true]` within a polynomially bounded number of steps form a language in
`P/poly`. -/
theorem acceptedWithin_mem_PPoly [Finite State] {T : ℕ → ℕ} (hT : PolynomiallyBounded T) :
    acceptedWithin tm T ∈ PPoly := by
  have := Fintype.ofFinite State
  refine PPoly.of_synthesis (polynomiallyBounded_simulationCost (k := k) (State := State) hT)
    fun n => ?_
  rw [acceptedWithin, Language.slice_ofSlices]
  exact (synthesis_basic tm (T n) le_rfl).mono Set.Subset.rfl
    (Set.singleton_subset_iff.2 (featureFn_mem_basicAt tm (out_mem_basicFeatures _))) le_rfl

end Cslib.Circuits.Boolean.MachineSimulation
