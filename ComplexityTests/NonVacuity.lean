/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.FirstOrder
import Complexity.Computability.Circuit.Boolean.GateElimination
import Complexity.Computability.Circuit.Boolean.Khrapchenko
import Complexity.Computability.Circuit.Boolean.LMN
import Complexity.Computability.Circuit.Boolean.PolynomialTime
import Complexity.Computability.Circuit.Boolean.Smolensky
import Mathlib.FieldTheory.Finite.GaloisField
import Complexity.Computability.Circuit.Boolean.TC0
import Complexity.Computability.Circuit.Boolean.TopDown
import Complexity.Computability.Circuit.Monotone.Clique.Asymptotic
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
import Complexity.Foundations.BooleanAnalysis.HadamardTester
import Complexity.Probability.ApproximateCounting.Relative
import Complexity.Probability.PairwiseIndependentHash.Toeplitz
import Complexity.Foundations.Combinatorics.Expander.Existence
import Complexity.Foundations.Combinatorics.Expander.AffineTower
import Complexity.Computability.Kolmogorov.ChainRule
import Complexity.Computability.Kolmogorov.MultiTape
import Complexity.Computability.Kolmogorov.NisanWigderson
import Complexity.Computability.RAM.Squaring
import Complexity.Computability.Circuit.Frontier.Reduction
import Complexity.Computability.Circuit.Frontier.Unconditional
import Complexity.Computability.Circuit.Frontier.Linear.Unconditional
import Complexity.Computability.Circuit.Frontier.Ledger.Unconditional
import Complexity.Computability.Circuit.Decomposable
import Complexity.Computability.Circuit.Frontier.FanInTwo
import Complexity.Computability.Circuit.Frontier.Correlation
import Complexity.Computability.Circuit.Frontier.Witness
import Complexity.Computability.Circuit.Boolean.Threshold.Parity
import Complexity.Logics.SecondOrder.Coloring
import Complexity.Computability.PCP.GapTheorem
import Complexity.Computability.PCP.Preprocess
import Complexity.Computability.PCP.ThreeSAT
import Complexity.Computability.PCP.Composition
import Complexity.Computability.PCP.PoweringBound
import Complexity.Foundations.Relation.InductiveCounting
import Mathlib.Tactic.FinCases
import Complexity.Crypto.Primitives.PRG.NisanWigderson.Design
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Id

/-!
# Non-vacuity of the complexity classes

A machine without work tapes that writes a constant answer in one step computes a constant
function in polynomial time, whatever the input encoding. So the empty and the full problem are in
`P`, `NP`, `BPP` and `RP`, and the hypotheses of the theorems about these classes (such as
`Cslib.Circuits.Boolean.P_subset_PPolyOn` and `BPP_subset_PPolyOn`) can be met.

Constant functions will come from the composition machinery upstream; this file only guards
against definitions that are accidentally unsatisfiable.
-/

namespace ComplexityTests.NonVacuity

open Turing Turing.MultiTapeTM Cslib.Complexity Cslib.Circuits.Boolean Finset Cslib

/-- The machine that writes `b` and halts. -/
def constTM (b : Bool) : MultiTapeTM 0 Bool Unit :=
  ofTr () fun _ _ _ => ⟨0, Fin.elim0, some b, none⟩

theorem computesTidily_constTM (b : Bool) (w : List Bool) :
    (constTM b).ComputesTidilyInTimeAndSpace w [b] 1 0 := by
  rw [computesTidily_iff]
  refine ⟨.ofDeterministic (constTM b) (wordsCfg w (some (constTM b).q₀) (fun _ => []) []) 1, rfl,
    ?_, le_rfl, by simp [MultiTapeNTM.RunPath.space]⟩
  rw [MultiTapeNTM.RunPath.last_ofDeterministic, runFrom_one, step_of_state (q := ()) rfl]
  simp only [constTM, tr_ofTr, wordsCfg, Action.apply, moveInputPos_zero]
  congr <;> funext i <;> exact i.elim0

theorem polyTime_const {α : Type} (enc : α ↪ List Bool) (b : Bool) :
    ComputableTidilyInPolyTime (fun _ : α => b) enc encBool :=
  ⟨fun _ => 1, fun _ => 0, .const 1, .const 0,
    0, Unit, inferInstance, constTM b, fun a => computesTidily_constTM b (enc a)⟩

example :
    (∅ : Set (List Bool)) ∈ Cslib.Complexity.P encBits ∧
    (Set.univ : Set (List Bool)) ∈ Cslib.Complexity.P encBits ∧
    (∅ : Set (List Bool)) ∈ NP encBits ∧
    (Set.univ : Set (List Bool)) ∈ NP encBits ∧
    (∅ : Set (List Bool)) ∈ BPP encBits ∧
    (∅ : Set (List Bool)) ∈ RP encBits :=
  ⟨⟨fun _ => false, .const false, fun _ => by simp⟩,
   ⟨fun _ => true, .const true, fun _ => by simp⟩,
   ⟨0, fun _ => false, .const false, fun _ => by simp⟩,
   ⟨0, fun _ => true, .const true, fun _ => by simp⟩,
   ⟨0, fun _ => false, .const false, fun _ => ⟨fun h => h.elim, fun _ => by
      simp only [BoundedErrorAt, Polynomial.eval_zero, pow_zero, mul_one]
      exact le_trans (by norm_num : 2 ≤ 3 * 1)
        (Nat.mul_le_mul_left 3 (Finset.card_pos.2
          ⟨fun _ => false, Finset.mem_filter.2 ⟨Finset.mem_univ _, trivial⟩⟩))⟩⟩,
   ⟨0, fun _ => false, .const false, fun _ => ⟨fun h => h.elim, fun _ _ => rfl⟩⟩⟩

/-- `P ⊆ P/poly` applies to a language in `P`. -/
example : (⊤ : Language Bool) ∈ PPoly :=
  mem_PPolyOn_encBits_iff.1
    (P_subset_PPolyOn ⟨fun _ => true, .const true, fun _ => ⟨fun _ => rfl, fun _ => trivial⟩⟩)

/-- `BPP ⊆ P/poly` applies to a language in `BPP`. -/
example : (⊥ : Language Bool) ∈ PPoly :=
  mem_PPolyOn_encBits_iff.1 (BPP_subset_PPolyOn ⟨0, fun _ => false, .const false,
    fun _ => ⟨fun h => h.elim, fun _ => by
      simp only [BoundedErrorAt, Polynomial.eval_zero, pow_zero, mul_one]
      exact le_trans (by norm_num : 2 ≤ 3 * 1)
        (Nat.mul_le_mul_left 3 (Finset.card_pos.2
          ⟨fun _ => false, Finset.mem_filter.2 ⟨Finset.mem_univ _, trivial⟩⟩))⟩⟩)

/-- The monotone lower bound for cliques, Schnorr's and Khrapchenko's parity bounds, and the
constant-depth classes (`AC0`, `TC0`, `AC0Mod 3`) are inhabited. -/
example :
    Cslib.Circuits.ecomplexity Cslib.Circuits.Monotone.interpretation
      (Cslib.Circuits.single (Cslib.Circuits.clique 16 2)) ≠ ⊤ ∧
    6 ≤ Cslib.Circuits.complexity Cslib.Circuits.Boolean.interpretation
      (Cslib.Circuits.single (Cslib.parity 3)) ∧
    (∃ F : Cslib.Circuits.Formula Cslib.Circuits.Boolean.signature (2 ^ 2),
      F.Computes Cslib.Circuits.Boolean.interpretation (Cslib.parity (2 ^ 2)) ∧
        F.leafSize = 16) ∧
    ((⊤ : Language Bool) ∈ AC0 ∧ (⊥ : Language Bool) ∈ AC0 ∧
      (⊤ : Language Bool) ∈ TC0 ∧ (⊥ : Language Bool) ∈ AC0Mod 3) :=
  ⟨Cslib.Circuits.Monotone.ecomplexity_clique_ne_top 16 2,
   Cslib.Circuits.Boolean.three_mul_le_complexity_parity 3,
   Cslib.Circuits.Boolean.exists_formula_parity_two_pow 2,
   ⟨ConstDepth.top_mem (Cslib.Circuits.Signature.Hom.id _),
    ConstDepth.bot_mem (Cslib.Circuits.Signature.Hom.id _),
    ConstDepth.top_mem Unbounded.toExt,
    ConstDepth.bot_mem Unbounded.toExt⟩⟩

/-- First-order model checking applies: over the empty language, the atomic facts of a structure
on `Fin n` are enumerated by `Fin 0`. -/
example (φ : FirstOrder.Language.empty.Sentence) (n : ℕ) :
    ∃ e : ModelChecking.Atom FirstOrder.Language.empty n ≃ Fin 0,
      ∃ F : Cslib.Circuits.Formula Unbounded.signature 0,
        (∀ (M : Type) [FirstOrder.Language.empty.Structure M] (eM : M ≃ Fin n),
          F.eval Unbounded.interpretation (ModelChecking.atomsOf eM ∘ e.symm) = true ↔ M ⊨ φ) ∧
        F.depth ≤ ModelChecking.foDepth φ ∧
          F.size ≤ ModelChecking.foSize φ * (n + 2) ^ ModelChecking.foSize φ := by
  have : IsEmpty (ModelChecking.Atom FirstOrder.Language.empty n) := ⟨fun a => a.1.2.elim⟩
  let e := Equiv.equivOfIsEmpty (ModelChecking.Atom FirstOrder.Language.empty n) (Fin 0)
  exact ⟨e, ModelChecking.exists_formula_realize_structure φ e⟩

/-- The hypotheses of the Linial–Mansour–Nisan theorem can be met: for depth one, `s = 2` and
`n = 528`, the restrictions keep `⌊528 / 33⌋ = 16` bits free, and `k = 264` works. -/
example {f : BooleanFunction 528} {C : Cslib.Circuits.Circuit Unbounded.signature 528 1}
    (hC : C.Computes Unbounded.interpretation (Cslib.Circuits.single f)) (hd : C.depth = 1) :
    ∑ U with 264 ≤ #U, BitString.fourierCoeff (fun x => BitString.signVal (f x)) U ^ 2 ≤
      2 * C.size / 2 ^ 2 :=
  Unbounded.sum_fourierCoeff_sq_le_of_computes hC le_rfl (by norm_num) (by rw [hd]; norm_num)

/-- The AND/OR depth of Korten's theorem differs from the depth: a negation of an input has AND/OR
depth zero and depth one. -/
example : (Cslib.Circuits.Circuit.oneGate (σ := Unbounded.signature) (n := 1) .not
      fun _ => 0).depthWith Unbounded.andOrCost = 0 ∧
    (Cslib.Circuits.Circuit.oneGate (σ := Unbounded.signature) (n := 1) .not fun _ => 0).depth =
      1 := by
  decide

/-- The tidy normal form applies to upstream's machine for the identity on `encBits`, which is not
tidy: it leaves its input head at the end of the input. -/
example :
    ∃ c, ComputableTidilyInTimeAndSpace (id : List Bool → List Bool) encBits encBits
      (fun a => 2 * ((encBits a).length + 1) + 3 * 0 + c) (fun _ => c * (0 + 1)) :=
  computableInTimeAndSpace_id.exists_computableTidilyInTimeAndSpace

/-- The Fourier analysis of the cube applies to any finite index type: on the cube `Bool → Bool`,
the character of a nonempty set sums to zero. -/
example : ∑ x : Bool → Bool, BitString.chi ℝ {true} x = 0 := by
  simp [BitString.sum_chi]

/-- The hypotheses of the soundness of the Hadamard tester can be met: the honest tables for a
solution pass every test with probability one. -/
example {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (x : ι → Bool)
    (A : κ → ι × ι → Bool) (b : κ → Bool)
    (h : ∀ e, BitString.hadamardCode (BitString.tensor x x) (A e) = b e) :
    ∃ x', (hammingDist (BitString.hadamardCode x) (BitString.hadamardCode x') : ℝ) /
        2 ^ Fintype.card ι ≤ 0 ∧
      ∀ e, BitString.hadamardCode (BitString.tensor x' x') (A e) = b e :=
  BitString.exists_forall_hadamardCode_tensor_eq_of_le_blrAcceptance
    (g := BitString.hadamardCode (BitString.tensor x x)) (ε := 0) (ε' := 0)
    (by simp) (by simp) (by norm_num)
    (by rw [BitString.equationTestAcceptance_hadamardCode h]; norm_num)

/-- Nisan–Wigderson designs exist for some parameters: two disjoint singletons. -/
example : Cslib.Crypto.PRG.NisanWigderson.Design 2 1 0 2 where
  block := ![{0}, {1}]
  card_block := by decide
  card_inter_le := by decide

/-- Nisan–Wigderson designs with nontrivial parameters exist: a `(36, 3, 1)`-design with 16
blocks. -/
example : Nonempty (Cslib.Crypto.PRG.NisanWigderson.Design 36 3 1 16) :=
  Cslib.Crypto.PRG.NisanWigderson.Design.nonempty_four_mul_sq 3 2

/-- The root recovery of relative-error counting applies: `e = 100 · 3 ^ 7` lies between `3 ^ 7`
and `128 · 3 ^ 7`, and `128 · 1 ^ 7 ≤ 2 ^ 7`, so the integer seventh root of `e` lies between `3`
and `2 · 3`. -/
example : 3 ≤ Nat.nthRoot 7 (100 * 3 ^ 7) ∧ 1 * Nat.nthRoot 7 (100 * 3 ^ 7) ≤ (1 + 1) * 3 :=
  Cslib.Probability.ApproximateCounting.le_nthRoot_and_mul_nthRoot_le (c := 128) (by norm_num)
    (by norm_num) (by norm_num)
    (Cslib.Probability.ApproximateCounting.two_pow_mul_pow_le_add_one_pow 7 one_ne_zero)

section Toeplitz

open Cslib.Probability Matrix Finset

/-- Toeplitz hashing gives a concrete pair of values its pairwise-independent probability. -/
example : dens {p : (Fin (2 + 3 - 1) → ZMod 2) × (Fin 2 → ZMod 2) |
    toeplitzHash p ![1, 0, 0] = 0 ∧ toeplitzHash p ![0, 1, 0] = ![1, 1]} = 1 / 16 := by
  rw [isPairwiseIndependentHash_toeplitzHash.dens_filter_apply_eq_and_apply_eq (by decide)]
  simp [ZMod.card]
  norm_num

/-- The diagonals of a Toeplitz matrix are read along its last column, then its first row. -/
example : toeplitz ![(1 : ℤ), 2, 3, 4] = !![3, 2, 1; 4, 3, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end Toeplitz

/-- The lazy graph satisfies the hypothesis of Cheeger's lazy-walk bound. -/
example {V D : Type} [Fintype D] [Nonempty D] (G : Cslib.RotationMap V D) :
    ∀ f v, G.lazy.walk f v = (f v + G.walk f v) / 2 :=
  G.walk_lazy_apply

/-- Constant-degree expanders exist on five vertices. -/
example : ∃ G : Cslib.RotationMap (Fin 5) (Fin 120), G.spectralExpansion < 1 :=
  ⟨Cslib.RotationMap.expander (Fin 5),
    (Cslib.RotationMap.spectralExpansion_expander_le _).trans_lt (by norm_num)⟩

/-- A family of expanders with a spectral bound below one exists, so the hypotheses of
preprocessing with a family can be met. -/
example : ∃ μ < 1, Nonempty (Cslib.RotationMap.ExpanderFamily.{0} (Fin 120) μ) :=
  ⟨_, by norm_num, ⟨Cslib.RotationMap.expanderFamily⟩⟩

section Kolmogorov

open Cslib.Kolmogorov Cslib.Kolmogorov.DescriptionMethod

/-- Some finite-state multi-tape machine describes every string `x` with `|x|` bits within
`|x| + 1` steps, so the Turing-machine description method is not vacuous. -/
example : ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : Turing.MultiTapeTM k Bool State),
    ∀ x : List Bool,
      (ofMultiTapeTM tm).etimeBoundedComplexity (x.length + 1) x ≤ x.length := by
  obtain ⟨k, State, hfin, tm, ⟨S⟩⟩ := exists_simulation_literal
  refine ⟨k, State, hfin, tm, fun x => ?_⟩
  simpa [etimeBoundedComplexity_literal le_rfl] using S.etimeBoundedComplexity_le x.length x

/-- The canonical composition of the literal method with itself describes every pair `(x, y)`
with `|x| + |y| + 2 size |x| + 1` bits, so the chain rule is not vacuous. -/
example (x y : List Bool) :
    (literal.compose (fun _ => literal) Prod.mk).ecomplexity (x, y) ≤
      (x.length + y.length + (2 * x.length.size + 1) : ℕ) := by
  simpa using (Composition.compose literal (fun _ => literal) Prod.mk).ecomplexity_le x y

/-- The same within `|x| + |y|` steps, from the time-bounded chain rule. -/
example (x y : List Bool) :
    (literal.compose (fun _ => literal) Prod.mk).etimeBoundedComplexity (x.length + y.length)
      (x, y) ≤ (x.length + y.length + (2 * x.length.size + 1) : ℕ) :=
  (Composition.compose literal (fun _ => literal) Prod.mk).etimeBoundedComplexity_le_of_le
    (fun _ _ h => by dsimp only; have := Nat.size_le_size h; omega) monotone_const
    (etimeBoundedComplexity_literal le_rfl).le (etimeBoundedComplexity_literal le_rfl).le

end Kolmogorov

section SecondOrder

open FirstOrder Language Cslib.Logic

/-- The triangle satisfies the three-colorability sentence but not the two-colorability one. -/
example :
    (letI := (⊤ : SimpleGraph (Fin 3)).structure; (ESO.Sentence.colorable 3).Realize (Fin 3)) ∧
      ¬ (letI := (⊤ : SimpleGraph (Fin 3)).structure;
        (ESO.Sentence.colorable 2).Realize (Fin 3)) := by
  rw [ESO.Sentence.realize_colorable_structure_iff, ESO.Sentence.realize_colorable_structure_iff]
  refine ⟨⟨(⊤ : SimpleGraph (Fin 3)).selfColoring⟩, fun h => ?_⟩
  have := h.card_le_of_pairwise_adj id fun i j hij => (SimpleGraph.top_adj i j).2 hij
  simp at this

/-- Definable classes meet the isomorphism-closure hypothesis of first-order reducibility: the
class of `3`-colorable finite simple graphs reduces to itself. -/
example :
    let K : Set (CategoryTheory.Bundled.{0} Language.graph.Structure) :=
      {M | M ⊨ Theory.simpleGraph ∧
        ∃ f : M → Fin 3, ∀ x y, Structure.RelMap adj ![x, y] → f x ≠ f y}
    FO.Reduces K K :=
  .refl (ESO.Definable.colorable_simpleGraph 3).isoClosed

end SecondOrder

section PCP

open Cslib.PCP Cslib.Logic.PL

/-- The whole first layer of Dinur's proof applies: an unsatisfiable formula gives a preprocessed
constraint graph of positive value. -/
example (φ : CNF ℕ) (hφ : φ = [[(0, true)], [(0, false)]]) :
    0 < ((ConstraintGraph.ofCNF φ).preprocess
      Cslib.RotationMap.expanderFamily).toConstraintGraph.unsatVal := by
  subst hφ
  have h : 0 < (ConstraintGraph.ofCNF ([[(0, true)], [(0, false)]] : CNF ℕ)).unsatVal := by
    rw [ConstraintGraph.unsatVal_pos_iff, ConstraintGraph.satisfiable_ofCNF_iff _ (by simp)]
    rintro ⟨σ, hσ⟩
    simp at hσ
  exact lt_of_lt_of_le (by positivity) (ConstraintGraph.le_unsatVal_preprocess_expanderFamily _)

/-- Dinur's gap theorem applies: the gap graph of an unsatisfiable formula has value at least the
gap. -/
example :
    Dinur.gap ≤ (Dinur.gapGraph ([[((), true)], [((), false)]] : CNF Unit)).graph.unsatVal := by
  refine Dinur.gap_le_unsatVal_gapGraph _ (by simp) ?_
  rintro ⟨σ, hσ⟩
  cases h : σ () <;> simp_all

end PCP

/-- A round list certifies unreachability: on `Fin 3` with the successor relation, `0` is not
reachable from `1`, certified by the list `[1, 2]` of everything reachable within two steps. -/
example : ¬ Relation.ReflTransGen (fun i j : Fin 3 => j.val = i.val + 1) 1 0 := by
  open Relation in
  have hsub : reachableWithin (fun i j : Fin 3 => j.val = i.val + 1) 1 2 ⊆ {1, 2} := by
    intro j hj
    have hle : (1 : Fin 3).val ≤ j.val := by
      induction (mem_reachableWithin.mp hj).reflTransGen with
      | refl => exact le_rfl
      | tail _ h ih => omega
    fin_cases j <;> simp_all
  open Relation in
  refine (not_reflTransGen_iff_exists_isRoundList (N := 2) (by simp)).mpr
    ⟨[1, 2], ⟨by decide, ?_, ?_⟩, by decide⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨Relation.RelatesWithinSteps.refl 1 |>.mono (by omega),
      (Relation.RelatesWithinSteps.single (by decide)).mono (by omega)⟩
  · refine (Set.encard_le_encard hsub).trans ?_
    rw [Set.encard_pair (by decide)]
    simp

/-- The zig-zag tower has a base graph: a graph on `Fin 2 → D × D` of degree `|D| > 1` with
`λ ≤ 1 / 5`. -/
example : ∃ (D : Type) (_ : Fintype D) (H : Cslib.RotationMap (Fin 2 → D × D) D),
    1 < Fintype.card D ∧ H.spectralExpansion ≤ 1 / 5 := by
  obtain ⟨D, _, H, hD, hH, -⟩ := Cslib.RotationMap.exists_spectralExpansion_zigzagTower_le
  exact ⟨D, inferInstance, H, hD, hH⟩

open Cslib.RAM in
/-- Repeated squaring on a RAM: on input `2` the program halts after `4 * 2 + 5 = 13` steps with
`2 ^ 2 ^ 2 = 16` in the output register, and the run costs `31` units of logarithmic time. -/
example : (run repeatedSquaring 13 (State.init [2])).isHalted repeatedSquaring ∧
    (run repeatedSquaring 13 (State.init [2])).regs.output = 16 ∧
    time logCost repeatedSquaring 13 (State.init [2]) = 31 := by
  decide

open Cslib.RAM in
/-- The repeated-squaring program evaluates to `2 ^ 2 ^ k` on input `k`. -/
example (k : ℕ) : eval repeatedSquaring [k] = .some (2 ^ 2 ^ k) :=
  computesInTime_unitCost_repeatedSquaring.eval_eq ![k]

section RAMInputCosts

open Cslib Cslib.RAM

/-- Free initialization and output extraction allow an arbitrary preloaded input to be returned
in zero logarithmic time. This does not charge for reading or writing its binary encoding. -/
example : ComputesInTime logCost 1 [] (fun x => x 0) (fun _ => 0) := by
  intro x
  refine ⟨0, ?_, ?_, le_rfl⟩
  · change 0 ≤ 0
    exact le_rfl
  · simp [run, State.init, URM.Regs.output, URM.Regs.ofInputs]

/-- Even without multiplication, one fixed program takes one unit step but has logarithmic cost
unbounded over its freely preloaded inputs. Initial bit lengths matter in cost comparisons. -/
example (B : ℕ) : ∃ n,
    time unitCost [.add 0 0 0] 1 (State.init [n]) = 1 ∧
    B < time logCost [.add 0 0 0] 1 (State.init [n]) := by
  refine ⟨2 ^ B, rfl, ?_⟩
  change B < bitLength (2 ^ B) + bitLength (2 ^ B)
  rw [bitLength_two_pow]
  lia

end RAMInputCosts

section Frontier

open Cslib.Circuits.Frontier Set

/-- The hypotheses of the frontier counting lemma can be met: all strings of one bit form a
`2`-rectangle-free set with at least two elements. -/
example : RectangleFree (univ : Set (Fin 1 → Bool)) 2 ∧ 2 ≤ (univ : Set (Fin 1 → Bool)).ncard := by
  refine ⟨rectangleFree_iff.mpr fun X A B _ => ?_, by simp⟩
  by_cases h : (0 : Fin 1) ∈ X
  · right
    have : Subsingleton (↥Xᶜ → Bool) :=
      ⟨fun f g => funext fun i => absurd (Subsingleton.elim i.1 0 ▸ h) i.2⟩
    exact (ncard_le_one (toFinite _)).mpr (fun a _ b _ => Subsingleton.elim a b) |>.trans_lt
      one_lt_two
  · left
    have : Subsingleton (↥X → Bool) :=
      ⟨fun f g => funext fun i => absurd (Subsingleton.elim i.1 0 ▸ i.2) h⟩
    exact (ncard_le_one (toFinite _)).mpr (fun a _ b _ => Subsingleton.elim a b) |>.trans_lt
      one_lt_two

/-- The hypotheses of the average-case bound can be met by every family of sets: every set has
bias at most `1/2` on rectangles, and the constant threshold `K_n = 1` has logarithm `0 = o(n)`. -/
example (S : ∀ n, Set (Fin n → Bool)) :
    (∀ᶠ n in Filter.atTop, RectangleBias (S n) ((fun _ => 1 : ℕ → ℕ) n) (1 / 2)) ∧
      (fun n => Real.log ((fun _ => 1 : ℕ → ℕ) n)) =o[Filter.atTop] fun n => (n : ℝ) := by
  refine ⟨Filter.Eventually.of_forall fun n => rectangleBias_one_half _ _, ?_⟩
  simpa only [Nat.cast_one, Real.log_one] using Asymptotics.isLittleO_zero _ _

/-- A set with no bias at all: on two bits, the inputs whose bits differ fill exactly half of
every rectangle with both sides of size at least two. Such a rectangle cuts the two bits apart and
has every assignment on both sides. -/
example : RectangleBias {x : Fin 2 → Bool | x 0 ≠ x 1} 2 0 := by
  intro X A B hA hB
  have hcard (Y : Set (Fin 2)) : Nat.card (Y → Bool) = 2 ^ Y.ncard := by
    rw [Nat.card_fun, Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_bool]
  have hA' : A.ncard ≤ 2 ^ X.ncard := hcard X ▸ ncard_le_card A
  have hB' : B.ncard ≤ 2 ^ Xᶜ.ncard := hcard Xᶜ ▸ ncard_le_card B
  have hX : X.ncard + Xᶜ.ncard = 2 := by
    rw [ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  -- Both sides are nontrivial, so each bit lies on its own side.
  have h1 : X.ncard = 1 ∧ Xᶜ.ncard = 1 := by
    rcases Nat.lt_or_ge X.ncard 1 with h | h
    · rw [show X.ncard = 0 by omega] at hA'
      omega
    · rcases Nat.lt_or_ge Xᶜ.ncard 1 with h' | h'
      · rw [show Xᶜ.ncard = 0 by omega] at hB'
        omega
      · omega
  -- Hence both sides are everything, and so is the rectangle.
  have hAu : A = univ := eq_of_subset_of_ncard_le (subset_univ A)
    (by rw [ncard_univ, hcard, h1.1]; omega)
  have hBu : B = univ := eq_of_subset_of_ncard_le (subset_univ B)
    (by rw [ncard_univ, hcard, h1.2]; omega)
  have hR : rectangle X A B = univ := by
    subst hAu hBu
    ext x
    simp [rectangle]
  have hS : {x : Fin 2 → Bool | x 0 ≠ x 1}.ncard = 2 := by
    rw [ncard_eq_toFinset_card', toFinset_ofPred]
    decide
  rw [hR, Set.univ_inter, hS, ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]
  norm_num

end Frontier

section KolmogorovNW

open Cslib Cslib.Kolmogorov Cslib.Crypto.PRG.NisanWigderson

/-- The literal description method runs any list decoder whose outputs have bounded length, so the
hypothesis of the Nisan–Wigderson step to short descriptions can be met. -/
example {ℓ n a m L K : ℕ} (D : Design ℓ n a m)
    (C : ListCode (List Bool) (Fin n → Bool) Bool L) (test : (Fin m → Bool) → Bool)
    (hC : ∀ w k, (C.decode w k).length ≤ K) :
    DescriptionMethod.ReconstructionDecoder DescriptionMethod.literal D C test K K where
  program R k := C.decode (R.guess test) k
  length_program_le _ k := (hC _ k).trans (Nat.le_add_left _ _)
  mem_runFor_program _ k := DescriptionMethod.mem_literal_runFor.mpr ⟨hC _ k, rfl⟩

/-- List decoding, a hypothesis of the Nisan–Wigderson reconstruction, is satisfiable: a decoder
listing all `Fintype.card α` messages decodes any code at every radius. -/
example {α ι : Type} [Fintype α] [Fintype ι] (encode : α → ι → Bool) (ρ : ℝ) :
    (⟨encode, fun _ k => (Fintype.equivFin α).symm k⟩ :
      ListCode α ι Bool (Fintype.card α)).ListDecodes ρ :=
  ListCode.listDecodes_of_surjective (fun _ => (Fintype.equivFin α).symm.surjective) ρ

end KolmogorovNW

section Composition

open Cslib.PCP

/-- Composition keeps an unsatisfiable constraint graph unsatisfiable by a constant margin: the
graph asking two equal labels to differ composes to a graph of positive value. -/
example : 0 < (⟨fun _ ↦ (), fun _ ↦ (), fun _ (a b : Bool) ↦ a ≠ b⟩ :
    ConstraintGraph Unit Unit Bool).compose.unsatVal := by
  set G : ConstraintGraph Unit Unit Bool := ⟨fun _ ↦ (), fun _ ↦ (), fun _ a b ↦ a ≠ b⟩
  have h := G.le_unsatVal_compose
  have hG : 0 < G.unsatVal := G.unsatVal_pos_iff.2 fun ⟨σ, hσ⟩ ↦ hσ () rfl
  linarith

/-- The honest proof passes the Hadamard assignment tester with probability one. -/
example :
    (hadamardTester (α := Fin 2) (· = ·)).acceptProb (HadamardTester.honestProof ![0, 0]) = 1 :=
  HadamardTester.acceptProb_honestProof rfl

/-- Powering an unsatisfiable regular constraint graph whose spectral expansion is below one gives a
graph of positive value. -/
example {V D α : Type*} [Fintype V] [Fintype D] [Fintype α] [Nonempty α]
    (R : RegularConstraintGraph V D α) (hR : ¬ R.toConstraintGraph.Satisfiable)
    (hl : R.graph.spectralExpansion < 1) :
    0 < (R.power (4 * Fintype.card α * (2 - 1)) 2).toConstraintGraph.unsatVal := by
  refine lt_of_lt_of_le ?_ (R.le_unsatVal_power _ 2 le_rfl rfl le_rfl hl)
  have h₀ := (R.toConstraintGraph.unsatVal_pos_iff).2 hR
  have hl' : 0 < 1 - R.graph.spectralExpansion := sub_pos.2 hl
  have hα : (1 : ℝ) ≤ Fintype.card α := by exact_mod_cast Fintype.card_pos
  apply mul_pos
  · norm_num
    positivity
  · exact lt_min h₀ (by positivity)

end Composition

section FrontierReduction

open Cslib.Circuits Cslib.Circuits.Frontier Set

/-- The hypotheses of the reduction theorem are satisfiable: a one-gate circuit decides the
inputs with exactly one bit set, an 8-element 2-rectangle-free set. -/
example : ∃ (c : Circuit (fullSignature 8 Bool) 8 1) (S : Set (Fin 8 → Bool)),
    c.FanInAtMost 8 ∧ c.Decides fullInterpretation {true} S ∧ RectangleFree S 2 ∧
      Nat.card Bool * 2 ^ 2 ≤ S.ncard := by
  let S : Set (Fin 8 → Bool) := {x | {i | x i = true}.ncard = 1}
  -- Two set bits of an input of `S` coincide.
  have huniq {x} (hx : x ∈ S) {i j} (hi : x i = true) (hj : x j = true) : i = j := by
    obtain ⟨k, hk⟩ := ncard_eq_one.mp hx
    exact ((hk ▸ hi : i ∈ ({k} : Set _))).trans (hk ▸ hj : j ∈ ({k} : Set _)).symm
  refine ⟨⟨Program.empty.gate ⟨.fn fun x => decide ({i | x i = true}.ncard = 1),
    fun k => .input k⟩, fun _ => .gate 0⟩, S, ⟨trivial, le_rfl⟩, fun x => ?_, ?_, ?_⟩
  · change _ ↔ decide ({i | x i = true}.ncard = 1) = true
    simp [S]
  · -- A rectangle with two distinct sides on `X` forces every side on `Xᶜ` to be zero.
    refine rectangleFree_iff.mpr fun X A B hAB => ?_
    by_contra! h
    obtain ⟨a, a', ha, ha', hne⟩ := (one_lt_ncard_iff).mp (by omega : 1 < A.ncard)
    obtain ⟨b, b', hb, hb', hne'⟩ := (one_lt_ncard_iff).mp (by omega : 1 < B.ncard)
    classical
    let z (a : X → Bool) (b : ↥Xᶜ → Bool) : Fin 8 → Bool :=
      fun i => if h : i ∈ X then a ⟨i, h⟩ else b ⟨i, h⟩
    have hz {a b} (ha : a ∈ A) (hb : b ∈ B) : z a b ∈ S := by
      refine hAB ⟨?_, ?_⟩
      · convert ha using 1; funext ⟨i, hi⟩; simp [z, hi]
      · convert hb using 1; funext ⟨i, hi⟩; simp [z, show i ∉ X from hi]
    have hzero {a} (ha : a ∈ A) {i : X} (hi : a i = true) {b} (hb : b ∈ B) :
        b = fun _ => false := by
      funext j
      by_contra hj
      have := huniq (hz ha hb) (i := i) (j := j) (by simp [z, i.2, hi])
        (by simpa [z, show (j : Fin 8) ∉ X from j.2] using hj)
      exact j.2 (this ▸ i.2)
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    rcases Bool.eq_false_or_eq_true (a i) with h₁ | h₁
    · exact hne' ((hzero ha h₁ hb).trans (hzero ha h₁ hb').symm)
    · have h₂ : a' i = true := by simpa [h₁] using hi
      exact hne' ((hzero ha' h₂ hb).trans (hzero ha' h₂ hb').symm)
  · -- The eight unit vectors lie in `S`.
    let e (i : Fin 8) : Fin 8 → Bool := fun j => decide (j = i)
    have he : Function.Injective e := fun i i' h => by simpa [e] using congrFun h i
    calc Nat.card Bool * 2 ^ 2 = (range e).ncard := by simp [ncard_range_of_injective he]
      _ ≤ S.ncard := ncard_le_ncard (range_subset_iff.mpr fun i => by simp [S, e]) (toFinite _)

/-- The hypotheses of the spanning-tree layout theorem can be met: one edge between two vertices
is connected, loopless and of maximum degree one, and it has a layout of width at most one. -/
example : ∃ π : Layout (Fin 2),
    (⟨fun _ => 0, fun _ => 1⟩ : Multigraph (Fin 2) Unit).width π ≤ 1 := by
  set G : Multigraph (Fin 2) Unit := ⟨fun _ => 0, fun _ => 1⟩
  have hadj : G.toSimpleGraph.Adj 0 1 := G.toSimpleGraph_adj.mpr ⟨by decide, (), rfl⟩
  have hconn : G.toSimpleGraph.Connected := by
    refine (SimpleGraph.connected_iff_exists_forall_reachable _).mpr ⟨0, fun v => ?_⟩
    fin_cases v
    exacts [SimpleGraph.Reachable.refl _, hadj.reachable]
  have hdeg : G.MaxDegreeLE 1 := fun v => (Set.ncard_le_card _).trans (by simp)
  obtain ⟨π, hπ⟩ := Multigraph.exists_width_le_cycleRank_add hconn hdeg
  refine ⟨π, hπ.trans ?_⟩
  simp [Multigraph.cycleRank, Nat.log_eq_one_iff'.mpr (by decide : 2 ≤ 2 ∧ 2 < 2 * 2)]

end FrontierReduction

section FrontierLinear

open Cslib.Circuits Matrix

/-- An arithmetic circuit computing the `1 × 1` Cauchy map `x ↦ -x`: a constant `-1` and a
product. -/
def negCircuit : Circuit (arithSignature ℚ) 1 1 :=
  ⟨(Program.empty.gate ⟨ArithOp.const (-1), Fin.elim0⟩).gate
      ⟨ArithOp.mul, ![.input 0, .gate 0]⟩, fun _ => .gate 1⟩

/-- The `Computes` hypothesis of the arithmetic Cauchy lower bound can be met. -/
example : negCircuit.Computes (arithInterpretation ℚ) (fun x => cauchyNat ℚ 1 *ᵥ x) := by
  intro x; funext i; fin_cases i
  change x 0 * (-1) = (cauchyNat ℚ 1 *ᵥ x) 0
  simp [mulVec, dotProduct, cauchyNat, cauchy_apply]

/-- Explicit Cauchy matrices are totally regular. -/
example : (cauchyNat ℚ 5).IsTotallyRegular := isTotallyRegular_cauchyNat 5

end FrontierLinear

section FrontierLedger

open Cslib.Circuits Cslib.Circuits.Frontier

/-- The ledger hypothesis can be met: every AC⁰ program has a ledger for all of its gates. -/
noncomputable example {n s : ℕ} (p : Program Boolean.Unbounded.signature n s) :
    Ledger (fun _ : Fin s => True) p Boolean.Unbounded.interpretation
      ({_g : Fin s // True} → ZMod 2) :=
  Ledger.ofAggregates fun _ _ => aggregates_unbounded _

end FrontierLedger

section FrontierDecomposable

open Cslib.Circuits Set

/-- A decomposable DAG for the conjunction of two bits: a product of two leaves. -/
def conjunctionDAG : DecomposableDAG (Fin 2) Bool (Option (Fin 2)) where
  scope
    | none => univ
    | some i => {i}
  root := none
  scope_root := rfl
  gate
    | none => .product (some 0) (some 1)
    | some _ => .leaf
  rank
    | none => 1
    | some _ => 0
  values
    | none => {f | ∀ i, f ⟨i, mem_univ i⟩ = true}
    | some _ => {fun _ => true}
  values_subsingleton
    | none, h => nomatch h
    | some _, _ => subsingleton_singleton
  scope_union
    | none, _, h => nomatch h
    | some _, _, h => nomatch h
  rank_union
    | none, _, h => nomatch h
    | some _, _, h => nomatch h
  values_union
    | none, _, h => nomatch h
    | some _, _, h => nomatch h
  scope_product
    | none, _, _, h => by
      cases h
      ext i
      match i with
      | 0 => simp
      | 1 => simp
    | some _, _, _, h => nomatch h
  disjoint_product
    | none, _, _, h => by
      cases h
      simp
    | some _, _, _, h => nomatch h
  rank_product
    | none, _, _, h => by
      cases h
      simp
    | some _, _, _, h => nomatch h
  values_product
    | none, _, _, h, x => by
      cases h
      simp [Fin.forall_fin_two, funext_iff]
    | some _, _, _, h, _ => nomatch h

/-- It represents the conjunction of the two bits. -/
example : conjunctionDAG.accepted = {x | x 0 = true ∧ x 1 = true} := by
  ext x
  exact Fin.forall_fin_two

end FrontierDecomposable

section FrontierGaussian

open Cslib.Circuits.Frontier

/-- `m` disjoint theta graphs, each two vertices joined by three parallel edges. -/
def thetaGraphs (m : ℕ) : Multigraph (Fin m × Bool) (Fin m × Fin 3) :=
  ⟨fun e => (e.1, false), fun e => (e.1, true)⟩

theorem thetaGraphs_loopless (m : ℕ) : (thetaGraphs m).Loopless :=
  fun e h => by simp [thetaGraphs] at h

theorem ncard_incidenceSet_thetaGraphs (m : ℕ) (v : Fin m × Bool) :
    ((thetaGraphs m).incidenceSet v).ncard = 3 := by
  obtain ⟨i, b⟩ := v
  have : (thetaGraphs m).incidenceSet (i, b) = Set.range fun j : Fin 3 => (i, j) := by
    ext ⟨i', j⟩
    cases b <;> simp [thetaGraphs, Multigraph.mem_incidenceSet, eq_comm]
  rw [this, Set.ncard_range_of_injective fun j j' h => by simpa using h]
  simp

/-- The hypotheses of the Gaussian layouts of cubic multigraphs can be met in every size, and
large theta graphs get layouts of width at most `(p + 1)` times their number of vertices. -/
example : ∃ N₀ : ℕ, ∀ m : ℕ, N₀ < 2 * m → ∃ σ : Layout (Fin m × Bool),
    ((thetaGraphs m).width σ : ℝ) ≤
      (Gaussian.gaussianCoefficient + 1) * Nat.card (Fin m × Bool) := by
  obtain ⟨N₀, hN₀⟩ := Gaussian.exists_width_le_gaussianCoefficient one_pos
  exact ⟨N₀, fun m hm => hN₀ _ _ _ (thetaGraphs_loopless m) (ncard_incidenceSet_thetaGraphs m)
    (by simpa [mul_comm] using hm)⟩

end FrontierGaussian

section FrontierCorrelation

open Cslib.Circuits Cslib.Circuits.Frontier Filter Matrix

/-- The headline bound is not vacuous: its rate is positive, it applies to the zero-gate circuit
of fan-in two that outputs the first input (over the full binary basis), and its bound `2^{-γ n}`
is below one for every `n ≥ 1`, while every correlation is at most one. -/
example : ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop,
    |correlation {x | hardForm (n + 1) x} {x : Fin (n + 1) → Bool | x 0 ∈ ({true} : Set Bool)}| ≤
      (2 : ℝ) ^ (-γ * (n + 1 : ℕ)) ∧ (2 : ℝ) ^ (-γ * (n + 1 : ℕ)) < 1 := by
  obtain ⟨γ, hγ, H⟩ := exists_eventually_abs_correlation_hardForm_le.{0}
  refine ⟨γ, hγ, ?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually H] with n hn
  let C : Circuit (fullSignature 2 Bool) (n + 1) 1 := Circuit.wiring _ fun _ => 0
  have hsize : (C.innerSize : ℝ) ≤ 277 / 100 * (n + 1 : ℕ) := by
    have : C.innerSize = 0 := Nat.le_zero.mp (C.innerSize_le_size)
    rw [this, Nat.cast_zero]
    positivity
  refine ⟨hn _ fullInterpretation {true} C (Circuit.fanInAtMost_wiring _ _) hsize, ?_⟩
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    (by have : (0 : ℝ) < (n + 1 : ℕ) := by positivity
        nlinarith)

/-- The hypothesis on the cut ranks is met by the explicit family at a concrete length: every
bisection of `100` coordinates has cut rank at least `19 = 50 - 31` in the polar matrix of
`hardMatrix 100`, and bisections exist. -/
example : (∃ U : Set (Fin 100), U.ncard = 50) ∧
    ∀ U : Set (Fin 100), U.ncard = 50 → 19 ≤ (hardMatrix 100 + (hardMatrix 100)ᵀ).cutRank U := by
  refine ⟨Set.exists_subset_card_eq (s := Set.univ) (by simp) |>.imp fun _ h => h.2, ?_⟩
  intro U hU
  have h := half_le_cutRank_hardMatrix 100 hU
  have hs : Nat.sqrt 50 = 7 := (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩).symm
  rw [show (100 : ℕ) / 2 = 50 from rfl, hs] at h
  omega

/-- Robustness is not trivial at a concrete size: the fixed `100 × 100` matrix has every square
block with `k` rows of rank at least `k - 21`. -/
example : (robustMatrix 100).SubmatrixRobust 21 := by
  have h := robustMatrix_submatrixRobust 100
  rwa [show Nat.sqrt 100 = 10 from (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩).symm] at h

/-- The threshold `c* ≈ 2.78125` exceeds `2.77`, so the hypothesis `c < c*` of
`exists_eventually_abs_correlation_hardForm_le_of_lt` is satisfiable. -/
example : (277 / 100 : ℝ) < 1 + Real.pi / (6 * Real.arccos ((1 + 2 * √2) / 4)) := by
  linarith [correlationThreshold_ge]

/-- The rate hypothesis of `eventually_abs_correlation_hardForm_le` is satisfiable at `c = 2`. -/
example : ∃ γ : ℝ, 0 < γ ∧ γ < (1 + Real.pi / (6 * Real.arccos ((1 + 2 * √2) / 4)) - 2) /
      (2 * (1 + Real.pi / (3 * Real.arccos ((1 + 2 * √2) / 4)))) := by
  have h₁ := correlationThreshold_ge
  have h₂ := Gaussian.circuitCoefficient_ge_456
  refine ⟨(1 + Real.pi / (6 * Real.arccos ((1 + 2 * √2) / 4)) - 2) /
      (2 * (1 + Real.pi / (3 * Real.arccos ((1 + 2 * √2) / 4)))) / 2, ?_, ?_⟩
  · apply div_pos (div_pos (by linarith) (by linarith)) two_pos
  · have : 0 < (1 + Real.pi / (6 * Real.arccos ((1 + 2 * √2) / 4)) - 2) /
        (2 * (1 + Real.pi / (3 * Real.arccos ((1 + 2 * √2) / 4)))) :=
      div_pos (by linarith) (by linarith)
    linarith

end FrontierCorrelation

section FrontierWitness

open Cslib.Circuits Cslib.Circuits.Frontier Filter

/-- The hypotheses `hfree`, `hK` and `hdense` of the worst-case claim `CircuitLowerBound` can be
met over the alphabet `Bool`, with `K_n = n + 2`. -/
example : ∃ (S : ∀ n, Set (Fin n → Bool)) (K : ℕ → ℕ),
    (∀ᶠ n in atTop, RectangleFree (S n) (K n)) ∧
    (fun n => Real.log (K n)) =o[atTop] (fun n => (n : ℝ)) ∧
    (fun n => n * Real.log (Nat.card Bool) - Real.log (S n).ncard) =o[atTop]
      (fun n => (n : ℝ)) := by
  obtain ⟨S, hfree, hK, hdense, -⟩ := exists_rectangleFree_family
  exact ⟨S, fun n => n + 2, hfree, hK, hdense⟩

/-- So `CircuitLowerBound 4` applies non-vacuously: for every `ε > 0` and all large `n`, circuits
of fan-in at most two deciding a set of at least `2 ^ (n - 1)` bit strings (half of the cube) need
more than `(4 - ε) n` gates of positive arity. -/
example : ∃ S : ∀ n, Set (Fin n → Bool), (∀ n, 2 ^ (n - 1) ≤ (S n).ncard) ∧
    ∀ ε > (0 : ℝ), ∀ᶠ n in atTop,
      ∀ (σ : Signature.{0}) (I : Interpretation σ Bool) (Acc : Set Bool) (c : Circuit σ n 1),
        c.FanInAtMost 2 → c.Decides I Acc (S n) → (4 - ε) * n < c.innerSize := by
  obtain ⟨S, hfree, hK, hdense, hhalf⟩ := exists_rectangleFree_family
  exact ⟨S, hhalf, circuitLowerBound_four.{0, 0} Bool S (fun n => n + 2) hfree hK hdense⟩

/-- The hypotheses of the average-case claim `AverageCaseBound` can be met over the alphabet
`Bool` with bias `b_n = 1 / (n + 1)` tending to zero, and `K_n = (n + 1) ^ 3`. -/
example : ∃ (S : ∀ n, Set (Fin n → Bool)) (K : ℕ → ℕ) (b : ℕ → ℝ),
    (∀ᶠ n in atTop, RectangleBias (S n) (K n) (b n)) ∧
    (fun n => Real.log (K n)) =o[atTop] (fun n => (n : ℝ)) ∧ Tendsto b atTop (nhds 0) := by
  obtain ⟨S, hbias, hK, hb⟩ := exists_rectangleBias_family
  exact ⟨S, fun n => (n + 1) ^ 3, fun n => 1 / ((n : ℝ) + 1), hbias, hK, hb⟩

/-- The bias bound constrains such sets once rectangles with both sides of size at least `K_n`
exist. For `60` coordinates the cube is a rectangle with both sides of size `2 ^ 30 ≥ 61 ^ 3`, so
a set of bias at most `1 / 61` on rectangles with both sides of size at least `61 ^ 3` has within
`2 ^ 60 / 61` of `2 ^ 59` elements; and such a set exists. -/
example : ∃ S : Set (Fin 60 → Bool), RectangleBias S (61 ^ 3) (1 / 61) ∧
    |(S.ncard : ℝ) - 2 ^ 59| ≤ 2 ^ 60 / 61 := by
  obtain ⟨S, hS⟩ := exists_rectangleBias (ι := Fin 60) (K := 61 ^ 3) (b := 1 / 61) (by norm_num)
    (by norm_num)
  refine ⟨S, hS, ?_⟩
  obtain ⟨X, -, hX⟩ := Set.exists_subset_card_eq (s := (Set.univ : Set (Fin 60))) (n := 30)
    (by simp)
  have hXc : Xᶜ.ncard = 30 := by
    have := Set.ncard_add_ncard_compl X
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at this
    omega
  have hcard (Y : Set (Fin 60)) (hY : Y.ncard = 30) :
      (Set.univ : Set (Y → Bool)).ncard = 2 ^ 30 := by
    rw [Set.ncard_univ, Nat.card_fun, Nat.card_coe_set_eq, hY, Nat.card_eq_fintype_card,
      Fintype.card_bool]
  have h := hS X Set.univ Set.univ (by rw [hcard X hX]; norm_num) (by rw [hcard Xᶜ hXc]; norm_num)
  have hR : rectangle X (Set.univ : Set (X → Bool)) Set.univ = Set.univ := by
    ext
    simp [rectangle]
  rw [hR, Set.univ_inter, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin] at h
  convert h using 1 <;> norm_num

/-- So `AverageCaseBound 4` applies with a conclusion tending to `1/2`: for every `ε > 0` there is
a `γ > 0` such that for all large `n`, circuits of fan-in at most two with at most `(4 - ε) n`
gates of positive arity agree with a set of bias `1 / (n + 1)` on at most a
`1/2 + 1 / (n + 1) + exp (-γ n)` fraction of the inputs. -/
example : ∃ S : ∀ n, Set (Fin n → Bool), ∀ ε > (0 : ℝ), ∃ γ > (0 : ℝ), ∀ᶠ n in atTop,
    ∀ (σ : Signature.{0}) (I : Interpretation σ Bool) (Acc : Set Bool) (c : Circuit σ n 1),
      c.FanInAtMost 2 → (c.innerSize : ℝ) ≤ (4 - ε) * n →
        agreement (S n) {x | c.eval I x 0 ∈ Acc} ≤
          1 / 2 + 1 / ((n : ℝ) + 1) + Real.exp (-(γ * n)) := by
  obtain ⟨S, hbias, hK, -⟩ := exists_rectangleBias_family
  refine ⟨S, fun ε hε => ?_⟩
  obtain ⟨γ, hγ, H⟩ := averageCaseBound_four.{0, 0} ε hε
  exact ⟨γ, hγ, H Bool S (fun n => (n + 1) ^ 3) (fun n => 1 / ((n : ℝ) + 1)) hbias hK⟩

end FrontierWitness

section ThresholdParity

open Cslib.Circuits Cslib.Circuits.Boolean

/-- The parity circuit over threshold gates evaluates correctly on an input, by computation. -/
example : (Threshold.parityCircuit 4).eval Threshold.interpretation ![true, false, true, true] 0 =
    true := by
  decide

/-- Its counts: `n + 1` threshold gates and `n + n / 2 + 1` gates in all. -/
example : (Threshold.parityCircuit 5).program.cost Threshold.thresholdCost = 6 ∧
    (Threshold.parityCircuit 5).size = 8 :=
  ⟨Threshold.cost_parityCircuit, Threshold.size_parityCircuit⟩

/-- The majority circuit of the threshold gate `Th^3_2` evaluates correctly, by computation. -/
example : (Threshold.majorityCircuit (.threshold 3 2)).eval (Unbounded.extInterpretation majority)
      ![true, false, true] 0 = true ∧
    (Threshold.majorityCircuit (.threshold 3 2)).eval (Unbounded.extInterpretation majority)
      ![false, false, true] 0 = false := by
  decide

end ThresholdParity

section SmolenskyField

open Cslib.Circuits Cslib.Circuits.Boolean

open Classical in
/-- Smolensky's approximation applies over the field of order `9`, not only over `ZMod 3`. -/
example {n ℓ : ℕ} (hℓ : 1 ≤ ℓ) (C : Circuit Unbounded.extSignature n 1) :
    ∃ Q ∈ BitString.lowDegree (GaloisField 3 2) (Fin n) (((3 - 1) * ℓ) ^ C.depth),
      #(univ.filter fun x => Q x ≠
        BitString.bitVal (GaloisField 3 2) (C.eval (Unbounded.extInterpretation (modGate 3)) x 0)) *
        2 ^ ℓ ≤ C.size * 2 ^ n :=
  Smolensky.exists_lowDegree_approx hℓ C

end SmolenskyField

end ComplexityTests.NonVacuity
