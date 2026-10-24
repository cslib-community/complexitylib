/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.BranchingProgram.MonoidProgram
public import Complexity.Computability.Circuit.Boolean.NegationNormalForm
public import Complexity.Foundations.GroupTheory.Perm.FiveCycle
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Commutator
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Data.List.ProdSigma
import Mathlib.Tactic.Ring

/-!
# Barrington's theorem

**Barrington's theorem**: a De Morgan formula of depth `d`, with negations free, becomes a
permutation branching program of width `5` and length at most `4 ^ d`, which is a fixed `5`-cycle
on the inputs where the formula is true and the identity elsewhere
(`Formula.exists_monoidProgram_computes`) [Barrington1989], [Jukna, Section 15.4][Jukna2012]. The
programs here are the programs over Boolean inputs `BitString n = Fin n → Bool`, those of
`MonoidProgram (Fin n) Bool M`.

The construction works for every `5`-cycle `σ` at once. An input `xᵢ` reads `xᵢ` and selects `σ`
or the identity (`Instruction.cond i σ 1`). A negation `σ⁻¹`-computes its argument and multiplies
by `σ`. For a conjunction, `σ` is the commutator `⁅α, β⁆ = α β α⁻¹ β⁻¹` of two `5`-cycles
(`Equiv.Perm.IsFiveCycle.exists_commutator`); running the programs for the arguments with `α` and
`β`, then their inverses, gives `σ` exactly when both arguments are true. A disjunction is the
negation of the conjunction of the negations. This works in any group with a set of elements
closed under inverses in which every element is a commutator of two of them
(`Formula.exists_monoidProgram_computes_of_forall_commutator`). Five-cycles are even, so the
programs select only elements of the alternating group `A₅`
(`Formula.exists_monoidProgram_alternatingGroup_computes`); mapped into `S₅`, they are permutation
branching programs of width `5` (`Formula.exists_monoidProgram_computes`).

Conversely, whether a branching program of width `w`, a program over `Function.End (Fin w)`, maps
`a` to `b` is a formula of depth `O(log w · log L)`: split the program in halves and take the
disjunction over the middle values (`MonoidProgram.entryFormulaMul`), recursively along a balanced
tree (`MonoidProgram.entryFormula`, by `List.balancedFold`). So a branching program of width
`w` and length `L` is a formula of depth `(⌈log₂ w⌉ + 1) ⌈log₂ L⌉ + ⌈log₂ w⌉`
(`MonoidProgram.exists_formula`), with negations only at the leaves, and constant-width
polynomial-length branching programs and logarithmic-depth formulas compute the same functions.

## Main definitions

* `Cslib.BranchingPrograms.Instruction.entryFormula`: the formula saying that an instruction maps
  `a` to `b`.
* `Cslib.BranchingPrograms.MonoidProgram.entryFormula`: the formula saying that a branching
  program maps `a` to `b`.
* `Cslib.BranchingPrograms.MonoidProgram.entryFormulaMul`: the formulas of a program from those of
  its two halves.

## Main results

* `Cslib.Circuits.Formula.exists_monoidProgram_computes_of_forall_commutator`: Barrington's
  construction in a group.
* `Cslib.Circuits.Formula.exists_monoidProgram_alternatingGroup_computes`,
  `Cslib.Circuits.Formula.exists_monoidProgram_computes`: Barrington's theorem, with programs over
  `A₅` and over `S₅`.
* `Cslib.Circuits.Boolean.exists_monoidProgram_alternatingGroup_computes_of_formulaDepth`,
  `Cslib.Circuits.Boolean.exists_monoidProgram_computes_of_formulaDepth`: the same for Boolean
  functions, in terms of their formula depth.
* `Cslib.BranchingPrograms.MonoidProgram.exists_formula`: branching programs give formulas of
  logarithmic depth.
* `Cslib.BranchingPrograms.MonoidProgram.Computes.exists_formula`: so do permutation branching
  programs.

## References

* [D. A. Barrington, *Bounded-width polynomial-size branching programs recognize exactly those
  languages in NC¹*][Barrington1989]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

open Equiv Equiv.Perm Cslib.BranchingPrograms Cslib.Circuits.Boolean
open scoped commutatorElement

variable {n w : ℕ}

/-! ### Barrington's theorem -/

namespace Cslib.Circuits.Formula

open MonoidProgram

/-- **Barrington's construction** in a group `G`. Let `C` be a set of elements of `G`, closed
under inverses, in which every element is the commutator of two elements of `C`. For every
`σ ∈ C`, a De Morgan formula of depth `d`, with negations and constants free, has a program over
`G` of length at most `4 ^ d` that `σ`-computes it. -/
theorem exists_monoidProgram_computes_of_forall_commutator {G : Type*} [Group G] [NeZero n]
    {C : Set G} (hinv : ∀ σ ∈ C, σ⁻¹ ∈ C) (hcomm : ∀ σ ∈ C, ∃ α ∈ C, ∃ β ∈ C, ⁅α, β⁆ = σ)
    (F : Formula signature n) {σ : G} (hσ : σ ∈ C) :
    ∃ P : MonoidProgram (Fin n) Bool G, P.length ≤ 4 ^ F.depthWith binaryCost ∧
      P.Computes σ (F.eval interpretation) := by
  induction F generalizing σ with
  | input i =>
    refine ⟨FreeMonoid.of (.cond i σ 1), by simp, fun x => ?_⟩
    cases h : x i <;> simp [h]
  | gate op args ih =>
    cases op with
    | const c =>
      cases c
      · exact ⟨1, by simp, fun x => by simp [interpretation]⟩
      · exact ⟨FreeMonoid.of (.const 0 σ), by simp, fun x => by simp [interpretation]⟩
    | not =>
      obtain ⟨P, hlen, hP⟩ := ih 0 (hinv σ hσ)
      refine ⟨mulLeft σ P, (length_mulLeft σ P).trans_le (max_le ?_ (hlen.trans ?_)),
        fun x => (hP.not x).trans (by simp [interpretation])⟩
      · exact Nat.one_le_pow _ _ (by decide)
      · exact Nat.pow_le_pow_right (by decide) (by simp)
    | and =>
      obtain ⟨α, hα, β, hβ, rfl⟩ := hcomm σ hσ
      obtain ⟨P, hPlen, hP⟩ := ih 0 hα
      obtain ⟨Q, hQlen, hQ⟩ := ih 1 hβ
      refine ⟨P * Q * P.inv * Q.inv, ?_, fun x => (hP.and hQ x).trans rfl⟩
      set D : ℕ := max (depthWith (σ := signature) binaryCost (args 0))
        (depthWith (σ := signature) binaryCost (args 1))
      have hd : (gate (σ := signature) Op.and args).depthWith binaryCost = D + 1 := by
        simp [D, Fin.univ_succ]
      have h₀ : P.length ≤ 4 ^ D :=
        hPlen.trans (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
      have h₁ : Q.length ≤ 4 ^ D :=
        hQlen.trans (Nat.pow_le_pow_right (by decide) (le_max_right _ _))
      calc (P * Q * P.inv * Q.inv).length = 2 * (P.length + Q.length) := by
            simp only [FreeMonoid.length_mul, length_inv]
            omega
        _ ≤ 2 * (4 ^ D + 4 ^ D) := Nat.mul_le_mul_left 2 (Nat.add_le_add h₀ h₁)
        _ = 4 ^ (D + 1) := by ring
        _ = 4 ^ (gate (σ := signature) Op.and args).depthWith binaryCost := by rw [hd]
    | or =>
      obtain ⟨α, hα, β, hβ, hαβ⟩ := hcomm σ⁻¹ (hinv σ hσ)
      obtain ⟨P, hPlen, hP⟩ := ih 0 (hinv α hα)
      obtain ⟨Q, hQlen, hQ⟩ := ih 1 (hinv β hβ)
      let R := mulLeft α P * mulLeft β Q * (mulLeft α P).inv * (mulLeft β Q).inv
      have hR : R.Computes σ⁻¹ fun x => !(args 0).eval interpretation x &&
          !(args 1).eval interpretation x := by
        rw [← hαβ]
        exact hP.not.and hQ.not
      set D : ℕ := max (depthWith (σ := signature) binaryCost (args 0))
        (depthWith (σ := signature) binaryCost (args 1))
      have hd : (gate (σ := signature) Op.or args).depthWith binaryCost = D + 1 := by
        simp [D, Fin.univ_succ]
      have hD : 1 ≤ 4 ^ D := Nat.one_le_pow _ _ (by decide)
      have h₀ : (mulLeft α P).length ≤ 4 ^ D := (length_mulLeft α P).trans_le (max_le hD
        (hPlen.trans (Nat.pow_le_pow_right (by decide) (le_max_left _ _))))
      have h₁ : (mulLeft β Q).length ≤ 4 ^ D := (length_mulLeft β Q).trans_le (max_le hD
        (hQlen.trans (Nat.pow_le_pow_right (by decide) (le_max_right _ _))))
      have hRlen : R.length ≤ 4 ^ (gate (σ := signature) Op.or args).depthWith binaryCost :=
        calc R.length = 2 * ((mulLeft α P).length + (mulLeft β Q).length) := by
              simp only [R, FreeMonoid.length_mul, length_inv]
              omega
          _ ≤ 2 * (4 ^ D + 4 ^ D) := Nat.mul_le_mul_left 2 (Nat.add_le_add h₀ h₁)
          _ = 4 ^ (D + 1) := by ring
          _ = 4 ^ (gate (σ := signature) Op.or args).depthWith binaryCost := by rw [hd]
      refine ⟨mulLeft σ R, (length_mulLeft σ R).trans_le
        (max_le (Nat.one_le_pow _ _ (by decide)) hRlen), fun x => ?_⟩
      · rw [hR.not x]
        simp [interpretation]

/-- **Barrington's theorem in `A₅`.** For every `5`-cycle `σ`, a De Morgan formula of depth `d`,
with negations and constants free, is `σ`-computed by a program of length at most `4 ^ d` over the
alternating group `A₅`: five-cycles are even. -/
theorem exists_monoidProgram_alternatingGroup_computes [NeZero n] (F : Formula signature n)
    {σ : alternatingGroup (Fin 5)} (hσ : IsFiveCycle (σ : Perm (Fin 5))) :
    ∃ P : MonoidProgram (Fin n) Bool (alternatingGroup (Fin 5)),
      P.length ≤ 4 ^ F.depthWith binaryCost ∧ P.Computes σ (F.eval interpretation) :=
  F.exists_monoidProgram_computes_of_forall_commutator
    (C := {σ : alternatingGroup (Fin 5) | IsFiveCycle (σ : Perm (Fin 5))})
    (fun _ h => by simpa using h.inv) (fun _ h => by
      obtain ⟨α, β, hα, hβ, h⟩ := h.exists_commutator
      exact ⟨⟨α, hα.mem_alternatingGroup⟩, hα, ⟨β, hβ.mem_alternatingGroup⟩, hβ,
        Subtype.ext (by simpa [commutatorElement_def] using h)⟩) hσ

/-- **Barrington's theorem.** For every `5`-cycle `σ`, a De Morgan formula of depth `d`, with
negations and constants free, has a permutation branching program of width `5` and length at most
`4 ^ d` that `σ`-computes it: the program over `A₅` mapped into `S₅`. -/
theorem exists_monoidProgram_computes [NeZero n] (F : Formula signature n) {σ : Perm (Fin 5)}
    (hσ : IsFiveCycle σ) :
    ∃ P : MonoidProgram (Fin n) Bool (Perm (Fin 5)), P.length ≤ 4 ^ F.depthWith binaryCost ∧
      P.Computes σ (F.eval interpretation) := by
  obtain ⟨P, hlen, hP⟩ :=
    F.exists_monoidProgram_alternatingGroup_computes (σ := ⟨σ, hσ.mem_alternatingGroup⟩) hσ
  exact ⟨P.map (alternatingGroup (Fin 5)).subtype, (length_map _ P).trans_le hlen, hP.map _⟩

end Cslib.Circuits.Formula

namespace Cslib.Circuits.Boolean

/-- A function of formula depth `d` is `σ`-computed, for every `5`-cycle `σ`, by a program over the
alternating group `A₅` of length at most `4 ^ d`. -/
theorem exists_monoidProgram_alternatingGroup_computes_of_formulaDepth [NeZero n]
    (f : BooleanFunction n) {σ : alternatingGroup (Fin 5)} (hσ : IsFiveCycle (σ : Perm (Fin 5))) :
    ∃ P : MonoidProgram (Fin n) Bool (alternatingGroup (Fin 5)),
      P.length ≤ 4 ^ formulaDepth f ∧ P.Computes σ f := by
  obtain ⟨F, hF, hd⟩ := exists_computes_depthWith_eq_formulaDepth f
  obtain ⟨P, hlen, hP⟩ := F.exists_monoidProgram_alternatingGroup_computes hσ
  exact ⟨P, hd ▸ hlen, fun x => (hP x).trans (by rw [hF x])⟩

/-- A function of formula depth `d` is `σ`-computed, for every `5`-cycle `σ`, by a permutation
branching program of width `5` and length at most `4 ^ d`. -/
theorem exists_monoidProgram_computes_of_formulaDepth [NeZero n]
    (f : BooleanFunction n) {σ : Perm (Fin 5)} (hσ : IsFiveCycle σ) :
    ∃ P : MonoidProgram (Fin n) Bool (Perm (Fin 5)),
      P.length ≤ 4 ^ formulaDepth f ∧ P.Computes σ f := by
  obtain ⟨P, hlen, hP⟩ :=
    exists_monoidProgram_alternatingGroup_computes_of_formulaDepth f
      (σ := ⟨σ, hσ.mem_alternatingGroup⟩) hσ
  exact ⟨P.map (alternatingGroup (Fin 5)).subtype, (MonoidProgram.length_map _ P).trans_le hlen,
    hP.map _⟩

end Cslib.Circuits.Boolean

/-! ### The converse -/

namespace Cslib.BranchingPrograms

open Cslib.Circuits

/-- The formula saying that an instruction of a width-`w` branching program maps `a` to `b`: a
constant or a literal. -/
def Instruction.entryFormula (I : Instruction (Fin n) Bool (Function.End (Fin w)))
    (a b : Fin w) : Formula signature n :=
  match decide (I.select false a = b), decide (I.select true a = b) with
  | true, true => .const true
  | false, true => .input I.var
  | true, false => (Formula.input I.var).not
  | false, false => .const false

/-- Evaluating `I.entryFormula a b` at `x` decides whether `I.eval x` maps `a` to `b`. -/
@[simp] theorem Instruction.eval_entryFormula
    (I : Instruction (Fin n) Bool (Function.End (Fin w))) (a b : Fin w) (x : BitString n) :
    (I.entryFormula a b).eval interpretation x = decide ((I.eval x) a = b) := by
  unfold entryFormula
  cases h₀ : decide (I.select false a = b) <;> cases h₁ : decide (I.select true a = b) <;>
    cases hx : x I.var <;> simp_all [Instruction.eval]

/-- The entry formula of an instruction has binary-gate depth zero. -/
@[simp] theorem Instruction.depthWith_entryFormula
    (I : Instruction (Fin n) Bool (Function.End (Fin w))) (a b : Fin w) :
    (I.entryFormula a b).depthWith binaryCost = 0 := by
  unfold entryFormula
  cases decide (I.select false a = b) <;> cases decide (I.select true a = b) <;> simp

/-- The formula of an instruction is a constant or a literal, so in negation normal form. -/
private theorem Instruction.isNNF_entryFormula (I : Instruction (Fin n) Bool (Function.End (Fin w)))
    (a b : Fin w) : (I.entryFormula a b).IsNNF := by
  unfold entryFormula
  cases decide (I.select false a = b) <;> cases decide (I.select true a = b) <;> constructor

namespace MonoidProgram

/-- The formulas saying that two pieces of a branching program of width `w`, run one after the
other, map `a` to `b`, from the formulas `u` and `v` of the two pieces: the second piece, which
acts first, maps `a` to some `c` that the first piece maps to `b`. -/
def entryFormulaMul (u v : Fin w → Fin w → Formula signature n) (a b : Fin w) :
    Formula signature n :=
  Formula.orList ((List.finRange w).map fun c => (v a c).and (u c b))

/-- The formula saying that a branching program of width `w` maps `a` to `b`: split the program in
halves, and say that the second half maps `a` to some `c` that the first half maps to `b`
(`List.balancedFold`). -/
def entryFormula (P : MonoidProgram (Fin n) Bool (Function.End (Fin w))) (a b : Fin w) :
    Formula signature n :=
  P.toList.balancedFold entryFormulaMul (fun a b => .const (decide (a = b)))
    Instruction.entryFormula a b

/-- Evaluating `P.entryFormula a b` at `x` decides whether `P.eval x` maps `a` to `b`. -/
@[simp] theorem eval_entryFormula (P : MonoidProgram (Fin n) Bool (Function.End (Fin w)))
    (a b : Fin w) (x : BitString n) :
    (P.entryFormula a b).eval interpretation x = decide ((P.eval x) a = b) := by
  rw [eval_eq_prod, entryFormula]
  revert a b
  refine List.balancedFold_induction (op := entryFormulaMul)
    (e := fun a b => .const (decide (a = b))) (f := Instruction.entryFormula)
    (p := fun l (T : Fin w → Fin w → Formula signature n) =>
      ∀ a b, (T a b).eval interpretation x =
        decide (((l.map (·.eval x)).prod : Function.End (Fin w)) a = b))
    (fun a b => by simp; rfl) (fun I a b => by simp) (fun l₁ l₂ u v _ _ hu hv a b => ?_) P.toList
  rw [entryFormulaMul, Formula.eval_orList, List.map_append, List.prod_append, Bool.eq_iff_iff,
    List.any_eq_true, decide_eq_true_iff]
  simp only [List.mem_map, List.mem_finRange, true_and, exists_exists_eq_and, Formula.eval_and,
    hu, hv, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨c, hc, hcb⟩ => by subst hc; exact hcb, fun h => ⟨_, rfl, h⟩⟩

/-- The formula saying that a branching program maps `a` to `b` has negations only at the
leaves. -/
private theorem isNNF_entryFormula (P : MonoidProgram (Fin n) Bool (Function.End (Fin w)))
    (a b : Fin w) :
    (P.entryFormula a b).IsNNF := by
  rw [entryFormula]
  revert a b
  refine List.balancedFold_induction (op := entryFormulaMul)
    (e := fun a b => .const (decide (a = b))) (f := Instruction.entryFormula)
    (p := fun _ (T : Fin w → Fin w → Formula signature n) => ∀ a b, (T a b).IsNNF)
    (fun a b => .const _) (fun I => I.isNNF_entryFormula)
    (fun _ _ u v _ _ hu hv a b => .orList fun F hF => ?_) P.toList
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hF
  exact .and (hv a c) (hu c b)

/-- The entry formula of a width-`w` branching program `P` has binary-gate depth at most
`(⌈log₂ w⌉ + 1) ⌈log₂ P.length⌉`. -/
theorem depthWith_entryFormula_le (P : MonoidProgram (Fin n) Bool (Function.End (Fin w)))
    (a b : Fin w) :
    (P.entryFormula a b).depthWith binaryCost ≤ (Nat.clog 2 w + 1) * Nat.clog 2 P.length := by
  let d (T : Fin w → Fin w → Formula signature n) : ℕ :=
    Finset.univ.sup fun ab : Fin w × Fin w => (T ab.1 ab.2).depthWith binaryCost
  have hd (T : Fin w → Fin w → Formula signature n) (a b : Fin w) :
      (T a b).depthWith binaryCost ≤ d T :=
    Finset.le_sup (f := fun ab : Fin w × Fin w => (T ab.1 ab.2).depthWith binaryCost)
      (Finset.mem_univ (a, b))
  have hop (u v : Fin w → Fin w → Formula signature n) :
      d (entryFormulaMul u v) ≤ max (d u) (d v) + (Nat.clog 2 w + 1) := by
    refine Finset.sup_le fun ab _ => (Formula.depthWith_binaryCost_orList_le (d := max (d u)
      (d v) + 1) fun F hF => ?_).trans ?_
    · obtain ⟨c, -, rfl⟩ := List.mem_map.1 hF
      rw [Formula.depthWith_and, binaryCost_and]
      have := hd u c ab.2
      have := hd v ab.1 c
      omega
    · rw [List.length_map, List.length_finRange]
      omega
  have := List.apply_balancedFold_le d hop (l := P.toList) (D := 0)
    (e := fun a b => .const (decide (a = b))) (f := Instruction.entryFormula)
    (fun I _ => Finset.sup_le fun ab _ => (Instruction.depthWith_entryFormula I ab.1 ab.2).le)
    (fun _ => Finset.sup_le fun ab _ => by simp)
  rw [zero_add] at this
  exact (hd _ a b).trans this

/-- **Branching programs give formulas.** A branching program of width `w` and length `L`, started
at `a` and accepting at the states of `acc`, is computed by a De Morgan formula of depth at most
`(⌈log₂ w⌉ + 1) ⌈log₂ L⌉ + ⌈log₂ w⌉`, with negations only at the leaves (`Formula.IsNNF`). -/
theorem exists_formula (P : MonoidProgram (Fin n) Bool (Function.End (Fin w))) (a : Fin w)
    (acc : Finset (Fin w)) :
    ∃ F : Formula signature n, (∀ x, F.eval interpretation x = decide ((P.eval x) a ∈ acc)) ∧
      F.depthWith binaryCost ≤ (Nat.clog 2 w + 1) * Nat.clog 2 P.length + Nat.clog 2 w ∧
        F.IsNNF := by
  classical
  refine ⟨Formula.orList (acc.toList.map (P.entryFormula a)), fun x => ?_, ?_,
    .orList fun F hF => ?_⟩
  · rw [Formula.eval_orList, Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
    simp
  · refine (Formula.depthWith_binaryCost_orList_le fun F hF => ?_).trans (Nat.add_le_add_left
      (Nat.clog_mono_right 2 (by simpa using acc.card_le_univ)) _)
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hF
    exact depthWith_entryFormula_le P a b
  · obtain ⟨b, -, rfl⟩ := List.mem_map.1 hF
    exact P.isNNF_entryFormula a b

/-- **Permutation branching programs give formulas.** A permutation branching program of width `w`
and length `L` that `σ`-computes `f`, with `σ ≠ 1`, is turned into a De Morgan formula computing
`f` of depth at most `(⌈log₂ w⌉ + 1) ⌈log₂ L⌉ + ⌈log₂ (w ^ 2)⌉`, with negations only at the
leaves (`Formula.IsNNF`): `f` is true where some `a` is mapped to some `b ≠ a`. -/
theorem Computes.exists_formula {P : MonoidProgram (Fin n) Bool (Perm (Fin w))} {σ : Perm (Fin w)}
    {f : BooleanFunction n} (hP : P.Computes σ f) (hσ : σ ≠ 1) :
    ∃ F : Formula signature n, F.Computes interpretation f ∧
      F.depthWith binaryCost ≤ (Nat.clog 2 w + 1) * Nat.clog 2 P.length + Nat.clog 2 (w * w) ∧
        F.IsNNF := by
  let Q := P.map (MulAction.toEndHom (M := Perm (Fin w)) (α := Fin w))
  let pairs := (List.finRange w ×ˢ List.finRange w).filter fun p => p.1 ≠ p.2
  refine ⟨Formula.orList (pairs.map fun p => Q.entryFormula p.1 p.2), fun x => ?_, ?_,
    .orList fun F hF => ?_⟩
  · rw [Formula.eval_orList, List.any_map, Bool.eq_iff_iff, List.any_eq_true]
    simp only [Function.comp_def, eval_entryFormula, Q, eval_map, hP x, pairs, List.mem_filter,
      List.mem_product, List.mem_finRange, true_and, decide_eq_true_eq, Prod.exists, ne_eq]
    cases hf : f x
    · simp only [MulAction.toEndHom, Bool.false_eq_true, ↓reduceIte, map_one, iff_false]
      simp only [not_exists, not_and]
      intro a b hab h
      exact hab h
    · simp only [↓reduceIte, iff_true]
      obtain ⟨a, ha⟩ := not_forall.1 fun h => hσ (Perm.ext h)
      exact ⟨a, σ a, fun h => ha h.symm, rfl⟩
  · refine (Formula.depthWith_binaryCost_orList_le fun F hF => ?_).trans (Nat.add_le_add_left
      (Nat.clog_mono_right 2 ?_) _)
    · obtain ⟨p, -, rfl⟩ := List.mem_map.1 hF
      simpa [Q] using depthWith_entryFormula_le Q p.1 p.2
    · rw [List.length_map]
      exact (List.length_filter_le _ _).trans
        (by rw [List.length_product, List.length_finRange])
  · obtain ⟨p, -, rfl⟩ := List.mem_map.1 hF
    exact Q.isNNF_entryFormula p.1 p.2

end MonoidProgram

end Cslib.BranchingPrograms
