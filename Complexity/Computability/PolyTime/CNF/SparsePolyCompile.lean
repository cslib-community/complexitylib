/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.Problems.SAT
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List.Size
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Option
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
public import Complexity.Foundations.BooleanAnalysis.LowDegree
public import Complexity.Logics.Propositional.CNF.ParityTests
public import Mathlib.Data.ZMod.Basic
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Foundations.Data.BitString.ZModTwo
import Mathlib.Data.List.GetD

/-!
# Polynomial-time compilation of CNF parity checks to sparse `𝔽₂` monomial systems

This module implements the executable sparse `𝔽₂` polynomial compilation and heavy-variable
restriction algorithms from §5.5 (pp. 38–39) and §6 / §6.2–6.3 (pp. 39–40, 42–43) of
[OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]:

1. **Canonical monomial-list algebra over `𝔽₂`**: strictly increasing monomials
   (`IsCanonicalMonomial`), duplicate-free equations (`IsCanonicalEquation`), Boolean evaluation
   (`evalMonomialList`, `evalSystem`), and mod-2 symmetric difference (`xorEquation`).
2. **Clause falsification and parity-row compilation (§6 eq. (6.1), §6.2–6.3)**:
   `compileClause`, `compileParityRow`, and `compileParitySystem`, plus width-`k` guarded
   polynomial-time variants (`compileClauseBounded`, `compileParityRowBounded`,
   `compileParitySystemBounded`).
3. **Heavy-variable detection and single-variable restriction (§5.5)**:
   `equationVars`, `varDegree`, `findHeavyVar`, `restrictEquation`, and `restrictSystem`, all
   certified by plain `ComputableInPolyTime`.

## Main definitions

* `Cslib.Complexity.IsCanonicalMonomial`, `Cslib.Complexity.IsCanonicalEquation`: canonical sorted
  monomials and duplicate-free sparse `𝔽₂` equations.
* `Cslib.Complexity.evalMonomialList`, `Cslib.Complexity.evalSystem`: Boolean evaluation of a
  sparse `𝔽₂` equation and common-zero test for a sparse system.
* `Cslib.Complexity.toggleMonomial`, `Cslib.Complexity.reduceEquation`,
  `Cslib.Complexity.xorEquation`: executable mod-2 duplicate cancellation and symmetric difference.
* `Cslib.Complexity.insertSorted`, `Cslib.Complexity.sortDedup`: strictly increasing variable
  insertion and deduplication.
* `Cslib.Complexity.isTautologicalClause`, `Cslib.Complexity.compileClause`,
  `Cslib.Complexity.compileParityRow`, `Cslib.Complexity.compileParitySystem`: executable clause
  falsification and parity-row compilation.
* `Cslib.Complexity.compileClauseBounded`, `Cslib.Complexity.compileParityRowBounded`,
  `Cslib.Complexity.compileParitySystemBounded`: width-`k` guarded polynomial-time compilers.
* `Cslib.Complexity.equationVars`, `Cslib.Complexity.varDegree`, `Cslib.Complexity.findHeavyVar`:
  equation variable support, variable incidence degree, and heavy-variable finder.
* `Cslib.Complexity.restrictEquation`, `Cslib.Complexity.restrictSystem`: single-variable Boolean
  substitution on sparse `𝔽₂` equations and systems.

## Main results

* `Cslib.Complexity.evalMonomialList_xorEquation`, `Cslib.Complexity.length_xorEquation_le`,
  `Cslib.Complexity.isCanonicalEquation_xorEquation`,
  `Cslib.Complexity.length_enc_reduceEquation_le`,
  `Cslib.Complexity.computableInPolyTime_reduceEquation`,
  `Cslib.Complexity.computableInPolyTime_xorEquation`: mod-2 equation reduction/addition specs.
* `Cslib.Complexity.bitVal_evalMonomialList_eq_sum_monomial`,
  `Cslib.Complexity.bitVal_evalMonomialList_mem_lowDegree`: bridge to `BitString.monomial (ZMod 2)`
  and `BitString.lowDegree (ZMod 2) ℕ k`.
* `Cslib.Complexity.evalMonomialList_compileClause`,
  `Cslib.Complexity.length_compileClause_le`, `Cslib.Complexity.length_mem_compileClause_le`,
  `Cslib.Complexity.isCanonicalEquation_compileClause`: clause compilation semantics and bounds.
* `Cslib.Complexity.evalMonomialList_compileParityRow_eq_dotProduct`,
  `Cslib.Complexity.evalSystem_compileParitySystem_iff_passesTests`,
  `Cslib.Complexity.length_compileParityRow_le`,
  `Cslib.Complexity.length_mem_compileParityRow_le`: parity-row semantics and sparsity/degree
  bounds.
* `Cslib.Complexity.computableInPolyTime_compileClauseBounded`,
  `Cslib.Complexity.computableInPolyTime_compileParityRowBounded`,
  `Cslib.Complexity.computableInPolyTime_compileParitySystemBounded`: polynomial-time compilation.
* `Cslib.Complexity.findHeavyVar_eq_some_iff`, `Cslib.Complexity.findHeavyVar_eq_none_iff`,
  `Cslib.Complexity.evalMonomialList_restrictEquation`,
  `Cslib.Complexity.length_restrictEquation_le`, `Cslib.Complexity.length_mem_restrictEquation_le`,
  `Cslib.Complexity.not_mem_of_mem_restrictEquation`,
  `Cslib.Complexity.computableInPolyTime_varDegree`,
  `Cslib.Complexity.computableInPolyTime_findHeavyVar`,
  `Cslib.Complexity.computableInPolyTime_restrictEquation`,
  `Cslib.Complexity.computableInPolyTime_restrictSystem`: heavy-variable and restriction specs.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §5.5 (pp. 38–39) and
  §6 / §6.2–6.3 (pp. 39–40, 42–43)
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Cslib.BitString Turing.MultiTapeTM
open scoped List

/-! ### 1. Canonical Sparse `𝔽₂` Monomial-List Representation & Mod-2 Algebra -/

/-- A canonical multilinear monomial is a strictly increasing list of variable indices. -/
def IsCanonicalMonomial (m : List ℕ) : Prop := m.Pairwise (· < ·)

theorem IsCanonicalMonomial.nodup {m : List ℕ} (hm : IsCanonicalMonomial m) : m.Nodup :=
  hm.imp ne_of_lt

theorem IsCanonicalMonomial.eq_of_toFinset_eq {m₁ m₂ : List ℕ}
    (hm₁ : IsCanonicalMonomial m₁) (hm₂ : IsCanonicalMonomial m₂)
    (h : m₁.toFinset = m₂.toFinset) : m₁ = m₂ :=
  List.Pairwise.eq_of_mem_iff hm₁ hm₂ fun v => by rw [← List.mem_toFinset, h, List.mem_toFinset]

/-- A sparse `𝔽₂` polynomial equation is canonical when its monomial list is duplicate-free and
every monomial is strictly increasing. -/
def IsCanonicalEquation (eq : List (List ℕ)) : Prop :=
  eq.Nodup ∧ ∀ m ∈ eq, IsCanonicalMonomial m

theorem isCanonicalEquation_nil : IsCanonicalEquation [] :=
  ⟨List.nodup_nil, fun _ hm => False.elim (List.not_mem_nil hm)⟩

/-- Evaluate a sparse `𝔽₂` monomial list on a Boolean assignment `σ : ℕ → Bool`. -/
def evalMonomialList (eq : List (List ℕ)) (σ : ℕ → Bool) : Bool :=
  eq.foldl (fun acc m => xor acc (m.all σ)) false

/-- Evaluate a sparse `𝔽₂` polynomial system (`true` iff every equation evaluates to `false`). -/
def evalSystem (sys : List (List (List ℕ))) (σ : ℕ → Bool) : Bool :=
  sys.all fun eq => !evalMonomialList eq σ

private theorem foldl_xor_all (eq : List (List ℕ)) (σ : ℕ → Bool) (init : Bool) :
    eq.foldl (fun acc m => xor acc (m.all σ)) init = xor init (evalMonomialList eq σ) := by
  induction eq generalizing init with
  | nil => simp only [evalMonomialList, List.foldl_nil, Bool.xor_false]
  | cons m _ ih =>
    simp only [evalMonomialList, List.foldl_cons, Bool.false_xor]
    rw [ih, ih (m.all σ), Bool.xor_assoc]

@[simp] theorem evalMonomialList_nil (σ : ℕ → Bool) : evalMonomialList [] σ = false := rfl

@[simp] theorem evalMonomialList_cons (m : List ℕ) (eq : List (List ℕ)) (σ : ℕ → Bool) :
    evalMonomialList (m :: eq) σ = xor (m.all σ) (evalMonomialList eq σ) := by
  simp only [evalMonomialList, List.foldl_cons, Bool.false_xor]
  exact foldl_xor_all eq σ (m.all σ)

theorem evalMonomialList_singleton (m : List ℕ) (σ : ℕ → Bool) :
    evalMonomialList [m] σ = m.all σ := by
  simp only [evalMonomialList_cons, evalMonomialList_nil, Bool.xor_false]

theorem evalMonomialList_append (eq1 eq2 : List (List ℕ)) (σ : ℕ → Bool) :
    evalMonomialList (eq1 ++ eq2) σ = xor (evalMonomialList eq1 σ) (evalMonomialList eq2 σ) := by
  induction eq1 with
  | nil => simp only [List.nil_append, evalMonomialList_nil, Bool.false_xor]
  | cons _ _ ih => simp only [List.cons_append, evalMonomialList_cons, ih, Bool.xor_assoc]

theorem evalSystem_eq_true_iff (sys : List (List (List ℕ))) (σ : ℕ → Bool) :
    evalSystem sys σ = true ↔ ∀ eq ∈ sys, evalMonomialList eq σ = false := by
  simp only [evalSystem, List.all_eq_true, Bool.not_eq_true']

private theorem bitVal_all_eq_monomial (m : List ℕ) (σ : ℕ → Bool) :
    bitVal (ZMod 2) (m.all σ) = monomial (ZMod 2) m.toFinset σ := by
  rw [monomial_apply]
  split_ifs with h'
  · rw [List.all_eq_true.mpr fun i hi => h' i (List.mem_toFinset.mpr hi), bitVal_true]
  · rw [Bool.eq_false_iff.mpr fun h => h' fun i hi =>
      List.all_eq_true.mp h i (List.mem_toFinset.mp hi), bitVal_false]

private theorem bitVal_evalMonomialList_eq_list_sum (eq : List (List ℕ)) (σ : ℕ → Bool) :
    bitVal (ZMod 2) (evalMonomialList eq σ) =
      (eq.map fun m => monomial (ZMod 2) m.toFinset σ).sum := by
  rw [← bitEquiv_symm_apply, evalMonomialList,
    ← List.foldl_map (f := fun m : List ℕ => m.all σ) (g := xor),
    bitEquiv_symm_foldl_xor, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun m _ => ?_)
  simp only [Function.comp_apply, bitEquiv_symm_apply, bitVal_all_eq_monomial]

/-- On a canonical equation `eq`, reading `evalMonomialList eq σ` in `ZMod 2` equals the `Finset`
sum of `BitString.monomial (ZMod 2)` over `(eq.map List.toFinset).toFinset`. -/
theorem bitVal_evalMonomialList_eq_sum_monomial {eq : List (List ℕ)}
    (heq : IsCanonicalEquation eq) (σ : ℕ → Bool) :
    bitVal (ZMod 2) (evalMonomialList eq σ) =
      ∑ S ∈ (eq.map List.toFinset).toFinset, monomial (ZMod 2) S σ := by
  have hnd : (eq.map List.toFinset).Nodup :=
    heq.1.map_on fun m₁ hm₁ m₂ hm₂ h => (heq.2 m₁ hm₁).eq_of_toFinset_eq (heq.2 m₂ hm₂) h
  have hmap : (eq.map fun m => monomial (ZMod 2) m.toFinset σ) =
      (eq.map List.toFinset).map fun S => monomial (ZMod 2) S σ := by
    simp only [List.map_map, Function.comp_def]
  rw [bitVal_evalMonomialList_eq_list_sum, hmap, ← List.sum_toFinset _ hnd]

/-- Every sparse `𝔽₂` equation whose monomials have length at most `k` defines a Boolean-cube
function of `ZMod 2`-degree at most `k`. -/
theorem bitVal_evalMonomialList_mem_lowDegree {k : ℕ} {eq : List (List ℕ)}
    (hdeg : ∀ m ∈ eq, m.length ≤ k) :
    (fun σ : ℕ → Bool => bitVal (ZMod 2) (evalMonomialList eq σ)) ∈ lowDegree (ZMod 2) ℕ k := by
  induction eq with
  | nil =>
    rw [show (fun σ : ℕ → Bool => bitVal (ZMod 2) (evalMonomialList [] σ)) = fun _ => 0 from
      funext fun _ => by simp only [evalMonomialList_nil, bitVal_false]]
    exact const_mem_lowDegree k 0
  | cons m ms ih =>
    rw [show (fun σ : ℕ → Bool => bitVal (ZMod 2) (evalMonomialList (m :: ms) σ)) =
        monomial (ZMod 2) m.toFinset + fun σ => bitVal (ZMod 2) (evalMonomialList ms σ) from
      funext fun σ => by
        rw [evalMonomialList_cons, ← bitEquiv_symm_apply (xor _ _), ← Bool.add_eq_xor, map_add,
          bitEquiv_symm_apply, bitEquiv_symm_apply, bitVal_all_eq_monomial, Pi.add_apply]]
    exact Submodule.add_mem _
      (monomial_mem_lowDegree ((List.toFinset_card_le m).trans (hdeg m List.mem_cons_self)))
      (ih fun m' hm' => hdeg m' (List.mem_cons_of_mem _ hm'))

/-- Toggle the presence of monomial `m` in a duplicate-free list `eq` modulo 2. -/
def toggleMonomial (eq : List (List ℕ)) (m : List ℕ) : List (List ℕ) :=
  if decide (m ∈ eq) then eq.filter (fun m' => decide (m' ≠ m)) else eq ++ [m]

/-- Cancel duplicate monomials in `eq` modulo 2 by folding `toggleMonomial` from `[]`. -/
def reduceEquation (eq : List (List ℕ)) : List (List ℕ) := eq.foldl toggleMonomial []

/-- Executable mod-2 symmetric difference of two sparse `𝔽₂` equations. -/
def xorEquation (eq1 eq2 : List (List ℕ)) : List (List ℕ) := reduceEquation (eq1 ++ eq2)

private theorem nodup_toggleMonomial {eq : List (List ℕ)} (heq : eq.Nodup) (m : List ℕ) :
    (toggleMonomial eq m).Nodup := by
  unfold toggleMonomial; split_ifs with h
  · exact heq.filter _
  · rw [decide_eq_true_iff] at h
    exact List.nodup_middle.mpr (by simpa only [List.append_nil, List.nodup_cons] using ⟨h, heq⟩)

private theorem mem_of_mem_toggleMonomial {eq : List (List ℕ)} {m m' : List ℕ}
    (hm' : m' ∈ toggleMonomial eq m) : m' ∈ eq ∨ m' = m := by
  unfold toggleMonomial at hm'; split_ifs at hm'
  · exact Or.inl (List.mem_filter.mp hm').1
  · exact (List.mem_append.mp hm').imp id List.mem_singleton.mp

private theorem length_toggleMonomial_le (eq : List (List ℕ)) (m : List ℕ) :
    (toggleMonomial eq m).length ≤ eq.length + 1 := by
  unfold toggleMonomial; split_ifs
  · exact (List.length_filter_le _ _).trans (Nat.le_succ _)
  · simp only [List.length_append, List.length_singleton, le_rfl]

private theorem evalMonomialList_toggleMonomial {eq : List (List ℕ)} (heq : eq.Nodup)
    (m : List ℕ) (σ : ℕ → Bool) :
    evalMonomialList (toggleMonomial eq m) σ = xor (evalMonomialList eq σ) (m.all σ) := by
  unfold toggleMonomial; split_ifs with hm
  · rw [decide_eq_true_iff] at hm
    induction eq with
    | nil => exact False.elim (List.not_mem_nil hm)
    | cons x xs ih =>
      rw [List.nodup_cons] at heq
      by_cases hxm : x = m
      · subst hxm
        have hfilter : ((x :: xs).filter fun m' => decide (m' ≠ x)) = xs := by
          rw [List.filter_cons_of_neg (by simp only [ne_eq, not_true_eq_false, decide_false,
            Bool.false_eq_true, not_false_eq_true])]
          exact List.filter_eq_self.mpr fun m' hm' => decide_eq_true (fun h => heq.1 (h ▸ hm'))
        rw [hfilter, evalMonomialList_cons, Bool.xor_comm (x.all σ), Bool.xor_assoc,
          Bool.xor_self, Bool.xor_false]
      · have hmxs : m ∈ xs := (List.mem_cons.mp hm).resolve_left (Ne.symm hxm)
        simp only [List.filter_cons, decide_eq_true hxm, ↓reduceIte, evalMonomialList_cons]
        rw [ih heq.2 hmxs, Bool.xor_assoc]
  · exact (evalMonomialList_append eq [m] σ).trans (by rw [evalMonomialList_singleton])

private theorem foldl_toggleMonomial_props (eq acc : List (List ℕ)) (hacc : acc.Nodup) :
    (eq.foldl toggleMonomial acc).Nodup ∧
      (∀ m, m ∈ eq.foldl toggleMonomial acc → m ∈ acc ∨ m ∈ eq) ∧
      (eq.foldl toggleMonomial acc).length ≤ acc.length + eq.length ∧
      ∀ σ, evalMonomialList (eq.foldl toggleMonomial acc) σ =
        xor (evalMonomialList acc σ) (evalMonomialList eq σ) := by
  induction eq generalizing acc with
  | nil =>
    exact ⟨hacc, fun _ hm => Or.inl hm,
      by simp only [List.foldl_nil, List.length_nil, Nat.add_zero, le_rfl],
      fun _ => by simp only [List.foldl_nil, evalMonomialList_nil, Bool.xor_false]⟩
  | cons x xs ih =>
    obtain ⟨hnd, hsub, hlen, heval⟩ := ih (toggleMonomial acc x) (nodup_toggleMonomial hacc x)
    refine ⟨hnd, fun m hm => ?_, ?_, fun σ => ?_⟩
    · rcases hsub m hm with hmx | hmxs
      · rcases mem_of_mem_toggleMonomial hmx with hma | rfl
        · exact Or.inl hma
        · exact Or.inr List.mem_cons_self
      · exact Or.inr (List.mem_cons_of_mem x hmxs)
    · have ht := length_toggleMonomial_le acc x
      simp only [List.foldl_cons, List.length_cons]; omega
    · simp only [List.foldl_cons]
      rw [heval σ, evalMonomialList_toggleMonomial hacc x σ, evalMonomialList_cons, Bool.xor_assoc]

theorem nodup_reduceEquation (eq : List (List ℕ)) : (reduceEquation eq).Nodup :=
  (foldl_toggleMonomial_props eq [] List.nodup_nil).1

theorem mem_of_mem_reduceEquation {eq : List (List ℕ)} {m : List ℕ}
    (hm : m ∈ reduceEquation eq) : m ∈ eq :=
  ((foldl_toggleMonomial_props eq [] List.nodup_nil).2.1 m hm).resolve_left List.not_mem_nil

theorem length_reduceEquation_le (eq : List (List ℕ)) :
    (reduceEquation eq).length ≤ eq.length := by
  unfold reduceEquation
  simpa only [List.length_nil, Nat.zero_add] using
    (foldl_toggleMonomial_props eq [] List.nodup_nil).2.2.1

theorem evalMonomialList_reduceEquation (eq : List (List ℕ)) (σ : ℕ → Bool) :
    evalMonomialList (reduceEquation eq) σ = evalMonomialList eq σ := by
  unfold reduceEquation
  simpa only [evalMonomialList_nil, Bool.false_xor] using
    (foldl_toggleMonomial_props eq [] List.nodup_nil).2.2.2 σ

theorem nodup_xorEquation (eq1 eq2 : List (List ℕ)) : (xorEquation eq1 eq2).Nodup :=
  nodup_reduceEquation (eq1 ++ eq2)

theorem mem_of_mem_xorEquation {eq1 eq2 : List (List ℕ)} {m : List ℕ}
    (hm : m ∈ xorEquation eq1 eq2) : m ∈ eq1 ∨ m ∈ eq2 :=
  List.mem_append.mp (mem_of_mem_reduceEquation hm)

/-- `xorEquation` preserves canonical sorted monomials and `Nodup`. -/
theorem isCanonicalEquation_xorEquation {eq1 eq2 : List (List ℕ)}
    (h1 : IsCanonicalEquation eq1) (h2 : IsCanonicalEquation eq2) :
    IsCanonicalEquation (xorEquation eq1 eq2) :=
  ⟨nodup_xorEquation eq1 eq2, fun m hm => (mem_of_mem_xorEquation hm).elim (h1.2 m) (h2.2 m)⟩

/-- `xorEquation` evaluates to the Boolean XOR of the two equations' evaluations. -/
theorem evalMonomialList_xorEquation (eq1 eq2 : List (List ℕ)) (σ : ℕ → Bool) :
    evalMonomialList (xorEquation eq1 eq2) σ =
      xor (evalMonomialList eq1 σ) (evalMonomialList eq2 σ) := by
  rw [xorEquation, evalMonomialList_reduceEquation, evalMonomialList_append]

/-- `xorEquation` outputs at most `eq1.length + eq2.length` monomials. -/
theorem length_xorEquation_le (eq1 eq2 : List (List ℕ)) :
    (xorEquation eq1 eq2).length ≤ eq1.length + eq2.length := by
  unfold xorEquation
  simpa only [List.length_append] using length_reduceEquation_le (eq1 ++ eq2)

/-! ### 2. Executable Clause Falsification & Parity-Row Compiler (§6 eq. (6.1) & §6.3) -/

/-- Insert `v` into a strictly increasing monomial `m`, omitting duplicates. -/
def insertSorted (m : List ℕ) (v : ℕ) : List ℕ :=
  m.filter (fun u => decide (u < v)) ++ [v] ++ m.filter (fun u => decide (v < u))

/-- Canonical strictly increasing deduplication of variable indices. -/
def sortDedup (vs : List ℕ) : List ℕ := vs.foldl insertSorted []

theorem mem_insertSorted {m : List ℕ} {v u : ℕ} :
    u ∈ insertSorted m v ↔ u ∈ m ∨ u = v := by
  simp only [insertSorted, List.append_assoc, List.mem_append, List.mem_filter,
    List.mem_cons, List.not_mem_nil, or_false, decide_eq_true_eq]
  rcases lt_trichotomy u v with hlt | rfl | hgt
  · exact ⟨fun h => h.elim (fun h1 => Or.inl h1.1) (fun h2 => h2.imp_right And.left |>.symm),
      fun h => h.elim (fun hu => Or.inl ⟨hu, hlt⟩) fun h => absurd (h ▸ hlt) (lt_irrefl _)⟩
  · simp only [lt_irrefl, and_false, or_true, true_or]
  · exact ⟨fun h => h.elim (fun h1 => Or.inl h1.1) (fun h2 => h2.elim Or.inr (Or.inl ∘ And.left)),
      fun h => h.elim (fun hu => Or.inr (Or.inr ⟨hu, hgt⟩))
        fun h => absurd (h ▸ hgt) (lt_irrefl _)⟩

@[simp] theorem toFinset_insertSorted (m : List ℕ) (v : ℕ) :
    (insertSorted m v).toFinset = insert v m.toFinset := by
  ext u; simp only [List.mem_toFinset, Finset.mem_insert, mem_insertSorted, or_comm]

theorem isCanonicalMonomial_insertSorted {m : List ℕ} (hm : IsCanonicalMonomial m) (v : ℕ) :
    IsCanonicalMonomial (insertSorted m v) := by
  unfold IsCanonicalMonomial insertSorted
  rw [List.pairwise_append]
  refine ⟨List.pairwise_append.mpr ⟨hm.filter _, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩,
    hm.filter _, fun a ha b hb => ?_⟩
  · exact List.mem_singleton.mp hb ▸ of_decide_eq_true (List.mem_filter.mp ha).2
  · have hb' : v < b := of_decide_eq_true (List.mem_filter.mp hb).2
    exact (List.mem_append.mp ha).elim
      (fun ha1 => lt_trans (of_decide_eq_true (List.mem_filter.mp ha1).2) hb')
      fun ha2 => List.mem_singleton.mp ha2 ▸ hb'

private theorem length_insertSorted_le {m : List ℕ} (hm : IsCanonicalMonomial m) (v : ℕ) :
    (insertSorted m v).length ≤ m.length + 1 := by
  rw [← List.toFinset_card_of_nodup (isCanonicalMonomial_insertSorted hm v).nodup,
    toFinset_insertSorted, ← List.toFinset_card_of_nodup hm.nodup]
  exact Finset.card_insert_le v m.toFinset

theorem all_insertSorted (m : List ℕ) (v : ℕ) (σ : ℕ → Bool) :
    (insertSorted m v).all σ = (m.all σ && σ v) := by
  rw [Bool.eq_iff_iff, List.all_eq_true, Bool.and_eq_true, List.all_eq_true]
  exact ⟨fun h => ⟨fun u hu => h u (mem_insertSorted.mpr (Or.inl hu)),
      h v (mem_insertSorted.mpr (Or.inr rfl))⟩,
    fun ⟨hm, hv⟩ u hu => (mem_insertSorted.mp hu).elim (hm u) fun h => h ▸ hv⟩

private theorem foldl_insertSorted_props (vs acc : List ℕ) (hacc : IsCanonicalMonomial acc) :
    IsCanonicalMonomial (vs.foldl insertSorted acc) ∧
      ∀ u, u ∈ vs.foldl insertSorted acc ↔ u ∈ acc ∨ u ∈ vs := by
  induction vs generalizing acc with
  | nil => exact ⟨hacc, fun _ => by simp only [List.foldl_nil, List.not_mem_nil, or_false]⟩
  | cons v vs ih =>
    obtain ⟨hcan, hmem⟩ := ih (insertSorted acc v) (isCanonicalMonomial_insertSorted hacc v)
    refine ⟨hcan, fun u => ?_⟩
    simp only [List.foldl_cons, hmem, mem_insertSorted, List.mem_cons]; tauto

theorem isCanonicalMonomial_sortDedup (vs : List ℕ) : IsCanonicalMonomial (sortDedup vs) :=
  (foldl_insertSorted_props vs [] List.Pairwise.nil).1

theorem nodup_sortDedup (vs : List ℕ) : (sortDedup vs).Nodup :=
  (isCanonicalMonomial_sortDedup vs).nodup

@[simp] theorem mem_sortDedup {vs : List ℕ} {u : ℕ} : u ∈ sortDedup vs ↔ u ∈ vs := by
  unfold sortDedup
  simpa only [List.not_mem_nil, false_or] using
    (foldl_insertSorted_props vs [] List.Pairwise.nil).2 u

@[simp] theorem toFinset_sortDedup (vs : List ℕ) : (sortDedup vs).toFinset = vs.toFinset := by
  ext u; simp only [List.mem_toFinset, mem_sortDedup]

private theorem length_sortDedup_le (vs : List ℕ) : (sortDedup vs).length ≤ vs.length := by
  rw [← List.toFinset_card_of_nodup (nodup_sortDedup vs), toFinset_sortDedup]
  exact List.toFinset_card_le vs

/-- Check whether clause `c` contains both `(v, true)` and `(v, false)` for some `v`. -/
def isTautologicalClause (c : Clause ℕ) : Bool :=
  c.any fun l => c.any fun l' => decide (l.1 = l'.1 ∧ l.2 ≠ l'.2)

/-- Sorted distinct positive-literal variables of `c`. -/
def posVars (c : Clause ℕ) : List ℕ := sortDedup ((c.filter Prod.snd).map Prod.fst)

/-- Sorted distinct negative-literal variables of `c`. -/
def negVars (c : Clause ℕ) : List ℕ := sortDedup ((c.filter fun l => !l.2).map Prod.fst)

/-- Expand `∏_{v ∈ vs} (1 ⊕ x_v)` starting from a canonical base monomial `base`. -/
def expandPosVars (base : List ℕ) (vs : List ℕ) : List (List ℕ) :=
  vs.foldl (fun acc v => acc ++ acc.map fun m => insertSorted m v) [base]

/-- Compile the falsification indicator `v_c(x) = !c.eval x` of a clause `c : Clause ℕ` into a
canonical sparse `𝔽₂` polynomial (§6, p. 39). Tautological clauses compile to `[]` (`0`). -/
def compileClause (c : Clause ℕ) : List (List ℕ) :=
  if isTautologicalClause c then [] else expandPosVars (negVars c) (posVars c)

private theorem mem_posVars_iff {c : Clause ℕ} {v : ℕ} : v ∈ posVars c ↔ (v, true) ∈ c := by
  simp only [posVars, mem_sortDedup, List.mem_map, List.mem_filter, Prod.exists]
  exact ⟨fun ⟨_, b, ⟨hl, hb⟩, hv⟩ => hv ▸ hb ▸ hl, fun hl => ⟨v, true, ⟨hl, rfl⟩, rfl⟩⟩

private theorem mem_negVars_iff {c : Clause ℕ} {v : ℕ} : v ∈ negVars c ↔ (v, false) ∈ c := by
  simp only [negVars, mem_sortDedup, List.mem_map, List.mem_filter, Bool.not_eq_true', Prod.exists]
  exact ⟨fun ⟨_, b, ⟨hl, hb⟩, hv⟩ => hv ▸ hb ▸ hl, fun hl => ⟨v, false, ⟨hl, rfl⟩, rfl⟩⟩

private theorem length_posVars_le (c : Clause ℕ) : (posVars c).length ≤ c.length :=
  (length_sortDedup_le _).trans ((List.length_map _).trans_le (List.length_filter_le _ c))

private theorem length_negVars_le (c : Clause ℕ) : (negVars c).length ≤ c.length :=
  (length_sortDedup_le _).trans ((List.length_map _).trans_le (List.length_filter_le _ c))

private theorem isTautologicalClause_eq_true_iff {c : Clause ℕ} :
    isTautologicalClause c = true ↔ ∃ v, (v, true) ∈ c ∧ (v, false) ∈ c := by
  simp only [isTautologicalClause, List.any_eq_true, decide_eq_true_eq, Prod.exists]
  refine ⟨?_, fun ⟨v, ht, hf⟩ => ⟨v, true, ht, v, false, hf, rfl, by decide⟩⟩
  rintro ⟨v, b, hl, _, b', hl', rfl, hne⟩
  cases b <;> cases b'
  · exact False.elim (hne rfl)
  · exact ⟨v, hl', hl⟩
  · exact ⟨v, hl, hl'⟩
  · exact False.elim (hne rfl)

private theorem evalMonomialList_append_insertSorted (acc : List (List ℕ)) (v : ℕ)
    (σ : ℕ → Bool) :
    evalMonomialList (acc ++ acc.map fun m => insertSorted m v) σ =
      (!σ v && evalMonomialList acc σ) := by
  rw [evalMonomialList_append]
  have hmap : evalMonomialList (acc.map fun m => insertSorted m v) σ =
      (σ v && evalMonomialList acc σ) := by
    induction acc with
    | nil => simp only [List.map_nil, evalMonomialList_nil, Bool.and_false]
    | cons m ms ih =>
      rw [List.map_cons, evalMonomialList_cons, all_insertSorted, ih, evalMonomialList_cons]
      cases σ v <;> cases m.all σ <;> cases evalMonomialList ms σ <;> rfl
  rw [hmap]; cases σ v <;> cases evalMonomialList acc σ <;> rfl

private theorem expandPosVars_props {vs : List ℕ} (hvs : vs.Nodup)
    {acc : List (List ℕ)} (hcan : IsCanonicalEquation acc)
    (hdisj : ∀ v ∈ vs, ∀ m ∈ acc, v ∉ m) :
    IsCanonicalEquation (vs.foldl (fun a v => a ++ a.map fun m => insertSorted m v) acc) ∧
      (vs.foldl (fun a v => a ++ a.map fun m => insertSorted m v) acc).length =
        acc.length * 2 ^ vs.length ∧
      (∀ m' ∈ vs.foldl (fun a v => a ++ a.map fun m => insertSorted m v) acc,
        ∃ m ∈ acc, m'.toFinset ⊆ m.toFinset ∪ vs.toFinset) ∧
      ∀ σ, evalMonomialList
        (vs.foldl (fun a v => a ++ a.map fun m => insertSorted m v) acc) σ =
        (!vs.any σ && evalMonomialList acc σ) := by
  induction vs generalizing acc with
  | nil =>
    exact ⟨hcan, by simp only [List.foldl_nil, List.length_nil, pow_zero, Nat.mul_one],
      fun m' hm' => ⟨m', hm', by simp only [List.toFinset_nil, Finset.union_empty,
        Finset.Subset.refl]⟩,
      fun _ => by simp only [List.foldl_nil, List.any_nil, Bool.not_false, Bool.true_and]⟩
  | cons v vs ih =>
    rw [List.nodup_cons] at hvs
    set acc' := acc ++ acc.map fun m => insertSorted m v
    have hcan' : IsCanonicalEquation acc' := by
      refine ⟨List.nodup_append.mpr ⟨hcan.1, ?_, fun m₁ hm₁ m₂ hm₂ heq => ?_⟩, fun m' hm' => ?_⟩
      · refine hcan.1.map_on fun m₁ hm₁ m₂ hm₂ heq => ?_
        have ht := congrArg (fun l : List ℕ => l.toFinset.erase v) heq
        simp only [toFinset_insertSorted,
          Finset.erase_insert (List.mem_toFinset.not.mpr (hdisj v List.mem_cons_self m₁ hm₁)),
          Finset.erase_insert (List.mem_toFinset.not.mpr (hdisj v List.mem_cons_self m₂ hm₂))] at ht
        exact (hcan.2 m₁ hm₁).eq_of_toFinset_eq (hcan.2 m₂ hm₂) ht
      · obtain ⟨m₀, -, rfl⟩ := List.mem_map.mp hm₂
        exact hdisj v List.mem_cons_self m₁ hm₁ (heq ▸ mem_insertSorted.mpr (Or.inr rfl))
      · rcases List.mem_append.mp hm' with hm₁ | hm₂
        · exact hcan.2 m' hm₁
        · obtain ⟨m₀, hm₀, rfl⟩ := List.mem_map.mp hm₂
          exact isCanonicalMonomial_insertSorted (hcan.2 m₀ hm₀) v
    have hdisj' : ∀ w ∈ vs, ∀ m' ∈ acc', w ∉ m' := by
      intro w hw m' hm' hwm'
      rcases List.mem_append.mp hm' with hm₁ | hm₂
      · exact hdisj w (List.mem_cons_of_mem v hw) m' hm₁ hwm'
      · obtain ⟨m₀, hm₀, rfl⟩ := List.mem_map.mp hm₂
        exact (mem_insertSorted.mp hwm').elim
          (hdisj w (List.mem_cons_of_mem v hw) m₀ hm₀) fun h => hvs.1 (h ▸ hw)
    obtain ⟨hcan_res, hlen_res, hsub_res, heval_res⟩ := ih hvs.2 hcan' hdisj'
    refine ⟨hcan_res, ?_, fun m' hm' => ?_, fun σ => ?_⟩
    · simp only [List.foldl_cons, hlen_res, acc', List.length_append, List.length_map,
        List.length_cons, pow_succ]; ring
    · obtain ⟨m₁, hm₁, hsub₁⟩ := hsub_res m' hm'
      rcases List.mem_append.mp hm₁ with hm_acc | hm_map
      · refine ⟨m₁, hm_acc, hsub₁.trans fun u hu => ?_⟩
        simp only [Finset.mem_union, List.mem_toFinset, List.mem_cons] at hu ⊢; tauto
      · obtain ⟨m₀, hm₀, rfl⟩ := List.mem_map.mp hm_map
        refine ⟨m₀, hm₀, hsub₁.trans fun u hu => ?_⟩
        simp only [toFinset_insertSorted, Finset.mem_union, Finset.mem_insert,
          List.mem_toFinset, List.mem_cons] at hu ⊢; tauto
    · simp only [List.foldl_cons, heval_res σ, acc', evalMonomialList_append_insertSorted,
        List.any_cons, Bool.not_or]
      cases σ v <;> cases vs.any σ <;> cases evalMonomialList acc σ <;> rfl

private theorem compileClause_nontaut_props {c : Clause ℕ} (ht : ¬isTautologicalClause c = true) :
    IsCanonicalEquation (expandPosVars (negVars c) (posVars c)) ∧
      (expandPosVars (negVars c) (posVars c)).length = 2 ^ (posVars c).length ∧
      (∀ m' ∈ expandPosVars (negVars c) (posVars c),
        m'.toFinset ⊆ (negVars c).toFinset ∪ (posVars c).toFinset) ∧
      ∀ σ, evalMonomialList (expandPosVars (negVars c) (posVars c)) σ =
        (!(posVars c).any σ && (negVars c).all σ) := by
  have hbase : IsCanonicalEquation [negVars c] :=
    ⟨List.nodup_singleton _, fun _ hm => List.mem_singleton.mp hm ▸ isCanonicalMonomial_sortDedup _⟩
  have hdisj : ∀ v ∈ posVars c, ∀ m ∈ ([negVars c] : List (List ℕ)), v ∉ m := fun v hv m hm hvm =>
    ht (isTautologicalClause_eq_true_iff.mpr
      ⟨v, mem_posVars_iff.mp hv, mem_negVars_iff.mp (List.mem_singleton.mp hm ▸ hvm)⟩)
  obtain ⟨hcan, hlen, hsub, hev⟩ := expandPosVars_props (vs := posVars c) (nodup_sortDedup _)
    hbase hdisj
  dsimp only [expandPosVars]
  refine ⟨hcan, by simpa only [List.length_singleton, Nat.one_mul] using hlen, fun m' hm' => ?_,
    fun σ => by simpa only [evalMonomialList_singleton] using hev σ⟩
  obtain ⟨m₀, hm₀, hsub₀⟩ := hsub m' hm'
  exact List.mem_singleton.mp hm₀ ▸ hsub₀

/-- `compileClause c` always produces a canonical sparse `𝔽₂` equation. -/
theorem isCanonicalEquation_compileClause (c : Clause ℕ) :
    IsCanonicalEquation (compileClause c) := by
  unfold compileClause; split_ifs with ht
  · exact isCanonicalEquation_nil
  · exact (compileClause_nontaut_props ht).1

/-- Every variable occurring in `compileClause c` is a variable of `c`. -/
theorem mem_clause_of_mem_compileClause {c : Clause ℕ} {m : List ℕ} {v : ℕ}
    (hm : m ∈ compileClause c) (hv : v ∈ m) : ∃ b, (v, b) ∈ c := by
  unfold compileClause at hm; split_ifs at hm with ht
  · exact False.elim (List.not_mem_nil hm)
  · have hv' := (compileClause_nontaut_props ht).2.2.1 m hm (List.mem_toFinset.mpr hv)
    simp only [Finset.mem_union, List.mem_toFinset] at hv'
    exact hv'.elim (fun hn => ⟨false, mem_negVars_iff.mp hn⟩)
      fun hp => ⟨true, mem_posVars_iff.mp hp⟩

/-- Every monomial in `compileClause c` has length at most `c.length`. -/
theorem length_mem_compileClause_le {c : Clause ℕ} {m : List ℕ} (hm : m ∈ compileClause c) :
    m.length ≤ c.length := by
  rw [← List.toFinset_card_of_nodup ((isCanonicalEquation_compileClause c).2 m hm).nodup]
  have hsub : m.toFinset ⊆ (c.map Prod.fst).toFinset := fun v hv => by
    obtain ⟨b, hb⟩ := mem_clause_of_mem_compileClause hm (List.mem_toFinset.mp hv)
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(v, b), hb, rfl⟩)
  exact (Finset.card_le_card hsub).trans
    ((List.toFinset_card_le _).trans (by simp only [List.length_map, le_rfl]))

/-- `compileClause c` expands into at most `2 ^ c.length` monomials. -/
theorem length_compileClause_le (c : Clause ℕ) : (compileClause c).length ≤ 2 ^ c.length := by
  unfold compileClause; split_ifs with ht
  · exact Nat.zero_le _
  · rw [(compileClause_nontaut_props ht).2.1]
    exact Nat.pow_le_pow_right (by omega) (length_posVars_le c)

/-- **Exact clause falsification semantics (§6, p. 39)**: `compileClause c` evaluates to
`!c.eval σ` for every assignment `σ`. -/
theorem evalMonomialList_compileClause (c : Clause ℕ) (σ : ℕ → Bool) :
    evalMonomialList (compileClause c) σ = !c.eval σ := by
  unfold compileClause; split_ifs with ht
  · obtain ⟨v, hvt, hvf⟩ := isTautologicalClause_eq_true_iff.mp ht
    have hev : c.eval σ = true := by
      rw [Clause.eval_eq_true_iff]
      cases hσ : σ v
      · exact ⟨(v, false), hvf, hσ⟩
      · exact ⟨(v, true), hvt, hσ⟩
    simp only [evalMonomialList_nil, hev, Bool.not_true]
  · rw [(compileClause_nontaut_props ht).2.2.2 σ, Bool.eq_iff_iff, Bool.and_eq_true,
      Bool.not_eq_true', List.any_eq_false, List.all_eq_true, Bool.not_eq_true',
      ← Bool.not_eq_true, Clause.eval_eq_true_iff]
    refine ⟨fun ⟨hpos, hneg⟩ ⟨⟨v, b⟩, hl, hσ⟩ => ?_, fun hunsat =>
      ⟨fun v hv hσ => hunsat ⟨(v, true), mem_posVars_iff.mp hv, hσ⟩, fun v hv => ?_⟩⟩
    · cases b
      · have hneg' := hneg v (mem_negVars_iff.mpr hl)
        dsimp only at hσ; rw [hσ] at hneg'
        exact Bool.false_ne_true hneg'
      · exact hpos v (mem_posVars_iff.mpr hl) hσ
    · cases hσ : σ v
      · exact False.elim (hunsat ⟨(v, false), mem_negVars_iff.mp hv, hσ⟩)
      · rfl

/-- Compile a parity-check row `row : List Bool` on `φ : CNF ℕ` into a sparse `𝔽₂` polynomial
equation by XORing `compileClause φ[e]` over `e < φ.length` with `row.getD e false = true`. -/
def compileParityRow (φ : CNF ℕ) (row : List Bool) : List (List ℕ) :=
  (List.range φ.length).foldl
    (fun acc e => if row.getD e false then xorEquation acc (compileClause (φ.getD e [])) else acc)
    []

/-- Compile a list of parity-check rows on `φ : CNF ℕ` into a sparse `𝔽₂` polynomial system. -/
def compileParitySystem (φ : CNF ℕ) (rows : List (List Bool)) : List (List (List ℕ)) :=
  rows.map (compileParityRow φ)

private theorem countP_range_getD_eq_count_take (row : List Bool) (n : ℕ) :
    ((List.range n).countP fun e => row.getD e false) = (row.take n).count true := by
  induction n with
  | zero => simp only [List.range_zero, List.countP_nil, List.take_zero, List.count_nil]
  | succ n ih =>
    rw [List.range_succ, List.countP_append, List.countP_cons, List.countP_nil, Nat.add_zero, ih]
    by_cases hn : n < row.length
    · rw [List.take_succ_eq_append_getElem hn, List.count_append, List.count_cons, List.count_nil,
        List.getD_eq_getElem _ _ hn]
      cases row[n] <;> simp only [↓reduceIte, Bool.false_eq_true,
        show (false == true) = false from rfl, show (true == true) = true from rfl,
        Nat.zero_add, Nat.add_zero]
    · have hge : row.length ≤ n := Nat.le_of_not_lt hn
      rw [List.take_of_length_le hge, List.take_of_length_le (Nat.le_succ_of_le hge),
        List.getD_eq_default _ _ hge]
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]

private theorem compileParityRow_prefix_props (φ : CNF ℕ) (row : List Bool) (k : ℕ)
    (hφ : ∀ c ∈ φ, c.length ≤ k) :
    ∀ n ≤ φ.length,
      let eq := (List.range n).foldl
        (fun acc e =>
          if row.getD e false then xorEquation acc (compileClause (φ.getD e [])) else acc) []
      IsCanonicalEquation eq ∧
        (∀ m ∈ eq, m.length ≤ k ∧ ∀ v ∈ m, v ∈ φ.vars) ∧
        eq.length ≤ ((List.range n).countP fun e => row.getD e false) * 2 ^ k := by
  intro n hn
  induction n with
  | zero =>
    refine ⟨isCanonicalEquation_nil, fun _ hm => False.elim (List.not_mem_nil hm), ?_⟩
    simp only [List.range_zero, List.foldl_nil, List.length_nil, List.countP_nil, Nat.zero_mul,
      le_rfl]
  | succ n ih =>
    have hnlt : n < φ.length := hn
    obtain ⟨hcan, hdeg, hlen⟩ := ih (Nat.le_of_lt hnlt)
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.countP_append, List.countP_cons, List.countP_nil]
    split_ifs with hr
    · have hc_mem : φ[n] ∈ φ := List.getElem_mem hnlt
      rw [List.getD_eq_getElem _ _ hnlt]
      refine ⟨isCanonicalEquation_xorEquation hcan (isCanonicalEquation_compileClause φ[n]),
        fun m hm => ?_, ?_⟩
      · rcases mem_of_mem_xorEquation hm with hm1 | hm2
        · exact hdeg m hm1
        · refine ⟨(length_mem_compileClause_le hm2).trans (hφ φ[n] hc_mem), fun v hv => ?_⟩
          obtain ⟨b, hb⟩ := mem_clause_of_mem_compileClause hm2 hv
          exact CNF.mem_vars.mpr ⟨φ[n], hc_mem, b, hb⟩
      · have hcl : (compileClause φ[n]).length ≤ 2 ^ k :=
          (length_compileClause_le φ[n]).trans (Nat.pow_le_pow_right (by omega) (hφ φ[n] hc_mem))
        calc (xorEquation _ (compileClause φ[n])).length
            ≤ _ + (compileClause φ[n]).length := length_xorEquation_le _ _
          _ ≤ ((List.range n).countP fun e => row.getD e false) * 2 ^ k + 2 ^ k :=
              Nat.add_le_add hlen hcl
          _ = (((List.range n).countP fun e => row.getD e false) + (0 + 1)) * 2 ^ k := by ring
    · simpa only [Nat.add_zero] using ⟨hcan, hdeg, hlen⟩

theorem isCanonicalEquation_compileParityRow (φ : CNF ℕ) (row : List Bool) :
    IsCanonicalEquation (compileParityRow φ row) :=
  (compileParityRow_prefix_props φ row _
    (fun c hc => List.le_sum_of_mem (List.mem_map.mpr ⟨c, hc, rfl⟩)) φ.length le_rfl).1

/-- When every clause of `φ` has width at most `k`, every monomial in `compileParityRow φ row` has
degree at most `k`. -/
theorem length_mem_compileParityRow_le {k : ℕ} {φ : CNF ℕ} (hφ : ∀ c ∈ φ, c.length ≤ k)
    (row : List Bool) {m : List ℕ} (hm : m ∈ compileParityRow φ row) : m.length ≤ k :=
  ((compileParityRow_prefix_props φ row k hφ φ.length le_rfl).2.1 m hm).1

theorem mem_vars_of_mem_compileParityRow {φ : CNF ℕ} {row : List Bool} {m : List ℕ} {v : ℕ}
    (hm : m ∈ compileParityRow φ row) (hv : v ∈ m) : v ∈ φ.vars :=
  ((compileParityRow_prefix_props φ row _
    (fun c hc => List.le_sum_of_mem (List.mem_map.mpr ⟨c, hc, rfl⟩)) φ.length le_rfl).2.1 m hm).2
    v hv

/-- **Row sparsity bound (§6.2, p. 42)**: when every clause of `φ` has width at most `k`,
`compileParityRow φ row` contains at most `row.count true * 2 ^ k` monomials. -/
theorem length_compileParityRow_le {k : ℕ} {φ : CNF ℕ} (hφ : ∀ c ∈ φ, c.length ≤ k)
    (row : List Bool) :
    (compileParityRow φ row).length ≤ row.count true * 2 ^ k := by
  have h := (compileParityRow_prefix_props φ row k hφ φ.length le_rfl).2.2
  rw [countP_range_getD_eq_count_take] at h
  exact h.trans (Nat.mul_le_mul_right _ ((List.take_sublist φ.length row).count_le true))

/-- **Exact parity-row semantics (§6 eq. (6.1))**: `compileParityRow φ row` evaluates to the `𝔽₂`
dot product of `row` with `φ.violations σ`. -/
theorem evalMonomialList_compileParityRow_eq_dotProduct (φ : CNF ℕ) (row : List Bool)
    (σ : ℕ → Bool) :
    evalMonomialList (compileParityRow φ row) σ =
      (fun e : Fin φ.length => row.getD e.1 false) ⬝ᵥ φ.violations σ := by
  have hprefix : ∀ n (hn : n ≤ φ.length),
      evalMonomialList ((List.range n).foldl
        (fun acc e =>
          if row.getD e false then xorEquation acc (compileClause (φ.getD e [])) else acc) []) σ =
        ∑ i : Fin n, row.getD i.1 false * !(φ[i.1]'(Nat.lt_of_lt_of_le i.2 hn)).eval σ := by
    intro n hn
    induction n with
    | zero =>
      simp only [List.range_zero, List.foldl_nil, evalMonomialList_nil, Finset.univ_eq_empty,
        Finset.sum_empty]; rfl
    | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      have hgetD : φ.getD n [] = φ[n]'hn := List.getD_eq_getElem _ _ hn
      split_ifs with hr
      · rw [evalMonomialList_xorEquation, ih (Nat.le_of_lt hn), hgetD,
          evalMonomialList_compileClause, hr, Bool.add_eq_xor]
        cases (φ[n]'hn).eval σ <;> rfl
      · simp only [Bool.not_eq_true] at hr
        have h0 : (false * !(φ[n]'hn).eval σ) = false := by cases (φ[n]'hn).eval σ <;> rfl
        rw [ih (Nat.le_of_lt hn), hr, h0, Bool.add_eq_xor, Bool.xor_false]
  rw [compileParityRow, hprefix φ.length le_rfl]; rfl

/-- **System acceptance equivalence**: `σ` is a common zero of `compileParitySystem φ rows` over
`𝔽₂` if and only if `σ` passes all parity tests represented by `rows` on `φ.violations`. -/
theorem evalSystem_compileParitySystem_iff_passesTests (φ : CNF ℕ) (rows : List (List Bool))
    (σ : ℕ → Bool) :
    evalSystem (compileParitySystem φ rows) σ = true ↔
      PassesTests φ.violations (rows.map fun row (e : Fin φ.length) => row.getD e.1 false) σ := by
  simp only [evalSystem_eq_true_iff, compileParitySystem, PassesTests, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    evalMonomialList_compileParityRow_eq_dotProduct]

/-- Width-`k` guarded clause compiler (agrees with `compileClause` on clauses of width `≤ k`). -/
def compileClauseBounded (k : ℕ) (c : Clause ℕ) : List (List ℕ) := compileClause (c.take k)

/-- Width-`k` guarded parity-row compiler. -/
def compileParityRowBounded (k : ℕ) (φ : CNF ℕ) (row : List Bool) : List (List ℕ) :=
  compileParityRow (φ.map (List.take k)) row

/-- Width-`k` guarded parity-system compiler. -/
def compileParitySystemBounded (k : ℕ) (φ : CNF ℕ) (rows : List (List Bool)) :
    List (List (List ℕ)) :=
  compileParitySystem (φ.map (List.take k)) rows

theorem compileParitySystemBounded_eq_compileParitySystem {k : ℕ} {φ : CNF ℕ}
    (hφ : ∀ c ∈ φ, c.length ≤ k) (rows : List (List Bool)) :
    compileParitySystemBounded k φ rows = compileParitySystem φ rows := by
  rw [compileParitySystemBounded,
    (List.map_congr_left fun c hc => List.take_of_length_le (hφ c hc)).trans (List.map_id φ)]

/-! ### 3. Executable Heavy-Variable Finder & Variable Restriction (§5.5, pp. 38–39) -/

/-- Canonical duplicate-free variable scope of an equation `eq`. -/
def equationVars (eq : List (List ℕ)) : List ℕ := sortDedup eq.flatten

/-- Incidence degree of variable `v` in `sys`: number of equation scopes containing `v`. -/
def varDegree (v : ℕ) (sys : List (List (List ℕ))) : ℕ :=
  sys.countP fun eq => decide (v ∈ equationVars eq)

/-- First variable `v < n` with `varDegree v sys > b₀`, or `none` if none exists (§5.5, p. 38). -/
def findHeavyVar (n b₀ : ℕ) (sys : List (List (List ℕ))) : Option ℕ :=
  (List.range n).find? fun v => decide (b₀ < varDegree v sys)

/-- Substitute `x_v = val` into `eq` over `𝔽₂`, dropping monomials containing `v` when
`val = false` and erasing `v` then cancelling mod-2 duplicates when `val = true` (§5.5, p. 38). -/
def restrictEquation (v : ℕ) (val : Bool) (eq : List (List ℕ)) : List (List ℕ) :=
  if val then reduceEquation (eq.map fun m => m.filter fun u => decide (u ≠ v))
  else eq.filter fun m => !decide (v ∈ m)

/-- Substitute `x_v = val` across every equation of a sparse `𝔽₂` system. -/
def restrictSystem (v : ℕ) (val : Bool) (sys : List (List (List ℕ))) : List (List (List ℕ)) :=
  sys.map (restrictEquation v val)

@[simp] theorem mem_equationVars {eq : List (List ℕ)} {v : ℕ} :
    v ∈ equationVars eq ↔ ∃ m ∈ eq, v ∈ m := by
  simp only [equationVars, mem_sortDedup, List.mem_flatten]

/-- `findHeavyVar n b₀ sys = some v` iff `v < n` is minimal with `varDegree v sys > b₀`. -/
theorem findHeavyVar_eq_some_iff {n b₀ : ℕ} {sys : List (List (List ℕ))} {v : ℕ} :
    findHeavyVar n b₀ sys = some v ↔
      v < n ∧ b₀ < varDegree v sys ∧ ∀ u < v, varDegree u sys ≤ b₀ := by
  rw [findHeavyVar, List.find?_eq_some_iff_append]
  simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not, not_lt]
  constructor
  · rintro ⟨hgt, xs, ys, hr, hmin⟩
    have hv_mem : v ∈ List.range n := hr ▸ List.mem_append_right _ List.mem_cons_self
    refine ⟨List.mem_range.mp hv_mem, hgt, fun u hu => hmin u ?_⟩
    have hu_mem : u ∈ List.range n := List.mem_range.mpr (lt_trans hu (List.mem_range.mp hv_mem))
    rw [hr, List.mem_append, List.mem_cons] at hu_mem
    rcases hu_mem with hux | rfl | huy
    · exact hux
    · exact absurd hu (lt_irrefl _)
    · have hp : (List.range n).Pairwise (· < ·) := List.pairwise_lt_range
      rw [hr, List.pairwise_append] at hp
      exact absurd (lt_trans hu ((List.pairwise_cons.mp hp.2.1).1 u huy)) (lt_irrefl _)
  · rintro ⟨hv, hgt, hmin⟩
    have hv' : v < (List.range n).length := by simpa only [List.length_range] using hv
    have hsplit : List.range n = List.range v ++ v :: (List.range n).drop (v + 1) := by
      have h1 : (List.range n).take v = List.range v := by
        rw [List.take_range, Nat.min_eq_left (Nat.le_of_lt hv)]
      have h2 : (List.range n).drop v = v :: (List.range n).drop (v + 1) := by
        rw [← List.getElem_cons_drop hv', List.getElem_range]
      conv_lhs => rw [← List.take_append_drop v (List.range n), h1, h2]
    exact ⟨hgt, List.range v, (List.range n).drop (v + 1), hsplit,
      fun u hu => hmin u (List.mem_range.mp hu)⟩

/-- `findHeavyVar n b₀ sys = none` iff every `v < n` occurs in at most `b₀` equation scopes. -/
theorem findHeavyVar_eq_none_iff {n b₀ : ℕ} {sys : List (List (List ℕ))} :
    findHeavyVar n b₀ sys = none ↔ ∀ v < n, varDegree v sys ≤ b₀ := by
  rw [findHeavyVar, List.find?_eq_none]
  simp only [List.mem_range, Bool.not_eq_true, decide_eq_false_iff_not, not_lt]

theorem exists_sublist_of_mem_restrictEquation {v : ℕ} {val : Bool} {eq : List (List ℕ)}
    {m' : List ℕ} (hm' : m' ∈ restrictEquation v val eq) : ∃ m ∈ eq, m' <+ m := by
  unfold restrictEquation at hm'; cases val
  · simp only [Bool.false_eq_true, ↓reduceIte, List.mem_filter] at hm'
    exact ⟨m', hm'.1, List.Sublist.refl m'⟩
  · simp only [↓reduceIte] at hm'
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp (mem_of_mem_reduceEquation hm')
    exact ⟨m, hm, List.filter_sublist⟩

/-- `restrictEquation` preserves any monomial degree bound `≤ k`. -/
theorem length_mem_restrictEquation_le {k v : ℕ} {val : Bool} {eq : List (List ℕ)}
    (hdeg : ∀ m ∈ eq, m.length ≤ k) {m' : List ℕ} (hm' : m' ∈ restrictEquation v val eq) :
    m'.length ≤ k := by
  obtain ⟨m, hm, hsub⟩ := exists_sublist_of_mem_restrictEquation hm'
  exact hsub.length_le.trans (hdeg m hm)

/-- `restrictEquation` never increases the number of monomials. -/
theorem length_restrictEquation_le (v : ℕ) (val : Bool) (eq : List (List ℕ)) :
    (restrictEquation v val eq).length ≤ eq.length := by
  unfold restrictEquation; cases val
  · simp only [Bool.false_eq_true, ↓reduceIte]; exact List.length_filter_le _ _
  · simp only [↓reduceIte]
    exact (length_reduceEquation_le _).trans (by simp only [List.length_map, le_rfl])

/-- `restrictEquation v val eq` eliminates `v` from all output monomials. -/
theorem not_mem_of_mem_restrictEquation {v : ℕ} {val : Bool} {eq : List (List ℕ)} {m' : List ℕ}
    (hm' : m' ∈ restrictEquation v val eq) : v ∉ m' := by
  unfold restrictEquation at hm'; cases val
  · simp only [Bool.false_eq_true, ↓reduceIte, List.mem_filter, Bool.not_eq_true',
      decide_eq_false_iff_not] at hm'
    exact hm'.2
  · simp only [↓reduceIte] at hm'
    obtain ⟨m, -, rfl⟩ := List.mem_map.mp (mem_of_mem_reduceEquation hm')
    exact fun hvm => absurd rfl (of_decide_eq_true (List.mem_filter.mp hvm).2)

/-- **Exact variable-restriction semantics (§5.5, p. 38)**: evaluating `restrictEquation v val eq`
on `σ` agrees with evaluating `eq` on `Function.update σ v val`. -/
theorem evalMonomialList_restrictEquation (v : ℕ) (val : Bool) (eq : List (List ℕ))
    (σ : ℕ → Bool) :
    evalMonomialList (restrictEquation v val eq) σ =
      evalMonomialList eq (Function.update σ v val) := by
  unfold restrictEquation; cases val
  · simp only [Bool.false_eq_true, ↓reduceIte]
    induction eq with
    | nil => rfl
    | cons m ms ih =>
      by_cases hvm : v ∈ m
      · have hcond : (!decide (v ∈ m)) = false := by simp only [hvm, decide_true, Bool.not_true]
        have hall : m.all (Function.update σ v false) = false := by
          rw [Bool.eq_false_iff, ne_eq, List.all_eq_true]
          exact fun hall =>
            Bool.false_ne_true (by simpa only [Function.update_self] using hall v hvm)
        simp only [List.filter_cons, hcond, Bool.false_eq_true, ↓reduceIte, evalMonomialList_cons,
          hall, Bool.false_xor, ih]
      · have hcond : (!decide (v ∈ m)) = true := by simp only [hvm, decide_false, Bool.not_false]
        have hall : m.all (Function.update σ v false) = m.all σ := by
          rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
          refine ⟨fun h u hu => ?_, fun h u hu => ?_⟩ <;>
          · have huv : u ≠ v := fun e => hvm (by rw [← e]; exact hu)
            simpa only [Function.update_of_ne huv] using h u hu
        simp only [List.filter_cons, hcond, ↓reduceIte, evalMonomialList_cons, hall, ih]
  · simp only [↓reduceIte, evalMonomialList_reduceEquation]
    induction eq with
    | nil => rfl
    | cons m ms ih =>
      rw [List.map_cons, evalMonomialList_cons, evalMonomialList_cons, ih]
      congr 1; rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
      refine ⟨fun h u hu => ?_, fun h u hu => ?_⟩
      · by_cases huv : u = v
        · subst huv; simp only [Function.update_self]
        · simpa only [Function.update_of_ne huv] using
            h u (List.mem_filter.mpr ⟨hu, decide_eq_true huv⟩)
      · obtain ⟨hum, huv⟩ := List.mem_filter.mp hu
        simpa only [Function.update_of_ne (of_decide_eq_true huv)] using h u hum

/-! ### 4. Polynomial-Time Complexity Proofs (Plain `ComputableInPolyTime`) -/

section PolyTime

open ComputableInPolyTime

local notation "encM" => encList encNat
local notation "encEq" => encList (encList encNat)
local notation "encSys" => encList (encList (encList encNat))
local notation "encC" => encList (encPair encNat encBool)

private theorem computableInPolyTime_toggleMonomial :
    ComputableInPolyTime (fun p : List (List ℕ) × List ℕ => toggleMonomial p.1 p.2)
      (encPair encEq encM) encEq := by
  unfold toggleMonomial; fun_prop

/-- Mod-2 duplicate monomial cancellation `reduceEquation` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_reduceEquation :
    ComputableInPolyTime reduceEquation encEq encEq := by
  unfold reduceEquation
  have hq := fst (encPair encEq encEq) encM
  exact foldlWith_of_bounded_growth (encA := encM) (encL := encEq) (encB := encEq)
    (par := fun x => x) (list := fun x => x) (init := fun _ => [])
    (step := fun _ state m => toggleMonomial state m)
    id' id' (const []) (computableInPolyTime_toggleMonomial.comp (hq.snd'.prod (snd _ _)))
    (growth := fun eq => 2 * (encEq eq).length + 1)
    (((PolyBounded.const 2).mul .self).add (.const 1))
    (fun eq state m hm => by
      have hmem := SizedListEncoding.length_elem_le (encA := encM) (encL := encEq) eq m hm
      unfold toggleMonomial; split_ifs
      · exact (length_encList_sublist encM List.filter_sublist).trans (Nat.le_add_right _ _)
      · simp only [encList_append, encList_cons, encList_nil, List.append_nil, List.length_append,
          length_frame]; omega)

/-- Mod-2 equation symmetric difference `xorEquation` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_xorEquation :
    ComputableInPolyTime (fun p : List (List ℕ) × List (List ℕ) => xorEquation p.1 p.2)
      (encPair encEq encEq) encEq := by
  unfold xorEquation; fun_prop

private theorem computableInPolyTime_insertSorted :
    ComputableInPolyTime (fun p : List ℕ × ℕ => insertSorted p.1 p.2)
      (encPair encM encNat) encM := by
  unfold insertSorted; fun_prop

private theorem length_encM_sortDedup_le (vs : List ℕ) :
    (encM (sortDedup vs)).length ≤ vs.length * (2 * (encM vs).length + 1) :=
  (length_encList_le encNat (sortDedup vs) fun u hu =>
    SizedListEncoding.length_elem_le (encA := encNat) (encL := encM) vs u (mem_sortDedup.mp hu)
    ).trans (Nat.mul_le_mul_right _ (length_sortDedup_le vs))

@[local fun_prop]
private theorem computableInPolyTime_sortDedup :
    ComputableInPolyTime sortDedup encM encM :=
  foldl' (encA := encNat) (encL := encM) (encB := encM)
    (list := fun x => x) (init := fun _ => []) (step := insertSorted)
    id' (const []) computableInPolyTime_insertSorted
    (B := fun vs => (encM vs).length * (2 * (encM vs).length + 1))
    (PolyBounded.self.mul (((PolyBounded.const 2).mul .self).add (.const 1)))
    (fun vs i _ => by
      change (encM (sortDedup (vs.take i))).length ≤ _
      have htake := length_encList_sublist encNat (List.take_sublist i vs)
      have hlen := (List.length_take_le' i vs).trans
        (SizedListEncoding.length_le (encA := encNat) (encL := encM) vs)
      exact (length_encM_sortDedup_le (vs.take i)).trans
        (Nat.mul_le_mul hlen (Nat.add_le_add_right (Nat.mul_le_mul_left 2 htake) 1)))

private theorem computableInPolyTime_isTautologicalClause :
    ComputableInPolyTime isTautologicalClause encC encBool := by
  unfold isTautologicalClause; fun_prop

private theorem computableInPolyTime_posVars :
    ComputableInPolyTime posVars encC encM := by
  unfold posVars; fun_prop

private theorem computableInPolyTime_negVars :
    ComputableInPolyTime negVars encC encM := by
  unfold negVars; fun_prop

private theorem length_encNat_le_of_mem_clause {c : Clause ℕ} {v : ℕ} {b : Bool}
    (h : (v, b) ∈ c) : (encNat v).length ≤ (encC c).length :=
  (length_le_encPair_left encNat encBool (v, b)).trans
    (SizedListEncoding.length_elem_le (encA := encPair encNat encBool) (encL := encC) c (v, b) h)

private theorem foldl_expand_bounds (l : List ℕ) (B : ℕ) (hl : ∀ u ∈ l, (encNat u).length ≤ B) :
    ∀ (acc : List (List ℕ)) (d : ℕ),
      (∀ m ∈ acc, IsCanonicalMonomial m ∧ m.length ≤ d ∧ ∀ u ∈ m, (encNat u).length ≤ B) →
      let res := l.foldl (fun a v => a ++ a.map fun m => insertSorted m v) acc
      res.length = acc.length * 2 ^ l.length ∧
        ∀ m ∈ res, m.length ≤ d + l.length ∧ ∀ u ∈ m, (encNat u).length ≤ B := by
  induction l with
  | nil =>
    intro acc d hacc
    refine ⟨by simp only [List.foldl_nil, List.length_nil, pow_zero, Nat.mul_one], fun m hm => ?_⟩
    obtain ⟨-, hml, hmsz⟩ := hacc m hm
    exact ⟨by simpa only [List.length_nil, Nat.add_zero] using hml, hmsz⟩
  | cons v vs ih =>
    intro acc d hacc
    have hacc' : ∀ m' ∈ acc ++ acc.map (fun m => insertSorted m v),
        IsCanonicalMonomial m' ∧ m'.length ≤ d + 1 ∧ ∀ u ∈ m', (encNat u).length ≤ B := by
      intro m' hm'
      rcases List.mem_append.mp hm' with hm1 | hm2
      · obtain ⟨hmc, hml, hmsz⟩ := hacc m' hm1
        exact ⟨hmc, Nat.le_succ_of_le hml, hmsz⟩
      · obtain ⟨m₀, hm₀, rfl⟩ := List.mem_map.mp hm2
        obtain ⟨hmc, hml, hmsz⟩ := hacc m₀ hm₀
        refine ⟨isCanonicalMonomial_insertSorted hmc v,
          (length_insertSorted_le hmc v).trans (Nat.succ_le_succ hml), fun u hu => ?_⟩
        rcases mem_insertSorted.mp hu with hum₀ | huv
        · exact hmsz u hum₀
        · rw [huv]; exact hl v List.mem_cons_self
    obtain ⟨hr_len, hr_mem⟩ := ih (fun u hu => hl u (List.mem_cons_of_mem v hu)) _ (d + 1) hacc'
    refine ⟨?_, fun m hm => ?_⟩
    · simp only [List.foldl_cons, hr_len, List.length_append, List.length_map, List.length_cons,
        pow_succ]; ring
    · obtain ⟨hml, hmsz⟩ := hr_mem m hm
      exact ⟨by simp only [List.length_cons]; omega, hmsz⟩

private theorem expandPosVars_size_aux (base vs : List ℕ) (k B : ℕ)
    (hbase_can : IsCanonicalMonomial base) (hbase_len : base.length ≤ k) (hvs_len : vs.length ≤ k)
    (hbase_sz : ∀ u ∈ base, (encNat u).length ≤ B) (hvs_sz : ∀ u ∈ vs, (encNat u).length ≤ B) :
    ∀ i ≤ vs.length,
      (encEq ((vs.take i).foldl
        (fun acc v => acc ++ acc.map fun m => insertSorted m v) [base])).length ≤
        2 ^ k * (2 * ((2 * k) * (2 * B + 1)) + 1) := by
  intro i _
  have htake_len : (vs.take i).length ≤ k := (List.length_take_le' i vs).trans hvs_len
  obtain ⟨hr_len, hr_mem⟩ := foldl_expand_bounds (vs.take i) B
    (fun u hu => hvs_sz u (List.mem_of_mem_take hu)) [base] k
    (fun m hm => List.mem_singleton.mp hm ▸ ⟨hbase_can, hbase_len, hbase_sz⟩)
  refine (length_encList_le encM _ (b := (2 * k) * (2 * B + 1)) fun m hm => ?_).trans ?_
  · obtain ⟨hml, hmu⟩ := hr_mem m hm
    exact (length_encList_le encNat m hmu).trans (Nat.mul_le_mul_right _ (by omega))
  · rw [hr_len, List.length_singleton, Nat.one_mul]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) htake_len)

/-- For any fixed width bound `k : ℕ`, compiling a clause with width guard `k` into a canonical
sparse `𝔽₂` polynomial is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_compileClauseBounded (k : ℕ) :
    ComputableInPolyTime (compileClauseBounded k) encC encEq := by
  have htake : ComputableInPolyTime (fun c : Clause ℕ => c.take k) encC encC := by fun_prop
  have hstep : ComputableInPolyTime
      (fun p : List (List ℕ) × ℕ => p.1 ++ p.1.map fun m => insertSorted m p.2)
      (encPair encEq encNat) encEq := by
    have := computableInPolyTime_insertSorted; fun_prop
  have hexpand : ComputableInPolyTime
      (fun c : Clause ℕ => expandPosVars (negVars (c.take k)) (posVars (c.take k)))
      encC encEq := by
    unfold expandPosVars
    have hp := computableInPolyTime_posVars.comp htake
    have hn := computableInPolyTime_negVars.comp htake
    exact foldl' (encA := encNat) (encL := encM) (encB := encEq)
      (list := fun c : Clause ℕ => posVars (c.take k))
      (init := fun c : Clause ℕ => [negVars (c.take k)])
      (step := fun acc v => acc ++ acc.map fun m => insertSorted m v)
      hp ((snoc encM).comp ((const []).prod hn)) hstep
      (B := fun c => 2 ^ k * (2 * ((2 * k) * (2 * (encC c).length + 1)) + 1))
      ((PolyBounded.const (2 ^ k)).mul
        (((PolyBounded.const 2).mul
          ((PolyBounded.const (2 * k)).mul
            (((PolyBounded.const 2).mul .self).add (.const 1)))).add (.const 1)))
      (fun c i hi => by
        have hlen_c' : (c.take k).length ≤ k := List.length_take_le k c
        exact expandPosVars_size_aux (negVars (c.take k)) (posVars (c.take k)) k (encC c).length
          (isCanonicalMonomial_sortDedup _)
          ((length_negVars_le _).trans hlen_c') ((length_posVars_le _).trans hlen_c')
          (fun _ hu =>
            length_encNat_le_of_mem_clause (List.mem_of_mem_take (mem_negVars_iff.mp hu)))
          (fun _ hu =>
            length_encNat_le_of_mem_clause (List.mem_of_mem_take (mem_posVars_iff.mp hu)))
          i hi)
  exact (computableInPolyTime_isTautologicalClause.comp htake).ite (const []) hexpand

/-- Reducing an equation modulo `2` (`reduceEquation`) does not increase its encoded length. -/
theorem length_enc_reduceEquation_le (l : List (List ℕ)) :
    (encEq (reduceEquation l)).length ≤ (encEq l).length := by
  have hred : ∀ (L acc : List (List ℕ)),
      (encEq (L.foldl toggleMonomial acc)).length ≤ (encEq acc).length + (encEq L).length := by
    intro L
    induction L with
    | nil =>
      intro acc; simp only [List.foldl_nil, encList_nil, List.length_nil, Nat.add_zero, le_rfl]
    | cons m ms ih =>
      intro acc
      have hstep : (encEq (toggleMonomial acc m)).length ≤
          (encEq acc).length + (frame (encM m)).length := by
        unfold toggleMonomial; split_ifs
        · exact (length_encList_sublist encM List.filter_sublist).trans (Nat.le_add_right _ _)
        · simp only [encList_append, encList_cons, encList_nil, List.append_nil,
            List.length_append, le_rfl]
      calc (encEq ((m :: ms).foldl toggleMonomial acc)).length
          ≤ (encEq (toggleMonomial acc m)).length + (encEq ms).length := ih _
        _ ≤ (encEq acc).length + (frame (encM m)).length + (encEq ms).length :=
            Nat.add_le_add_right hstep _
        _ = (encEq acc).length + (encEq (m :: ms)).length := by
            simp only [encList_cons, List.length_append]; omega
  simpa only [reduceEquation, encList_nil, List.length_nil, Nat.zero_add] using hred l []

private theorem length_encEq_xorEquation_le (eq1 eq2 : List (List ℕ)) :
    (encEq (xorEquation eq1 eq2)).length ≤ (encEq eq1).length + (encEq eq2).length :=
  (length_enc_reduceEquation_le (eq1 ++ eq2)).trans_eq (by
    simp only [encList_append, List.length_append])

private theorem compileParityRowBounded_eq_foldl (k : ℕ) (φ : CNF ℕ) (row : List Bool) :
    compileParityRowBounded k φ row =
      (List.range φ.length).foldl
        (fun acc e =>
          if row.getD e false then xorEquation acc (compileClauseBounded k (φ.getD e [])) else acc)
        [] := by
  unfold compileParityRowBounded compileParityRow compileClauseBounded
  rw [List.length_map]
  have hcongr : ∀ (l : List ℕ) (hl : ∀ e ∈ l, e < φ.length) (acc : List (List ℕ)),
      l.foldl (fun a e =>
        if row.getD e false then xorEquation a (compileClause ((φ.map (List.take k)).getD e []))
        else a) acc =
      l.foldl (fun a e =>
        if row.getD e false then xorEquation a (compileClause ((φ.getD e []).take k))
        else a) acc := by
    intro l hl acc
    induction l generalizing acc with
    | nil => rfl
    | cons e es ih =>
      have he : e < φ.length := hl e List.mem_cons_self
      have hget1 : (φ.map (List.take k)).getD e [] = φ[e].take k := by
        rw [List.getD_eq_getElem _ _ (by simp only [List.length_map]; exact he), List.getElem_map]
      simp only [List.foldl_cons, hget1, List.getD_eq_getElem _ _ he]
      exact ih (fun e' he' => hl e' (List.mem_cons_of_mem _ he')) _
  exact hcongr (List.range φ.length) (fun _ he => List.mem_range.mp he) []

private theorem length_encEq_compileClauseBounded_le (k : ℕ) (c : Clause ℕ) :
    (encEq (compileClauseBounded k c)).length ≤
      2 ^ k * (2 * (k * (2 * (encC c).length + 1)) + 1) := by
  have hc_len : (c.take k).length ≤ k := List.length_take_le k c
  refine (length_encList_le encM (compileClause (c.take k))
    (b := k * (2 * (encC c).length + 1)) fun m hm => ?_).trans ?_
  · refine (length_encList_le encNat m (b := (encC c).length) fun v hv => ?_).trans ?_
    · obtain ⟨b, hb⟩ := mem_clause_of_mem_compileClause hm hv
      exact length_encNat_le_of_mem_clause (List.mem_of_mem_take hb)
    · exact Nat.mul_le_mul_right _ ((length_mem_compileClause_le hm).trans hc_len)
  · exact Nat.mul_le_mul_right _
      ((length_compileClause_le (c.take k)).trans (Nat.pow_le_pow_right (by omega) hc_len))

/-- For any fixed width bound `k : ℕ`, compiling a parity-check row on `φ : CNF ℕ` is
polynomial-time (for any sized Boolean list encoding `encRow`, such as `encBits` or
`encList encBool`). -/
@[fun_prop]
theorem computableInPolyTime_compileParityRowBounded (k : ℕ)
    {encRow : List Bool ↪ List Bool} [ListEncoding encBool encRow]
    [SizedListEncoding encBool encRow] :
    ComputableInPolyTime (fun p : CNF ℕ × List Bool => compileParityRowBounded k p.1 p.2)
      (encPair encCNF encRow) encEq := by
  unfold encCNF
  have hstep : ComputableInPolyTime
      (fun q : ((CNF ℕ × List Bool) × List (List ℕ)) × ℕ =>
        if q.1.1.2.getD q.2 false then
          xorEquation q.1.2 (compileClauseBounded k (q.1.1.1.getD q.2 []))
        else q.1.2)
      (encPair (encPair (encPair (encList encC) encRow) encEq) encUnary) encEq := by
    have hcond := (listGetD (encA := encBool) (encL := encRow) false).comp
      (((fst (encPair (encPair (encList encC) encRow) encEq) encUnary).fst'.snd').prod (snd _ _))
    have hcl := (computableInPolyTime_compileClauseBounded k).comp
      ((listGetD (encA := encC) (encL := encList encC) []).comp
        (((fst (encPair (encPair (encList encC) encRow) encEq) encUnary).fst'.fst').prod (snd _ _)))
    exact hcond.ite (computableInPolyTime_xorEquation.comp (((fst _ _).snd').prod hcl))
      ((fst _ _).snd')
  have hfold := foldlWith_of_bounded_growth (encA := encUnary) (encL := encList encUnary)
    (encB := encEq) (par := fun p => p) (list := fun p : CNF ℕ × List Bool => List.range p.1.length)
    (init := fun _ => [])
    (step := fun p acc e =>
      if p.2.getD e false then xorEquation acc (compileClauseBounded k (p.1.getD e [])) else acc)
    id' (range.comp ((length_list encC).comp (fst _ _))) (const []) hstep
    (growth := fun p =>
      2 ^ k * (2 * (k * (2 * (encPair (encList encC) encRow p).length + 1)) + 1))
    ((PolyBounded.const (2 ^ k)).mul
      (((PolyBounded.const 2).mul
        ((PolyBounded.const k).mul
          (((PolyBounded.const 2).mul .self).add (.const 1)))).add (.const 1)))
    (fun p acc e he => by
      split_ifs
      · have he_lt : e < p.1.length := List.mem_range.mp he
        have hc_sz : (encC (p.1.getD e [])).length ≤ (encPair (encList encC) encRow p).length := by
          rw [List.getD_eq_getElem _ _ he_lt]
          exact (SizedListEncoding.length_elem_le (encA := encC) (encL := encList encC)
            p.1 p.1[e] (List.getElem_mem he_lt)).trans
            (length_le_encPair_left (encList encC) encRow p)
        have hcb := (length_encEq_compileClauseBounded_le k (p.1.getD e [])).trans
          (Nat.mul_le_mul_left (2 ^ k)
            (Nat.add_le_add_right
              (Nat.mul_le_mul_left 2
                (Nat.mul_le_mul_left k
                  (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hc_sz) 1))) 1))
        exact (length_encEq_xorEquation_le acc _).trans (Nat.add_le_add_left hcb _)
      · exact Nat.le_add_right _ _)
  exact hfold.of_enc_eq fun p => congrArg encEq (compileParityRowBounded_eq_foldl k p.1 p.2)

/-- For any fixed width bound `k : ℕ`, compiling a list of parity-check rows on `φ : CNF ℕ` into a
sparse degree-`≤ k` `𝔽₂` polynomial system is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_compileParitySystemBounded (k : ℕ)
    {encRow : List Bool ↪ List Bool} [ListEncoding encBool encRow]
    [SizedListEncoding encBool encRow] :
    ComputableInPolyTime
      (fun p : CNF ℕ × List (List Bool) => compileParitySystemBounded k p.1 p.2)
      (encPair encCNF (encList encRow)) encSys :=
  mapWithInput (snd encCNF (encList encRow))
    ((computableInPolyTime_compileParityRowBounded k (encRow := encRow)).comp
      (((fst _ _).fst').prod (snd _ _)))

@[local fun_prop]
private theorem computableInPolyTime_equationVars :
    ComputableInPolyTime equationVars encEq encM := by
  unfold equationVars; fun_prop

/-- Computing `varDegree v sys` (returned in unary) is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_varDegree :
    ComputableInPolyTime (fun p : ℕ × List (List (List ℕ)) => varDegree p.1 p.2)
      (encPair encNat encSys) encUnary := by
  unfold varDegree; fun_prop

/-- Finding the first heavy variable `v < n` with `varDegree v sys > b₀` (`n` in unary, `b₀` in
binary, result in `encOption encNat`) is polynomial-time. -/
theorem computableInPolyTime_findHeavyVar :
    ComputableInPolyTime
      (fun p : (ℕ × ℕ) × List (List (List ℕ)) => findHeavyVar p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encNat) encSys) (encOption encNat) := by
  have hdeg := computableInPolyTime_varDegree
  have hrange : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × List (List (List ℕ)) => (List.range p.1.1).map fun v => v)
      (encPair (encPair encUnary encNat) encSys) (encList encNat) :=
    mapWithInput (range.comp ((fst _ _).fst')) (unary_to_binary.comp (snd _ _))
  have hpred : ComputableInPolyTime
      (fun q : ((ℕ × ℕ) × List (List (List ℕ))) × ℕ => decide (q.1.1.2 < varDegree q.2 q.1.2))
      (encPair (encPair (encPair encUnary encNat) encSys) encNat) encBool :=
    binary_lt' ((fst _ _).fst'.snd')
      (unary_to_binary.comp (hdeg.comp ((snd _ _).prod ((fst _ _).snd'))))
  have hfind := findWithInput (test := fun x v => decide (x.1.2 < varDegree v x.2)) hrange hpred
  refine hfind.of_enc_eq fun p => congrArg (encOption encNat) ?_
  rw [List.map_id']; rfl

@[fun_prop]
theorem computableInPolyTime_findHeavyVar_apply {α : Type} {encIn : α ↪ List Bool}
    {fn fb : α → ℕ} {fsys : α → List (List (List ℕ))}
    (hn : ComputableInPolyTime fn encIn encUnary)
    (hb : ComputableInPolyTime fb encIn encNat)
    (hsys : ComputableInPolyTime fsys encIn encSys) :
    ComputableInPolyTime (fun x => findHeavyVar (fn x) (fb x) (fsys x)) encIn (encOption encNat) :=
  computableInPolyTime_findHeavyVar.comp ((hn.pair (enc := encPair encUnary encNat) hb).pair hsys)

/-- Substituting `x_v = val` into a sparse `𝔽₂` equation (`restrictEquation`) is polynomial-time. -/
theorem computableInPolyTime_restrictEquation :
    ComputableInPolyTime
      (fun p : (ℕ × Bool) × List (List ℕ) => restrictEquation p.1.1 p.1.2 p.2)
      (encPair (encPair encNat encBool) encEq) encEq := by
  unfold restrictEquation; fun_prop

@[fun_prop]
theorem computableInPolyTime_restrictEquation_apply {α : Type} {encIn : α ↪ List Bool}
    {fv : α → ℕ} {fval : α → Bool} {feq : α → List (List ℕ)}
    (hv : ComputableInPolyTime fv encIn encNat)
    (hval : ComputableInPolyTime fval encIn encBool)
    (heq : ComputableInPolyTime feq encIn encEq) :
    ComputableInPolyTime (fun x => restrictEquation (fv x) (fval x) (feq x)) encIn encEq :=
  computableInPolyTime_restrictEquation.comp
    ((hv.pair (enc := encPair encNat encBool) hval).pair heq)

/-- Substituting `x_v = val` across a sparse `𝔽₂` system (`restrictSystem`) is polynomial-time. -/
theorem computableInPolyTime_restrictSystem :
    ComputableInPolyTime
      (fun p : (ℕ × Bool) × List (List (List ℕ)) => restrictSystem p.1.1 p.1.2 p.2)
      (encPair (encPair encNat encBool) encSys) encSys :=
  mapWithInput (snd (encPair encNat encBool) encSys)
    (computableInPolyTime_restrictEquation.comp (((fst _ _).fst').prod (snd _ _)))

@[fun_prop]
theorem computableInPolyTime_restrictSystem_apply {α : Type} {encIn : α ↪ List Bool}
    {fv : α → ℕ} {fval : α → Bool} {fsys : α → List (List (List ℕ))}
    (hv : ComputableInPolyTime fv encIn encNat)
    (hval : ComputableInPolyTime fval encIn encBool)
    (hsys : ComputableInPolyTime fsys encIn encSys) :
    ComputableInPolyTime (fun x => restrictSystem (fv x) (fval x) (fsys x)) encIn encSys :=
  computableInPolyTime_restrictSystem.comp
    ((hv.pair (enc := encPair encNat encBool) hval).pair hsys)

end PolyTime

end Cslib.Complexity
