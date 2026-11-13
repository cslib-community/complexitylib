/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.EdgeCSP.Blossom.Size
public import CslibFrontier.Computability.PolyTime.CSP.Table
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import Mathlib.Data.List.MinMax
import Mathlib.Algebra.Order.BigOperators.Group.List
public import CslibFrontier.Computability.PolyTime.CSP.Edge.Augmenting

/-!
# Bit storage of explicit-table solver instances

Storage charges full binary names and declared arities, row bits, and every list/pair frame.
The quantitative bookkeeping here is original. The actual contraction's row/variable bounds
come from Observation 26 and Corollary 27 of [KazdaKolmogorovRolinek2018],
arXiv:1602.03124v6, printed p. 13. No unit-cost name or table access is used in the bounds.
-/

public section

namespace Cslib.Complexity.CSP.EdgeSolver.Size

open Cslib.Logic.PL Cslib.Logic.PL.CSP Turing.MultiTapeTM

/-- Total number of actual stored rows, retaining duplicate constraints and duplicate rows. -/
@[expose] def rowCount (F : CSP Table ℕ) : ℕ := (F.map fun c => c.rel.rows.length).sum

/-- A fresh connector increases maximum binary name length additively. The bound depends on
the actual constraint count; it never enumerates the interval below an original name. -/
theorem connector_bits_le (F : CSP Table ℕ) (B : ℕ)
    (hB : ∀ v ∈ F.vars, (encNat v).length ≤ B) (i : Fin F.length) :
    (encNat (Blossom.connector F i)).length ≤ B + F.length + 3 := by
  have hnames : ∀ v ∈ F.vars, v ≤ 2 ^ B - 1 := by
    intro v hv
    have hb := hB v hv
    simp only [encNat_apply, Nat.size_eq_bits_len] at hb
    have := Nat.size_le.mp hb
    omega
  have hm := List.max_le_of_forall_le F.vars (2 ^ B - 1) hnames
  change F.vars.foldr max 0 ≤ 2 ^ B - 1 at hm
  have hp : 0 < 2 ^ B := Nat.two_pow_pos B
  have hs : (F.vars.foldr max 0).size ≤ B := Nat.size_le.mpr (by omega)
  have ha := Nat.size_add_le (F.vars.foldr max 0) 1
  have hc := Nat.size_add_le (F.vars.foldr max 0 + 1) i.val
  have hi := Nat.size_le_self i.val
  simp only [Blossom.connector, Blossom.freshBase, encNat_apply, Nat.size_eq_bits_len]
  norm_num only [Nat.size_one] at ha
  omega

/-- Every name in the actual child is either an unchanged outside name or one of the actual
fresh connectors. This includes arbitrary sparse original names and every framing bit. -/
theorem contract_name_bits_le (F : CSP Table ℕ) (f : OccurrenceLabeling F Bool)
    (vs : List ℕ) (B : ℕ) (hB : ∀ v ∈ F.vars, (encNat v).length ≤ B) :
    ∀ v ∈ (Blossom.contract f vs).vars, (encNat v).length ≤ B + F.length + 3 := by
  intro v hv
  have hm : v ∈ (F.vars.toFinset \ vs.toFinset) ∪ (Blossom.connectors F vs).toFinset := by
    rw [← Blossom.vars_contract f vs]
    exact List.mem_toFinset.mpr hv
  rcases Finset.mem_union.mp hm with ho | hn
  · have hb := hB v (List.mem_toFinset.mp (Finset.mem_sdiff.mp ho).1)
    omega
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hn)
    exact connector_bits_le F B hB i

/-- Full framed storage of any valid explicit-table occurrence problem. The bound includes
binary declared arities, every stored row and variable-name bit, and all nested list framing.
The arities are derived from actual local validity; huge malformed declared widths cannot
silently enter this estimate. -/
theorem encoded_body_le (F : CSP Table ℕ) (f : OccurrenceLabeling F Bool)
    (hf : ValidLabeling Table.sem f) (B : ℕ)
    (hB : ∀ v ∈ F.vars, (encNat v).length ≤ B) :
    (encCSP encTable encNat F).length ≤
      7 * F.length + (4 * B + 10) * F.vars.length +
        4 * (6 * F.vars.length + 1) * rowCount F := by
  have htable (c : Constraint Table ℕ) (hc : c ∈ F) :
      c.rel.wellFormed = true ∧ c.rel.arity = c.scope.length := by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
    have hs := Table.sem_eq_true.mp (hf ⟨i, hi⟩)
    refine ⟨hs.1, ?_⟩
    have hl := Table.wellFormed_eq_true.mp hs.1 _ hs.2
    simpa only [localTuple, List.length_ofFn, Fin.getElem_fin] using hl.symm
  have hscope (c : Constraint Table ℕ) (hc : c ∈ F) :
      (encList encNat c.scope).length ≤ c.scope.length * (2 * B + 1) := by
    rw [length_encList]
    calc
      _ ≤ (c.scope.map fun _ => 2 * B + 1).sum := by
        apply List.sum_le_sum
        intro v hv
        have hb := hB v (List.mem_flatMap.mpr ⟨c, hc, hv⟩)
        omega
      _ = _ := by simp [Nat.mul_comm]
  have hclause (c : Constraint Table ℕ) (hc : c ∈ F) :
      2 * (encConstraint encTable encNat c).length + 1 ≤
        7 + (4 * B + 10) * c.scope.length + 4 * (6 * F.vars.length + 1) * c.rel.rows.length := by
    have hw := (htable c hc).1
    have ha := (htable c hc).2
    have hb : (encNat c.rel.arity).length ≤ c.scope.length := by
      simp only [encNat_apply, Nat.size_eq_bits_len]
      exact (Nat.size_le_self _).trans_eq ha
    have hn : c.scope.length ≤ F.vars.length := by
      have hh := List.le_sum_of_mem (List.mem_map.mpr ⟨c, hc, rfl⟩ :
        c.scope.length ∈ F.map fun d => d.scope.length)
      simpa only [vars, List.length_flatMap] using hh
    have hs := hscope c hc
    have hr : c.rel.rows.length * (6 * c.rel.arity + 1) ≤
        c.rel.rows.length * (6 * F.vars.length + 1) := Nat.mul_le_mul_left _ (by omega)
    simp only [encConstraint_apply, length_encPair, length_encTable hw]
    nlinarith
  rw [encCSP, length_encList]
  calc
    _ ≤ (F.map fun c => 7 + (4 * B + 10) * c.scope.length +
        4 * (6 * F.vars.length + 1) * c.rel.rows.length).sum := List.sum_le_sum hclause
    _ = _ := by
      simp only [List.sum_map_add, List.sum_map_mul_left, rowCount, vars, List.length_flatMap]
      simp [Nat.mul_comm]

/-- A finite history of actual whole-instance blossom contractions. Labels and blossoms are
the existing mathematical objects, not resource certificates or alternative CSP instances. -/
inductive Chain (F : CSP Table ℕ) : ℕ → CSP Table ℕ → Prop where
  /-- The original explicit-table problem. -/
  | nil : Chain F 0 F
  /-- One actual valid prepared blossom and its exact constructor. -/
  | step {k : ℕ} {G : CSP Table ℕ} (previous : Chain F k G)
      (f : OccurrenceLabeling G Bool) (w : Walk G)
      (valid : ValidLabeling Table.sem f) (blossom : w.IsBlossom Table.sem f) :
      Chain F (k + 1) (Blossom.contract f (Blossom.internal w))

variable {F G : CSP Table ℕ} {k : ℕ}

/-- Every body in an actual contraction history retains the original edge model. -/
theorem Chain.edge (h : Chain F k G) (hF : EdgeInstance F) : EdgeInstance G := by
  induction h with
  | nil => exact hF
  | step previous f w valid blossom ih => exact Blossom.edge_contract ih f (Blossom.internal w)

/-- Each stored parent contributes exactly one new constraint, including all old nullaries. -/
theorem Chain.length (h : Chain F k G) : G.length = F.length + k := by
  induction h with
  | nil => simp
  | step previous f w valid blossom ih => simp only [Blossom.length_contract, ih]; omega

/-- Variable counts do not increase anywhere along the actual contraction history. -/
theorem Chain.numVars_le (h : Chain F k G) (hF : EdgeInstance F) : G.numVars ≤ F.numVars := by
  induction h with
  | nil => rfl
  | step previous f w valid blossom ih =>
    exact (Blossom.numVars_contract_le (previous.edge hF) blossom.1 blossom.2.1 f).trans ih

/-- Every descent spends the actual concrete measure, including `r = b` contractions. -/
theorem Chain.measure_add_le (h : Chain F k G) (hF : EdgeInstance F) :
    k + G.contractionMeasure ≤ F.contractionMeasure := by
  induction h with
  | nil => simp
  | step previous f w valid blossom ih =>
    have := Blossom.contractionMeasure_contract_lt (previous.edge hF) blossom
    omega

/-- All contractions in one improvement have depth at most twice the original variable count. -/
theorem Chain.depth_le (h : Chain F k G) (hF : EdgeInstance F) : k ≤ 2 * F.numVars := by
  have := h.measure_add_le hF
  unfold contractionMeasure at this
  omega

/-- The total stored row count grows only additively with descent depth, not multiplicatively. -/
theorem Chain.rowCount_le (h : Chain F k G) (hF : EdgeInstance F) :
    rowCount G ≤ rowCount F + k * F.numVars := by
  induction h with
  | nil => simp
  | @step j H previous f w valid blossom ih =>
    have hr := Blossom.totalRows_contract_le f (Blossom.internal w)
    have ht := Blossom.length_touched_le_internal (previous.edge hF) blossom.1 blossom.2.1
    have hb := Finset.card_le_card (Blossom.internal_subset_vars w)
    have hn := previous.numVars_le hF
    change rowCount (Blossom.contract f (Blossom.internal w)) ≤
      rowCount _ + (Blossom.touched _ (Blossom.internal w)).length at hr
    change (Blossom.internal w).toFinset.card ≤ H.numVars at hb
    nlinarith

/-- Full binary original-name storage grows additively along every actual contraction history. -/
theorem Chain.name_bits_le (h : Chain F k G) (hF : EdgeInstance F) (B : ℕ)
    (hB : ∀ v ∈ F.vars, (encNat v).length ≤ B) :
    ∀ v ∈ G.vars, (encNat v).length ≤ B + k * (F.length + 2 * F.numVars + 3) := by
  induction h with
  | nil => simpa only [Nat.zero_mul, Nat.add_zero] using hB
  | @step j H previous f w valid blossom ih =>
    intro v hv
    have hb := contract_name_bits_le H f (Blossom.internal w)
      (B + j * (F.length + 2 * F.numVars + 3)) ih v hv
    have hl := previous.length
    have hd := previous.depth_le hF
    nlinarith

/-- Full binary fresh-name budget across one complete descent. All counts are actual lists;
the original complete framed input pays for its maximum original name bit length. -/
@[expose] def nameBudget (F : CSP Table ℕ) : ℕ :=
  (encCSP encTable encNat F).length +
    2 * F.vars.length * (F.length + 2 * F.vars.length + 3)

/-- Stored-row budget across one complete descent, including all central one-hot rows. -/
@[expose] def rowBudget (F : CSP Table ℕ) : ℕ :=
  rowCount F + 2 * F.vars.length * F.vars.length

/-- Full framed body-storage budget, polynomial in actual original counts and bit lengths. -/
@[expose] def bodyBudget (F : CSP Table ℕ) : ℕ :=
  7 * (F.length + 2 * F.vars.length) +
    (4 * nameBudget F + 10) * (2 * F.vars.length) +
      4 * (12 * F.vars.length + 1) * rowBudget F

/-- Every original binary name is charged by the complete original CSP encoding. -/
theorem original_name_bits_le (F : CSP Table ℕ) :
    ∀ v ∈ F.vars, (encNat v).length ≤ (encCSP encTable encNat F).length := by
  intro v hv
  obtain ⟨c, hc, hv⟩ := List.mem_flatMap.mp hv
  have hn := length_le_encList_of_mem encNat hv
  have hb := length_le_encList_of_mem (encConstraint encTable encNat) hc
  simp only [encConstraint_apply, length_encPair] at hb
  change 2 * (encTable c.rel).length + 1 + (encList encNat c.scope).length ≤
    (encCSP encTable encNat F).length at hb
  exact hn.trans (by omega)

/-- Every actual descended body obeys the original polynomial binary-name budget. -/
theorem Chain.name_budget (h : Chain F k G) (hF : EdgeInstance F) :
    ∀ v ∈ G.vars, (encNat v).length ≤ nameBudget F := by
  have hn : F.numVars ≤ F.vars.length := List.toFinset_card_le _
  have hk := (h.depth_le hF).trans (Nat.mul_le_mul_left 2 hn)
  intro v hv
  exact (h.name_bits_le hF _ (original_name_bits_le F) v hv).trans (by
    unfold nameBudget
    gcongr)

/-- Complete framed bit storage of every actual valid descended body has one fixed original
polynomial bound. This includes duplicate/nullary constraints and full binary name lengths. -/
theorem Chain.body_budget (h : Chain F k G) (hF : EdgeInstance F)
    (f : OccurrenceLabeling G Bool) (hf : ValidLabeling Table.sem f) :
    (encCSP encTable encNat G).length ≤ bodyBudget F := by
  have hn : F.numVars ≤ F.vars.length := List.toFinset_card_le _
  have hk := (h.depth_le hF).trans (Nat.mul_le_mul_left 2 hn)
  have hl : G.length ≤ F.length + 2 * F.vars.length := by rw [h.length]; omega
  have hv : G.vars.length ≤ 2 * F.vars.length := by
    rw [(h.edge hF).length_vars_eq_two_mul_numVars]
    exact Nat.mul_le_mul_left 2 ((h.numVars_le hF).trans hn)
  have hr : rowCount G ≤ rowBudget F := (h.rowCount_le hF).trans (by
    unfold rowBudget
    gcongr)
  refine (encoded_body_le G f hf (nameBudget F) (h.name_budget hF)).trans ?_
  calc
    _ ≤ 7 * (F.length + 2 * F.vars.length) +
        (4 * nameBudget F + 10) * (2 * F.vars.length) +
          4 * (6 * (2 * F.vars.length) + 1) * rowBudget F := by gcongr
    _ = bodyBudget F := by unfold bodyBudget; ring

/-- The binary-position encoding of any actual trail includes every original start-name bit
and every step's two global positions and pair/list framing. -/
theorem encoded_walk_le {H : CSP Table ℕ} (w : Walk H) (hw : w.IsWalk) (B : ℕ)
    (hb : (encNat w.start).length ≤ B) :
    (EdgeAugmenting.encWalkCode (EdgeAugmenting.code w)).length ≤
      2 * B + 1 + (incidenceList H).length * (6 * (incidenceList H).length + 3) := by
  have he : w.edges.length = 2 * w.steps.length := by
    simp [Walk.edges, Walk.edgesOf, List.length_flatMap, Nat.mul_comm]
  have hn := hw.2.length_le_of_subset (l₂ := incidenceList H) (fun o _ => mem_incidenceList o)
  have hsteps : w.steps.length ≤ (incidenceList H).length := by omega
  have hindex (o : Occurrence H) :
      (encNat (EdgeAugmenting.occurrenceIndex o)).length ≤ (incidenceList H).length := by
    have hi := EdgeAugmenting.occurrenceIndex_lt o
    simp only [encNat_apply, Nat.size_eq_bits_len]
    exact (Nat.size_le_self _).trans (by omega)
  simp only [EdgeAugmenting.encWalkCode_apply, EdgeAugmenting.encWalkCodeFields,
    EdgeAugmenting.code, length_encPair, length_encList, List.map_map, Function.comp_def]
  have hs : (w.steps.map fun s =>
      2 * (2 * (encNat (EdgeAugmenting.occurrenceIndex s.1)).length + 1 +
        (encNat (EdgeAugmenting.occurrenceIndex s.2)).length) + 1).sum ≤
      w.steps.length * (6 * (incidenceList H).length + 3) := by
    calc
      _ ≤ (w.steps.map fun _ => 6 * (incidenceList H).length + 3).sum := by
        apply List.sum_le_sum
        intro s _
        have ha := hindex s.1
        have hb := hindex s.2
        omega
      _ = _ := by simp [Nat.mul_comm]
  have hmul := Nat.mul_le_mul_right (6 * (incidenceList H).length + 3) hsteps
  omega

/-- Every actual descended occurrence buffer fits twice the original actual occurrence count. -/
theorem Chain.width_le (h : Chain F k G) (hF : EdgeInstance F) :
    (incidenceList G).length ≤ 2 * F.vars.length := by
  have he := congrArg List.length (occurrences_eq_map_incidenceList (F := G))
  simp only [List.length_map] at he
  rw [← he, CSP.length_occurrences]
  have hv : (G.map fun c => c.scope.length).sum = G.vars.length := by
    simp [vars, List.length_flatMap]
  rw [hv, (h.edge hF).length_vars_eq_two_mul_numVars]
  exact Nat.mul_le_mul_left 2 ((h.numVars_le hF).trans (List.toFinset_card_le _))

end Cslib.Complexity.CSP.EdgeSolver.Size
