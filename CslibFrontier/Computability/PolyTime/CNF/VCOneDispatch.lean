/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CNF.VCOneFrontend
public import CslibFrontier.Logics.Propositional.CNF.ExactOnePathPlan
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.List.Perm.Basic
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# Actual table-to-tagged-plan dispatch

Compose explicit local-table preprocessing with original-row binary elimination and the
side-CNF/path writer. The executable constructor accepts only the original framed table payload.
Declarations and local widths are unary, global scope columns and output literals are binary.
This is the representation convention of the table frontend for [ChenJiangZhu2027], Theorem 6.3.
-/

public section

namespace Cslib.Logic.PL.VCOne.BinaryFrontend

open Turing.MultiTapeTM

/-- The complete table constructor computes preprocessing, all direct/rank branches and queries. -/
@[expose] def compile (x : ℕ × List Table) : WeightedRow.BinaryPlan.Output :=
  ExactOne.BinaryPlan.compile (x.1, payload x)

/-- Polynomial binary resources for every construction branch, including query writing and the
binary encoding of direct answers. No rank, separator or runtime is supplied. -/
@[fun_prop] theorem compile_polytime : ComputableInPolyTime compile encTablePayload
    ExactOne.BinaryPlan.encOutput := by
  have hn : ComputableInPolyTime (fun x : ℕ × List Table => x.1)
      encTablePayload encUnary := by unfold encTablePayload; fun_prop
  exact ExactOne.BinaryPlan.compile_polytime.comp (hn.prod payload_polytime)

private theorem signedClause_relabel_perm {r w : ℕ} (S : Finset (Fin w))
    (p : Fin w → Bool) (scope : Fin w ↪ Fin r) :
    ((ExactOne.signedClause S p).relabel scope).Perm
      (ExactOne.signedClause (S.map scope) (Function.extend scope p (fun _ => false))) := by
  classical
  have hinj (q : Fin r → Bool) : Function.Injective (fun v : Fin r => (v, q v)) :=
    fun _ _ h => congrArg Prod.fst h
  have hlocal : Function.Injective (fun v : Fin w => (v, p v)) :=
    fun _ _ h => congrArg Prod.fst h
  apply (List.perm_ext_iff_of_nodup
    (((Finset.sort_nodup S (· ≤ ·)).map hlocal).map
      (scope.injective.prodMap Function.injective_id))
    ((Finset.sort_nodup _ (· ≤ ·)).map (hinj _))).mpr
  intro l
  simp only [List.mem_map, Finset.mem_sort]
  constructor
  · rintro ⟨a, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨scope v, Finset.mem_map.mpr ⟨v, hv, rfl⟩, by
      rw [scope.injective.extend_apply]; rfl⟩
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hv
    exact ⟨(i, p i), ⟨i, hi, rfl⟩, by rw [scope.injective.extend_apply]; rfl⟩

private theorem lift_clause {r : ℕ} {c : Clause ℕ}
    (hv : ∀ l ∈ c, l.1 < r) :
    ∃ d : Clause (Fin r), d.relabel Fin.val = c := by
  let d : Clause (Fin r) := c.attach.map fun l => (⟨l.val.1, hv l.val l.property⟩, l.val.2)
  refine ⟨d, ?_⟩
  simp only [d, Clause.relabel, List.map_map, Function.comp_def, Prod.map_apply, id_eq]
  simpa only [Prod.eta, List.map_id, id_eq] using (List.attach_map_val (l := c) (f := id))

/-- Every actual global equation, in its emitted order, is a finite signed distinct-column row.
This transports the local separator through the given scope embedding; global sorting is only
used in the mathematical presentation, never as execution advice. -/
theorem equation_presentation {r w : ℕ} (R : Finset (Fin w → Bool))
    (y : Fin w → Bool) (scope : Fin w ↪ Fin r) :
    let c := scopeClause (List.ofFn fun i => (scope i).val)
      (BinarySeparator.equation (w, BinaryClosure.rows R) (List.ofFn y))
    ∃ d : Clause (Fin r), d.relabel Fin.val = c ∧
      ∃ S : Finset (Fin r), ∃ p : Fin r → Bool, d.Perm (ExactOne.signedClause S p) := by
  classical
  let S := greedyScope R y
  let p : Fin w → Bool := fun i => !y i
  let D := (ExactOne.signedClause S p).relabel scope
  let c := scopeClause (List.ofFn fun i => (scope i).val)
    (BinarySeparator.equation (w, BinaryClosure.rows R) (List.ofFn y))
  have hp : c.Perm (D.relabel Fin.val) := by
    have h := (BinarySeparator.equation_rows_perm R y).map
      (Prod.map (fun i => (List.ofFn fun j => (scope j).val).getD i 0) id)
    simpa only [c, scopeClause, D, ExactOne.signedClause, S, p, Clause.relabel,
      List.map_map, Function.comp_def, Prod.map_apply, id_eq, List.getD_ofFn] using h
  have hv (l : Literal ℕ) (hl : l ∈ c) : l.1 < r := by
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp (hp.mem_iff.mp hl)
    exact a.1.isLt
  obtain ⟨d, hd⟩ := lift_clause hv
  refine ⟨d, hd, S.map scope, Function.extend scope p (fun _ => false), ?_⟩
  have hpd : (d.relabel Fin.val).Perm (D.relabel Fin.val) := by rw [hd]; exact hp
  have hdD : d.Perm D := (List.map_perm_map_iff
    (Fin.val_injective.prodMap Function.injective_id)).mp hpd
  exact hdD.trans (signedClause_relabel_perm S p scope)

private theorem payload_row_presentation {r m : ℕ} (w : Fin m → ℕ)
    (scope : (i : Fin m) → Fin (w i) ↪ Fin r)
    (R : (i : Fin m) → Finset (Fin (w i) → Bool)) (hR : ∀ i, DimensionOne (R i))
    (c : Clause ℕ) (hc : c ∈ (payload (tablePayload w scope R)).2) :
    ∃ d : Clause (Fin r), d.relabel Fin.val = c ∧
      ∃ S : Finset (Fin r), ∃ p : Fin r → Bool, d.Perm (ExactOne.signedClause S p) := by
  classical
  simp only [payload, tablePayload, List.flatMap_map, List.mem_flatMap,
    List.mem_finRange, true_and] at hc
  obtain ⟨i, hc⟩ := hc
  have hcols : (List.finRange (w i)).map (fun j => (scope i j).val) =
      List.ofFn (fun j => (scope i j).val) := by
    simp only [List.finRange, List.map_ofFn, Function.comp_def]
  simp only [compileTable, hcols, List.mem_map, BinarySeparator.equations] at hc
  obtain ⟨a, ⟨y, hy, rfl⟩, rfl⟩ := hc
  have hy' : y ∈ (closure (R i) \ R i).image List.ofFn := by
    rw [← BinaryClosure.missing_rows (R i) (hR i)]
    exact List.mem_toFinset.mpr hy
  obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hy'
  exact equation_presentation (R i) z (scope i)

private theorem lift_equations {r : ℕ} (E : CNF ℕ)
    (h : ∀ c ∈ E, ∃ d : Clause (Fin r), d.relabel Fin.val = c ∧
      ∃ S : Finset (Fin r), ∃ p : Fin r → Bool, d.Perm (ExactOne.signedClause S p)) :
    ∃ F : CNF (Fin r), CNF.relabel Fin.val F = E ∧
      ∀ c ∈ F, ∃ S : Finset (Fin r), ∃ p : Fin r → Bool,
        c.Perm (ExactOne.signedClause S p) := by
  induction E with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons c E ih =>
    obtain ⟨d, hd, hdp⟩ := h c (List.mem_cons_self)
    obtain ⟨F, hF, hFp⟩ := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
    refine ⟨d :: F, by simp only [CNF.relabel, List.map_cons] at hF ⊢; rw [hd, hF], ?_⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hdp
    · exact hFp a ha

open Classical in
/-- The original table payload admits a finite signed-row presentation, including all overlaps
and degenerate tables. The witnesses are used only to prove correctness of the actual raw writer. -/
theorem payload_presentation {r m : ℕ} (w : Fin m → ℕ)
    (scope : (i : Fin m) → Fin (w i) ↪ Fin r)
    (R : (i : Fin m) → Finset (Fin (w i) → Bool)) (hR : ∀ i, DimensionOne (R i)) :
    ∃ E : CNF (Fin r), CNF.relabel Fin.val E = (payload (tablePayload w scope R)).2 ∧
      ∃ S : Fin E.length → Finset (Fin r), ∃ p : Fin E.length → Fin r → Bool,
        ∀ j, (E.get j).Perm (ExactOne.signedClause (S j) (p j)) := by
  obtain ⟨E, he, hp⟩ := lift_equations _ (payload_row_presentation w scope R hR)
  choose S p h using (fun j : Fin E.length => hp (E.get j) (E.get_mem j))
  exact ⟨E, he, S, p, h⟩

open Classical in
/-- The actual executable table dispatcher preserves the original count on every declared bit.
All tables have local VC dimension at most one and injective individual scopes; inter-table
scopes may overlap arbitrarily, and unused declared bits keep their assignment multiplicity. -/
theorem compile_count {r m : ℕ} (w : Fin m → ℕ)
    (scope : (i : Fin m) → Fin (w i) ↪ Fin r)
    (R : (i : Fin m) → Finset (Fin (w i) → Bool)) (hR : ∀ i, DimensionOne (R i)) :
    WeightedRow.BinaryPlan.Output.count (compile (tablePayload w scope R)) =
      Fintype.card {x : Fin r → Bool // Satisfies w scope R x} := by
  obtain ⟨E, hE, S, p, hp⟩ := payload_presentation w scope R hR
  let B : CNF (Fin r) := (listedSide w scope R).dedup
  have hB : B.relabel Fin.val = (payload (tablePayload w scope R)).1 :=
    (payload_side w scope R).symm
  have hc := ExactOne.BinaryPlan.compile_count_of_perm B E S p hp
  rw [ExactOne.BinaryPlan.sourceCount_of_perm B E S p hp] at hc
  change WeightedRow.BinaryPlan.Output.count
    (ExactOne.BinaryPlan.compile (r, payload (tablePayload w scope R))) = _
  have hpair : payload (tablePayload w scope R) =
      (B.relabel Fin.val, E.relabel Fin.val) := by rw [hB, hE]
  rw [hpair, hc, payload_count w scope R hR]
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro σ
  have he : (Function.extend Fin.val σ (fun _ => false)) ∘ Fin.val = σ := by
    funext i
    exact Fin.val_injective.extend_apply _ _ _
  dsimp only
  rw [← hB, ← hE, CNF.eval_relabel, CNF.evalOne_relabel, he]

/-- The table writer and all actual branches retain the two-query declaration/width/index budget. -/
theorem compile_withinBudget {r m : ℕ} (w : Fin m → ℕ)
    (scope : (i : Fin m) → Fin (w i) ↪ Fin r)
    (R : (i : Fin m) → Finset (Fin (w i) → Bool)) (hR : ∀ i, DimensionOne (R i)) :
    WeightedRow.BinaryPlan.WithinBudget r 1 (compile (tablePayload w scope R)) := by
  classical
  obtain ⟨E, hE, S, p, hp⟩ := payload_presentation w scope R hR
  let B : CNF (Fin r) := (listedSide w scope R).dedup
  have hB : B.relabel Fin.val = (payload (tablePayload w scope R)).1 :=
    (payload_side w scope R).symm
  have hb : ∀ c ∈ B, c.length ≤ 2 := by
    intro c hc
    obtain ⟨i, _, hc⟩ := List.mem_flatMap.mp (List.mem_dedup.mp hc)
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    simpa only [Clause.relabel, List.length_map] using binary_width (R i) a ha
  have he : ∀ c ∈ E, c.length ≤ r := by
    intro c hc
    obtain ⟨i, rfl⟩ := List.get_of_mem hc
    rw [(hp i).length_eq]
    simpa only [ExactOne.signedClause, List.length_map, Finset.length_sort,
      Fintype.card_fin] using (S i).card_le_univ
  have hpair : payload (tablePayload w scope R) =
      (B.relabel Fin.val, E.relabel Fin.val) := by rw [hB, hE]
  change WeightedRow.BinaryPlan.WithinBudget r 1
    (ExactOne.BinaryPlan.compile (r, payload (tablePayload w scope R)))
  rw [hpair]
  exact ExactOne.BinaryPlan.compile_withinBudget B E hb he

end Cslib.Logic.PL.VCOne.BinaryFrontend
