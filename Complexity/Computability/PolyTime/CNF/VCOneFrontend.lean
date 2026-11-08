/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.PolyTime.CNF.VCOneSeparator
public import Complexity.Logics.Propositional.CNF.VCOneElimination
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Foundations.Data.List.Lookup
import Mathlib.Data.List.OfFn

/-!
# Executable polynomial table representation and overlapping-scope writing

Construct unary/binary restrictions and the actual signed separators from explicit local tables,
then align their columns using the original scope lists. This is the local representation of
[ChenJiangZhu2027], Theorem 1.3, and the preprocessing part of Theorem 6.3 (PDF pp. 18–21).
Declared counts and local widths are unary; scope columns are binary and rows are literal bits.
No disjoint-scope assumption is made. Polynomial resources charge all closure/deletion scans,
literal writing, scope lookup and global deduplication. The global rank-to-two-query counting
resource composition remains a separate obligation; these constructors are not that endpoint.
## Main results

* `representation`: the actual local writers satisfy the source representation theorem.
* `payload_polytime`, `payload_tables`, `payload_count`: efficient shared-column writing and exact
  original constraint/count correspondence, including arbitrary overlap and unused bits.
* `payload_side_length`: the globally deduplicated quadratic side-clause bound.
* `basis_polytime`, `consistent_polytime`: construction through actual binary backend diagnostics.

-/

public section

namespace Cslib.Logic.PL.VCOne.BinaryFrontend

open Turing.MultiTapeTM

/-- Local clauses store unary local positions, rather than arbitrary global indices. -/
@[expose] def encLocalCNF : CNF ℕ ↪ List Bool := encList (encList (encPair encUnary encBool))

/-- Exactly the local literal clauseUniverse, generated from the unary declared width. -/
@[expose] def literals (n : ℕ) : List (Literal ℕ) :=
  (List.range n).flatMap fun i => [(i, false), (i, true)]

/-- The syntax clauseUniverse is quadratic, not an enumeration of Boolean assignments. -/
@[expose] def clauseUniverse (n : ℕ) : CNF ℕ :=
  [[]] ++ (literals n).map (fun l => [l]) ++
    (literals n).flatMap fun l => (literals n).map fun k => [l, k]

/-- Keep precisely those unary/binary restrictions satisfied by all explicit allowed rows. -/
@[expose] def side (p : BinaryClosure.Input) : CNF ℕ :=
  ((clauseUniverse p.1).filter fun c => p.2.all fun x =>
    c.any fun l => x.getD l.1 false == l.2).dedup

private theorem literals_polytime : ComputableInPolyTime literals encUnary
    (encList (encPair encUnary encBool)) := by
  unfold literals
  apply ComputableInPolyTime.flatMapWithInput (by fun_prop)
  fun_prop

private theorem universe_polytime : ComputableInPolyTime clauseUniverse encUnary encLocalCNF := by
  unfold clauseUniverse encLocalCNF
  apply ComputableInPolyTime.listAppend'
  · apply ComputableInPolyTime.listAppend' (ComputableInPolyTime.const _)
    exact ComputableInPolyTime.mapWithInput literals_polytime (by fun_prop)
  · apply ComputableInPolyTime.flatMapWithInput literals_polytime
    exact ComputableInPolyTime.mapWithInput
      (literals_polytime.comp (by fun_prop)) (by fun_prop)

/-- Actual side-clause generation scans the input tables, including the empty-table case. -/
@[fun_prop] theorem side_polytime :
    ComputableInPolyTime side BinaryClosure.encInput encLocalCNF := by
  unfold side encLocalCNF
  apply (Cslib.dedup_polytime (encList (encPair encUnary encBool)) []).comp
  apply ComputableInPolyTime.filterWithInput
    (universe_polytime.comp (by unfold BinaryClosure.encInput; fun_prop))
  apply ComputableInPolyTime.allWithInput (by unfold BinaryClosure.encInput; fun_prop)
  apply ComputableInPolyTime.anyWithInput (by fun_prop)
  fun_prop

private theorem universe_fin (n : ℕ) :
    clauseUniverse n = (ExactOne.binaryUniverse (V := Fin n)).relabel Fin.val := by
  have hl : literals n = (ExactOne.literals (V := Fin n)).map (Prod.map Fin.val id) := by
    have hm : (List.finRange n).map Fin.val = List.range n := by simp
    unfold literals ExactOne.literals
    rw [Fin.sort_univ, ← hm]
    simp only [List.map_flatMap, List.flatMap_map, List.map_cons, List.map_nil,
      Prod.map_apply, id_eq]
  simp only [clauseUniverse, ExactOne.binaryUniverse, CNF.relabel, List.map_append,
    List.map_map, List.map_flatMap, List.flatMap_map, hl]
  rfl

/-- The actual side writer emits exactly the reviewed binary restriction syntax,
up to relabeling. -/
theorem side_rows {n : ℕ} (R : Finset (Fin n → Bool)) :
    side (n, BinaryClosure.rows R) = (binary R).relabel Fin.val := by
  simp only [side, universe_fin, CNF.relabel, List.filter_map]
  have he : (fun c : Clause (Fin n) =>
      (BinaryClosure.rows R).all fun x =>
        (c.map (Prod.map Fin.val id)).any fun l => x.getD l.1 false == l.2) =
      (fun c => @decide (∀ x ∈ R, c.eval x = true) Finset.decidableDforallFinset) := by
    funext c
    apply Bool.eq_iff_iff.mpr
    rw [@decide_eq_true_eq _ Finset.decidableDforallFinset]
    simp [BinaryClosure.rows, List.all_eq_true, List.any_map, Clause.eval, Literal.eval]
  simp only [Function.comp_def, Clause.relabel]
  rw [he]
  rw [binary_eq_scanBinary]
  simp only [scanBinary]
  exact List.dedup_map_of_injective
    (List.map_injective_iff.mpr (Fin.val_injective.prodMap Function.injective_id)) _

/-- The actual local 2-CNF has a quadratic clause bound, independent of table size. -/
theorem side_length {n : ℕ} (R : Finset (Fin n → Bool)) :
    (side (n, BinaryClosure.rows R)).length ≤ 1 + 2 * n + 4 * n ^ 2 := by
  rw [side_rows]
  simpa only [CNF.relabel, List.length_map, Fintype.card_fin] using binary_length R

/-- All actual local side clauses have width at most two. -/
theorem side_width {n : ℕ} (R : Finset (Fin n → Bool)) (c : Clause ℕ)
    (hc : c ∈ side (n, BinaryClosure.rows R)) : c.length ≤ 2 := by
  rw [side_rows] at hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  simpa only [Clause.relabel, List.length_map] using binary_width R d hd

/-- Every unwanted tuple supplies its actual equation; no other equation is written. -/
theorem equations_eval {n : ℕ} (R : Finset (Fin n → Bool)) (hR : DimensionOne R)
    (σ : ℕ → Bool) :
    (BinarySeparator.equations (n, BinaryClosure.rows R)).evalOne σ = true ↔
      ∀ y : ↥(closure R \ R),
        ExactOne.Holds (separatorScope R y) (fun i => !y.val i) (σ ∘ Fin.val) := by
  rw [CNF.evalOne_eq_true_iff]
  simp only [BinarySeparator.equations, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  constructor
  · intro h y
    have hy : List.ofFn y.val ∈ BinaryClosure.missing (n, BinaryClosure.rows R) := by
      rw [← List.mem_toFinset, BinaryClosure.missing_rows R hR]
      exact Finset.mem_image.mpr ⟨y.val, y.property, rfl⟩
    exact (BinarySeparator.equation_rows_eval R y.val σ).mp (h _ hy)
  · intro h row hr
    have hm : row ∈ (closure R \ R).image List.ofFn := by
      rw [← BinaryClosure.missing_rows R hR]
      exact List.mem_toFinset.mpr hr
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hm
    exact (BinarySeparator.equation_rows_eval R y σ).mpr (h ⟨y, hy⟩)

/-- Pointwise Theorem 1.3 for the actual polynomial-time writers on the original variables.
The VC-one promise concerns the input relation only; every output is computed from its rows. -/
theorem representation {n : ℕ} (R : Finset (Fin n → Bool)) (hR : DimensionOne R)
    (σ : ℕ → Bool) :
    σ ∘ Fin.val ∈ R ↔
      (side (n, BinaryClosure.rows R)).eval σ = true ∧
        (BinarySeparator.equations (n, BinaryClosure.rows R)).evalOne σ = true := by
  rw [side_rows, CNF.eval_relabel, equations_eval R hR]
  exact representation_iff R hR (σ ∘ Fin.val)

/-- One raw table: unary width, explicit Boolean rows and binary global scope columns. -/
abbrev Table := ℕ × List (List Bool) × List ℕ

/-- The existing table payload encoding, restricted to one actual table. -/
@[expose] def encTable : Table ↪ List Bool :=
  encPair encUnary (encPair (encList encBits) (encList encNat))

/-- Align local positions to global columns without adding variables or changing polarities. -/
@[expose] def scopeClause (columns : List ℕ) (c : Clause ℕ) : Clause ℕ :=
  c.relabel (fun i => columns.getD i 0)

/-- Write the side clauses and equations of one table in its original global columns. -/
@[expose] def compileTable (table : Table) : CNF ℕ × CNF ℕ :=
  let (w, rs, columns) := table
  ((side (w, rs)).map (scopeClause columns),
    (BinarySeparator.equations (w, rs)).map (scopeClause columns))

private theorem scopeClause_polytime : ComputableInPolyTime
    (fun p : List ℕ × Clause ℕ => scopeClause p.1 p.2)
    (encPair (encList encNat) (encList (encPair encUnary encBool)))
    (encList (encPair encNat encBool)) := by
  unfold scopeClause Clause.relabel
  apply ComputableInPolyTime.mapWithInput (by fun_prop)
  change ComputableInPolyTime
    (fun p : (List ℕ × Clause ℕ) × (ℕ × Bool) => (p.1.1.getD p.2.1 0, p.2.2)) _ _
  fun_prop

private theorem local_polytime : ComputableInPolyTime compileTable encTable
    (encPair encSignedCNF encSignedCNF) := by
  have ht : ComputableInPolyTime (fun t : Table => (t.1, t.2.1))
      encTable BinaryClosure.encInput := by unfold encTable BinaryClosure.encInput; fun_prop
  have hctx : ComputableInPolyTime
      (fun p : Table × Clause ℕ => (p.1.2.2, p.2))
      (encPair encTable (encList (encPair encUnary encBool)))
      (encPair (encList encNat) (encList (encPair encUnary encBool))) := by
    unfold encTable; fun_prop
  unfold compileTable
  exact (ComputableInPolyTime.mapWithInput (side_polytime.comp ht)
    (scopeClause_polytime.comp hctx)).prod
      (ComputableInPolyTime.mapWithInput (BinarySeparator.equations_polytime.comp ht)
        (scopeClause_polytime.comp hctx))

/-- Compile every input table independently, align overlapping scopes, and deduplicate only the
side formula globally. Distinct separating equations keep their table origins and signs. -/
@[expose] def payload (x : ℕ × List Table) : CNF ℕ × CNF ℕ :=
  (((x.2.flatMap fun t => (compileTable t).1)).dedup, x.2.flatMap fun t => (compileTable t).2)

/-- Actual polynomial resources for the complete table-to-side-and-equations constructor. -/
@[fun_prop] theorem payload_polytime : ComputableInPolyTime payload encTablePayload
    (encPair encSignedCNF encSignedCNF) := by
  have hl : ComputableInPolyTime (fun x : ℕ × List Table => x.2)
      encTablePayload (encList encTable) := by unfold encTablePayload encTable; fun_prop
  have hcs := (ComputableInPolyTime.fst encSignedCNF encSignedCNF).comp local_polytime
  have hce := (ComputableInPolyTime.snd encSignedCNF encSignedCNF).comp local_polytime
  have hs : ComputableInPolyTime
      (fun x : ℕ × List Table => x.2.flatMap fun t => (compileTable t).1)
      encTablePayload encSignedCNF := by
    unfold encSignedCNF at hcs ⊢
    exact ComputableInPolyTime.flatMapWithInput hl
      (hcs.comp (ComputableInPolyTime.snd encTablePayload encTable))
  have he : ComputableInPolyTime
      (fun x : ℕ × List Table => x.2.flatMap fun t => (compileTable t).2)
      encTablePayload encSignedCNF := by
    unfold encSignedCNF at hce ⊢
    exact ComputableInPolyTime.flatMapWithInput hl
      (hce.comp (ComputableInPolyTime.snd encTablePayload encTable))
  unfold payload
  exact ((Cslib.dedup_polytime (encList (encPair encNat encBool)) []).comp hs).prod he

/-- Local shared-column writing preserves the original local-table predicate pointwise. -/
theorem local_rows {r w : ℕ} (R : Finset (Fin w → Bool)) (hR : DimensionOne R)
    (scope : Fin w ↪ Fin r) (σ : ℕ → Bool) :
    (fun i => σ (scope i).val) ∈ R ↔
      (compileTable (w, BinaryClosure.rows R, List.ofFn fun i => (scope i).val)).1.eval σ = true ∧
        (compileTable (w, BinaryClosure.rows R, List.ofFn fun i =>
          (scope i).val)).2.evalOne σ = true := by
  have he : ∀ B : CNF ℕ,
      B.map (scopeClause (List.ofFn fun i => (scope i).val)) =
        B.relabel (fun j => (List.ofFn fun i => (scope i).val).getD j 0) := fun _ => rfl
  simp only [compileTable, he, CNF.eval_relabel, CNF.evalOne_relabel]
  simpa only [Function.comp_def, List.getD_ofFn] using
    representation R hR (σ ∘ fun j => (List.ofFn fun i => (scope i).val).getD j 0)

/-- Pointwise global table correspondence without any restriction on inter-table overlap.
Only each original scope is injective; table count and arities are arbitrary. -/
theorem payload_tables {r m : ℕ} (w : Fin m → ℕ)
    (scope : (i : Fin m) → Fin (w i) ↪ Fin r)
    (R : (i : Fin m) → Finset (Fin (w i) → Bool)) (hR : ∀ i, DimensionOne (R i))
    (σ : ℕ → Bool) :
    (∀ i, (fun j => σ (scope i j).val) ∈ R i) ↔
      (payload (tablePayload w scope R)).1.eval σ = true ∧
        (payload (tablePayload w scope R)).2.evalOne σ = true := by
  have heach (i : Fin m) := local_rows (R i) (hR i) (scope i) σ
  have hmap (i : Fin m) :
      (List.finRange (w i)).map (fun j => (scope i j).val) =
        List.ofFn (fun j => (scope i j).val) := by
        simp only [List.finRange, List.map_ofFn, Function.comp_def]
  have hd (B : CNF ℕ) : CNF.eval σ B.dedup = B.eval σ := by
    apply Bool.eq_iff_iff.mpr
    simp [CNF.eval_eq_true_iff]
  simp only [payload, tablePayload, List.flatMap_map,
    hmap, hd, CNF.eval_flatMap_eq_true_iff, CNF.evalOne_flatMap_eq_true_iff,
    List.mem_finRange, forall_true_left]
  constructor
  · intro h
    exact ⟨fun i => (heach i).mp (h i) |>.1, fun i => (heach i).mp (h i) |>.2⟩
  · rintro ⟨hs, he⟩ i
    exact (heach i).mpr ⟨hs i, he i⟩

open Classical in
/-- The actual side/equation payload preserves the count on all declared original bits, including
unused bits. The extension only gives a meaning to natural-number literal labels in the statement;
it is not auxiliary input to the constructor or enumeration of the declared cube. -/
theorem payload_count {r m : ℕ} (w : Fin m → ℕ)
    (scope : (i : Fin m) → Fin (w i) ↪ Fin r)
    (R : (i : Fin m) → Finset (Fin (w i) → Bool)) (hR : ∀ i, DimensionOne (R i)) :
    Fintype.card {x : Fin r → Bool // Satisfies w scope R x} =
      Fintype.card {x : Fin r → Bool //
        let σ := Function.extend Fin.val x (fun _ => false)
        (payload (tablePayload w scope R)).1.eval σ = true ∧
          (payload (tablePayload w scope R)).2.evalOne σ = true} := by
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro x
  let σ : ℕ → Bool := Function.extend Fin.val x (fun _ => false)
  have he (i : Fin m) : (fun j => σ (scope i j).val) = x ∘ scope i := by
    funext j
    exact Fin.val_injective.extend_apply _ _ _
  simpa only [he, Satisfies] using payload_tables w scope R hR σ

private theorem local_side_rows {r w : ℕ} (R : Finset (Fin w → Bool))
    (scope : Fin w ↪ Fin r) :
    (compileTable (w, BinaryClosure.rows R, List.ofFn fun i => (scope i).val)).1 =
      (binary R).relabel (fun i => (scope i).val) := by
  simp only [compileTable, side_rows, CNF.relabel, scopeClause, List.map_map,
    Clause.relabel, Function.comp_def]
  congr 1
  funext c
  apply List.map_congr_left
  intro l _
  rcases l with ⟨i, b⟩
  simp only [Prod.map_apply, id_eq, List.getD_ofFn]

/-- Global side deduplication produces exactly the reviewed shared-column formula, up to
bounded-index erasure. The equality does not assume disjoint scopes or the VC-one promise. -/
theorem payload_side {r m : ℕ} (w : Fin m → ℕ)
    (scope : (i : Fin m) → Fin (w i) ↪ Fin r)
    (R : (i : Fin m) → Finset (Fin (w i) → Bool)) :
    (payload (tablePayload w scope R)).1 = CNF.relabel Fin.val (listedSide w scope R).dedup := by
  have hmap (i : Fin m) : (List.finRange (w i)).map (fun j => (scope i j).val) =
      List.ofFn (fun j => (scope i j).val) := by
    simp only [List.finRange, List.map_ofFn, Function.comp_def]
  simp only [payload, tablePayload, List.flatMap_map, hmap]
  change ((List.finRange m).flatMap fun i => (compileTable
    (w i, BinaryClosure.rows (R i), List.ofFn fun j => (scope i j).val)).1).dedup = _
  simp only [local_side_rows]
  have hr : (listedSide w scope R).relabel Fin.val =
      (List.finRange m).flatMap fun i => (binary (R i)).relabel (fun j => (scope i j).val) := by
    simp only [listedSide, CNF.relabel, List.map_flatMap, List.map_map, Function.comp_def]
    congr 1
    funext i
    congr 1
    funext c
    simp only [Clause.relabel, List.map_map, Function.comp_def]
    rfl
  rw [← hr]
  exact List.dedup_map_of_injective
    (List.map_injective_iff.mpr (Fin.val_injective.prodMap Function.injective_id)) _

/-- Actual global side output has the source quadratic budget even with arbitrarily many tables. -/
theorem payload_side_length {r m : ℕ} (w : Fin m → ℕ)
    (scope : (i : Fin m) → Fin (w i) ↪ Fin r)
    (R : (i : Fin m) → Finset (Fin (w i) → Bool)) :
    (payload (tablePayload w scope R)).1.length ≤ 1 + 2 * r + 4 * r ^ 2 := by
  rw [payload_side]
  have hw (c : Clause (Fin r)) (hc : c ∈ listedSide w scope R) : c.length ≤ 2 := by
    obtain ⟨i, _, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    simpa only [Clause.relabel, List.length_map] using binary_width (R i) d hd
  simpa only [CNF.relabel, List.length_map, Fintype.card_fin] using
    ExactOne.dedup_binary_length _ hw

/-- Execute actual binary rectangular consistency on the derived global equations. This includes
closure enumeration, separator extraction, overlap alignment and integer matrix/RHS writing. -/
@[expose] def consistent (x : ℕ × List Table) : Bool :=
  payloadConsistent x.1 (payload x).2

/-- A composed machine certificate for table construction through binary consistency diagnostics.
This is not a certificate for the later two-query/direct-answer table dispatcher. -/
@[fun_prop] theorem consistent_polytime : ComputableInPolyTime consistent encTablePayload
    encBool := by
  unfold consistent
  exact payloadConsistent_polytime.comp ((show ComputableInPolyTime
    (fun x : ℕ × List Table => x.1) encTablePayload encUnary from by
      unfold encTablePayload; fun_prop).prod
        ((ComputableInPolyTime.snd _ _).comp payload_polytime))

/-- Compute original equation indices using the actual derived integer matrix. -/
@[expose] def basis (x : ℕ × List Table) : List ℕ :=
  Cslib.LinearSystem.gramRowBasis x.1 (payloadRows x.1 (payload x).2)

/-- The complete table-to-basis computation has polynomial binary resources,
without basis advice. -/
@[fun_prop] theorem basis_polytime : ComputableInPolyTime basis encTablePayload
    (encList encUnary) := by
  have hn : ComputableInPolyTime (fun x : ℕ × List Table => x.1)
      encTablePayload encUnary := by unfold encTablePayload; fun_prop
  have he : ComputableInPolyTime (fun x : ℕ × List Table => (payload x).2)
      encTablePayload encSignedCNF :=
    (ComputableInPolyTime.snd encSignedCNF encSignedCNF).comp payload_polytime
  have hA : ComputableInPolyTime
      (fun x : ℕ × List Table => payloadRows x.1 (payload x).2)
      encTablePayload (encList (encList encIntBin)) :=
    payloadRows_polytime.comp (hn.prod he)
  have hb := Cslib.LinearSystem.gramRowBasis_polytime.comp (hn.prod hA)
  exact hb.of_enc_eq fun _ => rfl

/-- Every actual selected index refers to an equation written by this constructor. -/
theorem basis_mem (x : ℕ × List Table) (i : ℕ) (hi : i ∈ basis x) :
    i < (payload x).2.length := by
  have h := Cslib.LinearSystem.gramRowBasis_mem x.1 (payloadRows x.1 (payload x).2) i hi
  simpa only [payloadRows, List.length_map] using h

/-- Computed original-row selection never exceeds the original declared dimension. -/
theorem basis_length (x : ℕ × List Table) : (basis x).length ≤ x.1 :=
  Cslib.LinearSystem.gramRowBasis_length _ _

end Cslib.Logic.PL.VCOne.BinaryFrontend
