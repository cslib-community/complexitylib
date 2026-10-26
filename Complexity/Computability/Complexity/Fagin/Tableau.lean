/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Fagin.Tableau.Defs
public import Complexity.Computability.Complexity.Fagin.Tableau.Semantics

/-!
# Existential second-order tableau sentence on `Fin B`

Given a deterministic multi-tape Turing machine `tm : MultiTapeTM m Bool State` (`[Fintype State]
[DecidableEq State]`) and a language `L₀` equipped with a strict linear order `lt` on `Fin B` and
unary relations `uLenRel` and `uBitRel` describing an input prefix `u : List Bool`, this file
constructs an existential second-order sentence `FO.tableauESOSentence lt uLenRel uBitRel tm` over
`L₀`.

On `Fin B` with `u.length + 1 < B`, `FO.tableauESOSentence lt uLenRel uBitRel tm` is realized if
and only if there exists a certificate word `w : List Bool` with `u.length + w.length + 1 < B` such
that `tm`, started on `u ++ w`, halts within `B - 1` steps with output `[true]` — equivalently,
by `Cslib.Complexity.CookLevin.tableau_satisfiable_iff`, if and only if
`CookLevin.tableau tm u L (B - 1)` is satisfiable for some `L` with `u.length + L + 1 < B`.

The relation-symbol bundle `FO.TableauRels` and component first-order formulas are defined in
`Complexity.Computability.Complexity.Fagin.Tableau.Defs`, and the configuration-agreement predicate
(`FO.TableauRels.AgreesAt`) and realization equivalences are proved in
`Complexity.Computability.Complexity.Fagin.Tableau.Semantics`; both are re-exported here.

## Main definitions

* `Cslib.Logic.FO.tableauRels`, `Cslib.Logic.FO.tableauMatrix`: the canonical relation-symbol
  bundle in the matrix language and the first-order matrix of the sentence.
* `Cslib.Logic.FO.tableauESOSentence`: the existential second-order sentence encoding an accepting
  computation of `tm` on `u ++ w` within `B - 1` steps.
* `Cslib.Logic.Vocabulary.tableauESOSentence`: specialization to
  `v.powerLanguage.sum v.inputVarLanguage`.

## Main results

* `Cslib.Logic.FO.realize_tableauESOSentence`: on `Fin B`, `tableauESOSentence` holds iff some
  certificate `w` with `u.length + w.length + 1 < B` is accepted within `B - 1` steps.
* `Cslib.Logic.Vocabulary.realize_tableauESOSentence`: on `Fin B`, `v.tableauESOSentence tm`
  holds iff `CookLevin.tableau tm u L (B - 1)` is satisfiable for some `L` with
  `u.length + L + 1 < B`.

## References

* [R. Fagin, *Generalized first-order spectra and polynomial-time recognizable sets*][Fagin1974]
* [N. Immerman, *Descriptive Complexity*][Immerman1999]
* [C. H. Papadimitriou, *Computational Complexity*][Papadimitriou94], Theorem 8.3
-/

@[expose] public section

universe u v

namespace Cslib.Logic

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure
open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Feature
open Cslib.Complexity

namespace FO

/-! ### Full ESO tableau sentence -/

section TableauESO

variable {L₀ : Language.{0, 0}} (lt : L₀.Relations 2) (uLenRel uBitRel : L₀.Relations 1)
  {m : ℕ} {State : Type} [Fintype State] [DecidableEq State]
  (tm : MultiTapeTM m Bool State)

/-- The language of the first-order matrix of `tableauESOSentence`. -/
abbrev tableauMatrixLanguage (m : ℕ) (State : Type) : Language.{0, 0} :=
  L₀.sum (ESO.varLanguage (arity := tableauArity m State))

/-- The canonical `TableauRels` bundle in `tableauMatrixLanguage`. -/
def tableauRels : TableauRels (tableauMatrixLanguage (L₀ := L₀) m State) m State where
  lt := Sum.inl lt
  uLen := Sum.inl uLenRel
  uBit := Sum.inl uBitRel
  endPos := Sum.inr ⟨.inl (.inl ()), rfl⟩
  certBit := Sum.inr ⟨.inl (.inr (.inl ())), rfl⟩
  state q := Sum.inr ⟨.inl (.inr (.inr (.inl q))), rfl⟩
  out o := Sum.inr ⟨.inl (.inr (.inr (.inr o))), rfl⟩
  inPos := Sum.inr ⟨.inr (.inl ()), rfl⟩
  headPos i := Sum.inr ⟨.inr (.inr (.inl i)), rfl⟩
  headNeg i := Sum.inr ⟨.inr (.inr (.inr (.inl i))), rfl⟩
  cellPos i s := Sum.inr ⟨.inr (.inr (.inr (.inr (.inl (i, s))))), rfl⟩
  cellNeg i s := Sum.inr ⟨.inr (.inr (.inr (.inr (.inr (i, s))))), rfl⟩

/-- The first-order matrix of `tableauESOSentence`. -/
noncomputable def tableauMatrix : (tableauMatrixLanguage (L₀ := L₀) m State).Sentence :=
  let r := tableauRels (m := m) (State := State) lt uLenRel uBitRel
  endPosSentence r ⊓ initSentence r tm ⊓ stepSentence r tm ⊓ acceptSentence r

/-- The existential second-order sentence asserting that `tm`, started on `u ++ w` for some
certificate `w` with `u.length + w.length + 1 < B`, halts within `B - 1` steps with output
`[true]`. -/
noncomputable def tableauESOSentence : ESO.Sentence L₀ where
  Var := TableauVar m State
  arity := tableauArity m State
  matrix := tableauMatrix lt uLenRel uBitRel tm

omit [Fintype State] [DecidableEq State] in
private theorem exists_certWord_of_realize_endPosSentence {L' : Language.{0, 0}}
    {r : TableauRels L' m State} {B : ℕ} [L'.Structure (Fin B)]
    (hlt : ∀ x : Fin 2 → Fin B, RelMap r.lt x ↔ x 0 < x 1)
    {u : List Bool} (huLen : ∀ z : Fin B, RelMap r.uLen ![z] ↔ (z : ℕ) = u.length)
    (hendSent : (endPosSentence r).Realize (Fin B)) :
    ∃ w : List Bool, u.length + w.length + 1 < B ∧
      (∀ z : Fin B, RelMap r.endPos ![z] ↔ (z : ℕ) = u.length + w.length) ∧
      (∀ j : Fin B, u.length < (j : ℕ) → (j : ℕ) ≤ u.length + w.length →
        (RelMap r.certBit ![j] ↔ w[(j : ℕ) - 1 - u.length]? = some true)) := by
  classical
  obtain ⟨e, hle_e, heB, hend⟩ := exists_of_realize_endPosSentence hlt huLen hendSent
  let L := (e : ℕ) - u.length
  have he_eq : u.length + L = (e : ℕ) := by omega
  let w : List Bool := (List.range L).map fun k =>
    if hk : u.length + 1 + k < B then
      decide (RelMap r.certBit ![(⟨u.length + 1 + k, hk⟩ : Fin B)])
    else false
  have hw_len : w.length = L := by simp [w]
  refine ⟨w, by omega, fun z => by rw [hend z, hw_len, he_eq], fun j hgt hle => ?_⟩
  have hk_lt : (j : ℕ) - 1 - u.length < L := by omega
  have hj_eq : u.length + 1 + ((j : ℕ) - 1 - u.length) = (j : ℕ) := by omega
  have hjB : u.length + 1 + ((j : ℕ) - 1 - u.length) < B := by omega
  have hfin_eq : (⟨u.length + 1 + ((j : ℕ) - 1 - u.length), hjB⟩ : Fin B) = j := Fin.ext hj_eq
  simp [w, List.getElem?_range hk_lt, hjB, hfin_eq]

omit [Fintype State] [DecidableEq State] in
private theorem abs_workTapePos_runFrom_add_one_lt (B : ℕ) (w : List Bool) (n : ℕ)
    (hn : n + 1 < B) (i : Fin m) :
    |(tm.runFrom (tm.initCfg w) n).workTapePos i| + 1 < B := by
  have := abs_workTapePos_runFrom_le (tm := tm) w n i
  omega

omit [DecidableEq State] in
private theorem realize_cellPosStepRHS {L' : Language.{0, 0}} {r : TableauRels L' m State}
    {B : ℕ} [L'.Structure (Fin B)] (hlt : ∀ x : Fin 2 → Fin B, RelMap r.lt x ↔ x 0 < x 1)
    {u w : List Bool} {cfg : Cfg m Bool State (u ++ w)} {t : Fin B}
    (heB : u.length + w.length + 1 < B) (hb : ∀ i : Fin m, |cfg.workTapePos i| < B)
    (huLen : ∀ z : Fin B, RelMap r.uLen ![z] ↔ (z : ℕ) = u.length)
    (huBit : ∀ p : Fin B, (p : ℕ) < u.length → (RelMap r.uBit ![p] ↔ u[(p : ℕ)]? = some true))
    (hend : ∀ z : Fin B, RelMap r.endPos ![z] ↔ (z : ℕ) = u.length + w.length)
    (hcert : ∀ j : Fin B, u.length < (j : ℕ) → (j : ℕ) ≤ u.length + w.length →
      (RelMap r.certBit ![j] ↔ w[(j : ℕ) - 1 - u.length]? = some true))
    (hA : r.AgreesAt cfg t) (i : Fin m) (s : Option Bool)
    (y : Fin 2 → Fin B) (yA : Fin 1 → Fin B) (ht : y 0 = t) :
    (cellStepRHS r tm (r.headPos i) (r.cellPos i) i s (.inl 0) (.inr 0)).Realize (Sum.elim y yA) ↔
      (Feature.cell i (yA 0 : ℤ) s).Holds (tm.step cfg) :=
  realize_cellStepRHS hlt heB hb huLen huBit hend hcert hA i s (yA 0 : ℤ)
    (r.headPos i) (r.cellPos i) (.inl 0 : Fin 2 ⊕ Fin 1) (.inr 0) (Sum.elim y yA) ht
    (hA.headPos i (yA 0)) (fun s' => hA.cellPos i s' (yA 0))

omit [DecidableEq State] in
private theorem realize_cellNegStepRHS {L' : Language.{0, 0}} {r : TableauRels L' m State}
    {B : ℕ} [L'.Structure (Fin B)] (hlt : ∀ x : Fin 2 → Fin B, RelMap r.lt x ↔ x 0 < x 1)
    {u w : List Bool} {cfg : Cfg m Bool State (u ++ w)} {t : Fin B}
    (heB : u.length + w.length + 1 < B) (hb : ∀ i : Fin m, |cfg.workTapePos i| < B)
    (huLen : ∀ z : Fin B, RelMap r.uLen ![z] ↔ (z : ℕ) = u.length)
    (huBit : ∀ p : Fin B, (p : ℕ) < u.length → (RelMap r.uBit ![p] ↔ u[(p : ℕ)]? = some true))
    (hend : ∀ z : Fin B, RelMap r.endPos ![z] ↔ (z : ℕ) = u.length + w.length)
    (hcert : ∀ j : Fin B, u.length < (j : ℕ) → (j : ℕ) ≤ u.length + w.length →
      (RelMap r.certBit ![j] ↔ w[(j : ℕ) - 1 - u.length]? = some true))
    (hA : r.AgreesAt cfg t) (i : Fin m) (s : Option Bool)
    (y : Fin 2 → Fin B) (yA : Fin 1 → Fin B) (ht : y 0 = t) :
    (cellStepRHS r tm (r.headNeg i) (r.cellNeg i) i s (.inl 0) (.inr 0)).Realize (Sum.elim y yA) ↔
      (Feature.cell i (-(yA 0 : ℤ)) s).Holds (tm.step cfg) :=
  realize_cellStepRHS hlt heB hb huLen huBit hend hcert hA i s (-(yA 0 : ℤ))
    (r.headNeg i) (r.cellNeg i) (.inl 0 : Fin 2 ⊕ Fin 1) (.inr 0) (Sum.elim y yA) ht
    (hA.headNeg i (yA 0)) (fun s' => hA.cellNeg i s' (yA 0))

private theorem agreesAt_step_of_realize_stepSentence {L' : Language.{0, 0}}
    {r : TableauRels L' m State} {B : ℕ} [L'.Structure (Fin B)]
    (hlt : ∀ x : Fin 2 → Fin B, RelMap r.lt x ↔ x 0 < x 1)
    {u w : List Bool} (hwB : u.length + w.length + 1 < B)
    (huLen : ∀ z : Fin B, RelMap r.uLen ![z] ↔ (z : ℕ) = u.length)
    (huBit : ∀ p : Fin B, (p : ℕ) < u.length → (RelMap r.uBit ![p] ↔ u[(p : ℕ)]? = some true))
    (hend : ∀ z : Fin B, RelMap r.endPos ![z] ↔ (z : ℕ) = u.length + w.length)
    (hcert : ∀ j : Fin B, u.length < (j : ℕ) → (j : ℕ) ≤ u.length + w.length →
      (RelMap r.certBit ![j] ↔ w[(j : ℕ) - 1 - u.length]? = some true))
    (hstepSent : (stepSentence r tm).Realize (Fin B))
    {n : ℕ} (hn : n + 1 < B)
    (hA_t : r.AgreesAt (tm.runFrom (tm.initCfg (u ++ w)) n) (⟨n, by omega⟩ : Fin B)) :
    r.AgreesAt (tm.runFrom (tm.initCfg (u ++ w)) (n + 1)) ⟨n + 1, hn⟩ := by
  have hb := abs_workTapePos_runFrom_add_one_lt tm B (u ++ w) n hn
  have hb' : ∀ i : Fin m, |(tm.runFrom (tm.initCfg (u ++ w)) n).workTapePos i| < B :=
    fun i => by have := hb i; omega
  simp only [stepSentence, realize_closeAll, Formula.realize_imp, Formula.realize_inf,
    Formula.realize_iInf, Formula.realize_iff, Formula.realize_iAlls, realize_succ hlt,
    realize_rel₁, realize_rel₂, Sum.elim_inl, Sum.elim_inr] at hstepSent
  let y : Fin 2 → Fin B := ![⟨n, by omega⟩, ⟨n + 1, hn⟩]
  obtain ⟨⟨⟨hs_state, hs_out⟩, hs_inPos⟩, hs_work⟩ := hstepSent y rfl
  rw [runFrom_succ]
  exact ⟨fun q' => (hs_state q').trans
      (realize_stateStepRHS hlt hwB hb' huLen huBit hend hcert hA_t q' 0 y rfl),
    fun o => (hs_out o).trans
      (realize_outStepRHS hlt hwB hb' huLen huBit hend hcert hA_t o 0 y rfl),
    fun j => (hs_inPos ![j]).trans
      (realize_inPosStepRHS hlt hwB hb' huLen huBit hend hcert hA_t
        (.inl 0) (.inr 0) (Sum.elim y ![j]) rfl),
    fun i a => (hs_work i ![a]).1.1.trans
      (realize_headPosStepRHS hlt hwB hb huLen huBit hend hcert hA_t i
        (.inl 0) (.inr 0) (Sum.elim y ![a]) rfl),
    fun i a => (hs_work i ![a]).1.2.trans
      (realize_headNegStepRHS hlt hwB hb huLen huBit hend hcert hA_t i
        (.inl 0) (.inr 0) (Sum.elim y ![a]) rfl),
    fun i s a => ((hs_work i ![a]).2 s).1.trans
      (realize_cellPosStepRHS tm hlt hwB hb' huLen huBit hend hcert hA_t i s y ![a] rfl),
    fun i s a => ((hs_work i ![a]).2 s).2.trans
      (realize_cellNegStepRHS tm hlt hwB hb' huLen huBit hend hcert hA_t i s y ![a] rfl)⟩

private theorem realize_stepSentence_of_agreesAt {L' : Language.{0, 0}}
    {r : TableauRels L' m State} {B : ℕ} [L'.Structure (Fin B)]
    (hlt : ∀ x : Fin 2 → Fin B, RelMap r.lt x ↔ x 0 < x 1)
    {u w : List Bool} (hwB : u.length + w.length + 1 < B)
    (huLen : ∀ z : Fin B, RelMap r.uLen ![z] ↔ (z : ℕ) = u.length)
    (huBit : ∀ p : Fin B, (p : ℕ) < u.length → (RelMap r.uBit ![p] ↔ u[(p : ℕ)]? = some true))
    (hend : ∀ z : Fin B, RelMap r.endPos ![z] ↔ (z : ℕ) = u.length + w.length)
    (hcert : ∀ j : Fin B, u.length < (j : ℕ) → (j : ℕ) ≤ u.length + w.length →
      (RelMap r.certBit ![j] ↔ w[(j : ℕ) - 1 - u.length]? = some true))
    (hAgrees : ∀ t : Fin B, r.AgreesAt (tm.runFrom (tm.initCfg (u ++ w)) (t : ℕ)) t) :
    (stepSentence r tm).Realize (Fin B) := by
  simp only [stepSentence, realize_closeAll, Formula.realize_imp, Formula.realize_inf,
    Formula.realize_iInf, Formula.realize_iff, Formula.realize_iAlls, realize_succ hlt,
    realize_rel₁, realize_rel₂, Sum.elim_inl, Sum.elim_inr]
  intro y hsucc
  have hA_t := hAgrees (y 0)
  have hb := abs_workTapePos_runFrom_add_one_lt tm B (u ++ w) (y 0) (by omega)
  have hb' : ∀ i : Fin m, |(tm.runFrom (tm.initCfg (u ++ w)) (y 0 : ℕ)).workTapePos i| < B :=
    fun i => by have := hb i; omega
  have hA_t' : r.AgreesAt (tm.step (tm.runFrom (tm.initCfg (u ++ w)) (y 0 : ℕ))) (y 1) := by
    simpa [← runFrom_succ, ← hsucc] using hAgrees (y 1)
  exact ⟨⟨⟨fun q' => (hA_t'.state q').trans
        (realize_stateStepRHS hlt hwB hb' huLen huBit hend hcert hA_t q' 0 y rfl).symm,
      fun o => (hA_t'.out o).trans
        (realize_outStepRHS hlt hwB hb' huLen huBit hend hcert hA_t o 0 y rfl).symm⟩,
      fun yJ => (hA_t'.inPos (yJ 0)).trans
        (realize_inPosStepRHS hlt hwB hb' huLen huBit hend hcert hA_t
          (.inl 0) (.inr 0) (Sum.elim y yJ) rfl).symm⟩,
    fun i yA => ⟨⟨(hA_t'.headPos i (yA 0)).trans
        (realize_headPosStepRHS hlt hwB hb huLen huBit hend hcert hA_t i
          (.inl 0) (.inr 0) (Sum.elim y yA) rfl).symm,
      (hA_t'.headNeg i (yA 0)).trans
        (realize_headNegStepRHS hlt hwB hb huLen huBit hend hcert hA_t i
          (.inl 0) (.inr 0) (Sum.elim y yA) rfl).symm⟩,
      fun s => ⟨(hA_t'.cellPos i s (yA 0)).trans
          (realize_cellPosStepRHS tm hlt hwB hb' huLen huBit hend hcert hA_t i s y yA rfl).symm,
        (hA_t'.cellNeg i s (yA 0)).trans
          (realize_cellNegStepRHS tm hlt hwB hb' huLen huBit hend hcert hA_t i s y yA rfl).symm⟩⟩⟩

omit [Fintype State] [DecidableEq State] in
private theorem realize_acceptSentence_iff_of_agreesAt {L' : Language.{0, 0}}
    {r : TableauRels L' m State} {B : ℕ} [L'.Structure (Fin B)] (hB1 : 1 < B)
    (hlt : ∀ x : Fin 2 → Fin B, RelMap r.lt x ↔ x 0 < x 1)
    {w : List Bool} {cfg : Cfg m Bool State w}
    (hA : r.AgreesAt cfg (⟨B - 1, by omega⟩ : Fin B)) :
    (acceptSentence r).Realize (Fin B) ↔ cfg.state = none ∧ cfg.output = [true] := by
  simp only [acceptSentence, realize_closeAll, Formula.realize_imp, Formula.realize_inf,
    realize_isMax hlt, realize_rel₁]
  refine ⟨fun h => ?_, fun ⟨hhalt, hout⟩ y hy => ?_⟩
  · obtain ⟨hs, ho⟩ := h ![(⟨B - 1, by omega⟩ : Fin B)] rfl
    exact ⟨(hA.state none).1 hs, OutView.ofList_eq_one_iff.1 ((hA.out (.one true)).1 ho)⟩
  · have hy' : y 0 = ⟨B - 1, by omega⟩ := Fin.ext hy
    rw [hy', hA.state none, hA.out (.one true)]
    exact ⟨hhalt, OutView.ofList_eq_one_iff.2 hout⟩

private theorem realize_tableauMatrix_sound {B : ℕ} [L₀.Structure (Fin B)]
    (hlt0 : ∀ x : Fin 2 → Fin B, RelMap lt x ↔ x 0 < x 1)
    {u : List Bool} (_huB : u.length + 1 < B)
    (huLen0 : ∀ z : Fin B, RelMap uLenRel ![z] ↔ (z : ℕ) = u.length)
    (huBit0 : ∀ p : Fin B, (p : ℕ) < u.length → (RelMap uBitRel ![p] ↔ u[(p : ℕ)]? = some true))
    (R : ∀ idx : TableauVar m State, Set (Fin (tableauArity m State idx) → Fin B))
    (hmat : (letI := ESO.varLanguage.structure (arity := tableauArity m State) R;
      (tableauMatrix lt uLenRel uBitRel tm).Realize (Fin B))) :
    ∃ w : List Bool, u.length + w.length + 1 < B ∧
      (tm.runFrom (tm.initCfg (u ++ w)) (B - 1)).state = none ∧
      (tm.runFrom (tm.initCfg (u ++ w)) (B - 1)).output = [true] := by
  let _ := ESO.varLanguage.structure (arity := tableauArity m State) R
  have hB1 : 1 < B := by omega
  let r := tableauRels (m := m) (State := State) lt uLenRel uBitRel
  change (endPosSentence r ⊓ initSentence r tm ⊓ stepSentence r tm ⊓ acceptSentence r).Realize
    (Fin B) at hmat
  simp only [Sentence.realize_inf] at hmat
  obtain ⟨⟨⟨hendSent, hinitSent⟩, hstepSent⟩, haccSent⟩ := hmat
  obtain ⟨w, hwB, hend, hcert⟩ := exists_certWord_of_realize_endPosSentence hlt0 huLen0 hendSent
  have hAgrees : ∀ (n : ℕ) (hn : n < B),
      r.AgreesAt (tm.runFrom (tm.initCfg (u ++ w)) n) ⟨n, hn⟩ := by
    intro n hn
    induction n with
    | zero => simpa [runFrom] using (realize_initSentence hlt0 hB1).1 hinitSent
    | succ n ih =>
      exact agreesAt_step_of_realize_stepSentence tm hlt0 hwB huLen0 huBit0 hend hcert
        hstepSent hn (ih (by omega))
  have hacc := (realize_acceptSentence_iff_of_agreesAt hB1 hlt0 (hAgrees (B - 1) (by omega))).1
    haccSent
  exact ⟨w, hwB, hacc.1, hacc.2⟩

omit [Fintype State] [DecidableEq State] in
/-- Canonical witness interpretation of `TableauVar m State` on `Fin B` for certificate `w`. -/
private def canonicalTableauR (B : ℕ) (u w : List Bool) :
    ∀ idx : TableauVar m State, Set (Fin (tableauArity m State idx) → Fin B)
  | .inl (.inl ()) => {x : Fin 1 → Fin B | (x 0 : ℕ) = u.length + w.length}
  | .inl (.inr (.inl ())) =>
    {x : Fin 1 → Fin B | w[(x 0 : ℕ) - 1 - u.length]? = some true}
  | .inl (.inr (.inr (.inl q))) =>
    {x : Fin 1 → Fin B | (Feature.state q).Holds (tm.runFrom (tm.initCfg (u ++ w)) (x 0 : ℕ))}
  | .inl (.inr (.inr (.inr o))) =>
    {x : Fin 1 → Fin B | (Feature.out o).Holds (tm.runFrom (tm.initCfg (u ++ w)) (x 0 : ℕ))}
  | .inr (.inl ()) =>
    {x : Fin 2 → Fin B |
      (Feature.inPos (x 1 : ℕ)).Holds (tm.runFrom (tm.initCfg (u ++ w)) (x 0 : ℕ))}
  | .inr (.inr (.inl i)) =>
    {x : Fin 2 → Fin B |
      (Feature.head i (x 1 : ℤ)).Holds (tm.runFrom (tm.initCfg (u ++ w)) (x 0 : ℕ))}
  | .inr (.inr (.inr (.inl i))) =>
    {x : Fin 2 → Fin B |
      (Feature.head i (-(x 1 : ℤ))).Holds (tm.runFrom (tm.initCfg (u ++ w)) (x 0 : ℕ))}
  | .inr (.inr (.inr (.inr (.inl (i, s))))) =>
    {x : Fin 2 → Fin B |
      (Feature.cell i (x 1 : ℤ) s).Holds (tm.runFrom (tm.initCfg (u ++ w)) (x 0 : ℕ))}
  | .inr (.inr (.inr (.inr (.inr (i, s))))) =>
    {x : Fin 2 → Fin B |
      (Feature.cell i (-(x 1 : ℤ)) s).Holds (tm.runFrom (tm.initCfg (u ++ w)) (x 0 : ℕ))}

private theorem realize_tableauMatrix_complete {B : ℕ} [L₀.Structure (Fin B)]
    (hlt0 : ∀ x : Fin 2 → Fin B, RelMap lt x ↔ x 0 < x 1)
    {u w : List Bool} (hwB : u.length + w.length + 1 < B)
    (huLen0 : ∀ z : Fin B, RelMap uLenRel ![z] ↔ (z : ℕ) = u.length)
    (huBit0 : ∀ p : Fin B, (p : ℕ) < u.length → (RelMap uBitRel ![p] ↔ u[(p : ℕ)]? = some true))
    (hhalt : (tm.runFrom (tm.initCfg (u ++ w)) (B - 1)).state = none)
    (hout : (tm.runFrom (tm.initCfg (u ++ w)) (B - 1)).output = [true]) :
    (letI := ESO.varLanguage.structure (arity := tableauArity m State) (canonicalTableauR tm B u w);
      (tableauMatrix lt uLenRel uBitRel tm).Realize (Fin B)) := by
  let _ := ESO.varLanguage.structure (arity := tableauArity m State) (canonicalTableauR tm B u w)
  have hB1 : 1 < B := by omega
  let r := tableauRels (m := m) (State := State) lt uLenRel uBitRel
  have hend : ∀ z : Fin B, RelMap r.endPos ![z] ↔ (z : ℕ) = u.length + w.length :=
    fun _ => Iff.rfl
  have hcert : ∀ j : Fin B, u.length < (j : ℕ) → (j : ℕ) ≤ u.length + w.length →
      (RelMap r.certBit ![j] ↔ w[(j : ℕ) - 1 - u.length]? = some true) :=
    fun _ _ _ => Iff.rfl
  have hAgrees : ∀ t : Fin B, r.AgreesAt (tm.runFrom (tm.initCfg (u ++ w)) (t : ℕ)) t := fun _ =>
    ⟨fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ _ => Iff.rfl,
      fun _ _ => Iff.rfl, fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl⟩
  change (endPosSentence r ⊓ initSentence r tm ⊓ stepSentence r tm ⊓ acceptSentence r).Realize
    (Fin B)
  simp only [Sentence.realize_inf]
  exact ⟨⟨⟨realize_endPosSentence_of_canonical hlt0 (Nat.le_add_right _ _) hwB huLen0 hend,
      (realize_initSentence hlt0 hB1).2 (hAgrees ⟨0, by omega⟩)⟩,
    realize_stepSentence_of_agreesAt tm hlt0 hwB huLen0 huBit0 hend hcert hAgrees⟩,
    (realize_acceptSentence_iff_of_agreesAt hB1 hlt0 (hAgrees ⟨B - 1, by omega⟩)).2 ⟨hhalt, hout⟩⟩

/-- **Correctness of `tableauESOSentence` on `Fin B`.** -/
theorem realize_tableauESOSentence {B : ℕ} [L₀.Structure (Fin B)]
    (hlt0 : ∀ x : Fin 2 → Fin B, RelMap lt x ↔ x 0 < x 1)
    {u : List Bool} (huB : u.length + 1 < B)
    (huLen0 : ∀ z : Fin B, RelMap uLenRel ![z] ↔ (z : ℕ) = u.length)
    (huBit0 : ∀ p : Fin B, (p : ℕ) < u.length → (RelMap uBitRel ![p] ↔ u[(p : ℕ)]? = some true)) :
    (tableauESOSentence lt uLenRel uBitRel tm).Realize (Fin B) ↔
      ∃ w : List Bool, u.length + w.length + 1 < B ∧
        (tm.runFrom (tm.initCfg (u ++ w)) (B - 1)).state = none ∧
        (tm.runFrom (tm.initCfg (u ++ w)) (B - 1)).output = [true] := by
  rw [tableauESOSentence, ESO.Sentence.Realize]
  exact ⟨fun ⟨R, hmat⟩ =>
      realize_tableauMatrix_sound lt uLenRel uBitRel tm hlt0 huB huLen0 huBit0 R hmat,
    fun ⟨w, hwB, hhalt, hout⟩ =>
      ⟨canonicalTableauR tm B u w,
        realize_tableauMatrix_complete lt uLenRel uBitRel tm hlt0 hwB huLen0 huBit0 hhalt hout⟩⟩

end TableauESO

end FO

namespace Vocabulary

variable {L : Language.{u, v}} (v : Vocabulary L)
  {m : ℕ} {State : Type} [Fintype State] [DecidableEq State]
  (tm : MultiTapeTM m Bool State)

/-- Specialization of `FO.tableauESOSentence` to `v.powerLanguage.sum inputVarLanguage`. -/
noncomputable def tableauESOSentence :
    ESO.Sentence (v.powerLanguage.sum inputVarLanguage) :=
  FO.tableauESOSentence (L₀ := v.powerLanguage.sum inputVarLanguage)
    (Sum.inl v.powerLt) (Sum.inr uLenSym) (Sum.inr uBitSym) tm

/-- **Correctness of `v.tableauESOSentence` on `Fin B`.** When `I_in` satisfies the layout
specification for `u`, `(v.tableauESOSentence tm).Realize (Fin B)` holds if and only if
`CookLevin.tableau tm u L (B - 1)` is satisfiable for some certificate length `L` with
`u.length + L + 1 < B`. -/
theorem realize_tableauESOSentence (a : EncodedStructure) (B : ℕ)
    (I_in : ∀ b : Bool, Set (Fin ((fun _ : Bool => 1) b) → Fin B))
    {u : List Bool} (huB : u.length + 1 < B)
    (huLen : ∀ z : Fin B, ![z] ∈ I_in true ↔ (z : ℕ) = u.length)
    (huBit : ∀ p : Fin B, (p : ℕ) < u.length →
      (![p] ∈ I_in false ↔ u[(p : ℕ)]? = some true)) :
    (letI := v.powerStructure a B;
      letI := ESO.varLanguage.structure (arity := fun _ : Bool => 1) I_in;
      (v.tableauESOSentence tm).Realize (Fin B)) ↔
      ∃ L : ℕ, u.length + L + 1 < B ∧
        (CookLevin.tableau tm u L (B - 1)).Satisfiable := by
  let _ := v.powerStructure a B
  let _ := ESO.varLanguage.structure (arity := fun _ : Bool => 1) I_in
  have h := FO.realize_tableauESOSentence (L₀ := v.powerLanguage.sum inputVarLanguage)
    (Sum.inl v.powerLt) (Sum.inr uLenSym) (Sum.inr uBitSym) tm
    (fun _ => Iff.rfl) huB huLen huBit
  rw [tableauESOSentence, h]
  simp only [CookLevin.tableau_satisfiable_iff]
  constructor
  · rintro ⟨w, hwB, hhalt, hout⟩
    exact ⟨w.length, hwB, w, rfl, hhalt, hout⟩
  · rintro ⟨L, hLB, w, rfl, hhalt, hout⟩
    exact ⟨w, hLB, hhalt, hout⟩

end Vocabulary

end Cslib.Logic
