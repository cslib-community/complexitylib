/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Fagin.Tableau.Defs
import Complexity.Computability.Machines.Turing.MultiTape.InputAt

/-!
# Semantic realization of the first-order tableau formulas on `Fin B`

This file proves the semantic realization lemmas on `Fin B` for the first-order formulas defined in
`Complexity.Computability.Complexity.Fagin.Tableau.Defs`, relating relation interpretations via
`FO.TableauRels.AgreesAt` to configuration features of `tm : MultiTapeTM m Bool State`.

## Main definitions

* `Cslib.Logic.FO.TableauRels.EncodesInput`: the input relations of `r` on `Fin B` describe an
  input `u` followed by a certificate `w`.
* `Cslib.Logic.FO.TableauRels.AgreesAt`: agreement at time `t : Fin B` between the relation symbols
  of `r : TableauRels L' m State` and a configuration `cfg : Cfg m Bool State input`.

## Main results

* `Cslib.Logic.FO.exists_of_realize_endPosSentence`,
  `Cslib.Logic.FO.realize_endPosSentence_of_canonical`: soundness and completeness of
  `endPosSentence`.
* `Cslib.Logic.FO.realize_inputAtFormula`, `Cslib.Logic.FO.realize_sitFormula`: semantic
  characterization of the input-tape and situation formulas.
* `Cslib.Logic.FO.realize_stateStepRHS`, `Cslib.Logic.FO.realize_outStepRHS`,
  `Cslib.Logic.FO.realize_inPosStepRHS`, `Cslib.Logic.FO.realize_headPosStepRHS`,
  `Cslib.Logic.FO.realize_headNegStepRHS`, `Cslib.Logic.FO.realize_cellStepRHS`: semantic
  characterization of the step right-hand-side formulas.
* `Cslib.Logic.FO.realize_initSentence`: semantic characterization of `initSentence`.

## References

* [R. Fagin, *Generalized first-order spectra and polynomial-time recognizable sets*][Fagin1974]
* [N. Immerman, *Descriptive Complexity*][Immerman1999]
* [C. H. Papadimitriou, *Computational Complexity*][Papadimitriou94], Theorem 8.3
-/

@[expose] public section

namespace Cslib.Logic.FO

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure
open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Feature
open Cslib.Complexity

/-- The input relations of `r` on `Fin B` describe the tape contents `u ++ w`, an input `u`
followed by a certificate `w`, with room for both and an end marker below `B`: `uLen` holds
exactly at `u.length`, `endPos` exactly at `u.length + w.length`, `uBit` at the positions
`p < u.length` where `u` has a `true`, and `certBit` at the positions `j` with
`u.length < j ≤ u.length + w.length` where `w` has a `true` at `j - 1 - u.length`. -/
structure TableauRels.EncodesInput {L' : Language.{0, 0}} {m : ℕ} {State : Type}
    (r : TableauRels L' m State) (B : ℕ) [L'.Structure (Fin B)] (u w : List Bool) : Prop where
  /-- Both words and the end marker fit below `B`. -/
  length_lt : u.length + w.length + 1 < B
  /-- `uLen` marks the length of the input. -/
  uLen_iff : ∀ z : Fin B, RelMap r.uLen ![z] ↔ (z : ℕ) = u.length
  /-- `uBit` marks the `true` bits of the input. -/
  uBit_iff : ∀ p : Fin B, (p : ℕ) < u.length → (RelMap r.uBit ![p] ↔ u[(p : ℕ)]? = some true)
  /-- `endPos` marks the end of the certificate. -/
  endPos_iff : ∀ z : Fin B, RelMap r.endPos ![z] ↔ (z : ℕ) = u.length + w.length
  /-- `certBit` marks the `true` bits of the certificate, which starts after position
  `u.length`. -/
  certBit_iff : ∀ j : Fin B, u.length < (j : ℕ) → (j : ℕ) ≤ u.length + w.length →
    (RelMap r.certBit ![j] ↔ w[(j : ℕ) - 1 - u.length]? = some true)

section Semantics

variable {L' : Language.{0, 0}} {B : ℕ} [L'.Structure (Fin B)]
  {m : ℕ} {State : Type} {r : TableauRels L' m State}
  (hlt : ∀ x : Fin 2 → Fin B, RelMap r.lt x ↔ x 0 < x 1)
  {tm : MultiTapeTM m Bool State}

include hlt in
/-- Soundness of `endPosSentence`: extracts the unique certificate end position `e : Fin B` with
`u.length ≤ e` and `e + 1 < B`. -/
theorem exists_of_realize_endPosSentence {u : List Bool}
    (huLen : ∀ z : Fin B, RelMap r.uLen ![z] ↔ (z : ℕ) = u.length)
    (h : (Fin B) ⊨ endPosSentence r) :
    ∃ e : Fin B, u.length ≤ (e : ℕ) ∧ (e : ℕ) + 1 < B ∧
      ∀ z : Fin B, RelMap r.endPos ![z] ↔ (z : ℕ) = (e : ℕ) := by
  simp only [endPosSentence, Sentence.realize_inf, realize_closeEx, realize_closeAll,
    Formula.realize_inf, Formula.realize_not, Formula.realize_imp, Formula.realize_iExs,
    realize_rel₁, realize_le hlt, realize_isMax hlt, realize_varEq,
    Sum.elim_inl, Sum.elim_inr] at h
  obtain ⟨⟨yE, ⟨hE, ⟨yU, hU, hle⟩⟩, hnotMax⟩, huniq⟩ := h
  have hU_eq : (yU 0 : ℕ) = u.length := (huLen (yU 0)).1 hU
  rw [Fin.le_def] at hle
  have he0 := (yE 0).2
  refine ⟨yE 0, by omega, by omega, fun z => ?_⟩
  constructor
  · intro hz
    have := huniq ![z, yE 0] ⟨hz, hE⟩
    exact congrArg Fin.val this
  · intro hz
    have heq : z = yE 0 := Fin.ext hz
    rwa [heq]

include hlt in
/-- Completeness of `endPosSentence`. -/
theorem realize_endPosSentence_of_canonical {u : List Bool} {e : ℕ}
    (hle : u.length ≤ e) (heB : e + 1 < B)
    (huLen : ∀ z : Fin B, RelMap r.uLen ![z] ↔ (z : ℕ) = u.length)
    (hend : ∀ z : Fin B, RelMap r.endPos ![z] ↔ (z : ℕ) = e) :
    (Fin B) ⊨ endPosSentence r := by
  simp only [endPosSentence, Sentence.realize_inf, realize_closeEx, realize_closeAll,
    Formula.realize_inf, Formula.realize_not, Formula.realize_imp, Formula.realize_iExs,
    realize_rel₁, realize_le hlt, realize_isMax hlt, realize_varEq,
    Sum.elim_inl, Sum.elim_inr]
  refine ⟨⟨![(⟨e, by omega⟩ : Fin B)], ⟨(hend _).2 rfl, ⟨![(⟨u.length, by omega⟩ : Fin B)],
    (huLen _).2 rfl, ?_⟩⟩, ?_⟩, fun y ⟨h0, h1⟩ => ?_⟩
  · simpa [Fin.le_def] using hle
  · dsimp; omega
  · exact Fin.ext (((hend (y 0)).1 h0).trans ((hend (y 1)).1 h1).symm)

include hlt in
/-- Semantic characterization of `inputAtFormula`. -/
theorem realize_inputAtFormula {u w : List Bool}
    (hI : r.EncodesInput B u w) (s : Option Bool) {V : Type*} (vJ : V) (env : V → Fin B) :
    (inputAtFormula r s vJ).Realize env ↔
      inputAt (u ++ w) (env vJ : ℕ) = s := by
  have heB := hI.length_lt
  rcases s with _ | b
  · -- `s = none`
    simp only [inputAtFormula, Formula.realize_sup, realize_isZero hlt, Formula.realize_iExs,
      Formula.realize_inf, realize_rel₁, realize_lt hlt, Sum.elim_inl, Sum.elim_inr,
      Fin.lt_def, inputAt_eq_none_iff, List.length_append]
    refine or_congr Iff.rfl ⟨fun ⟨yE, hE, hltE⟩ => ?_, fun hj => ?_⟩
    · have hE' := (hI.endPos_iff (yE 0)).1 hE
      omega
    · exact ⟨![⟨u.length + w.length, by omega⟩], (hI.endPos_iff _).2 rfl, hj⟩
  · -- `s = some b`
    have huBit_iff : ∀ (p : Fin B) (hp : (p : ℕ) < u.length),
        (if b then RelMap r.uBit ![p] else ¬RelMap r.uBit ![p]) ↔ u[(p : ℕ)]? = some b := by
      intro p hp
      rw [hI.uBit_iff p hp, List.getElem?_eq_getElem hp]
      cases b <;> cases u[(p : ℕ)] <;> simp
    have hcert_iff : ∀ (j : Fin B) (hgt : u.length < (j : ℕ)) (hle : (j : ℕ) ≤ u.length + w.length),
        (if b then RelMap r.certBit ![j] else ¬RelMap r.certBit ![j]) ↔
          w[(j : ℕ) - 1 - u.length]? = some b := by
      intro j hgt hle
      have hidx : (j : ℕ) - 1 - u.length < w.length := by omega
      rw [hI.certBit_iff j hgt hle, List.getElem?_eq_getElem hidx]
      cases b <;> cases w[(j : ℕ) - 1 - u.length] <;> simp
    have hform : (inputAtFormula r (some b) vJ).Realize env ↔
        (∃ y : Fin 2 → Fin B,
          (((env vJ : ℕ) = (y 0 : ℕ) + 1 ∧ RelMap r.uLen ![y 1]) ∧ (y 0 : ℕ) < (y 1 : ℕ)) ∧
            (if b then RelMap r.uBit ![y 0] else ¬RelMap r.uBit ![y 0])) ∨
        (∃ y : Fin 2 → Fin B,
          (((RelMap r.uLen ![y 0] ∧ RelMap r.endPos ![y 1]) ∧ (y 0 : ℕ) < (env vJ : ℕ)) ∧
            (env vJ : ℕ) ≤ (y 1 : ℕ)) ∧
            (if b then RelMap r.certBit ![env vJ] else ¬RelMap r.certBit ![env vJ])) := by
      cases b <;>
        simp only [inputAtFormula, Formula.realize_sup, Formula.realize_iExs, Formula.realize_inf,
          Formula.realize_not, realize_succ hlt, realize_rel₁, realize_lt hlt,
          realize_le hlt, Sum.elim_inl, Sum.elim_inr, Fin.lt_def, Fin.le_def,
          Bool.false_eq_true, ↓reduceIte]
    rw [hform, inputAt_eq_some_iff]
    constructor
    · rintro (⟨y, ⟨⟨hp, hU⟩, hltU⟩, hBit⟩ | ⟨y, ⟨⟨⟨hU, hE⟩, hgtU⟩, hleE⟩, hCert⟩)
      · have hU' := (hI.uLen_iff (y 1)).1 hU
        have hp_lt : (y 0 : ℕ) < u.length := by omega
        refine ⟨y 0, hp, ?_⟩
        rw [List.getElem?_append_left hp_lt]
        exact (huBit_iff (y 0) hp_lt).1 hBit
      · have hU' := (hI.uLen_iff (y 0)).1 hU
        have hE' := (hI.endPos_iff (y 1)).1 hE
        refine ⟨(env vJ : ℕ) - 1, by omega, ?_⟩
        rw [List.getElem?_append_right (by omega)]
        exact (hcert_iff (env vJ) (by omega) (by omega)).1 hCert
    · rintro ⟨q, hq, hsome⟩
      rcases lt_or_ge q u.length with hqu | hqu
      · -- the position lies in the input `u`
        rw [List.getElem?_append_left hqu] at hsome
        let p : Fin B := ⟨q, by omega⟩
        exact Or.inl ⟨![p, ⟨u.length, by omega⟩], ⟨⟨hq, (hI.uLen_iff _).2 rfl⟩, hqu⟩,
          (huBit_iff p hqu).2 hsome⟩
      · -- the position lies in the certificate `w`
        rw [List.getElem?_append_right hqu] at hsome
        have hidx : q - u.length < w.length := (List.getElem?_eq_some_iff.mp hsome).choose
        refine Or.inr ⟨![⟨u.length, by omega⟩, ⟨u.length + w.length, by omega⟩],
          ⟨⟨⟨(hI.uLen_iff _).2 rfl, (hI.endPos_iff _).2 rfl⟩, by dsimp; omega⟩, by dsimp; omega⟩,
          ?_⟩
        rw [hcert_iff (env vJ) (by omega) (by omega), hq, Nat.add_sub_cancel]
        exact hsome

/-- Predicate stating that the relation symbols of `r` at time `t : Fin B` agree with a
configuration `cfg : Cfg m Bool State input`. -/
structure TableauRels.AgreesAt (r : TableauRels L' m State)
    {input : List Bool} (cfg : Cfg m Bool State input) (t : Fin B) : Prop where
  state : ∀ q : Option State, RelMap (r.state q) ![t] ↔ (Feature.state q).Holds cfg
  out : ∀ o : OutView, RelMap (r.out o) ![t] ↔ (Feature.out o).Holds cfg
  inPos : ∀ j : Fin B, RelMap r.inPos ![t, j] ↔ (Feature.inPos (j : ℕ)).Holds cfg
  headPos : ∀ (i : Fin m) (a : Fin B),
    RelMap (r.headPos i) ![t, a] ↔ (Feature.head i (a : ℤ)).Holds cfg
  headNeg : ∀ (i : Fin m) (a : Fin B),
    RelMap (r.headNeg i) ![t, a] ↔ (Feature.head i (-(a : ℤ))).Holds cfg
  cellPos : ∀ (i : Fin m) (s : Option Bool) (a : Fin B),
    RelMap (r.cellPos i s) ![t, a] ↔ (Feature.cell i (a : ℤ) s).Holds cfg
  cellNeg : ∀ (i : Fin m) (s : Option Bool) (a : Fin B),
    RelMap (r.cellNeg i s) ![t, a] ↔ (Feature.cell i (-(a : ℤ)) s).Holds cfg

include hlt in
/-- Semantic characterization of `inReadFormula` under `AgreesAt`. -/
private theorem realize_inReadFormula {u w : List Bool} {cfg : Cfg m Bool State (u ++ w)}
    {t : Fin B} (hI : r.EncodesInput B u w) (hA : r.AgreesAt cfg t)
    (s : Option Bool) {V : Type*} (vT : V) (env : V → Fin B) (ht : env vT = t) :
    (inReadFormula r s vT).Realize env ↔ (Feature.inRead s).Holds cfg := by
  have heB := hI.length_lt
  simp only [inReadFormula, Formula.realize_iExs, Formula.realize_inf, realize_rel₂,
    realize_inputAtFormula hlt hI, Sum.elim_inl, Sum.elim_inr, ht,
    hA.inPos, holds_inPos, holds_inRead, Cfg.inputSymbol_eq_inputAt]
  constructor
  · rintro ⟨y, hpos, hs⟩
    rwa [hpos]
  · intro hs
    have hp : cfg.inputPos.val < u.length + w.length + 2 := by simpa using cfg.inputPos.isLt
    exact ⟨![(⟨cfg.inputPos.val, by omega⟩ : Fin B)], rfl, hs⟩

/-- Semantic characterization of `readFormula` under `AgreesAt`. -/
private theorem realize_readFormula {input : List Bool} {cfg : Cfg m Bool State input} {t : Fin B}
    (hb : ∀ i : Fin m, |cfg.workTapePos i| < B) (hA : r.AgreesAt cfg t)
    (i : Fin m) (s : Option Bool) {V : Type*} (vT : V) (env : V → Fin B) (ht : env vT = t) :
    (readFormula r i s vT).Realize env ↔ (Feature.read i s).Holds cfg := by
  simp only [readFormula, Formula.realize_iExs, Formula.realize_sup, Formula.realize_inf,
    realize_rel₂, Sum.elim_inl, Sum.elim_inr, ht,
    hA.headPos, hA.headNeg, hA.cellPos, hA.cellNeg,
    holds_head, holds_cell, holds_read, Cfg.workTapeSymbols]
  constructor
  · rintro ⟨y, (⟨hh, hc⟩ | ⟨hh, hc⟩)⟩ <;> rwa [hh]
  · intro hs
    have hbi := hb i
    rw [abs_lt] at hbi
    by_cases hnonneg : 0 ≤ cfg.workTapePos i
    · let a : Fin B := ⟨(cfg.workTapePos i).toNat, by omega⟩
      refine ⟨![a], Or.inl ⟨by dsimp [a]; omega, ?_⟩⟩
      have heq : ((a : ℕ) : ℤ) = cfg.workTapePos i := by dsimp [a]; omega
      rwa [Matrix.cons_val_zero, heq]
    · let a : Fin B := ⟨(-cfg.workTapePos i).toNat, by omega⟩
      refine ⟨![a], Or.inr ⟨by dsimp [a]; omega, ?_⟩⟩
      have heq : -((a : ℕ) : ℤ) = cfg.workTapePos i := by dsimp [a]; omega
      rwa [Matrix.cons_val_zero, heq]

include hlt in
/-- Semantic characterization of `sitFormula` under `AgreesAt`. -/
theorem realize_sitFormula {u w : List Bool} {cfg : Cfg m Bool State (u ++ w)} {t : Fin B}
    (hI : r.EncodesInput B u w) (hb : ∀ i : Fin m, |cfg.workTapePos i| < B) (hA : r.AgreesAt cfg t)
    (y : Situation m State) {V : Type*} (vT : V) (env : V → Fin B) (ht : env vT = t) :
    (sitFormula r y vT).Realize env ↔ (Feature.sit y).Holds cfg := by
  simp only [sitFormula, Formula.realize_inf, Formula.realize_iInf, realize_rel₁, ht,
    hA.state, realize_inReadFormula hlt hI  hA _ vT env ht,
    realize_readFormula hb hA _ _ vT env ht, holds_sit_iff, and_assoc]

include hlt in
/-- Semantic characterization of `inPosPrevFormula` under `AgreesAt`. -/
private theorem realize_inPosPrevFormula {u w : List Bool} {cfg : Cfg m Bool State (u ++ w)}
    {t : Fin B}
    (heB : u.length + w.length + 1 < B)
    (hend : ∀ z : Fin B, RelMap r.endPos ![z] ↔ (z : ℕ) = u.length + w.length)
    (hA : r.AgreesAt cfg t)
    (d : SignType) {V : Type*} (vT vJ : V) (env : V → Fin B) (ht : env vT = t) :
    (inPosPrevFormula r d vT vJ).Realize env ↔
      moveInputPosNat (u ++ w).length cfg.inputPos.val d = (env vJ : ℕ) := by
  have hp : cfg.inputPos.val < u.length + w.length + 2 := by simpa using cfg.inputPos.isLt
  have hlen : (u ++ w).length = u.length + w.length := List.length_append
  rcases d with _ | _ | _
  · -- `d = .zero`
    simp only [inPosPrevFormula, realize_rel₂, ht, hA.inPos, holds_inPos,
      moveInputPosNat, SignType.zero_eq_zero, SignType.coe_zero]
    omega
  · -- `d = .neg`
    simp only [inPosPrevFormula, Formula.realize_sup, Formula.realize_inf,
      realize_isZero hlt, Formula.realize_iExs, realize_succ hlt, realize_rel₂,
      Sum.elim_inl, Sum.elim_inr, ht, hA.inPos, holds_inPos,
      moveInputPosNat, SignType.neg_eq_neg_one, SignType.coe_neg_one]
    constructor
    · rintro (⟨hj0, hp0⟩ | ⟨y, hy, hpy⟩) <;> omega
    · intro hmove
      by_cases hp0 : cfg.inputPos.val = 0
      · exact Or.inl ⟨by omega, by omega⟩
      · right
        refine ⟨![(⟨cfg.inputPos.val, by omega⟩ : Fin B)], by dsimp; omega, rfl⟩
  · -- `d = .pos`
    simp only [inPosPrevFormula, Formula.realize_sup, Formula.realize_inf,
      Formula.realize_iExs, realize_rel₁, realize_succ hlt, realize_le hlt,
      realize_rel₂, Sum.elim_inl, Sum.elim_inr, Fin.le_def, ht, hA.inPos, holds_inPos,
      moveInputPosNat, SignType.pos_eq_one, SignType.coe_one]
    constructor
    · rintro (⟨y, ⟨hE, hsucc⟩, hpj⟩ | ⟨y, ⟨⟨⟨hE, hle⟩, hsucc⟩, hp0⟩⟩)
      · have hE' := (hend (y 0)).1 hE
        omega
      · have hE' := (hend (y 1)).1 hE
        omega
    · intro hmove
      by_cases hpe : cfg.inputPos.val = u.length + w.length + 1
      · left
        refine ⟨![(⟨u.length + w.length, by omega⟩ : Fin B)],
          ⟨(hend _).2 rfl, by dsimp; omega⟩, by omega⟩
      · right
        let j' : Fin B := ⟨cfg.inputPos.val, by omega⟩
        let eFin : Fin B := ⟨u.length + w.length, by omega⟩
        refine ⟨![j', eFin], ⟨⟨⟨(hend eFin).2 rfl, by dsimp [j', eFin]; omega⟩,
          by dsimp [j']; omega⟩, rfl⟩⟩

include hlt in
/-- Semantic characterization of `headPrevFormula`. -/
private theorem realize_headPrevFormula {headSame headOpp : L'.Relations 2} {t : Fin B}
    {pos : ℤ} (hb : |pos| + 1 < B) {sign : ℤ} (hsign : sign = 1 ∨ sign = -1)
    (hSame : ∀ a : Fin B, RelMap headSame ![t, a] ↔ pos = sign * (a : ℤ))
    (hOpp : ∀ a : Fin B, RelMap headOpp ![t, a] ↔ pos = -sign * (a : ℤ))
    (d : SignType) {V : Type*} (vT vA : V) (env : V → Fin B) (ht : env vT = t) :
    (headPrevFormula r headSame headOpp d vT vA).Realize env ↔
      pos + sign * (d : ℤ) = sign * (env vA : ℤ) := by
  have hb' : |pos| < (B : ℤ) - 1 := by omega
  rw [abs_lt] at hb'
  rcases d with _ | _ | _
  · -- `d = .zero`
    simp only [headPrevFormula, realize_rel₂, ht, hSame,
      SignType.zero_eq_zero, SignType.coe_zero, mul_zero, add_zero]
  · -- `d = .neg`
    simp only [headPrevFormula, Formula.realize_iExs, Formula.realize_inf,
      realize_succ hlt, realize_rel₂, Sum.elim_inl, Sum.elim_inr, ht, hSame,
      SignType.neg_eq_neg_one, SignType.coe_neg_one]
    constructor
    · rintro ⟨y, hsucc, hpos⟩
      rcases hsign with rfl | rfl <;> omega
    · intro hmove
      have haB : (env vA : ℕ) + 1 < B := by rcases hsign with rfl | rfl <;> omega
      refine ⟨![(⟨(env vA : ℕ) + 1, haB⟩ : Fin B)], rfl, ?_⟩
      dsimp
      rcases hsign with rfl | rfl <;> omega
  · -- `d = .pos`
    simp only [headPrevFormula, Formula.realize_sup, Formula.realize_inf,
      realize_isZero hlt, Formula.realize_iExs, realize_succ hlt, realize_rel₂,
      Sum.elim_inl, Sum.elim_inr, ht, hSame, hOpp,
      SignType.pos_eq_one, SignType.coe_one, mul_one]
    constructor
    · rintro (⟨ha0, y, hsucc, hpos⟩ | ⟨y, hsucc, hpos⟩)
      · rcases hsign with rfl | rfl <;> omega
      · rcases hsign with rfl | rfl <;> omega
    · intro hmove
      by_cases ha0 : (env vA : ℕ) = 0
      · left
        refine ⟨ha0, ![(⟨1, by omega⟩ : Fin B)], by dsimp; omega, ?_⟩
        dsimp
        rcases hsign with rfl | rfl <;> omega
      · right
        refine ⟨![(⟨(env vA : ℕ) - 1, by omega⟩ : Fin B)], by dsimp; omega, ?_⟩
        dsimp
        rcases hsign with rfl | rfl <;> omega

variable [Fintype State]

include hlt in
/-- Semantic characterization of `stateStepRHS` under `AgreesAt`. -/
theorem realize_stateStepRHS [DecidableEq State]
    {u w : List Bool} {cfg : Cfg m Bool State (u ++ w)} {t : Fin B}
    (hI : r.EncodesInput B u w) (hb : ∀ i : Fin m, |cfg.workTapePos i| < B) (hA : r.AgreesAt cfg t)
    (q' : Option State) {V : Type*} (vT : V) (env : V → Fin B) (ht : env vT = t) :
    (stateStepRHS r tm q' vT).Realize env ↔ (Feature.state q').Holds (tm.step cfg) := by
  simp only [stateStepRHS, Formula.realize_sup, Formula.realize_inf, Formula.realize_iSup,
    realize_rel₁, ht, hA.state,
    realize_sitFormula hlt hI hb hA _ vT env ht]
  rw [holds_step_state_iff tm q']
  refine or_congr ⟨fun ⟨h, hq⟩ => ⟨h, by split_ifs at hq with h' <;> simp_all⟩,
    fun ⟨h, hq⟩ => ⟨h, by simp [hq]⟩⟩ ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact exists_congr fun y => ⟨fun ⟨hq, hy⟩ => ⟨by split_ifs at hq with h' <;> simp_all, hy⟩,
    fun ⟨hq, hy⟩ => ⟨by simp [hq], hy⟩⟩

include hlt in
/-- Semantic characterization of `outStepRHS` under `AgreesAt`. -/
theorem realize_outStepRHS {u w : List Bool} {cfg : Cfg m Bool State (u ++ w)} {t : Fin B}
    (hI : r.EncodesInput B u w) (hb : ∀ i : Fin m, |cfg.workTapePos i| < B) (hA : r.AgreesAt cfg t)
    (o : OutView) {V : Type*} (vT : V) (env : V → Fin B) (ht : env vT = t) :
    (outStepRHS r tm o vT).Realize env ↔ (Feature.out o).Holds (tm.step cfg) := by
  classical
  simp only [outStepRHS, Formula.realize_sup, Formula.realize_inf, Formula.realize_iSup,
    realize_rel₁, ht, hA.state, hA.out,
    realize_sitFormula hlt hI hb hA _ vT env ht]
  rw [holds_step_out_iff tm o]
  refine or_congr Iff.rfl ?_
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
  exact exists_congr fun p =>
    ⟨fun ⟨⟨ho, hs⟩, hp⟩ => ⟨by split_ifs at ho with h' <;> simp_all, hs, hp⟩,
     fun ⟨ho, hs, hp⟩ => ⟨⟨by simp [ho], hs⟩, hp⟩⟩

include hlt in
/-- Semantic characterization of `inPosStepRHS` under `AgreesAt`. -/
theorem realize_inPosStepRHS {u w : List Bool} {cfg : Cfg m Bool State (u ++ w)} {t : Fin B}
    (hI : r.EncodesInput B u w) (hb : ∀ i : Fin m, |cfg.workTapePos i| < B) (hA : r.AgreesAt cfg t)
    {V : Type*} (vT vJ : V) (env : V → Fin B) (ht : env vT = t) :
    (inPosStepRHS r tm vT vJ).Realize env ↔ (Feature.inPos (env vJ : ℕ)).Holds (tm.step cfg) := by
  classical
  simp only [inPosStepRHS, Formula.realize_sup, Formula.realize_inf, Formula.realize_iSup,
    realize_rel₁, realize_rel₂, ht, hA.state, hA.inPos,
    realize_sitFormula hlt hI hb hA _ vT env ht,
    realize_inPosPrevFormula hlt hI.length_lt hI.endPos_iff hA _ vT vJ env ht]
  rcases hq : cfg.state with _ | q
  · simp [hq, not_holds_sit hq]
  · simp [holds_state, hq, holds_sit_iff_eq hq, holds_inPos, step_eq_apply tm hq,
      Action.apply_inputPos, val_moveInputPos_eq_moveInputPosNat]

include hlt in
/-- Semantic characterization of `headStepRHS` for either orientation `sign ∈ {.pos, .neg}`
under `AgreesAt`. -/
private theorem realize_headStepRHS {u w : List Bool} {cfg : Cfg m Bool State (u ++ w)} {t : Fin B}
    (hI : r.EncodesInput B u w) (hb : ∀ i : Fin m, |cfg.workTapePos i| + 1 < B)
    (hA : r.AgreesAt cfg t)
    (headSame headOpp : L'.Relations 2) (sign : SignType) (hsign : sign = .pos ∨ sign = .neg)
    (i : Fin m)
    (hSame : ∀ a' : Fin B, RelMap headSame ![t, a'] ↔ cfg.workTapePos i = (sign : ℤ) * (a' : ℤ))
    (hOpp : ∀ a' : Fin B, RelMap headOpp ![t, a'] ↔ cfg.workTapePos i = -(sign : ℤ) * (a' : ℤ))
    {V : Type*} (vT vA : V) (env : V → Fin B) (ht : env vT = t) :
    (headStepRHS r tm headSame headOpp sign i vT vA).Realize env ↔
      (Feature.head i ((sign : ℤ) * (env vA : ℤ))).Holds (tm.step cfg) := by
  classical
  have hb' : ∀ i : Fin m, |cfg.workTapePos i| < B := fun i => by have := hb i; omega
  have hsign' : (sign : ℤ) = 1 ∨ (sign : ℤ) = -1 := by rcases hsign with rfl | rfl <;> simp
  have hmul_coe : ∀ d : SignType, (sign : ℤ) * ((sign * d : SignType) : ℤ) = (d : ℤ) := by
    rcases hsign with rfl | rfl <;> rintro (_ | _ | _) <;> rfl
  simp only [headStepRHS, Formula.realize_sup, Formula.realize_inf, Formula.realize_iSup,
    realize_rel₁, realize_rel₂, ht, hA.state, hSame,
    realize_sitFormula hlt hI hb' hA _ vT env ht,
    realize_headPrevFormula hlt (hb i) hsign' hSame hOpp _ vT vA env ht,
    hmul_coe]
  rcases hq : cfg.state with _ | q
  · simp [hq, not_holds_sit hq]
  · simp [holds_state, hq, holds_sit_iff_eq hq, holds_head, step_eq_apply tm hq,
      Action.apply_workTapePos]

include hlt in
/-- Semantic characterization of `headStepRHS` (positive orientation) under `AgreesAt`. -/
theorem realize_headPosStepRHS {u w : List Bool} {cfg : Cfg m Bool State (u ++ w)} {t : Fin B}
    (hI : r.EncodesInput B u w) (hb : ∀ i : Fin m, |cfg.workTapePos i| + 1 < B)
    (hA : r.AgreesAt cfg t)
    (i : Fin m) {V : Type*} (vT vA : V) (env : V → Fin B) (ht : env vT = t) :
    (headStepRHS r tm (r.headPos i) (r.headNeg i) .pos i vT vA).Realize env ↔
      (Feature.head i (env vA : ℤ)).Holds (tm.step cfg) := by
  simpa using realize_headStepRHS hlt hI hb hA
    (r.headPos i) (r.headNeg i) .pos (Or.inl rfl) i
    (fun a' => by simpa using hA.headPos i a')
    (fun a' => by simpa using hA.headNeg i a') vT vA env ht

include hlt in
/-- Semantic characterization of `headStepRHS` (negative orientation) under `AgreesAt`. -/
theorem realize_headNegStepRHS {u w : List Bool} {cfg : Cfg m Bool State (u ++ w)} {t : Fin B}
    (hI : r.EncodesInput B u w) (hb : ∀ i : Fin m, |cfg.workTapePos i| + 1 < B)
    (hA : r.AgreesAt cfg t)
    (i : Fin m) {V : Type*} (vT vA : V) (env : V → Fin B) (ht : env vT = t) :
    (headStepRHS r tm (r.headNeg i) (r.headPos i) .neg i vT vA).Realize env ↔
      (Feature.head i (-(env vA : ℤ))).Holds (tm.step cfg) := by
  simpa using realize_headStepRHS hlt hI hb hA
    (r.headNeg i) (r.headPos i) .neg (Or.inr rfl) i
    (fun a' => by simpa using hA.headNeg i a')
    (fun a' => by simpa using hA.headPos i a') vT vA env ht

include hlt in
/-- Semantic characterization of `cellStepRHS` under `AgreesAt`. -/
theorem realize_cellStepRHS {u w : List Bool} {cfg : Cfg m Bool State (u ++ w)} {t : Fin B}
    (hI : r.EncodesInput B u w) (hb : ∀ i : Fin m, |cfg.workTapePos i| < B) (hA : r.AgreesAt cfg t)
    (i : Fin m) (s : Option Bool) (z : ℤ)
    (headSame : L'.Relations 2) (cellSame : Option Bool → L'.Relations 2)
    {V : Type*} (vT vA : V) (env : V → Fin B) (ht : env vT = t)
    (hhead : RelMap headSame ![t, env vA] ↔ (Feature.head i z).Holds cfg)
    (hcell : ∀ s', RelMap (cellSame s') ![t, env vA] ↔ (Feature.cell i z s').Holds cfg) :
    (cellStepRHS r tm headSame cellSame i s vT vA).Realize env ↔
      (Feature.cell i z s).Holds (tm.step cfg) := by
  classical
  simp only [cellStepRHS, Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
    Formula.realize_iSup, realize_rel₁, realize_rel₂, ht, hA.state, hhead, hcell,
    realize_sitFormula hlt hI hb hA _ vT env ht]
  rw [holds_step_cell_iff tm z s]
  refine or_congr Iff.rfl ?_
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
  exact exists_congr fun p =>
    ⟨fun ⟨⟨⟨hs, hsit⟩, hh⟩, hc⟩ => ⟨by split_ifs at hs with h' <;> simp_all, hsit, hh, hc⟩,
     fun ⟨hs, hsit, hh, hc⟩ => ⟨⟨⟨by simp [hs], hsit⟩, hh⟩, hc⟩⟩

include hlt in
/-- Semantic characterization of `initSentence`: it holds iff `AgreesAt` holds at `t = 0`. -/
theorem realize_initSentence [DecidableEq State] {input : List Bool} (hB1 : 1 < B) :
    (Fin B) ⊨ initSentence r tm ↔ r.AgreesAt (tm.initCfg input) (⟨0, by omega⟩ : Fin B) := by
  simp only [initSentence, realize_closeAll, Formula.realize_imp, Formula.realize_inf,
    Formula.realize_iInf, Formula.realize_iff, Formula.realize_iAlls, Formula.realize_iExs,
    realize_isZero hlt, realize_rel₁, realize_rel₂, realize_succ hlt,
    Sum.elim_inl, Sum.elim_inr]
  have h1_iff : ∀ j : Fin B,
      (∃ y : Fin 1 → Fin B, (y 0 : ℕ) = 0 ∧ (j : ℕ) = (y 0 : ℕ) + 1) ↔ (j : ℕ) = 1 := by
    intro j
    constructor
    · rintro ⟨y, h0, hj⟩; omega
    · intro hj
      exact ⟨![(⟨0, by omega⟩ : Fin B)], rfl, hj⟩
  constructor
  · intro h
    obtain ⟨⟨⟨hstate, hout⟩, hinPos⟩, hwork⟩ := h ![(⟨0, by omega⟩ : Fin B)] rfl
    refine ⟨fun q => ?_, fun o => ?_, fun j => ?_, fun i a => ?_, fun i a => ?_,
      fun i s a => ?_, fun i s a => ?_⟩
    · by_cases hq0 : q = some tm.q₀ <;>
        simpa [hq0, Feature.Holds, eq_comm] using hstate q
    · by_cases ho0 : o = .empty <;>
        simpa [ho0, Feature.Holds, OutView.ofList, eq_comm] using hout o
    · have hj := (hinPos ![j]).trans (h1_iff j)
      simpa [Feature.Holds, eq_comm] using hj
    · have ha := (hwork i ![a]).1.1
      simpa [Feature.Holds, eq_comm] using ha
    · have ha := (hwork i ![a]).1.2
      simpa [Feature.Holds, eq_comm] using ha
    · by_cases hs0 : s = none <;>
        simpa [hs0, Feature.Holds, eq_comm] using ((hwork i ![a]).2 s).1
    · by_cases hs0 : s = none <;>
        simpa [hs0, Feature.Holds, eq_comm] using ((hwork i ![a]).2 s).2
  · intro hA y hy0
    have hy : y 0 = ⟨0, by omega⟩ := Fin.ext hy0
    rw [hy]
    refine ⟨⟨⟨fun q => ?_, fun o => ?_⟩, fun yJ => ?_⟩, fun i yA => ⟨⟨?_, ?_⟩, fun s => ⟨?_, ?_⟩⟩⟩
    · rw [hA.state q]
      by_cases hq0 : q = some tm.q₀ <;>
        simp [hq0, Feature.Holds, eq_comm]
    · rw [hA.out o]
      by_cases ho0 : o = .empty <;>
        simp [ho0, Feature.Holds, OutView.ofList, eq_comm]
    · rw [hA.inPos (yJ 0), h1_iff (yJ 0)]
      simp [Feature.Holds, eq_comm]
    · rw [hA.headPos i (yA 0)]
      simp only [MultiTapeNTM.initCfg, Cfg.init, holds_head]
      omega
    · rw [hA.headNeg i (yA 0)]
      simp [Feature.Holds]
    · rw [hA.cellPos i s (yA 0)]
      by_cases hs0 : s = none <;>
        simp [hs0, Feature.Holds, eq_comm]
    · rw [hA.cellNeg i s (yA 0)]
      by_cases hs0 : s = none <;>
        simp [hs0, Feature.Holds, eq_comm]

end Semantics

end Cslib.Logic.FO
