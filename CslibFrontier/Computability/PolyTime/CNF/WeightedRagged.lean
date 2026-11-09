/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CNF.WeightedPlan
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Int
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Binary admission and exact refinement of ragged weighted rows

Rows retain their individual lengths, including zero, and every original variable and target.
Indices, positive weights and signed targets are binary; declared variable count is unary.
Admission checks declaration, strict positivity and the computed normalized demand. Conversion
to the existing writer caps indices before unary materialization, and is the identity on admitted
inputs. No zero-weight padding, new variables or altered equations are introduced.
This supplies the original-row encoding/refinement for [ChenJiangZhu2027], Section 7.1,
Theorem 7.1 (PDF pp. 23–24); `WeightedRaggedResources` composes the counting resources.
-/

public section

namespace Cslib.Logic.PL.WeightedRow.BinaryRagged

open Turing.MultiTapeTM ComputableInPolyTime
open BinaryNormalization

/-- Declared size and arbitrary explicit rows, each with its own occurrence-list length. -/
abbrev Input := ℕ × List BinaryNormalization.Input

/-- Binary variable index, polarity, and signed binary coefficient. -/
@[expose] def encEntry : Entry ↪ List Bool := encPair encNat (encPair encBool encIntBin)
/-- A variable-length row and its signed binary target. -/
@[expose] def encRow : BinaryNormalization.Input ↪ List Bool :=
  encPair (encList encEntry) encIntBin
/-- Unary declaration, framed ragged lists and complete binary indices/integers. -/
@[expose] def encInput : Input ↪ List Bool := encPair encUnary (encList encRow)
/-- The existing writer's encoding, after safe unary-index conversion. -/
abbrev encLegacy := encPair encUnary (encList BinaryNormalization.encInput)

/-- Source structural validity, without any common row-length condition. -/
@[expose] def WellFormed (x : Input) : Prop :=
  ∀ row ∈ x.2, ∀ e ∈ row.1, e.1 < x.1 ∧ 0 < e.2.2

/-- Check one occurrence against the declaration and the strict positive-weight requirement. -/
@[expose] def entryOK (q : ℕ × Entry) : Bool := decide (q.2.1 < q.1) && decide (0 < q.2.2.2)
/-- Check every occurrence in one row; an empty row passes structural validation. -/
@[expose] def rowOK (q : ℕ × BinaryNormalization.Input) : Bool :=
  q.2.1.all fun e => entryOK (q.1, e)
/-- Actual declaration and positive-weight admission. -/
@[expose] def shape (x : Input) : Bool := x.2.all fun row => rowOK (x.1, row)

theorem shape_iff (x : Input) : shape x = true ↔ WellFormed x := by
  simp only [shape, rowOK, entryOK, WellFormed, List.all_eq_true, Bool.and_eq_true,
    decide_eq_true_eq]

private theorem entryOK_polytime : ComputableInPolyTime entryOK
    (encPair encUnary encEntry) encBool := by
  have hn := unary_to_binary.comp (fst encUnary encEntry)
  have hi : ComputableInPolyTime (fun q : ℕ × Entry => q.2.1)
      (encPair encUnary encEntry) encNat := by unfold encEntry; fun_prop
  have hw : ComputableInPolyTime (fun q : ℕ × Entry => q.2.2.2)
      (encPair encUnary encEntry) encIntBin := by unfold encEntry; fun_prop
  exact bool_and' (binary_lt.comp (hi.prod hn))
    ((of_tidy ComputableTidilyInPolyTime.intBin_lt).comp ((const (0 : ℤ)).prod hw))

private theorem rowOK_polytime : ComputableInPolyTime rowOK
    (encPair encUnary encRow) encBool := by
  have hctx : ComputableInPolyTime (fun p : (ℕ × BinaryNormalization.Input) × Entry =>
      (p.1.1, p.2)) (encPair (encPair encUnary encRow) encEntry)
      (encPair encUnary encEntry) := by fun_prop
  exact allWithInput (by unfold encRow; fun_prop) (entryOK_polytime.comp hctx)

/-- Validation includes every binary index and positive coefficient. -/
@[fun_prop] theorem shape_polytime : ComputableInPolyTime shape encInput encBool := by
  have hctx : ComputableInPolyTime (fun p : Input × BinaryNormalization.Input => (p.1.1, p.2))
      (encPair encInput encRow) (encPair encUnary encRow) := by unfold encInput; fun_prop
  exact allWithInput (by unfold encInput; fun_prop) (rowOK_polytime.comp hctx)

/-- Saturate before unary conversion, so even a huge invalid binary index has polynomial cost. -/
@[expose] def recodeEntry (q : ℕ × Entry) : Entry := (min q.1 q.2.1, q.2.2)
/-- Safely recode the occurrences of one row and keep its signed target. -/
@[expose] def recodeRow (q : ℕ × BinaryNormalization.Input) : BinaryNormalization.Input :=
  (q.2.1.map fun e => recodeEntry (q.1, e), q.2.2)
/-- Total safe conversion to the existing encoding, preserving every occurrence and row. -/
@[expose] def recode (x : Input) : Input := (x.1, x.2.map fun row => recodeRow (x.1, row))

private theorem recodeEntry_polytime : ComputableInPolyTime recodeEntry
    (encPair encUnary encEntry) BinaryNormalization.encEntry := by
  unfold recodeEntry encEntry BinaryNormalization.encEntry
  exact (binary_min_unary' (by fun_prop) (by fun_prop)).prod (by fun_prop)

private theorem recodeRow_polytime : ComputableInPolyTime recodeRow
    (encPair encUnary encRow) BinaryNormalization.encInput := by
  have hctx : ComputableInPolyTime (fun p : (ℕ × BinaryNormalization.Input) × Entry =>
      (p.1.1, p.2)) (encPair (encPair encUnary encRow) encEntry)
      (encPair encUnary encEntry) := by fun_prop
  unfold recodeRow BinaryNormalization.encInput
  exact (mapWithInput (by unfold encRow; fun_prop) (recodeEntry_polytime.comp hctx)).prod
    (by unfold encRow; fun_prop)

/-- Actual binary-to-unary admission-path conversion has polynomial time and output storage. -/
@[fun_prop] theorem recode_polytime : ComputableInPolyTime recode encInput encLegacy := by
  have hctx : ComputableInPolyTime (fun p : Input × BinaryNormalization.Input => (p.1.1, p.2))
      (encPair encInput encRow) (encPair encUnary encRow) := by unfold encInput; fun_prop
  unfold recode encLegacy
  exact (show ComputableInPolyTime (fun x : Input => x.1) encInput encUnary from
    by unfold encInput; fun_prop).prod
    (mapWithInput (by unfold encInput; fun_prop) (recodeRow_polytime.comp hctx))

/-- Conversion changes no admitted data, including empty rows and signed targets. -/
theorem recode_eq {x : Input} (hx : WellFormed x) : recode x = x := by
  change (x.1, _) = x
  apply Prod.ext
  · rfl
  change x.2.map (fun row => recodeRow (x.1, row)) = x.2
  calc _ = x.2.map id := List.map_congr_left fun row hr => by
          apply Prod.ext
          · change row.1.map (fun e => recodeEntry (x.1, e)) = row.1
            calc _ = row.1.map id := List.map_congr_left fun e he => by
                    exact Prod.ext (min_eq_right (hx row hr e he).1.le) rfl
              _ = _ := List.map_id _
          · rfl
    _ = _ := List.map_id _

/-- Demand is computed on actual normalized rows, with interval contradictions handled by the
existing compiler. Invalid intervals have truncated demand zero. -/
@[expose] def bounded (d : ℕ) (x : Input) : Bool :=
  x.2.all fun row => decide ((BinaryNormalization.demand x.1 row).toNat ≤ d)

@[fun_prop] theorem bounded_polytime (d : ℕ) :
    ComputableInPolyTime (bounded d) encLegacy encBool := by
  have hn : ComputableInPolyTime (fun p : Input × BinaryNormalization.Input => p.1.1)
      (encPair encLegacy BinaryNormalization.encInput) encUnary := by unfold encLegacy; fun_prop
  have hr : ComputableInPolyTime (fun p : Input × BinaryNormalization.Input => p.2)
      (encPair encLegacy BinaryNormalization.encInput) BinaryNormalization.encInput := by fun_prop
  unfold bounded
  exact allWithInput (by unfold encLegacy; fun_prop)
    (binary_le.comp (((ComputableInPolyTime.intBin_toNat).comp
      (BinaryNormalization.demand_polytime hn hr)).prod (const d)))

/-- Admission computes structural and normalized-demand checks from the original binary input. -/
@[expose] def admit (d : ℕ) (x : Input) : Bool := shape x && bounded d (recode x)

@[fun_prop] theorem admit_polytime (d : ℕ) : ComputableInPolyTime (admit d) encInput encBool :=
  bool_and' shape_polytime ((bounded_polytime d).comp recode_polytime)

/-- Total framed binary parsing of every row and occurrence; canonicality is checked separately. -/
@[expose] def decoder : Decoder encInput :=
  Decoder.pair Decoder.unary (Decoder.list (Decoder.pair
    (Decoder.list (Decoder.pair Decoder.nat (Decoder.pair Decoder.bool Decoder.int))) Decoder.int))

/-- Accept exactly canonical byte encodings, rather than silently accepting malformed frames. -/
@[expose] def canonical (w : List Bool) : Bool := decide (encInput (decoder.decode w) = w)

@[fun_prop] theorem canonical_polytime : ComputableInPolyTime canonical encBits encBool := by
  have he := (of_tidy (ComputableTidilyInPolyTime.encode encInput)).comp
    decoder.computableInPolyTime
  exact (of_tidy (ComputableTidilyInPolyTime.decide_eq encBits)).comp (he.prod id')

/-- An actual canonical word parser with polynomial binary cost and independent output growth. -/
@[expose] def parse (w : List Bool) : Option Input :=
  if canonical w then some (decoder.decode w) else none

@[fun_prop] theorem parse_polytime : ComputableInPolyTime parse encBits (encOption encInput) := by
  unfold parse
  exact canonical_polytime.ite'
    (optionSome encInput |>.comp decoder.computableInPolyTime) (const none)

theorem parse_encode (x : Input) : parse (encInput x) = some x := by
  simp [parse, canonical, decoder.decode_enc]

/-- Accepted words are exactly the original input encoding, including canonical integer signs. -/
theorem parse_eq_some_iff (w : List Bool) (x : Input) :
    parse w = some x ↔ w = encInput x := by
  constructor
  · intro h
    unfold parse at h
    split_ifs at h with hw
    · have hd : decoder.decode w = x := Option.some.inj h
      have he : encInput (decoder.decode w) = w := of_decide_eq_true hw
      rw [hd] at he
      exact he.symm
  · rintro rfl
    exact parse_encode x

/-- Original signed occurrence sum on all declared variables. -/
@[expose] def rowValue {n : ℕ} (p : BinaryNormalization.Input) (σ : Fin n → Bool) : ℤ :=
  (p.1.map fun (i, (s, w)) => if BinaryPlan.assignment σ i = s then w else 0).sum

/-- The input equations, with no normalization or padding hidden in their semantics. -/
@[expose] def Holds (x : Input) (σ : Fin x.1 → Bool) : Prop :=
  ∀ row ∈ x.2, rowValue row σ = row.2

instance (x : Input) (σ : Fin x.1 → Bool) : Decidable (Holds x σ) :=
  inferInstanceAs (Decidable (∀ row ∈ x.2, rowValue row σ = row.2))

/-- Refine a checked list without padding or changing any index, coefficient or target. -/
@[expose] def refineRow (n : ℕ) (p : BinaryNormalization.Input)
    (h : ∀ e ∈ p.1, e.1 < n ∧ 0 < e.2.2) : Occurrences n p.1.length where
  var j := ⟨p.1[j.val].1, (h _ (List.getElem_mem j.isLt)).1⟩
  sign j := p.1[j.val].2.1
  weight j := p.1[j.val].2.2.toNat
  positive j := by
    have hp := (h _ (List.getElem_mem j.isLt)).2
    omega
  target := p.2

/-- Refinement serializes to the exact original list, including the empty list. -/
theorem ofOccurrences_refineRow (n : ℕ) (p : BinaryNormalization.Input)
    (h : ∀ e ∈ p.1, e.1 < n ∧ 0 < e.2.2) :
    ofOccurrences (refineRow n p h) = p := by
  apply Prod.ext
  · apply List.ext_getElem
    · simp [ofOccurrences]
    · intro i hi hj
      simp only [ofOccurrences, List.getElem_ofFn, refineRow]
      apply Prod.ext
      · rfl
      apply Prod.ext
      · rfl
      change (p.1[i].2.2.toNat : ℤ) = p.1[i].2.2
      have hp := (h _ (List.getElem_mem hj)).2
      omega
  · rfl

/-- Raw signed evaluation agrees with the positive occurrence model on the declared cube. -/
theorem rowValue_ofOccurrences {n m : ℕ} (R : Occurrences n m) (σ : Fin n → Bool) :
    rowValue (ofOccurrences R) σ = (R.value σ : ℤ) := by
  simp [rowValue, ofOccurrences, Occurrences.value, List.sum_ofFn, Nat.cast_sum,
    Nat.cast_ite, BinaryPlan.assignment]

/-- The admitted input has an exact dependent occurrence-family presentation. No padding is used. -/
theorem admitted_refinement {d : ℕ} {x : Input} (hx : admit d x = true) :
    ∃ (t : ℕ) (m : Fin t → ℕ) (R : (j : Fin t) → Occurrences x.1 (m j)),
      x.2 = (List.finRange t).map (fun j => ofOccurrences (R j)) ∧
      (∀ j, (R j).demand ≤ d) ∧
      ∀ σ, Holds x σ ↔ ∀ j, ((R j).value σ : ℤ) = (R j).target := by
  have ha : shape x = true ∧ bounded d (recode x) = true := by
    simpa only [admit, Bool.and_eq_true] using hx
  have hs : WellFormed x := (shape_iff x).mp ha.1
  have hb : bounded d x = true := by
    have := ha.2
    rwa [recode_eq hs] at this
  let R (j : Fin x.2.length) := refineRow x.1 x.2[j.val]
    (hs _ (List.getElem_mem j.isLt))
  have hR (j : Fin x.2.length) : ofOccurrences (R j) = x.2[j.val] :=
    ofOccurrences_refineRow _ _ _
  have hlist : x.2 = (List.finRange x.2.length).map (fun j => ofOccurrences (R j)) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      rw [List.getElem_map, List.getElem_finRange]
      change x.2[i] = ofOccurrences (R ⟨i, hi⟩)
      exact (hR ⟨i, hi⟩).symm
  refine ⟨x.2.length, fun j => x.2[j.val].1.length, R, hlist, ?_, ?_⟩
  · intro j
    have hbrow := (List.all_eq_true.mp hb) _ (List.getElem_mem j.isLt)
    have := of_decide_eq_true hbrow
    rw [← hR j, demand_toNat_ofOccurrences] at this
    exact this
  · intro σ
    constructor
    · intro h j
      have hv := h _ (List.getElem_mem j.isLt)
      rw [← hR j, rowValue_ofOccurrences] at hv
      exact hv
    · intro h row hr
      rw [hlist] at hr
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
      rw [rowValue_ofOccurrences]
      exact h j

/-- The actual constructor retains its two-query, variable, width and clause budget on admission. -/
theorem compile_admitted_budget {d : ℕ} {x : Input} (hx : admit d x = true) :
    BinaryPlan.WithinBudget x.1 d (BinaryPlan.compile d x.1 x.2) := by
  obtain ⟨t, m, R, hrows, hd, _⟩ := admitted_refinement hx
  rw [hrows]
  exact BinaryPlan.compile_withinBudget R hd

end Cslib.Logic.PL.WeightedRow.BinaryRagged
