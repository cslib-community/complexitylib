/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Fagin.Power
public import Complexity.Logics.FirstOrder.Encoding.Layout
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Frame

/-!
# Existential second-order layout of framed structure encodings

On the canonical power structure `(Fin B, v.powerStructure a B)` for a well-formed input
`a : EncodedStructure` with `(frame (encStructure a)).length < B`, the Cook–Levin tableau needs the
input tape word `u = frame (encStructure a)` and its length `u.length` as unary predicates on
`Fin B`.

Because `encStructure a = frame (encUnary a.1) ++ (a.2.flatMap frame)` and
`u = frame (encStructure a)`, every stage of the binary encoding is an application of
`Turing.MultiTapeTM.frame` at some starting offset `base`. We therefore axiomatize a single
stride-2 framing step (`FO.frameChunkSentence`) in first-order logic using the linear order
`powerLt` on `Fin B`:
* given a domain formula `inDom(j)` (`j < w.length`), a bit formula `inBit(j)` (`w[j] = true`), and
  a unary relation `baseRel` holding of `{base}`,
* a binary relation `mapRel(j, p)` tracks `p = base + 2 * j` for `j ≤ w.length`, writing `true` at
  `base + 2 * j` and `w[j]` at `base + 2 * j + 1` into `outBitRel`, and writing the terminator
  `false` at `base + 2 * w.length` while advancing `nextBaseRel` to `{base + 2 * w.length + 1}`.

Chaining `v.count + 1` instances of `frameChunkSentence` reconstructs `encStructure a` and its
length, and one final instance reconstructs `frame (encStructure a)` and its length.

## Main definitions

* `Cslib.Logic.FO.frameChunkSentence`: the first-order sentence axiomatizing a single stride-2
  framing step on `Fin B`.
* `Cslib.Logic.Vocabulary.inputVarLanguage`: the two unary relation symbols `uBitSym` and `uLenSym`
  representing the framed input word `u = frame (encStructure a)` and its length on `Fin B`.
* `Cslib.Logic.Vocabulary.layoutESOSentence`: the existential second-order sentence over
  `v.powerLanguage.sum inputVarLanguage` characterizing `u` and `u.length`.

## Main results

* `Cslib.Logic.FO.nextBase_and_getElem?_frame_of_realize_frameChunkSentence`,
  `Cslib.Logic.FO.realize_frameChunkSentence_of_canonical`: soundness and completeness of
  `frameChunkSentence` on `Fin B`.
* `Cslib.Logic.Vocabulary.realize_layoutESOSentence`: for well-formed `a` with
  `(frame (encStructure a)).length < B`, `v.layoutESOSentence` holds on `Fin B` iff `uLenSym` holds
  solely of `(frame (encStructure a)).length` and `uBitSym` agrees with `frame (encStructure a)`
  below `(frame (encStructure a)).length`.

## References

* [R. Fagin, *Generalized first-order spectra and polynomial-time recognizable sets*][Fagin1974]
* [N. Immerman, *Descriptive Complexity*][Immerman1999]
-/

@[expose] public section

universe u v

open FirstOrder Language Structure BoundedFormula Turing.MultiTapeTM

namespace Cslib.Logic

/-! ### Generic stride-2 framing sentence -/

namespace FO

variable {L' : Language.{u, v}}

/-- The first-order sentence axiomatizing a single stride-2 framing step on `Fin B`:
starting at `baseRel`, the binary relation `mapRel(j, p)` maps `j ≤ w.length` to `base + 2 * j`,
writes `[true, w[j]]` into `outBitRel` at `base + 2 * j` and `base + 2 * j + 1`, writes the
terminator `false` at `base + 2 * w.length`, and sets `nextBaseRel` to
`{base + 2 * w.length + 1}`. -/
noncomputable def frameChunkSentence (r : L'.Relations 2)
    (inDom inBit : L'.Formula (Fin 1))
    (baseRel nextBaseRel : L'.Relations 1) (mapRel : L'.Relations 2)
    (outBitRel : L'.Relations 1) : L'.Sentence :=
  -- 1. Functionality of `mapRel`: `mapRel(j, p₁) ∧ mapRel(j, p₂) → p₁ = p₂`
  closeAll (Fin 3) ((rel₂ mapRel 0 1 ⊓ rel₂ mapRel 0 2) ⟹ varEq 1 2) ⊓
  -- 2. Base step at `j = 0`: `mapRel(0, p) ↔ baseRel(p)`
  closeAll (Fin 2) (isZero r 0 ⟹ (rel₂ mapRel 0 1 ⇔ rel₁ baseRel 1)) ⊓
  -- 3. Inductive step for `j` in `inDom`:
  closeAll (Fin 1) (atVar inDom 0 ⟹
    Formula.iExs (Fin 4) (
      rel₂ mapRel (.inl 0) (.inr 0) ⊓
      succ r (.inr 0) (.inr 1) ⊓
      succ r (.inr 1) (.inr 2) ⊓
      succ r (.inl 0) (.inr 3) ⊓
      rel₂ mapRel (.inr 3) (.inr 2) ⊓
      rel₁ outBitRel (.inr 0) ⊓
      (rel₁ outBitRel (.inr 1) ⇔ atVar inBit (.inl 0)))) ⊓
  -- 4. Terminator step at the first element `j` outside `inDom`:
  closeAll (Fin 1) (isFirstOut r inDom 0 ⟹
    Formula.iExs (Fin 2) (
      rel₂ mapRel (.inl 0) (.inr 0) ⊓
      succ r (.inr 0) (.inr 1) ⊓
      ∼(rel₁ outBitRel (.inr 0)) ⊓
      Formula.iAlls (Fin 1) (rel₁ nextBaseRel (.inr 0) ⇔ varEq (.inr 0) (.inl (.inr 1)))))

section FinOrder

variable {B : ℕ} [L'.Structure (Fin B)] {r : L'.Relations 2}
  (hlt : ∀ x : Fin 2 → Fin B, RelMap r x ↔ x 0 < x 1)

omit [L'.Structure (Fin B)] in
private theorem exists_lt_iff_of_val_eq (S : (Fin 1 → Fin B) → Prop) {n : ℕ} (y : Fin B)
    (hy : (y : ℕ) = n) :
    (∃ h : n < B, S ![⟨n, h⟩]) ↔ S ![y] := by
  subst hy
  simp [y.2]

include hlt

/-- Soundness of `frameChunkSentence`: when `baseRel` holds solely of `base` and
`base + (frame w).length < B`, any realization of `frameChunkSentence` forces `nextBaseRel` to hold
solely of `base + (frame w).length` and `outBitRel` to agree with `frame w` on
`[base, base + (frame w).length)`. -/
theorem nextBase_and_getElem?_frame_of_realize_frameChunkSentence
    {inDom inBit : L'.Formula (Fin 1)}
    {baseRel nextBaseRel : L'.Relations 1} {mapRel : L'.Relations 2}
    {outBitRel : L'.Relations 1}
    {w : List Bool} {base : ℕ} (hbound : base + (frame w).length < B)
    (hdom : ∀ j : Fin B, inDom.Realize ![j] ↔ (j : ℕ) < w.length)
    (hbit : ∀ j : Fin B, (j : ℕ) < w.length → (inBit.Realize ![j] ↔ w[(j : ℕ)]? = some true))
    (hbase : ∀ z : Fin B, RelMap baseRel ![z] ↔ (z : ℕ) = base)
    (hreal : (frameChunkSentence r inDom inBit baseRel nextBaseRel mapRel outBitRel).Realize
      (Fin B)) :
    (∀ z : Fin B, RelMap nextBaseRel ![z] ↔ (z : ℕ) = base + (frame w).length) ∧
      (∀ p : Fin B, base ≤ (p : ℕ) → (p : ℕ) < base + (frame w).length →
        (RelMap outBitRel ![p] ↔ (frame w)[(p : ℕ) - base]? = some true)) := by
  have hlen : (frame w).length = 2 * w.length + 1 := length_frame w
  have hMB : w.length < B := by omega
  simp only [frameChunkSentence, Sentence.realize_inf, realize_closeAll,
    Formula.realize_imp, Formula.realize_inf, Formula.realize_iff, Formula.realize_not,
    Formula.realize_iExs, Formula.realize_iAlls, realize_rel₂, realize_rel₁,
    realize_varEq, realize_isZero hlt, realize_succ hlt, realize_atVar,
    realize_isFirstOut hlt hMB hdom, Sum.elim_inl, Sum.elim_inr] at hreal
  rcases hreal with ⟨⟨⟨hfunc, hzero⟩, hstep⟩, hend⟩
  have hmap : ∀ m ≤ w.length, ∀ (j p : Fin B), (j : ℕ) = m →
      (RelMap mapRel ![j, p] ↔ (p : ℕ) = base + 2 * m) := by
    intro m hm
    induction m with
    | zero => intro j p hj; simpa [hbase] using hzero ![j, p] hj
    | succ m ih =>
      intro j p hj
      let j₀ : Fin B := ⟨m, by omega⟩
      have hj₀ : (j₀ : ℕ) = m := rfl
      obtain ⟨y, ⟨⟨⟨⟨⟨hmap0, hs0⟩, hs1⟩, hsj⟩, hmap1⟩, _⟩, _⟩ :=
        hstep ![j₀] ((hdom j₀).2 (by omega))
      simp only [Matrix.cons_val_zero] at hmap0 hsj
      have hy0 : (y 0 : ℕ) = base + 2 * m := (ih (by omega) j₀ (y 0) rfl).1 hmap0
      have hy2 : (y 2 : ℕ) = base + 2 * (m + 1) := by omega
      rw [show y 3 = j from Fin.ext (by omega)] at hmap1
      refine ⟨fun hjp => ?_, fun hp => by rwa [show p = y 2 from Fin.ext (by omega)]⟩
      have heq : p = y 2 := hfunc ![j, p, y 2] ⟨hjp, hmap1⟩
      rw [heq, hy2]
  let jM : Fin B := ⟨w.length, hMB⟩
  obtain ⟨yEnd, ⟨⟨hmapEnd, hsEnd⟩, houtEnd⟩, hnextEnd⟩ := hend ![jM] rfl
  have hyEnd0 : (yEnd 0 : ℕ) = base + 2 * w.length :=
    (hmap w.length le_rfl jM (yEnd 0) rfl).1 hmapEnd
  have hyEnd1 : (yEnd 1 : ℕ) = base + (frame w).length := by omega
  refine ⟨fun z => by simpa [Fin.ext_iff, hyEnd1] using hnextEnd ![z], ?_⟩
  have hP : ∀ n, base ≤ n → n < base + (frame w).length →
      ((∃ h : n < B, RelMap outBitRel ![(⟨n, h⟩ : Fin B)]) ↔
        (frame w)[n - base]? = some true) := by
    refine (forall_getElem?_frame_iff w base _).2 ⟨?_, fun m hm => ?_⟩
    · rwa [exists_lt_iff_of_val_eq (RelMap outBitRel) (yEnd 0) hyEnd0]
    · let jm : Fin B := ⟨m, by omega⟩
      obtain ⟨y, ⟨⟨⟨⟨⟨hmap0, hs0⟩, hs1⟩, _⟩, _⟩, hout0⟩, hout1⟩ :=
        hstep ![jm] ((hdom jm).2 hm)
      have hy0 : (y 0 : ℕ) = base + 2 * m := (hmap m (by omega) jm (y 0) rfl).1 hmap0
      have hy1 : (y 1 : ℕ) = base + 2 * m + 1 := by omega
      rw [exists_lt_iff_of_val_eq (RelMap outBitRel) (y 0) hy0,
        exists_lt_iff_of_val_eq (RelMap outBitRel) (y 1) hy1, ← hbit jm hm]
      exact ⟨hout0, hout1⟩
  intro p hlo hhi
  simpa [p.2] using hP (p : ℕ) hlo hhi

/-- Completeness of `frameChunkSentence`: the canonical stride-2 relation
`mapRel(j, p) ↔ j ≤ w.length ∧ p = base + 2 * j` satisfies `frameChunkSentence` whenever
`baseRel` is `{base}`, `nextBaseRel` is `{base + (frame w).length}`, and `outBitRel` agrees with
`frame w` on `[base, base + (frame w).length)`. -/
theorem realize_frameChunkSentence_of_canonical
    {inDom inBit : L'.Formula (Fin 1)}
    {baseRel nextBaseRel : L'.Relations 1} {mapRel : L'.Relations 2}
    {outBitRel : L'.Relations 1}
    {w : List Bool} {base : ℕ} (hbound : base + (frame w).length < B)
    (hdom : ∀ j : Fin B, inDom.Realize ![j] ↔ (j : ℕ) < w.length)
    (hbit : ∀ j : Fin B, (j : ℕ) < w.length → (inBit.Realize ![j] ↔ w[(j : ℕ)]? = some true))
    (hbase : ∀ z : Fin B, RelMap baseRel ![z] ↔ (z : ℕ) = base)
    (hnext : ∀ z : Fin B, RelMap nextBaseRel ![z] ↔ (z : ℕ) = base + (frame w).length)
    (hmap : ∀ j p : Fin B,
      RelMap mapRel ![j, p] ↔ (j : ℕ) ≤ w.length ∧ (p : ℕ) = base + 2 * (j : ℕ))
    (hout : ∀ p : Fin B, base ≤ (p : ℕ) → (p : ℕ) < base + (frame w).length →
      (RelMap outBitRel ![p] ↔ (frame w)[(p : ℕ) - base]? = some true)) :
    (frameChunkSentence r inDom inBit baseRel nextBaseRel mapRel outBitRel).Realize (Fin B) := by
  have hlen : (frame w).length = 2 * w.length + 1 := length_frame w
  have hMB : w.length < B := by omega
  simp only [frameChunkSentence, Sentence.realize_inf, realize_closeAll,
    Formula.realize_imp, Formula.realize_inf, Formula.realize_iff, Formula.realize_not,
    Formula.realize_iExs, Formula.realize_iAlls, realize_rel₂, realize_rel₁,
    realize_varEq, realize_isZero hlt, realize_succ hlt, realize_atVar,
    realize_isFirstOut hlt hMB hdom, Sum.elim_inl, Sum.elim_inr]
  refine ⟨⟨⟨fun v ⟨h1, h2⟩ => ?_, fun v hv0 => ?_⟩, fun v hv => ?_⟩, fun v hv => ?_⟩
  · rw [hmap] at h1 h2; exact Fin.ext (by omega)
  · rw [hmap, hbase, hv0]; omega
  · have hj : (v 0 : ℕ) < w.length := (hdom (v 0)).1 hv
    let p0 : Fin B := ⟨base + 2 * (v 0 : ℕ), by omega⟩
    let p1 : Fin B := ⟨base + 2 * (v 0 : ℕ) + 1, by omega⟩
    let p2 : Fin B := ⟨base + 2 * ((v 0 : ℕ) + 1), by omega⟩
    let j1 : Fin B := ⟨(v 0 : ℕ) + 1, by omega⟩
    have hp0 : (p0 : ℕ) = base + 2 * (v 0 : ℕ) := rfl
    have hp1 : (p1 : ℕ) = base + 2 * (v 0 : ℕ) + 1 := rfl
    refine ⟨![p0, p1, p2, j1], ⟨⟨⟨⟨⟨⟨?_, rfl⟩, ?_⟩, rfl⟩, ?_⟩, ?_⟩, ?_⟩⟩
    · change RelMap mapRel ![v 0, p0]; rw [hmap]; exact ⟨by omega, rfl⟩
    · change base + 2 * ((v 0 : ℕ) + 1) = (base + 2 * (v 0 : ℕ) + 1) + 1; omega
    · change RelMap mapRel ![j1, p2]; rw [hmap]; exact ⟨by change (v 0 : ℕ) + 1 ≤ _; omega, rfl⟩
    · change RelMap outBitRel ![p0]
      rw [hout p0 (by omega) (by omega)]; simpa [p0] using getElem?_frame_two_mul hj
    · change RelMap outBitRel ![p1] ↔ inBit.Realize ![v 0]
      rw [hbit (v 0) hj, hout p1 (by omega) (by omega),
        show (p1 : ℕ) - base = 2 * (v 0 : ℕ) + 1 by omega, getElem?_frame_two_mul_add_one hj]
  · let p0 : Fin B := ⟨base + 2 * w.length, by omega⟩
    have hp0 : (p0 : ℕ) = base + 2 * w.length := rfl
    refine ⟨![p0, ⟨base + (frame w).length, hbound⟩], ⟨⟨⟨?_, ?_⟩, ?_⟩, fun z => ?_⟩⟩
    · change RelMap mapRel ![v 0, p0]; rw [hmap, hv]; exact ⟨le_rfl, rfl⟩
    · change base + (frame w).length = (base + 2 * w.length) + 1; omega
    · change ¬RelMap outBitRel ![p0]
      rw [hout p0 (by omega) (by omega)]; simpa [p0] using getElem?_frame_two_mul_length w
    · change RelMap nextBaseRel ![z 0] ↔ z 0 = ⟨base + (frame w).length, hbound⟩
      rw [hnext, Fin.ext_iff]

end FinOrder

end FO

/-! ### Prefix decomposition of `encStructure a` -/

namespace Vocabulary

variable {L : Language.{u, v}} (v : Vocabulary L)

/-- The prefix of `encStructure a` consisting of `frame (encUnary a.1)` followed by the framed
truth tables of the first `m` relation symbols of `v`. -/
def encStructurePrefix (a : EncodedStructure) (m : ℕ) : List Bool :=
  frame (encUnary a.1) ++
    (((List.ofFn fun i : Fin v.count => v.table a (v.symbol i)).take m).flatMap frame)

@[simp]
theorem encStructurePrefix_zero (a : EncodedStructure) :
    v.encStructurePrefix a 0 = frame (encUnary a.1) := by
  simp [encStructurePrefix]

theorem encStructurePrefix_succ (a : EncodedStructure) (i : Fin v.count) :
    v.encStructurePrefix a (i.1 + 1) =
      v.encStructurePrefix a i.1 ++ frame (v.table a (v.symbol i)) := by
  simp only [encStructurePrefix]
  have htake :
      (List.ofFn fun j : Fin v.count => v.table a (v.symbol j)).take (i.1 + 1) =
        (List.ofFn fun j : Fin v.count => v.table a (v.symbol j)).take i.1 ++
          [v.table a (v.symbol i)] := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by simp [i.2]), List.getElem_ofFn]
    simp
  rw [htake, List.flatMap_append, List.flatMap_singleton, List.append_assoc]

theorem encStructurePrefix_count {a : EncodedStructure} (ha : v.WellFormed a) :
    v.encStructurePrefix a v.count = encStructure a := by
  simp only [encStructurePrefix, encStructure, encPair_apply, encList]
  congr 1
  have htables : (List.ofFn fun i : Fin v.count => v.table a (v.symbol i)) = a.2 := by
    refine List.ext_getElem (by simp [ha.1]) fun i hi hi' => ?_
    simp only [List.getElem_ofFn, table, index, Equiv.symm_apply_apply]
    exact List.getD_eq_getElem a.2 [] hi'
  rw [List.take_of_length_le (by simp), htables]
  rfl

/-- The prefix through the first `m` tables ends where the table at position `m` starts
(`Cslib.Logic.tableStart`). -/
theorem length_encStructurePrefix {a : EncodedStructure} {m : ℕ} (hm : m ≤ a.2.length)
    (hmc : m ≤ v.count) : (v.encStructurePrefix a m).length = tableStart a m := by
  have htake : (List.ofFn fun i : Fin v.count => v.table a (v.symbol i)).take m = a.2.take m := by
    refine List.ext_getElem (by simp only [List.length_take, List.length_ofFn]; omega)
      fun i hi hi' => ?_
    simp only [List.getElem_take, List.getElem_ofFn, table, index, Equiv.symm_apply_apply]
    exact List.getD_eq_getElem a.2 [] (by simp only [List.length_take] at hi'; omega)
  rw [encStructurePrefix, htake, List.length_append, length_frame, length_flatMap_frame,
    tableStart, encUnary_apply, List.length_replicate]

private theorem length_encStructurePrefix_le (a : EncodedStructure) {m : ℕ} (hm : m ≤ v.count) :
    (v.encStructurePrefix a m).length ≤ (v.encStructurePrefix a v.count).length := by
  simp only [encStructurePrefix, List.length_append]
  exact Nat.add_le_add_left (((List.take_sublist_take_left hm).flatMap frame).length_le) _

private theorem getElem?_encStructure_of_lt_prefix {a : EncodedStructure} (ha : v.WellFormed a)
    {m k : ℕ} (hk : k < (v.encStructurePrefix a m).length) :
    (encStructure a)[k]? = (v.encStructurePrefix a m)[k]? := by
  rw [← v.encStructurePrefix_count ha]
  have hsub : v.encStructurePrefix a v.count =
      v.encStructurePrefix a m ++
        ((List.ofFn fun i : Fin v.count => v.table a (v.symbol i)).drop m |>.flatMap frame) := by
    simp only [encStructurePrefix, List.append_assoc, ← List.flatMap_append]
    congr 2
    rw [List.take_append_drop, List.take_of_length_le (by simp)]
  rw [hsub, List.getElem?_append_left hk]

/-! ### The input variable language and layout ESO sentence -/

/-- The language of the two unary relations exposed by `layoutESOSentence` to the Cook–Levin
tableau:
* `false` (`uBitSym`): bit `p` of `u = frame (encStructure a)`, and
* `true` (`uLenSym`): the singleton `{u.length}`. -/
abbrev inputVarLanguage : Language.{0, 0} :=
  ESO.varLanguage (fun _ : Bool => 1)

/-- The unary relation symbol `uBit(p)` in `inputVarLanguage`. -/
def uBitSym : inputVarLanguage.Relations 1 :=
  ⟨false, rfl⟩

/-- The unary relation symbol `uLen(p)` in `inputVarLanguage`. -/
def uLenSym : inputVarLanguage.Relations 1 :=
  ⟨true, rfl⟩

/-- The index type of internal relation variables quantified by `v.layoutESOSentence`:
* `.inl (.inl m)` (`m : Fin (v.count + 2)`): unary `base_m`,
* `.inl (.inr ())`: unary `rawBit`,
* `.inr (.inl m)` (`m : Fin (v.count + 1)`): binary `chunkMap_m`,
* `.inr (.inr ())`: binary `outerMap`. -/
abbrev LayoutVar (count : ℕ) : Type :=
  (Fin (count + 2) ⊕ Unit) ⊕ (Fin (count + 1) ⊕ Unit)

/-- The arities of `LayoutVar`: `1` on the left summand and `2` on the right summand. -/
def layoutArity (count : ℕ) : LayoutVar count → ℕ
  | .inl _ => 1
  | .inr _ => 2

/-- The combined language of `v.layoutESOSentence`'s first-order matrix. -/
abbrev layoutMatrixLanguage : Language.{0, 0} :=
  (v.powerLanguage.sum inputVarLanguage).sum (ESO.varLanguage (layoutArity v.count))

/-- Binary `<` inside `v.layoutMatrixLanguage`. -/
def layoutLt : v.layoutMatrixLanguage.Relations 2 :=
  .inl (.inl v.powerLt)

/-- Unary `< n` inside `v.layoutMatrixLanguage`. -/
def layoutIsElem : v.layoutMatrixLanguage.Relations 1 :=
  .inl (.inl v.powerIsElem)

/-- Unary `< n ^ v.arity i` inside `v.layoutMatrixLanguage`. -/
def layoutInTable (i : Fin v.count) : v.layoutMatrixLanguage.Relations 1 :=
  .inl (.inl (v.powerInTable i))

/-- Unary relation table bit `i` inside `v.layoutMatrixLanguage`. -/
def layoutTableBit (i : Fin v.count) : v.layoutMatrixLanguage.Relations 1 :=
  .inl (.inl (v.powerTableBit i))

/-- Unary `uBit` inside `v.layoutMatrixLanguage`. -/
def layoutUBit : v.layoutMatrixLanguage.Relations 1 :=
  .inl (.inr uBitSym)

/-- Unary `uLen` inside `v.layoutMatrixLanguage`. -/
def layoutULen : v.layoutMatrixLanguage.Relations 1 :=
  .inl (.inr uLenSym)

/-- Unary `base_m` (`m : Fin (v.count + 2)`) inside `v.layoutMatrixLanguage`. -/
def layoutBase (m : Fin (v.count + 2)) : v.layoutMatrixLanguage.Relations 1 :=
  .inr ⟨.inl (.inl m), rfl⟩

/-- Unary `rawBit` inside `v.layoutMatrixLanguage`. -/
def layoutRawBit : v.layoutMatrixLanguage.Relations 1 :=
  .inr ⟨.inl (.inr ()), rfl⟩

/-- Binary `chunkMap_m` (`m : Fin (v.count + 1)`) inside `v.layoutMatrixLanguage`. -/
def layoutChunkMap (m : Fin (v.count + 1)) : v.layoutMatrixLanguage.Relations 2 :=
  .inr ⟨.inr (.inl m), rfl⟩

/-- Binary `outerMap` inside `v.layoutMatrixLanguage`. -/
def layoutOuterMap : v.layoutMatrixLanguage.Relations 2 :=
  .inr ⟨.inr (.inr ()), rfl⟩

/-- The domain formula `j < rawLen` for the outer framing step
(`base_{v.count + 1}` is `rawLen`). -/
noncomputable def layoutInRaw : v.layoutMatrixLanguage.Formula (Fin 1) :=
  Formula.iExs (Fin 1) (FO.rel₁ (v.layoutBase (Fin.last (v.count + 1))) (.inr 0) ⊓
    FO.lt v.layoutLt (.inl 0) (.inr 0))

/-- The first-order matrix of `v.layoutESOSentence`:
1. `base_0` holds solely of `0`,
2. chunk `0` frames `encUnary a.1` (`inDom = powerIsElem`, `inBit = ⊤`) from `base_0` to `base_1`
   into `rawBit`,
3. for each `i : Fin v.count`, chunk `i + 1` frames table `i` (`inDom = powerInTable i`,
   `inBit = powerTableBit i`) from `base_{i + 1}` to `base_{i + 2}` into `rawBit`, and
4. the outer chunk frames `encStructure a` (`inDom = layoutInRaw`, `inBit = rawBit`) from `base_0`
   to `uLen` into `uBit`. -/
noncomputable def layoutMatrix : v.layoutMatrixLanguage.Sentence :=
  FO.closeAll (Fin 1) (FO.rel₁ (v.layoutBase 0) 0 ⇔ FO.isZero v.layoutLt 0) ⊓
  FO.frameChunkSentence v.layoutLt (FO.rel₁ v.layoutIsElem 0) ⊤
    (v.layoutBase 0) (v.layoutBase 1) (v.layoutChunkMap 0) v.layoutRawBit ⊓
  (Formula.iInf fun i : Fin v.count =>
    FO.frameChunkSentence v.layoutLt
      (FO.rel₁ (v.layoutInTable i) 0) (FO.rel₁ (v.layoutTableBit i) 0)
      (v.layoutBase i.succ.castSucc) (v.layoutBase i.succ.succ)
      (v.layoutChunkMap i.succ) v.layoutRawBit) ⊓
  FO.frameChunkSentence v.layoutLt v.layoutInRaw (FO.rel₁ v.layoutRawBit 0)
    (v.layoutBase 0) v.layoutULen v.layoutOuterMap v.layoutUBit

/-- The existential second-order sentence over `v.powerLanguage.sum inputVarLanguage` that forces
`uLenSym` to hold solely of `(frame (encStructure a)).length` and `uBitSym` to agree with
`frame (encStructure a)` below `(frame (encStructure a)).length`. -/
noncomputable def layoutESOSentence : ESO.Sentence (v.powerLanguage.sum inputVarLanguage) where
  Var := LayoutVar v.count
  arity := layoutArity v.count
  matrix := v.layoutMatrix

private theorem length_frame_encUnary_lt {a : EncodedStructure} (ha : v.WellFormed a) {B : ℕ}
    (hB : (frame (encStructure a)).length < B) :
    0 + (frame (encUnary a.1)).length < B := by
  have h1 := v.length_encStructurePrefix_le a (Nat.zero_le v.count)
  have h2 := length_frame (encStructure a)
  rw [v.encStructurePrefix_zero, v.encStructurePrefix_count ha] at h1
  omega

private theorem length_prefix_add_frame_table_lt {a : EncodedStructure} (ha : v.WellFormed a)
    {B : ℕ} (hB : (frame (encStructure a)).length < B) (idx : Fin v.count) :
    (v.encStructurePrefix a idx.1).length + (frame (v.table a (v.symbol idx))).length < B := by
  have h1 := v.length_encStructurePrefix_le a (by omega : idx.1 + 1 ≤ v.count)
  have h2 := length_frame (encStructure a)
  rw [v.encStructurePrefix_count ha] at h1
  rw [← List.length_append, ← v.encStructurePrefix_succ a idx]
  omega

private theorem realize_layoutIsElem_iff (a : EncodedStructure) (B : ℕ)
    (I_in : ∀ b : Bool, Set (Fin ((fun _ : Bool => 1) b) → Fin B))
    (R : ∀ i : LayoutVar v.count, Set (Fin (layoutArity v.count i) → Fin B)) (j : Fin B) :
    (letI := v.powerStructure a B;
      letI := ESO.varLanguage.structure (arity := fun _ : Bool => 1) I_in;
      letI := ESO.varLanguage.structure (arity := layoutArity v.count) R;
      (FO.rel₁ v.layoutIsElem (0 : Fin 1)).Realize ![j]) ↔ (j : ℕ) < (encUnary a.1).length := by
  let _ := v.powerStructure a B
  let _ := ESO.varLanguage.structure (arity := fun _ : Bool => 1) I_in
  let _ := ESO.varLanguage.structure (arity := layoutArity v.count) R
  rw [FO.realize_rel₁]; simp [encUnary_apply]; rfl

private theorem realize_top_iff_getElem?_encUnary (a : EncodedStructure) (B : ℕ)
    (I_in : ∀ b : Bool, Set (Fin ((fun _ : Bool => 1) b) → Fin B))
    (R : ∀ i : LayoutVar v.count, Set (Fin (layoutArity v.count i) → Fin B))
    (j : Fin B) (hj : (j : ℕ) < (encUnary a.1).length) :
    (letI := v.powerStructure a B;
      letI := ESO.varLanguage.structure (arity := fun _ : Bool => 1) I_in;
      letI := ESO.varLanguage.structure (arity := layoutArity v.count) R;
      (⊤ : v.layoutMatrixLanguage.Formula (Fin 1)).Realize ![j]) ↔
      (encUnary a.1)[(j : ℕ)]? = some true := by
  let _ := v.powerStructure a B
  let _ := ESO.varLanguage.structure (arity := fun _ : Bool => 1) I_in
  let _ := ESO.varLanguage.structure (arity := layoutArity v.count) R
  simp only [Formula.realize_top, true_iff, encUnary_apply]
  rw [List.getElem?_eq_getElem (by simpa using hj), List.getElem_replicate]

private theorem realize_layoutInTable_iff {a : EncodedStructure} (ha : v.WellFormed a) (B : ℕ)
    (I_in : ∀ b : Bool, Set (Fin ((fun _ : Bool => 1) b) → Fin B))
    (R : ∀ i : LayoutVar v.count, Set (Fin (layoutArity v.count i) → Fin B))
    (idx : Fin v.count) (j : Fin B) :
    (letI := v.powerStructure a B;
      letI := ESO.varLanguage.structure (arity := fun _ : Bool => 1) I_in;
      letI := ESO.varLanguage.structure (arity := layoutArity v.count) R;
      (FO.rel₁ (v.layoutInTable idx) (0 : Fin 1)).Realize ![j]) ↔
      (j : ℕ) < (v.table a (v.symbol idx)).length := by
  let _ := v.powerStructure a B
  let _ := ESO.varLanguage.structure (arity := fun _ : Bool => 1) I_in
  let _ := ESO.varLanguage.structure (arity := layoutArity v.count) R
  rw [FO.realize_rel₁, Vocabulary.WellFormed.length_table v ha (v.symbol idx)]
  exact v.relMap_powerInTable a B idx ![j]

private theorem realize_layoutTableBit_iff {a : EncodedStructure} (ha : v.WellFormed a) (B : ℕ)
    (I_in : ∀ b : Bool, Set (Fin ((fun _ : Bool => 1) b) → Fin B))
    (R : ∀ i : LayoutVar v.count, Set (Fin (layoutArity v.count i) → Fin B))
    (idx : Fin v.count) (j : Fin B) (hj : (j : ℕ) < (v.table a (v.symbol idx)).length) :
    (letI := v.powerStructure a B;
      letI := ESO.varLanguage.structure (arity := fun _ : Bool => 1) I_in;
      letI := ESO.varLanguage.structure (arity := layoutArity v.count) R;
      (FO.rel₁ (v.layoutTableBit idx) (0 : Fin 1)).Realize ![j]) ↔
      (v.table a (v.symbol idx))[(j : ℕ)]? = some true := by
  let _ := v.powerStructure a B
  let _ := ESO.varLanguage.structure (arity := fun _ : Bool => 1) I_in
  let _ := ESO.varLanguage.structure (arity := layoutArity v.count) R
  have hlen_table := Vocabulary.WellFormed.length_table v ha (v.symbol idx)
  rw [FO.realize_rel₁]
  change ((j : ℕ) < a.1 ^ (v.symbol idx).1 ∧
    (v.table a (v.symbol idx)).getD (j : ℕ) false = true) ↔ _
  rw [← hlen_table, and_iff_right hj, List.getD_eq_getElem _ _ hj,
    List.getElem?_eq_getElem hj, Option.some.injEq]

private theorem realize_layoutInRaw_iff (a : EncodedStructure) {B : ℕ}
    (hB : (frame (encStructure a)).length < B)
    (I_in : ∀ b : Bool, Set (Fin ((fun _ : Bool => 1) b) → Fin B))
    (R : ∀ i : LayoutVar v.count, Set (Fin (layoutArity v.count i) → Fin B))
    (hbase_last : letI := v.powerStructure a B;
      letI := ESO.varLanguage.structure (arity := fun _ : Bool => 1) I_in;
      letI := ESO.varLanguage.structure (arity := layoutArity v.count) R;
      ∀ z : Fin B, RelMap (v.layoutBase (Fin.last (v.count + 1))) ![z] ↔
        (z : ℕ) = (encStructure a).length)
    (j : Fin B) :
    (letI := v.powerStructure a B;
      letI := ESO.varLanguage.structure (arity := fun _ : Bool => 1) I_in;
      letI := ESO.varLanguage.structure (arity := layoutArity v.count) R;
      v.layoutInRaw.Realize ![j]) ↔ (j : ℕ) < (encStructure a).length := by
  let _ := v.powerStructure a B
  let _ := ESO.varLanguage.structure (arity := fun _ : Bool => 1) I_in
  let _ := ESO.varLanguage.structure (arity := layoutArity v.count) R
  have hrawB : (encStructure a).length < B := by have := length_frame (encStructure a); omega
  have hlt : ∀ x : Fin 2 → Fin B, RelMap v.layoutLt x ↔ x 0 < x 1 := fun _ => Iff.rfl
  simp only [layoutInRaw, Formula.realize_iExs, Formula.realize_inf,
    FO.realize_rel₁, FO.realize_lt hlt, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero]
  refine ⟨fun ⟨y, hy, hjy⟩ => ?_, fun hj => ⟨![⟨(encStructure a).length, hrawB⟩],
    (hbase_last _).2 rfl, by simpa [Fin.lt_def] using hj⟩⟩
  have hy' := (hbase_last (y 0)).1 hy
  rw [Fin.lt_def] at hjy; omega

private theorem realize_layoutMatrix_sound {a : EncodedStructure} (ha : v.WellFormed a) {B : ℕ}
    (hB : (frame (encStructure a)).length < B)
    (I_in : ∀ b : Bool, Set (Fin ((fun _ : Bool => 1) b) → Fin B))
    (R : ∀ i : LayoutVar v.count, Set (Fin (layoutArity v.count i) → Fin B))
    (hR : (letI := v.powerStructure a B;
      letI := ESO.varLanguage.structure (arity := fun _ : Bool => 1) I_in;
      letI := ESO.varLanguage.structure (arity := layoutArity v.count) R;
      v.layoutMatrix.Realize (Fin B))) :
    (∀ z : Fin B, ![z] ∈ I_in true ↔ (z : ℕ) = (frame (encStructure a)).length) ∧
      (∀ p : Fin B, (p : ℕ) < (frame (encStructure a)).length →
        (![p] ∈ I_in false ↔ (frame (encStructure a))[(p : ℕ)]? = some true)) := by
  let _ := v.powerStructure a B
  let _ := ESO.varLanguage.structure (arity := fun _ : Bool => 1) I_in
  let _ := ESO.varLanguage.structure (arity := layoutArity v.count) R
  have hlt : ∀ x : Fin 2 → Fin B, RelMap v.layoutLt x ↔ x 0 < x 1 := fun _ => Iff.rfl
  simp only [layoutMatrix, Sentence.realize_inf, FO.realize_closeAll,
    Formula.realize_iff, FO.realize_rel₁, FO.realize_isZero hlt] at hR
  rcases hR with ⟨⟨⟨hbase0, hchunk0⟩, hchunks⟩, houter⟩
  rw [Sentence.Realize, Formula.realize_iInf] at hchunks
  have hbase0' : ∀ z : Fin B, RelMap (v.layoutBase 0) ![z] ↔ (z : ℕ) = 0 := fun z => hbase0 ![z]
  have hprefix : ∀ (m : ℕ) (hm : m ≤ v.count),
      (∀ z : Fin B, RelMap (v.layoutBase ⟨m + 1, by omega⟩) ![z] ↔
        (z : ℕ) = (v.encStructurePrefix a m).length) ∧
      (∀ p : Fin B, (p : ℕ) < (v.encStructurePrefix a m).length →
        (RelMap v.layoutRawBit ![p] ↔ (v.encStructurePrefix a m)[(p : ℕ)]? = some true)) := by
    intro m hm
    induction m with
    | zero =>
      obtain ⟨hnext, hout⟩ :=
        FO.nextBase_and_getElem?_frame_of_realize_frameChunkSentence hlt
          (v.length_frame_encUnary_lt ha hB) (v.realize_layoutIsElem_iff a B I_in R)
          (v.realize_top_iff_getElem?_encUnary a B I_in R) hbase0' hchunk0
      simp only [Nat.zero_add, Nat.sub_zero, ← v.encStructurePrefix_zero a] at hnext hout
      exact ⟨hnext, fun p hp => hout p (Nat.zero_le _) hp⟩
    | succ m ih =>
      let idx : Fin v.count := ⟨m, by omega⟩
      obtain ⟨hbase_m, hout_m⟩ := ih (by omega)
      have hsucc_eq := v.encStructurePrefix_succ a idx
      obtain ⟨hnext, hout⟩ :=
        FO.nextBase_and_getElem?_frame_of_realize_frameChunkSentence hlt
          (v.length_prefix_add_frame_table_lt ha hB idx)
          (v.realize_layoutInTable_iff ha B I_in R idx)
          (v.realize_layoutTableBit_iff ha B I_in R idx) hbase_m (hchunks idx)
      refine ⟨fun z => ?_, fun p hp => ?_⟩
      · change RelMap (v.layoutBase idx.succ.succ) ![z] ↔
          (z : ℕ) = (v.encStructurePrefix a (idx.1 + 1)).length
        rw [hsucc_eq, List.length_append]; exact hnext z
      · change (p : ℕ) < (v.encStructurePrefix a (idx.1 + 1)).length at hp
        change RelMap v.layoutRawBit ![p] ↔
          (v.encStructurePrefix a (idx.1 + 1))[(p : ℕ)]? = some true
        rw [hsucc_eq] at hp ⊢
        rcases lt_or_ge (p : ℕ) (v.encStructurePrefix a m).length with hlt_p | hge_p
        · rw [List.getElem?_append_left hlt_p]; exact hout_m p hlt_p
        · rw [List.getElem?_append_right hge_p]
          exact hout p hge_p (by simpa [List.length_append] using hp)
  obtain ⟨hbase_last, hout_last⟩ := hprefix v.count le_rfl
  rw [v.encStructurePrefix_count ha] at hbase_last hout_last
  obtain ⟨hnext_outer, hout_outer⟩ :=
    FO.nextBase_and_getElem?_frame_of_realize_frameChunkSentence hlt (by omega)
      (v.realize_layoutInRaw_iff a hB I_in R hbase_last)
      (fun j hj => by rw [FO.realize_rel₁, Matrix.cons_val_zero]; exact hout_last j hj)
      hbase0' houter
  simp only [Nat.zero_add, Nat.sub_zero] at hnext_outer hout_outer
  exact ⟨hnext_outer, fun p hp => hout_outer p (Nat.zero_le _) hp⟩

/-- Canonical witness assignment for `v.layoutMatrix` on `Fin B`. -/
private def canonicalLayoutR (a : EncodedStructure) (B : ℕ) :
    ∀ i : LayoutVar v.count, Set (Fin (layoutArity v.count i) → Fin B)
  | .inl (.inl m) =>
    {x : Fin 1 → Fin B | (x 0 : ℕ) =
      if (m : ℕ) = 0 then 0 else (v.encStructurePrefix a ((m : ℕ) - 1)).length}
  | .inl (.inr ()) => {x : Fin 1 → Fin B | (encStructure a)[(x 0 : ℕ)]? = some true}
  | .inr (.inl m) =>
    if h : (m : ℕ) = 0 then
      {x : Fin 2 → Fin B | (x 0 : ℕ) ≤ a.1 ∧ (x 1 : ℕ) = 2 * (x 0 : ℕ)}
    else
      let idx : Fin v.count := ⟨(m : ℕ) - 1, by omega⟩
      {x : Fin 2 → Fin B | (x 0 : ℕ) ≤ a.1 ^ v.arity idx ∧
        (x 1 : ℕ) = (v.encStructurePrefix a idx.1).length + 2 * (x 0 : ℕ)}
  | .inr (.inr ()) =>
    {x : Fin 2 → Fin B | (x 0 : ℕ) ≤ (encStructure a).length ∧ (x 1 : ℕ) = 2 * (x 0 : ℕ)}

private theorem realize_layoutMatrix_complete {a : EncodedStructure} (ha : v.WellFormed a) {B : ℕ}
    (hB : (frame (encStructure a)).length < B)
    (I_in : ∀ b : Bool, Set (Fin ((fun _ : Bool => 1) b) → Fin B))
    (huLen : ∀ z : Fin B, ![z] ∈ I_in true ↔ (z : ℕ) = (frame (encStructure a)).length)
    (huBit : ∀ p : Fin B, (p : ℕ) < (frame (encStructure a)).length →
      (![p] ∈ I_in false ↔ (frame (encStructure a))[(p : ℕ)]? = some true)) :
    (letI := v.powerStructure a B;
      letI := ESO.varLanguage.structure (arity := fun _ : Bool => 1) I_in;
      letI := ESO.varLanguage.structure (arity := layoutArity v.count) (v.canonicalLayoutR a B);
      v.layoutMatrix.Realize (Fin B)) := by
  let _ := v.powerStructure a B
  let _ := ESO.varLanguage.structure (arity := fun _ : Bool => 1) I_in
  let R := v.canonicalLayoutR a B
  let _ := ESO.varLanguage.structure (arity := layoutArity v.count) R
  have hlt : ∀ x : Fin 2 → Fin B, RelMap v.layoutLt x ↔ x 0 < x 1 := fun _ => Iff.rfl
  have hbase_char : ∀ (m : Fin (v.count + 2)) (z : Fin B),
      RelMap (v.layoutBase m) ![z] ↔
        (z : ℕ) = if (m : ℕ) = 0 then 0 else (v.encStructurePrefix a ((m : ℕ) - 1)).length :=
    fun _ _ => Iff.rfl
  have hbase0 : ∀ z : Fin B, RelMap (v.layoutBase 0) ![z] ↔ (z : ℕ) = 0 := fun z => by
    simp [hbase_char]
  have hraw_prefix : ∀ (m : ℕ) (p : Fin B), (p : ℕ) < (v.encStructurePrefix a m).length →
      (RelMap v.layoutRawBit ![p] ↔ (v.encStructurePrefix a m)[(p : ℕ)]? = some true) := by
    intro m p hp
    change (encStructure a)[(p : ℕ)]? = some true ↔ _
    rw [v.getElem?_encStructure_of_lt_prefix ha hp]
  simp only [layoutMatrix, Sentence.realize_inf, FO.realize_closeAll,
    Formula.realize_iff, FO.realize_rel₁, FO.realize_isZero hlt]
  refine ⟨⟨⟨fun x => hbase0 (x 0), ?_⟩, ?_⟩, ?_⟩
  · refine FO.realize_frameChunkSentence_of_canonical hlt (v.length_frame_encUnary_lt ha hB)
      (v.realize_layoutIsElem_iff a B I_in R) (v.realize_top_iff_getElem?_encUnary a B I_in R)
      hbase0 (fun z => by rw [hbase_char]; simp [v.encStructurePrefix_zero])
      (fun j p => by change ((j : ℕ) ≤ a.1 ∧ (p : ℕ) = 2 * (j : ℕ)) ↔ _; simp)
      (fun p _ hp => by
        simpa [v.encStructurePrefix_zero] using hraw_prefix 0 p
          (by simpa [v.encStructurePrefix_zero] using hp))
  · rw [Sentence.Realize, Formula.realize_iInf]
    intro idx
    have hsucc_eq := v.encStructurePrefix_succ a idx
    refine FO.realize_frameChunkSentence_of_canonical hlt
      (v.length_prefix_add_frame_table_lt ha hB idx)
      (v.realize_layoutInTable_iff ha B I_in R idx)
      (v.realize_layoutTableBit_iff ha B I_in R idx)
      (fun z => by rw [hbase_char]; simp)
      (fun z => by rw [hbase_char, ← List.length_append, ← hsucc_eq]; simp)
      (fun j p => by
        rw [Vocabulary.WellFormed.length_table v ha (v.symbol idx)]
        change ![j, p] ∈ R (.inr (.inl idx.succ)) ↔ _; simp [R, canonicalLayoutR]; rfl)
      (fun p hlo hhi => ?_)
    have hp' : (p : ℕ) < (v.encStructurePrefix a (idx.1 + 1)).length := by
      rw [hsucc_eq, List.length_append]; exact hhi
    rw [hraw_prefix (idx.1 + 1) p hp', hsucc_eq, List.getElem?_append_right hlo]
  · have hbase_last : ∀ z : Fin B,
        RelMap (v.layoutBase (Fin.last (v.count + 1))) ![z] ↔
          (z : ℕ) = (encStructure a).length := fun z => by
      rw [hbase_char]; simp [v.encStructurePrefix_count ha]
    refine FO.realize_frameChunkSentence_of_canonical hlt (by omega)
      (v.realize_layoutInRaw_iff a hB I_in R hbase_last) (fun _ _ => Iff.rfl) hbase0
      (fun z => by rw [Nat.zero_add]; exact huLen z)
      (fun j p => by
        change ((j : ℕ) ≤ (encStructure a).length ∧ (p : ℕ) = 2 * (j : ℕ)) ↔ _; simp)
      (fun p _ hp => by rw [Nat.zero_add] at hp; rw [Nat.sub_zero]; exact huBit p hp)

/-- **Characterization of `layoutESOSentence`**: on `(Fin B, v.powerStructure a B)` for a
well-formed input `a` with `(frame (encStructure a)).length < B`, an interpretation `I_in` of
`inputVarLanguage` satisfies `v.layoutESOSentence` iff `I_in true` (`uLenSym`) holds solely of
`(frame (encStructure a)).length` and `I_in false` (`uBitSym`) agrees with `frame (encStructure a)`
on all positions `< (frame (encStructure a)).length`. -/
theorem realize_layoutESOSentence {a : EncodedStructure} (ha : v.WellFormed a) {B : ℕ}
    (hB : (frame (encStructure a)).length < B)
    (I_in : ∀ b : Bool, Set (Fin ((fun _ : Bool => 1) b) → Fin B)) :
    (letI := v.powerStructure a B;
      letI := ESO.varLanguage.structure (arity := fun _ : Bool => 1) I_in;
      v.layoutESOSentence.Realize (Fin B)) ↔
      (∀ z : Fin B, ![z] ∈ I_in true ↔ (z : ℕ) = (frame (encStructure a)).length) ∧
        (∀ p : Fin B, (p : ℕ) < (frame (encStructure a)).length →
          (![p] ∈ I_in false ↔ (frame (encStructure a))[(p : ℕ)]? = some true)) := by
  let _ := v.powerStructure a B
  let _ := ESO.varLanguage.structure (arity := fun _ : Bool => 1) I_in
  rw [layoutESOSentence, ESO.Sentence.Realize]
  exact ⟨fun ⟨R, hR⟩ => v.realize_layoutMatrix_sound ha hB I_in R hR,
    fun ⟨huLen, huBit⟩ => ⟨v.canonicalLayoutR a B,
      v.realize_layoutMatrix_complete ha hB I_in huLen huBit⟩⟩

end Vocabulary

end Cslib.Logic
