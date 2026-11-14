/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.FuzzyExtractor.DecodeThenExtract
public import CslibFrontier.Crypto.Computational.LWE.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Matrix.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.UniformNat.Residue
import Mathlib.Algebra.BigOperators.Fin

/-!
# Asymptotic security of the LWE fuzzy extractor

Fuller, Meng and Reyzin's LWE fuzzy extractor `lweFuzzyExtractor` ([FullerMengReyzin2020]) uses
the noisy reading `w` as the error of an LWE sample. Its secret has `k + l` coordinates, of which
the first `k` are the key. This module makes it a family in the security parameter `κ`, with `m κ`
samples, key length `k κ`, `l κ` further secret coordinates and modulus `2 ^ w κ`, and proves it
secure from decision LWE in dimension `l κ` whose error law is the source itself.

A distinguisher family reads the security parameter in unary, the key, and the helper matrix
`[c | A]`, each residue as `w κ` binary digits (`LWEFamily.encInput`). It is admissible when one
uniform strict PPT machine realizes it on these encodings (`LWEFamily.Distinguisher.IsPPT`), as for
`LWE.Distinguisher.IsPPT`.

The two reductions behind the fixed-parameter bound `securityAdvantage_lweFuzzyExtractor_le` are
the explicit programs `hardcoreKeyReduction` and `hardcoreUniformReduction`. Given a dimension-`l`
sample `(A₂, c₂)`, each draws `A₁` and `x₁` and hands the distinguisher the helper
`([A₁ | A₂], A₁ x₁ + c₂)`. `LWEFamily.isPPT_keyReduction` and `LWEFamily.isPPT_uniformReduction`
prove that, run at every parameter, they are uniform strict PPT LWE distinguishers whenever the
distinguisher is, provided `m, k, l, w` are computable in polynomial time in unary. The certificate
samples the coins as `w`-bit naturals and computes the helper word entry by entry; that word
program has the same output law as the typed reduction.

## Main definitions

* `Cslib.Crypto.FuzzyExtractor.LWEFamily.Input`, `Cslib.Crypto.FuzzyExtractor.LWEFamily.encInput`:
  the input of a distinguisher and its encoding.
* `Cslib.Crypto.FuzzyExtractor.LWEFamily.Distinguisher`,
  `Cslib.Crypto.FuzzyExtractor.LWEFamily.Distinguisher.IsPPT`: distinguisher families and their
  efficiency.
* `Cslib.Crypto.FuzzyExtractor.LWEFamily.keyReduction`,
  `Cslib.Crypto.FuzzyExtractor.LWEFamily.uniformReduction`: the two reductions at every parameter,
  as LWE distinguishers.

## Main results

* `Cslib.Crypto.FuzzyExtractor.LWEFamily.isPPT_keyReduction`,
  `Cslib.Crypto.FuzzyExtractor.LWEFamily.isPPT_uniformReduction`: strict PPT certificates for the
  reductions, from the distinguisher's certificate.
* `Cslib.Crypto.FuzzyExtractor.computationallySecure_lweFuzzyExtractor`: under
  `DecisionLWEWithErrors l m w source` for every source ensemble in `sources`, the family is
  `ComputationallySecure` for `sources` against PPT distinguishers.

## Deviations and limitations

* The modulus is `2 ^ w κ`, the modulus of the library's typed decision LWE (`DecisionLWE`). The
  fixed-parameter results in `DecodeThenExtract` allow any modulus `q`.
* The assumption is LWE with the source as its error law. Its hardness for particular sources is
  not proved here.
* The efficiency of the honest `Gen` and `Rep` is not certified; `Rep` runs an arbitrary decoder,
  whose correctness is a hypothesis in `DecodeThenExtract` (`DecoderCorrectWithError`).
* Distinguishers are uniform strict PPT programs. Non-uniform, circuit-size formulations are not
  treated.

## References

* [B. Fuller, X. Meng, and L. Reyzin, *Computational Fuzzy Extractors*][FullerMengReyzin2020]
-/

@[expose] public section

namespace Cslib.Crypto.FuzzyExtractor

open Probability Turing.MultiTapeTM
open scoped _root_.Matrix

namespace LWEFamily

/-! ### Distinguishers -/

variable (m k l w : ℕ → ℕ)

/-- The input of a distinguisher against the LWE fuzzy-extractor family: the security parameter
`κ`, a key of `k κ` residues modulo `2 ^ w κ`, and a helper whose matrix has `m κ` rows and
`k κ + l κ` columns. -/
structure Input where
  /-- The security parameter, given to machines in unary. -/
  secParam : ℕ
  /-- The key, real or uniform. -/
  key : Fin (k secParam) → ZMod (2 ^ w secParam)
  /-- The public helper `(A, c)`. -/
  helper : DecodeHelper (m secParam) (k secParam + l secParam) (2 ^ w secParam) Unit

variable {m k l w}

/-- The binary word of a key: its residues in order, each as `w` digits, least significant first.
-/
def keyWord {k w : ℕ} (key : Fin k → ZMod (2 ^ w)) : List Bool :=
  Cslib.Matrix.toBinary (_root_.Matrix.of fun _ : Fin 1 => key)

/-- The binary word of a helper: the matrix `[c | A]` row by row, as for an LWE sample. -/
def helperWord {m n w : ℕ} (helper : DecodeHelper m n (2 ^ w) Unit) : List Bool :=
  Cslib.Matrix.toBinary (LWE.augmentedMatrix helper.matrix helper.cipher)

/-- The words a machine reads for a distinguisher input: the security parameter, the key word and
the helper word. -/
def Input.words (x : Input m k l w) : ℕ × List Bool × List Bool :=
  (x.secParam, keyWord x.key, helperWord x.helper)

/-- A distinguisher input is determined by its words. -/
theorem Input.words_injective :
    Function.Injective (Input.words (m := m) (k := k) (l := l) (w := w)) := by
  rintro ⟨κ, key, ⟨A, c, ⟨⟩⟩⟩ ⟨κ', key', ⟨A', c', ⟨⟩⟩⟩ h
  simp only [Input.words, Prod.mk.injEq] at h
  obtain ⟨rfl, hkey, hhelper⟩ := h
  have hkey := congrArg (fun word => Cslib.Matrix.ofBinary 1 (k κ) (w κ) word 0) hkey
  have hhelper := congrArg (Cslib.Matrix.ofBinary (m κ) (k κ + l κ + 1) (w κ)) hhelper
  simp only [keyWord, helperWord, Cslib.Matrix.ofBinary_toBinary, LWE.augmentedMatrix_inj]
    at hkey hhelper
  obtain ⟨rfl, rfl⟩ := hhelper
  subst hkey
  rfl

variable (m k l w)

/-- The encoding of a distinguisher input: the framed unary security parameter, then the framed
key word and helper word. -/
def encInput : Input m k l w ↪ List Bool :=
  (⟨Input.words, Input.words_injective⟩ : Input m k l w ↪ _).trans
    (encPair encUnary (encPair encBits encBits))

/-- A distinguisher family against the LWE fuzzy extractor: at each security parameter `κ`, a
program reading a key and a helper and outputting a bit. -/
abbrev Distinguisher : Type :=
  (κ : ℕ) → (Fin (k κ) → ZMod (2 ^ w κ)) →
    DecodeHelper (m κ) (k κ + l κ) (2 ^ w κ) Unit → Experiment

variable {m k l w}

/-- A distinguisher family is PPT when one uniform strict PPT machine reads `encInput` and writes
its output bit. -/
def Distinguisher.IsPPT (D : Distinguisher m k l w) : Prop :=
  IsPPTOn (encInput m k l w) encBool fun x => D x.secParam x.key x.helper

/-! ### The reductions at every parameter -/

/-- `hardcoreKeyReduction` at every security parameter: an LWE distinguisher in dimension `l κ`
with `m κ` samples. -/
noncomputable def keyReduction (D : Distinguisher m k l w) : LWE.Distinguisher l m w :=
  fun κ => hardcoreKeyReduction (D κ)

/-- `hardcoreUniformReduction` at every security parameter: an LWE distinguisher in dimension
`l κ` with `m κ` samples. -/
noncomputable def uniformReduction (D : Distinguisher m k l w) : LWE.Distinguisher l m w :=
  fun κ => hardcoreUniformReduction (D κ)

/-! ### Coins as natural numbers -/

/-- Sample `count` independent `width`-bit naturals. -/
private noncomputable def sampleCoins (count width : ℕ) : ProbComp (List ℕ) :=
  OracleComp.replicate count (ProbComp.sampleBinaryNat width)

/-- Sample `rows` lists of `cols` independent `width`-bit naturals. -/
private noncomputable def sampleCoinRows (rows cols width : ℕ) : ProbComp (List (List ℕ)) :=
  OracleComp.replicate rows (sampleCoins cols width)

/-- Read a residue vector from a list of naturals, padding with zero. -/
private def coinVector (count width : ℕ) (coins : List ℕ) : Fin count → ZMod (2 ^ width) :=
  fun j => (coins.getD j.val 0 : ZMod (2 ^ width))

/-- Read a residue matrix from a list of rows of naturals, padding with zero. -/
private def coinMatrix (rows cols width : ℕ) (coins : List (List ℕ)) :
    _root_.Matrix (Fin rows) (Fin cols) (ZMod (2 ^ width)) :=
  fun i j => ((coins.getD i.val []).getD j.val 0 : ZMod (2 ^ width))

private theorem coinVector_ofFn {count width : ℕ} (x : Fin count → ZMod (2 ^ width)) :
    coinVector count width (List.ofFn fun j => (x j).val) = x := by
  ext j
  simp only [coinVector, List.getD_ofFn, ZMod.natCast_zmod_val]

private theorem coinMatrix_ofFn {rows cols width : ℕ}
    (A : _root_.Matrix (Fin rows) (Fin cols) (ZMod (2 ^ width))) :
    coinMatrix rows cols width (List.ofFn fun i => List.ofFn fun j => (A i j).val) = A := by
  ext i j
  simp only [coinMatrix, List.getD_ofFn, ZMod.natCast_zmod_val]

/-! ### The distinguisher input built by the reductions -/

/-- The distinguisher input built from an LWE input `x = (A₂, c₂)` and coins: the key read from
`keyCoins`, and the helper `([A₁ | A₂], A₁ x₁ + c₂)` with `A₁` read from `a` and `x₁` from `b`. -/
private def reductionInput (x : LWE.Input l m w) (a : List (List ℕ)) (b keyCoins : List ℕ) :
    Input m k l w where
  secParam := x.secParam
  key := coinVector (k x.secParam) (w x.secParam) keyCoins
  helper :=
    ⟨joinCols (coinMatrix (m x.secParam) (k x.secParam) (w x.secParam) a) x.matrix,
      (coinMatrix (m x.secParam) (k x.secParam) (w x.secParam) a) *ᵥ
        coinVector (k x.secParam) (w x.secParam) b + x.target, ()⟩

/-- The key word computed from natural-number coins. -/
private def keyWordOf (k w : ℕ) (keyCoins : List ℕ) : List Bool :=
  (List.range k).flatMap fun j => BitString.lowBits w (keyCoins.getD j 0)

/-- The helper word computed row by row from the LWE word and natural-number coins: entry `0` of
row `i` is `∑ⱼ a i j * b j` plus `c₂ i`, then the row of `A₁`, then the row of `A₂`. -/
private def helperWordOf (m k l w : ℕ) (lweWord : List Bool) (a : List (List ℕ)) (b : List ℕ) :
    List Bool :=
  (List.range m).flatMap fun i =>
    BitString.lowBits w (((List.range k).map fun j => (a.getD i []).getD j 0 * b.getD j 0).sum +
        Cslib.Matrix.binaryEntry (l + 1) w lweWord i 0) ++
      ((List.range k).flatMap fun j => BitString.lowBits w ((a.getD i []).getD j 0)) ++
      (List.range l).flatMap fun j =>
        BitString.lowBits w (Cslib.Matrix.binaryEntry (l + 1) w lweWord i (j + 1))

private theorem lowBits_eq_ofFn_val (w x : ℕ) :
    BitString.lowBits w x =
      List.ofFn fun t : Fin w => (x : ZMod (2 ^ w)).val.testBit t.val := by
  rw [← BitString.lowBits_val_natCast, BitString.lowBits_eq_ofFn]

private theorem keyWord_coinVector (k w : ℕ) (keyCoins : List ℕ) :
    keyWord (coinVector k w keyCoins) = keyWordOf k w keyCoins := by
  simp only [keyWord, keyWordOf, Cslib.Matrix.toBinary_eq, _root_.Matrix.of_apply,
    List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.flatMap_def, List.map_range_eq_ofFn, coinVector, lowBits_eq_ofFn_val]

private theorem helperWord_reductionInput (x : LWE.Input l m w) (a : List (List ℕ))
    (b keyCoins : List ℕ) :
    helperWord (reductionInput (k := k) x a b keyCoins).helper =
      helperWordOf (m x.secParam) (k x.secParam) (l x.secParam) (w x.secParam)
        (Cslib.Matrix.toBinary (LWE.augmentedMatrix x.matrix x.target)) a b := by
  obtain ⟨κ, A₂, c₂⟩ := x
  have hc (i : Fin (m κ)) : (Cslib.Matrix.binaryEntry (l κ + 1) (w κ)
      (Cslib.Matrix.toBinary (LWE.augmentedMatrix A₂ c₂)) i.val 0 : ZMod (2 ^ w κ)) = c₂ i := by
    simpa [LWE.augmentedMatrix] using
      Cslib.Matrix.binaryEntry_toBinary (LWE.augmentedMatrix A₂ c₂) i 0
  have hA (i : Fin (m κ)) (j : Fin (l κ)) : (Cslib.Matrix.binaryEntry (l κ + 1) (w κ)
      (Cslib.Matrix.toBinary (LWE.augmentedMatrix A₂ c₂)) i.val (j.val + 1) : ZMod (2 ^ w κ)) =
        A₂ i j := by
    simpa [LWE.augmentedMatrix] using
      Cslib.Matrix.binaryEntry_toBinary (LWE.augmentedMatrix A₂ c₂) i j.succ
  generalize Cslib.Matrix.toBinary (LWE.augmentedMatrix A₂ c₂) = word at hc hA ⊢
  simp only [helperWord, helperWordOf, reductionInput, Cslib.Matrix.toBinary_eq,
    List.flatMap_def, List.map_range_eq_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  rw [List.ofFn_succ, List.ofFn_add, List.flatten_cons, List.flatten_append, List.append_assoc]
  simp only [LWE.augmentedMatrix, Fin.cons_zero, Fin.cons_succ, joinCols, _root_.Matrix.of_apply,
    Fin.append_left', Fin.append_right, lowBits_eq_ofFn_val, Pi.add_apply,
    _root_.Matrix.mulVec, dotProduct, coinMatrix, coinVector, Nat.cast_add, List.sum_ofFn,
    Nat.cast_sum, Nat.cast_mul, hc, hA]

/-- The words of the reductions' distinguisher input. -/
private theorem words_reductionInput (x : LWE.Input l m w) (a : List (List ℕ))
    (b keyCoins : List ℕ) :
    (reductionInput (k := k) x a b keyCoins).words =
      (x.secParam, keyWordOf (k x.secParam) (w x.secParam) keyCoins,
        helperWordOf (m x.secParam) (k x.secParam) (l x.secParam) (w x.secParam)
          (Cslib.Matrix.toBinary (LWE.augmentedMatrix x.matrix x.target)) a b) := by
  rw [Input.words, helperWord_reductionInput]
  simp only [reductionInput, keyWord_coinVector]

/-! ### Polynomial-time computation of the input words -/

section PolyTime

open ComputableInPolyTime

variable {α : Type} {input : α ↪ List Bool}

private theorem computableInPolyTime_keyWordOf {k w : α → ℕ} {keyCoins : α → List ℕ}
    (hk : ComputableInPolyTime k input encUnary) (hw : ComputableInPolyTime w input encUnary)
    (hcoins : ComputableInPolyTime keyCoins input (encList encNat)) :
    ComputableInPolyTime (fun a => keyWordOf (k a) (w a) (keyCoins a)) input encBits := by
  unfold keyWordOf
  apply flatMapToBitsWithInput (range.comp hk)
  apply bitsLow (hw.comp (fst input encUnary))
  exact (listGetD (encA := encNat) 0).comp
    ((hcoins.comp (fst input encUnary)).prod (snd input encUnary))

private theorem computableInPolyTime_helperWordOf {m k l w : α → ℕ} {lweWord : α → List Bool}
    {a : α → List (List ℕ)} {b : α → List ℕ}
    (hm : ComputableInPolyTime m input encUnary) (hk : ComputableInPolyTime k input encUnary)
    (hl : ComputableInPolyTime l input encUnary) (hw : ComputableInPolyTime w input encUnary)
    (hlweWord : ComputableInPolyTime lweWord input encBits)
    (ha : ComputableInPolyTime a input (encList (encList encNat)))
    (hb : ComputableInPolyTime b input (encList encNat)) :
    ComputableInPolyTime
      (fun x => helperWordOf (m x) (k x) (l x) (w x) (lweWord x) (a x) (b x)) input encBits := by
  unfold helperWordOf
  apply flatMapToBitsWithInput (range.comp hm)
  have hrow : ComputableInPolyTime (fun p : α × ℕ => (a p.1).getD p.2 [])
      (encPair input encUnary) (encList encNat) :=
    (listGetD (encA := encList encNat) []).comp
      ((ha.comp (fst input encUnary)).prod (snd input encUnary))
  refine bitsAppend (bitsAppend ?_ ?_) ?_
  · apply bitsLow (hw.comp (fst input encUnary))
    have hterm : ComputableInPolyTime
        (fun q : (α × ℕ) × ℕ => ((a q.1.1).getD q.1.2 []).getD q.2 0 * (b q.1.1).getD q.2 0)
        (encPair (encPair input encUnary) encUnary) encNat :=
      binary_mul' ((listGetD (encA := encNat) 0).comp
          ((hrow.comp (fst _ encUnary)).prod (snd _ encUnary)))
        ((listGetD (encA := encNat) 0).comp
          ((hb.comp ((fst input encUnary).comp (fst _ encUnary))).prod (snd _ encUnary)))
    have hsum := (show ComputableInPolyTime List.sum (encList encNat) encNat by fun_prop).comp
      (mapWithInput (f := fun p j => ((a p.1).getD p.2 []).getD j 0 * (b p.1).getD j 0)
        (range.comp (hk.comp (fst input encUnary))) hterm)
    exact binary_add' hsum (matrixBinaryEntry (by fun_prop) (hw.comp (fst input encUnary))
      (hlweWord.comp (fst input encUnary)) (snd input encUnary) (const 0))
  · apply flatMapToBitsWithInput (range.comp (hk.comp (fst input encUnary)))
    apply bitsLow (hw.comp ((fst input encUnary).comp (fst _ encUnary)))
    exact (listGetD (encA := encNat) 0).comp
      ((hrow.comp (fst _ encUnary)).prod (snd _ encUnary))
  · apply flatMapToBitsWithInput (range.comp (hl.comp (fst input encUnary)))
    apply bitsLow (hw.comp ((fst input encUnary).comp (fst _ encUnary)))
    exact matrixBinaryEntry (by fun_prop) (hw.comp ((fst input encUnary).comp (fst _ encUnary)))
      (hlweWord.comp ((fst input encUnary).comp (fst _ encUnary)))
      ((snd input encUnary).comp (fst _ encUnary)) (by fun_prop)

end PolyTime

/-! ### Certificates for the reductions -/

/-- The security parameter of an LWE input is computable in polynomial time from its encoding. -/
private theorem computableInPolyTime_secParam :
    ComputableInPolyTime (fun x : LWE.Input l m w => x.secParam) (LWE.encInput l m w) encUnary :=
  (ComputableInPolyTime.fst encUnary encBits).comp
    (ComputableInPolyTime.of_eq (f := LWE.Input.words) fun _ => rfl)

/-- The LWE word of an input is computable in polynomial time from its encoding. -/
private theorem computableInPolyTime_lweWord :
    ComputableInPolyTime
      (fun x : LWE.Input l m w => Cslib.Matrix.toBinary (LWE.augmentedMatrix x.matrix x.target))
      (LWE.encInput l m w) encBits :=
  (ComputableInPolyTime.snd encUnary encBits).comp
    (ComputableInPolyTime.of_eq (f := LWE.Input.words) fun _ => rfl)

/-- Building the distinguisher input from an LWE input and coins is polynomial-time. -/
private theorem computableInPolyTime_reductionInput {β : Type} {enc : β ↪ List Bool}
    {x : β → LWE.Input l m w} {a : β → List (List ℕ)} {b keyCoins : β → List ℕ}
    (hm : ComputableInPolyTime m encUnary encUnary) (hk : ComputableInPolyTime k encUnary encUnary)
    (hl : ComputableInPolyTime l encUnary encUnary) (hw : ComputableInPolyTime w encUnary encUnary)
    (hx : ComputableInPolyTime x enc (LWE.encInput l m w))
    (ha : ComputableInPolyTime a enc (encList (encList encNat)))
    (hb : ComputableInPolyTime b enc (encList encNat))
    (hkeyCoins : ComputableInPolyTime keyCoins enc (encList encNat)) :
    ComputableInPolyTime (fun q => reductionInput (k := k) (x q) (a q) (b q) (keyCoins q)) enc
      (encInput m k l w) := by
  have hκ := computableInPolyTime_secParam.comp hx
  have hword := computableInPolyTime_lweWord.comp hx
  refine ComputableInPolyTime.of_enc_eq
    (hκ.prod ((computableInPolyTime_keyWordOf (hk.comp hκ) (hw.comp hκ) hkeyCoins).prod
      (computableInPolyTime_helperWordOf (hm.comp hκ) (hk.comp hκ) (hl.comp hκ) (hw.comp hκ)
        hword ha hb))) fun q => ?_
  change encPair encUnary (encPair encBits encBits) (reductionInput (x q) (a q) (b q)
    (keyCoins q)).words = _
  rw [words_reductionInput]
  rfl

/-- The word program of `keyReduction`: sample the coins as naturals and run the distinguisher on
the input they determine. -/
private noncomputable def keyReductionWords (D : Distinguisher m k l w) (x : LWE.Input l m w) :
    Experiment := do
  let a ← sampleCoinRows (m x.secParam) (k x.secParam) (w x.secParam)
  let b ← sampleCoins (k x.secParam) (w x.secParam)
  let y := reductionInput x a b b
  D y.secParam y.key y.helper

/-- The word program of `uniformReduction`, with separate coins for the key. -/
private noncomputable def uniformReductionWords (D : Distinguisher m k l w)
    (x : LWE.Input l m w) : Experiment := do
  let a ← sampleCoinRows (m x.secParam) (k x.secParam) (w x.secParam)
  let b ← sampleCoins (k x.secParam) (w x.secParam)
  let r ← sampleCoins (k x.secParam) (w x.secParam)
  let y := reductionInput x a b r
  D y.secParam y.key y.helper

private theorem eval_keyReductionWords (D : Distinguisher m k l w) (x : LWE.Input l m w) :
    ProbComp.eval (keyReductionWords D x) =
      ProbComp.eval (keyReduction D x.secParam x.matrix x.target) := by
  simp only [keyReductionWords, keyReduction, hardcoreKeyReduction, sampleCoinRows, sampleCoins,
    ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_replicate_replicate_sampleBinaryNat,
    ProbComp.eval_replicate_sampleBinaryNat, PMF.bind_map, Function.comp_def, reductionInput,
    coinMatrix_ofFn, coinVector_ofFn]

private theorem eval_uniformReductionWords (D : Distinguisher m k l w) (x : LWE.Input l m w) :
    ProbComp.eval (uniformReductionWords D x) =
      ProbComp.eval (uniformReduction D x.secParam x.matrix x.target) := by
  simp only [uniformReductionWords, uniformReduction, hardcoreUniformReduction, sampleCoinRows,
    sampleCoins, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbComp.eval_replicate_replicate_sampleBinaryNat, ProbComp.eval_replicate_sampleBinaryNat,
    PMF.bind_map, Function.comp_def, reductionInput, coinMatrix_ofFn, coinVector_ofFn]

/-- Sampling the coins is strict PPT on LWE inputs. -/
private theorem isPPTOn_sampleCoinRows (hm : ComputableInPolyTime m encUnary encUnary)
    (hk : ComputableInPolyTime k encUnary encUnary)
    (hw : ComputableInPolyTime w encUnary encUnary) :
    IsPPTOn (LWE.encInput l m w) (encList (encList encNat))
      fun x => sampleCoinRows (m x.secParam) (k x.secParam) (w x.secParam) :=
  ((hw.comp computableInPolyTime_secParam).sampleBinaryNat.replicate
    (hk.comp computableInPolyTime_secParam)).replicate (hm.comp computableInPolyTime_secParam)

/-- Sampling a coin vector is strict PPT for every input encoding with a polynomial-time security
parameter. -/
private theorem isPPTOn_sampleCoins {β : Type} {enc : β ↪ List Bool} {κ : β → ℕ}
    (hκ : ComputableInPolyTime κ enc encUnary) (hk : ComputableInPolyTime k encUnary encUnary)
    (hw : ComputableInPolyTime w encUnary encUnary) :
    IsPPTOn enc (encList encNat) fun q => sampleCoins (k (κ q)) (w (κ q)) :=
  (hw.comp hκ).sampleBinaryNat.replicate (hk.comp hκ)

/-- **`keyReduction` is PPT.** When `m, k, l, w` are computable in polynomial time in unary, the
real-key reduction of a PPT distinguisher family is a uniform strict PPT LWE distinguisher. -/
theorem isPPT_keyReduction (hm : ComputableInPolyTime m encUnary encUnary)
    (hk : ComputableInPolyTime k encUnary encUnary)
    (hl : ComputableInPolyTime l encUnary encUnary)
    (hw : ComputableInPolyTime w encUnary encUnary)
    {D : Distinguisher m k l w} (hD : D.IsPPT) : (keyReduction D).IsPPT := by
  let encA := encPair (LWE.encInput l m w) (encList (encList encNat))
  have hκ : ComputableInPolyTime (fun p : LWE.Input l m w × List (List ℕ) => p.1.secParam)
      encA encUnary :=
    computableInPolyTime_secParam.comp (ComputableInPolyTime.fst _ _)
  have hinput := computableInPolyTime_reductionInput hm hk hl hw
    (x := fun q : (LWE.Input l m w × List (List ℕ)) × List ℕ => q.1.1)
    (a := fun q => q.1.2) (b := fun q => q.2) (keyCoins := fun q => q.2)
    ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _))
    ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _))
    (ComputableInPolyTime.snd _ _) (ComputableInPolyTime.snd _ _)
  have hrun := hD.preprocess hinput
  have hb := (isPPTOn_sampleCoins hκ hk hw).bind_with (second := fun p b =>
    let y := reductionInput p.1 p.2 b b
    D y.secParam y.key y.helper) hrun
  have hall := (isPPTOn_sampleCoinRows (l := l) hm hk hw).bind_with (second := fun x a => do
    let b ← sampleCoins (k x.secParam) (w x.secParam)
    let y := reductionInput x a b b
    D y.secParam y.key y.helper) hb
  exact hall.congr (eval_keyReductionWords D)

/-- **`uniformReduction` is PPT.** When `m, k, l, w` are computable in polynomial time in unary,
the uniform-key reduction of a PPT distinguisher family is a uniform strict PPT LWE
distinguisher. -/
theorem isPPT_uniformReduction (hm : ComputableInPolyTime m encUnary encUnary)
    (hk : ComputableInPolyTime k encUnary encUnary)
    (hl : ComputableInPolyTime l encUnary encUnary)
    (hw : ComputableInPolyTime w encUnary encUnary)
    {D : Distinguisher m k l w} (hD : D.IsPPT) : (uniformReduction D).IsPPT := by
  let encA := encPair (LWE.encInput l m w) (encList (encList encNat))
  let encB := encPair encA (encList encNat)
  have hκA : ComputableInPolyTime (fun p : LWE.Input l m w × List (List ℕ) => p.1.secParam)
      encA encUnary :=
    computableInPolyTime_secParam.comp (ComputableInPolyTime.fst _ _)
  have hκB : ComputableInPolyTime
      (fun p : (LWE.Input l m w × List (List ℕ)) × List ℕ => p.1.1.secParam) encB encUnary :=
    hκA.comp (ComputableInPolyTime.fst _ _)
  have hinput := computableInPolyTime_reductionInput hm hk hl hw
    (x := fun q : ((LWE.Input l m w × List (List ℕ)) × List ℕ) × List ℕ => q.1.1.1)
    (a := fun q => q.1.1.2) (b := fun q => q.1.2) (keyCoins := fun q => q.2)
    (((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _)).comp
      (ComputableInPolyTime.fst _ _))
    (((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _)).comp
      (ComputableInPolyTime.fst _ _))
    ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _))
    (ComputableInPolyTime.snd _ _)
  have hrun := hD.preprocess hinput
  have hr := (isPPTOn_sampleCoins hκB hk hw).bind_with (second := fun p r =>
    let y := reductionInput p.1.1 p.1.2 p.2 r
    D y.secParam y.key y.helper) hrun
  have hb := (isPPTOn_sampleCoins hκA hk hw).bind_with (second := fun p b => do
    let r ← sampleCoins (k p.1.secParam) (w p.1.secParam)
    let y := reductionInput p.1 p.2 b r
    D y.secParam y.key y.helper) hr
  have hall := (isPPTOn_sampleCoinRows (l := l) hm hk hw).bind_with (second := fun x a => do
    let b ← sampleCoins (k x.secParam) (w x.secParam)
    let r ← sampleCoins (k x.secParam) (w x.secParam)
    let y := reductionInput x a b r
    D y.secParam y.key y.helper) hb
  exact hall.congr (eval_uniformReductionWords D)

end LWEFamily

/-! ### Asymptotic security -/

/-- **Asymptotic security of the LWE fuzzy extractor** ([FullerMengReyzin2020]). Let
`m, k, l, w` be computable in polynomial time in unary, and let `sources` be a set of source
ensembles such that, for every `source ∈ sources`, decision LWE in dimension `l κ` with `m κ`
samples, modulus `2 ^ w κ` and error law `source κ` holds against uniform strict PPT
distinguishers (`DecisionLWEWithErrors l m w source`). Then the family
`κ ↦ lweFuzzyExtractor (m κ) (k κ) (l κ) (2 ^ w κ) (decode κ)` is `ComputationallySecure` for
`sources` against uniform strict PPT distinguisher families: on each source ensemble, the key is
indistinguishable from uniform given the helper.

The proof bounds the advantage at each `κ` by the LWE advantages of `LWEFamily.keyReduction D`
and `LWEFamily.uniformReduction D` (`securityAdvantage_lweFuzzyExtractor_le`), which are PPT by
`LWEFamily.isPPT_keyReduction` and `LWEFamily.isPPT_uniformReduction`. The decoder affects only
correctness. -/
theorem computationallySecure_lweFuzzyExtractor {m k l w : ℕ → ℕ}
    (hm : ComputableInPolyTime m encUnary encUnary)
    (hk : ComputableInPolyTime k encUnary encUnary)
    (hl : ComputableInPolyTime l encUnary encUnary)
    (hw : ComputableInPolyTime w encUnary encUnary)
    (decode : (κ : ℕ) → _root_.Matrix (Fin (m κ)) (Fin (k κ + l κ)) (ZMod (2 ^ w κ)) →
      (Fin (m κ) → ZMod (2 ^ w κ)) → ProbComp (Option (Fin (k κ + l κ) → ZMod (2 ^ w κ))))
    {sources : Set ((κ : ℕ) → PMF (Fin (m κ) → ZMod (2 ^ w κ)))}
    (hLWE : ∀ source ∈ sources, DecisionLWEWithErrors l m w source) :
    ComputationallySecure (fun κ => lweFuzzyExtractor (m κ) (k κ) (l κ) (2 ^ w κ) (decode κ))
      sources LWEFamily.Distinguisher.IsPPT := by
  intro source hsource D hD
  have hkey := hLWE source hsource _ (LWEFamily.isPPT_keyReduction hm hk hl hw hD)
  have hunif := hLWE source hsource _ (LWEFamily.isPPT_uniformReduction hm hk hl hw hD)
  exact negligible_of_le (hkey.add hunif) fun κ =>
    securityAdvantage_lweFuzzyExtractor_le (decode κ) (source κ) (D κ)

end Cslib.Crypto.FuzzyExtractor
