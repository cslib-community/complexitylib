/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Space.TQBF
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import Complexity.Computability.Complexity.Classes.Oracle.Space
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain

/-!
# The words of `TQBF`

`TQBF` is a problem on formulas. As an oracle language it is the set `encQBF '' TQBF` of words
encoding true closed formulas, and a decider must handle every word. A word encodes a formula
exactly when its framed tokens decode to the token list of a formula, which is encoded back to the
word (`Cslib.Complexity.TQBF.isCode_iff`). Token lists are decoded by the total decoders of
`Turing.MultiTapeTM.Decoder`, and the token lists of formulas, in prefix order, are recognized by
counting the formulas still expected: a token is expected when the count is positive, consumes one
expected formula and announces as many as it has operands
(`Cslib.Complexity.TQBF.foldl_wfStep_eq_iff`). Both tests are polynomial-time
(`Cslib.Complexity.TQBF.isCode_pt`), and a word that encodes a formula is evaluated by the
polynomial-space evaluator of `TQBF`. Hence `encQBF '' TQBF` is in `PSPACE`
(`Cslib.Complexity.image_TQBF_mem_PSPACE`), and, through `encQBF`, `PSPACE`-hard
(`Cslib.Complexity.image_TQBF_pspaceHard`) [Sipser, Theorem 8.9][Sipser2013].

## Main definitions

* `Cslib.Complexity.TQBF.tokensDecoder`: the total decoder of token lists.
* `Cslib.Complexity.TQBF.wellFormed`: whether a token list is the token list of a formula.
* `Cslib.Complexity.TQBF.isCode`, `Cslib.Complexity.TQBF.decodeQBF`: whether a word encodes a
  formula, and the formula it encodes, `bot` for other words.

## Main results

* `Cslib.Complexity.TQBF.wellFormed_iff`, `Cslib.Complexity.TQBF.isCode_iff`: the tests are
  correct.
* `Cslib.Complexity.TQBF.isCode_pt`, `Cslib.Complexity.TQBF.decodeQBF_pt`: they are
  polynomial-time.
* `Cslib.Complexity.image_TQBF_mem_PSPACE`, `Cslib.Complexity.image_TQBF_pspaceHard`,
  `Cslib.Complexity.image_TQBF_pspaceComplete`: the words of `TQBF` are `PSPACE`-complete.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Theorem 8.9][Sipser2013]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Theorem 4.13][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity.TQBF

open Cslib.Logic.PL _root_.Turing.MultiTapeTM

/-! ### Well-formed token lists -/

/-- The number of operands of a node of the kind. -/
def arity : QBF.Kind → ℕ
  | .var | .top | .bot => 0
  | .not | .ex | .all => 1
  | .and | .or => 2

/-- Whether the token can occur in a formula: only variables and quantifiers carry a variable. -/
def tokenOk (t : QBF.Kind × ℕ) : Bool :=
  match t.1 with
  | .var | .ex | .all => true
  | _ => decide (t.2 = 0)

/-- A step of the well-formedness check: whether every token so far has been expected, and the
number of formulas still expected. -/
def wfStep (s : Bool × ℕ) (t : QBF.Kind × ℕ) : Bool × ℕ :=
  (s.1 && decide (s.2 ≠ 0) && tokenOk t, s.2 - 1 + arity t.1)

private theorem foldl_wfStep_false (ts : List (QBF.Kind × ℕ)) (n : ℕ) :
    (ts.foldl wfStep (false, n)).1 = false := by
  induction ts generalizing n with
  | nil => rfl
  | cons t ts ih => exact ih _

/-- Reading the tokens of a formula consumes one expected formula. -/
private theorem foldl_wfStep_tokens (φ : QBF ℕ) (n : ℕ) (rest : List (QBF.Kind × ℕ)) :
    (φ.tokens ++ rest).foldl wfStep (true, n + 1) = rest.foldl wfStep (true, n) := by
  induction φ generalizing n rest with
  | var v => simp [QBF.tokens, wfStep, tokenOk, arity]
  | top => simp [QBF.tokens, wfStep, tokenOk, arity]
  | bot => simp [QBF.tokens, wfStep, tokenOk, arity]
  | not φ ih =>
    simp only [QBF.tokens, List.cons_append, List.foldl_cons, wfStep, tokenOk, arity]
    simpa using ih n rest
  | and φ ψ ihφ ihψ =>
    simp only [QBF.tokens, List.cons_append, List.foldl_cons, wfStep, tokenOk, arity,
      List.append_assoc]
    have e : (true && decide (n + 1 ≠ 0) && decide True, n + 1 - 1 + 2) = (true, n + 1 + 1) := by
      simp
    rw [e, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
    simp only [QBF.tokens, List.cons_append, List.foldl_cons, wfStep, tokenOk, arity,
      List.append_assoc]
    have e : (true && decide (n + 1 ≠ 0) && decide True, n + 1 - 1 + 2) = (true, n + 1 + 1) := by
      simp
    rw [e, ihφ, ihψ]
  | ex v φ ih =>
    simp only [QBF.tokens, List.cons_append, List.foldl_cons, wfStep, tokenOk, arity]
    simpa using ih n rest
  | all v φ ih =>
    simp only [QBF.tokens, List.cons_append, List.foldl_cons, wfStep, tokenOk, arity]
    simpa using ih n rest

/-- The concatenated tokens of `n` formulas are accepted. -/
private theorem foldl_wfStep_flatten (φs : List (QBF ℕ)) :
    (φs.map QBF.tokens).flatten.foldl wfStep (true, φs.length) = (true, 0) := by
  induction φs with
  | nil => rfl
  | cons φ φs ih =>
    rw [List.map_cons, List.flatten_cons, List.length_cons, foldl_wfStep_tokens, ih]

/-- **The check accepts exactly the concatenated tokens of `n` formulas.** -/
theorem foldl_wfStep_eq_iff (ts : List (QBF.Kind × ℕ)) (n : ℕ) :
    ts.foldl wfStep (true, n) = (true, 0) ↔
      ∃ φs : List (QBF ℕ), φs.length = n ∧ ts = (φs.map QBF.tokens).flatten := by
  refine ⟨fun h => ?_, fun ⟨φs, hlen, hts⟩ => hlen ▸ hts ▸ foldl_wfStep_flatten φs⟩
  induction ts generalizing n with
  | nil =>
    simp only [List.foldl_nil, Prod.mk.injEq, true_and] at h
    exact ⟨[], h.symm, rfl⟩
  | cons t ts ih =>
    simp only [List.foldl_cons, wfStep] at h
    obtain ⟨k, v⟩ := t
    by_cases hok : (true && decide (n ≠ 0) && tokenOk (k, v)) = true
    · rw [hok] at h
      obtain ⟨φs, hlen, hts⟩ := ih _ h
      simp only [Bool.true_and, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨hn, hok⟩ := hok
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      cases k <;> simp only [arity, tokenOk, decide_eq_true_eq] at hlen hok
      · exact ⟨.var v :: φs, by simpa using hlen, by simp [QBF.tokens, hts]⟩
      · subst hok; exact ⟨.top :: φs, by simpa using hlen, by simp [QBF.tokens, hts]⟩
      · subst hok; exact ⟨.bot :: φs, by simpa using hlen, by simp [QBF.tokens, hts]⟩
      · subst hok
        obtain ⟨φ, φs, rfl⟩ := List.exists_cons_of_length_eq_add_one (by simpa using hlen)
        exact ⟨.not φ :: φs, by simpa using hlen, by simp [QBF.tokens, hts]⟩
      · subst hok
        obtain ⟨φ, φs, rfl⟩ := List.exists_cons_of_length_eq_add_one (by simpa using hlen)
        obtain ⟨ψ, φs, rfl⟩ := List.exists_cons_of_length_eq_add_one (by simpa using hlen)
        exact ⟨.and φ ψ :: φs, by simpa using hlen, by simp [QBF.tokens, hts]⟩
      · subst hok
        obtain ⟨φ, φs, rfl⟩ := List.exists_cons_of_length_eq_add_one (by simpa using hlen)
        obtain ⟨ψ, φs, rfl⟩ := List.exists_cons_of_length_eq_add_one (by simpa using hlen)
        exact ⟨.or φ ψ :: φs, by simpa using hlen, by simp [QBF.tokens, hts]⟩
      · obtain ⟨φ, φs, rfl⟩ := List.exists_cons_of_length_eq_add_one (by simpa using hlen)
        exact ⟨.ex v φ :: φs, by simpa using hlen, by simp [QBF.tokens, hts]⟩
      · obtain ⟨φ, φs, rfl⟩ := List.exists_cons_of_length_eq_add_one (by simpa using hlen)
        exact ⟨.all v φ :: φs, by simpa using hlen, by simp [QBF.tokens, hts]⟩
    · rw [Bool.not_eq_true] at hok
      rw [hok] at h
      have h1 := congrArg Prod.fst h
      rw [foldl_wfStep_false] at h1
      exact absurd h1 (by simp)


/-! ### Decoding words -/

/-- The kind of a given index, `all` from `7` on. -/
def kindOfIndex : ℕ → QBF.Kind
  | 0 => .var
  | 1 => .top
  | 2 => .bot
  | 3 => .not
  | 4 => .and
  | 5 => .or
  | 6 => .ex
  | _ => .all

private theorem kindIndex_kindOfIndex : ∀ n, kindIndex (kindOfIndex n) = min n 7
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => rfl
  | n + 7 => by simp [kindOfIndex, kindIndex]

/-- Kinds are decoded from the length of the word. -/
def kindDecoder : Decoder encKind where
  decode w := kindOfIndex w.length
  decode_enc k := by cases k <;> rfl
  computable := by
    have h : ComputableInPolyTime (fun w : List Bool => min w.length 7) encBits encUnary :=
      (by fun_prop :
        ComputableInPolyTime (fun w : List Bool => w.length - (w.length - 7)) encBits encUnary)
      |>.of_enc_eq fun w => congrArg encUnary (by omega)
    have hp : ComputableInPolyTime (fun w : List Bool => kindOfIndex w.length)
        encBits encKind := h.of_enc_eq fun w => by
      change encUnary (kindIndex (kindOfIndex w.length)) = _
      rw [kindIndex_kindOfIndex]
    exact hp.exists_degree

/-- Token lists are decoded element by element. -/
def tokensDecoder : Decoder (encList encToken) := .list (.pair kindDecoder .nat)

/-- Whether a token list is the token list of a formula. -/
def wellFormed (ts : List (QBF.Kind × ℕ)) : Bool := decide (ts.foldl wfStep (true, 1) = (true, 0))

/-- `wellFormed ts` holds exactly when `ts` is the token list of a formula. -/
theorem wellFormed_iff (ts : List (QBF.Kind × ℕ)) :
    wellFormed ts = true ↔ ∃ φ : QBF ℕ, φ.tokens = ts := by
  rw [wellFormed, decide_eq_true_iff, foldl_wfStep_eq_iff]
  constructor
  · rintro ⟨φs, hlen, rfl⟩
    obtain ⟨φ, rfl⟩ := List.length_eq_one_iff.mp hlen
    exact ⟨φ, by simp⟩
  · rintro ⟨φ, rfl⟩
    exact ⟨[φ], rfl, by simp⟩

private theorem wellFormed_pt : ComputableInPolyTime wellFormed
    (encList encToken) encBool := by
  have hstep : ComputableInPolyTime (fun p : (Bool × ℕ) × (QBF.Kind × ℕ) => wfStep p.1 p.2)
      (encPair (encPair encBool encUnary) encToken) (encPair encBool encUnary) := by
    have hok : ComputableInPolyTime tokenOk encToken encBool := by
      refine ComputableInPolyTime.finite_cases (tag := fun t : QBF.Kind × ℕ => t.1)
        (tagEncoding := encKind) (branch := fun k t => match k with
          | .var | .ex | .all => true
          | _ => decide (t.2 = 0)) (ComputableInPolyTime.fst encKind encNat) ?_
      intro k
      cases k <;> first | exact ComputableInPolyTime.const _ | fun_prop
    have hn : ComputableInPolyTime (fun p : (Bool × ℕ) × (QBF.Kind × ℕ) => p.1.2)
        (encPair (encPair encBool encUnary) encToken) encUnary := by fun_prop
    have hpos : ComputableInPolyTime (fun p : (Bool × ℕ) × (QBF.Kind × ℕ) =>
        decide (p.1.2 ≠ 0)) (encPair (encPair encBool encUnary) encToken) encBool :=
      (ComputableInPolyTime.unary_lt' (ComputableInPolyTime.const 0) hn).of_enc_eq
        fun p => by simp [Nat.pos_iff_ne_zero]
    have harity : ComputableInPolyTime (fun p : (Bool × ℕ) × (QBF.Kind × ℕ) =>
        arity p.2.1) (encPair (encPair encBool encUnary) encToken) encUnary :=
      (ComputableInPolyTime.of_finite arity).comp
        ((ComputableInPolyTime.fst encKind encNat).comp
          (ComputableInPolyTime.snd (encPair encBool encUnary) encToken))
    have hb : ComputableInPolyTime (fun p : (Bool × ℕ) × (QBF.Kind × ℕ) => p.1.1)
        (encPair (encPair encBool encUnary) encToken) encBool := by fun_prop
    have hokp : ComputableInPolyTime (fun p : (Bool × ℕ) × (QBF.Kind × ℕ) => tokenOk p.2)
        (encPair (encPair encBool encUnary) encToken) encBool :=
      hok.comp (ComputableInPolyTime.snd (encPair encBool encUnary) encToken)
    exact ((ComputableInPolyTime.of_finite (fun q : Bool × Bool × Bool =>
      q.1 && q.2.1 && q.2.2)).comp (hb.prod (hpos.prod hokp))).prod
      (ComputableInPolyTime.unary_add.comp ((ComputableInPolyTime.unary_sub.comp
        (hn.prod (ComputableInPolyTime.const 1))).prod harity))
  have hfold := ComputableInPolyTime.foldl_of_bounded_growth
    (encB := encPair encBool encUnary)
    (encIn := encList encToken) (encL := encList encToken)
    (list := fun ts : List (QBF.Kind × ℕ) => ts) (init := fun _ => (true, 1))
    ComputableInPolyTime.id' (ComputableInPolyTime.const _) hstep (growth := 2)
    (fun state t => by
      simp only [wfStep, length_encPair, encBool_apply, List.length_singleton, encUnary_apply,
        List.length_replicate]
      have : arity t.1 ≤ 2 := by cases t.1 <;> simp [arity]
      omega)
  exact (ComputableInPolyTime.decide_eq' hfold (ComputableInPolyTime.const _)).of_enc_eq
    fun _ => rfl


/-- Whether a word encodes a formula: it decodes to a well-formed token list that is encoded back
to the word. -/
def isCode (w : List Bool) : Bool :=
  wellFormed (tokensDecoder.decode w) && decide (encList encToken (tokensDecoder.decode w) = w)

/-- A word passes `isCode` exactly when it encodes a formula. -/
theorem isCode_iff (w : List Bool) : isCode w = true ↔ ∃ φ, encQBF φ = w := by
  unfold isCode
  rw [Bool.and_eq_true, wellFormed_iff, decide_eq_true_iff]
  constructor
  · rintro ⟨⟨φ, hφ⟩, he⟩
    exact ⟨φ, by rw [encQBF_apply, hφ, he]⟩
  · rintro ⟨φ, rfl⟩
    rw [encQBF_apply, tokensDecoder.decode_enc]
    exact ⟨⟨φ, rfl⟩, rfl⟩

/-- Whether a word encodes a formula is decidable in polynomial time. -/
theorem isCode_pt : Turing.MultiTapeTM.ComputableInPolyTime isCode encBits encBool := by
  obtain ⟨d, e, hD⟩ := tokensDecoder.computable
  have hD := hD.computableInPolyTime
  have hre : ComputableInPolyTime (fun w => encList encToken (tokensDecoder.decode w))
      encBits encBits := hD.of_enc_eq fun _ => rfl
  exact (ComputableInPolyTime.of_finite (fun q : Bool × Bool => q.1 && q.2)).comp
    ((wellFormed_pt.comp hD).prod
      (ComputableInPolyTime.decide_eq' hre ComputableInPolyTime.id'))

open Classical in
/-- The formula a word encodes, or `bot` if it encodes none. -/
noncomputable def decodeQBF (w : List Bool) : QBF ℕ :=
  if h : ∃ φ, encQBF φ = w then h.choose else .bot

private theorem encQBF_decodeQBF (w : List Bool) :
    encQBF (decodeQBF w) = if isCode w then w else encQBF .bot := by
  unfold decodeQBF
  split_ifs with h₁ h₂ h₃
  · exact h₁.choose_spec
  · exact absurd ((isCode_iff w).mpr h₁) h₂
  · exact absurd ((isCode_iff w).mp h₃) h₁
  · rfl

/-- `decodeQBF` is polynomial-time. -/
theorem decodeQBF_pt : Turing.MultiTapeTM.ComputableInPolyTime decodeQBF encBits encQBF :=
  (ComputableInPolyTime.ite' isCode_pt ComputableInPolyTime.id'
    (ComputableInPolyTime.const (encQBF .bot))).of_enc_eq fun w => encQBF_decodeQBF w

theorem decodeQBF_encQBF (φ : QBF ℕ) : decodeQBF (encQBF φ) = φ :=
  encQBF.injective (by simp [encQBF_decodeQBF, (isCode_iff _).mpr ⟨φ, rfl⟩])

end Cslib.Complexity.TQBF

namespace Cslib.Complexity

open Cslib.Logic.PL _root_.Turing _root_.Turing.MultiTapeTM TQBF

/-- A word is in `encQBF '' TQBF` when it encodes a formula that the evaluator accepts. -/
theorem mem_image_TQBF_iff (w : List Bool) :
    w ∈ encQBF '' TQBF ↔ (isCode w && evaluate (decodeQBF w)) = true := by
  rw [Bool.and_eq_true, evaluate_eq_true_iff]
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    exact ⟨(isCode_iff _).mpr ⟨φ, rfl⟩, by rwa [decodeQBF_encQBF]⟩
  · rintro ⟨hw, hφ⟩
    obtain ⟨φ, rfl⟩ := (isCode_iff w).mp hw
    rw [decodeQBF_encQBF] at hφ
    exact ⟨φ, hφ, rfl⟩

/-- **The words encoding true closed formulas are decided within polynomial space**: a word is
tested for encoding a formula in polynomial time, and then evaluated. -/
theorem image_TQBF_mem_PSPACE : encQBF '' TQBF ∈ PSPACE encBits := by
  obtain ⟨e, he⟩ := exists_computableInO_evaluate
  obtain ⟨dc, _, hc⟩ := isCode_pt.exists_degree
  obtain ⟨dd, _, hd⟩ := decodeQBF_pt.exists_degree
  have h := hc.inO.ite (he.comp hd.inO) (ComputableInO.const false)
  refine mem_PSPACE_of_computableInO (h.mono_le (T' := _) (S' := fun w =>
      (w.length + 1) ^ dc + ((w.length + 1) ^ dd +
        (w.length + (encQBF .bot).length + 1) ^ e + w.length)) (fun _ => le_rfl) fun w => ?_) ?_
    fun w => ?_
  · have hlen : (encQBF (decodeQBF w)).length ≤ w.length + (encQBF .bot).length := by
      rw [encQBF_decodeQBF]
      split_ifs <;> simp
    have := Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) e
    simp only [encBits_apply]
    split_ifs <;> omega
  · exact PolyBounded.mono (PolyBounded.of_polynomiallyBounded
      (fun w : List Bool => (encBits w).length)
      (bound := fun L => (L + 1) ^ dc + ((L + 1) ^ dd + (L + (encQBF .bot).length + 1) ^ e + L))
      (by fun_prop)) fun w => le_rfl
  · rw [mem_image_TQBF_iff]
    cases isCode w <;> rfl

/-- **The words encoding true closed formulas are `PSPACE`-hard**, through the encoding
`encQBF`. -/
theorem image_TQBF_pspaceHard : PSPACEHard encBits (encQBF '' TQBF) :=
  TQBF_pspaceHard.trans ⟨fun φ => encQBF φ, by fun_prop,
    fun φ => encQBF.injective.mem_set_image.symm⟩

/-- **The words encoding true closed formulas are `PSPACE`-complete.** -/
theorem image_TQBF_pspaceComplete : PSPACEComplete encBits (encQBF '' TQBF) :=
  ⟨image_TQBF_mem_PSPACE, image_TQBF_pspaceHard⟩

end Cslib.Complexity
