/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarryLookaheadCountingInitialLayout
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveDepthPrepare.Embedded
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WordFunctionLayout

/-!
# Physical preparation of an ordinary count-bit evaluator

The initial work tapes contain only a separately stored predicate context and one raw parameter
word. Native word computations install count, width, query metadata, header and status. The
checked depth machine then derives the binary height and unary frontier. No derived field is
supplied in advance, and the long context is preserved throughout initialization.
-/

public section

namespace Turing.MultiTapeATM.CarryLookaheadCountingPrepare

open MultiTapeTM Cslib.Circuits.Boolean.CarryLookahead.Query
open CarryLookaheadCountingInitialLayout

/-- Reusable initializer scratch, the complete evaluator, then raw parameters and a marker. -/
abbrev size (scratch k r q : ℕ) : ℕ :=
  scratch + CarryLookaheadCountingLayout.size k r q + 2

/-- The evaluator runs in the protected middle block. -/
def evaluatorTapes (scratch k r q : ℕ) :
    Fin (CarryLookaheadCountingLayout.size k r q) ↪ Fin (size scratch k r q) :=
  (Fin.natAddEmb scratch).trans (Fin.castAddEmb 2)

/-- Actual ambient words with reusable scratch and the untouched raw parameter source. -/
@[expose] def ambientWords (scratch k r q : ℕ) (context : List Bool) (a : CountingInput.Input)
    (fields : Fields) : Fin (size scratch k r q) → List Bool :=
  Fin.append (Fin.append (fun _ : Fin scratch => []) (words k r q context fields))
    ![CountingInput.encInput a, []]

/-- Every initializer stage has all work heads at zero and the host at its left blank. -/
@[expose] def config (scratch k r q : ℕ) (input context : List Bool) (a : CountingInput.Input)
    (fields : Fields) : Cfg (size scratch k r q) Bool Unit input :=
  { tapesCfg input (ambientWords scratch k r q context a fields) 0 0 [] with inputPos := 0 }

/-- Initially only the context and raw parameter word are present; every derived word is blank. -/
@[expose] def initial (scratch k r q : ℕ) (input context : List Bool) (a : CountingInput.Input) :
    Cfg (size scratch k r q) Bool Unit input :=
  config scratch k r q input context a {}

private theorem ambientWords_update_of_eq (scratch k r q : ℕ) (context : List Bool)
    (a : CountingInput.Input) (fields fields' : Fields)
    (dest : Fin (CarryLookaheadCountingLayout.size k r q)) (word : List Bool)
    (hwords : Function.update (words k r q context fields) dest word =
      words k r q context fields') :
    Function.update (ambientWords scratch k r q context a fields)
      (evaluatorTapes scratch k r q dest) word =
      ambientWords scratch k r q context a fields' := by
  funext i
  cases i using Fin.addCases with
  | left i =>
    cases i using Fin.addCases with
    | left i =>
      simp [ambientWords, evaluatorTapes, Function.update_of_ne
        (show (i.castAdd (CarryLookaheadCountingLayout.size k r q)).castAdd 2 ≠
          (Fin.natAdd scratch dest).castAdd 2 from by
            intro h
            have hv := congrArg Fin.val h
            have := i.isLt
            change i.val = scratch + dest.val at hv
            omega)]
    | right i =>
      have h := congrFun hwords i
      simpa [ambientWords, evaluatorTapes, Function.update_apply] using h
  | right i =>
    simp [ambientWords, evaluatorTapes,
      Function.update_of_ne (Fin.castAdd_ne_natAdd _ _).symm]

private theorem ambientWords_update (scratch k r q : ℕ) (context : List Bool)
    (a : CountingInput.Input) (fields : Fields) (field : CountingInput.Field)
    (word : List Bool) :
    Function.update (ambientWords scratch k r q context a fields)
      (evaluatorTapes scratch k r q (destination k r q field)) word =
      ambientWords scratch k r q context a (fields.set field word) :=
  ambientWords_update_of_eq scratch k r q context a fields _ _ word
    (words_update_field k r q context fields field word)

/-- The prepared protected block is exactly the existing native evaluator's initial storage. -/
theorem view_prepared (scratch k r q : ℕ) (input context : List Bool) (a : CountingInput.Input) :
    viewCfg (evaluatorTapes scratch k r q)
      (config scratch k r q input context a (canonical a)) =
      CarryLookaheadCounting.initial k r q input context a.count a.query.width a.query.bit
        a.query.claim := by
  rw [initial_eq_tapesCfg]
  apply Cfg.ext <;> try rfl
  · funext i
    simp [viewCfg, evaluatorTapes, config, ambientWords, tapesCfg]

/-- Construct all seven derived words from the raw parameter source using fixed finite native
machines. The supplied context is preserved without copying it during preparation. -/
theorem exists_prepare (k r q : ℕ) :
    ∃ (scratch : ℕ) (S : Type) (_ : Finite S)
      (tm : MultiTapeTM (size scratch k r q) Bool S) (c d : ℕ),
      ∀ (input context : List Bool) (a : CountingInput.Input),
        tm.runFrom ((initial scratch k r q input context a).withState (some tm.q₀))
          (c * ((CountingInput.encInput a).length + 1) ^ d) =
          (config scratch k r q input context a (canonical a)).withState none := by
  classical
  have hfields (field : CountingInput.Field) :=
    WordFunctionLayout.exists_of_polyTime (CountingInput.word_polyTime field)
  choose fieldScratch Q hQ fieldMachine cField dField hField using hfields
  obtain ⟨depthScratch, QD, hQD, depthMachine, cD, dD, hDepth⟩ :=
    CarrySaveDepthPrepare.Embedded.exists_prepare
  let (field : CountingInput.Field) : Finite (Q field) := hQ field
  let : Finite QD := hQD
  let scratch := fieldScratch .count + fieldScratch .width + fieldScratch .metadata +
    fieldScratch .header + fieldScratch .status + depthScratch
  let E := CarryLookaheadCountingLayout.size k r q
  have hsize : 12 ≤ E := by
    unfold E CarryLookaheadCountingLayout.size CountingTerminalLayout.size
    omega
  have hfield (field : CountingInput.Field) : fieldScratch field ≤ scratch := by
    cases field <;> dsimp only [scratch] <;> omega
  have hdepth : depthScratch ≤ scratch := by dsimp only [scratch]; omega
  let write := fun field =>
    ((fieldMachine field).extendTapes
      (WordFunctionLayout.outputTapes (hfield field) (destination k r q field))).fromLeftBlank
  let depth := depthMachine.extendTapes
    (CarrySaveDepthPrepare.Embedded.embedding depthScratch scratch E hdepth hsize)
  let prepare := (write .count).seq ((write .width).seq ((write .metadata).seq
    ((write .header).seq ((write .status).seq depth))))
  let bound (m : ℕ) := (cField .count * (m + 1) ^ dField .count + 2) +
    ((cField .width * (m + 1) ^ dField .width + 2) +
      ((cField .metadata * (m + 1) ^ dField .metadata + 2) +
        ((cField .header * (m + 1) ^ dField .header + 2) +
          ((cField .status * (m + 1) ^ dField .status + 2) + cD * (m + 1) ^ dD))))
  have hbound : Cslib.PolynomiallyBounded bound := by unfold bound; fun_prop
  obtain ⟨c, d, hc⟩ := Cslib.polynomiallyBounded_iff_le.mp hbound
  refine ⟨scratch, _, inferInstance, prepare, c, d, ?_⟩
  intro input context a
  have hwrite (field : CountingInput.Field) (fields : Fields) (hblank : fields.get field = []) :
      RunsBetween (write field) (config scratch k r q input context a fields)
        (config scratch k r q input context a
          (fields.set field (CountingInput.word field a)))
        (cField field * ((CountingInput.encInput a).length + 1) ^ dField field + 2)
        ((scratch + E + 2) *
          (cField field * ((CountingInput.encInput a).length + 1) ^ dField field + 1) +
            4 * (scratch + E + 2)) := by
    have hr := hField field scratch E (hfield field) (destination k r q field) input a
      (ambientWords scratch k r q context a fields) []
      (by intro i; simp [ambientWords, E])
      (by simpa [ambientWords, words_destination] using hblank)
      (by simp [ambientWords, E]) (by simp [ambientWords, E])
    simp only [encBits_apply] at hr
    rw [show (Fin.natAdd scratch (destination k r q field)).castAdd 2 =
      evaluatorTapes scratch k r q (destination k r q field) from rfl,
      ambientWords_update] at hr
    exact hr
  let f₀ : Fields := {}
  let f₁ := f₀.set .count (CountingInput.word .count a)
  let f₂ := f₁.set .width (CountingInput.word .width a)
  let f₃ := f₂.set .metadata (CountingInput.word .metadata a)
  let f₄ := f₃.set .header (CountingInput.word .header a)
  let f₅ := f₄.set .status (CountingInput.word .status a)
  have h₀ := hwrite .count f₀ rfl
  have h₁ := hwrite .width f₁ rfl
  have h₂ := hwrite .metadata f₂ rfl
  have h₃ := hwrite .header f₃ rfl
  have h₄ := hwrite .status f₄ rfl
  have hcore (i : Fin 12) :
      CarrySaveDepthPrepare.Embedded.coreTapes scratch E hsize i =
        evaluatorTapes scratch k r q ⟨i.val, by have := i.isLt; omega⟩ := by
    apply Fin.ext
    simp [CarrySaveDepthPrepare.Embedded.coreTapes_val, evaluatorTapes]
  have hcore₀ : CarrySaveDepthPrepare.Embedded.coreTapes scratch E hsize 0 =
      evaluatorTapes scratch k r q (height k r q) := by
    exact hcore 0
  have hcore₄ : CarrySaveDepthPrepare.Embedded.coreTapes scratch E hsize 4 =
      evaluatorTapes scratch k r q (unary k r q) := by
    exact hcore 4
  have hcore₇ : CarrySaveDepthPrepare.Embedded.coreTapes scratch E hsize 7 =
      evaluatorTapes scratch k r q (destination k r q .count) := by
    exact hcore 7
  have hmiddle (fields : Fields) (i : Fin E) :
      ambientWords scratch k r q context a fields (evaluatorTapes scratch k r q i) =
        words k r q context fields i := by
    change Fin.append _ _ ((Fin.natAdd scratch i).castAdd 2) = _
    rw [Fin.append_left, Fin.append_right]
  have hd := hDepth scratch E hdepth hsize input a.count
    (ambientWords scratch k r q context a f₅) []
    (by rw [hcore₇, hmiddle, words_destination]; rfl)
    (by rw [hcore₀, hmiddle, words_height]; rfl)
    (by rw [hcore₄, hmiddle, words_unary]; rfl)
    (by
      intro i hi
      have he : i = ((⟨i.val, hi⟩ : Fin scratch).castAdd E).castAdd 2 := Fin.ext rfl
      conv_lhs => rw [he]
      simp only [ambientWords, E, Fin.append_left])
  have hw₀ := ambientWords_update_of_eq scratch k r q context a f₅
    { f₅ with height := encNat (Nat.clog 2 a.count) } (height k r q)
    (encNat (Nat.clog 2 a.count)) (words_update_height k r q context f₅ _)
  have hw₄ := ambientWords_update_of_eq scratch k r q context a
    { f₅ with height := encNat (Nat.clog 2 a.count) } (canonical a) (unary k r q)
    (encUnary (Nat.clog 2 a.count)) (words_update_unary k r q context _ _)
  rw [hcore₀, hcore₄, hw₀, hw₄] at hd
  have hr := h₀.seq (h₁.seq (h₂.seq (h₃.seq (h₄.seq hd))))
  have hlen : (encNat a.count).length ≤ (CountingInput.encInput a).length := by
    rw [CountingInput.length_encInput]
    simp only [encNat_apply, ← Nat.size_eq_bits_len]
    omega
  have ht := Nat.mul_le_mul_left cD
    (Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) dD)
  have htime := hc (CountingInput.encInput a).length
  dsimp only [bound] at htime
  exact (hr.mono (t' := c * ((CountingInput.encInput a).length + 1) ^ d)
    (by omega) (Nat.le_refl _)).1

end Turing.MultiTapeATM.CarryLookaheadCountingPrepare
