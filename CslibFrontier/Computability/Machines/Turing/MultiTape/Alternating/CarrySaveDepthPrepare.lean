/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WordFunction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.FromLeftBlank
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveCountingRoot
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveLeafLayout
import Mathlib.Data.Fin.Tuple.Embedding

/-!
# Preparing both depth counters from a binary count

The source count remains on tape seven. Two native word computations write its ceiling logarithm
in binary on tape zero and in unary on tape four. Their scratch lies beyond the twelve protected
controller tapes, so context, width, bit index and every other protected word survive. All work,
including the host input head movements, is charged in the binary count's length.
-/

public noncomputable section

namespace Turing.MultiTapeATM.CarrySaveDepthPrepare

open MultiTapeTM

/-- Work-tape words and heads at their origins, with the host input parked at its left blank. -/
@[expose] def config {k : ℕ} (input : List Bool) (words : Fin (k + 12) → List Bool)
    (out : List Bool) : Cfg (k + 12) Bool Unit input :=
  { tapesCfg input words 0 0 out with inputPos := 0 }

private def scratchEmbedding (m k : ℕ) (h : m ≤ k) : Fin m ↪ Fin (k + 12) :=
  (Fin.natAddEmb 12).trans (Fin.castLEEmb (by omega))

private theorem scratchEmbedding_val (m k : ℕ) (h : m ≤ k) (i : Fin m) :
    (scratchEmbedding m k h i).val = 12 + i.val := rfl

private def outputEmbedding (m k : ℕ) (h : m ≤ k) (target : Fin 12) :
    Fin (m + 1) ↪ Fin (k + 12) :=
  Fin.Embedding.snoc (scratchEmbedding m k h) (a := ⟨target.val, by omega⟩) (by
    rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    have := target.isLt
    simp only [scratchEmbedding_val] at hv
    omega)

private def inputMarker (m k : ℕ) (h : m + 1 ≤ k) : Fin 2 ↪ Fin (k + 12) :=
  Function.Embedding.embFinTwo (a := 7) (b := ⟨12 + m, by omega⟩) (by
    intro he
    have hv := congrArg Fin.val he
    change 7 = 12 + m at hv
    omega)

private theorem outputEmbedding_last (m k : ℕ) (h : m ≤ k) (target : Fin 12) :
    outputEmbedding m k h target (Fin.last m) = ⟨target.val, by omega⟩ :=
  Fin.Embedding.snoc_last

private theorem outputEmbedding_cast (m k : ℕ) (h : m ≤ k) (target : Fin 12) (i : Fin m) :
    outputEmbedding m k h target i.castSucc = scratchEmbedding m k h i :=
  Fin.Embedding.snoc_castSucc

private def embedding (m k : ℕ) (h : m + 1 ≤ k) (target : Fin 12)
    (htarget : target.val ≠ 7) : Fin (m + 1 + 2) ↪ Fin (k + 12) :=
  Fin.Embedding.append (x := outputEmbedding m k (by omega) target)
    (y := inputMarker m k h) (by
      rw [Set.disjoint_left]
      rintro _ ⟨i, rfl⟩ ⟨j, hj⟩
      have hseven : 7 % (k + 12) = 7 := Nat.mod_eq_of_lt (by omega)
      cases i using Fin.lastCases with
      | last =>
        fin_cases j <;>
          have hv := congrArg Fin.val hj <;>
          simp [inputMarker, outputEmbedding_last,
            Function.Embedding.embFinTwo_apply_zero,
            Function.Embedding.embFinTwo_apply_one, hseven] at hv <;> omega
      | cast i =>
        fin_cases j <;>
          have hv := congrArg Fin.val hj <;>
          simp [inputMarker, outputEmbedding_cast,
            Function.Embedding.embFinTwo_apply_zero,
            Function.Embedding.embFinTwo_apply_one, scratchEmbedding_val, hseven] at hv <;> omega)

private theorem embedding_source (m k : ℕ) (h : m + 1 ≤ k) (target : Fin 12)
    (htarget : target.val ≠ 7) :
    embedding m k h target htarget (Fin.natAdd (m + 1) 0) = 7 := by
  simp [embedding, inputMarker, Function.Embedding.embFinTwo_apply_zero]

private theorem embedding_output (m k : ℕ) (h : m + 1 ≤ k) (target : Fin 12)
    (htarget : target.val ≠ 7) :
    embedding m k h target htarget ((Fin.last m).castAdd 2) = ⟨target.val, by omega⟩ := by
  simp [embedding, outputEmbedding_last]

private theorem embedding_private (m k : ℕ) (h : m + 1 ≤ k) (target : Fin 12)
    (htarget : target.val ≠ 7) (j : Fin (m + 1 + 2))
    (hsource : j ≠ Fin.natAdd (m + 1) 0) (houtput : j ≠ (Fin.last m).castAdd 2) :
    12 ≤ (embedding m k h target htarget j).val := by
  cases j using Fin.addCases with
  | left j =>
    cases j using Fin.lastCases with
    | last => exact (houtput rfl).elim
    | cast j => simp [embedding, outputEmbedding_cast,
        scratchEmbedding_val]
  | right j =>
    fin_cases j
    · exact (hsource rfl).elim
    · simp [embedding, inputMarker, Function.Embedding.embFinTwo_apply_one]

/-- One finite native preparation constructs both depth counters from the binary count.
All twelve protected words except height and unary frontier survive. The bound depends only on
the count's binary length; the source count, width and potentially long predicate context are
never copied into the function's input. -/
theorem exists_prepare :
    ∃ (k : ℕ) (S : Type) (_ : Finite S) (tm : MultiTapeTM (k + 12) Bool S) (c d : ℕ),
      ∀ (input : List Bool) (n : ℕ) (words : Fin (k + 12) → List Bool) (out : List Bool),
        words 7 = encNat n → words 0 = [] → words 4 = [] →
        (∀ i, 12 ≤ i.val → words i = []) →
        tm.runFrom
          ((config input words out).withState (some tm.q₀))
          (c * ((encNat n).length + 1) ^ d) =
          (config input
              (Function.update (Function.update words 0 (encNat (Nat.clog 2 n))) 4
                (encUnary (Nat.clog 2 n))) out).withState none := by
  obtain ⟨mB, SB, hSB, binary, cB, dB, hB⟩ :=
    WordFunction.exists_of_polyTime ComputableInPolyTime.binary_clog_two_nat
  obtain ⟨mU, SU, hSU, unary, cU, dU, hU⟩ :=
    WordFunction.exists_of_polyTime ComputableInPolyTime.binary_clog_two
  let := hSB
  let := hSU
  let k := max mB mU + 1
  let eB := embedding mB k (by simp [k]) 0 (by decide)
  let eU := embedding mU k (by simp [k]) 4 (by decide)
  have htB : PolyBounded (fun n : ℕ => (encNat n).length)
      (fun n => cB * ((encNat n).length + 1) ^ dB) :=
    .of_forall_le cB dB (fun _ => le_rfl)
  have htU : PolyBounded (fun n : ℕ => (encNat n).length)
      (fun n => cU * ((encNat n).length + 1) ^ dU) :=
    .of_forall_le cU dU (fun _ => le_rfl)
  obtain ⟨c, d, hclock⟩ := ((htB.add htU).add (PolyBounded.const 2)).exists_le
  refine ⟨k, _, inferInstance, ((binary.extendTapes eB).seq (unary.extendTapes eU)).fromLeftBlank,
    c, d, ?_⟩
  intro input n words out hcount hheight hfront hblank
  have hoB : eB ((Fin.last mB).castAdd 2) = 0 := by
    dsimp only [eB]
    rw [embedding_output]
    rfl
  have hoU : eU ((Fin.last mU).castAdd 2) = 4 := by
    dsimp only [eU]
    rw [embedding_output]
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (show 4 < k + 12 by omega)]
  have h70 : (7 : Fin (k + 12)) ≠ 0 := by
    intro he
    have hv := congrArg Fin.val he
    simp [Nat.mod_eq_of_lt (show 7 < k + 12 by omega)] at hv
  have h40 : (4 : Fin (k + 12)) ≠ 0 := by
    intro he
    have hv := congrArg Fin.val he
    simp [Nat.mod_eq_of_lt (show 4 < k + 12 by omega)] at hv
  have hb := hB (k + 12) eB input n words out (by simpa [eB, embedding_source] using hcount)
    (by
      intro j hj
      by_cases ho : j = (Fin.last mB).castAdd 2
      · subst j
        simpa only [hoB] using hheight
      · exact hblank _ (embedding_private mB k _ 0 (by decide) j hj ho))
  have hu := hU (k + 12) eU input n
    (Function.update words 0 (encNat (Nat.clog 2 n))) out
    (by simpa [eU, embedding_source, Function.update_of_ne h70] using hcount) (by
      intro j hj
      by_cases ho : j = (Fin.last mU).castAdd 2
      · subst j
        simpa only [hoU, Function.update_of_ne h40] using hfront
      · have hprivate := embedding_private mU k (by simp [k]) 4 (by decide) j hj ho
        have hzero : eU j ≠ 0 := by
          intro hz
          have hv := congrArg Fin.val hz
          change (embedding mU k _ 4 _ j).val = 0 at hv
          omega
        rw [Function.update_of_ne hzero]
        exact hblank _ hprivate)
  rw [hoB] at hb
  rw [hoU] at hu
  have hr := (hb.seq hu).fromLeftBlank rfl rfl
  unfold config
  rw [runFrom_eq_of_halt _ _ (hclock n) (by rw [hr.1]; rfl), hr.1]

/-- Root storage before depth preparation: count, width, context and index are already present,
while height, unary frontier, path and private scratch are blank. -/
@[expose] def initial (k : ℕ) (input context : List Bool) (n w bit : ℕ) :
    Cfg (k + 12) Bool Unit input :=
  CarrySaveLeaf.initial k input context (encNat n) (encNat w) [] (encNat bit) [] [] 0 false

/-- Actual initialization of both depth words reaches the canonical counting-root configuration.
The same finite machine works for every count, precision and queried bit. -/
theorem exists_root :
    ∃ (k : ℕ) (S : Type) (_ : Finite S) (tm : MultiTapeTM (k + 12) Bool S) (c d : ℕ),
      ∀ (input context : List Bool) (n w bit : ℕ),
        tm.runFrom ((initial k input context n w bit).withState (some tm.q₀))
          (c * ((encNat n).length + 1) ^ d) =
          (CarrySaveCountingRoot.initial k input context n w bit).withState none := by
  obtain ⟨k, S, hS, tm, c, d, h⟩ := exists_prepare
  refine ⟨k, S, hS, tm, c, d, ?_⟩
  intro input context n w bit
  have hr := h input n
    (CarrySaveLeafLayout.words k context (encNat n) (encNat w) [] (encNat bit) [] [] false) []
    (by simp [CarrySaveLeafLayout.words, Nat.mod_eq_of_lt (show 7 < k + 12 by omega)])
    (by simp [CarrySaveLeafLayout.words])
    (by simp [CarrySaveLeafLayout.words, Nat.mod_eq_of_lt (show 4 < k + 12 by omega)])
    (by
      intro i hi
      exact CarrySaveLeafLayout.words_scratch _ _ _ _ _ _ _ _ _ i (by omega))
  rw [CarrySaveLeafLayout.words_update_height, CarrySaveLeafLayout.words_update_unary] at hr
  simpa only [initial, CarrySaveCountingRoot.initial, CarrySaveLeafLayout.initial_nil_eq_tapesCfg,
    config, Pi.zero_def] using hr

end Turing.MultiTapeATM.CarrySaveDepthPrepare
