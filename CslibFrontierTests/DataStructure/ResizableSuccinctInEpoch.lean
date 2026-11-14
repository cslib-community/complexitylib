/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: local-only (test)

public import CslibFrontier.DataStructure.HashFamily.WordRAM.RuntimeReducedKWise
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.InEpoch
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Params
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Compaction
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.WindowOps
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.MetaSync
public import CslibFrontier.Computability.WordRAM.Resizable.Basic

public section

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.HashFamily.WordRAM.RuntimeReducedKWise
open Cslib.Probability

local notation "rChunk" w₀:arg b:arg b':arg => reducedChunkBits (reducedTrinomialStep w₀ b b')

/-!
# Unit Tests for In-Epoch Resizable Succinct Operations and Infrastructure

This test suite covers both concrete evaluations and symbolic specifications:
1. Concrete footprint bounds `compactedEpochWords` for $n = 8$ and empty $n = 0$.
2. Initial empty dictionary `CompactedRep` representation.
3. Symbolic key reconstruction on live slots from `CompactedRep`.
4. `RuntimeReducedKWise` Horner evaluation (`evalHashGenProg`) on polynomial coefficients.
5. Concrete circular window growth (`winGrowRight`) evaluation.
6. Symbolic state transition and resulting window mapping of `winGrowRightGenProg`.
7. Physical-to-dense slot mapping of `denseOfPhysGenProg`.
-/

/-- Test 1 (Concrete evaluation): Space bound calculation for positive active epoch size
$n = 8 > 0$, $N = 16$. -/
theorem test_compacted_words_positive_eval :
    compactedEpochWords 64 16 64 16 8 ≤ Dynamic.succinctWords 1355 441 64 16 64 8 := by
  have hw : 0 < 64 := by decide
  have hU : 64 ≤ 2 ^ 64 := by decide
  have hev : EpochValid 64 8 16 := by
    right
    refine ⟨by decide, by decide, by decide, by decide⟩
  exact compactedEpochWords_le_succinctWords hw hU hev

/-- Test 2 (Concrete evaluation): Space bound calculation for empty dictionary $n = 0$, $N = 0$. -/
theorem test_compacted_words_empty_eval :
    compactedEpochWords 64 16 64 0 0 ≤ Dynamic.succinctWords 1355 441 64 16 64 0 := by
  have hw : 0 < 64 := by decide
  have hU : 64 ≤ 2 ^ 64 := by decide
  have hev : EpochValid 64 0 0 := Or.inl ⟨rfl, rfl⟩
  exact compactedEpochWords_le_succinctWords hw hU hev

/-- Test 3 (Symbolic specification): Verify `CompactedRep` empty initial state. -/
theorem test_compactedRep_empty_state {r : ℕ} {x : RData r}
    (hx : x.Bounded 64) (hfr : x.frontier = 8)
    (hhdr : RootHeaderValid 64 16 64 0 0 0 0 x.mem) :
    CompactedRep 64 16 64 0 0 0 0 (empty 64) x :=
  compactedRep_empty hx hfr hhdr

/-- Test 4 (Symbolic specification): Key reconstruction on live slots in `CompactedRep`. -/
theorem test_reconstructKeyAt_spec_eval {U V w N n n_init base : ℕ}
    {s_abs : Dictionary.State U} {r : ℕ} {x : RData r}
    (hrep : CompactedRep U V w N n n_init base s_abs x)
    (hNU : N ≤ U) (hn : 0 < n) {d : ℕ} (hd : d < n) :
    ∃ θ : QuotHashSeed U N,
      let key := reconstructKeyAt base (base + offCompItems U w N) U V w N n θ x.mem d
      ∃ hu : key < U, ⟨key, hu⟩ ∈ Dictionary.dom s_abs := by
  obtain ⟨θ, hsplit⟩ := hrep.active_inv hn
  obtain ⟨s_fix, hinv, htot, hcpl⟩ := hsplit.coupled
  have hspec := reconstructKeyAt_spec hrep.vals_lt hNU hinv hcpl htot
  obtain ⟨hu, hsome, _⟩ := hspec.1 d hd
  refine ⟨θ, hu, ?_⟩
  rw [Dictionary.mem_dom_iff]
  exact ⟨_, hsome⟩

/-- Test 5 (Symbolic specification): Behavioral evaluation of `evalHashGenProg` on non-trivial
polynomial coefficients. -/
theorem test_evalHashGenProg_result {w U w₀ b b' k hashBase scratchBase : ℕ}
    {θ : ReducedPolySeed w₀ b b' k} {u : Fin U} {s₀ : Memory.State}
    (hw₀_pos : 0 < w₀) (hw₀ : w₀ ≤ w) (hU : U ≤ 2 ^ w₀) (hb' : b' ≤ w) (hk_pos : 0 < k)
    (hc_lt : 2 * rChunk w₀ b b' < w)
    (hfr_h : hashBase + ReducedKWise.space w w₀ b b' k ≤ s₀.frontier)
    (hfit_h : Fits w (hashBase + ReducedKWise.space w w₀ b b' k))
    (hfr_s : scratchBase + scratchWords ≤ s₀.frontier)
    (hfit_s : Fits w (scratchBase + scratchWords))
    (hdisj : hashBase + ReducedKWise.space w w₀ b b' k ≤ scratchBase ∨
      scratchBase + scratchWords ≤ hashBase)
    (hrep : ReducedKWise.Rep hashBase w w₀ b b' k θ s₀.mem) :
    let hp := mkHashParams w w₀ b b' k
    let prog := evalHashGenProg (hp, hashBase, scratchBase, u.val)
    (Memory.spec 0).clientResult s₀ prog = (reducedPolyHash U w₀ b b' k θ u).val ∧
    memoryCost prog s₀ ≤ evalMemBound k := by
  intro hp prog
  have haux := evalHashGenProg_spec (u := u) hw₀_pos hw₀ hU hb' hk_pos hc_lt hfr_h hfit_h
    hfr_s hfit_s hdisj hrep
  exact ⟨haux.2.2.2.1, haux.2.2.1⟩

/-- Test 6 (Concrete evaluation): Circular window growth maps new tail offset to
circular position. -/
theorem test_winGrowRight_concrete_eval :
    let r := winGrowRight 8 3 2 (fun _ => 0, fun _ => 0)
    r.1 2 = 5 ∧ r.2 5 = 2 := by
  decide

/-- Test 7 (Symbolic specification): State transition and resulting window mapping of
`winGrowRightGenProg`. -/
theorem test_winGrowRightGenProg_transition
    (U V w N metaBase itemBase m_items b_win n_win : ℕ) (s : Memory.State)
    (hw : 0 < w) (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hn : n_win < maxTailItems N) :
    let prog := winGrowRightGenProg ((mkCompParams U V w N, metaBase), (b_win, n_win))
    let s' := (Memory.spec 0).clientState s prog
    s'.frontier = s.frontier ∧ memoryCost prog s = 8 ∧
    compTDAt metaBase U w N s'.mem n_win = (b_win + n_win) % maxTailItems N ∧
    compDTAt metaBase U w N s'.mem ((b_win + n_win) % maxTailItems N) = n_win := by
  intro prog s'
  have heff := winGrowRightGenProg_effect (V := V) (b_win := b_win) (m_items := m_items)
    hw hitem hn s
  have hcost := memoryCost_winGrowRightGenProg ((mkCompParams U V w N, metaBase), (b_win, n_win)) s
  dsimp only [s', prog]
  refine ⟨heff.1, hcost, ?_, ?_⟩
  · rw [heff.2.1]
    unfold winGrowRight
    dsimp only
    exact Function.update_self _ _ _
  · rw [heff.2.2.1]
    unfold winGrowRight
    dsimp only
    exact Function.update_self _ _ _

/-- Test 8 (Symbolic specification): Behavioral execution of `denseOfPhysGenProg`
physical-to-dense slot mapping. -/
theorem test_denseOfPhysGenProg_result {U V w N metaBase g : ℕ} {s : Memory.State}
    (ht_lt : 0 < bucketBits N → ¬(g < compGmAt metaBase U w N s.mem 0 * slabSize N) →
      N - 1 - g < maxTailItems N ∧
      compTDAt metaBase U w N s.mem (N - 1 - g) < maxTailItems N) :
    (Memory.spec 0).clientResult s
        (denseOfPhysGenProg ((mkCompParams U V w N, metaBase), g)) =
      denseOfPhys N (compGmAt metaBase U w N s.mem) (compTDAt metaBase U w N s.mem) g :=
  clientResult_denseOfPhysGenProg ht_lt
