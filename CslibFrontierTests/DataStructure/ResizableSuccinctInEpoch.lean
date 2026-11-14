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
1. Concrete footprint bounds `compactedEpochWords` for $n = 8$ and empty $n = 0$ (Tests 1, 2).
2. Concrete initial empty dictionary `CompactedRep` representation with `V = 2 ^ w` (Test 3).
3. Symbolic non-empty `CompactedRep` construction from `CompactedSplitRep` (Test 4).
4. Symbolic key reconstruction on live slots from `CompactedRep` (Test 5).
5. Symbolic `RuntimeReducedKWise` Horner evaluation on polynomial coefficients (Test 6).
6. Concrete circular window growth (`winGrowRight`) evaluation (Test 7).
7. Symbolic state transition and resulting window mapping of `winGrowRightGenProg` (Test 8).
8. Symbolic physical-to-dense slot mapping of `denseOfPhysGenProg` (Test 9).
9. Module client verification: `WinGrowRightPre` safety precondition construction (Test 10).
10. Module client verification: `realizesBounded_winGrowRightGen` verification (Test 11).
-/

/-- Test 1 (Concrete evaluation): Space bound calculation for positive active epoch size
$n = 8 > 0$, $N = 16$. -/
theorem test_compacted_words_positive_eval :
    compactedEpochWords 64 16 64 16 8 ≤ Dynamic.succinctWords 1355 441 64 16 64 8 := by
  have hw : 0 < 64 := by decide
  have hU : Fits 64 64 := by decide
  have hU_pos : 0 < 64 := by decide
  have hV_pos : 0 < 16 := by decide
  have hev : EpochValid 64 8 16 := by
    right
    refine ⟨by decide, by decide, by decide, by decide⟩
  exact compactedEpochWords_le_succinctWords hw hU hU_pos hV_pos hev

/-- Test 2 (Concrete evaluation): Space bound calculation for empty dictionary $n = 0$, $N = 0$. -/
theorem test_compacted_words_empty_eval :
    compactedEpochWords 64 16 64 0 0 ≤ Dynamic.succinctWords 1355 441 64 16 64 0 := by
  have hw : 0 < 64 := by decide
  have hU : Fits 64 64 := by decide
  have hU_pos : 0 < 64 := by decide
  have hV_pos : 0 < 16 := by decide
  have hev : EpochValid 64 0 0 := Or.inl ⟨rfl, rfl⟩
  exact compactedEpochWords_le_succinctWords hw hU hU_pos hV_pos hev

/-- Concrete memory layout for an empty initial resting dictionary state with `V = 2 ^ 64`. -/
def testEmptyMem (a : ℕ) : ℕ :=
  if a = 0 then 63
  else if a = 1 then 2 ^ 64 - 1
  else if a = 2 then 64
  else if a = 3 then keyBits 64
  else if a = 4 then valBits (2 ^ 64)
  else 0

/-- Concrete 0-register machine state with frontier 8 and `testEmptyMem`. -/
def testXEmpty : RData 0 := ⟨fun _ => 0, testEmptyMem, 8⟩

/-- Test 3 (Concrete witness): Verify `CompactedRep` empty initial state at `V = 2 ^ w`. -/
theorem test_compactedRep_empty_witness :
    CompactedRep 64 (2 ^ 64) 64 0 0 0 0 (empty 64) testXEmpty := by
  have hx : testXEmpty.Bounded 64 := by
    refine ⟨⟨fun i => Fin.elim0 i, ?_⟩, by decide, ?_⟩
    · intro a
      change testEmptyMem a < 2 ^ 64
      unfold testEmptyMem
      split_ifs <;> decide
    · intro a ha
      change testEmptyMem a = 0
      unfold testEmptyMem
      have h8 : 8 ≤ a := ha
      have : a ≠ 0 := by omega
      have : a ≠ 1 := by omega
      have : a ≠ 2 := by omega
      have : a ≠ 3 := by omega
      have : a ≠ 4 := by omega
      simp only [*, ↓reduceIte]
  have hhdr : RootHeaderValid 64 (2 ^ 64) 64 0 0 0 0 testXEmpty.mem := by
    refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals decide
  exact compactedRep_empty hx rfl hhdr

/-- Test 4 (Symbolic constructor specification): Non-empty `CompactedRep` constructed via
`compactedRep_of_split`. -/
theorem test_compactedRep_of_split_witness {r : ℕ} {U V w N n n_init base : ℕ}
    {θ : QuotHashSeed U N} {s_abs : Dictionary.State U} {x : RData r}
    (hx : x.Bounded w)
    (hfr : x.frontier = base + compactedEpochWords U V w N n)
    (hepoch : EpochValid U n N)
    (hsplit : CompactedSplitRep base (base + offCompItems U w N) U V w N n n_init θ s_abs
      ⟨x.mem, x.frontier⟩) :
    CompactedRep U V w N n n_init base s_abs x :=
  compactedRep_of_split hx hfr hepoch hsplit

/-- Test 5 (Symbolic specification): Key reconstruction on live slots in `CompactedRep`. -/
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

/-- Test 6 (Symbolic specification): Behavioral evaluation of `evalHashGenProg` on non-trivial
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

/-- Test 7 (Concrete evaluation): Circular window growth maps new tail offset to
circular position. -/
theorem test_winGrowRight_concrete_eval :
    let r := winGrowRight 8 3 2 (fun _ => 0, fun _ => 0)
    r.1 2 = 5 ∧ r.2 5 = 2 := by
  decide

/-- Test 8 (Symbolic specification): State transition and resulting window mapping of
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

/-- Test 9 (Symbolic specification): Behavioral execution of `denseOfPhysGenProg`
physical-to-dense slot mapping. -/
theorem test_denseOfPhysGenProg_result {U V w N metaBase g : ℕ} {s : Memory.State}
    (ht_lt : 0 < bucketBits N → ¬(g < compGmAt metaBase U w N s.mem 0 * slabSize N) →
      N - 1 - g < maxTailItems N ∧
      compTDAt metaBase U w N s.mem (N - 1 - g) < maxTailItems N) :
    (Memory.spec 0).clientResult s
        (denseOfPhysGenProg ((mkCompParams U V w N, metaBase), g)) =
      denseOfPhys N (compGmAt metaBase U w N s.mem) (compTDAt metaBase U w N s.mem) g :=
  clientResult_denseOfPhysGenProg ht_lt

/-- Test 10 (Module client verification): Safety precondition `WinGrowRightPre` can be constructed
and satisfied across the `module` boundary. -/
theorem test_winGrowRightPre_constructible :
    ∃ (w : ℕ) (d : (CompParams × ℕ) × (ℕ × ℕ)) (s : Memory.State),
      WinGrowRightPre w d s := by
  let w := 64
  let U := 65536
  let V := 2 ^ 64
  let N := 65536
  let metaBase := 0
  let cp := mkCompParams U V w N
  let s : Memory.State := ⟨fun _ => 0, offCompItems U w N⟩
  refine ⟨w, ((cp, metaBase), (0, 0)), s, ?_⟩
  unfold WinGrowRightPre
  dsimp only
  refine ⟨⟨U, V, N, by decide, by decide, by decide, by decide, le_refl _, rfl, ?_⟩, ?_, ?_⟩
  · change 0 + offCompItems U w N ≤ offCompItems U w N; rw [Nat.zero_add]
  · change 0 < maxTailItems 65536; decide
  · change 0 + 0 ≤ 65536; decide

/-- Test 11 (Module client verification): `realizesBounded_winGrowRightGen` is callable
and verifies across the `module` boundary. -/
theorem test_winGrowRight_realizesBounded_module_client :
    RealizesBounded .exact winGrowRightGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × (ℕ × ℕ))) (WordEncoding.encode (α := Unit))
      WinGrowRightPre (fun _ _ => 0) :=
  realizesBounded_winGrowRightGen
