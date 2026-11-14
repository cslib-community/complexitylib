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
public import CslibFrontier.DataStructure.Dictionary.Dynamic.Spec
public import CslibFrontier.DataStructure.Dictionary.FeistelQuotient
public import CslibFrontier.DataStructure.Dictionary.SuccinctBucket
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctLayout
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctHash
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctSlabOps
public import CslibFrontier.Foundations.FieldTheory.Finite.Trinomial
public import CslibFrontier.Computability.WordRAM.Resizable.Basic

public section

open Cslib
open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.Dynamic
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
11. Concrete non-empty $n = 1$ `CompactedRep` representation witness (Test 12).
12. Concrete evaluation of `reconstructKeyAt` on slot 0 returning key 0 (Test 13).
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

def testOneMem (a : ℕ) : ℕ :=
  if a < 8 then
    match a with
    | 0 => 1
    | 1 => 1
    | 2 => 64
    | 3 => 1
    | 4 => 1
    | 5 => 1
    | 6 => 1
    | _ => 0
  else if h : a < 27 then
    RuntimeReducedKWise.mkHashParams 64 (epochQBits 2 1) (epochHashB 1)
      (totalMicroBits 1) 3 ⟨a - 8, by omega⟩
  else if h : 27 ≤ a ∧ a < 63 then
    mkCompParams 2 2 64 1 ⟨a - 27, by omega⟩
  else if a = 232 then 64
  else if a = 233 then 1
  else if a = 260 then 1
  else 0

/-- Concrete 0-register machine state with frontier 270 and `testOneMem`. -/
def testXOne : RData 0 := ⟨fun _ => 0, testOneMem, 270⟩

/-- Abstract dictionary state with key 0 mapped to value 0. -/
def s_abs_one : Dictionary.State 2 :=
  Function.update (empty 2) ⟨0, by decide⟩ (some 0)

/-- Quotient hash seed for `U = 2, N = 1`. -/
def θ_one : QuotHashSeed 2 1 :=
  (⟨0, by decide⟩, fun _ => ⟨0, Nat.two_pow_pos _⟩)

/-- Reference fixed-capacity memory state for `n = 1`. -/
def testFixMem (a : ℕ) : ℕ :=
  if a = 14 then 1
  else if a = 41 then 1
  else 0

/-- Reference fixed-capacity machine state. -/
def testSFix : Memory.State := ⟨testFixMem, 100⟩

theorem test_rootHeaderValid_one :
    RootHeaderValid 2 2 64 1 1 0 0 testOneMem := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

theorem test_epochParamsStored_one :
    EpochParamsStored 2 2 64 1 0 testOneMem := by
  refine ⟨fun ⟨i, hi⟩ => ?_, fun ⟨i, hi⟩ => ?_⟩
  · unfold testOneMem offHashParams; dsimp only
    split_ifs with h1 h2 <;> try omega
    congr 1; apply Fin.ext; dsimp only; omega
  · unfold testOneMem offCompParams; dsimp only
    split_ifs with h1 h2 h3 <;> try omega
    congr 1; apply Fin.ext; dsimp only; omega

theorem h_step : reducedTrinomialStep (qBits 2 1) (hashB 1) (totalMicroBits 1) = 0 := by
  unfold reducedTrinomialStep reducedTargetBits trinomialStepAux
  decide

theorem h_step_epoch :
    reducedTrinomialStep (epochQBits 2 1) (epochHashB 1) (totalMicroBits 1) = 0 :=
  h_step

theorem h_tabWords : ReducedKWise.tableWords 64 (qBits 2 1) (hashB 1) (totalMicroBits 1) = 1 := by
  unfold ReducedKWise.tableWords reducedTableWords
  rw [h_step]
  decide

theorem h_tabBase :
    ReducedKWise.tabBase (0 + epochHdrWords) (qBits 2 1) (hashB 1)
      (totalMicroBits 1) 3 = 232 := by
  unfold ReducedKWise.tabBase ReducedKWise.seedWords epochHdrWords
  rw [h_step]
  decide

theorem test_clmul_1_1 : clmul 1 1 = 1 := by
  rw [clmul_step]
  change (if 1 &&& 1 = 1 then 1 else 0) ^^^ (clmul 1 0 <<< 1) = 1
  rw [clmul_zero_right]
  decide

theorem test_tableRep_one :
    ReducedKWise.TableRep (0 + epochHdrWords) 64 (qBits 2 1) (hashB 1) (totalMicroBits 1) 3
      testOneMem := by
  refine ⟨?_, ?_⟩
  · intro wIdx hwIdx
    rw [h_tabWords] at hwIdx
    have : wIdx = 0 := by omega
    subst this
    rw [h_tabBase, h_step]
    unfold reducedPackShift reducedChunkBits
    decide
  · intro idx hidx
    rw [h_step] at hidx
    have : idx < 4 := hidx
    rw [h_tabBase, h_step]
    interval_cases idx
    · change getLimb (2 * reducedChunkBits 0) (testOneMem 232) 0 = clmul 0 0
      rw [clmul_zero_left]
      unfold getLimb reducedChunkBits; decide
    · change getLimb (2 * reducedChunkBits 0) (testOneMem 232) 1 = clmul 0 1
      rw [clmul_zero_left]
      unfold getLimb reducedChunkBits; decide
    · change getLimb (2 * reducedChunkBits 0) (testOneMem 232) 2 = clmul 1 0
      rw [clmul_zero_right]
      unfold getLimb reducedChunkBits; decide
    · change getLimb (2 * reducedChunkBits 0) (testOneMem 232) 3 = clmul 1 1
      rw [test_clmul_1_1]
      unfold getLimb reducedChunkBits; decide

theorem test_seedRep_one :
    ReducedKWise.SeedRep (0 + epochHdrWords) (qBits 2 1) (hashB 1) (totalMicroBits 1) 3
      θ_one testOneMem := by
  refine ⟨rfl, fun j m => ?_⟩
  dsimp only [θ_one, getLimb]
  rw [Nat.zero_shiftRight, Nat.zero_and]
  have hj : (j : ℕ) < 3 := j.isLt
  have hlimbs :
      reducedLimbCount (reducedTrinomialStep (qBits 2 1) (hashB 1) (totalMicroBits 1)) = 2 := by
    rw [h_step]; decide
  have hm_lt := m.isLt
  have hm : (m : ℕ) < 2 := by omega
  have hprod :
      reducedLimbCount (reducedTrinomialStep (qBits 2 1) (hashB 1) (totalMicroBits 1)) * (j : ℕ) =
        2 * (j : ℕ) := by
    rw [hlimbs]
  have ha_ge : 226 ≤ 0 + epochHdrWords + 1 +
      ((m : ℕ) +
        reducedLimbCount (reducedTrinomialStep (qBits 2 1) (hashB 1) (totalMicroBits 1)) *
          (j : ℕ)) := by
    unfold epochHdrWords; omega
  have ha_le : 0 + epochHdrWords + 1 +
      ((m : ℕ) +
        reducedLimbCount (reducedTrinomialStep (qBits 2 1) (hashB 1) (totalMicroBits 1)) *
          (j : ℕ)) ≤ 231 := by
    unfold epochHdrWords
    omega
  unfold testOneMem
  split_ifs with h1 h2 h3 h4 h4_2 h5 <;> try omega

theorem test_hashRep_one :
    ReducedKWise.Rep (0 + epochHdrWords) 64 (qBits 2 1) (hashB 1) (totalMicroBits 1) 3
      θ_one testOneMem :=
  ⟨test_tableRep_one, test_seedRep_one⟩

theorem hoff1 : offCompGM 2 64 1 = 260 := by
  unfold offCompGM offCompLM lmSubWords totalMicroBuckets
    effBucketPosBits effBucketCap numMicroPerBucket totalMicroBits microBits
    Dynamic.logLogFactor epochHdrWords
    epochHashSpace ReducedKWise.space ReducedKWise.seedWords ReducedKWise.tableWords
    reducedTrinomialStep reducedTargetBits trinomialStepAux
  decide

theorem hoff2 : offGM 2 2 (ghostW 64) 1 (epochHashSpace 2 (ghostW 64) 1) = 41 := by
  unfold offGM ghostW epochHashSpace offLM lmSubWords totalMicroBuckets
    effBucketPosBits effBucketCap numMicroPerBucket totalMicroBits microBits Dynamic.logLogFactor
    offVal offQuot bucketBits quotientBits valBits
    ReducedKWise.space ReducedKWise.seedWords ReducedKWise.tableWords
    reducedTrinomialStep reducedTargetBits trinomialStepAux
  decide

theorem h_qb : quotientBits 2 1 = 1 := by
  unfold quotientBits keyBits bucketBits; decide

theorem h_vb : valBits 2 = 1 := by
  unfold valBits; decide

theorem h_llf : logLogFactor 1 = 1 := by
  unfold logLogFactor; decide

theorem h_ehb : epochHashB 1 = 1 := by
  unfold epochHashB totalMicroBits microBits logLogFactor; decide

theorem h_eqb : epochQBits 2 1 = 1 := by
  unfold epochQBits; decide

theorem h_bb : bucketBits 1 = 0 := by
  unfold bucketBits; decide

theorem h_items : offCompItems 2 64 1 = 267 := by
  unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM lmSubWords totalMicroBuckets
    effBucketPosBits effBucketCap numMicroPerBucket totalMicroBits microBits
    epochHdrWords epochHashSpace ReducedKWise.space ReducedKWise.seedWords ReducedKWise.tableWords
    reducedTrinomialStep reducedTargetBits maxTailItems globalMetaLen
    globalMetaVarLen globalPtrBits numBuckets
  rw [h_ehb, h_eqb, h_bb, h_llf]
  unfold trinomialStepAux packedWords
  decide

theorem test_quot : compQuotAt 267 2 2 64 1 1 testOneMem 0 = 0 := by
  unfold compQuotAt
  rw [h_qb, h_vb]
  dsimp only
  unfold readBitSlice wOffQ bOffQ wordOffset bitOffset
  decide

theorem test_val : compValAt 267 2 2 64 1 1 testOneMem 0 = 0 := by
  unfold compValAt
  rw [h_qb, h_vb]
  dsimp only
  unfold readBitSlice wOffV bOffV wOffQ bOffQ wordOffset bitOffset
  decide

theorem test_fix_quot :
    quotAt 0 2 (ghostW 64) 1 (epochHashSpace 2 (ghostW 64) 1) testFixMem 0 = 0 := by
  unfold quotAt offQuot readPacked readBitSlice wordOffset bitOffset ghostW epochHashSpace
    ReducedKWise.space ReducedKWise.seedWords ReducedKWise.tableWords
    reducedTrinomialStep reducedTargetBits trinomialStepAux
    quotientBits bucketBits keyBits testFixMem
  decide

theorem test_fix_val :
    valAt 0 2 2 (ghostW 64) 1 (epochHashSpace 2 (ghostW 64) 1) testFixMem 0 = 0 := by
  unfold valAt offVal offQuot packedWords readPacked readBitSlice wordOffset bitOffset
    ghostW epochHashSpace
    ReducedKWise.space ReducedKWise.seedWords ReducedKWise.tableWords
    reducedTrinomialStep reducedTargetBits trinomialStepAux
    valBits quotientBits bucketBits keyBits testFixMem
  decide

theorem test_gm_eq :
    compGmAt 0 2 64 1 testOneMem =
      gmAt 0 2 2 (ghostW 64) 1 (epochHashSpace 2 (ghostW 64) 1) testFixMem := by
  funext idx
  unfold compGmAt gmAt globalPtrBits
  rw [hoff1, hoff2]
  have hgml : globalMetaLen 1 = 4 := by
    unfold globalMetaLen globalMetaVarLen bucketBits; decide
  split_ifs with h1 <;> try rfl
  rw [hgml] at h1
  interval_cases idx <;> decide

theorem test_lm_eq :
    compLmAt 0 2 64 1 testOneMem =
      lmAt 0 2 2 (ghostW 64) 1 (epochHashSpace 2 (ghostW 64) 1) testFixMem := by
  funext ⟨c, idx⟩
  have htmb : totalMicroBuckets 1 = 1 := by
    unfold totalMicroBuckets totalMicroBits microBits bucketBits logLogFactor; decide
  unfold compLmAt lmAt effBucketPosBits
  rw [htmb]
  dsimp only
  split_ifs with h1 <;> try rfl
  rcases h1 with ⟨hc, hidx⟩
  have : idx = 0 := by omega
  subst this
  interval_cases c <;>
    { unfold offCompLMSub offLMSub offCompLM offLM epochHdrWords epochHashSpace ghostW
        lmSubWords totalMicroBuckets effBucketCap numMicroPerBucket totalMicroBits microBits
        logLogFactor ReducedKWise.space ReducedKWise.seedWords ReducedKWise.tableWords
        reducedTrinomialStep reducedTargetBits trinomialStepAux
        offVal offQuot packedWords quotientBits valBits bucketBits
        readPacked readBitSlice wordOffset bitOffset testOneMem testFixMem
      decide }

theorem test_td_lt (mem : ℕ → ℕ) (i : ℕ) :
    compTDAt 0 2 64 1 mem i < max (maxTailItems 1) 1 := by
  have hm : maxTailItems 1 = 0 := by
    unfold maxTailItems numBuckets tailCapPerBucket bucketBits; decide
  unfold compTDAt
  rw [hm]
  have : ¬(i < 0) := by omega
  simp [this]

theorem test_dt_lt (mem : ℕ → ℕ) (i : ℕ) :
    compDTAt 0 2 64 1 mem i < max (maxTailItems 1) 1 := by
  have hm : maxTailItems 1 = 0 := by
    unfold maxTailItems numBuckets tailCapPerBucket bucketBits; decide
  unfold compDTAt
  rw [hm]
  have : ¬(i < 0) := by omega
  simp [this]

theorem test_phys (b : ℕ) (dt : ℕ → ℕ) : physByBase 1 b dt 0 = 0 := by
  have hbb : bucketBits 1 = 0 := by decide
  unfold physByBase
  rw [hbb]
  rfl

theorem test_tot : totalSlots 1 (compGmAt 0 2 64 1 testOneMem) = 1 := by
  unfold totalSlots bucketBits
  unfold compGmAt globalPtrBits; rw [hoff1]
  unfold globalMetaLen globalMetaVarLen; decide

theorem test_windowCoupled :
    WindowCoupled 0 (0 + offCompItems 2 64 1) 2 2 64 1
      (compGmAt 0 2 64 1 testOneMem 0 * slabSize 1)
      (if bucketBits 1 = 0 then 0 else compGmAt 0 2 64 1 testOneMem 1)
      (epochTotalSlots 1 (compGmAt 0 2 64 1 testOneMem))
      testSFix ⟨testOneMem, 270⟩ := by
  refine ⟨test_gm_eq, test_lm_eq, ?_, test_td_lt testOneMem, test_dt_lt testOneMem, ?_, ?_⟩
  · unfold bucketBits
    exact windowInv_zero _ _ _ _
  · intro d hd
    have hslots : epochTotalSlots 1 (compGmAt 0 2 64 1 testOneMem) = 1 := test_tot
    rw [hslots] at hd ⊢
    have : d = 0 := by omega
    subst this
    dsimp only [testSFix]
    rw [test_phys, Nat.zero_add, h_items, test_quot, test_fix_quot]
  · intro d hd
    have hslots : epochTotalSlots 1 (compGmAt 0 2 64 1 testOneMem) = 1 := test_tot
    rw [hslots] at hd ⊢
    have : d = 0 := by omega
    subst this
    dsimp only [testSFix]
    rw [test_phys, Nat.zero_add, h_items, test_val, test_fix_val]

theorem test_fixedCoupled_one :
    FixedCoupled 0 (0 + offCompItems 2 64 1) 2 2 64 1 testSFix ⟨testOneMem, 270⟩ :=
  test_windowCoupled

theorem feistelReconstruct_zero (h1 : ℕ → ℕ) (bucket q : ℕ) :
    feistelReconstruct 0 h1 bucket q = q := by
  unfold feistelReconstruct
  rw [pow_zero, Nat.mod_one, Nat.mod_one]
  change q * 1 + 0 = q
  omega

theorem feistel_at_one (h1 : ℕ → ℕ) (b q : ℕ) :
    feistelReconstruct (bucketBits 1) h1 b q = q := by
  have : bucketBits 1 = 0 := by decide
  rw [this]
  exact feistelReconstruct_zero h1 b q

theorem test_bucketMap_0_0 :
    bucketMapOfState 2 1 (hValOfSeed 2 1 θ_one) s_abs_one 0 0 = some 0 := by
  unfold bucketMapOfState
  simp only [feistel_at_one]
  split_ifs with hcond
  · unfold s_abs_one; rfl
  · exfalso; apply hcond
    refine ⟨by decide, by decide, by decide⟩

theorem test_bucketMap_ne_zero (q : ℕ) (hq : q ≠ 0) :
    bucketMapOfState 2 1 (hValOfSeed 2 1 θ_one) s_abs_one 0 q = none := by
  unfold bucketMapOfState
  simp only [feistel_at_one]
  split_ifs with hcond
  · have : q = 1 := by omega
    subst this
    unfold s_abs_one
    rfl
  · rfl

theorem test_fits_hash (i : Fin 19) :
    Fits 64 (RuntimeReducedKWise.mkHashParams 64 (epochQBits 2 1) (epochHashB 1)
      (totalMicroBits 1) 3 i) := by
  apply RuntimeReducedKWise.fits_mkHashParams (w := 64) (w₀ := epochQBits 2 1) (b := epochHashB 1)
    (b' := totalMicroBits 1) (k := 3) (hashBase := 0) (scratchBase := 0)
  · decide
  · decide
  · decide
  · rw [h_step_epoch]; decide
  · unfold ReducedKWise.space ReducedKWise.tableWords ReducedKWise.seedWords
    rw [h_step_epoch]; decide
  · decide

theorem test_fits_comp (i : Fin 36) :
    Fits 64 (mkCompParams 2 2 64 1 i) := by
  apply fits_mkCompParams (U := 2) (V := 2) (w := 64) (N := 1) (metaBase := 0)
  · decide
  · decide
  · decide
  · decide
  · rw [h_items]; decide

theorem test_dictStateInv_one :
    DictStateInv 2 2 (ghostW 64) 1 0 θ_one s_abs_one testSFix := by
  have hsf_mem : testSFix.mem = testFixMem := rfl
  have hhs : hashSpace 2 (ghostW 64) 1 = epochHashSpace 2 (ghostW 64) 1 := rfl
  have hnb : numBuckets 1 = 1 := by
    unfold numBuckets bucketBits; decide
  have hbb : bucketBits 1 = 0 := by decide
  have hmpb : numMicroPerBucket 1 = 1 := by decide
  have heff : effBucketCap 1 = 4 := by
    unfold effBucketCap; decide
  have hbc : bCount 1 (gmAt 0 2 2 (ghostW 64) 1
      (hashSpace 2 (ghostW 64) 1) testFixMem) 0 = 1 := by
    rw [hhs]
    unfold bCount gmAt globalPtrBits; rw [hoff2]
    unfold globalMetaLen globalMetaVarLen; decide
  have hslot : slotOf 1 (gmAt 0 2 2 (ghostW 64) 1
      (hashSpace 2 (ghostW 64) 1) testFixMem) 0 0 = 0 := by
    rw [hhs]
    unfold slotOf gmAt globalPtrBits; rw [hoff2]
    unfold globalMetaLen globalMetaVarLen; decide
  refine ⟨⟨fun _ _ => [0], ?_⟩, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨fun _ => ?_, fun hb => by rw [hbb] at hb; omega,
        fun hb => by rw [hbb] at hb; omega,
        fun hb => by rw [hbb] at hb; omega,
        fun hb => by rw [hbb] at hb; omega⟩
      rw [hsf_mem]
      have : gmAt 0 2 2 (ghostW 64) 1 (hashSpace 2 (ghostW 64) 1) testFixMem 0 = 1 := by
        rw [hhs]
        unfold gmAt globalPtrBits; rw [hoff2]
        unfold globalMetaLen globalMetaVarLen; decide
      omega
    · refine ⟨fun b hb m hm => ?_,
        fun b hb m₁ hm₁ m₂ hm₂ j hj₁ hj₂ => by rw [hmpb] at hm₁ hm₂; omega⟩
      have : b = 0 := by rw [hnb] at hb; omega
      subst this
      have : m = 0 := by rw [hmpb] at hm; omega
      subst this
      rw [hsf_mem]
      have h_head :
          lmHead 1 (lmAt 0 2 2 (ghostW 64) 1 (hashSpace 2 (ghostW 64) 1) testFixMem) 0 0 = 1 := by
        rw [hhs]
        unfold lmHead lmAt effBucketPosBits offLMSub offLM epochHashSpace ghostW
          lmSubWords totalMicroBuckets effBucketCap numMicroPerBucket totalMicroBits microBits
          logLogFactor ReducedKWise.space ReducedKWise.seedWords ReducedKWise.tableWords
          reducedTrinomialStep reducedTargetBits trinomialStepAux
          offVal offQuot packedWords quotientBits valBits bucketBits
          readPacked readBitSlice wordOffset bitOffset testFixMem
        decide
      have h_prev :
          lmPrev 1 (lmAt 0 2 2 (ghostW 64) 1 (hashSpace 2 (ghostW 64) 1) testFixMem) 0 0 = 0 := by
        rw [hhs]
        unfold lmPrev lmAt effBucketPosBits offLMSub offLM epochHashSpace ghostW
          lmSubWords totalMicroBuckets effBucketCap numMicroPerBucket totalMicroBits microBits
          logLogFactor ReducedKWise.space ReducedKWise.seedWords ReducedKWise.tableWords
          reducedTrinomialStep reducedTargetBits trinomialStepAux
          offVal offQuot packedWords quotientBits valBits bucketBits
          readPacked readBitSlice wordOffset bitOffset testFixMem
        decide
      have h_next :
          lmNext 1 (lmAt 0 2 2 (ghostW 64) 1 (hashSpace 2 (ghostW 64) 1) testFixMem) 0 0 = 0 := by
        rw [hhs]
        unfold lmNext lmAt effBucketPosBits offLMSub offLM epochHashSpace ghostW
          lmSubWords totalMicroBuckets effBucketCap numMicroPerBucket totalMicroBits microBits
          logLogFactor ReducedKWise.space ReducedKWise.seedWords ReducedKWise.tableWords
          reducedTrinomialStep reducedTargetBits trinomialStepAux
          offVal offQuot packedWords quotientBits valBits bucketBits
          readPacked readBitSlice wordOffset bitOffset testFixMem
        decide
      refine ⟨by rw [h_head]; rfl, by omega, by decide, h_prev, h_next, trivial⟩
    · intro b hb m hm j
      have : b = 0 := by rw [hnb] at hb; omega
      subst this
      have : m = 0 := by rw [hmpb] at hm; omega
      subst this
      rw [hsf_mem]
      simp only [List.mem_singleton]
      constructor
      · rintro rfl
        have hlt := mOfSeed_lt 2 1 θ_one (quotAt 0 2 (ghostW 64) 1
            (hashSpace 2 (ghostW 64) 1) testFixMem
            (slotOf 1 (gmAt 0 2 2 (ghostW 64) 1 (hashSpace 2 (ghostW 64) 1) testFixMem)
              0 0))
        rw [hmpb] at hlt
        have hm0 : mOfSeed 2 1 θ_one (quotAt 0 2 (ghostW 64) 1
            (hashSpace 2 (ghostW 64) 1) testFixMem
            (slotOf 1 (gmAt 0 2 2 (ghostW 64) 1 (hashSpace 2 (ghostW 64) 1) testFixMem)
              0 0)) = 0 := by omega
        exact ⟨by omega, by omega, hm0⟩
      · rintro ⟨hj, _, _⟩
        omega
    · intro b hb j₁ hj₁ j₂ hj₂ _
      have : b = 0 := by rw [hnb] at hb; omega
      subst this
      rw [hsf_mem] at hj₁ hj₂
      omega
    · intro b hb j hj
      have : b = 0 := by rw [hnb] at hb; omega
      subst this
      rw [hsf_mem] at hj ⊢
      have : j = 0 := by omega
      subst this
      rw [hslot, hhs, test_fix_quot, test_fix_val]
      exact test_bucketMap_0_0
    · intro b hb q
      have : b = 0 := by rw [hnb] at hb; omega
      subst this
      rw [hsf_mem]
      constructor
      · intro hisSome
        refine ⟨0, by omega, ?_⟩
        rw [hslot, hhs, test_fix_quot]
        by_cases hq0 : q = 0
        · exact hq0.symm
        · exfalso
          rw [test_bucketMap_ne_zero q hq0] at hisSome
          cases hisSome
      · rintro ⟨j, hj, hq_eq⟩
        have hj0 : j = 0 := by omega
        subst hj0
        rw [hslot, hhs, test_fix_quot] at hq_eq
        subst hq_eq
        rw [test_bucketMap_0_0]
        rfl
  · have htot : totalSlots 1 (gmAt 0 2 2 (ghostW 64) 1
        (hashSpace 2 (ghostW 64) 1) testFixMem) = 1 := by
      rw [hhs]
      unfold totalSlots bucketBits
      unfold gmAt globalPtrBits; rw [hoff2]
      unfold globalMetaLen globalMetaVarLen; decide
    rw [hsf_mem, htot]
    unfold s_abs_one
    decide

theorem test_compactedSplitRep_one :
    CompactedSplitRep 0 (0 + offCompItems 2 64 1) 2 2 64 1 1 0 θ_one s_abs_one
      ⟨testOneMem, 270⟩ := by
  refine ⟨test_rootHeaderValid_one, test_epochParamsStored_one, test_hashRep_one, ?_, ?_,
    ⟨testSFix, ?_, ?_, test_fixedCoupled_one⟩⟩
  · unfold s_abs_one; decide
  · intro u v hsome
    unfold s_abs_one at hsome
    fin_cases u
    · rw [Function.update_self] at hsome
      cases hsome
      decide
    · rw [Function.update_of_ne (by decide)] at hsome
      cases hsome
  · exact test_dictStateInv_one
  · have htot : totalSlots 1 (compGmAt 0 2 64 1 testOneMem) = 1 := test_tot
    have hcard : (Dictionary.dom s_abs_one).card = 1 := by
      unfold s_abs_one; decide
    omega

/-- Test 12 (Concrete non-empty witness): Genuine concrete resting state `CompactedRep`
witness for $n = 1$ with zero uninstantiated hypotheses. -/
theorem test_compactedRep_one_witness :
    CompactedRep 2 2 64 1 1 0 0 s_abs_one testXOne := by
  have hx : testXOne.Bounded 64 := by
    refine ⟨⟨fun i => Fin.elim0 i, ?_⟩, by decide, ?_⟩
    · intro a
      change testOneMem a < 2 ^ 64
      unfold testOneMem
      split_ifs with h1 h2 h3 h4 h5 h6
      · interval_cases a <;> decide
      · exact test_fits_hash ⟨a - 8, by omega⟩
      · exact test_fits_comp ⟨a - 27, by omega⟩
      · subst h4; decide
      · subst h5; decide
      · subst h6; decide
      · decide
    · intro a ha
      change testOneMem a = 0
      unfold testOneMem
      have h270 : 270 ≤ a := ha
      have : a ≠ 0 := by omega
      have : a ≠ 1 := by omega
      have : a ≠ 2 := by omega
      have : a ≠ 3 := by omega
      have : a ≠ 4 := by omega
      have : a ≠ 5 := by omega
      have : a ≠ 6 := by omega
      have : a ≠ 7 := by omega
      have : ¬(a < 8) := by omega
      have : ¬(a < 27) := by omega
      have : ¬(27 ≤ a ∧ a < 63) := by omega
      have : a ≠ 232 := by omega
      have : a ≠ 233 := by omega
      have : a ≠ 260 := by omega
      split_ifs
      rfl
  have hfr : testXOne.frontier = 0 + compactedEpochWords 2 2 64 1 1 := by
    unfold testXOne compactedEpochWords compactedItemWords
    rw [Nat.zero_add, h_items]
    decide
  have hepoch : EpochValid 2 1 1 := Or.inr ⟨by decide, by decide, by decide, by decide⟩
  exact compactedRep_of_split hx hfr hepoch test_compactedSplitRep_one

/-- Test 13 (Concrete evaluation): Genuine concrete evaluation of `reconstructKeyAt` and
`compValAt` on live slot 0 of the concrete $n = 1$ state yielding key 0 and value 0. -/
theorem test_reconstructKeyAt_concrete_eval :
    reconstructKeyAt 0 (0 + offCompItems 2 64 1) 2 2 64 1 1 θ_one testOneMem 0 = 0 ∧
    compValAt (0 + offCompItems 2 64 1) 2 2 64 1 1 testOneMem 0 = 0 := by
  refine ⟨?_, ?_⟩
  · unfold reconstructKeyAt
    have hbb : bucketBits 1 = 0 := by decide
    rw [hbb, feistelReconstruct_zero]
    change compQuotAt (0 + offCompItems 2 64 1) 2 2 64 1 1 testOneMem 0 = 0
    rw [Nat.zero_add, h_items]
    exact test_quot
  · rw [Nat.zero_add, h_items]
    exact test_val

