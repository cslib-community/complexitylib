/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.WordRAM.SuccinctChainOps
import Complexity.Tactic.Realize

/-!
# Bucket-Level Dictionary Lookup and Insertion (`query`, `insert`) in `Memory.Prog`

This module defines the bucket-level representation invariant `BucketStateInv` and realizes the
bucket-level lookup and insertion operations of the fixed-capacity succinct dictionary in
`Memory.Prog` via `realize`:
* `BucketStateInv`: couples `SlotStoreInv`, `AllChainsValid`, indexed micro-chain membership,
  per-bucket quotient uniqueness, and the abstract per-bucket quotient-to-value map `B`;
* `queryBodyProg_bucket_spec`: lookup correctness and probe-excess cost bound under
  `BucketStateInv`;
* `insertBodyProg` and `realizes_insertBodyGen`: bucket-level `insert` (update in-place if present,
  otherwise append to bucket and prepend to micro-chain if `< effBucketCap n_max`).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.BucketStateInv`: bucket-level representation
  invariant coupling `SlotStoreInv`, `AllChainsValid`, and the abstract per-bucket map `B`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.insertBodyProg`: `Memory.Prog` operation for
  bucket-level insertion (`update` in place if present, otherwise `pushBackSlotProg` +
  `prependIfIndexedProg`).

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.bucketStateInv_of_zero`: an all-zero dictionary
  memory region satisfies `BucketStateInv` with empty buckets and zero potential.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.queryBodyProg_bucket_spec`: lookup correctness
  and probe-excess `memoryCost` bound for `queryBodyProg` under `BucketStateInv`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.insertBodyProg_bucket_spec`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_insertBodyGen`: insertion correctness,
  `BucketStateInv` preservation, amortized `memoryCost` bound, and `Realizes` certificate for
  `insertBodyProg`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.Succinct

open Cslib.WordRAM Cslib.WordRAM.ExactLog Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.WordRAM Cslib.DataStructure.WordRAM.Randomized
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray

/-! ## Section 1: `BucketStateInv` and `queryBodyProg_bucket_spec` -/

/-- Combined bucket-level state invariant at `base` with local micro-bucket mapping `mOf : ℕ → ℕ`,
per-bucket micro-chain lists `L : ℕ → ℕ → List ℕ`, and abstract per-bucket quotient-to-value map
`B : ℕ → ℕ → Option ℕ`. -/
structure BucketStateInv (U V w₀ n_max h_space base : ℕ)
    (mOf : ℕ → ℕ) (L : ℕ → ℕ → List ℕ) (B : ℕ → ℕ → Option ℕ) (s : Memory.State) : Prop where
  hslot : SlotStoreInv n_max (gmAt base U V w₀ n_max h_space s.mem)
  hchains : AllChainsValid n_max (lmAt base U V w₀ n_max h_space s.mem) L
  hchain_mem : ∀ b < numBuckets n_max, ∀ m < numMicroPerBucket n_max, ∀ j,
    j ∈ L b m ↔
      j < bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b ∧
      j < effBucketCap n_max ∧
      mOf (quotAt base U w₀ n_max h_space s.mem
        (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b j)) = m
  hnodup_q : ∀ b < numBuckets n_max,
    ∀ j₁ < bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b,
    ∀ j₂ < bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b,
    quotAt base U w₀ n_max h_space s.mem
      (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b j₁) =
    quotAt base U w₀ n_max h_space s.mem
      (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b j₂) →
    j₁ = j₂
  hmap_some : ∀ b < numBuckets n_max,
    ∀ j < bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b,
    B b (quotAt base U w₀ n_max h_space s.mem
      (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b j)) =
    some (valAt base U V w₀ n_max h_space s.mem
      (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b j))
  hmap_dom : ∀ b < numBuckets n_max, ∀ q,
    (B b q).isSome ↔
      ∃ j < bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b,
        quotAt base U w₀ n_max h_space s.mem
          (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b j) = q

/-- An all-zero dictionary memory region satisfies `BucketStateInv` with empty chains and empty
bucket maps. -/
theorem bucketStateInv_of_zero {U V w₀ n_max h_space base : ℕ} (mOf : ℕ → ℕ)
    {s : Memory.State}
    (hgm0 : ∀ i, gmAt base U V w₀ n_max h_space s.mem i = 0)
    (hlm0 : ∀ p, lmAt base U V w₀ n_max h_space s.mem p = 0) :
    BucketStateInv U V w₀ n_max h_space base mOf (fun _ _ => []) (fun _ _ => none) s ∧
    totalSlots n_max (gmAt base U V w₀ n_max h_space s.mem) = 0 ∧
    slotPotential n_max (gmAt base U V w₀ n_max h_space s.mem) = 0 := by
  obtain ⟨hslot, hbc0, hpot0⟩ := slotStoreInv_of_zero n_max hgm0
  have hchains := allChainsValid_of_zero n_max hlm0
  have htot0 := totalSlots_of_zero n_max hgm0
  refine ⟨⟨hslot, hchains, fun b _ m _ j => ?_, fun b _ j₁ hj₁ => by rw [hbc0 b] at hj₁; omega,
    fun b _ j hj => by rw [hbc0 b] at hj; omega,
    fun b _ q => ?_⟩, htot0, hpot0⟩
  · rw [hbc0 b]
    simp
  · rw [hbc0 b]
    simp

/-- `BucketStateInv` implies `SearchMicroChainPre` for any valid `(b, q_target, m)`. -/
theorem BucketStateInv.searchMicroChainPre {U V w₀ n_max h_space w base b q_target m : ℕ}
    {mOf : ℕ → ℕ} {L : ℕ → ℕ → List ℕ} {B : ℕ → ℕ → Option ℕ} {s : Memory.State}
    (hinv : BucketStateInv U V w₀ n_max h_space base mOf L B s)
    (henv : DictEnvGen w (mkDictParams U V w₀ n_max h_space) base)
    (hb : b < numBuckets n_max) (hm : m < numMicroPerBucket n_max) :
    SearchMicroChainPre U V w₀ n_max h_space w (((base, b), q_target), m) s :=
  ⟨henv, hb, hm, hinv.hslot, L b m, hinv.hchains.1 b hb m hm,
    fun j hj => ((hinv.hchain_mem b hb m hm j).mp hj).1⟩

/-- Under `BucketStateInv` and `m = mOf q_target < numMicroPerBucket n_max`, the two-phase search
condition in `searchBucketProg_spec` is equivalent to
`∃ j < bCount b, quotAt (slotOf b j) = q_target`. -/
theorem searchBucket_exists_iff {U V w₀ n_max h_space base b q_target m : ℕ}
    {mOf : ℕ → ℕ} {L : ℕ → ℕ → List ℕ} {B : ℕ → ℕ → Option ℕ} {s : Memory.State}
    (hinv : BucketStateInv U V w₀ n_max h_space base mOf L B s)
    (hb : b < numBuckets n_max) (hm_eq : m = mOf q_target)
    (hm_lt : m < numMicroPerBucket n_max) :
    let gm := gmAt base U V w₀ n_max h_space s.mem
    ((∃ j ∈ L b m, quotAt base U w₀ n_max h_space s.mem (slotOf n_max gm b j) = q_target) ∨
     (∃ j, effBucketCap n_max ≤ j ∧ j < bCount n_max gm b ∧
        quotAt base U w₀ n_max h_space s.mem (slotOf n_max gm b j) = q_target)) ↔
    (∃ j < bCount n_max gm b,
      quotAt base U w₀ n_max h_space s.mem (slotOf n_max gm b j) = q_target) := by
  intro gm
  constructor
  · rintro (⟨j, hj_in, hq⟩ | ⟨j, _, hj_lt, hq⟩)
    · exact ⟨j, ((hinv.hchain_mem b hb m hm_lt j).mp hj_in).1, hq⟩
    · exact ⟨j, hj_lt, hq⟩
  · rintro ⟨j, hj_lt, hq⟩
    by_cases hj_cap : j < effBucketCap n_max
    · left
      refine ⟨j, (hinv.hchain_mem b hb m hm_lt j).mpr ⟨hj_lt, hj_cap, ?_⟩, hq⟩
      rw [hq, hm_eq]
    · right
      exact ⟨j, by omega, hj_lt, hq⟩

/-- Specification of `searchBucketProg` under `BucketStateInv` when `m = mOf q_target`. -/
theorem searchBucketProg_bucket_spec {U V w₀ n_max h_space w base b q_target m : ℕ}
    {mOf : ℕ → ℕ} {L : ℕ → ℕ → List ℕ} {B : ℕ → ℕ → Option ℕ} {s : Memory.State}
    (hinv : BucketStateInv U V w₀ n_max h_space base mOf L B s)
    (henv : DictEnvGen w (mkDictParams U V w₀ n_max h_space) base)
    (hb : b < numBuckets n_max) (hm_eq : m = mOf q_target)
    (hm_lt : m < numMicroPerBucket n_max) :
    let gm := gmAt base U V w₀ n_max h_space s.mem
    let d := (((base, b), q_target), m)
    let prog := searchBucketProg U V w₀ n_max h_space d
    (Memory.spec 0).clientState s prog = s ∧
    memoryCost prog s ≤
      10 + 8 * (L b m).length + 6 * (bCount n_max gm b - effBucketCap n_max) ∧
    (let res := (Memory.spec 0).clientResult s prog
     if ∃ j < bCount n_max gm b,
         quotAt base U w₀ n_max h_space s.mem (slotOf n_max gm b j) = q_target then
       res.1.1 = 1 ∧
       res.1.2 < bCount n_max gm b ∧
       quotAt base U w₀ n_max h_space s.mem (slotOf n_max gm b res.1.2) = q_target ∧
       res.2 = slotOf n_max gm b res.1.2
     else
       res.1.1 = 0) := by
  intro gm d prog
  have hc_lt : ∀ j ∈ L b m, j < bCount n_max gm b :=
    fun j hj => ((hinv.hchain_mem b hb m hm_lt j).mp hj).1
  have hsb := searchBucketProg_spec henv hb hm_lt hinv.hslot (hinv.hchains.1 b hb m hm_lt) hc_lt
    (d := d)
  have hiff := searchBucket_exists_iff hinv hb hm_eq hm_lt
  refine ⟨hsb.1, hsb.2.1, ?_⟩
  have hres := hsb.2.2
  dsimp only [d, gm, prog] at hres hiff ⊢
  by_cases hex : ∃ j < bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b,
      quotAt base U w₀ n_max h_space s.mem
        (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b j) = q_target
  · rw [ite_eq_left (hiff.mpr hex)] at hres
    rw [ite_eq_left hex]
    exact ⟨hres.1, hres.2.1, hres.2.2.2.1, hres.2.2.2.2⟩
  · rw [ite_eq_right (mt hiff.mp hex)] at hres
    rw [ite_eq_right hex]
    exact hres

/-- Specification of `queryBodyProg` under `BucketStateInv` when `m = mOf q_target`:
returns `B b q_target` without modifying memory. -/
theorem queryBodyProg_bucket_spec {U V w₀ n_max h_space w base b q_target m : ℕ}
    {mOf : ℕ → ℕ} {L : ℕ → ℕ → List ℕ} {B : ℕ → ℕ → Option ℕ} {s : Memory.State}
    (hinv : BucketStateInv U V w₀ n_max h_space base mOf L B s)
    (henv : DictEnvGen w (mkDictParams U V w₀ n_max h_space) base)
    (hb : b < numBuckets n_max) (hm_eq : m = mOf q_target)
    (hm_lt : m < numMicroPerBucket n_max) :
    let gm := gmAt base U V w₀ n_max h_space s.mem
    let d := (((base, b), q_target), m)
    let prog := queryBodyProg U V w₀ n_max h_space d
    (Memory.spec 0).clientState s prog = s ∧
    memoryCost prog s ≤
      12 + 8 * (L b m).length + 6 * (bCount n_max gm b - effBucketCap n_max) ∧
    (Memory.spec 0).clientResult s prog = B b q_target := by
  intro gm d prog
  have hc_lt : ∀ j ∈ L b m, j < bCount n_max gm b :=
    fun j hj => ((hinv.hchain_mem b hb m hm_lt j).mp hj).1
  have hqb := queryBodyProg_spec henv hb hm_lt hinv.hslot (hinv.hchains.1 b hb m hm_lt) hc_lt
    (d := d)
  have hiff := searchBucket_exists_iff hinv hb hm_eq hm_lt
  refine ⟨hqb.1, hqb.2.1, ?_⟩
  have hres := hqb.2.2
  dsimp only [d, gm, prog] at hres hiff ⊢
  by_cases hex : ∃ j < bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b,
      quotAt base U w₀ n_max h_space s.mem
        (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b j) = q_target
  · rw [ite_eq_left (hiff.mpr hex)] at hres
    obtain ⟨j, hj_lt, hq_eq, hres_eq⟩ := hres
    rw [hres_eq, ← hq_eq, (hinv.hmap_some b hb j hj_lt)]
  · rw [ite_eq_right (mt hiff.mp hex)] at hres
    rw [hres]
    have hnot_some : ¬(B b q_target).isSome := mt (hinv.hmap_dom b hb q_target).mp hex
    cases hB : B b q_target with
    | none => rfl
    | some v => simp [hB] at hnot_some

/-! ## Section 2: `insertBodyProg` via `realize` -/

/-- Parameter-free helper `Memory.Prog` appending a new `(q_target, v_new)` entry to bucket `b` and
prepending its logical index `j_new = bCount b` to micro-chain `(b, m)` when `totalSlots < n_max`.
Input `d = (dp, ((((base, b), q_target), v_new), m))`. -/
@[expose]
def insertNewGenProg
    (d : DictParams × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)) : Memory.Prog Unit := do
  let tot ← readTotalSlotsGenProg (d.1, d.2.1.1.1.1)
  let cap ← pure (dpNMax d.1)
  if tot < cap then do
    let j_new ← readBucketCountGenProg (d.1, d.2.1.1.1)
    pushBackSlotGenProg (((d.1, d.2.1.1.1), d.2.1.1.2), d.2.1.2)
    prependIfIndexedGenProg ((d.1, (d.2.1.1.1, d.2.2)), j_new)
  else
    pure ()

/-- Helper `Memory.Prog` appending a new `(q_target, v_new)` entry to bucket `b` and prepending
its logical index `j_new = bCount b` to micro-chain `(b, m)` when `totalSlots < n_max`.
Input `d = ((((base, b), q_target), v_new), m)`. -/
@[expose]
def insertNewProg (U V w n_max h_space : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) : Memory.Prog Unit := do
  let tot ← readTotalSlotsProg U V w n_max h_space d.1.1.1.1
  let cap ← pure n_max
  if tot < cap then do
    let j_new ← readBucketCountProg U V w n_max h_space d.1.1.1
    pushBackSlotProg U V w n_max h_space d.1
    prependIfIndexedProg U V w n_max h_space ((d.1.1.1, d.2), j_new)
  else
    pure ()

@[simp]
theorem insertNewGenProg_mk (U V w n_max h_space : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) :
    insertNewGenProg (mkDictParams U V w n_max h_space, d) =
      insertNewProg U V w n_max h_space d := by
  simp only [insertNewGenProg, insertNewProg, readTotalSlotsGenProg_mk, p_nMax_mk,
    readBucketCountGenProg_mk, pushBackSlotGenProg_mk, prependIfIndexedGenProg_mk]

/-- Precondition for `insertNewProg` in `Realizes`. -/
@[expose]
def InsertNewPre (U V w₀ n_max h_space w : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) (s : Memory.State) : Prop :=
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) d.1.1.1.1 ∧
  d.1.1.1.2 < numBuckets n_max ∧
  d.2 < numMicroPerBucket n_max ∧
  d.1.1.2 < 2 ^ quotientBits U n_max ∧
  d.1.2 < 2 ^ valBits V ∧
  SlotStoreInv n_max (gmAt d.1.1.1.1 U V w₀ n_max h_space s.mem) ∧
  lmHead n_max (lmAt d.1.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.1.2 d.2 ≤ effBucketCap n_max

/-- Parameter-free precondition for `insertNewGenProg` in `Realizes`. -/
@[expose]
def InsertNewGenPre (w : ℕ)
    (d : DictParams × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)) (s : Memory.State) : Prop :=
  DictEnvGen w d.1 d.2.1.1.1.1 ∧
  d.2.1.1.1.2 < numBuckets (dpNMax d.1) ∧
  d.2.2 < numMicroPerBucket (dpNMax d.1) ∧
  d.2.1.1.2 < 2 ^ quotientBits (dpU d.1) (dpNMax d.1) ∧
  d.2.1.2 < 2 ^ valBits (dpV d.1) ∧
  SlotStoreInv (dpNMax d.1)
    (gmAt d.2.1.1.1.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem) ∧
  lmHead (dpNMax d.1)
    (lmAt d.2.1.1.1.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem)
    d.2.1.1.1.2 d.2.2 ≤ effBucketCap (dpNMax d.1)

@[simp]
theorem insertNewGenPre_mk (U V w₀ n_max h_space w : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    InsertNewGenPre w (mkDictParams U V w₀ n_max h_space, d) s ↔
      InsertNewPre U V w₀ n_max h_space w d s := Iff.rfl

theorem realizes_insertNewGen :
    Realizes .exact insertNewGenProg
      (WordEncoding.encode (α := DictParams × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)))
      (WordEncoding.encode (α := Unit))
      InsertNewGenPre
      (fun _ _ => 0) := by
  have htot := realizes_readTotalSlotsGen
  have hbc := realizes_readBucketCountGen
  have hpb := realizes_pushBackSlotGen
  have hpr := realizes_prependIfIndexedGen
  realizeDictWith [insertNewGenPre_mk, InsertNewPre, readTotalSlotsGenProg_mk,
    pushBackSlotGenPre_mk, PushBackSlotPre, pushBackSlotGenProg_mk,
    prependIfIndexedGenPre_mk, PrependIfIndexedPre, prependIfIndexedGenProg_mk]
  · exact h.1
  · exact h.2.2.2.2.2.1
  · exact h.1
  · rw [clientState_readTotalSlotsProg]
    exact h.2.2.2.2.2.1
  · exact h.2.1
  · rw [clientState_readTotalSlotsProg, clientState_readBucketCountProg]
    rw [clientResult_readTotalSlotsProg] at hc
    exact ⟨h.1, h.2.2.2.2.2.1, h.2.1, hc, h.2.2.2.1, h.2.2.2.2.1⟩
  · rw [clientState_readTotalSlotsProg, clientState_readBucketCountProg]
    rw [clientResult_readTotalSlotsProg] at hc
    have eff := pushBackSlotProg_effect (U := U) (V := V) (w := w₀) (n_max := n_max)
      (h_space := h_space) (base := d.1.1.1.1) (b := d.1.1.1.2) (q_val := d.1.1.2)
      (v_val := d.1.2) hw s h.2.2.2.2.2.1 h.2.1 hc h.2.2.2.1 h.2.2.2.2.1
    refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
    rw [eff.2.2.1]
    exact h.2.2.2.2.2.2

/-- Parameter-free dictionary `insert` body `insertBodyGenProg`
(`d = (dp, ((((base, b), q_target), v_new), m))`). -/
@[expose]
def insertBodyGenProg
    (d : DictParams × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)) : Memory.Prog Unit := do
  let res ← searchBucketGenProg (d.1, (d.2.1.1, d.2.2))
  let z1 ← pure 1
  if res.1.1 = z1 then
    writeValGenProg (d.1, ((d.2.1.1.1.1, res.2), d.2.1.2))
  else
    insertNewGenProg d

/-- Dictionary `insert` body `insertBodyProg` (`d = ((((base, b), q_target), v_new), m)`):
searches bucket `b` for `q_target` via `searchBucketProg`; if found, overwrites `valAt` in-place;
otherwise calls `insertNewProg`. -/
@[expose]
def insertBodyProg (U V w n_max h_space : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) : Memory.Prog Unit := do
  let res ← searchBucketProg U V w n_max h_space (d.1.1, d.2)
  let z1 ← pure 1
  if res.1.1 = z1 then
    writeValProg U V w n_max h_space ((d.1.1.1.1, res.2), d.1.2)
  else
    insertNewProg U V w n_max h_space d

@[simp]
theorem insertBodyGenProg_mk (U V w n_max h_space : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) :
    insertBodyGenProg (mkDictParams U V w n_max h_space, d) =
      insertBodyProg U V w n_max h_space d := by
  simp only [insertBodyGenProg, insertBodyProg, searchBucketGenProg_mk, writeValGenProg_mk,
    insertNewGenProg_mk]

/-- Precondition for `insertBodyProg` in `Realizes`. -/
@[expose]
def InsertBodyPre (U V w₀ n_max h_space w : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) (s : Memory.State) : Prop :=
  SearchMicroChainPre U V w₀ n_max h_space w (d.1.1, d.2) s ∧
  d.1.1.2 < 2 ^ quotientBits U n_max ∧
  d.1.2 < 2 ^ valBits V

/-- Parameter-free precondition for `insertBodyGenProg` in `Realizes`. -/
@[expose]
def InsertBodyGenPre (w : ℕ)
    (d : DictParams × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)) (s : Memory.State) : Prop :=
  SearchMicroChainGenPre w (d.1, (d.2.1.1, d.2.2)) s ∧
  d.2.1.1.2 < 2 ^ quotientBits (dpU d.1) (dpNMax d.1) ∧
  d.2.1.2 < 2 ^ valBits (dpV d.1)

@[simp]
theorem insertBodyGenPre_mk (U V w₀ n_max h_space w : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    InsertBodyGenPre w (mkDictParams U V w₀ n_max h_space, d) s ↔
      InsertBodyPre U V w₀ n_max h_space w d s := Iff.rfl

theorem realizes_insertBodyGen :
    Realizes .exact insertBodyGenProg
      (WordEncoding.encode (α := DictParams × ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)))
      (WordEncoding.encode (α := Unit))
      InsertBodyGenPre
      (fun _ _ => 0) := by
  have hsb := realizes_searchBucketGen
  have hwv := realizes_writeValGen
  have hin := realizes_insertNewGen
  realize
  all_goals (
    rcases d with ⟨dp, d⟩
    obtain ⟨⟨U, V, w₀, n_max, h_space, hw, hnU, hU, hV, rfl⟩, henv⟩ := h.1.1
    simpDictParamsWith [insertBodyGenPre_mk, InsertBodyPre,
      searchMicroChainGenPre_mk, SearchMicroChainPre, searchBucketGenProg_mk,
      insertNewGenPre_mk, InsertNewPre, insertNewGenProg_mk]
  )
  · exact h.1
  · exact fits_const_of_dictEnv h.1.1 (by decide)
  · exact h.1.1
  · obtain ⟨L, hchain, hc_lt⟩ := h.1.2.2.2.2
    have hspec := (searchBucketProg_spec (d := (d.1.1, d.2))
      h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 hchain hc_lt).2.2
    dsimp only at hspec
    split_ifs at hspec with hex
    · rw [hspec.2.2.2.2]
      exact (slotOf_lt_and_injective h.1.2.2.2.1).1 d.1.1.1.2 h.1.2.1 _ hspec.2.1
    · omega
  · obtain ⟨L, hchain, hc_lt⟩ := h.1.2.2.2.2
    rw [(searchBucketProg_spec (d := (d.1.1, d.2))
      h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 hchain hc_lt).1]
    exact ⟨h.1.1, h.1.2.1, h.1.2.2.1, h.2.1, h.2.2, h.1.2.2.2.1, hchain.head_le_cap⟩

/-- Pure state effect, `BucketStateInv` preservation, and amortized `memoryCost` bound of
`insertBodyProg` when `m = mOf q_target` and `(B b q_target).isSome ∨ totalSlots < n_max`. -/
theorem insertBodyProg_bucket_spec {U V w₀ n_max h_space w base b q_target v_new m : ℕ}
    {mOf : ℕ → ℕ} {L : ℕ → ℕ → List ℕ} {B : ℕ → ℕ → Option ℕ} {s : Memory.State}
    (hw : 0 < w₀)
    (hinv : BucketStateInv U V w₀ n_max h_space base mOf L B s)
    (henv : DictEnvGen w (mkDictParams U V w₀ n_max h_space) base)
    (hb : b < numBuckets n_max) (hm_eq : m = mOf q_target)
    (hm_lt : m < numMicroPerBucket n_max)
    (hq_lt : q_target < 2 ^ quotientBits U n_max)
    (hv_lt : v_new < 2 ^ valBits V)
    (hcap : (B b q_target).isSome ∨
      totalSlots n_max (gmAt base U V w₀ n_max h_space s.mem) < n_max) :
    let gm₀ := gmAt base U V w₀ n_max h_space s.mem
    let d := ((((base, b), q_target), v_new), m)
    let s' := (Memory.spec 0).clientState s (insertBodyProg U V w₀ n_max h_space d)
    let gm' := gmAt base U V w₀ n_max h_space s'.mem
    let B' := Function.update B b (Function.update (B b) q_target (some v_new))
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offQuot h_space ≤ a ∧
        a < base + totalSpace U V w₀ n_max h_space) → s'.mem a = s.mem a) ∧
    (∃ L', BucketStateInv U V w₀ n_max h_space base mOf L' B' s') ∧
    totalSlots n_max gm' =
      (if (B b q_target).isSome then totalSlots n_max gm₀ else totalSlots n_max gm₀ + 1) ∧
    memoryCost (insertBodyProg U V w₀ n_max h_space d) s + 66 * slotPotential n_max gm' ≤
      66 * slotPotential n_max gm₀ + 170 +
        8 * (L b m).length + 6 * (bCount n_max gm₀ b - effBucketCap n_max) := by
  intro gm₀ d s' gm' B'
  dsimp only [gm₀, gm']
  have hsb := searchBucketProg_bucket_spec hinv henv hb hm_eq hm_lt (q_target := q_target)
  dsimp only at hsb
  set res := (Memory.spec 0).clientResult s
    (searchBucketProg U V w₀ n_max h_space (((base, b), q_target), m))
  have hres := hsb.2.2
  by_cases hex : ∃ j < bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b,
      quotAt base U w₀ n_max h_space s.mem
        (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b j) = q_target
  · rw [ite_eq_left hex] at hres
    rcases hres with ⟨hf1, hj_lt, hq_match, hphys_eq⟩
    have hsome : (B b q_target).isSome := (hinv.hmap_dom b hb q_target).mpr hex
    have hphys_lt : res.2 < n_max := by
      rw [hphys_eq]
      exact (slotOf_lt_and_injective hinv.hslot).1 b hb res.1.2 hj_lt
    have hs' : s' = (Memory.spec 0).clientState s
        (writeValProg U V w₀ n_max h_space ((base, res.2), v_new)) := by
      change (Memory.spec 0).clientState s (insertBodyProg U V w₀ n_max h_space d) = _
      unfold insertBodyProg
      simp only [pure_bind, d]
      rw [StateTransitionSpec.clientState_bind, hsb.1]
      change (Memory.spec 0).clientState s
        (if res.1.1 = 1 then writeValProg U V w₀ n_max h_space ((base, res.2), v_new)
         else insertNewProg U V w₀ n_max h_space d) = _
      rw [ite_eq_left hf1]
    have hcost : memoryCost (insertBodyProg U V w₀ n_max h_space d) s ≤
        16 + 8 * (L b m).length +
          6 * (bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b - effBucketCap n_max) := by
      unfold insertBodyProg
      simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, d]
      rw [memoryCost_bind, hsb.1]
      change memoryCost (searchBucketProg U V w₀ n_max h_space (((base, b), q_target), m)) s +
        memoryCost (if res.1.1 = 1 then writeValProg U V w₀ n_max h_space ((base, res.2), v_new)
          else insertNewProg U V w₀ n_max h_space d) s ≤ _
      rw [ite_eq_left hf1, memoryCost_writeValProg]
      have := hsb.2.1
      omega
    have eff := writeValProg_effect (U := U) (base := base) (h_space := h_space)
      hw hphys_lt hv_lt s
    have hgm_eq : gmAt base U V w₀ n_max h_space s'.mem =
        gmAt base U V w₀ n_max h_space s.mem := by rw [hs', eff.2.2.2.2.2]
    have hlm_eq : lmAt base U V w₀ n_max h_space s'.mem =
        lmAt base U V w₀ n_max h_space s.mem := by rw [hs', eff.2.2.2.2.1]
    have hq_eq : quotAt base U w₀ n_max h_space s'.mem =
        quotAt base U w₀ n_max h_space s.mem := by rw [hs', eff.2.2.1]
    have hv_eq : valAt base U V w₀ n_max h_space s'.mem =
        Function.update (valAt base U V w₀ n_max h_space s.mem) res.2 v_new := by
      rw [hs', eff.2.2.2.1]
    refine ⟨by rw [hs', eff.1],
      fun a ha => by
        rw [hs', eff.2.1 a
          (by dsimp only [totalSpace, offGM, offLM, offVal, offQuot] at ha ⊢; omega)],
      ⟨L, ?_⟩,
      by rw [hgm_eq, ite_eq_left hsome],
      by rw [hgm_eq]; omega⟩
    refine ⟨by rw [hgm_eq]; exact hinv.hslot,
      hinv.hchains.of_lm_eq hlm_eq,
      fun b' hb' m' hm' j => by rw [hgm_eq, hq_eq]; exact hinv.hchain_mem b' hb' m' hm' j,
      fun b' hb' j₁ hj₁ j₂ hj₂ => by
        rw [hgm_eq] at hj₁ hj₂
        rw [hgm_eq, hq_eq]
        exact hinv.hnodup_q b' hb' j₁ hj₁ j₂ hj₂,
      fun b' hb' j hj => ?_,
      fun b' hb' q => ?_⟩
    · rw [hgm_eq] at hj
      rw [hgm_eq, hq_eq, hv_eq]
      dsimp only [B']
      by_cases hbeq : b' = b
      · subst hbeq
        rw [Function.update_self]
        by_cases hjeq : j = res.1.2
        · subst hjeq
          rw [hq_match, ← hphys_eq, Function.update_self, Function.update_self]
        · have hq_ne :
              quotAt base U w₀ n_max h_space s.mem
                (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b' j) ≠ q_target :=
            fun heq => hjeq (hinv.hnodup_q b' hb' j hj res.1.2 hj_lt (heq.trans hq_match.symm))
          have hslot_ne : slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b' j ≠ res.2 := by
            rw [hphys_eq]
            intro heq
            exact hjeq
              ((slotOf_lt_and_injective hinv.hslot).2 b' hb' j hj b' hb' res.1.2 hj_lt heq).2
          rw [Function.update_of_ne hq_ne, Function.update_of_ne hslot_ne]
          exact hinv.hmap_some b' hb' j hj
      · have hslot_ne : slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b' j ≠ res.2 := by
          rw [hphys_eq]
          intro heq
          exact hbeq ((slotOf_lt_and_injective hinv.hslot).2 b' hb' j hj b hb res.1.2 hj_lt heq).1
        rw [Function.update_of_ne hbeq, Function.update_of_ne hslot_ne]
        exact hinv.hmap_some b' hb' j hj
    · rw [hgm_eq, hq_eq]
      dsimp only [B']
      by_cases hbeq : b' = b
      · subst hbeq
        rw [Function.update_self]
        by_cases hqeq : q = q_target
        · subst hqeq
          rw [Function.update_self]
          exact ⟨fun _ => hex, fun _ => rfl⟩
        · rw [Function.update_of_ne hqeq]
          exact hinv.hmap_dom b' hb' q
      · rw [Function.update_of_ne hbeq]
        exact hinv.hmap_dom b' hb' q
  · rw [ite_eq_right hex] at hres
    have hnot_some : ¬(B b q_target).isSome := mt (hinv.hmap_dom b hb q_target).mp hex
    have htot : totalSlots n_max (gmAt base U V w₀ n_max h_space s.mem) < n_max :=
      hcap.resolve_left hnot_some
    have hne1 : res.1.1 ≠ 1 := by omega
    let s₁ := (Memory.spec 0).clientState s
      (pushBackSlotProg U V w₀ n_max h_space (((base, b), q_target), v_new))
    let j_new := bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b
    have hs' : s' = (Memory.spec 0).clientState s₁
        (prependIfIndexedProg U V w₀ n_max h_space (((base, b), m), j_new)) := by
      change (Memory.spec 0).clientState s (insertBodyProg U V w₀ n_max h_space d) = _
      unfold insertBodyProg insertNewProg
      simp only [pure_bind, d]
      rw [StateTransitionSpec.clientState_bind, hsb.1]
      change (Memory.spec 0).clientState s
        (if res.1.1 = 1 then writeValProg U V w₀ n_max h_space ((base, res.2), v_new)
         else do
           let tot ← readTotalSlotsProg U V w₀ n_max h_space base
           if tot < n_max then do
             let j_new ← readBucketCountProg U V w₀ n_max h_space (base, b)
             pushBackSlotProg U V w₀ n_max h_space (((base, b), q_target), v_new)
             prependIfIndexedProg U V w₀ n_max h_space (((base, b), m), j_new)
           else pure ()) = _
      rw [ite_eq_right hne1, StateTransitionSpec.clientState_bind,
        clientState_readTotalSlotsProg, clientResult_readTotalSlotsProg,
        ite_eq_left htot, StateTransitionSpec.clientState_bind,
        clientState_readBucketCountProg, clientResult_readBucketCountProg (base, b) s hb,
        StateTransitionSpec.clientState_bind]
    have eff_pb := pushBackSlotProg_effect (U := U) (V := V) (w := w₀) (n_max := n_max)
      (h_space := h_space) (base := base) (b := b) (q_val := q_target) (v_val := v_new)
      hw s hinv.hslot hb htot hq_lt hv_lt
    rcases eff_pb with ⟨hf_pb, hout_pb, hlm_pb, hslot_s₁, htot_s₁, hbc_b_s₁, hbc_other_s₁,
      hq_new_s₁, hv_new_s₁, hold_s₁, hcost_pb⟩
    have hchains_s₁ : AllChainsValid n_max (lmAt base U V w₀ n_max h_space s₁.mem) L :=
      hinv.hchains.of_lm_eq hlm_pb
    have hj_new_lt_n : j_new < n_max :=
      lt_of_le_of_lt (bCount_le_totalSlots hinv.hslot b hb) htot
    have hj_not : ∀ m' < numMicroPerBucket n_max, j_new ∉ L b m' := by
      intro m' hm' hj_in
      have hlt := ((hinv.hchain_mem b hb m' hm' j_new).mp hj_in).1
      dsimp only [j_new] at hlt
      omega
    have eff_pr := prependIfIndexedProg_allChainsValid (U := U) (V := V) (w := w₀)
      (n_max := n_max) (h_space := h_space) (base := base) (b := b) (m := m) (j_new := j_new)
      hw hb hm_lt hj_new_lt_n hchains_s₁ hj_not
    rcases eff_pr with ⟨hf_pr, hout_pr, hq_pr, hv_pr, hgm_pr, L', hchains', hmem'⟩
    have hcost_in : memoryCost (insertBodyProg U V w₀ n_max h_space d) s ≤
        memoryCost (searchBucketProg U V w₀ n_max h_space (((base, b), q_target), m)) s +
        26 +
        memoryCost (pushBackSlotProg U V w₀ n_max h_space (((base, b), q_target), v_new)) s := by
      unfold insertBodyProg insertNewProg
      simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, d]
      rw [memoryCost_bind, hsb.1]
      change memoryCost (searchBucketProg U V w₀ n_max h_space (((base, b), q_target), m)) s +
        memoryCost (if res.1.1 = 1 then writeValProg U V w₀ n_max h_space ((base, res.2), v_new)
          else _) s ≤ _
      rw [ite_eq_right hne1, memoryCost_bind, clientState_readTotalSlotsProg,
        clientResult_readTotalSlotsProg, ite_eq_left htot,
        memoryCost_bind, clientState_readBucketCountProg,
        clientResult_readBucketCountProg (base, b) s hb,
        memoryCost_bind]
      have hc_tot := memoryCost_readTotalSlotsProg_le U V w₀ n_max h_space base s
      have hc_bc := memoryCost_readBucketCountProg_le (U := U) (V := V) (w := w₀) (n_max := n_max)
        (h_space := h_space) (base, b) s
      have hc_pr := memoryCost_prependIfIndexedProg_le U V w₀ n_max h_space
        (((base, b), m), bCount n_max (gmAt (base, b).1 U V w₀ n_max h_space s.mem) (base, b).2)
        ((Memory.spec 0).clientState s
          (pushBackSlotProg U V w₀ n_max h_space (((base, b), q_target), v_new)))
      omega
    have hgm'_eq : gmAt base U V w₀ n_max h_space s'.mem =
        gmAt base U V w₀ n_max h_space s₁.mem := by rw [hs', hgm_pr]
    have hq'_eq : quotAt base U w₀ n_max h_space s'.mem =
        quotAt base U w₀ n_max h_space s₁.mem := by rw [hs', hq_pr]
    have hv'_eq : valAt base U V w₀ n_max h_space s'.mem =
        valAt base U V w₀ n_max h_space s₁.mem := by rw [hs', hv_pr]
    refine ⟨by rw [hs', hf_pr, hf_pb],
      fun a ha => by
        rw [hs',
          hout_pr a (by dsimp only [totalSpace, offGM, offLM, offVal, offQuot] at ha ⊢; omega),
          hout_pb a ha],
      ⟨L', ?_⟩,
      by rw [hgm'_eq, htot_s₁, ite_eq_right hnot_some],
      by
        rw [hgm'_eq]
        have := hsb.2.1
        dsimp only [s₁] at hcost_in ⊢
        omega⟩
    refine ⟨by rw [hgm'_eq]; exact hslot_s₁,
      by rw [hs']; exact hchains',
      fun b' hb' m' hm' j => ?_,
      fun b' hb' j₁ hj₁ j₂ hj₂ hq_eq => ?_,
      fun b' hb' j hj => ?_,
      fun b' hb' q => ?_⟩
    · rw [hmem' b' hb' m' hm' j, hgm'_eq, hq'_eq]
      by_cases hbeq : b' = b
      · subst hbeq
        rw [hbc_b_s₁]
        by_cases hjeq : j = j_new
        · subst hjeq
          rw [hq_new_s₁, ← hm_eq]
          have hnot_in : j_new ∉ L b' m' := hj_not m' hm'
          constructor
          · rintro (h_in | ⟨_, rfl, _, hcap'⟩)
            · exact False.elim (hnot_in h_in)
            · exact ⟨by dsimp only [j_new]; omega, hcap', rfl⟩
          · rintro ⟨_, hcap', rfl⟩
            exact Or.inr ⟨rfl, rfl, rfl, hcap'⟩
        · rw [hinv.hchain_mem b' hb' m' hm' j]
          constructor
          · rintro (⟨hj_lt, hj_cap, hm_j⟩ | ⟨_, _, h_eq, _⟩)
            · rw [(hold_s₁ b' hb' j hj_lt).1]
              exact ⟨by omega, hj_cap, hm_j⟩
            · exact False.elim (hjeq h_eq)
          · rintro ⟨hj_lt1, hj_cap, hm_j⟩
            have hj_lt : j < bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b' := by
              dsimp only [j_new] at hjeq; omega
            rw [(hold_s₁ b' hb' j hj_lt).1] at hm_j
            exact Or.inl ⟨hj_lt, hj_cap, hm_j⟩
      · rw [hbc_other_s₁ b' hb' hbeq, hinv.hchain_mem b' hb' m' hm' j]
        constructor
        · rintro (⟨hj_lt, hj_cap, hm_j⟩ | ⟨h_eq, _⟩)
          · rw [(hold_s₁ b' hb' j hj_lt).1]
            exact ⟨hj_lt, hj_cap, hm_j⟩
          · exact False.elim (hbeq h_eq)
        · rintro ⟨hj_lt, hj_cap, hm_j⟩
          rw [(hold_s₁ b' hb' j hj_lt).1] at hm_j
          exact Or.inl ⟨hj_lt, hj_cap, hm_j⟩
    · rw [hgm'_eq] at hj₁ hj₂
      rw [hgm'_eq, hq'_eq] at hq_eq
      by_cases hbeq : b' = b
      · subst hbeq
        rw [hbc_b_s₁] at hj₁ hj₂
        by_cases hj1 : j₁ = j_new <;> by_cases hj2 : j₂ = j_new
        · rw [hj1, hj2]
        · subst hj1
          have hj2_lt : j₂ < bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b' := by
            dsimp only [j_new] at hj2; omega
          rw [hq_new_s₁, (hold_s₁ b' hb' j₂ hj2_lt).1] at hq_eq
          exact False.elim (hex ⟨j₂, hj2_lt, hq_eq.symm⟩)
        · subst hj2
          have hj1_lt : j₁ < bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b' := by
            dsimp only [j_new] at hj1; omega
          rw [hq_new_s₁, (hold_s₁ b' hb' j₁ hj1_lt).1] at hq_eq
          exact False.elim (hex ⟨j₁, hj1_lt, hq_eq⟩)
        · have hj1_lt : j₁ < bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b' := by
            dsimp only [j_new] at hj1; omega
          have hj2_lt : j₂ < bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b' := by
            dsimp only [j_new] at hj2; omega
          rw [(hold_s₁ b' hb' j₁ hj1_lt).1, (hold_s₁ b' hb' j₂ hj2_lt).1] at hq_eq
          exact hinv.hnodup_q b' hb' j₁ hj1_lt j₂ hj2_lt hq_eq
      · rw [hbc_other_s₁ b' hb' hbeq] at hj₁ hj₂
        rw [(hold_s₁ b' hb' j₁ hj₁).1, (hold_s₁ b' hb' j₂ hj₂).1] at hq_eq
        exact hinv.hnodup_q b' hb' j₁ hj₁ j₂ hj₂ hq_eq
    · rw [hgm'_eq] at hj
      rw [hgm'_eq, hq'_eq, hv'_eq]
      dsimp only [B']
      by_cases hbeq : b' = b
      · subst hbeq
        rw [Function.update_self]
        rw [hbc_b_s₁] at hj
        by_cases hjeq : j = j_new
        · subst hjeq
          rw [hq_new_s₁, hv_new_s₁, Function.update_self]
        · have hj_lt : j < bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b' := by
            dsimp only [j_new] at hjeq; omega
          rw [(hold_s₁ b' hb' j hj_lt).1, (hold_s₁ b' hb' j hj_lt).2]
          have hq_ne :
              quotAt base U w₀ n_max h_space s.mem
                (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b' j) ≠ q_target :=
            fun heq => hex ⟨j, hj_lt, heq⟩
          rw [Function.update_of_ne hq_ne]
          exact hinv.hmap_some b' hb' j hj_lt
      · rw [Function.update_of_ne hbeq]
        rw [hbc_other_s₁ b' hb' hbeq] at hj
        rw [(hold_s₁ b' hb' j hj).1, (hold_s₁ b' hb' j hj).2]
        exact hinv.hmap_some b' hb' j hj
    · rw [hgm'_eq, hq'_eq]
      dsimp only [B']
      by_cases hbeq : b' = b
      · subst hbeq
        rw [Function.update_self, hbc_b_s₁]
        by_cases hqeq : q = q_target
        · subst hqeq
          rw [Function.update_self]
          exact ⟨fun _ => ⟨j_new, by dsimp only [j_new]; omega, hq_new_s₁⟩, fun _ => rfl⟩
        · rw [Function.update_of_ne hqeq, hinv.hmap_dom b' hb' q]
          constructor
          · rintro ⟨j, hj_lt, hq_j⟩
            refine ⟨j, by omega, ?_⟩
            rw [(hold_s₁ b' hb' j hj_lt).1]
            exact hq_j
          · rintro ⟨j, hj_lt1, hq_j⟩
            by_cases hjeq : j = j_new
            · subst hjeq
              rw [hq_new_s₁] at hq_j
              exact False.elim (hqeq hq_j.symm)
            · have hj_lt : j < bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b' := by
                dsimp only [j_new] at hjeq; omega
              rw [(hold_s₁ b' hb' j hj_lt).1] at hq_j
              exact ⟨j, hj_lt, hq_j⟩
      · rw [Function.update_of_ne hbeq, hbc_other_s₁ b' hb' hbeq, hinv.hmap_dom b' hb' q]
        constructor <;> rintro ⟨j, hj_lt, hq_j⟩ <;> refine ⟨j, hj_lt, ?_⟩
        · rw [(hold_s₁ b' hb' j hj_lt).1]; exact hq_j
        · rw [← (hold_s₁ b' hb' j hj_lt).1]; exact hq_j

end Cslib.DataStructure.Dictionary.WordRAM.Succinct
