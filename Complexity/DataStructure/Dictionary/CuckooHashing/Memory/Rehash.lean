/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.CuckooHashing.Memory.Insert
import Complexity.Probability.PMF.Expect

/-!
# Cuckoo hashing over the memory oracle: rehashing

A rehash with `n` attempts left (`Layout.rehash`) draws two fresh hash tables with the memory
pilot `HashFamily.RandomTable.fill`, clears the tables and replays the keys (`Layout.attempt`,
`Layout.rebuildProg`). It marks the seed fresh if the replay settles and otherwise tries again.
With no attempts left it falls back (`Layout.fallbackProg`): it hashes each key to its position in
the first table, under which every insertion settles at once (`isSome_pureReplay_posMap`), and
marks the seed stale. Programs over memory are finite, so the loop of Pagh and Rodler cannot run
until success; the fallback keeps every operation correct.

The three facts the distributional hop needs are proved by induction on the attempts left:
* `Layout.rehash_spec`: the stored model after a rehash follows `Scheme.rehashLaw`, and every
  outcome satisfies the invariant. Two fills draw a uniform seed (`Layout.run_fills_bind`, from
  `HashFamily.RandomTable.run_fill` and `uniformOfFintype_prod`).
* `Layout.expectedCost_rehash_le`: when a uniform seed fails the keys with probability at most a
  half, a rehash costs at most `rehashCost` in expectation: `attemptCost` per attempt, a
  geometric number of attempts, and the fallback.
* `Layout.demonicValid_rehash`: every memory call is admissible.

## Main definitions

* `Memory.Layout.clearFrom`, `Memory.Layout.positions`, `Memory.Layout.fallbackProg`: clearing,
  position hashing and the fallback.
* `Memory.Layout.rebuildProg`, `Memory.Layout.attempt`, `Memory.Layout.rehash`: rebuilding,
  one random attempt, and the rehash.
* `Memory.Layout.fillState`: the memory holding a given seed.
* `Memory.memCharge`: memory charges with unit coins.
* `Memory.Layout.fallbackCost`, `Memory.Layout.rebuildCost`, `Memory.Layout.attemptCost`,
  `Memory.Layout.rehashCost`: memory costs.

## Main results

* `Memory.isSome_pureReplay_posMap`: the fallback seed replays any distinct keys.
* `Memory.Layout.wp_fallbackProg`, `Memory.Layout.wp_rebuildProg`: the deterministic parts.
* `Memory.Layout.run_fills_bind`, `Memory.Layout.run_attempt`: fresh hash tables are a uniform
  seed.
* `Memory.Layout.rehash_spec`, `Memory.Layout.expectedCost_rehash_le`,
  `Memory.Layout.demonicValid_rehash`: law, expected cost and admissibility of a rehash.

## References

* [R. Pagh and F. F. Rodler, "Cuckoo hashing"][PaghRodler2004]
-/

@[expose] public section

namespace Cslib.DataStructure.Dictionary.CuckooHashing.Memory

open Cslib.WordRAM Cslib.DataStructure
open Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing
open Cslib.DataStructure.HashFamily.RandomTable (fill writeFrom tableOf)
open scoped ENNReal

variable {U b : ℕ}

/-! ## The fallback seed -/

/-- **The fallback seed replays.** Under the seed that hashes each key to its position in the
first table, every insertion settles at once, provided the keys are distinct and fit the
table. -/
theorem isSome_pureReplay_posMap {ks : List (Fin U)} (hnd : ks.Nodup) (hlen : ks.length ≤ 2 ^ b)
    {maxLoop : ℕ} (hloop : 0 < maxLoop) :
    (pureReplay (fun u => Fin.ofNat (2 ^ b) (posMap ks u)) (fun _ => 0) maxLoop ks).isSome := by
  have key : ∀ i ≤ ks.length, ∃ T : PureTable U (2 ^ b),
      pureReplay (fun u => Fin.ofNat (2 ^ b) (posMap ks u)) (fun _ => 0) maxLoop (ks.take i) =
        some T ∧ ∀ j : Fin (2 ^ b), i ≤ j → T.t1 j = none := by
    intro i hi
    induction i with
    | zero => exact ⟨PureTable.empty U (2 ^ b), by simp, fun _ _ => rfl⟩
    | succ i ih =>
      obtain ⟨T, hT, hfree⟩ := ih (by omega)
      have hik : i < ks.length := by omega
      have hpos : (Fin.ofNat (2 ^ b) (posMap ks ks[i]) : Fin (2 ^ b)) = ⟨i, by omega⟩ := by
        ext
        simp only [posMap, List.getElem_mem, ite_true, Fin.val_ofNat,
          List.Nodup.idxOf_getElem hnd]
        exact Nat.mod_eq_of_lt (by omega)
      obtain ⟨fuel, rfl⟩ := Nat.exists_eq_add_of_lt hloop
      refine ⟨{ T with t1 := Function.update T.t1 ⟨i, by omega⟩ (some ⟨ks[i], i⟩) }, ?_, ?_⟩
      · rw [List.take_add_one, List.getElem?_eq_getElem hik, Option.toList_some,
          pureReplay_append_singleton, hT, List.length_take_of_le hik.le]
        simp only [pureEvict, pureEvictRound, WordRAM.CuckooHashing.putT1, hpos, Option.bind_some,
          hfree ⟨i, by omega⟩ le_rfl]
      · intro j hj
        have hne : j ≠ ⟨i, by omega⟩ := fun h => by rw [h] at hj; simp at hj
        simp only [Function.update_of_ne hne]
        exact hfree j (by omega)
  obtain ⟨T, hT, -⟩ := key ks.length le_rfl
  rw [List.take_length] at hT
  rw [hT]
  rfl

namespace Layout

variable {n_max : ℕ} (L : Layout U b n_max) {w : ℕ}

/-! ## Clearing and positions -/

/-- The two tables as one field. -/
def tables : Block := ⟨L.t1.base, 2 * 2 ^ b⟩

/-- The two hash tables as one field. -/
def hashes : Block := ⟨L.h1.base, 2 * U⟩

/-- Write `0` to entries `i, …, i + k - 1` of the field `blk`. -/
def clearFrom (blk : Block) : ℕ → ℕ → Memory.Prog Unit
  | _, 0 => pure ()
  | i, k + 1 => do
    blk.set i 0
    clearFrom blk (i + 1) k

omit L in
/-- Clearing entries writes `0` to them and costs one unit each. -/
theorem wp_clearFrom (blk : Block) :
    ∀ (k i : ℕ) {s : Memory.State}, blk.base + i + k ≤ s.frontier →
      (Memory.spec w).wp Memory.charge (Layout.clearFrom blk i k) (fun _ s' t =>
        (∀ a, s'.mem a = if blk.base + i ≤ a ∧ a < blk.base + i + k then 0 else s.mem a) ∧
        s'.frontier = s.frontier ∧ t = k) s
  | 0, i, s, _ => by
    simp only [clearFrom, StateTransitionSpec.wp_pure]
    exact ⟨fun a => by rw [ite_eq_right (by omega)], trivial, trivial⟩
  | k + 1, i, s, hk => by
    simp only [clearFrom, StateTransitionSpec.wp_lift_bind, StateTransitionSpec.stepFn,
      Memory.step_write, Memory.valid_write, Memory.charge_write]
    refine ⟨⟨by omega, fits_zero w⟩, ?_⟩
    refine StateTransitionSpec.wp_mono (fun _ s' t ⟨hm, hf, hc⟩ => ⟨fun a => ?_, hf, by omega⟩)
      (wp_clearFrom blk k (i + 1) (s := ⟨Function.update s.mem (blk.base + i) 0, s.frontier⟩)
        (by change blk.base + (i + 1) + k ≤ s.frontier; omega))
    rw [hm a]
    by_cases ha : a = blk.base + i
    · subst ha
      rw [ite_eq_right (by omega), ite_eq_left (by omega)]
      exact Function.update_self _ _ _
    · simp only [Function.update_of_ne ha]
      by_cases h₁ : blk.base + (i + 1) ≤ a ∧ a < blk.base + (i + 1) + k
      · rw [ite_eq_left h₁, ite_eq_left (by omega)]
      · rw [ite_eq_right h₁, ite_eq_right (by omega)]

/-- Write each key's position into the first hash table, for the keys with insertion indices
`i, …, i + r - 1`. -/
def positions : ℕ → ℕ → Memory.Prog Unit
  | _, 0 => pure ()
  | i, r + 1 => do
    let k ← L.keys.get i
    L.h1.set k i
    positions (i + 1) r

/-- Writing the positions of the keys with indices `i, …, i + r - 1`: the first hash cell of
each such key holds its insertion index, and nothing else changes. -/
theorem wp_positions {ks : List (Fin U)} (hnd : ks.Nodup) (hfit : Fits w (L.base + span U b n_max))
    (hlen : ks.length ≤ n_max) :
    ∀ (r i : ℕ) {s : Memory.State}, i + r ≤ ks.length → L.base + span U b n_max ≤ s.frontier →
      (∀ j (hj : j < ks.length), s.mem (L.keys.base + j) = ks[j]) →
      (Memory.spec w).wp Memory.charge (L.positions i r) (fun _ s' t =>
        (∀ u : Fin U, s'.mem (L.h1.base + u) =
          if u ∈ (ks.drop i).take r then ks.idxOf u else s.mem (L.h1.base + u)) ∧
        (∀ a, ¬ (L.h1.base ≤ a ∧ a < L.h1.base + U) → s'.mem a = s.mem a) ∧
        s'.frontier = s.frontier ∧ t = 2 * r) s
  | 0, i, s, _, _, _ => by
    simp only [positions, StateTransitionSpec.wp_pure, List.take_zero, List.not_mem_nil,
      ite_false]
    exact ⟨fun _ => trivial, fun _ _ => trivial, trivial, trivial⟩
  | r + 1, i, s, hr, hfront, hkeys => by
    have hi : i < ks.length := by omega
    have hk := ks[i].2
    have r₁ : L.keys.base + i < s.frontier := by simp only [keys_base, span] at hfront ⊢; omega
    have r₂ : L.h1.base + (ks[i] : ℕ) < s.frontier := by
      simp only [h1_base, span] at hfront ⊢; omega
    have fi : Fits w i := hfit.of_le (by simp only [span]; omega)
    simp only [positions, StateTransitionSpec.wp_lift_bind, StateTransitionSpec.stepFn,
      Memory.step_read, Memory.step_write, Memory.valid_read, Memory.valid_write,
      Memory.charge_read, Memory.charge_write, hkeys i hi]
    refine ⟨r₁, ⟨r₂, fi⟩, ?_⟩
    refine StateTransitionSpec.wp_mono (fun _ s' t ⟨hm, hfr, hf, hc⟩ => ⟨fun u => ?_,
      fun a ha => ?_, hf, by omega⟩)
      (wp_positions hnd hfit hlen r (i + 1)
        (s := ⟨Function.update s.mem (L.h1.base + ks[i]) i, s.frontier⟩)
        (by omega) hfront fun j hj => by
          change Function.update s.mem (L.h1.base + ks[i]) i (L.keys.base + j) = _
          rw [Function.update_of_ne (by simp only [h1_base, keys_base]; omega)]
          exact hkeys j hj)
    · have hsplit : (ks.drop i).take (r + 1) = ks[i] :: (ks.drop (i + 1)).take r := by
        rw [List.drop_eq_getElem_cons hi, List.take_succ_cons]
      rw [hm u]
      simp only [hsplit, List.mem_cons]
      by_cases hu : u ∈ (ks.drop (i + 1)).take r
      · rw [ite_eq_left hu, ite_eq_left (Or.inr hu)]
      · rw [ite_eq_right hu]
        change Function.update s.mem (L.h1.base + ks[i]) i (L.h1.base + u) = _
        by_cases hui : u = ks[i]
        · subst hui
          rw [Function.update_self, ite_eq_left (Or.inl rfl), List.Nodup.idxOf_getElem hnd]
        · rw [Function.update_of_ne (fun h => hui (Fin.ext (by omega))),
            ite_eq_right (by tauto)]
    · rw [hfr a ha]
      exact Function.update_of_ne (fun h => ha (by subst h; omega)) _ _

/-- The fallback: clear the hash tables, hash each key to its position in the first table,
clear the tables, replay the keys, and mark the seed stale. -/
def fallbackProg (maxLoop : ℕ) : Memory.Prog Unit := do
  clearFrom L.hashes 0 (2 * U)
  let n ← L.count.get 0
  L.positions 0 n
  clearFrom L.tables 0 (2 * 2 ^ b)
  let _ ← L.replay maxLoop 0 n
  L.fresh.set 0 0

variable (U b n_max) in
/-- The memory cost of the fallback. -/
def fallbackCost (maxLoop : ℕ) : ℕ :=
  2 * U + 2 * n_max + 2 * 2 ^ b + n_max * (1 + 8 * maxLoop) + 2

variable [NeZero U] {maxLoop : ℕ}

/-- The fallback seed of `scheme`, for the stored keys. -/
abbrev fallbackSeed (ks : List (Fin U)) : Seed U b :=
  (fun u => Fin.ofNat _ (posMap ks u), fun _ => 0)

/-- **The fallback.** From the records, the fallback stores the fallback seed of the keys,
restores the invariant with a stale seed, keeps the keys and values, and costs at most
`fallbackCost`. -/
theorem wp_fallbackProg {s : Memory.State} (h : L.Records s)
    (hfit : Fits w (L.base + span U b n_max)) (hcap : n_max ≤ 2 ^ b) (hloop : 0 < maxLoop) :
    (Memory.spec w).wp Memory.charge (L.fallbackProg maxLoop) (fun _ s' t =>
      L.Inv maxLoop s' ∧
      L.abs s' = ⟨fallbackSeed (L.keyList s), L.keyList s, (L.abs s).dict, false⟩ ∧
      s'.frontier = s.frontier ∧ t ≤ fallbackCost U b n_max maxLoop) s := by
  have hfront := h.allocated
  have hcnt := h.count_le
  set ks := L.keyList s with hks
  obtain ⟨n, hn⟩ : ∃ n, L.n s = n := ⟨_, rfl⟩
  rw [hn] at hcnt
  have hlen : ks.length = n := (length_keyList _ _).trans hn
  have hposlt : ∀ u, posMap ks u < 2 ^ b := fun u => by
    unfold posMap
    split_ifs with hu
    · have := List.idxOf_lt_length_of_mem hu
      omega
    · exact Nat.two_pow_pos b
  rw [fallbackProg, StateTransitionSpec.wp_bind]
  refine StateTransitionSpec.wp_mono (fun _ s₁ t₁ ⟨hm₁, hf₁, hc₁⟩ => ?_)
    (wp_clearFrom (w := w) L.hashes (2 * U) 0
      (by simp only [hashes, h1_base, span] at hfront ⊢; omega))
  -- the first clear changes only the hash tables
  have hout₁ : ∀ a, a < L.h1.base → s₁.mem a = s.mem a := fun a ha => by
    rw [hm₁ a, ite_eq_right (by simp only [hashes, h1_base] at ha ⊢; omega)]
  have hn₁ : s₁.mem (L.count.base + 0) = n :=
    (hout₁ _ (by simp only [count_base, h1_base]; omega)).trans hn
  have hkeys₁ : ∀ j (hj : j < ks.length), s₁.mem (L.keys.base + j) = ks[j] := fun j hj => by
    rw [hout₁ _ (by simp only [keys_base, h1_base]; omega)]
    exact h.keys_eq hj
  simp only [StateTransitionSpec.wp_lift_bind, StateTransitionSpec.stepFn, Memory.step_read,
    Memory.valid_read, Memory.charge_read, hn₁]
  refine ⟨by simp only [count_base, span] at hfront ⊢; rw [hf₁]; omega, ?_⟩
  rw [StateTransitionSpec.wp_bind]
  refine StateTransitionSpec.wp_mono (fun _ s₂ t₂ ⟨hm₂, hfr₂, hf₂, hc₂⟩ => ?_)
    (wp_positions L h.nodup hfit (hlen ▸ hcnt) n 0 (by simp only [length_keyList]; omega)
      (hf₁ ▸ hfront) hkeys₁)
  rw [StateTransitionSpec.wp_bind]
  refine StateTransitionSpec.wp_mono (fun _ s₃ t₃ ⟨hm₃, hf₃, hc₃⟩ => ?_)
    (wp_clearFrom (w := w) L.tables (2 * 2 ^ b) 0 (s := s₂)
      (by rw [hf₂, hf₁]; simp only [tables, t1_base, span] at hfront ⊢; omega))
  -- the memory before the replay
  have hout₃ : ∀ a, a < L.t1.base → s₃.mem a = s.mem a := fun a ha => by
    rw [hm₃ a, ite_eq_right (by simp only [tables, t1_base] at ha ⊢; omega),
      hfr₂ a (by simp only [t1_base, h1_base] at ha ⊢; omega), hout₁ a (by
        simp only [t1_base, h1_base] at ha ⊢; omega)]
  have hh1₃ : ∀ u : Fin U, s₃.mem (L.h1.base + u) = posMap ks u := fun u => by
    have hu := u.2
    have h₁ : s₁.mem (L.h1.base + u) = 0 := by
      rw [hm₁ _, ite_eq_left (by simp only [hashes, h1_base]; omega)]
    rw [hm₃ _, ite_eq_right (by simp only [tables, t1_base, h1_base]; omega), hm₂ u, h₁,
      List.drop_zero, List.take_of_length_le (by simp only [length_keyList]; omega)]
    rfl
  have hh2₃ : ∀ u : Fin U, s₃.mem (L.h2.base + u) = 0 := fun u => by
    have hu := u.2
    rw [hm₃ _, ite_eq_right (by simp only [tables, t1_base, h2_base]; omega),
      hfr₂ _ (by simp only [h1_base, h2_base]; omega), hm₁ _,
      ite_eq_left (by simp only [hashes, h1_base, h2_base]; omega)]
  have hW₃ : L.Walk w s₃ (fallbackSeed ks) ks (PureTable.empty U (2 ^ b)) :=
    { allocated := by rw [hf₃, hf₂, hf₁]; exact hfront
      fits := hfit
      length_le := hlen ▸ hcnt
      h1_eq := fun u => by
        rw [hh1₃ u, Fin.val_ofNat, Nat.mod_eq_of_lt (hposlt u)]
      h2_eq := fun u => by rw [hh2₃ u]; rfl
      keys_eq := fun j hj => by
        rw [hout₃ _ (by simp only [keys_base, t1_base]; omega)]
        exact h.keys_eq hj
      encodes := fun j => by
        have hj := j.2
        rw [hm₃ _, ite_eq_left (by simp only [tables, t1_base]; omega), hm₃ _,
          ite_eq_left (by simp only [tables, t1_base, t2_base]; omega)]
        exact ⟨rfl, rfl⟩
      consistent := consistent_empty ks }
  obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp
    (isSome_pureReplay_posMap (b := b) h.nodup (by simp only [length_keyList]; omega) hloop
      (maxLoop := maxLoop))
  rw [StateTransitionSpec.wp_bind]
  refine StateTransitionSpec.wp_mono (fun _ s₄ t₄ ⟨_, hW₄, hfr₄, hf₄, hc₄⟩ => ?_)
    (wp_replay (L := L) (w := w) n 0 (by omega) hW₃ (by simp))
  rw [Nat.zero_add, ← hlen, List.take_length] at hW₄
  have hW₅ := hW₄ T hT
  have r₅ : L.fresh.base + 0 < s₄.frontier := by
    rw [hf₄, hf₃, hf₂, hf₁]; simp only [fresh_base, span] at hfront ⊢; omega
  simp only [StateTransitionSpec.wp_lift, StateTransitionSpec.stepFn, Memory.step_write,
    Memory.valid_write, Memory.charge_write]
  refine ⟨⟨r₅, fits_zero w⟩, ?_⟩
  -- the final memory
  set s₅ : Memory.State := ⟨Function.update s₄.mem (L.fresh.base + 0) 0, s₄.frontier⟩ with hs₅
  have hfr₅ : ∀ a, a ≠ L.base + 1 → ¬ L.InTables a → s₅.mem a = s₃.mem a := fun a ha ht => by
    rw [hs₅]
    simp only [fresh_base, Nat.add_zero]
    rw [Function.update_of_ne ha, hfr₄ a ht]
  have hn₅ : L.n s₅ = L.n s := by
    rw [Layout.n, hfr₅ _ (by omega) (by simp only [InTables, t1_base]; omega),
      hout₃ _ (by simp only [t1_base]; omega)]
    rfl
  have hk₅ : ∀ i < L.n s, s₅.mem (L.keys.base + i) = s.mem (L.keys.base + i) := fun i hi => by
    rw [hfr₅ _ (by simp only [keys_base]; omega)
      (by simp only [InTables, t1_base, keys_base]; omega),
      hout₃ _ (by simp only [keys_base, t1_base]; omega)]
  have hv₅ : ∀ i < L.n s, s₅.mem (L.vals.base + i) = s.mem (L.vals.base + i) := fun i hi => by
    rw [hfr₅ _ (by simp only [vals_base]; omega)
      (by simp only [InTables, t1_base, vals_base]; omega),
      hout₃ _ (by simp only [vals_base, t1_base]; omega)]
  have hks₅ : L.keyList s₅ = ks := keyList_congr hn₅ hk₅
  have hh1₅ : ∀ u : Fin U, s₅.mem (L.h1.base + u) = posMap ks u := fun u => by
    have hu := u.2
    rw [hfr₅ _ (by simp only [h1_base]; omega)
      (by simp only [InTables, t1_base, h1_base]; omega), hh1₃ u]
  have hh2₅ : ∀ u : Fin U, s₅.mem (L.h2.base + u) = 0 := fun u => by
    have hu := u.2
    rw [hfr₅ _ (by simp only [h2_base]; omega)
      (by simp only [InTables, t1_base, h2_base]; omega), hh2₃ u]
  have hseed₅ : L.seed s₅ = fallbackSeed ks := by
    simp only [seed]
    congr 1 <;> funext u <;> unfold HashFamily.RandomTable.tableOf
    · rw [hh1₅ u]
    · rw [hh2₅ u]
      rfl
  have hR₅ : L.Records s₅ :=
    { allocated := by simp only [hs₅]; rw [hf₄, hf₃, hf₂, hf₁]; exact hfront
      count_le := by omega
      keys_lt := fun i hi => by
        rw [hn₅] at hi
        rw [hk₅ i hi]
        exact h.keys_lt i hi
      nodup := hks₅ ▸ h.nodup
      h1_lt := fun u hu => by
        have := hh1₅ ⟨u, hu⟩
        simp only at this
        rw [this]
        exact hposlt _
      h2_lt := fun u hu => by
        have := hh2₅ ⟨u, hu⟩
        simp only at this
        rw [this]
        exact Nat.two_pow_pos b }
  have hfresh₅ : s₅.mem (L.base + 1) = 0 := Function.update_self _ _ _
  refine ⟨⟨hR₅, T, by rw [hseed₅, hks₅]; exact hT, fun j => ?_⟩, ?_, ?_, ?_⟩
  · have hj := j.2
    simp only [hs₅, fresh_base, Nat.add_zero]
    rw [Function.update_of_ne (by simp only [t1_base]; omega),
      Function.update_of_ne (by simp only [t2_base]; omega)]
    exact hW₅.encodes j
  · simp only [abs, hseed₅, hks₅, valList_congr hn₅ hv₅, hfresh₅, ne_eq,
      not_true_eq_false, decide_false]
    rfl
  · show s₄.frontier = s.frontier
    rw [hf₄, hf₃, hf₂, hf₁]
  · have := Nat.mul_le_mul_right (1 + 8 * maxLoop) hcnt
    simp only [fallbackCost]
    omega

/-- Rebuild the tables under the stored seed: clear them and replay the keys. It answers whether
every walk settled. -/
def rebuildProg (maxLoop : ℕ) : Memory.Prog Bool := do
  let n ← L.count.get 0
  clearFrom L.tables 0 (2 * 2 ^ b)
  L.replay maxLoop 0 n

variable (b n_max) in
/-- The memory cost of a rebuild. -/
def rebuildCost (loop : ℕ) : ℕ := 1 + 2 * 2 ^ b + n_max * (1 + 8 * loop)

/-- **A rebuild replays the keys.** From the records, a rebuild answers whether the keys replay
under the stored seed, changes only the tables, restores the invariant if they do, and costs at
most `rebuildCost`. -/
theorem wp_rebuildProg {s : Memory.State} (h : L.Records s)
    (hfit : Fits w (L.base + span U b n_max)) :
    (Memory.spec w).wp Memory.charge (L.rebuildProg maxLoop) (fun ok s' t =>
      ok = (pureReplay (L.seed s).1 (L.seed s).2 maxLoop (L.keyList s)).isSome ∧
      (∀ a, ¬ L.InTables a → s'.mem a = s.mem a) ∧ (ok = true → L.Inv maxLoop s') ∧
      s'.frontier = s.frontier ∧ t ≤ rebuildCost b n_max maxLoop) s := by
  have hfront := h.allocated
  have hcnt := h.count_le
  have hlen : (L.keyList s).length = L.n s := length_keyList _ _
  rw [rebuildProg]
  simp only [StateTransitionSpec.wp_lift_bind, StateTransitionSpec.stepFn, Memory.step_read,
    Memory.valid_read, Memory.charge_read, count_base, Nat.add_zero]
  refine ⟨by simp only [span] at hfront; omega, ?_⟩
  rw [StateTransitionSpec.wp_bind]
  refine StateTransitionSpec.wp_mono (fun _ s₁ t₁ ⟨hm₁, hf₁, hc₁⟩ => ?_)
    (wp_clearFrom (w := w) L.tables (2 * 2 ^ b) 0 (s := s)
      (by simp only [tables, t1_base, span] at hfront ⊢; omega))
  have hfr₁ : ∀ a, ¬ L.InTables a → s₁.mem a = s.mem a := fun a ha => by
    rw [hm₁ a, ite_eq_right (by simp only [tables, InTables, Nat.add_zero] at ha ⊢; omega)]
  have hW₁ : L.Walk w s₁ (L.seed s) (L.keyList s) (PureTable.empty U (2 ^ b)) :=
    { allocated := hf₁ ▸ hfront
      fits := hfit
      length_le := hlen ▸ hcnt
      h1_eq := fun u => by
        have hu := u.2
        rw [hfr₁ _ (by simp only [InTables, t1_base, h1_base]; omega)]
        exact h.h1_eq u
      h2_eq := fun u => by
        have hu := u.2
        rw [hfr₁ _ (by simp only [InTables, t1_base, h2_base]; omega)]
        exact h.h2_eq u
      keys_eq := fun j hj => by
        rw [hfr₁ _ (by simp only [InTables, t1_base, keys_base]; omega)]
        exact h.keys_eq hj
      encodes := fun j => by
        have hj := j.2
        rw [hm₁ _, ite_eq_left (by simp only [tables, t1_base]; omega), hm₁ _,
          ite_eq_left (by simp only [tables, t1_base, t2_base]; omega)]
        exact ⟨rfl, rfl⟩
      consistent := consistent_empty _ }
  refine StateTransitionSpec.wp_mono (fun ok s₂ t₂ ⟨hok, hW₂, hfr₂, hf₂, hc₂⟩ => ?_)
    (wp_replay (L := L) (w := w) (L.n s) 0 (by omega) hW₁ (by simp))
  rw [Nat.zero_add, ← hlen, List.take_length] at hok hW₂
  have hfr : ∀ a, ¬ L.InTables a → s₂.mem a = s.mem a := fun a ha =>
    (hfr₂ a ha).trans (hfr₁ a ha)
  refine ⟨hok, hfr, fun htrue => ?_, hf₂.trans hf₁, ?_⟩
  · obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp (hok ▸ htrue)
    have hk := SameKeys.of_frame hcnt hfr
    exact ⟨h.congr hk (by rw [hf₂, hf₁]), T, by rw [hk.seed_eq, hk.keyList_eq]; exact hT,
      (hW₂ T hT).encodes⟩
  · have := Nat.mul_le_mul_right (1 + 8 * maxLoop) hcnt
    simp only [rebuildCost]
    omega

/-! ## Fresh hash tables -/

omit [NeZero U] in
/-- The memory after writing the seed `θ` into the two hash tables. -/
def fillState (s : Memory.State) (θ : Seed U b) : Memory.State :=
  writeFrom L.h2 b 0 U θ.2 (writeFrom L.h1 b 0 U θ.1 s)

omit [NeZero U] in
/-- Writing the hash tables changes no cell below them. -/
theorem fillState_mem_of_lt (s : Memory.State) (θ : Seed U b) {a : ℕ} (ha : a < L.h1.base) :
    (L.fillState s θ).mem a = s.mem a := by
  rw [fillState, HashFamily.RandomTable.mem_writeFrom_of_lt _ _ _ _
      (by simp only [h1_base, h2_base] at ha ⊢; omega),
    HashFamily.RandomTable.mem_writeFrom_of_lt _ _ _ _ (by omega)]

omit [NeZero U] in
@[simp] theorem frontier_fillState (s : Memory.State) (θ : Seed U b) :
    (L.fillState s θ).frontier = s.frontier := by
  simp [fillState]

omit [NeZero U] in
theorem fillState_h1 (s : Memory.State) (θ : Seed U b) (u : Fin U) :
    (L.fillState s θ).mem (L.h1.base + u) = θ.1 u := by
  have hu := u.2
  rw [fillState, HashFamily.RandomTable.mem_writeFrom_of_lt _ _ _ _
      (by simp only [h1_base, h2_base]; omega)]
  have := HashFamily.RandomTable.mem_writeFrom (table := L.h1) 0 U θ.1 s u
  rwa [Nat.zero_add] at this

omit [NeZero U] in
theorem fillState_h2 (s : Memory.State) (θ : Seed U b) (u : Fin U) :
    (L.fillState s θ).mem (L.h2.base + u) = θ.2 u := by
  have := HashFamily.RandomTable.mem_writeFrom (table := L.h2) 0 U θ.2
    (writeFrom L.h1 b 0 U θ.1 s) u
  rwa [Nat.zero_add] at this

omit [NeZero U] in
/-- The hash tables hold the written seed. -/
theorem seed_fillState (s : Memory.State) (θ : Seed U b) : L.seed (L.fillState s θ) = θ := by
  simp only [seed]
  congr 1 <;> funext u <;> unfold tableOf
  · rw [fillState_h1]
    exact Fin.ofNat_val_eq_self _
  · rw [fillState_h2]
    exact Fin.ofNat_val_eq_self _

variable {L} in
/-- Fresh hash tables keep the records. -/
theorem Records.fillState {s : Memory.State} (h : L.Records s) (θ : Seed U b) :
    L.Records (L.fillState s θ) := by
  have hcnt := h.count_le
  have hn : L.n (L.fillState s θ) = L.n s :=
    L.fillState_mem_of_lt s θ (by simp only [h1_base]; omega)
  have hk : ∀ i < L.n s, (L.fillState s θ).mem (L.keys.base + i) = s.mem (L.keys.base + i) :=
    fun i hi => L.fillState_mem_of_lt s θ (by simp only [keys_base, h1_base]; omega)
  exact
    { allocated := by rw [frontier_fillState]; exact h.allocated
      count_le := hn ▸ hcnt
      keys_lt := fun i hi => by
        rw [hn] at hi
        rw [hk i hi]
        exact h.keys_lt i hi
      nodup := (keyList_congr hn hk) ▸ h.nodup
      h1_lt := fun u hu => by
        have := L.fillState_h1 s θ ⟨u, hu⟩
        simp only at this
        rw [this]
        exact (θ.1 _).2
      h2_lt := fun u hu => by
        have := L.fillState_h2 s θ ⟨u, hu⟩
        simp only at this
        rw [this]
        exact (θ.2 _).2 }

/-- Fresh hash tables change the stored model only in its seed. -/
theorem abs_fillState {s : Memory.State} (h : L.Records s) (θ : Seed U b) :
    L.abs (L.fillState s θ) = { L.abs s with seed := θ } := by
  have hcnt := h.count_le
  have hn : L.n (L.fillState s θ) = L.n s :=
    L.fillState_mem_of_lt s θ (by simp only [h1_base]; omega)
  have hk := keyList_congr hn fun i hi =>
    L.fillState_mem_of_lt s θ (by simp only [keys_base, h1_base]; omega)
  have hv := valList_congr hn fun i hi =>
    L.fillState_mem_of_lt s θ (by simp only [vals_base, h1_base]; omega)
  have hf : (L.fillState s θ).mem (L.base + 1) = s.mem (L.base + 1) :=
    L.fillState_mem_of_lt s θ (by simp only [h1_base]; omega)
  simp only [abs, seed_fillState, hk, hv, hf]

omit [NeZero U] in
/-- A program after a fill runs from the filled memory, for a uniform table. -/
theorem run_fill_bind {α : Type} (blk : Block) (k : Unit → ProbOracleComp Memory.Op.Result α)
    (s : Memory.State) :
    (Memory.spec w).toRandomized.withCoins.run (fill blk b 0 U >>= k) s =
      (Probability.PMF.uniformOfFintype (Fin U → Fin (2 ^ b))).bind fun θ =>
        (Memory.spec w).toRandomized.withCoins.run (k ()) (writeFrom blk b 0 U θ s) := by
  rw [RandomizedSpec.run_bind]
  have h := HashFamily.RandomTable.run_fill (w := w) (table := blk) (b := b) 0 U s
  calc _ = ((Memory.spec w).toRandomized.withCoins.run (fill blk b 0 U) s).bind
        (fun x => (Memory.spec w).toRandomized.withCoins.run (k ()) x.2) := rfl
    _ = (((Memory.spec w).toRandomized.withCoins.run (fill blk b 0 U) s).map Prod.snd).bind
        (fun s' => (Memory.spec w).toRandomized.withCoins.run (k ()) s') := by
          rw [PMF.bind_map]
          rfl
    _ = _ := by rw [h, PMF.bind_map]; rfl

omit [NeZero U] in
/-- **Two fills draw a uniform seed.** A program after filling both hash tables runs from the
memory holding a uniform seed. -/
theorem run_fills_bind {α : Type} (k : ProbOracleComp Memory.Op.Result α) (s : Memory.State) :
    (Memory.spec w).toRandomized.withCoins.run
      (fill L.h1 b 0 U >>= fun _ => fill L.h2 b 0 U >>= fun _ => k) s =
      (Probability.PMF.uniformOfFintype (Seed U b)).bind fun θ =>
        (Memory.spec w).toRandomized.withCoins.run k (L.fillState s θ) := by
  rw [run_fill_bind, ← Probability.PMF.uniformOfFintype_prod, PMF.bind_bind]
  refine congrArg _ (funext fun θ₁ => ?_)
  rw [run_fill_bind, PMF.bind_map]
  rfl

/-! ## Rehashing -/

/-- One rehash attempt: fresh hash tables, then a rebuild. It answers whether the rebuild
settled. -/
noncomputable def attempt (maxLoop : ℕ) : ProbOracleComp Memory.Op.Result Bool :=
  fill L.h1 b 0 U >>= fun _ => fill L.h2 b 0 U >>= fun _ =>
    OracleComp.liftRight (L.rebuildProg maxLoop)

/-- A rehash with `n` random attempts left: try an attempt and mark the seed fresh if it
settles; with no attempts left, fall back. -/
noncomputable def rehash (maxLoop : ℕ) : ℕ → ProbOracleComp Memory.Op.Result Unit
  | 0 => OracleComp.liftRight (L.fallbackProg maxLoop)
  | n + 1 => L.attempt maxLoop >>= fun ok =>
      if ok then OracleComp.liftRight (L.fresh.set 0 1) else rehash maxLoop n

omit [NeZero U] in
/-- A deterministic program runs to its evaluation. -/
theorem run_liftRight {α : Type} (p : Memory.Prog α) (s : Memory.State) :
    (Memory.spec w).toRandomized.withCoins.run (OracleComp.liftRight p) s =
      PMF.pure ((Memory.spec w).clientResult s p, (Memory.spec w).clientState s p) := by
  rw [RandomizedSpec.withCoins_run_liftRight, StateTransitionSpec.run_toRandomized]
  rfl

omit [NeZero U] in
/-- An attempt draws a uniform seed and rebuilds under it. -/
theorem run_attempt (s : Memory.State) :
    (Memory.spec w).toRandomized.withCoins.run (L.attempt maxLoop) s =
      (Probability.PMF.uniformOfFintype (Seed U b)).bind fun θ =>
        PMF.pure ((Memory.spec w).clientResult (L.fillState s θ) (L.rebuildProg maxLoop),
          (Memory.spec w).clientState (L.fillState s θ) (L.rebuildProg maxLoop)) := by
  rw [attempt, run_fills_bind]
  exact congrArg _ (funext fun θ => run_liftRight _ _)

variable {L} in
/-- Writing the freshness flag keeps the invariant and sets the stored flag. -/
theorem Inv.setFresh {s : Memory.State} (h : L.Inv maxLoop s) (v : ℕ) :
    L.Inv maxLoop ⟨Function.update s.mem (L.fresh.base + 0) v, s.frontier⟩ ∧
      L.abs ⟨Function.update s.mem (L.fresh.base + 0) v, s.frontier⟩ =
        { L.abs s with fresh := decide (v ≠ 0) } := by
  have hcnt := h.count_le
  set s' : Memory.State := ⟨Function.update s.mem (L.fresh.base + 0) v, s.frontier⟩
  have hother : ∀ a, a ≠ L.base + 1 → s'.mem a = s.mem a := fun a ha =>
    Function.update_of_ne (by simpa only [fresh_base, Nat.add_zero] using ha) _ _
  have hk : L.SameKeys s s' :=
    { n_eq := hother _ (by omega)
      keys_eq := fun i _ => hother _ (by simp only [keys_base]; omega)
      h1_eq := fun u _ => hother _ (by simp only [h1_base]; omega)
      h2_eq := fun u _ => hother _ (by simp only [h2_base]; omega) }
  obtain ⟨T, hT, hE⟩ := h.tables
  refine ⟨⟨h.congr hk le_rfl, T, by rw [hk.seed_eq, hk.keyList_eq]; exact hT, fun j => ?_⟩, ?_⟩
  · have hj := j.2
    rw [hother _ (by simp only [t1_base]; omega), hother _ (by simp only [t2_base]; omega)]
    exact hE j
  · have hv := valList_congr hk.n_eq fun i hi => hother _ (by simp only [vals_base]; omega)
    have hf : s'.mem (L.base + 1) = v := Function.update_self _ _ _
    simp only [abs, hk.seed_eq, hk.keyList_eq, hv, hf]

/-- **The law of a rehash.** From the records, a rehash with `n` attempts left stores the keys and
the dictionary under a seed and freshness drawn from `rehashLaw`, and every outcome satisfies the
invariant. -/
theorem rehash_spec (hfit : Fits w (L.base + span U b n_max)) (hcap : n_max ≤ 2 ^ b)
    (hloop : 0 < maxLoop) (attempts : ℕ) :
    ∀ n {s : Memory.State}, L.Records s →
      ((Memory.spec w).toRandomized.withCoins.run (L.rehash maxLoop n) s).map
          (fun x => L.abs x.2) =
        ((scheme U b maxLoop attempts).rehashLaw (L.keyList s) n).map
          (Scheme.rehashed (Seed U b) (L.keyList s) (L.abs s).dict) ∧
      ∀ x ∈ ((Memory.spec w).toRandomized.withCoins.run (L.rehash maxLoop n) s).support,
        L.Inv maxLoop x.2 ∧ x.2.frontier = s.frontier
  | 0, s, h => by
    obtain ⟨_, s', _, ⟨hI, habs, hf, -⟩, hrun, -, -⟩ :=
      exists_run_liftRight_of_wp (fun _ => 1) (L.wp_fallbackProg h hfit hcap hloop)
    simp only [rehash, hrun, PMF.pure_map, Scheme.rehashLaw]
    refine ⟨by rw [habs]; rfl, fun x hx => ?_⟩
    rw [PMF.mem_support_pure_iff] at hx
    subst hx
    exact ⟨hI, hf⟩
  | n + 1, s, h => by
    have hcnt := h.count_le
    set ks := L.keyList s with hks
    set d := (L.abs s).dict with hd
    -- the memory after fresh hash tables, and after the rebuild
    have hkl (θ : Seed U b) : L.keyList (L.fillState s θ) = ks :=
      keyList_congr (L.fillState_mem_of_lt s θ (by simp only [h1_base]; omega))
        fun i hi => L.fillState_mem_of_lt s θ (by simp only [keys_base, h1_base]; omega)
    have hR (θ : Seed U b) := h.fillState θ
    have hreb (θ : Seed U b) := (StateTransitionSpec.wp_iff _ _ _).mp
      (L.wp_rebuildProg (maxLoop := maxLoop) (hR θ) hfit)
    set r := fun θ => (Memory.spec w).clientResult (L.fillState s θ) (L.rebuildProg maxLoop)
      with hr_def
    set s' := fun θ => (Memory.spec w).clientState (L.fillState s θ) (L.rebuildProg maxLoop)
      with hs'_def
    have hr (θ : Seed U b) : r θ = (pureReplay θ.1 θ.2 maxLoop ks).isSome := by
      have h₁ := (hreb θ).2.1
      rwa [seed_fillState, hkl] at h₁
    have hG (θ : Seed U b) : (scheme U b maxLoop attempts).Good θ ks ↔ r θ = true := by
      rw [hr θ]
      rfl
    have hk' (θ : Seed U b) : L.SameKeys (L.fillState s θ) (s' θ) :=
      SameKeys.of_frame (hR θ).count_le (hreb θ).2.2.1
    have hR' (θ : Seed U b) : L.Records (s' θ) := (hR θ).congr (hk' θ) (hreb θ).2.2.2.2.1.ge
    have habs' (θ : Seed U b) : L.abs (s' θ) = { L.abs s with seed := θ } := by
      rw [abs_congr (hR θ).count_le (hreb θ).2.2.1, abs_fillState L h θ]
    have hks' (θ : Seed U b) : L.keyList (s' θ) = ks := by
      have := congrArg Model.keys (habs' θ)
      simpa using this
    have hd' (θ : Seed U b) : (L.abs (s' θ)).dict = d := by rw [habs' θ]
    have hf' (θ : Seed U b) : (s' θ).frontier = s.frontier := by
      rw [(hreb θ).2.2.2.2.1, frontier_fillState]
    -- the run of the rehash
    have hrun : (Memory.spec w).toRandomized.withCoins.run (L.rehash maxLoop (n + 1)) s =
        (Probability.PMF.uniformOfFintype (Seed U b)).bind fun θ =>
          (Memory.spec w).toRandomized.withCoins.run
            (if r θ then OracleComp.liftRight (L.fresh.set 0 1) else L.rehash maxLoop n)
            (s' θ) := by
      rw [rehash, RandomizedSpec.run_bind, run_attempt, PMF.bind_bind]
      simp only [PMF.pure_bind]
      rfl
    have hfresh (θ : Seed U b) (hg : r θ = true) :
        (Memory.spec w).toRandomized.withCoins.run (OracleComp.liftRight (L.fresh.set 0 1))
          (s' θ) = PMF.pure ((), ⟨Function.update (s' θ).mem (L.fresh.base + 0) 1,
            (s' θ).frontier⟩) := run_liftRight _ _
    refine ⟨?_, fun x hx => ?_⟩
    · rw [hrun, PMF.map_bind, Scheme.rehashLaw, PMF.map_bind]
      refine congrArg _ (funext fun θ => ?_)
      by_cases hg : r θ = true
      · have hI := (hreb θ).2.2.2.1 hg
        rw [ite_eq_left hg, hfresh θ hg, PMF.pure_map, (hI.setFresh 1).2,
          ite_eq_left ((hG θ).mpr hg),
          PMF.pure_map, habs' θ]
        rfl
      · rw [ite_eq_right hg, ite_eq_right (mt (hG θ).mp hg),
          (rehash_spec hfit hcap hloop attempts n (hR' θ)).1, hks', hd']
    · rw [hrun, PMF.mem_support_bind_iff] at hx
      obtain ⟨θ, -, hx⟩ := hx
      by_cases hg : r θ = true
      · have hI := (hreb θ).2.2.2.1 hg
        rw [ite_eq_left hg, hfresh θ hg, PMF.mem_support_pure_iff] at hx
        subst hx
        exact ⟨(hI.setFresh 1).1, hf' θ⟩
      · rw [ite_eq_right hg] at hx
        obtain ⟨hI, hfx⟩ := (rehash_spec hfit hcap hloop attempts n (hR' θ)).2 x hx
        exact ⟨hI, hfx.trans (hf' θ)⟩

/-- The outcome of the rebuild after fresh hash tables holding `θ`: it answers whether the keys
replay under `θ`, keeps the records, the keys and the dictionary, restores the invariant if it
settles, and costs at most `rebuildCost`. -/
theorem attempt_outcome (hfit : Fits w (L.base + span U b n_max)) {s : Memory.State}
    (h : L.Records s) (θ : Seed U b) :
    (Memory.spec w).clientResult (L.fillState s θ) (L.rebuildProg maxLoop) =
        (pureReplay θ.1 θ.2 maxLoop (L.keyList s)).isSome ∧
      L.Records ((Memory.spec w).clientState (L.fillState s θ) (L.rebuildProg maxLoop)) ∧
      L.abs ((Memory.spec w).clientState (L.fillState s θ) (L.rebuildProg maxLoop)) =
        { L.abs s with seed := θ } ∧
      ((Memory.spec w).clientResult (L.fillState s θ) (L.rebuildProg maxLoop) = true →
        L.Inv maxLoop ((Memory.spec w).clientState (L.fillState s θ) (L.rebuildProg maxLoop))) ∧
      ((Memory.spec w).clientState (L.fillState s θ) (L.rebuildProg maxLoop)).frontier =
        s.frontier ∧
      (Memory.spec w).wp Memory.charge (L.rebuildProg maxLoop)
        (fun _ _ t => t ≤ rebuildCost b n_max maxLoop) (L.fillState s θ) := by
  have hcnt := h.count_le
  have hR := h.fillState θ
  have hwp := L.wp_rebuildProg (maxLoop := maxLoop) hR hfit
  have hreb := (StateTransitionSpec.wp_iff _ _ _).mp hwp
  have hkl : L.keyList (L.fillState s θ) = L.keyList s :=
    keyList_congr (L.fillState_mem_of_lt s θ (by simp only [h1_base]; omega))
      fun i hi => L.fillState_mem_of_lt s θ (by simp only [keys_base, h1_base]; omega)
  have hk' := SameKeys.of_frame hR.count_le hreb.2.2.1
  refine ⟨by rw [hreb.2.1, seed_fillState, hkl], hR.congr hk' hreb.2.2.2.2.1.ge, ?_,
    hreb.2.2.2.1, by rw [hreb.2.2.2.2.1, frontier_fillState],
    StateTransitionSpec.wp_mono (fun _ _ _ h => h.2.2.2.2) hwp⟩
  rw [abs_congr hR.count_le hreb.2.2.1, abs_fillState L h θ]

/-! ## Expected costs -/

end Layout

/-- Memory charges with coins: one unit per coin, and `Memory.charge` per memory operation. -/
noncomputable abbrev memCharge (w : ℕ) : (Memory.spec w).toRandomized.withCoins.State →
    (Memory.spec w).toRandomized.withCoins.Op → ℕ :=
  (Memory.spec w).toRandomized.coinCharge (fun _ => 1) Memory.charge

/-- The same charges as a cost on calls. -/
def opCost : ℕ ⊕ Memory.Op → ℕ := Sum.elim (fun _ => 1) (Memory.charge ⟨fun _ => 0, 0⟩)

theorem memCharge_eq (w : ℕ) : memCharge w = fun _ o => opCost o := by
  funext s o
  rcases o with n | o
  · rfl
  · cases o <;> rfl

/-- A fill of `n` cells makes `2 * n` unit calls. -/
theorem isCostBounded_fill (blk : Block) (i n : ℕ) :
    OracleComp.IsCostBounded opCost (fill blk b i n) (2 * n) := by
  induction n generalizing i with
  | zero => exact .pure _ _
  | succ n ih =>
    have hsample : OracleComp.IsCostBounded opCost
        (ProbOracleComp.sample (spec := Memory.Op.Result) (ProbComp.uniform (Fin (2 ^ b)))) 1 := by
      rw [ProbComp.uniform, ProbOracleComp.sample_map]
      exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query _)
    have hwrite (x : ℕ) : OracleComp.IsCostBounded opCost
        (OracleComp.liftRight (spec₁ := unifSpec) (blk.set i x)) 1 :=
      OracleComp.IsCostBounded.query (spec := probOracleSpec Memory.Op.Result) _
    have h := hsample.bind fun x => (hwrite x.val).bind fun _ => ih (i + 1)
    exact h.mono (by omega)

/-- A fill of the `U` cells of a field costs `2 * U` in expectation. -/
theorem expectedCost_fill_le {w : ℕ} (blk : Block) (s : Memory.State) :
    (Memory.spec w).toRandomized.withCoins.expectedCost (memCharge w) (fill blk b 0 U) s ≤
      (2 * U : ℕ) := by
  rw [memCharge_eq]
  exact (Memory.spec w).toRandomized.withCoins.expectedCost_le_of_isCostBounded
    (isCostBounded_fill blk 0 U) s

/-- Every outcome of a fill writes a table into the field. -/
theorem exists_eq_writeFrom_of_mem_support {w : ℕ} {blk : Block} {s : Memory.State}
    {x : Unit × Memory.State}
    (hx : x ∈ ((Memory.spec w).toRandomized.withCoins.run (fill blk b 0 U) s).support) :
    ∃ θ, x.2 = writeFrom blk b 0 U θ s := by
  have h : x.2 ∈ (((Memory.spec w).toRandomized.withCoins.run (fill blk b 0 U) s).map
      Prod.snd).support := (PMF.mem_support_map_iff _ _ _).mpr ⟨x, hx, rfl⟩
  rw [HashFamily.RandomTable.run_fill] at h
  obtain ⟨θ, -, hθ⟩ := (PMF.mem_support_map_iff _ _ _).mp h
  exact ⟨θ, hθ.symm⟩

namespace Layout

variable {n_max : ℕ} (L : Layout U b n_max) {w : ℕ} [NeZero U] {maxLoop : ℕ}

variable (U b n_max) in
/-- The memory cost of an attempt: two fills and a rebuild. -/
def attemptCost (loop : ℕ) : ℕ := 4 * U + rebuildCost b n_max loop

variable (U b n_max) in
/-- The expected memory cost of a rehash, when every attempt fails with probability at most a
half. -/
def rehashCost (loop : ℕ) : ℕ :=
  2 * (attemptCost U b n_max loop + 1) + fallbackCost U b n_max loop

/-- An attempt costs at most `attemptCost` in expectation. -/
theorem expectedCost_attempt_le (hfit : Fits w (L.base + span U b n_max)) {s : Memory.State}
    (h : L.Records s) :
    (Memory.spec w).toRandomized.withCoins.expectedCost (memCharge w) (L.attempt maxLoop) s ≤
      (attemptCost U b n_max maxLoop : ℕ) := by
  rw [attempt, attemptCost, show 4 * U = 2 * U + 2 * U by ring, Nat.cast_add, Nat.cast_add,
    add_assoc]
  refine RandomizedSpec.expectedCost_bind_le _ (expectedCost_fill_le _ _) fun x hx => ?_
  obtain ⟨θ₁, hx₂⟩ := exists_eq_writeFrom_of_mem_support hx
  refine RandomizedSpec.expectedCost_bind_le _ (expectedCost_fill_le _ _) fun y hy => ?_
  obtain ⟨θ₂, hy₂⟩ := exists_eq_writeFrom_of_mem_support hy
  have hst : y.2 = L.fillState s (θ₁, θ₂) := by rw [hy₂, hx₂]; rfl
  obtain ⟨-, -, t, ht, -, hcost, -⟩ := exists_run_liftRight_of_wp (fun _ => 1)
    (L.attempt_outcome (maxLoop := maxLoop) hfit h (θ₁, θ₂)).2.2.2.2.2
  rw [hst, hcost]
  exact_mod_cast ht

omit [NeZero U] in
/-- Marking the seed fresh is one admissible write. -/
theorem wp_setFresh (hfit : Fits w (L.base + span U b n_max)) {s : Memory.State}
    (hs : L.base + span U b n_max ≤ s.frontier) (v : ℕ) (hv : v ≤ 1) :
    (Memory.spec w).wp Memory.charge (L.fresh.set 0 v) (fun _ _ t => t = 1) s := by
  simp only [StateTransitionSpec.wp_lift, Memory.valid_write, Memory.charge_write]
  exact ⟨⟨by simp only [fresh_base, span] at hs ⊢; omega,
    hfit.of_le (by simp only [span]; omega)⟩, trivial⟩

/-- **The expected cost of a rehash.** When a uniform seed fails the keys with probability at
most a half, a rehash costs at most `rehashCost` in expectation, whatever the attempts left. -/
theorem expectedCost_rehash_le (hfit : Fits w (L.base + span U b n_max)) (hcap : n_max ≤ 2 ^ b)
    (hloop : 0 < maxLoop) (attempts : ℕ) {ks : List (Fin U)}
    (hhalf : (Probability.PMF.uniformOfFintype (Seed U b)).toOuterMeasure
      {θ | ¬ (scheme U b maxLoop attempts).Good θ ks} ≤ 2⁻¹) :
    ∀ n {s : Memory.State}, L.Records s → L.keyList s = ks →
      (Memory.spec w).toRandomized.withCoins.expectedCost (memCharge w) (L.rehash maxLoop n) s ≤
        (rehashCost U b n_max maxLoop : ℕ)
  | 0, s, h, _ => by
    obtain ⟨_, _, t, ⟨-, -, -, ht⟩, -, hcost, -⟩ :=
      exists_run_liftRight_of_wp (fun _ => 1) (L.wp_fallbackProg h hfit hcap hloop)
    rw [rehash, hcost]
    exact_mod_cast ht.trans (by simp only [rehashCost]; omega)
  | n + 1, s, h, hks => by
    set R : ℝ≥0∞ := ((rehashCost U b n_max maxLoop : ℕ) : ℝ≥0∞)
    have hout (θ : Seed U b) := L.attempt_outcome (maxLoop := maxLoop) hfit h θ
    -- the continuation costs one unit after a success, and at most `R` after a failure
    have hk (θ : Seed U b) : (Memory.spec w).toRandomized.withCoins.expectedCost (memCharge w)
        (if (Memory.spec w).clientResult (L.fillState s θ) (L.rebuildProg maxLoop) then
          OracleComp.liftRight (L.fresh.set 0 1) else L.rehash maxLoop n)
        ((Memory.spec w).clientState (L.fillState s θ) (L.rebuildProg maxLoop)) ≤
        if (scheme U b maxLoop attempts).Good θ ks then 1 else R := by
      obtain ⟨hr, hR', habs', -, hf', -⟩ := hout θ
      have hks' : L.keyList ((Memory.spec w).clientState (L.fillState s θ)
          (L.rebuildProg maxLoop)) = ks := by
        have := congrArg Model.keys habs'
        simpa [hks] using this
      have hG : (scheme U b maxLoop attempts).Good θ ks ↔
          (Memory.spec w).clientResult (L.fillState s θ) (L.rebuildProg maxLoop) = true := by
        rw [hr, hks]
        rfl
      by_cases hg : (scheme U b maxLoop attempts).Good θ ks
      · rw [ite_eq_left (hG.mp hg), ite_eq_left hg]
        obtain ⟨_, _, t, ht, -, hcost, -⟩ := exists_run_liftRight_of_wp (fun _ => 1)
          (L.wp_setFresh hfit hR'.allocated 1 le_rfl)
        rw [hcost, ht, Nat.cast_one]
      · rw [ite_eq_right (mt hG.mpr hg), ite_eq_right hg]
        exact expectedCost_rehash_le hfit hcap hloop attempts hhalf n hR' hks'
    rw [rehash, RandomizedSpec.expectedCost_bind, run_attempt, Probability.PMF.tsum_bind_mul]
    simp only [Probability.PMF.tsum_pure_mul]
    have hsum : ∑' θ, Probability.PMF.uniformOfFintype (Seed U b) θ *
        (if (scheme U b maxLoop attempts).Good θ ks then 1 else R) ≤ 1 + 2⁻¹ * R := by
      calc _ ≤ ∑' θ, (Probability.PMF.uniformOfFintype (Seed U b) θ +
            {θ | ¬ (scheme U b maxLoop attempts).Good θ ks}.indicator
              (Probability.PMF.uniformOfFintype (Seed U b)) θ * R) := by
            refine tsum_le_tsum fun θ => ?_
            by_cases hg : (scheme U b maxLoop attempts).Good θ ks
            · rw [ite_eq_left hg, mul_one]
              exact le_self_add
            · rw [ite_eq_right hg, Set.indicator_of_mem (by exact hg)]
              exact le_add_self
        _ = 1 + (Probability.PMF.uniformOfFintype (Seed U b)).toOuterMeasure
            {θ | ¬ (scheme U b maxLoop attempts).Good θ ks} * R := by
            rw [tsum_add, PMF.tsum_coe, ENNReal.tsum_mul_right, PMF.toOuterMeasure_apply]
        _ ≤ 1 + 2⁻¹ * R := by gcongr
    calc _ ≤ ((attemptCost U b n_max maxLoop : ℕ) : ℝ≥0∞) + (1 + 2⁻¹ * R) :=
          add_le_add (L.expectedCost_attempt_le hfit h)
            ((tsum_le_tsum fun θ => mul_le_mul' le_rfl (hk θ)).trans hsum)
      _ ≤ R := by
          simp only [R, rehashCost, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
          set X : ℝ≥0∞ := ((attemptCost U b n_max maxLoop : ℕ) : ℝ≥0∞) + 1
          set Y : ℝ≥0∞ := ((fallbackCost U b n_max maxLoop : ℕ) : ℝ≥0∞)
          have h2 : (2 : ℝ≥0∞)⁻¹ * (2 * X + Y) = X + 2⁻¹ * Y := by
            rw [mul_add, ← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top,
              one_mul]
          have hY : (2 : ℝ≥0∞)⁻¹ * Y ≤ Y :=
            mul_le_of_le_one_left (zero_le) (ENNReal.inv_le_one.mpr one_le_two)
          calc _ = X + (X + 2⁻¹ * Y) := by rw [h2]; ring
            _ ≤ X + (X + Y) := by gcongr
            _ = 2 * X + Y := by ring

omit [NeZero U] in
/-- Every outcome of an attempt is the rebuild after fresh hash tables holding some seed. -/
theorem exists_of_mem_support_attempt {s : Memory.State} {x : Bool × Memory.State}
    (hx : x ∈ ((Memory.spec w).toRandomized.withCoins.run (L.attempt maxLoop) s).support) :
    ∃ θ, x = ((Memory.spec w).clientResult (L.fillState s θ) (L.rebuildProg maxLoop),
      (Memory.spec w).clientState (L.fillState s θ) (L.rebuildProg maxLoop)) := by
  rw [run_attempt, PMF.mem_support_bind_iff] at hx
  obtain ⟨θ, -, hx⟩ := hx
  exact ⟨θ, (PMF.mem_support_pure_iff _ _).mp hx⟩

/-- **Every call of a rehash is admissible**, from the records, when `b`-bit words fit. -/
theorem demonicValid_rehash (hfit : Fits w (L.base + span U b n_max)) (hcap : n_max ≤ 2 ^ b)
    (hloop : 0 < maxLoop) (hb : b ≤ w) :
    ∀ n {s : Memory.State}, L.Records s →
      (Memory.spec w).toRandomized.withCoins.toSpec.DemonicValid s (L.rehash maxLoop n)
  | 0, s, h => (exists_run_liftRight_of_wp (fun _ => 1)
      (L.wp_fallbackProg h hfit hcap hloop)).choose_spec.choose_spec.choose_spec.2.2.2
  | n + 1, s, h => by
    have hfront := h.allocated
    refine StateTransitionSpec.DemonicValid.bind ?_ fun ok s' tr hrun => ?_
    · refine StateTransitionSpec.DemonicValid.bind
        (HashFamily.RandomTable.demonicValid_fill hb (by simp)
          (by simp only [Block.Allocated, h1_base, h1_length, span] at hfront ⊢; omega))
        fun _ s₁ tr₁ hrun₁ => ?_
      obtain ⟨θ₁, hs₁⟩ := exists_eq_writeFrom_of_mem_support
        (RandomizedSpec.mem_support_run_of_clientRun _ hrun₁)
      have hf₁ : s₁.frontier = s.frontier := by
        simp only at hs₁
        rw [hs₁, HashFamily.RandomTable.frontier_writeFrom]
      refine StateTransitionSpec.DemonicValid.bind
        (HashFamily.RandomTable.demonicValid_fill hb (by simp)
          (by simp only [Block.Allocated, h2_base, h2_length, span] at hfront ⊢; omega))
        fun _ s₂ tr₂ hrun₂ => ?_
      obtain ⟨θ₂, hs₂⟩ := exists_eq_writeFrom_of_mem_support
        (RandomizedSpec.mem_support_run_of_clientRun _ hrun₂)
      have hst : s₂ = L.fillState s (θ₁, θ₂) := by simp only at hs₁ hs₂; rw [hs₂, hs₁]; rfl
      rw [hst]
      exact (exists_run_liftRight_of_wp (fun _ => 1) (L.wp_rebuildProg (maxLoop := maxLoop)
        (h.fillState (θ₁, θ₂)) hfit)).choose_spec.choose_spec.choose_spec.2.2.2
    · obtain ⟨θ, hx⟩ := L.exists_of_mem_support_attempt
        (RandomizedSpec.mem_support_run_of_clientRun _ hrun)
      obtain ⟨-, hR', -, -, -, -⟩ := L.attempt_outcome (maxLoop := maxLoop) hfit h θ
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hx
      split
      · exact (exists_run_liftRight_of_wp (fun _ => 1)
          (L.wp_setFresh hfit hR'.allocated 1 le_rfl)).choose_spec.choose_spec.choose_spec.2.2.2
      · exact demonicValid_rehash hfit hcap hloop hb n hR'

end Layout

end Cslib.DataStructure.Dictionary.CuckooHashing.Memory
