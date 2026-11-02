/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.CuckooHashing.Memory.Basic

/-!
# Cuckoo hashing over the memory oracle: the eviction walk

An insertion places its entry in the first table at its first hash. A displaced entry moves to
the second table at its second hash, and an entry displaced there starts the next round
(`Layout.evict`). This is `WordRAM.CuckooHashing.pureEvict` on the encoded tables
(`Layout.wp_evict`): each round reads the hashes and the displaced keys, writes two slots, and
costs at most eight memory units, so a walk costs at most `8 * evictRounds`. The walk writes only
the tables, and its answer says whether it settled.

`Layout.Walk` is what the walk needs from memory: the hash tables hold the seed, the key cells hold
the keys, and the tables encode a pure table whose entries point at their keys. A replay is then a
sequence of walks over the cleared tables (`Layout.wp_replay`): from empty tables, the walks of the
first `n` keys settle exactly when `pureReplay` of these keys succeeds, and then the tables encode
it.

An insertion (`Layout.insertProg`) probes for the key. A stored key has its value overwritten in
place (`Layout.wp_insertProg_present`, seven units). A new key is appended with its value and its
walk is run (`Layout.wp_insertProg_new`, `10 + 8 * evictRounds` units); the insertion answers
whether a rehash is needed, which happens exactly when the keys with the new one do not replay.

## Main definitions

* `Memory.Consistent`: the entries of a pure table are the keys at their insertion indices.
* `Memory.Layout.Walk`: the memory during a walk.
* `Memory.Layout.evict`, `Memory.Layout.replay`, `Memory.Layout.insertProg`: the eviction walk,
  the replay of the keys, and an insertion.

## Main results

* `Memory.Layout.wp_evict`: a walk computes `pureEvict` within `8 * evictRounds` units.
* `Memory.Layout.wp_replay`: a replay computes `pureReplay`.
* `Memory.Layout.dictOf_append`, `Memory.Layout.dictOf_set`: the stored dictionary after an
  insertion.
* `Memory.Layout.wp_insertProg_present`, `Memory.Layout.wp_insertProg_new`: insertions.

## References

* [R. Pagh and F. F. Rodler, "Cuckoo hashing"][PaghRodler2004]
-/

@[expose] public section

namespace Cslib.DataStructure.Dictionary.CuckooHashing.Memory

open Cslib.WordRAM Cslib.DataStructure
open Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing

variable {U b : ℕ}

/-- The entries of `T` are the keys `ks` at their insertion indices. -/
def Consistent (T : PureTable U (2 ^ b)) (ks : List (Fin U)) : Prop :=
  ∀ j e, (T.t1 j = some e ∨ T.t2 j = some e) → ∃ h : e.idx < ks.length, ks[e.idx] = e.key

theorem consistent_empty (ks : List (Fin U)) : Consistent (PureTable.empty U (2 ^ b)) ks := by
  rintro j e (h | h) <;> cases h

/-- Placing a consistent entry in the first table keeps the table consistent. -/
theorem Consistent.putT1 {T : PureTable U (2 ^ b)} {ks : List (Fin U)} (hT : Consistent T ks)
    (h₁ : Fin U → Fin (2 ^ b)) {e : SlotEntry U}
    (he : ∃ h : e.idx < ks.length, ks[e.idx] = e.key) :
    Consistent (putT1 h₁ T e).1 ks := by
  intro j d hd
  simp only [WordRAM.CuckooHashing.putT1] at hd
  rcases hd with hd | hd
  · by_cases hj : j = h₁ e.key
    · subst hj
      rw [Function.update_self, Option.some.injEq] at hd
      exact hd ▸ he
    · rw [Function.update_of_ne hj] at hd
      exact hT j d (Or.inl hd)
  · exact hT j d (Or.inr hd)

/-- Placing a consistent entry in the second table keeps the table consistent. -/
theorem Consistent.putT2 {T : PureTable U (2 ^ b)} {ks : List (Fin U)} (hT : Consistent T ks)
    (h₂ : Fin U → Fin (2 ^ b)) {e : SlotEntry U}
    (he : ∃ h : e.idx < ks.length, ks[e.idx] = e.key) :
    Consistent (putT2 h₂ T e).1 ks := by
  intro j d hd
  simp only [WordRAM.CuckooHashing.putT2] at hd
  rcases hd with hd | hd
  · exact hT j d (Or.inl hd)
  · by_cases hj : j = h₂ e.key
    · subst hj
      rw [Function.update_self, Option.some.injEq] at hd
      exact hd ▸ he
    · rw [Function.update_of_ne hj] at hd
      exact hT j d (Or.inr hd)

/-- Consistency survives more keys. -/
theorem Consistent.append {T : PureTable U (2 ^ b)} {ks : List (Fin U)} (hT : Consistent T ks)
    (ks' : List (Fin U)) : Consistent T (ks ++ ks') := by
  intro j e he
  obtain ⟨hi, hk⟩ := hT j e he
  exact ⟨by simp; omega, by rw [List.getElem_append_left hi]; exact hk⟩

namespace Layout

variable {n_max : ℕ} (L : Layout U b n_max)

/-- The memory during an eviction walk under the seed `θ` with the keys `ks`: the layout is
allocated and fits a word, the hash tables hold `θ`, the key cells hold `ks`, and the tables
encode `T`, whose entries are consistent with `ks`. -/
structure Walk (w : ℕ) (s : Memory.State) (θ : Seed U b) (ks : List (Fin U))
    (T : PureTable U (2 ^ b)) : Prop where
  /-- Every field is allocated. -/
  allocated : L.base + span U b n_max ≤ s.frontier
  /-- Every address of the layout fits a word. -/
  fits : Fits w (L.base + span U b n_max)
  /-- At most `n_max` keys. -/
  length_le : ks.length ≤ n_max
  /-- The first hash table holds the first hash function. -/
  h1_eq : ∀ u : Fin U, s.mem (L.h1.base + u) = (θ.1 u : ℕ)
  /-- The second hash table holds the second hash function. -/
  h2_eq : ∀ u : Fin U, s.mem (L.h2.base + u) = (θ.2 u : ℕ)
  /-- The key cells hold the keys. -/
  keys_eq : ∀ i (hi : i < ks.length), s.mem (L.keys.base + i) = (ks[i] : ℕ)
  /-- The tables encode `T`. -/
  encodes : L.Encodes s T
  /-- The entries of `T` point at their keys. -/
  consistent : Consistent T ks

variable {L} {w : ℕ}

/-- A walk state survives changes to the tables that encode a new consistent table. -/
theorem Walk.of_tables {s s' : Memory.State} {θ : Seed U b} {ks : List (Fin U)}
    {T T' : PureTable U (2 ^ b)} (h : L.Walk w s θ ks T)
    (hframe : ∀ a, ¬ L.InTables a → s'.mem a = s.mem a) (hf : s'.frontier = s.frontier)
    (hE : L.Encodes s' T') (hC : Consistent T' ks) : L.Walk w s' θ ks T' where
  allocated := hf ▸ h.allocated
  fits := h.fits
  length_le := h.length_le
  h1_eq u := by
    rw [hframe _ (by simp only [InTables, t1_base, h1_base]; omega), h.h1_eq u]
  h2_eq u := by
    rw [hframe _ (by simp only [InTables, t1_base, h2_base]; omega), h.h2_eq u]
  keys_eq i hi := by
    have := h.length_le
    rw [hframe _ (by simp only [InTables, t1_base, keys_base]; omega), h.keys_eq i hi]
  encodes := hE
  consistent := hC

/-- Writing a slot of the first table encodes the updated table. -/
theorem Encodes.update_t1 {s : Memory.State} {T : PureTable U (2 ^ b)} (hE : L.Encodes s T)
    (j : Fin (2 ^ b)) (o : Option (SlotEntry U)) :
    L.Encodes ⟨Function.update s.mem (L.t1.base + j) (slotWord o), s.frontier⟩
      { T with t1 := Function.update T.t1 j o } := by
  intro j'
  refine ⟨?_, ?_⟩
  · by_cases hj : j' = j
    · subst hj
      simp
    · have hne : L.t1.base + (j' : ℕ) ≠ L.t1.base + j := fun h => hj (Fin.ext (by omega))
      simp only [Function.update_of_ne hne, Function.update_of_ne hj]
      exact (hE j').1
  · have hne : L.t2.base + (j' : ℕ) ≠ L.t1.base + j := by
      have := j.2
      simp only [t1_base, t2_base]
      omega
    simp only [Function.update_of_ne hne]
    exact (hE j').2

/-- Writing a slot of the second table encodes the updated table. -/
theorem Encodes.update_t2 {s : Memory.State} {T : PureTable U (2 ^ b)} (hE : L.Encodes s T)
    (j : Fin (2 ^ b)) (o : Option (SlotEntry U)) :
    L.Encodes ⟨Function.update s.mem (L.t2.base + j) (slotWord o), s.frontier⟩
      { T with t2 := Function.update T.t2 j o } := by
  intro j'
  refine ⟨?_, ?_⟩
  · have hne : L.t1.base + (j' : ℕ) ≠ L.t2.base + j := by
      have := j'.2
      simp only [t1_base, t2_base]
      omega
    simp only [Function.update_of_ne hne]
    exact (hE j').1
  · by_cases hj : j' = j
    · subst hj
      simp
    · have hne : L.t2.base + (j' : ℕ) ≠ L.t2.base + j := fun h => hj (Fin.ext (by omega))
      simp only [Function.update_of_ne hne, Function.update_of_ne hj]
      exact (hE j').2

variable (L) in
/-- The eviction walk of the entry with key `k` and insertion index `i`, for at most `fuel`
rounds: place it in the first table, move a displaced entry to the second table, and continue
with the entry displaced there. It answers whether the walk settled. -/
def evict : ℕ → ℕ → ℕ → Memory.Prog Bool
  | 0, _, _ => pure false
  | fuel + 1, k, i => do
    let j ← L.h1.get k
    let c ← L.t1.get j
    L.t1.set j (i + 1)
    if c = 0 then pure true else do
      let k₁ ← L.keys.get (c - 1)
      let j₂ ← L.h2.get k₁
      let c₂ ← L.t2.get j₂
      L.t2.set j₂ c
      if c₂ = 0 then pure true else do
        let k₂ ← L.keys.get (c₂ - 1)
        evict fuel k₂ (c₂ - 1)

/-- **The eviction walk computes `pureEvict`.** From a walk state and a consistent entry, the walk
answers whether `pureEvict` settles, leaves a walk state encoding its result if so, writes only
the tables, and costs at most eight units per round. -/
theorem wp_evict {θ : Seed U b} {ks : List (Fin U)} :
    ∀ (fuel : ℕ) {s : Memory.State} {T : PureTable U (2 ^ b)} {e : SlotEntry U},
      L.Walk w s θ ks T → (∃ h : e.idx < ks.length, ks[e.idx] = e.key) →
      (Memory.spec w).wp Memory.charge (L.evict fuel e.key e.idx) (fun r s' t =>
        r = (pureEvict θ.1 θ.2 fuel T e).isSome ∧
        (∀ T', pureEvict θ.1 θ.2 fuel T e = some T' → L.Walk w s' θ ks T') ∧
        (∀ a, ¬ L.InTables a → s'.mem a = s.mem a) ∧ s'.frontier = s.frontier ∧
        t ≤ 8 * evictRounds θ.1 θ.2 fuel T e) s
  | 0, s, T, e, _, _ => by
    simp [evict, pureEvict, evictRounds]
  | fuel + 1, s, T, e, h, he => by
    obtain ⟨hei, hek⟩ := he
    have hlen := h.length_le
    obtain ⟨j, hjdef⟩ : ∃ j, θ.1 e.key = j := ⟨_, rfl⟩
    have hj := j.2
    have hu := e.key.2
    have hfront := h.allocated
    have hfit := h.fits
    -- the first round: read the hash and the slot, write the entry
    have r₁ : L.h1.base + (e.key : ℕ) < s.frontier := by
      simp only [h1_base, span] at hfront ⊢; omega
    have r₂ : L.t1.base + (j : ℕ) < s.frontier := by
      simp only [t1_base, span] at hfront ⊢; omega
    have f₁ : Fits w (e.idx + 1) := hfit.of_le (by simp only [span]; omega)
    simp only [evict, StateTransitionSpec.wp_lift_bind, StateTransitionSpec.stepFn,
      Memory.step_read, Memory.step_write, Memory.valid_read, Memory.valid_write,
      Memory.charge_read, Memory.charge_write, h.h1_eq e.key, hjdef, (h.encodes j).1]
    refine ⟨r₁, r₂, ⟨r₂, f₁⟩, ?_⟩
    set s₁ : Memory.State := ⟨Function.update s.mem (L.t1.base + j) (e.idx + 1), s.frontier⟩
      with hs₁
    set T₁ : PureTable U (2 ^ b) := { T with t1 := Function.update T.t1 j (some e) }
    have hE₁ : L.Encodes s₁ T₁ := h.encodes.update_t1 j (some e)
    have hC₁ : Consistent T₁ ks := by
      convert h.consistent.putT1 θ.1 ⟨hei, hek⟩ using 1
      simp [WordRAM.CuckooHashing.putT1, T₁, hjdef]
    have hframe₁ : ∀ a, ¬ L.InTables a → s₁.mem a = s.mem a := fun a ha =>
      Function.update_of_ne (fun h' => ha (by simp only [InTables, t1_base] at h' ⊢; omega)) _ _
    have hW₁ : L.Walk w s₁ θ ks T₁ := h.of_tables hframe₁ rfl hE₁ hC₁
    cases ht : T.t1 j with
    | none =>
      have hround : pureEvictRound θ.1 θ.2 T e = (T₁, none) := by
        simp [pureEvictRound, WordRAM.CuckooHashing.putT1, ht, T₁, hjdef]
      simp only [slotWord_none, ite_true, StateTransitionSpec.wp_pure]
      refine ⟨by simp [pureEvict, hround], fun T' hT' => ?_, hframe₁, rfl, ?_⟩
      · simp only [pureEvict, hround, Option.some.injEq] at hT'
        exact hT' ▸ hW₁
      · simp [evictRounds, hround]
    | some e₁ =>
      obtain ⟨hi₁, hk₁⟩ := h.consistent j e₁ (Or.inl ht)
      obtain ⟨j₂, hj₂def⟩ : ∃ j₂, θ.2 e₁.key = j₂ := ⟨_, rfl⟩
      have hj₂ := j₂.2
      have hu₁ := e₁.key.2
      have r₃ : L.keys.base + e₁.idx < s.frontier := by
        simp only [keys_base, span] at hfront ⊢; omega
      have r₄ : L.h2.base + (e₁.key : ℕ) < s.frontier := by
        simp only [h2_base, span] at hfront ⊢; omega
      have r₅ : L.t2.base + (j₂ : ℕ) < s.frontier := by
        simp only [t2_base, span] at hfront ⊢; omega
      have f₂ : Fits w (e₁.idx + 1) := hfit.of_le (by simp only [span]; omega)
      have m₃ : s₁.mem (L.keys.base + e₁.idx) = e₁.key := by
        rw [hW₁.keys_eq e₁.idx hi₁, hk₁]
      have m₄ : s₁.mem (L.h2.base + e₁.key) = j₂ := by rw [hW₁.h2_eq e₁.key, hj₂def]
      have m₅ : s₁.mem (L.t2.base + j₂) = slotWord (T.t2 j₂) := (hE₁ j₂).2
      simp only [slotWord_some, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel,
        StateTransitionSpec.wp_lift_bind, StateTransitionSpec.stepFn, Memory.step_read,
        Memory.step_write, Memory.valid_read, Memory.valid_write, Memory.charge_read,
        Memory.charge_write, m₃, m₄, m₅]
      refine ⟨r₃, r₄, r₅, ⟨r₅, f₂⟩, ?_⟩
      set s₂ : Memory.State := ⟨Function.update s₁.mem (L.t2.base + j₂) (e₁.idx + 1), s₁.frontier⟩
        with hs₂
      set T₂ : PureTable U (2 ^ b) := { T₁ with t2 := Function.update T₁.t2 j₂ (some e₁) }
      have hE₂ : L.Encodes s₂ T₂ := hE₁.update_t2 j₂ (some e₁)
      have hC₂ : Consistent T₂ ks := by
        convert hC₁.putT2 θ.2 ⟨hi₁, hk₁⟩ using 1
        simp [WordRAM.CuckooHashing.putT2, T₂, hj₂def]
      have hframe₂ : ∀ a, ¬ L.InTables a → s₂.mem a = s.mem a := fun a ha => by
        rw [← hframe₁ a ha]
        exact Function.update_of_ne
          (fun h' => ha (by simp only [InTables, t1_base, t2_base] at h' ⊢; omega)) _ _
      have hW₂ : L.Walk w s₂ θ ks T₂ := h.of_tables hframe₂ rfl hE₂ hC₂
      cases ht₂ : T.t2 j₂ with
      | none =>
        have hround : pureEvictRound θ.1 θ.2 T e = (T₂, none) := by
          simp [pureEvictRound, WordRAM.CuckooHashing.putT1, WordRAM.CuckooHashing.putT2, ht,
            ht₂, T₁, T₂, hjdef, hj₂def]
        simp only [slotWord_none, ite_true, StateTransitionSpec.wp_pure]
        refine ⟨by simp [pureEvict, hround], fun T' hT' => ?_, hframe₂, rfl, ?_⟩
        · simp only [pureEvict, hround, Option.some.injEq] at hT'
          exact hT' ▸ hW₂
        · simp [evictRounds, hround]
      | some e₂ =>
        obtain ⟨hi₂, hk₂⟩ := h.consistent j₂ e₂ (Or.inr ht₂)
        have r₆ : L.keys.base + e₂.idx < s.frontier := by
          simp only [keys_base, span] at hfront ⊢; omega
        have m₆ : s₂.mem (L.keys.base + e₂.idx) = e₂.key := by
          rw [hW₂.keys_eq e₂.idx hi₂, hk₂]
        have hround : pureEvictRound θ.1 θ.2 T e = (T₂, some e₂) := by
          simp [pureEvictRound, WordRAM.CuckooHashing.putT1, WordRAM.CuckooHashing.putT2, ht,
            ht₂, T₁, T₂, hjdef, hj₂def]
        simp only [slotWord_some, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel,
          StateTransitionSpec.wp_lift_bind, StateTransitionSpec.stepFn, Memory.step_read,
          Memory.valid_read, Memory.charge_read, m₆]
        refine ⟨r₆, ?_⟩
        refine StateTransitionSpec.wp_mono (fun r s' t ⟨hr, hW, hfr, hf, hc⟩ => ?_)
          (wp_evict fuel hW₂ ⟨hi₂, hk₂⟩)
        refine ⟨by simpa [pureEvict, hround] using hr, fun T' hT' => hW T' (by
          simpa [pureEvict, hround] using hT'), fun a ha => (hfr a ha).trans (hframe₂ a ha),
          hf, ?_⟩
        simp only [evictRounds, hround]
        omega

/-! ## Replay -/

/-- Once a prefix of the keys fails to replay, every longer prefix fails. -/
theorem pureReplay_take_eq_none {θ : Seed U b} {ks : List (Fin U)} {maxLoop i : ℕ}
    (h : pureReplay θ.1 θ.2 maxLoop (ks.take i) = none) (r : ℕ) :
    pureReplay θ.1 θ.2 maxLoop (ks.take (i + r)) = none := by
  induction r with
  | zero => exact h
  | succ r ih =>
    rw [← Nat.add_assoc, List.take_add_one]
    cases hk : ks[i + r]? with
    | none => simpa using ih
    | some k => simp [pureReplay_append_singleton, ih]

variable (L) in
/-- Replay the keys with insertion indices `i, …, i + r - 1` into the tables, one eviction walk
each, and stop at the first walk that does not settle. It answers whether every walk settled. -/
def replay (maxLoop : ℕ) : ℕ → ℕ → Memory.Prog Bool
  | _, 0 => pure true
  | i, r + 1 => do
    let k ← L.keys.get i
    let ok ← L.evict maxLoop k i
    if ok then replay maxLoop (i + 1) r else pure false

/-- **A replay computes `pureReplay`.** From a walk state encoding the replay of the first `i`
keys, replaying the next `r` keys answers whether `pureReplay` of the first `i + r` keys succeeds,
leaves a walk state encoding it if so, writes only the tables, and costs at most
`1 + 8 * maxLoop` units per key. -/
theorem wp_replay {θ : Seed U b} {ks : List (Fin U)} {maxLoop : ℕ} :
    ∀ (r i : ℕ) {s : Memory.State} {T : PureTable U (2 ^ b)}, i + r ≤ ks.length →
      L.Walk w s θ ks T → pureReplay θ.1 θ.2 maxLoop (ks.take i) = some T →
      (Memory.spec w).wp Memory.charge (L.replay maxLoop i r) (fun ok s' t =>
        ok = (pureReplay θ.1 θ.2 maxLoop (ks.take (i + r))).isSome ∧
        (∀ T', pureReplay θ.1 θ.2 maxLoop (ks.take (i + r)) = some T' →
          L.Walk w s' θ ks T') ∧
        (∀ a, ¬ L.InTables a → s'.mem a = s.mem a) ∧ s'.frontier = s.frontier ∧
        t ≤ r * (1 + 8 * maxLoop)) s
  | 0, i, s, T, _, h, hT => by
    rw [replay, StateTransitionSpec.wp_pure, Nat.add_zero, hT]
    refine ⟨rfl, fun T' hT' => ?_, fun _ _ => rfl, rfl, Nat.zero_le _⟩
    cases hT'
    exact h
  | r + 1, i, s, T, hr, h, hT => by
    have hi : i < ks.length := by omega
    have hfront := h.allocated
    have hlen := h.length_le
    have r₁ : L.keys.base + i < s.frontier := by
      simp only [keys_base, span] at hfront ⊢; omega
    have htake : ks.take (i + 1) = ks.take i ++ [ks[i]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi]
      rfl
    have hstep : pureReplay θ.1 θ.2 maxLoop (ks.take (i + 1)) =
        pureEvict θ.1 θ.2 maxLoop T ⟨ks[i], i⟩ := by
      rw [htake, pureReplay_append_singleton, hT, List.length_take_of_le hi.le]
      rfl
    simp only [replay, StateTransitionSpec.wp_lift_bind, StateTransitionSpec.stepFn,
      Memory.step_read, Memory.valid_read, Memory.charge_read, h.keys_eq i hi]
    refine ⟨r₁, ?_⟩
    rw [StateTransitionSpec.wp_bind]
    refine StateTransitionSpec.wp_mono (fun ok s₁ t₁ ⟨hok, hW₁, hfr₁, hf₁, hc₁⟩ => ?_)
      (wp_evict (e := ⟨ks[i], i⟩) maxLoop h ⟨hi, rfl⟩)
    have hc₁' : t₁ ≤ 8 * maxLoop := hc₁.trans (Nat.mul_le_mul_left 8 (evictRounds_le _ _ _ _ _))
    by_cases hev : (pureEvict θ.1 θ.2 maxLoop T ⟨ks[i], i⟩).isSome
    · obtain ⟨T₁, hT₁⟩ := Option.isSome_iff_exists.mp hev
      rw [hok, hev, ite_eq_left rfl]
      refine StateTransitionSpec.wp_mono (fun ok' s' t' ⟨hok', hW', hfr', hf', hc'⟩ => ?_)
        (wp_replay r (i + 1) (by omega) (hW₁ T₁ hT₁) (hstep.trans hT₁))
      rw [show i + (r + 1) = i + 1 + r by omega]
      refine ⟨hok', hW', fun a ha => (hfr' a ha).trans (hfr₁ a ha), hf'.trans hf₁, ?_⟩
      rw [Nat.succ_mul]
      omega
    · rw [hok, Bool.eq_false_iff.mpr hev, ite_eq_right Bool.false_ne_true,
        StateTransitionSpec.wp_pure]
      have hnone : pureReplay θ.1 θ.2 maxLoop (ks.take (i + 1)) = none := by
        rw [hstep]
        simpa using hev
      rw [show i + (r + 1) = i + 1 + r by omega, pureReplay_take_eq_none hnone]
      refine ⟨rfl, (fun _ h' => by cases h'), hfr₁, hf₁, ?_⟩
      rw [Nat.succ_mul]
      omega

/-! ## Insertion -/

/-- Appending a new key and its value stores the value at the key. -/
theorem dictOf_append {ks : List (Fin U)} {vs : List ℕ} (hlen : vs.length = ks.length)
    {u : Fin U} (hu : u ∉ ks) (v : ℕ) :
    dictOf (ks ++ [u]) (vs ++ [v]) = Function.update (dictOf ks vs) u (some v) := by
  funext x
  unfold dictOf
  by_cases hx : x = u
  · subst hx
    rw [Function.update_self, List.idxOf_append_of_notMem hu, List.idxOf_cons_self, Nat.add_zero,
      List.getElem?_append_right (by omega), hlen, Nat.sub_self]
    rfl
  · rw [Function.update_of_ne hx]
    by_cases hm : x ∈ ks
    · rw [List.idxOf_append_of_mem hm,
        List.getElem?_append_left (by rw [hlen]; exact List.idxOf_lt_length_of_mem hm)]
    · rw [List.idxOf_append_of_notMem hm, List.idxOf_cons_ne _ (Ne.symm hx), List.idxOf_nil,
        List.idxOf_eq_length hm, List.getElem?_eq_none (by simp; omega),
        List.getElem?_eq_none (by omega)]

/-- Overwriting the value at the index of a stored key stores the new value at the key. -/
theorem dictOf_set {ks : List (Fin U)} {vs : List ℕ} (hlen : vs.length = ks.length)
    {u : Fin U} (hu : u ∈ ks) (v : ℕ) :
    dictOf ks (vs.set (ks.idxOf u) v) = Function.update (dictOf ks vs) u (some v) := by
  have hi := List.idxOf_lt_length_of_mem hu
  funext x
  unfold dictOf
  by_cases hx : x = u
  · subst hx
    rw [Function.update_self, List.getElem?_set_self (by omega)]
  · rw [Function.update_of_ne hx, List.getElem?_set_ne]
    intro heq
    by_cases hm : x ∈ ks
    · have hj := List.idxOf_lt_length_of_mem hm
      exact hx (by rw [← List.getElem_idxOf hj, ← List.getElem_idxOf hi]; simp only [heq])
    · rw [List.idxOf_eq_length hm] at heq
      omega

variable (L) in
/-- Insert `u ↦ v`: overwrite the value of a stored key in place; otherwise append the key and
the value and run the eviction walk of the new entry. It answers whether a rehash is needed. -/
def insertProg (maxLoop u v : ℕ) : Memory.Prog Bool := do
  let r ← L.probe u
  match r with
  | some i => do
    L.vals.set i v
    pure false
  | none => do
    let n ← L.count.get 0
    L.keys.set n u
    L.vals.set n v
    L.count.set 0 (n + 1)
    let ok ← L.evict maxLoop u n
    pure (!ok)

/-- Overwriting an entry of a field changes that entry of its list view. -/
theorem entries_update (blk : Block) (n i : ℕ) (m : ℕ → ℕ) (v : ℕ) :
    blk.entries n (Function.update m (blk.base + i) v) = (blk.entries n m).set i v := by
  refine List.ext_getElem (by simp) fun j hj _ => ?_
  simp only [Block.length_entries] at hj
  simp only [Block.getElem_entries, List.getElem_set]
  by_cases hji : i = j
  · subst hji
    simp
  · rw [Function.update_of_ne (by omega), ite_eq_right hji]

variable [NeZero U] {maxLoop : ℕ}

/-- **Updating a stored key.** Under the invariant, inserting a stored key overwrites its value
in place, in at most seven units, and needs no rehash. -/
theorem wp_insertProg_present {s : Memory.State} (h : L.Inv maxLoop s) {u : Fin U}
    (hu : u ∈ L.keyList s) {v : ℕ} (hv : Fits w v) :
    (Memory.spec w).wp Memory.charge (L.insertProg maxLoop u v) (fun r s' t =>
      r = false ∧ L.Inv maxLoop s' ∧
      L.abs s' = { L.abs s with dict := Function.update (L.abs s).dict u (some v) } ∧
      s'.frontier = s.frontier ∧ t ≤ 7) s := by
  obtain ⟨T, hT, hE⟩ := h.tables
  rw [insertProg, StateTransitionSpec.wp_bind]
  refine StateTransitionSpec.wp_mono (fun r s₀ t₀ ⟨hr, hs₀, hc₀⟩ => ?_)
    (wp_probe (w := w) h hT hE u)
  subst hs₀
  rw [lookupEntry_map_idx h hT, ite_eq_left hu] at hr
  subst hr
  have hi := List.idxOf_lt_length_of_mem hu
  rw [length_keyList] at hi
  have hn := h.count_le
  have r₁ := h.lt_frontier (a := L.vals.base + (L.keyList s₀).idxOf u)
    (by simp only [vals_base, span]; omega)
  have hk : L.SameKeys s₀
      ⟨Function.update s₀.mem (L.vals.base + (L.keyList s₀).idxOf u) v, s₀.frontier⟩ :=
    { n_eq := Function.update_of_ne (by simp only [vals_base]; omega) _ _
      keys_eq := fun i hi' => Function.update_of_ne (by simp only [vals_base, keys_base]; omega) _ _
      h1_eq := fun u hu' => Function.update_of_ne (by simp only [vals_base, h1_base]; omega) _ _
      h2_eq := fun u hu' => Function.update_of_ne (by simp only [vals_base, h2_base]; omega) _ _ }
  have hE' : L.Encodes
      ⟨Function.update s₀.mem (L.vals.base + (L.keyList s₀).idxOf u) v, s₀.frontier⟩ T :=
    fun j => by
      have hj := j.2
      simp only
      rw [Function.update_of_ne (by simp only [vals_base, t1_base]; omega),
        Function.update_of_ne (by simp only [vals_base, t2_base]; omega)]
      exact hE j
  have hval : L.valList
      ⟨Function.update s₀.mem (L.vals.base + (L.keyList s₀).idxOf u) v, s₀.frontier⟩ =
      (L.valList s₀).set ((L.keyList s₀).idxOf u) v := by
    simp only [valList, hk.n_eq]
    exact entries_update _ _ _ _ _
  have hf : (Function.update s₀.mem (L.vals.base + (L.keyList s₀).idxOf u) v) (L.base + 1) =
      s₀.mem (L.base + 1) :=
    Function.update_of_ne (by simp only [vals_base]; omega) _ _
  simp only [StateTransitionSpec.wp_lift_bind, StateTransitionSpec.wp_pure,
    StateTransitionSpec.stepFn, Memory.step_write, Memory.valid_write, Memory.charge_write]
  refine ⟨⟨r₁, hv⟩, trivial, ⟨h.toRecords.congr hk le_rfl, T, ?_, hE'⟩, ?_, trivial, by omega⟩
  · rw [hk.seed_eq, hk.keyList_eq]
    exact hT
  · simp only [abs, hk.seed_eq, hk.keyList_eq, hval, hf]
    rw [dictOf_set (by simp) hu]

/-- **Inserting a new key.** Under the invariant, inserting a new key below the capacity appends
it with its value and runs its eviction walk, in at most `10 + 8 * evictRounds` units. It needs a
rehash exactly when the keys with the new one do not replay under the seed, and otherwise
restores the invariant. The records always hold, and the stored model gains the key. -/
theorem wp_insertProg_new {s : Memory.State} (h : L.Inv maxLoop s)
    (hfit : Fits w (L.base + span U b n_max)) {u : Fin U} (hu : u ∉ L.keyList s)
    (hn : L.n s < n_max) {v : ℕ} (hv : Fits w v) {T : PureTable U (2 ^ b)}
    (hT : pureReplay (L.seed s).1 (L.seed s).2 maxLoop (L.keyList s) = some T) :
    (Memory.spec w).wp Memory.charge (L.insertProg maxLoop u v) (fun r s' t =>
      r = !(pureReplay (L.seed s).1 (L.seed s).2 maxLoop (L.keyList s ++ [u])).isSome ∧
      L.Records s' ∧
      L.abs s' = ⟨L.seed s, L.keyList s ++ [u], Function.update (L.abs s).dict u (some v),
        (L.abs s).fresh⟩ ∧
      (r = false → L.Inv maxLoop s') ∧ s'.frontier = s.frontier ∧
      t ≤ 10 + 8 * evictRounds (L.seed s).1 (L.seed s).2 maxLoop T ⟨u, (L.keyList s).length⟩)
      s := by
  obtain ⟨T₀, hT₀, hE⟩ := h.tables
  rw [hT₀, Option.some.injEq] at hT
  subst hT
  rw [insertProg, StateTransitionSpec.wp_bind]
  refine StateTransitionSpec.wp_mono (fun r s₀ t₀ ⟨hr, hs₀, hc₀⟩ => ?_)
    (wp_probe (w := w) h hT₀ hE u)
  subst hs₀
  rw [lookupEntry_map_idx h hT₀, ite_eq_right hu] at hr
  subst hr
  simp only [StateTransitionSpec.wp_lift_bind, StateTransitionSpec.stepFn, Memory.step_read,
    Memory.step_write, Memory.valid_read, Memory.valid_write, Memory.charge_read,
    Memory.charge_write, Nat.add_zero, show s₀.mem L.count.base = L.n s₀ from rfl]
  set n := L.n s₀ with hn_def
  set ks := L.keyList s₀ with hks_def
  have hlen : ks.length = n := length_keyList _ _
  have hfront := h.allocated
  have hu' := u.2
  have r₁ : L.count.base < s₀.frontier := by simp only [count_base, span] at hfront ⊢; omega
  have r₂ : L.keys.base + n < s₀.frontier := by simp only [keys_base, span] at hfront ⊢; omega
  have r₃ : L.vals.base + n < s₀.frontier := by simp only [vals_base, span] at hfront ⊢; omega
  have fu : Fits w (u : ℕ) := hfit.of_le (by simp only [span]; omega)
  have fn : Fits w (n + 1) := hfit.of_le (by simp only [span]; omega)
  refine ⟨r₁, ⟨r₂, fu⟩, ⟨r₃, hv⟩, ⟨r₁, fn⟩, ?_⟩
  set s₃ : Memory.State := ⟨Function.update (Function.update (Function.update s₀.mem
    (L.keys.base + n) u) (L.vals.base + n) v) L.count.base (n + 1), s₀.frontier⟩ with hs₃
  -- the cells after the three writes
  have hother : ∀ a, a ≠ L.count.base → a ≠ L.keys.base + n → a ≠ L.vals.base + n →
      s₃.mem a = s₀.mem a := fun a h₁ h₂ h₃ => by
    simp only [hs₃]
    rw [Function.update_of_ne h₁, Function.update_of_ne h₃, Function.update_of_ne h₂]
  have hn₃ : L.n s₃ = n + 1 := Function.update_self _ _ _
  have hcnt := h.count_le
  have hkey : ∀ i < n, s₃.mem (L.keys.base + i) = s₀.mem (L.keys.base + i) := fun i hi =>
    hother _ (by simp only [count_base, keys_base]; omega) (by omega)
      (by simp only [keys_base, vals_base]; omega)
  have hkeyn : s₃.mem (L.keys.base + n) = u := by
    simp only [hs₃]
    rw [Function.update_of_ne (by simp only [count_base, keys_base]; omega),
      Function.update_of_ne (by simp only [keys_base, vals_base]; omega), Function.update_self]
  have hval : ∀ i < n, s₃.mem (L.vals.base + i) = s₀.mem (L.vals.base + i) := fun i hi =>
    hother _ (by simp only [count_base, vals_base]; omega)
      (by simp only [keys_base, vals_base]; omega) (by omega)
  have hvaln : s₃.mem (L.vals.base + n) = v := by
    simp only [hs₃]
    rw [Function.update_of_ne (by simp only [count_base, vals_base]; omega), Function.update_self]
  have hfar : ∀ a, L.vals.base + n_max ≤ a → s₃.mem a = s₀.mem a := fun a ha =>
    hother a (by simp only [count_base, vals_base] at ha ⊢; omega)
      (by simp only [keys_base, vals_base] at ha ⊢; omega) (by omega)
  have hfresh : s₃.mem (L.base + 1) = s₀.mem (L.base + 1) :=
    hother _ (by simp only [count_base]; omega) (by simp only [keys_base]; omega)
      (by simp only [vals_base]; omega)
  have hseed : L.seed s₃ = L.seed s₀ := by
    simp only [seed]
    congr 1 <;> funext x <;> unfold HashFamily.RandomTable.tableOf
    · rw [hfar _ (by simp only [vals_base, h1_base]; omega)]
    · rw [hfar _ (by simp only [vals_base, h2_base]; omega)]
  have hks₃ : L.keyList s₃ = ks ++ [u] := by
    simp only [keyList, hn₃, Block.entries_succ, List.map_append, List.map_singleton, hkeyn,
      Fin.ofNat_val_eq_self, hks_def]
    rw [Block.entries_congr _ _ hkey]
  have hvs₃ : L.valList s₃ = L.valList s₀ ++ [v] := by
    simp only [valList, hn₃, Block.entries_succ, hvaln]
    rw [Block.entries_congr _ _ hval]
  have hR₃ : L.Records s₃ :=
    { allocated := hfront
      count_le := by omega
      keys_lt := fun i hi => by
        rw [hn₃] at hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · rw [hkey i hi]
          exact h.keys_lt i hi
        · rw [hkeyn]
          exact hu'
      nodup := by
        rw [hks₃]
        exact h.nodup.append (List.nodup_singleton u) (by simpa using hu)
      h1_lt := fun x hx => by
        rw [hfar _ (by simp only [vals_base, h1_base]; omega)]
        exact h.h1_lt x hx
      h2_lt := fun x hx => by
        rw [hfar _ (by simp only [vals_base, h2_base]; omega)]
        exact h.h2_lt x hx }
  have hC : Consistent T₀ (ks ++ [u]) := by
    refine Consistent.append (fun j e he => ?_) [u]
    refine entry_of_replay h.nodup hT₀ ?_
    rcases he with he | he
    · exact Or.inl ⟨j, he⟩
    · exact Or.inr ⟨j, he⟩
  have hW : L.Walk w s₃ (L.seed s₀) (ks ++ [u]) T₀ :=
    { allocated := hfront
      fits := hfit
      length_le := by simp; omega
      h1_eq := fun x => by
        rw [hfar _ (by simp only [vals_base, h1_base]; omega)]
        exact h.h1_eq x
      h2_eq := fun x => by
        rw [hfar _ (by simp only [vals_base, h2_base]; omega)]
        exact h.h2_eq x
      keys_eq := fun i hi => by
        simp only [List.length_append, List.length_singleton] at hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp (hlen ▸ hi) with hi' | rfl
        · rw [hkey i hi', h.keys_eq (by rw [← hks_def, hlen]; exact hi'),
            List.getElem_append_left (by omega)]
        · rw [hkeyn, List.getElem_append_right (by omega)]
          simp [hlen]
      encodes := fun j => by
        have hj := j.2
        rw [hfar _ (by simp only [vals_base, t1_base]; omega),
          hfar _ (by simp only [vals_base, t2_base]; omega)]
        exact hE j
      consistent := hC }
  have hstep : pureReplay (L.seed s₀).1 (L.seed s₀).2 maxLoop (ks ++ [u]) =
      pureEvict (L.seed s₀).1 (L.seed s₀).2 maxLoop T₀ ⟨u, ks.length⟩ := by
    rw [pureReplay_append_singleton, hT₀]
    rfl
  rw [StateTransitionSpec.wp_bind]
  refine StateTransitionSpec.wp_mono (fun ok s₄ t₄ ⟨hok, hW₄, hfr₄, hf₄, hc₄⟩ => ?_)
    (wp_evict (e := ⟨u, n⟩) maxLoop hW ⟨by simp [hlen], by simp [hlen]⟩)
  have hk₄ : L.SameKeys s₃ s₄ := SameKeys.of_frame (by omega) hfr₄
  have habs₄ : L.abs s₄ = L.abs s₃ := abs_congr (by omega) hfr₄
  simp only [StateTransitionSpec.wp_pure]
  refine ⟨by rw [hok, hstep, hlen], hR₃.congr hk₄ hf₄.ge, ?_, fun hfalse => ?_, hf₄, ?_⟩
  · rw [habs₄]
    simp only [abs, hseed, hks₃, hvs₃, hfresh]
    rw [dictOf_append (by simp [hlen, hn_def]) hu]
  · have hsome : (pureEvict (L.seed s₀).1 (L.seed s₀).2 maxLoop T₀ ⟨u, n⟩).isSome := by
      cases hev : (pureEvict (L.seed s₀).1 (L.seed s₀).2 maxLoop T₀ ⟨u, n⟩).isSome
      · rw [hok, hev] at hfalse
        exact absurd hfalse (by decide)
      · rfl
    obtain ⟨T', hT'⟩ := Option.isSome_iff_exists.mp hsome
    refine ⟨hR₃.congr hk₄ hf₄.ge, T', ?_, (hW₄ T' hT').encodes⟩
    rw [hk₄.seed_eq, hk₄.keyList_eq, hseed, hks₃, hstep, hlen]
    exact hT'
  · rw [hlen]
    omega

end Layout

end Cslib.DataStructure.Dictionary.CuckooHashing.Memory
