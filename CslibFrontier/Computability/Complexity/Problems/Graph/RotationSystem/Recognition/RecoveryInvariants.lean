/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.Recovery
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Size

/-!
# Finite invariants of candidate recovery

These invariants and storage bounds hold independently of a topological query criterion.
A failed search may return `none`; a returned table still passes the existing checker.
-/

public section

namespace Cslib.Complexity.Graph.RotationRecognition

open Turing.MultiTapeTM

/-- Remaining candidates are exactly unused darts of the original endpoint fiber. -/
theorem mem_remaining {I : FixedRotationInput} {v d : ℕ} {block : List ℕ} :
    d ∈ remaining I v block ↔ d ∈ fiber I.graph v ∧ d ∉ block := by
  simp only [remaining, List.mem_filter, Bool.not_eq_true', List.any_eq_false]
  aesop

/-- A successful first-candidate search retains the exact split-query guard. -/
theorem nextCandidate_some {I : FixedRotationInput} {v d : ℕ} {block : List ℕ}
    (h : nextCandidate I v block = some d) :
    d ∈ remaining I v block ∧ query (split I v (block ++ [d])) = true :=
  ⟨List.mem_of_find?_eq_some h,
    List.find?_some (p := fun d => query (split I v (block ++ [d]))) h⟩

/-- An extension either keeps a complete block or appends one unused, actually queried dart. -/
theorem advance_some {I : FixedRotationInput} {v : ℕ} {block result : List ℕ}
    (h : advance I v (some block) = some result) :
    (remaining I v block = [] ∧ result = block) ∨
      ∃ d, d ∈ remaining I v block ∧ query (split I v (block ++ [d])) = true ∧
        result = block ++ [d] := by
  unfold advance at h
  simp only [Option.elim_some] at h
  split at h
  · exact Or.inl ⟨List.isEmpty_iff.mp (by assumption), (Option.some.inj h).symm⟩
  · cases hc : nextCandidate I v block with
    | none => simp [hc] at h
    | some d =>
      simp only [hc, Option.elim_some] at h
      obtain ⟨hd, hq⟩ := nextCandidate_some hc
      exact Or.inr ⟨d, hd, hq, (Option.some.inj h).symm⟩

/-- Advancing preserves the finite endpoint fiber, duplicate freedom and directed prefix. -/
theorem advance_invariant {I : FixedRotationInput} {v : ℕ} {block result : List ℕ}
    (h : advance I v (some block) = some result) (hnd : block.Nodup)
    (hmem : ∀ d ∈ block, d ∈ fiber I.graph v) :
    result.Nodup ∧ (∀ d ∈ result, d ∈ fiber I.graph v) ∧
      block <+: result ∧ result.length ≤ block.length + 1 := by
  rcases advance_some h with ⟨_, rfl⟩ | ⟨d, hd, _, rfl⟩
  · exact ⟨hnd, hmem, List.prefix_refl _, by omega⟩
  · obtain ⟨hd, hnew⟩ := mem_remaining.mp hd
    refine ⟨?_, ?_, List.prefix_append _ _, by simp⟩
    · simpa using hnd.concat hnew
    · intro e he
      rcases List.mem_append.mp he with he | he
      · exact hmem e he
      · have : e = d := List.mem_singleton.mp he
        simpa only [this] using hd

/-- A successful recovered word uses at most the actual fiber length, with no repeated or invalid
binary dart index. This holds on malformed input too. -/
theorem recoverWord_invariant {I : FixedRotationInput} {v : ℕ} {word : List ℕ}
    (h : recoverWord I v = some word) :
    word.Nodup ∧ (∀ d ∈ word, d ∈ fiber I.graph v) ∧
      word.length ≤ (fiber I.graph v).length := by
  let darts := fiber I.graph v
  let initial := if darts.isEmpty then [] else [darts.headD 0]
  have hinit : initial.Nodup ∧ (∀ d ∈ initial, d ∈ darts) ∧ initial.length ≤ 1 := by
    dsimp only [initial]
    split
    · simp
    · rename_i hn
      have hne : darts ≠ [] := by simpa using hn
      cases hd : darts with
      | nil => exact False.elim (hne hd)
      | cons a rest => simp
  have step (i : ℕ) {w : List ℕ}
      (hi : (advance I v)^[i] (some initial) = some w) :
      w.Nodup ∧ (∀ d ∈ w, d ∈ darts) ∧ w.length ≤ initial.length + i := by
    induction i generalizing w with
    | zero =>
      have hw : initial = w := Option.some.inj hi
      subst w
      exact ⟨hinit.1, hinit.2.1, by omega⟩
    | succ i ih =>
      rw [Function.iterate_succ_apply'] at hi
      cases hx : (advance I v)^[i] (some initial) with
      | none => simp [hx, advance] at hi
      | some previous =>
        rw [hx] at hi
        obtain ⟨hn, hm, hl⟩ := ih hx
        obtain ⟨hn', hm', _, hl'⟩ := advance_invariant hi hn hm
        exact ⟨hn', hm', by omega⟩
  have hstep := step (darts.length - 1) h
  refine ⟨hstep.1, hstep.2.1, ?_⟩
  change word.length ≤ darts.length
  change (advance I v)^[darts.length - 1] (some initial) = some word at h
  by_cases hd : darts = []
  · have hz : (advance I v)^[darts.length - 1] (some initial) = some [] := by
      simp [hd, initial]
    rw [hz] at h
    have : word = [] := (Option.some.inj h).symm
    simp [this]
  · have hp : 0 < darts.length := List.length_pos_iff.mpr hd
    omega

/-- Every successful word enumerates its entire original endpoint fiber. -/
theorem recoverWord_enumerates {I : FixedRotationInput} {v : ℕ} {word : List ℕ}
    (h : recoverWord I v = some word) :
    word.Nodup ∧ ∀ d, d ∈ word ↔ d ∈ fiber I.graph v := by
  let darts := fiber I.graph v
  let initial := if darts.isEmpty then [] else [darts.headD 0]
  have hinit : initial.Nodup ∧ (∀ d ∈ initial, d ∈ darts) := by
    dsimp only [initial]
    split
    · simp
    · rename_i hn
      have hne : darts ≠ [] := by simpa using hn
      cases hd : darts with
      | nil => exact False.elim (hne hd)
      | cons a rest => simp
  have step (i : ℕ) {w : List ℕ}
      (hi : (advance I v)^[i] (some initial) = some w) :
      w.Nodup ∧ (∀ d ∈ w, d ∈ darts) ∧ min darts.length (initial.length + i) ≤ w.length := by
    induction i generalizing w with
    | zero =>
      have hw := Option.some.inj hi
      subst w
      exact ⟨hinit.1, hinit.2, by omega⟩
    | succ i ih =>
      rw [Function.iterate_succ_apply'] at hi
      cases hx : (advance I v)^[i] (some initial) with
      | none => simp [hx, advance] at hi
      | some previous =>
        rw [hx] at hi
        obtain ⟨hn, hm, hl⟩ := ih hx
        obtain ⟨hn', hm', _, _⟩ := advance_invariant hi hn hm
        refine ⟨hn', hm', ?_⟩
        rcases advance_some hi with ⟨he, hw⟩ | ⟨d, _, _, hw⟩
        · subst w
          have hsub : darts ⊆ previous := by
            intro d hd
            by_contra hnot
            have : d ∈ remaining I v previous := mem_remaining.mpr ⟨hd, hnot⟩
            rw [he] at this
            contradiction
          exact (Nat.min_le_left _ _).trans ((nodup_fiber I.graph v).length_le_of_subset hsub)
        · rw [hw, List.length_append, List.length_singleton]
          omega
  have hstep := step (darts.length - 1) h
  obtain ⟨hn, hm, hu⟩ := recoverWord_invariant h
  change word.length ≤ darts.length at hu
  have heq : word.length = darts.length := by
    by_cases hd : darts = []
    · simp only [hd, List.length_nil] at hu ⊢
      exact Nat.eq_zero_of_le_zero hu
    · have hp : 0 < darts.length := List.length_pos_iff.mpr hd
      have hlen : initial.length = 1 := by simp [initial, List.isEmpty_iff, hd]
      rw [hlen] at hstep
      omega
  have hsub : word.toFinset ⊆ darts.toFinset := by
    intro d hd
    exact List.mem_toFinset.mpr (hm d (List.mem_toFinset.mp hd))
  have hcard : darts.toFinset.card ≤ word.toFinset.card := by
    rw [List.toFinset_card_of_nodup (nodup_fiber I.graph v), List.toFinset_card_of_nodup hn]
    exact heq.ge
  have hset := Finset.eq_of_subset_of_card_le hsub hcard
  have hreverse : darts ⊆ word := by
    intro d hd
    apply List.mem_toFinset.mp
    rw [hset]
    exact List.mem_toFinset.mpr hd
  exact ⟨hn, fun d => ⟨hm d, fun hd => hreverse hd⟩⟩

/-- Explicit polynomial storage for a recovered binary dart word, including its list framing. -/
theorem length_enc_recoverWord {I : FixedRotationInput} {v : ℕ} {word : List ℕ}
    (h : recoverWord I v = some word) :
    (encList encNat word).length ≤ 2 * I.graph.2.length * (4 * I.graph.2.length + 1) := by
  obtain ⟨_, hm, hl⟩ := recoverWord_invariant h
  have hw := hl.trans (length_fiber_le I.graph v)
  have hb : ∀ d ∈ word, (encNat d).length ≤ 2 * I.graph.2.length := by
    intro d hd
    have hlt := (mem_fiber.mp (hm d hd)).1
    rw [encNat_apply, Nat.size_eq_bits_len]
    exact (Nat.size_le_self _).trans hlt.le
  exact (length_encList_le encNat word hb).trans (by nlinarith)

/-- A raw block step grows storage by at most one bounded dart. Failure discards the block.
The bound applies to every accumulator, including malformed or oversized blocks. -/
theorem length_enc_advance (I : FixedRotationInput) (v : ℕ) (state : Option (List ℕ)) :
    (encOption (encList encNat) (advance I v state)).length ≤
      (encOption (encList encNat) state).length + 4 * I.graph.2.length + 1 := by
  cases state with
  | none => simp [advance]
  | some block =>
    cases hs : advance I v (some block) with
    | none => simp
    | some result =>
      rcases advance_some hs with ⟨_, rfl⟩ | ⟨d, hd, _, rfl⟩
      · omega
      · have hlt := (mem_fiber.mp (mem_remaining.mp hd).1).1
        have hb : (encNat d).length ≤ 2 * I.graph.2.length := by
          rw [encNat_apply, Nat.size_eq_bits_len]
          exact (Nat.size_le_self _).trans hlt.le
        simp only [encOption_some, List.length_cons, length_encList, List.map_append,
          List.sum_append, List.map_singleton, List.sum_singleton]
        omega

/-- Prescribing an order keeps the original graph unchanged. -/
@[simp] theorem graph_prescribe (I : FixedRotationInput) (v : ℕ) (word : List ℕ) :
    (prescribe I v word).graph = I.graph := rfl

/-- Prescribing a vertex replaces an entry; it never appends to the original order table. -/
@[simp] theorem length_prescribe_orders (I : FixedRotationInput) (v : ℕ) (word : List ℕ) :
    (prescribe I v word).orders.length = I.orders.length := by simp [prescribe]

/-- A coarse all-raw storage bound for replacing one order. Counting every table entry makes
this bound independent of validity and of the numerical value of the supplied vertex index. -/
theorem length_enc_prescribe_le (I : FixedRotationInput) (v : ℕ) (word : List ℕ) :
    (encFixedRotationInput (prescribe I v word)).length ≤ (encFixedRotationInput I).length +
      I.orders.length * (2 * ((encList encNat word).length + 1)) := by
  let size (order : Option (List ℕ)) := 2 * (encOption (encList encNat) order).length + 1
  have hs : ∀ entry ∈ I.orders.zipIdx,
      size (if entry.2 = v then some word else entry.1) ≤
        size entry.1 + 2 * ((encList encNat word).length + 1) := by
    intro entry _
    split <;> simp only [size, encOption_some, List.length_cons] <;> omega
  have hbase : (I.orders.zipIdx.map fun entry => size entry.1).sum =
      (I.orders.map size).sum := by
    change (I.orders.zipIdx.map (size ∘ Prod.fst)).sum = _
    rw [← List.map_map, List.zipIdx_map_fst]
  have hsum := List.sum_le_sum hs
  simp only [List.sum_map_add, hbase, List.map_const', List.sum_const_nat,
    List.length_zipIdx] at hsum
  simp only [encFixedRotationInput_apply, encFixedRotationInputFields, length_encPair,
    prescribe, length_encList, List.map_map]
  simpa only [Nat.add_assoc, Function.comp_def, size, length_encList] using
    Nat.add_le_add_left hsum (2 * (encGraph I.graph).length + 1)

/-- A successful outer step retains the original graph/table width and adds only bounded
word storage. The statement is unconditional on raw input and algebraic completeness. -/
theorem completeVertex_some {I J : FixedRotationInput} {v : ℕ}
    (h : completeVertex (some I) v = some J) :
    J.graph = I.graph ∧ J.orders.length = I.orders.length ∧
      (encFixedRotationInput J).length ≤ (encFixedRotationInput I).length + I.orders.length *
        (2 * (2 * I.graph.2.length * (4 * I.graph.2.length + 1) + 1)) := by
  unfold completeVertex at h
  simp only [Option.elim_some] at h
  split at h
  · have hj := Option.some.inj h
    subst J
    exact ⟨rfl, rfl, Nat.le_add_right _ _⟩
  · cases hw : recoverWord I v with
    | none => simp [hw] at h
    | some word =>
      simp only [hw, Option.elim_some] at h
      have hj := Option.some.inj h
      subst J
      refine ⟨rfl, length_prescribe_orders .., (length_enc_prescribe_le I v word).trans ?_⟩
      apply Nat.add_le_add_left
      apply Nat.mul_le_mul_left
      exact Nat.mul_le_mul_left 2 (Nat.add_le_add_right (length_enc_recoverWord hw) 1)

/-- One outer step's explicit all-raw encoded-storage growth budget. -/
@[expose] def outerGrowth (I : FixedRotationInput) : ℕ :=
  I.orders.length * (2 * (2 * I.graph.2.length * (4 * I.graph.2.length + 1) + 1))

/-- Every finite prefix of the outer fold retains the original graph and order width, with
only polynomial storage growth. No query histories or split graphs are retained. -/
theorem completeVertex_fold (I : FixedRotationInput) (vertices : List ℕ) :
    vertices.foldl completeVertex (some I) = none ∨
      ∃ J, vertices.foldl completeVertex (some I) = some J ∧ J.graph = I.graph ∧
        J.orders.length = I.orders.length ∧
        (encFixedRotationInput J).length + 1 ≤ (encFixedRotationInput I).length + 1 +
          vertices.length * outerGrowth I := by
  induction vertices using List.reverseRecOn with
  | nil => exact Or.inr ⟨I, rfl, rfl, rfl, by simp⟩
  | append_singleton vertices v ih =>
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    rcases ih with hn | ⟨J, hj, hg, hl, hb⟩
    · rw [hn]
      exact Or.inl rfl
    · rw [hj]
      cases hx : completeVertex (some J) v with
      | none => exact Or.inl rfl
      | some K =>
        obtain ⟨hkg, hkl, hkb⟩ := completeVertex_some hx
        refine Or.inr ⟨K, rfl, hkg.trans hg, hkl.trans hl, ?_⟩
        have hb' : (encFixedRotationInput K).length ≤ (encFixedRotationInput J).length +
            outerGrowth I := by simpa only [outerGrowth, hg, hl] using hkb
        simp only [List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul]
        omega

/-- All original graph edges, including loops and parallel records, are unchanged by successful
order recovery. Its table width is unchanged even on malformed input. -/
theorem recoverOrders_some {I J : FixedRotationInput} (h : recoverOrders I = some J) :
    J.graph = I.graph ∧ J.orders.length = I.orders.length := by
  rcases completeVertex_fold I (List.range I.graph.1.length) with hn | ⟨K, hk, hg, hl, _⟩
  · rw [← recoverOrders] at hn
    rw [h] at hn
    contradiction
  · change recoverOrders I = some K at hk
    rw [h] at hk
    have : J = K := Option.some.inj hk
    exact this ▸ ⟨hg, hl⟩

/-- Replacing one entry leaves every other vertex's order unchanged. -/
theorem getD_prescribe_other (I : FixedRotationInput) (v u : ℕ) (word : List ℕ) (huv : u ≠ v) :
    (prescribe I v word).orders.getD u none = I.orders.getD u none := by
  by_cases hu : u < I.orders.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hu), List.getD_eq_getElem _ _ hu]
    simp only [prescribe, List.getElem_map, List.getElem_zipIdx, Nat.zero_add,
      huv, ↓reduceIte]
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hu),
      List.getD_eq_default _ _ (Nat.le_of_not_gt hu)]

/-- Every originally prescribed complete word remains literally unchanged. -/
@[expose] def PreservesOrders (original current : FixedRotationInput) : Prop :=
  ∀ v word, original.orders.getD v none = some word → current.orders.getD v none = some word

/-- Completing a free vertex preserves all already prescribed words on every raw input. -/
theorem completeVertex_preserves {I J : FixedRotationInput} {v : ℕ}
    (h : completeVertex (some I) v = some J) : PreservesOrders I J := by
  intro u word hu
  unfold completeVertex at h
  simp only [Option.elim_some] at h
  split at h
  · have hj := Option.some.inj h
    subst J
    exact hu
  · rename_i hfree
    have huv : u ≠ v := by
      rintro rfl
      simp only [hu, Option.isSome_some, not_true_eq_false] at hfree
    cases hw : recoverWord I v with
    | none => simp [hw] at h
    | some w =>
      simp only [hw, Option.elim_some] at h
      have hj := Option.some.inj h
      subst J
      rw [getD_prescribe_other I v u w huv]
      exact hu

/-- Full-order table guard implies the literal `Realizes` equations on the decoded rotation. -/
theorem verifyFixed_realizes {I : FixedRotationInput} {c : RotationCertificate}
    (hrot : RotationCertificate.verifyRotation I.graph c = true)
    (hfixed : verifyFixed I c = true) :
    Realizes I (RotationCertificate.decode I.graph c hrot) := by
  intro v word hv i hi d hd
  have hvlt : v < I.orders.length := by
    by_contra h
    rw [List.getD_eq_default _ _ (by omega)] at hv
    contradiction
  have hmem : some word ∈ I.orders := by
    rw [List.getD_eq_getElem _ _ hvlt] at hv
    rw [← hv]
    exact List.getElem_mem hvlt
  have hword := (List.all_eq_true.mp hfixed) _ hmem
  have hentry : (word.getD i 0, i) ∈ word.zipIdx := by
    apply List.mem_zipIdx_iff_getElem?.mpr
    rw [List.getD_eq_getElem _ _ hi]
    simp
  have hsucc := List.all_eq_true.mp hword _ hentry
  rw [RotationCertificate.index_decode_rotate hrot, hd]
  exact of_decide_eq_true hsucc

/-- A returned table has exactly one successor per original dart. -/
theorem length_recover_successor {I : FixedRotationInput} {c : RotationCertificate}
    (h : recover I = some c) : c.successor.length = 2 * I.graph.2.length := by
  unfold recover at h
  split at h
  · cases hx : recoverOrders I with
    | none => simp [hx] at h
    | some J =>
      simp only [hx, Option.elim_some] at h
      split at h
      · have hc := Option.some.inj h
        subst c
        rw [length_certificate, (recoverOrders_some hx).1]
      · contradiction
  · contradiction

/-- A returned successor is an actual original dart index, even on raw malformed input. -/
theorem mem_recover_successor_lt {I : FixedRotationInput} {c : RotationCertificate}
    (h : recover I = some c) {d : ℕ} (hd : d ∈ c.successor) : d < 2 * I.graph.2.length := by
  have hlen := length_recover_successor h
  obtain ⟨hrot, _⟩ := (RotationCertificate.verifyGenusZero_eq_true_iff _ _).mp (recover_sound h).1
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
  let dart := (Dart.indexEquiv I.graph).symm ⟨i.val, by omega⟩
  have hidx : dart.index = i.val := congrArg Fin.val
    ((Dart.indexEquiv I.graph).apply_symm_apply ⟨i.val, by omega⟩)
  have hvalue := RotationCertificate.index_decode_rotate hrot dart
  rw [hidx, List.getD_eq_getElem _ _ i.isLt] at hvalue
  have hget : c.successor[i.val] = d := by simpa only [List.get_eq_getElem] using hi
  rw [hget] at hvalue
  rw [← hvalue]
  exact (Dart.indexEquiv I.graph _).isLt

/-- Full framed binary storage of a returned existing certificate is explicitly quadratic in
the original edge count. No trace or query system is included in the output. -/
theorem length_enc_recover_le {I : FixedRotationInput} {c : RotationCertificate}
    (h : recover I = some c) :
    (encRotationCertificate c).length ≤ 2 * I.graph.2.length * (4 * I.graph.2.length + 1) := by
  have hbits : ∀ d ∈ c.successor, (encNat d).length ≤ 2 * I.graph.2.length := by
    intro d hd
    rw [encNat_apply, Nat.size_eq_bits_len]
    exact (Nat.size_le_self _).trans (mem_recover_successor_lt h hd).le
  have hb := length_encList_le encNat c.successor hbits
  rw [length_recover_successor h] at hb
  change (encList encNat c.successor).length ≤ _
  exact hb.trans (by nlinarith)

/-- Successful candidate recovery supplies the existing numerical feasibility predicate,
without requiring the missing algebraic completeness criterion. -/
theorem recover_feasible {I : FixedRotationInput} {c : RotationCertificate}
    (h : recover I = some c) : Feasible I := by
  obtain ⟨hg, hf⟩ := recover_sound h
  obtain ⟨hrot, hn⟩ := (RotationCertificate.verifyGenusZero_eq_true_iff _ _).mp hg
  exact ⟨RotationCertificate.decode I.graph c hrot, hn, verifyFixed_realizes hrot hf⟩

end Cslib.Complexity.Graph.RotationRecognition
