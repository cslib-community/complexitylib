/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleEndpointQuery
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.ExplicitBlockNetwork.Graph

/-!
# Root network endpoint keys from raw schedules

The root graph replaces each block edge by `copies` Boolean edges and subdivides each copy.
Its edge numbering lists all source halves, then all target halves. `query` reads the two
numbered endpoints of one such edge directly from its raw schedule, without constructing the
graph. Only a target half of a work-head block edge needs a schedule endpoint query.

The guard rejects malformed schedules and padded edge indices before edge-address decoding or
endpoint search. Valid exhaustion goes to the original edge's sink. In particular, no-work-head
machines retain their control edges, while zero intervals or zero copies have no valid edges.

`query_rows` agrees with the existing explicit graph's endpoint numbering, and
`query_explicitEdgeEquiv` identifies these keys with the actual subdivided network. These are
executable semantic bridges. Parsing, binary arithmetic, and native composition with the
schedule scanner still need their own charged machine implementation.
-/

public section

namespace Turing.MultiTapeTM.RootEndpointQuery

open MultiTapePTM

/-- A raw schedule, the number of Boolean copies of each block edge, and a numbered half-edge. -/
structure Input where
  /-- Input-first, two-bit row-major movement table. -/
  raw : List Bool
  /-- Boolean copies of each original block edge. -/
  copies : ℕ
  /-- Source halves precede target halves, as in `explicitEdgeEquiv`. -/
  edge : ℕ
  deriving DecidableEq

/-- The number of complete intervals in the raw word. Validation separately checks every row. -/
@[expose] def intervals (k : ℕ) (a : Input) : ℕ := a.raw.length / (2 * (k + 1))

/-- The actual edge universe of the subdivided, copied root graph. -/
@[expose] def edgeCount (k : ℕ) (a : Input) : ℕ :=
  2 * (intervals k a * (3 * k + 1) * a.copies)

/-- Only complete valid movement tables and genuine graph edges are admitted. -/
@[expose] def valid (k : ℕ) (a : Input) : Bool :=
  ScheduleBits.validate k a.raw && decide (a.edge < edgeCount k a)

/-- The root guard checks exactly the raw representation and the actual edge universe. -/
theorem valid_eq_true_iff (k : ℕ) (a : Input) :
    valid k a = true ↔ ScheduleBits.Canonical k a.raw ∧ a.edge < edgeCount k a := by
  simp [valid, ScheduleBits.validate_eq_true_iff]

/-- The target of an original block edge, using raw rows and the existing sink numbering.
This operation uses a supplied interval count; `query` validates that count and the edge first. -/
@[expose] def blockTarget (k q : ℕ) (raw : List Bool) (n : ℕ) : Option ℕ :=
  if n < q then some (if n + 1 < q then n + 1 else q + n)
  else (ScheduleEndpointQuery.query k ⟨raw, (n - q) % (k * 3), (n - q) / (k * 3)⟩).map
    (fun next => next.getD (q + n))

/-- Return the existing global vertex numbers of the row and subdivision-column endpoints.
The range guard runs before division by `copies` or any schedule query, including at zero copies. -/
@[expose] def query (k : ℕ) (a : Input) : Option (ℕ × ℕ) :=
  if valid k a then
    let q := intervals k a
    let half := q * (3 * k + 1) * a.copies
    let row := if a.edge < half then some (blockSrcNum k q (a.edge / a.copies))
      else blockTarget k q a.raw ((a.edge - half) / a.copies)
    row.map fun r => (r, explicitTgtNum k q a.copies a.edge)
  else none

/-- Rejected inputs cannot reach endpoint lookup. -/
theorem query_eq_none_of_not_valid (k : ℕ) (a : Input) (ha : valid k a = false) :
    query k a = none := by simp [query, ha]

/-- Padded indices are rejected, regardless of their numeric size or the raw table contents. -/
theorem query_eq_none_of_edgeCount_le (k : ℕ) (a : Input) (ha : edgeCount k a ≤ a.edge) :
    query k a = none :=
  query_eq_none_of_not_valid k a (by simp [valid, Nat.not_lt.mpr ha])

/-- There is no edge when the Boolean-copy count is zero. -/
@[simp] theorem query_zero_copies (k : ℕ) (raw : List Bool) (edge : ℕ) :
    query k ⟨raw, 0, edge⟩ = none := by simp [query, valid, edgeCount]

/-- An empty schedule has no graph edges. -/
@[simp] theorem query_empty (k copies edge : ℕ) :
    query k ⟨[], copies, edge⟩ = none := by simp [query, valid, edgeCount, intervals]

/-- The raw target lookup agrees with the numbered block-edge target on represented rows. -/
theorem blockTarget_rows {k q : ℕ} (σ n : ℕ) (hn : n < q * (3 * k + 1)) :
    blockTarget k q (ScheduleBits.rows (List.ofFn (scheduleOfNat k q σ))) n =
      some (edgeTargetNum k q σ n) := by
  obtain ⟨e, he⟩ := (blockEdgeEquiv k q).surjective ⟨n, hn⟩
  have hne : (blockEdgeEquiv k q e).val = n := congrArg Fin.val he
  rw [← hne]
  rcases e with i | ⟨i, h, d⟩
  · simp [blockTarget, edgeTargetNum, val_blockEdgeEquiv_inl, i.isLt]
  · obtain ⟨hdiv, hmod⟩ := blockEdge_div_mod i h d
    have hdmod : (d.val + 3 * h.val + k * 3 * i.val) % 3 = d.val := by
      rw [show d.val + 3 * h.val + k * 3 * i.val = d.val + 3 * (h.val + k * i.val) by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt d.isLt]
    have hddiv : (d.val + 3 * h.val) / 3 = h.val := by omega
    rw [val_blockEdgeEquiv_inr, blockTarget, ite_eq_right (by omega), edgeTargetNum,
      ite_eq_right (by omega), Nat.add_sub_cancel_left, hdiv, hmod, hdmod, hddiv]
    rw [show d.val + 3 * h.val = 3 * h.val + d.val by omega,
      ScheduleEndpointQuery.query_rows, firstAfterNum_eq]
    rfl

/-- On represented movement schedules, the query returns the existing explicit graph's
endpoint numbers for every genuine edge. No explicit endpoint list is supplied to the query. -/
theorem query_rows {k q copies : ℕ} (σ : ℕ)
    (edge : Fin (2 * (q * (3 * k + 1) * copies))) :
    query k ⟨ScheduleBits.rows (List.ofFn (scheduleOfNat k q σ)), copies, edge.val⟩ =
      some (explicitSrcNum k q copies σ edge.val, explicitTgtNum k q copies edge.val) := by
  have hq : intervals k
      ⟨ScheduleBits.rows (List.ofFn (scheduleOfNat k q σ)), copies, edge.val⟩ = q := by
    simp [intervals]
  have hv : valid k
      ⟨ScheduleBits.rows (List.ofFn (scheduleOfNat k q σ)), copies, edge.val⟩ = true := by
    simp [valid, edgeCount, hq, ScheduleBits.validate_rows, edge.isLt]
  have hm : 0 < copies := by
    by_contra hm
    have hm0 : copies = 0 := by omega
    have := edge.isLt
    simp [hm0] at this
  rw [query, hv]
  simp only [↓reduceIte, hq]
  split_ifs with hs
  · simp [explicitSrcNum, hs]
  · have hn : (edge.val - q * (3 * k + 1) * copies) / copies < q * (3 * k + 1) := by
      apply (Nat.div_lt_iff_lt_mul hm).mpr
      have := edge.isLt
      omega
    rw [blockTarget_rows σ _ hn]
    simp [explicitSrcNum, hs]

/-- Every admitted request has endpoints; valid exhaustion does not introduce rejection. -/
theorem query_isSome (k : ℕ) (a : Input) : (query k a).isSome = valid k a := by
  cases hv : valid k a with
  | false => simp [query_eq_none_of_not_valid k a hv]
  | true =>
    obtain ⟨hc, he⟩ := (valid_eq_true_iff k a).mp hv
    obtain ⟨rs, hr⟩ := hc.exists_rows
    let σ : Schedule k rs.length := fun i => rs[i.val]
    have hσ : List.ofFn σ = rs := List.ofFn_getElem
    have hraw : ScheduleBits.rows (List.ofFn σ) = a.raw := by rw [hσ]; exact hr
    let code := scheduleEquiv k rs.length σ
    have hcode : scheduleOfNat k rs.length code.val = σ := by
      rw [scheduleOfNat_eq_symm code.isLt]
      exact (scheduleEquiv k rs.length).symm_apply_apply σ
    have hi : intervals k a = rs.length := by
      simp [intervals, ← hr]
    have he' : a.edge < 2 * (rs.length * (3 * k + 1) * a.copies) := by
      simpa only [edgeCount, hi] using he
    have hq := query_rows code.val ⟨a.edge, he'⟩
    rw [hcode, hraw] at hq
    simp only [hq, Option.isSome_some]

/-- The returned keys are the endpoints of the actual copied and subdivided block network,
in its existing numbering. This is a semantic identity, not a native resource certificate. -/
theorem query_explicitEdgeEquiv {k q copies : ℕ} {State : Type}
    (machine : MultiTapePTM k Bool State) (input : List Bool) (b σ : ℕ)
    (code : BlockLetter k State b → Fin copies → Bool)
    (edge : (BlockEdge k q × Fin copies) ⊕ (BlockEdge k q × Fin copies)) :
    query k ⟨ScheduleBits.rows (List.ofFn (scheduleOfNat k q σ)), copies,
      (explicitEdgeEquiv k q copies edge).val⟩ =
      some ((explicitVertexEquiv k q copies
        (((machine.blockNetwork input b (scheduleOfNat k q σ)).binarize code).subdivide.src
          edge)).val,
        (explicitVertexEquiv k q copies
        (((machine.blockNetwork input b (scheduleOfNat k q σ)).binarize code).subdivide.tgt
          edge)).val) := by
  rw [query_rows, explicitSrcNum_explicitEdgeEquiv, explicitTgtNum_explicitEdgeEquiv]

end Turing.MultiTapeTM.RootEndpointQuery
