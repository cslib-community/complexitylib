/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.MatrixMultiplication.Schonhage.Full
public import Mathlib.Data.Multiset.Bind
public import Mathlib.Data.Finset.Piecewise

/-!
# Pruned tensor evaluation and the calls it makes

The recursion skips children with no requested output strings, reading only precomputed
leaf encodings. Its values agree with the full recursion on the requested set and vanish
elsewhere. A call trace records finite recursive calls and passed sets; it is not a machine
execution or an instruction counter.

The root is always called. At depth zero with an empty request set it is itself a visited
leaf, although the set of contributing leaves is empty. The leaf characterization therefore
requires positive depth or a nonempty request set. The value and total-set-size statements
hold without that qualification.

## Main definitions

* `Pruned.run`, `Pruned.result`, `Pruned.calls`: pruned evaluation and its call trace.
* `Pruned.Visits`, `Pruned.totalSize`: visited leaves and total size of passed sets.
* `computeEncoding`: recursive computation of either input encoding.

## Main results

* `Pruned.result_eq_piecewise_full`: agreement on requested strings and zero elsewhere.
* `Pruned.visits_iff_mem_leaves`: exact visited-leaf characterization with the root exception.
* `Pruned.totalSize_le`: passed-set total bounded by depth plus one times leaf count.
* `pruned_spec`: all three properties together for the two input encodings.

## References

Part of [AlmanWilliams2026, Section 2]. Direct mathematical adaptation of
[Anthropic's pinned formal source](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec2).
Definitions are selectively extracted from that pin's `PaperStatements.lean`; no machine
semantics or running-time statement is imported. The docstrings below explain the local
declarations in our own words.
-/

@[expose] public section

open Finset

namespace Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Retain the tails of requested tuples whose first coordinate equals `z`. -/
def sliceSet {n : ℕ} (S : Finset (OutStr (n + 1))) (z : OutVar) : Finset (OutStr n) :=
  univ.filter fun w' => (Fin.cons z w' : OutStr (n + 1)) ∈ S

/-- The requests for a child label are the union of slices for output coordinates to which that
label contributes.
-/
def childSet {n : ℕ} (S : Finset (OutStr (n + 1))) (lam : Term) : Finset (OutStr n) :=
  (univ.filter fun z => lam.Contributes z).biUnion fun z => sliceSet S z

/-- One mathematical call record, pairing its label-sequence position with the request set
supplied there. The dependent pairs retain the two tuple lengths.
-/
structure PrunedCall where
  /-- The call depth and the terms identifying its vertex.
-/
  vertex : Σ k, Vertex k
  /-- The remaining string length and requested output strings.
-/
  passed : Σ n, Finset (OutStr n)

/-- Embed a child call into its parent by prepending the child label to its recorded vertex. -/
def PrunedCall.under (lam : Term) (c : PrunedCall) : PrunedCall where
  vertex := ⟨c.vertex.1 + 1, (Fin.cons lam c.vertex.2 : Vertex (c.vertex.1 + 1))⟩
  passed := c.passed

/-- Evaluate requested outputs from the two supplied leaf-encoding arrays. For each term, form its
child request set and recurse only when that set is nonempty. Decode the child values and set
unrequested outputs to zero. The second component records recursive calls and their requested sets
as a multiset. Each child receives the corresponding slices of the encoding arrays. The root call
is always recorded, including at depth zero with an empty request set. These are mathematical
values and call records, without a native execution cost.
-/
def Pruned.run : (n : ℕ) → (Leaf n → ℤ) → (Leaf n → ℤ) → Finset (OutStr n) →
    (OutStr n → ℤ) × Multiset PrunedCall
  | 0, encA, encB, S =>
    (S.piecewise (fun _ => encA Fin.elim0 * encB Fin.elim0) 0, {⟨⟨0, Fin.elim0⟩, ⟨0, S⟩⟩})
  | n + 1, encA, encB, S =>
    let R : Term → (OutStr n → ℤ) × Multiset PrunedCall := fun lam =>
      if (childSet S lam).Nonempty then
        Pruned.run n (sliceAt encA lam) (sliceAt encB lam) (childSet S lam)
      else (0, 0)
    (S.piecewise (fun w =>
        match w 0 with
        | .z i j => (R (.P i j)).1 (Fin.tail w)
        | .z0 => ∑ lam, (R lam).1 (Fin.tail w)) 0,
      ⟨⟨0, Fin.elim0⟩, ⟨n + 1, S⟩⟩ ::ₘ
        univ.val.bind fun lam => ((R lam).2).map (PrunedCall.under lam))

/-- Project the output values from the pruned recursion and discard the call multiset. -/
def Pruned.result (n : ℕ) (encA encB : Leaf n → ℤ) (S : Finset (OutStr n)) : OutStr n → ℤ :=
  (Pruned.run n encA encB S).1

/-- Project the multiset of call records, retaining repetitions and the root record. -/
def Pruned.calls (n : ℕ) (encA encB : Leaf n → ℤ) (S : Finset (OutStr n)) : Multiset PrunedCall :=
  (Pruned.run n encA encB S).2

/-- A leaf is visited when some recorded call has that full-depth vertex. -/
def Pruned.Visits {L : ℕ} (encA encB : Leaf L → ℤ) (U : Finset (OutStr L)) (τ : Leaf L) : Prop :=
  ∃ c ∈ Pruned.calls L encA encB U, c.vertex = ⟨L, τ⟩

/-- Add the cardinalities of the request sets carried by all call records, with multiplicity. -/
def Pruned.totalSize {L : ℕ} (encA encB : Leaf L → ℤ) (U : Finset (OutStr L)) : ℕ :=
  ((Pruned.calls L encA encB U).map fun c => c.passed.2.card).sum

/-- Choose the private label at every output coordinate. The resulting leaf is relevant to that
output tuple and distinguishes it from every other output tuple.
-/
def privateLeaf {L : ℕ} (w : OutStr L) : Leaf L := fun ℓ => (w ℓ).privateTerm

/-! ### Section 2.4.1: the encodings -/

/-- Recursively apply the coefficient family `c` along a term string. Each level replaces the
input array by a weighted sum of its first-letter slices; depth zero returns its unique entry.
Choosing `phi` or `psi` computes the corresponding shared input encoding.
-/
def computeEncoding {α : Type} [Fintype α] (c : Term → α → ℤ) :
    (L : ℕ) → ((Fin L → α) → ℤ) → Leaf L → ℤ
  | 0, a, _ => a Fin.elim0
  | L + 1, a, τ => computeEncoding c L (fun u' => ∑ s, c (τ 0) s * sliceAt a s u') (Fin.tail τ)

/-- Recursive encoding agrees with the closed coefficient-product formula `encodeWith`. -/
theorem computeEncoding_eq_encodeWith {α : Type} [Fintype α] (c : Term → α → ℤ) {L : ℕ}
    (a : (Fin L → α) → ℤ) (τ : Leaf L) : computeEncoding c L a τ = encodeWith c τ a := by
  induction L with
  | zero => rw [computeEncoding, encodeWith_zero]
  | succ n ih => rw [computeEncoding, ih, ← encodeWith_cons, Fin.cons_self_tail]

/-- Specializing recursive encoding to `phi` gives the existing left-encoding array. -/
theorem computeEncoding_phi {L : ℕ} (a : LeftStr L → ℤ) : computeEncoding phi L a = encodingL a :=
  funext (computeEncoding_eq_encodeWith phi a)

/-- Specializing recursive encoding to `psi` gives the existing right-encoding array. -/
theorem computeEncoding_psi {L : ℕ} (b : RightStr L → ℤ) : computeEncoding psi L b = encodingR b :=
  funext (computeEncoding_eq_encodeWith psi b)

/-! ### Section 2.4.2: the sets `S_λ` of step (2) -/

/-- Membership in a slice of a set of output strings.
-/
@[simp]
theorem mem_sliceSet {n : ℕ} (S : Finset (OutStr (n + 1))) (z : OutVar) (w' : OutStr n) :
    w' ∈ sliceSet S z ↔ (Fin.cons z w' : OutStr (n + 1)) ∈ S := by
  simp [sliceSet]

/-- An indexed child combines the matching outer slice with the inner slice of the request set. -/
theorem childSet_P {n : ℕ} (S : Finset (OutStr (n + 1))) (i j : Fin 3) :
    childSet S (.P i j) = sliceSet S (.z i j) ∪ sliceSet S .z0 := by
  have hz : (univ.filter fun z => (Term.P i j).Contributes z) = {.z i j, .z0} := by
    decide +revert
  rw [childSet, hz, biUnion_insert, singleton_biUnion]

/-- The distinguished child needs only the inner slice of the request set. -/
theorem childSet_P0 {n : ℕ} (S : Finset (OutStr (n + 1))) :
    childSet S .P0 = sliceSet S .z0 := by
  have hz : (univ.filter fun z => Term.P0.Contributes z) = {.z0} := by decide
  rw [childSet, hz, singleton_biUnion]

/-- Every requested suffix in a relevant output slice belongs to the corresponding child request
set.
-/
theorem sliceSet_subset_childSet {n : ℕ} (S : Finset (OutStr (n + 1))) {lam : Term} {z : OutVar}
    (h : lam.Contributes z) : sliceSet S z ⊆ childSet S lam :=
  subset_biUnion_of_mem (fun z => sliceSet S z) (mem_filter.mpr ⟨mem_univ z, h⟩)

/-- A suffix belongs to a child request set precisely when it comes from a requested parent tuple
whose leading coordinate is relevant to that child label.
-/
theorem mem_childSet {n : ℕ} {S : Finset (OutStr (n + 1))} {lam : Term} {w' : OutStr n} :
    w' ∈ childSet S lam ↔ ∃ w ∈ S, lam.Contributes (w 0) ∧ Fin.tail w = w' := by
  simp only [childSet, mem_biUnion, mem_filter, mem_univ, true_and, mem_sliceSet]
  constructor
  · rintro ⟨z, hz, hw⟩
    exact ⟨_, hw, by simpa using hz, by simp⟩
  · rintro ⟨w, hw, hz, rfl⟩
    exact ⟨w 0, hz, by rwa [Fin.cons_self_tail]⟩

/-! ### Lemma 10, first claim: the values -/

/-- Evaluate a child on its requested suffixes, using the zero array when that child has no
requests.
-/
def Pruned.childResult {n : ℕ} (encA encB : Leaf (n + 1) → ℤ) (S : Finset (OutStr (n + 1)))
    (lam : Term) : OutStr n → ℤ :=
  if (childSet S lam).Nonempty then
    Pruned.result n (sliceAt encA lam) (sliceAt encB lam) (childSet S lam)
  else 0

/-- Unfold the pruned values once, exposing the child arrays used for decoding. -/
theorem Pruned.result_succ {n : ℕ} (encA encB : Leaf (n + 1) → ℤ) (S : Finset (OutStr (n + 1))) :
    Pruned.result (n + 1) encA encB S = S.piecewise (fun w =>
      match w 0 with
      | .z i j => Pruned.childResult encA encB S (.P i j) (Fin.tail w)
      | .z0 => ∑ lam, Pruned.childResult encA encB S lam (Fin.tail w)) 0 := by
  simp only [Pruned.result, Pruned.run, Pruned.childResult, apply_ite Prod.fst]

/-- At a requested tuple, decoding sums child values at its tail over labels relevant to its
leading coordinate; every unrequested tuple has value zero.
-/
theorem Pruned.result_succ_apply {n : ℕ} (encA encB : Leaf (n + 1) → ℤ)
    (S : Finset (OutStr (n + 1))) (w : OutStr (n + 1)) :
    Pruned.result (n + 1) encA encB S w = if w ∈ S then
      ∑ lam : Term with lam.Contributes (w 0), Pruned.childResult encA encB S lam (Fin.tail w)
    else 0 := by
  rw [Pruned.result_succ, Finset.piecewise, Term.sum_contributes]
  rfl

/-- For arbitrary supplied leaf arrays, the pruned result is zero off the request set and is a sum
of relevant leaf products on that set.
-/
theorem Pruned.result_eq_piecewise_sum {n : ℕ} (encA encB : Leaf n → ℤ) (S : Finset (OutStr n)) :
    Pruned.result n encA encB S
      = S.piecewise (fun w => ∑ τ : Leaf n with Leaf.Contributes τ w, encA τ * encB τ) 0 := by
  induction n with
  | zero =>
    -- The only leaf is the empty string, and it contributes to the empty output string.
    have hleaf (w : OutStr 0) :
        (univ.filter fun τ : Leaf 0 => Leaf.Contributes τ w) = {Fin.elim0} :=
      eq_singleton_iff_unique_mem.mpr
        ⟨mem_filter.mpr ⟨mem_univ _, fun ℓ => ℓ.elim0⟩, fun _ _ => Subsingleton.elim _ _⟩
    simp only [Pruned.result, Pruned.run, hleaf, sum_singleton]
  | succ n ih =>
    -- The induction hypothesis describes each `C_λ`, also when `S_λ = ∅`.
    have hC (lam : Term) : Pruned.childResult encA encB S lam
        = (childSet S lam).piecewise (fun w' =>
          ∑ τ' : Leaf n with Leaf.Contributes τ' w',
            encA (Fin.cons lam τ') * encB (Fin.cons lam τ')) 0 := by
      unfold Pruned.childResult
      split_ifs with hne
      · exact ih _ _ _
      · rw [not_nonempty_iff_eq_empty.mp hne, Finset.piecewise_empty]
    -- Step (4) reads `C_λ` only at strings of `S_λ`, and a leaf is its first term and the rest.
    funext w
    rw [Pruned.result_succ_apply, Finset.piecewise, Leaf.sum_contributes_succ]
    split_ifs with hw
    · refine sum_congr rfl fun lam hlam => ?_
      have hmem : Fin.tail w ∈ childSet S lam :=
        mem_childSet.mpr ⟨w, hw, (mem_filter.mp hlam).2, rfl⟩
      rw [hC, Finset.piecewise_eq_of_mem _ _ _ hmem]
    · rfl

/-- Pruning the two input encodings yields `bilinearProduct` on the requested strings and zero
elsewhere.
-/
theorem Pruned.result_eq_piecewise_bilinearProduct {L : ℕ} (a : LeftStr L → ℤ)
    (b : RightStr L → ℤ) (U : Finset (OutStr L)) :
    Pruned.result L (encodingL a) (encodingR b) U = U.piecewise (bilinearProduct a b) 0 :=
  -- Sum the products of the encoded numbers over the contributing leaves.
  Pruned.result_eq_piecewise_sum _ _ U

/-- Pruning precomputed input encodings agrees with full evaluation at every requested string and
is zero elsewhere.
-/
theorem Pruned.result_eq_piecewise_full {n : ℕ} (a : LeftStr n → ℤ) (b : RightStr n → ℤ)
    (S : Finset (OutStr n)) :
    Pruned.result n (encodingL a) (encodingR b) S = S.piecewise (Full.result n a b) 0 := by
  rw [Pruned.result_eq_piecewise_bilinearProduct, Full.result_eq_bilinearProduct]

/-! ### Lemma 10, second claim: the calls that are made and the sets passed to them -/

/-- Test relevance for an initial label sequence against the matching prefix of an output tuple.
Longer label sequences fail the depth condition.
-/
def Vertex.Contributes {k L : ℕ} (τ : Vertex k) (w : OutStr L) : Prop :=
  ∀ (ℓ : Fin k) (h : (ℓ : ℕ) < L), (τ ℓ).Contributes (w ⟨ℓ, h⟩)

/-- At full depth, vertex relevance coincides with the existing leaf-relevance predicate. -/
theorem Vertex.contributes_iff_leaf {L : ℕ} (τ : Leaf L) (w : OutStr L) :
    Vertex.Contributes τ w ↔ Leaf.Contributes τ w :=
  ⟨fun h ℓ => h ℓ ℓ.2, fun h ℓ _ => h ℓ⟩

/-- Decompose relevance of a nonempty vertex into relevance of its head and relevance of its
tail.
-/
theorem Vertex.contributes_cons {k L : ℕ} {lam : Term} {τ : Vertex k} {w : OutStr (L + 1)} :
    Vertex.Contributes (Fin.cons lam τ : Vertex (k + 1)) w
      ↔ lam.Contributes (w 0) ∧ Vertex.Contributes τ (Fin.tail w) := by
  constructor
  · intro h
    exact ⟨h 0 (Nat.succ_pos L), fun ℓ hℓ => h ℓ.succ (Nat.succ_lt_succ hℓ)⟩
  · rintro ⟨h0, h1⟩ ℓ h
    induction ℓ using Fin.cases with
    | zero => exact h0
    | succ i => exact h1 i (Nat.lt_of_succ_lt_succ h)

/-- Obtain a child call multiset from its recursion, or the empty multiset when its request set is
empty.
-/
def Pruned.childCalls {n : ℕ} (encA encB : Leaf (n + 1) → ℤ) (S : Finset (OutStr (n + 1)))
    (lam : Term) : Multiset PrunedCall :=
  if (childSet S lam).Nonempty then
    Pruned.calls n (sliceAt encA lam) (sliceAt encB lam) (childSet S lam)
  else 0

/-- Unfold call recording into the parent record and the embedded records from nonempty children. -/
theorem Pruned.calls_succ {n : ℕ} (encA encB : Leaf (n + 1) → ℤ) (S : Finset (OutStr (n + 1))) :
    Pruned.calls (n + 1) encA encB S = ⟨⟨0, Fin.elim0⟩, ⟨n + 1, S⟩⟩ ::ₘ
      univ.val.bind fun lam => (Pruned.childCalls encA encB S lam).map (.under lam) := by
  simp only [Pruned.calls, Pruned.run, Pruned.childCalls, apply_ite Prod.snd]

/-- Membership in the positive-depth call multiset means being the root record or an embedded call
of some nonempty child.
-/
theorem Pruned.mem_calls_succ {n : ℕ} {encA encB : Leaf (n + 1) → ℤ}
    {S : Finset (OutStr (n + 1))} {c : PrunedCall} :
    c ∈ Pruned.calls (n + 1) encA encB S ↔
      c = ⟨⟨0, Fin.elim0⟩, ⟨n + 1, S⟩⟩
        ∨ ∃ lam : Term, (childSet S lam).Nonempty
            ∧ ∃ c' ∈ Pruned.calls n (sliceAt encA lam) (sliceAt encB lam) (childSet S lam),
                c = c'.under lam := by
  rw [Pruned.calls_succ, Multiset.mem_cons, Multiset.mem_bind]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨lam, -, h⟩
    obtain ⟨c', hc', rfl⟩ := Multiset.mem_map.mp h
    unfold Pruned.childCalls at hc'
    split_ifs at hc' with hne
    · exact ⟨lam, hne, c', hc', rfl⟩
    · simp at hc'
  · rintro ⟨lam, hne, c', hc', rfl⟩
    refine ⟨lam, mem_univ lam, Multiset.mem_map.mpr ⟨c', ?_, rfl⟩⟩
    rwa [Pruned.childCalls, ite_eq_left hne]

/-- A call below the child `λ` is at the vertex `τ` of depth `k + 1` exactly if `λ` is the first
term of `τ` and, seen from the child, the call is at the rest of `τ`.
-/
private theorem PrunedCall.vertex_under_eq_iff {lam : Term} {c : PrunedCall} {k : ℕ}
    {τ : Vertex (k + 1)} :
    (c.under lam).vertex = ⟨k + 1, τ⟩ ↔ lam = τ 0 ∧ c.vertex = ⟨k, Fin.tail τ⟩ := by
  obtain ⟨⟨k', τ'⟩, T⟩ := c
  constructor
  · intro h
    simp only [PrunedCall.under, Sigma.mk.injEq, Nat.add_right_cancel_iff] at h
    obtain ⟨rfl, h⟩ := h
    obtain rfl := eq_of_heq h
    simp
  · rintro ⟨rfl, h⟩
    simp only [Sigma.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain rfl := eq_of_heq h
    simp [PrunedCall.under]

/-- A vertex is called when its depth and label tuple occur in the recorded call multiset. -/
def Pruned.Called {L k : ℕ} (encA encB : Leaf L → ℤ) (U : Finset (OutStr L)) (τ : Vertex k) :
    Prop :=
  ∃ c ∈ Pruned.calls L encA encB U, c.vertex = ⟨k, τ⟩

/-- The root is called.
-/
theorem Pruned.called_root {L : ℕ} (encA encB : Leaf L → ℤ) (U : Finset (OutStr L))
    (τ : Vertex 0) : Pruned.Called encA encB U τ := by
  obtain rfl : τ = Fin.elim0 := Subsingleton.elim _ _
  cases L with
  | zero => exact ⟨_, Multiset.mem_singleton_self _, rfl⟩
  | succ n => exact ⟨_, Pruned.mem_calls_succ.mpr (.inl rfl), rfl⟩

/-- A non-root vertex is called exactly when its leading child has requests and the tail vertex is
called within that child.
-/
theorem Pruned.called_succ {n k : ℕ} (encA encB : Leaf (n + 1) → ℤ) (S : Finset (OutStr (n + 1)))
    (τ : Vertex (k + 1)) :
    Pruned.Called encA encB S τ ↔ (childSet S (τ 0)).Nonempty ∧
      Pruned.Called (sliceAt encA (τ 0)) (sliceAt encB (τ 0)) (childSet S (τ 0)) (Fin.tail τ) := by
  constructor
  · rintro ⟨c, hc, hcτ⟩
    rcases Pruned.mem_calls_succ.mp hc with rfl | ⟨lam, hne, c', hc', rfl⟩
    · exact absurd (congrArg Sigma.fst hcτ) (by simp)
    · obtain ⟨rfl, hc'τ⟩ := PrunedCall.vertex_under_eq_iff.mp hcτ
      exact ⟨hne, c', hc', hc'τ⟩
  · rintro ⟨hne, c', hc', hc'τ⟩
    exact ⟨c'.under (τ 0), Pruned.mem_calls_succ.mpr (.inr ⟨τ 0, hne, c', hc', rfl⟩),
      PrunedCall.vertex_under_eq_iff.mpr ⟨rfl, hc'τ⟩⟩

/-- Existence of a requested tuple relevant to a cons vertex reduces to the same question for the
tail vertex and the child request set.
-/
private theorem exists_contributes_childSet {n k : ℕ} (S : Finset (OutStr (n + 1)))
    (τ : Vertex (k + 1)) :
    (∃ w' ∈ childSet S (τ 0), Vertex.Contributes (Fin.tail τ) w')
      ↔ ∃ w ∈ S, Vertex.Contributes τ w := by
  have hcons (w : OutStr (n + 1)) : Vertex.Contributes τ w
      ↔ (τ 0).Contributes (w 0) ∧ Vertex.Contributes (Fin.tail τ) (Fin.tail w) := by
    rw [← Vertex.contributes_cons, Fin.cons_self_tail]
  constructor
  · rintro ⟨w', hw', hτ'⟩
    obtain ⟨w, hw, hz, rfl⟩ := mem_childSet.mp hw'
    exact ⟨w, hw, (hcons w).mpr ⟨hz, hτ'⟩⟩
  · rintro ⟨w, hw, hτ⟩
    exact ⟨_, mem_childSet.mpr ⟨w, hw, ((hcons w).mp hτ).1, rfl⟩, ((hcons w).mp hτ).2⟩

/-- For vertices within the recursion depth, being called is equivalent to being the root or being
relevant to at least one requested tuple.
-/
theorem Pruned.called_iff_root_or {L k : ℕ} (encA encB : Leaf L → ℤ) (U : Finset (OutStr L))
    (hkL : k ≤ L) (τ : Vertex k) :
    Pruned.Called encA encB U τ ↔ k = 0 ∨ ∃ w ∈ U, Vertex.Contributes τ w := by
  induction L generalizing k with
  | zero =>
    obtain rfl : k = 0 := by omega
    exact iff_of_true (Pruned.called_root encA encB U τ) (.inl rfl)
  | succ n ih =>
    cases k with
    | zero => exact iff_of_true (Pruned.called_root encA encB U τ) (.inl rfl)
    | succ k =>
      have ihτ := ih (sliceAt encA (τ 0)) (sliceAt encB (τ 0)) (childSet U (τ 0))
        (Nat.le_of_succ_le_succ hkL) (Fin.tail τ)
      rw [Pruned.called_succ, ← exists_contributes_childSet]
      constructor
      · rintro ⟨⟨w', hw'⟩, hcalled⟩
        rcases ihτ.mp hcalled with rfl | hτ'
        · -- The child `λ` itself, as a vertex at depth 0, contributes to every string of `U_λ`.
          exact .inr ⟨w', hw', fun ℓ => ℓ.elim0⟩
        · exact .inr hτ'
      · rintro (hk | ⟨w', hw', hτ'⟩)
        · exact absurd hk (Nat.succ_ne_zero k)
        · exact ⟨⟨w', hw'⟩, ihτ.mpr (.inr ⟨w', hw', hτ'⟩)⟩

/-- Away from the empty-request root exception, a vertex within the recursion depth is called
exactly when some requested tuple is relevant to it. The hypothesis `hk` admits every
positive-depth vertex and also admits the root when requests are nonempty.
-/
theorem Pruned.called_iff {L k : ℕ} (encA encB : Leaf L → ℤ) (U : Finset (OutStr L))
    (hk : 1 ≤ k ∨ U.Nonempty) (hkL : k ≤ L) (τ : Vertex k) :
    Pruned.Called encA encB U τ ↔ ∃ w ∈ U, Vertex.Contributes τ w := by
  rw [Pruned.called_iff_root_or _ _ U hkL τ]
  constructor
  · rintro (rfl | h)
    · obtain ⟨w, hw⟩ := hk.resolve_left (by omega)
      exact ⟨w, hw, fun ℓ => ℓ.elim0⟩
    · exact h
  · exact Or.inr

/-- A call at depth `k` is passed strings of length `L - k`.
-/
theorem Pruned.depth_add_length {L : ℕ} {encA encB : Leaf L → ℤ} {U : Finset (OutStr L)}
    {c : PrunedCall} (hc : c ∈ Pruned.calls L encA encB U) : c.vertex.1 + c.passed.1 = L := by
  induction L generalizing c with
  | zero =>
    obtain rfl := Multiset.mem_singleton.mp hc
    rfl
  | succ n ih =>
    rcases Pruned.mem_calls_succ.mp hc with rfl | ⟨lam, -, c', hc', rfl⟩
    · exact Nat.zero_add _
    · have hlen := ih hc'
      change c'.vertex.1 + 1 + c'.passed.1 = n + 1
      omega

/-- `w'` is the suffix of `w` that is left when the first `k` variables are removed.
-/
def IsSuffixFrom {n L : ℕ} (k : ℕ) (w' : OutStr n) (w : OutStr L) : Prop :=
  ∀ (i : Fin n) (hi : k + (i : ℕ) < L), w' i = w ⟨k + i, hi⟩

/-- Removing no variable leaves the string as it is.
-/
private theorem isSuffixFrom_zero {n : ℕ} (w' w : OutStr n) : IsSuffixFrom 0 w' w ↔ w' = w := by
  have hidx (i : Fin n) (hi : 0 + (i : ℕ) < n) : (⟨0 + i, hi⟩ : Fin n) = i :=
    Fin.ext (Nat.zero_add _)
  constructor
  · intro h
    funext i
    rw [h i (by simp), hidx]
  · rintro rfl i hi
    rw [hidx]

/-- Removing `k + 1` variables is removing the first variable and then `k` more.
-/
private theorem isSuffixFrom_succ {n L k : ℕ} {w' : OutStr n} {w : OutStr (L + 1)} :
    IsSuffixFrom (k + 1) w' w ↔ IsSuffixFrom k w' (Fin.tail w) := by
  have hidx (i : Fin n) (h₁ : k + 1 + (i : ℕ) < L + 1) (h₂ : k + (i : ℕ) < L) :
      w ⟨k + 1 + i, h₁⟩ = Fin.tail w ⟨k + i, h₂⟩ :=
    congrArg w (Fin.ext (by simp only [Fin.val_succ]; omega))
  exact ⟨fun h i hi => (h i (by omega)).trans (hidx i _ hi),
    fun h i hi => (h i (by omega)).trans (hidx i hi _).symm⟩

/-- The set passed to the root is `U`, and the root contributes to every string.
-/
private theorem mem_iff_root {L : ℕ} (U : Finset (OutStr L)) (w' : OutStr L) :
    w' ∈ U ↔ ∃ w ∈ U, Vertex.Contributes (Fin.elim0 : Vertex 0) w ∧ IsSuffixFrom 0 w' w := by
  simp only [isSuffixFrom_zero]
  exact ⟨fun h => ⟨w', h, fun ℓ => ℓ.elim0, rfl⟩, fun ⟨_, hw, _, h⟩ => h ▸ hw⟩

/-- A recorded call receives exactly the suffixes of original requests relevant to its vertex. Its
recorded remaining length and depth identify the suffix position.
-/
theorem Pruned.mem_passed_iff {L : ℕ} {encA encB : Leaf L → ℤ} {U : Finset (OutStr L)}
    {c : PrunedCall} (hc : c ∈ Pruned.calls L encA encB U) (w' : OutStr c.passed.1) :
    w' ∈ c.passed.2 ↔
      ∃ w ∈ U, Vertex.Contributes c.vertex.2 w ∧ IsSuffixFrom c.vertex.1 w' w := by
  induction L generalizing c with
  | zero =>
    obtain rfl := Multiset.mem_singleton.mp hc
    exact mem_iff_root U w'
  | succ n ih =>
    rcases Pruned.mem_calls_succ.mp hc with rfl | ⟨lam, -, c', hc', rfl⟩
    · exact mem_iff_root U w'
    · -- A vertex below the child `λ`: the induction hypothesis for `S_λ`, whose strings are the
      -- rests of the strings of `U` to whose first variable `λ` contributes.
      refine (ih hc' w').trans ⟨?_, ?_⟩
      · rintro ⟨_, hw₁, hτ, hsuffix⟩
        obtain ⟨w, hw, hz, rfl⟩ := mem_childSet.mp hw₁
        exact ⟨w, hw, Vertex.contributes_cons.mpr ⟨hz, hτ⟩, isSuffixFrom_succ.mpr hsuffix⟩
      · rintro ⟨w, hw, hτ, hsuffix⟩
        obtain ⟨hz, hτ'⟩ := Vertex.contributes_cons.mp hτ
        exact ⟨Fin.tail w, mem_childSet.mpr ⟨w, hw, hz, rfl⟩, hτ', isSuffixFrom_succ.mp hsuffix⟩

/-- A leaf is visited exactly when it is the zero-depth root or contributes to a request. This
includes the empty request set without an exceptional hypothesis.
-/
theorem Pruned.visits_iff_root_or_mem_leaves {L : ℕ} (encA encB : Leaf L → ℤ)
    (U : Finset (OutStr L)) (τ : Leaf L) :
    Pruned.Visits encA encB U τ ↔ L = 0 ∨ τ ∈ leaves U := by
  change Pruned.Called encA encB U τ ↔ _
  simpa only [mem_leaves, Vertex.contributes_iff_leaf] using
    Pruned.called_iff_root_or encA encB U (le_refl L) τ

/-- With positive depth or nonempty requests, the visited-leaf set is exactly `leaves U`. The
unconditional root case is given separately by `Pruned.visits_iff_root_or_mem_leaves`.
-/
theorem Pruned.visits_iff_mem_leaves {L : ℕ} (encA encB : Leaf L → ℤ) (U : Finset (OutStr L))
    (h : 0 < L ∨ U.Nonempty) (τ : Leaf L) : Pruned.Visits encA encB U τ ↔ τ ∈ leaves U :=
  -- A leaf is a vertex at depth `L`.
  (Pruned.called_iff encA encB U h le_rfl τ).trans
    (by simp only [mem_leaves, Vertex.contributes_iff_leaf])

/-! ### Lemma 10, third claim: the total size of the sets passed -/

/-- Membership in a positive-depth relevant-leaf set reduces to membership of the tail in the
child relevant-leaf set.
-/
theorem mem_leaves_succ {n : ℕ} {S : Finset (OutStr (n + 1))} {τ : Leaf (n + 1)} :
    τ ∈ leaves S ↔ Fin.tail τ ∈ leaves (childSet S (τ 0)) := by
  rw [mem_leaves, mem_leaves]
  constructor
  · rintro ⟨w, hw, hcon⟩
    obtain ⟨h0, h1⟩ := Leaf.contributes_succ.mp hcon
    exact ⟨Fin.tail w, mem_childSet.mpr ⟨w, hw, h0, rfl⟩, h1⟩
  · rintro ⟨w', hw', h1⟩
    obtain ⟨w, hw, h0, rfl⟩ := mem_childSet.mp hw'
    exact ⟨w, hw, Leaf.contributes_succ.mpr ⟨h0, h1⟩⟩

/-- Count relevant leaves by summing the relevant-leaf counts of all children; distinct leading
labels keep these families disjoint.
-/
theorem card_leaves_succ {n : ℕ} (S : Finset (OutStr (n + 1))) :
    (leaves S).card = ∑ lam, (leaves (childSet S lam)).card := by
  rw [card_eq_sum_card_fiberwise (f := fun τ : Leaf (n + 1) => τ 0) (t := univ)
    (fun _ _ => mem_coe.mpr (mem_univ _))]
  refine sum_congr rfl fun lam _ => ?_
  rw [← card_image_of_injective (leaves (childSet S lam))
    (Fin.cons_right_injective (α := fun _ : Fin (n + 1) => Term) lam)]
  congr 1
  ext τ
  simp only [mem_filter, mem_image]
  constructor
  · rintro ⟨hτ, rfl⟩
    exact ⟨Fin.tail τ, mem_leaves_succ.mp hτ, Fin.cons_self_tail τ⟩
  · rintro ⟨τ', hτ', rfl⟩
    refine ⟨mem_leaves_succ.mpr ?_, Fin.cons_zero _ _⟩
    simpa using hτ'

/-- Different output strings have different private leaves.
-/
theorem privateLeaf_injective {L : ℕ} : Function.Injective (privateLeaf (L := L)) :=
  have hterm : Function.Injective OutVar.privateTerm := by decide
  fun _ _ h => funext fun ℓ => hterm (congrFun h ℓ)

/-- The private-leaf injection bounds the number of requested tuples by the number of their
relevant leaves.
-/
theorem card_le_card_leaves {n : ℕ} (S : Finset (OutStr n)) : S.card ≤ (leaves S).card := by
  refine card_le_card_of_injOn privateLeaf (fun w hw => ?_) privateLeaf_injective.injOn
  exact mem_coe.mpr (mem_leaves.mpr
    ⟨w, hw, fun _ => (Term.contributes_iff _ _).mpr (.inr rfl)⟩)

/-- The total size of the sets passed to the calls at depth `k` in a list of calls.
-/
private def sizeAt (s : Multiset PrunedCall) (k : ℕ) : ℕ :=
  ((s.filter fun c => c.vertex.1 = k).map fun c => c.passed.2.card).sum

/-- The size at depth `k` of a list of calls with one more call.
-/
private theorem sizeAt_cons (c : PrunedCall) (s : Multiset PrunedCall) (k : ℕ) :
    sizeAt (c ::ₘ s) k
      = (if c.vertex.1 = k then c.passed.2.card else 0) + sizeAt s k := by
  unfold sizeAt
  rw [Multiset.filter_cons]
  split_ifs <;> simp

/-- The size at depth `k` of the lists of calls of the ten children together.
-/
private theorem sizeAt_bind (f : Term → Multiset PrunedCall) (k : ℕ) :
    sizeAt (univ.val.bind f) k = ∑ lam, sizeAt (f lam) k := by
  unfold sizeAt
  rw [Multiset.filter_bind, Multiset.map_bind, Multiset.sum_bind]
  rfl

/-- Seen from one level higher, the calls at depth `k` are at depth `k + 1`.
-/
private theorem sizeAt_under_succ (lam : Term) (s : Multiset PrunedCall) (k : ℕ) :
    sizeAt (s.map (PrunedCall.under lam)) (k + 1) = sizeAt s k := by
  unfold sizeAt
  rw [Multiset.filter_map, Multiset.map_map]
  rw [Multiset.filter_congr (q := fun c => c.vertex.1 = k) (by simp [PrunedCall.under])]
  rfl

/-- Seen from one level higher, no call is at depth `0`.
-/
private theorem sizeAt_under_zero (lam : Term) (s : Multiset PrunedCall) :
    sizeAt (s.map (PrunedCall.under lam)) 0 = 0 := by
  unfold sizeAt
  rw [Multiset.filter_map, Multiset.filter_eq_nil.mpr (by simp [PrunedCall.under])]
  rfl

/-- The total size of the sets passed is the sum, over the depths, of the sizes at each depth.
-/
private theorem sum_sizeAt (s : Multiset PrunedCall) (N : ℕ) (h : ∀ c ∈ s, c.vertex.1 < N) :
    (s.map fun c => c.passed.2.card).sum = ∑ k ∈ range N, sizeAt s k := by
  induction s using Multiset.induction_on with
  | empty => simp [sizeAt]
  | cons c s ih =>
    simp only [sizeAt_cons, Multiset.map_cons, Multiset.sum_cons, sum_add_distrib]
    rw [ih fun c' hc' => h c' (Multiset.mem_cons_of_mem hc'), sum_ite_eq,
      ite_eq_left (mem_range.mpr (h c (Multiset.mem_cons_self c s)))]

/-- At any fixed depth, the sum of all passed request-set cardinalities is bounded by the root
request set's relevant-leaf count.
-/
theorem Pruned.sum_card_passed_le {L : ℕ} (encA encB : Leaf L → ℤ) (U : Finset (OutStr L)) (k : ℕ) :
    (((Pruned.calls L encA encB U).filter fun c => c.vertex.1 = k).map fun c => c.passed.2.card).sum
      ≤ (leaves U).card := by
  -- The paper's injection (vertex, suffix) ↦ leaf, organised as an induction on `L`: the strings
  -- passed to the root inject into `leaves(U)`, and the calls at depth `k + 1` are the calls at
  -- depth `k` of the children `λ`, whose leaves, with `λ` put in front, are pairwise disjoint parts
  -- of `leaves(U)`.
  change sizeAt (Pruned.calls L encA encB U) k ≤ _
  induction L generalizing k with
  | zero =>
    have hcalls : Pruned.calls 0 encA encB U = ⟨⟨0, Fin.elim0⟩, ⟨0, U⟩⟩ ::ₘ 0 := rfl
    rw [hcalls, sizeAt_cons]
    split_ifs
    · simpa [sizeAt] using card_le_card_leaves U
    · simp [sizeAt]
  | succ n ih =>
    rw [Pruned.calls_succ, sizeAt_cons, sizeAt_bind]
    cases k with
    | zero =>
      simp only [sizeAt_under_zero, sum_const_zero, ite_true, add_zero]
      exact card_le_card_leaves U
    | succ k =>
      simp only [sizeAt_under_succ]
      rw [ite_eq_right (by simp), zero_add, card_leaves_succ]
      refine sum_le_sum fun lam _ => ?_
      unfold Pruned.childCalls
      split_ifs
      · exact ih _ _ _ _
      · simp [sizeAt]

/-- The sum of the cardinalities of all passed request sets is at most `(L + 1) * (leaves
U).card`.
-/
theorem Pruned.totalSize_le {L : ℕ} (encA encB : Leaf L → ℤ) (U : Finset (OutStr L)) :
    Pruned.totalSize encA encB U ≤ (L + 1) * (leaves U).card := by
  have hdepth : ∀ c ∈ Pruned.calls L encA encB U, c.vertex.1 < L + 1 :=
    fun c hc => by have := Pruned.depth_add_length hc; omega
  rw [Pruned.totalSize, sum_sizeAt _ (L + 1) hdepth]
  calc ∑ k ∈ range (L + 1), sizeAt (Pruned.calls L encA encB U) k
      ≤ ∑ _k ∈ range (L + 1), (leaves U).card :=
        sum_le_sum fun k _ => Pruned.sum_card_passed_le _ _ U k
    _ = (L + 1) * (leaves U).card := by simp

/-- Combine value correctness, the visited-leaf characterization and the passed-set cardinality
bound for the two input encodings. Values and the set-size bound apply at every depth and request
set. The leaf equivalence excludes the empty zero-depth root;
`Pruned.visits_iff_root_or_mem_leaves` gives the unconditional alternative for that case.
-/
theorem pruned_spec {L : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ) (U : Finset (OutStr L)) :
    Pruned.result L (encodingL a) (encodingR b) U = U.piecewise (bilinearProduct a b) 0
      ∧ (0 < L ∨ U.Nonempty →
          ∀ τ : Leaf L, Pruned.Visits (encodingL a) (encodingR b) U τ ↔ τ ∈ leaves U)
      ∧ Pruned.totalSize (encodingL a) (encodingR b) U ≤ (L + 1) * (leaves U).card :=
  ⟨Pruned.result_eq_piecewise_bilinearProduct a b U, Pruned.visits_iff_mem_leaves _ _ U,
    Pruned.totalSize_le _ _ U⟩

end Cslib.Algorithms.MatrixMultiplication.Schonhage
