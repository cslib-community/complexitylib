/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Karger.Memory.Layout

/-!
# The contraction structure over memory: contraction

`contract u v` merges supervertex `v` into `u` and moves the last supervertex into slot `v`, in
the layout of `Karger.Memory.Layout`. It is the memory-level counterpart of the machine-level
`postRandStep` after the scans, in three phases, each with its own weakest-precondition lemma:

1. **Degrees and total** (`mergeDegrees`). Four reads, then the total becomes `S - 2 W u v` and
   the degree of `u` becomes `(D u - W u v) + (D v - W u v)`.
2. **Merge** (`mergeLoop`). For every `c ∉ {u, v}`, the entries `(u, c)` and `(c, u)` become
   `W u c + W v c`. Row and column `v` are left as they are: compaction overwrites them, or they
   fall outside the graph.
3. **Shrinking** (`shrink`). The size becomes `m = k - 1`. When `v` is not `m`, the degree of `m`
   moves to slot `v`, and row and column `m` move to row and column `v` (`compact`,
   `compactLoop`).

The matrix in memory part-way through each loop is a pure function of the matrix before it
(`mergedTo`, `compactedTo`), and the matrix after both is `contractMatrix`
(`mergedTo_eq_contractMatrix`, `compactedTo_mergedTo_eq_contractMatrix`). These are the only
intermediate invariants, and they are stated on matrices, not on memory. The degree and total
updates are the identities of `Karger.Graph` (`rowDeg_mergePair_u`, `rowDeg_mergePair_other`,
`rowDeg_contractMatrix`, `totalDoubledWeight_contractMatrix`), used unchanged.

A contraction of `k` supervertices costs at most `7 k + 7` memory units (`wp_contract`). The
machine-level counterparts are `phaseADegrees_exec`, `mergeLoop_exec`, `compactPhase_exec` and
`postRandStep_exec` in `Cslib.Algorithms.WordRAM.Karger`.

## Main definitions

* `mergedTo`, `compactedTo`: the matrix part-way through each loop.
* `mergeDegrees`, `mergeStep`, `mergeLoop`, `compactStep`, `compactLoop`, `compact`, `shrink`,
  `contract`: the programs.

## Main results

* `mergedTo_eq_mergePair`, `compactedTo_eq`, `mergedTo_eq_contractMatrix`,
  `compactedTo_mergedTo_eq_contractMatrix`: the loops compute `contractMatrix`.
* `wp_mergeDegrees`, `wp_mergeLoop`, `wp_compactLoop`, `wp_compact`, `wp_shrink`: the effect and
  cost of each phase.
* `wp_contract`: `contract u v` realizes `contractGraph`, preserves the invariant, writes only the
  layout's cells and costs at most `7 k + 7` memory units.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.Karger.Memory

open Finset Cslib.WordRAM Cslib.WeightedCut Cslib.Algorithms.WordRAM.Karger Cslib.DataStructure
  Cslib.DataStructure.Memory Cslib.DataStructure.StateTransitionSpec

/-! ## The matrix during the loops -/

/-- The matrix `M` part-way through merging `v` into `u`: the entries `(u, j)` and `(j, u)` for
`j < c` other than `u` and `v` hold `M u j + M v j`, and every other entry is `M`'s. -/
def mergedTo (M : ℕ → ℕ → ℕ) (u v c i j : ℕ) : ℕ :=
  if i = u ∧ j < c ∧ j ≠ u ∧ j ≠ v then M u j + M v j
  else if j = u ∧ i < c ∧ i ≠ u ∧ i ≠ v then M u i + M v i
  else M i j

/-- The matrix `M` part-way through moving row and column `m` to row and column `v`: the entries
`(v, j)` and `(j, v)` for `j < c` other than `v` hold `M m j`, and every other entry is `M`'s. -/
def compactedTo (M : ℕ → ℕ → ℕ) (v m c i j : ℕ) : ℕ :=
  if i = v ∧ j < c ∧ j ≠ v then M m j
  else if j = v ∧ i < c ∧ i ≠ v then M m i
  else M i j

section Pure

variable {M : ℕ → ℕ → ℕ} {u v m c : ℕ}

@[simp] theorem mergedTo_zero (i j : ℕ) : mergedTo M u v 0 i j = M i j := by
  simp [mergedTo]

/-- Merging skips `u` and `v`. -/
theorem mergedTo_succ_of_mem (hc : c = u ∨ c = v) : mergedTo M u v (c + 1) = mergedTo M u v c := by
  funext i j
  unfold mergedTo
  have h₁ : (i = u ∧ j < c + 1 ∧ j ≠ u ∧ j ≠ v) ↔ (i = u ∧ j < c ∧ j ≠ u ∧ j ≠ v) := by omega
  have h₂ : (j = u ∧ i < c + 1 ∧ i ≠ u ∧ i ≠ v) ↔ (j = u ∧ i < c ∧ i ≠ u ∧ i ≠ v) := by omega
  simp only [h₁, h₂]

/-- One merge step writes `(u, c)`, then `(c, u)`. -/
theorem mergedTo_succ (hu : c ≠ u) (hv : c ≠ v) (i j : ℕ) :
    mergedTo M u v (c + 1) i j =
      if i = c ∧ j = u then M u c + M v c
      else if i = u ∧ j = c then M u c + M v c
      else mergedTo M u v c i j := by
  unfold mergedTo
  by_cases h₁ : i = c ∧ j = u
  · obtain ⟨rfl, rfl⟩ := h₁
    simp [hu, hv]
  by_cases h₂ : i = u ∧ j = c
  · obtain ⟨rfl, rfl⟩ := h₂
    simp [hu, hv]
  simp only [h₁, h₂, ite_false]
  have e₁ : (i = u ∧ j < c + 1 ∧ j ≠ u ∧ j ≠ v) ↔ (i = u ∧ j < c ∧ j ≠ u ∧ j ≠ v) := by omega
  have e₂ : (j = u ∧ i < c + 1 ∧ i ≠ u ∧ i ≠ v) ↔ (j = u ∧ i < c ∧ i ≠ u ∧ i ≠ v) := by omega
  simp only [e₁, e₂]

/-- The merge reads `(u, c)` before writing it. -/
theorem mergedTo_left (hu : c ≠ u) : mergedTo M u v c u c = M u c := by
  simp [mergedTo, hu]

/-- The merge reads `(v, c)`, which it never writes. -/
theorem mergedTo_right (huv : u ≠ v) (hu : c ≠ u) : mergedTo M u v c v c = M v c := by
  simp [mergedTo, hu, huv.symm]

/-- **The merge computes `mergePair`** away from `v`, on a multigraph. -/
theorem mergedTo_eq_mergePair {k : ℕ} {W : Fin k → Fin k → ℕ} (hW : IsMultigraph W)
    (hM : ∀ a b : Fin k, M a b = W a b) {u v : Fin k} {a b : Fin k} (ha : a ≠ v) (hb : b ≠ v) :
    mergedTo M u v k a b = mergePair W u v a b := by
  have hav : (a : ℕ) ≠ v := Fin.val_ne_of_ne ha
  have hbv : (b : ℕ) ≠ v := Fin.val_ne_of_ne hb
  unfold mergedTo mergePair
  by_cases hab : a = b
  · subst hab
    have h : ¬((a : ℕ) = u ∧ (a : ℕ) < k ∧ (a : ℕ) ≠ u ∧ (a : ℕ) ≠ v) := fun h => h.2.2.1 h.1
    simp only [h, ite_false, true_or, ite_true, hM, hW.2]
  · have hab' : (a : ℕ) ≠ b := Fin.val_ne_of_ne hab
    simp only [hab, ha, hb, or_self, ite_false, Fin.val_inj, a.isLt, b.isLt, true_and,
      Fin.val_inj.not, not_false_eq_true, and_true]
    by_cases hau : a = u
    · subst hau
      simp [Ne.symm hab, hM]
    · by_cases hbu : b = u
      · subst hbu
        simp [hau, hM, hW.1 a b, hW.1 a v]
      · simp [hau, hbu, hM]

@[simp] theorem compactedTo_zero (i j : ℕ) : compactedTo M v m 0 i j = M i j := by
  simp [compactedTo]

/-- Compaction skips `v`. -/
theorem compactedTo_succ_of_eq (hc : c = v) : compactedTo M v m (c + 1) = compactedTo M v m c := by
  funext i j
  unfold compactedTo
  have h₁ : (i = v ∧ j < c + 1 ∧ j ≠ v) ↔ (i = v ∧ j < c ∧ j ≠ v) := by omega
  have h₂ : (j = v ∧ i < c + 1 ∧ i ≠ v) ↔ (j = v ∧ i < c ∧ i ≠ v) := by omega
  simp only [h₁, h₂]

/-- One compaction step writes `(v, c)`, then `(c, v)`. -/
theorem compactedTo_succ (hc : c ≠ v) (i j : ℕ) :
    compactedTo M v m (c + 1) i j =
      if i = c ∧ j = v then M m c
      else if i = v ∧ j = c then M m c
      else compactedTo M v m c i j := by
  unfold compactedTo
  by_cases h₁ : i = c ∧ j = v
  · obtain ⟨rfl, rfl⟩ := h₁
    simp [hc]
  by_cases h₂ : i = v ∧ j = c
  · obtain ⟨rfl, rfl⟩ := h₂
    simp [hc]
  simp only [h₁, h₂, ite_false]
  have e₁ : (i = v ∧ j < c + 1 ∧ j ≠ v) ↔ (i = v ∧ j < c ∧ j ≠ v) := by omega
  have e₂ : (j = v ∧ i < c + 1 ∧ i ≠ v) ↔ (j = v ∧ i < c ∧ i ≠ v) := by omega
  simp only [e₁, e₂]

/-- Compaction reads `(m, c)`, which it never writes. -/
theorem compactedTo_last (hm : m ≠ v) (hc : c ≠ v) : compactedTo M v m c m c = M m c := by
  simp [compactedTo, hm, hc]

/-- **Compaction moves row and column `m` into slot `v`**, for a matrix symmetric in row and
column `m` whose entries `(v, v)` and `(m, m)` agree. -/
theorem compactedTo_eq (hsym : ∀ i < m, i ≠ v → M m i = M i m) (hdiag : M v v = M m m) {i j : ℕ}
    (hi : i < m) (hj : j < m) :
    compactedTo M v m m i j = M (if i = v then m else i) (if j = v then m else j) := by
  unfold compactedTo
  by_cases hiv : i = v <;> by_cases hjv : j = v
  · subst hiv; subst hjv
    simp [hdiag]
  · subst hiv
    simp [hj, hjv]
  · subst hjv
    simp [hi, hiv, hsym i hi hiv]
  · simp [hiv, hjv]

/-- The index of `embedCompact v i`: `m` at the removed slot, `i` elsewhere. -/
theorem val_embedCompact {m : ℕ} (v : Fin (m + 1)) (i : Fin m) :
    (embedCompact v i : ℕ) = if (i : ℕ) = v then m else i := by
  unfold embedCompact
  split_ifs <;> rfl

/-- **The merge alone computes `contractMatrix`** when `v` is the last supervertex. -/
theorem mergedTo_eq_contractMatrix {W : Fin (m + 1) → Fin (m + 1) → ℕ} (hW : IsMultigraph W)
    (hM : ∀ a b : Fin (m + 1), M a b = W a b) {u v : Fin (m + 1)} (hv : (v : ℕ) = m)
    (i j : Fin m) : mergedTo M u v (m + 1) i j = contractMatrix W u v i j := by
  have hne (i : Fin m) : i.castSucc ≠ v := Fin.ne_of_val_ne (by
    have := i.isLt
    simp only [Fin.val_castSucc]
    omega)
  have he (i : Fin m) : embedCompact v i = i.castSucc := by
    rw [embedCompact, ite_eq_right (by have := i.isLt; omega)]
  rw [contractMatrix, he, he]
  exact mergedTo_eq_mergePair hW hM (hne i) (hne j)

/-- **The merge and the compaction compute `contractMatrix`** when `v` is not the last
supervertex. -/
theorem compactedTo_mergedTo_eq_contractMatrix {W : Fin (m + 1) → Fin (m + 1) → ℕ}
    (hW : IsMultigraph W) (hM : ∀ a b : Fin (m + 1), M a b = W a b) {u v : Fin (m + 1)}
    (huv : u ≠ v) (hv : (v : ℕ) < m) (i j : Fin m) :
    compactedTo (mergedTo M u v (m + 1)) v m m i j = contractMatrix W u v i j := by
  have hmerge (a b : Fin (m + 1)) (ha : a ≠ v) (hb : b ≠ v) :
      mergedTo M u v (m + 1) a b = mergePair W u v a b := mergedTo_eq_mergePair hW hM ha hb
  have hlast : Fin.last m ≠ v := Fin.ne_of_val_ne (by simp only [Fin.val_last]; omega)
  have hsym (c : ℕ) (hc : c < m) (hcv : c ≠ (v : ℕ)) :
      mergedTo M u v (m + 1) m c = mergedTo M u v (m + 1) c m := by
    have hc' : (⟨c, by omega⟩ : Fin (m + 1)) ≠ v := Fin.ne_of_val_ne hcv
    have h₁ := hmerge (Fin.last m) ⟨c, by omega⟩ hlast hc'
    have h₂ := hmerge ⟨c, by omega⟩ (Fin.last m) hc' hlast
    simp only [Fin.val_last] at h₁ h₂
    rw [h₁, h₂, (isMultigraph_mergePair hW u v).1]
  have hdiag : mergedTo M u v (m + 1) v v = mergedTo M u v (m + 1) m m := by
    have h₁ := hmerge (Fin.last m) (Fin.last m) hlast hlast
    simp only [Fin.val_last] at h₁
    have hvu : (v : ℕ) ≠ u := Fin.val_ne_of_ne huv.symm
    rw [h₁, (isMultigraph_mergePair hW u v).2]
    simp [mergedTo, hvu, hM, hW.2]
  rw [compactedTo_eq hsym hdiag i.isLt j.isLt, contractMatrix, ← val_embedCompact,
    ← val_embedCompact]
  exact hmerge _ _ (embedCompact_ne v i) (embedCompact_ne v j)

/-- The merged row `u` away from `u` and `v`. -/
theorem mergePair_left {W : Fin (m + 1) → Fin (m + 1) → ℕ} {u v c : Fin (m + 1)} (huv : u ≠ v)
    (hcu : c ≠ u) (hcv : c ≠ v) : mergePair W u v u c = W u c + W v c := by
  simp [mergePair, Ne.symm hcu, huv, hcv]

/-- Entries of the merged matrix away from `v` are at most the total weight. -/
theorem mergePair_le_totalDoubledWeight {W : Fin (m + 1) → Fin (m + 1) → ℕ} (hW : IsMultigraph W)
    {u v a b : Fin (m + 1)} (huv : u ≠ v) (ha : a ≠ v) (hb : b ≠ v) :
    mergePair W u v a b ≤ totalDoubledWeight W := by
  have h := entry_le_totalDoubledWeight (contractMatrix W u v) (compactIdx v a ha)
    (compactIdx v b hb)
  rw [contractMatrix, embedCompact_compactIdx, embedCompact_compactIdx] at h
  have := totalDoubledWeight_contractMatrix hW huv
  omega

/-- Degrees of the merged matrix away from `v` are at most the total weight. -/
theorem rowDeg_mergePair_le_totalDoubledWeight {W : Fin (m + 1) → Fin (m + 1) → ℕ}
    (hW : IsMultigraph W) {u v a : Fin (m + 1)} (huv : u ≠ v) (ha : a ≠ v) :
    rowDeg (mergePair W u v) a ≤ totalDoubledWeight W := by
  have h := rowDeg_le_totalDoubledWeight (contractMatrix W u v) (compactIdx v a ha)
  rw [rowDeg_contractMatrix, embedCompact_compactIdx] at h
  have := totalDoubledWeight_contractMatrix hW huv
  omega

end Pure

/-! ## The loops -/

variable (L : Layout) {w : ℕ}

/-- Merge index `c`: the entries `(u, c)` and `(c, u)` become `W u c + W v c`. -/
def mergeStep (u v c : ℕ) : Prog Unit := do
  let a ← (L.row u).get c
  let b ← (L.row v).get c
  (L.row u).set c (a + b)
  (L.row c).set u (a + b)

/-- Merge `v` into `u` at the indices `c, …, c + n - 1`, skipping `u` and `v`. -/
def mergeLoop (u v : ℕ) : ℕ → ℕ → Prog Unit
  | 0, _ => pure ()
  | n + 1, c =>
    (if c = u ∨ c = v then pure () else mergeStep L u v c) >>= fun _ => mergeLoop u v n (c + 1)

/-- Compact index `c`: the entries `(v, c)` and `(c, v)` become `W m c`. -/
def compactStep (v m c : ℕ) : Prog Unit := do
  let a ← (L.row m).get c
  (L.row v).set c a
  (L.row c).set v a

/-- Move row and column `m` into slot `v` at the indices `c, …, c + n - 1`, skipping `v`. -/
def compactLoop (v m : ℕ) : ℕ → ℕ → Prog Unit
  | 0, _ => pure ()
  | n + 1, c =>
    (if c = v then pure () else compactStep L v m c) >>= fun _ => compactLoop v m n (c + 1)

variable {L}

/-- One merge step reads two entries and writes two. -/
theorem wp_mergeStep {s : Memory.State} {u v c : ℕ} (hu : u < L.capacity) (hv : v < L.capacity)
    (hc : c < L.capacity) (hw : L.weight.base + L.weight.length ≤ s.frontier)
    (hfit : Fits w (L.mat s.mem u c + L.mat s.mem v c)) {Q : Unit → Memory.State → ℕ → Prop}
    (hQ : Q () ⟨Function.update (Function.update s.mem ((L.row u).base + c)
      (L.mat s.mem u c + L.mat s.mem v c)) ((L.row c).base + u)
        (L.mat s.mem u c + L.mat s.mem v c), s.frontier⟩ 4) :
    (Memory.spec w).wp charge (mergeStep L u v c) Q s := by
  have h₁ := (Layout.row_base_add_lt hu hc).trans_le hw
  have h₂ := (Layout.row_base_add_lt hv hc).trans_le hw
  have h₃ := (Layout.row_base_add_lt hc hu).trans_le hw
  simp only [mergeStep, wp_lift_bind, wp_lift, StateTransitionSpec.stepFn, step_read, step_write,
    valid_read, valid_write, charge_read, charge_write]
  exact ⟨h₁, h₂, ⟨h₁, hfit⟩, ⟨h₃, hfit⟩, hQ⟩

/-- One compaction step reads one entry and writes two. -/
theorem wp_compactStep {s : Memory.State} {v m c : ℕ} (hv : v < L.capacity) (hm : m < L.capacity)
    (hc : c < L.capacity) (hw : L.weight.base + L.weight.length ≤ s.frontier)
    (hfit : Fits w (L.mat s.mem m c)) {Q : Unit → Memory.State → ℕ → Prop}
    (hQ : Q () ⟨Function.update (Function.update s.mem ((L.row v).base + c) (L.mat s.mem m c))
      ((L.row c).base + v) (L.mat s.mem m c), s.frontier⟩ 3) :
    (Memory.spec w).wp charge (compactStep L v m c) Q s := by
  have h₁ := (Layout.row_base_add_lt hm hc).trans_le hw
  have h₂ := (Layout.row_base_add_lt hv hc).trans_le hw
  have h₃ := (Layout.row_base_add_lt hc hv).trans_le hw
  simp only [compactStep, wp_lift_bind, wp_lift, StateTransitionSpec.stepFn, step_read,
    step_write, valid_read, valid_write, charge_read, charge_write]
  exact ⟨h₁, ⟨h₂, hfit⟩, ⟨h₃, hfit⟩, hQ⟩

/-- Two writes of the same value inside the weight field leave every cell outside it unchanged. -/
theorem update_update_of_not_owns {m : ℕ → ℕ} {i j i' j' : ℕ} (hi : i < L.capacity)
    (hj : j < L.capacity) (hi' : i' < L.capacity) (hj' : j' < L.capacity) (x : ℕ) {a : ℕ}
    (ha : ¬L.weight.Owns a) :
    Function.update (Function.update m ((L.row i).base + j) x) ((L.row i').base + j') x a =
      m a := by
  have hne : ∀ {p q}, p < L.capacity → q < L.capacity → a ≠ (L.row p).base + q :=
    fun hp hq he => ha (he ▸ ⟨by simp only [Layout.row]; omega, Layout.row_base_add_lt hp hq⟩)
  rw [Function.update_of_ne (hne hi' hj'), Function.update_of_ne (hne hi hj)]

/-- **The merge loop.** From the matrix `M` merged up to index `c`, merging `n` more indices
within `k` leaves it merged up to `c + n`, changes no cell outside the weight field, and costs
at most `4 n` memory units. -/
theorem wp_mergeLoop {M : ℕ → ℕ → ℕ} {u v k : ℕ} (hu : u < k) (hv : v < k) (huv : u ≠ v)
    (hk : k ≤ L.capacity) (hfit : ∀ c < k, c ≠ u → c ≠ v → Fits w (M u c + M v c)) :
    ∀ (n c : ℕ) (s : Memory.State), c + n ≤ k → L.weight.base + L.weight.length ≤ s.frontier →
      (∀ i j, i < L.capacity → j < L.capacity → L.mat s.mem i j = mergedTo M u v c i j) →
      (Memory.spec w).wp charge (mergeLoop L u v n c)
        (fun _ s' t => s'.frontier = s.frontier ∧ (∀ a, ¬L.weight.Owns a → s'.mem a = s.mem a) ∧
          (∀ i j, i < L.capacity → j < L.capacity →
            L.mat s'.mem i j = mergedTo M u v (c + n) i j) ∧ t ≤ 4 * n) s
  | 0, c, s, _, _, hmat => ⟨rfl, fun _ _ => rfl, hmat, le_rfl⟩
  | n + 1, c, s, hn, hw, hmat => by
    rw [mergeLoop, wp_bind]
    by_cases hc : c = u ∨ c = v
    · rw [ite_eq_left hc, wp_pure]
      refine wp_mono ?_ (wp_mergeLoop hu hv huv hk hfit n (c + 1) s (by omega) hw
        fun i j hi hj => by rw [hmat i j hi hj, mergedTo_succ_of_mem hc])
      rintro _ s' t ⟨hf, hfr, hm, ht⟩
      exact ⟨hf, hfr, by rwa [show c + (n + 1) = c + 1 + n by omega], by omega⟩
    · rw [ite_eq_right hc]
      have hcu : c ≠ u := fun h => hc (.inl h)
      have hcv : c ≠ v := fun h => hc (.inr h)
      have hck : c < L.capacity := by omega
      have hx : L.mat s.mem u c + L.mat s.mem v c = M u c + M v c := by
        rw [hmat u c (by omega) hck, hmat v c (by omega) hck, mergedTo_left hcu,
          mergedTo_right huv hcu]
      refine wp_mergeStep (by omega) (by omega) hck hw (hx ▸ hfit c (by omega) hcu hcv) ?_
      rw [hx]
      refine wp_mono ?_ (wp_mergeLoop hu hv huv hk hfit n (c + 1) _ (by omega) hw
        fun i j hi hj => ?_)
      · rintro _ s' t ⟨hf, hfr, hm, ht⟩
        refine ⟨hf, fun a ha => ?_, by rwa [show c + (n + 1) = c + 1 + n by omega], by omega⟩
        rw [hfr a ha]
        exact update_update_of_not_owns (by omega) hck hck (by omega) _ ha
      · rw [Layout.mat_update (by omega) _ hj, Layout.mat_update hck _ hj, mergedTo_succ hcu hcv,
          hmat i j hi hj]

/-- **The compaction loop.** From the matrix `M` compacted up to index `c`, compacting `n` more
indices within `m` leaves it compacted up to `c + n`, changes no cell outside the weight field,
and costs at most `3 n` memory units. -/
theorem wp_compactLoop {M : ℕ → ℕ → ℕ} {v m : ℕ} (hv : v < m) (hm : m < L.capacity)
    (hfit : ∀ c < m, c ≠ v → Fits w (M m c)) :
    ∀ (n c : ℕ) (s : Memory.State), c + n ≤ m → L.weight.base + L.weight.length ≤ s.frontier →
      (∀ i j, i < L.capacity → j < L.capacity → L.mat s.mem i j = compactedTo M v m c i j) →
      (Memory.spec w).wp charge (compactLoop L v m n c)
        (fun _ s' t => s'.frontier = s.frontier ∧ (∀ a, ¬L.weight.Owns a → s'.mem a = s.mem a) ∧
          (∀ i j, i < L.capacity → j < L.capacity →
            L.mat s'.mem i j = compactedTo M v m (c + n) i j) ∧ t ≤ 3 * n) s
  | 0, c, s, _, _, hmat => ⟨rfl, fun _ _ => rfl, hmat, le_rfl⟩
  | n + 1, c, s, hn, hw, hmat => by
    rw [compactLoop, wp_bind]
    by_cases hc : c = v
    · rw [ite_eq_left hc, wp_pure]
      refine wp_mono ?_ (wp_compactLoop hv hm hfit n (c + 1) s (by omega) hw
        fun i j hi hj => by rw [hmat i j hi hj, compactedTo_succ_of_eq hc])
      rintro _ s' t ⟨hf, hfr, hmc, ht⟩
      exact ⟨hf, hfr, by rwa [show c + (n + 1) = c + 1 + n by omega], by omega⟩
    · rw [ite_eq_right hc]
      have hck : c < L.capacity := by omega
      have hx : L.mat s.mem m c = M m c := by
        rw [hmat m c hm hck, compactedTo_last (by omega) hc]
      refine wp_compactStep (by omega) hm hck hw (hx ▸ hfit c (by omega) hc) ?_
      rw [hx]
      refine wp_mono ?_ (wp_compactLoop hv hm hfit n (c + 1) _ (by omega) hw fun i j hi hj => ?_)
      · rintro _ s' t ⟨hf, hfr, hmc, ht⟩
        refine ⟨hf, fun a ha => ?_, by rwa [show c + (n + 1) = c + 1 + n by omega], by omega⟩
        rw [hfr a ha]
        exact update_update_of_not_owns (by omega) hck hck (by omega) _ ha
      · rw [Layout.mat_update (by omega) _ hj, Layout.mat_update hck _ hj, compactedTo_succ hc,
          hmat i j hi hj]

/-! ## Contraction -/

variable (L)

/-- Update the total and the degree of `u` for merging `v` into `u`. -/
def mergeDegrees (u v : ℕ) : Prog Unit := do
  let S ← L.total.get 0
  let x ← (L.row u).get v
  let du ← L.degree.get u
  let dv ← L.degree.get v
  L.total.set 0 (S - 2 * x)
  L.degree.set u (du - x + (dv - x))

/-- Move the last supervertex `m` into slot `v`: its degree, then its row and column. -/
def compact (v m : ℕ) : Prog Unit := do
  let d ← L.degree.get m
  L.degree.set v d
  compactLoop L v m m 0

/-- Shrink to `m` supervertices, moving supervertex `m` into slot `v` unless `v` is `m`. -/
def shrink (v m : ℕ) : Prog Unit := do
  L.size.set 0 m
  if v < m then compact L v m else pure ()

/-- **Contraction**: update the total and the degree of `u`, merge `v` into `u`, and move the last
supervertex into slot `v`. -/
def contract (u v : ℕ) : Prog Unit := do
  let k ← L.size.get 0
  mergeDegrees L u v
  mergeLoop L u v k 0
  shrink L v (k - 1)

variable {L}

/-- The degree and total update reads four cells and writes two. -/
theorem wp_mergeDegrees {s : Memory.State} (hs : Inv L w s) {u v : ℕ} (hu : u < L.capacity)
    (hv : v < L.capacity) {S D : ℕ}
    (hS : s.mem L.total.base - 2 * s.mem ((L.row u).base + v) = S)
    (hD : s.mem (L.degree.base + u) - s.mem ((L.row u).base + v) +
      (s.mem (L.degree.base + v) - s.mem ((L.row u).base + v)) = D) (hSf : Fits w S)
    (hDf : Fits w D) {Q : Unit → Memory.State → ℕ → Prop}
    (hQ : Q () ⟨Function.update (Function.update s.mem L.total.base S) (L.degree.base + u) D,
      s.frontier⟩ 6) :
    (Memory.spec w).wp charge (mergeDegrees L u v) Q s := by
  have htt := hs.lt_frontier L.total_mem_footprint
  have hdu := hs.lt_frontier (L.degree_mem_footprint hu)
  simp only [mergeDegrees, wp_lift_bind, wp_lift, StateTransitionSpec.stepFn, step_read,
    step_write, valid_read, valid_write, charge_read, charge_write, Nat.add_zero]
  rw [hS, hD]
  exact ⟨htt, (Layout.row_base_add_lt hu hv).trans_le hs.weight_le, hdu,
    hs.lt_frontier (L.degree_mem_footprint hv), ⟨htt, hSf⟩, ⟨hdu, hDf⟩, hQ⟩

/-- **The compaction phase.** It copies the degree of `m` to slot `v`, moves row and column `m`
into slot `v`, changes no other cell outside the weight field, and costs at most `3 m + 2`. -/
theorem wp_compact {s : Memory.State} {M : ℕ → ℕ → ℕ} {v m : ℕ} (hv : v < m)
    (hm : m < L.capacity) (hlim : L.limit ≤ s.frontier) (hd : Fits w (s.mem (L.degree.base + m)))
    (hfit : ∀ c < m, c ≠ v → Fits w (M m c))
    (hmat : ∀ i j, i < L.capacity → j < L.capacity → L.mat s.mem i j = M i j) :
    (Memory.spec w).wp charge (compact L v m)
      (fun _ s' t => s'.frontier = s.frontier ∧
        (∀ a, ¬L.weight.Owns a → a ≠ L.degree.base + v → s'.mem a = s.mem a) ∧
        s'.mem (L.degree.base + v) = s.mem (L.degree.base + m) ∧
        (∀ i j, i < L.capacity → j < L.capacity → L.mat s'.mem i j = compactedTo M v m m i j) ∧
        t ≤ 3 * m + 2) s := by
  have hdm : L.degree.base + m < s.frontier := by
    simp only [Layout.degree, Layout.limit] at hlim ⊢; nlinarith
  have hdv : L.degree.base + v < s.frontier := by omega
  have hw : L.weight.base + L.weight.length ≤ s.frontier := by
    simp only [Layout.weight, Layout.limit] at hlim ⊢; omega
  have hdvw := L.not_owns_degree (show v < L.capacity by omega)
  simp only [compact, wp_lift_bind, StateTransitionSpec.stepFn, step_read, step_write, valid_read,
    valid_write, charge_read, charge_write]
  refine ⟨hdm, ⟨hdv, hd⟩, wp_mono ?_ (wp_compactLoop hv hm hfit m 0 _ (by omega) hw
    fun i j hi hj => ?_)⟩
  · rintro _ s' t ⟨hf, hfr, hmc, ht⟩
    refine ⟨hf, fun a ha hav => ?_, ?_, by simpa using hmc, by omega⟩
    · exact (hfr a ha).trans (Function.update_of_ne hav _ _)
    · exact (hfr _ hdvw).trans (Function.update_self _ _ _)
  · rw [compactedTo_zero, Layout.mat_update_of_not_owns hdvw _ hi hj, hmat i j hi hj]

/-- **The tail of a contraction.** From the state after the merge, with the total and the degrees
of the merged graph in place, shrinking to `m` supervertices ends in a state satisfying the
invariant that abstracts to `contractMatrix`, and costs at most `3 m + 3`. -/
theorem wp_shrink {s s₂ : Memory.State} (hs : Inv L w s) {m : ℕ}
    {W : Fin (m + 1) → Fin (m + 1) → ℕ} (hW : IsMultigraph W)
    (hWm : ∀ a b : Fin (m + 1), L.mat s.mem a b = W a b) {u v : Fin (m + 1)} (huv : u ≠ v)
    (hk : m + 1 ≤ L.capacity) (hS : Fits w (totalDoubledWeight W))
    (hf : s₂.frontier = s.frontier) (hfr : ∀ a ∉ L.footprint, s₂.mem a = s.mem a)
    (htot : s₂.mem L.total.base = totalDoubledWeight (contractMatrix W u v))
    (hdeg : ∀ a : Fin (m + 1), a ≠ v → s₂.mem (L.degree.base + a) = rowDeg (mergePair W u v) a)
    (hmat : ∀ i j, i < L.capacity → j < L.capacity →
      L.mat s₂.mem i j = mergedTo (L.mat s.mem) u v (m + 1) i j) :
    (Memory.spec w).wp charge (shrink L v m)
      (fun _ s' t => s'.frontier = s.frontier ∧ (∀ a ∉ L.footprint, s'.mem a = s.mem a) ∧
        abs L s' = ⟨m, contractMatrix W u v⟩ ∧ Inv L w s' ∧ t ≤ 3 * m + 3) s₂ := by
  have hlim : L.limit ≤ s₂.frontier := hf ▸ hs.allocated
  have hmerge (a b : Fin (m + 1)) (ha : a ≠ v) (hb : b ≠ v) :
      mergedTo (L.mat s.mem) u v (m + 1) a b = mergePair W u v a b :=
    mergedTo_eq_mergePair hW hWm ha hb
  rw [shrink, wp_lift_bind]
  refine ⟨⟨hs.lt_frontier L.size_mem_footprint |>.trans_eq hf.symm,
    hs.capacity_fits.of_le (by omega)⟩, ?_⟩
  dsimp only [StateTransitionSpec.stepFn, step_write, charge_write, Nat.add_zero]
  -- the state after the size write
  set s₃ : Memory.State := ⟨Function.update s₂.mem L.size.base m, s₂.frontier⟩ with hs₃
  have hsize₃ : s₃.mem L.size.base = m := Function.update_self _ _ _
  have htot₃ : s₃.mem L.total.base = totalDoubledWeight (contractMatrix W u v) :=
    (Function.update_of_ne L.size_ne_total.symm _ _).trans htot
  have hdeg₃ (a : Fin (m + 1)) (ha : a ≠ v) :
      s₃.mem (L.degree.base + a) = rowDeg (mergePair W u v) a :=
    (Function.update_of_ne (L.size_ne_degree a).symm _ _).trans (hdeg a ha)
  have hmat₃ (i j : ℕ) (hi : i < L.capacity) (hj : j < L.capacity) :
      L.mat s₃.mem i j = mergedTo (L.mat s.mem) u v (m + 1) i j := by
    rw [hs₃, Layout.mat_update_of_not_owns L.not_owns_size _ hi hj, hmat i j hi hj]
  have hfr₃ (a : ℕ) (ha : a ∉ L.footprint) : s₃.mem a = s.mem a :=
    (Function.update_of_ne (L.not_owns_of_not_mem ha).2.1 _ _).trans (hfr a ha)
  have hval (i : Fin m) (hiv : (i : ℕ) ≠ v) : embedCompact v i = ⟨i, by omega⟩ :=
    Fin.ext (by rw [val_embedCompact, ite_eq_right hiv])
  by_cases hvm : (v : ℕ) < m
  · rw [ite_eq_left hvm]
    have hlast : (⟨m, by omega⟩ : Fin (m + 1)) ≠ v := Fin.ne_of_val_ne (by simp only; omega)
    have hdm : s₃.mem (L.degree.base + m) = rowDeg (mergePair W u v) ⟨m, by omega⟩ :=
      hdeg₃ _ hlast
    refine wp_mono ?_ (wp_compact (M := mergedTo (L.mat s.mem) u v (m + 1)) hvm (by omega) hlim
      (hdm ▸ hS.of_le (rowDeg_mergePair_le_totalDoubledWeight hW huv hlast))
      (fun c hc hcv => ?_) hmat₃)
    · rintro _ s₄ t₄ ⟨hf₄, hfr₄, hd₄, hm₄, ht₄⟩
      have hdeg₄ (i : Fin m) :
          s₄.mem (L.degree.base + i) = rowDeg (contractMatrix W u v) i := by
        rw [rowDeg_contractMatrix]
        by_cases hiv : (i : ℕ) = v
        · rw [show embedCompact v i = ⟨m, by omega⟩ from
            Fin.ext (by rw [val_embedCompact, ite_eq_left hiv]), ← hdm, hiv, hd₄]
        · rw [hval i hiv, ← hdeg₃ _ (Fin.ne_of_val_ne hiv)]
          exact hfr₄ _ (L.not_owns_degree (by omega)) (by omega)
      obtain ⟨habs₄, hinv₄⟩ := abs_eq_and_inv (s := s₄) (isMultigraph_contractMatrix hW u v)
        (by rw [hf₄]; exact hlim) hs.capacity_fits (show m ≤ L.capacity by omega)
        (by rw [hfr₄ _ L.not_owns_size (L.size_ne_degree v), hsize₃])
        (fun i j => (hm₄ i j (by omega) (by omega)).trans
          (compactedTo_mergedTo_eq_contractMatrix hW hWm huv hvm i j))
        hdeg₄ (by rw [hfr₄ _ L.not_owns_total (L.total_ne_degree v), htot₃])
        (hS.of_le (by have := totalDoubledWeight_contractMatrix hW huv; omega))
      refine ⟨by rw [hf₄, hf], fun a ha => ?_, habs₄, hinv₄, by omega⟩
      have hout := L.not_owns_of_not_mem ha
      rw [hfr₄ a hout.1 (hout.2.2.2 v (by omega)), hfr₃ a ha]
    · have hc' : (⟨c, by omega⟩ : Fin (m + 1)) ≠ v := Fin.ne_of_val_ne hcv
      exact (hmerge _ _ hlast hc').symm ▸
        hS.of_le (mergePair_le_totalDoubledWeight hW huv hlast hc')
  · rw [ite_eq_right hvm, wp_pure]
    obtain ⟨habs₃, hinv₃⟩ := abs_eq_and_inv (s := s₃) (isMultigraph_contractMatrix hW u v)
      hlim hs.capacity_fits (show m ≤ L.capacity by omega) hsize₃
      (fun i j => (hmat₃ i j (by omega) (by omega)).trans
        (mergedTo_eq_contractMatrix hW hWm (by omega) i j))
      (fun i => by
        have hiv : (i : ℕ) ≠ v := by have := i.isLt; omega
        rw [rowDeg_contractMatrix, hval i hiv, ← hdeg₃ _ (Fin.ne_of_val_ne hiv)])
      htot₃ (hS.of_le (by have := totalDoubledWeight_contractMatrix hW huv; omega))
    exact ⟨hf, hfr₃, habs₃, hinv₃, by omega⟩

/-- **Contraction over memory.** On two distinct supervertices `u` and `v`, `contract u v` ends
in a state satisfying the invariant that abstracts to `contractGraph`. It changes no cell outside
the layout and costs at most `7 k + 7` memory units. -/
theorem wp_contract {s : Memory.State} (hs : Inv L w s) {u v : ℕ}
    (hvalid : spec.valid (abs L s) (.contract u v)) :
    (Memory.spec w).wp charge (contract L u v)
      (fun _ s' t => s'.frontier = s.frontier ∧ (∀ a ∉ L.footprint, s'.mem a = s.mem a) ∧
        abs L s' = contractGraph (abs L s) u v ∧ Inv L w s' ∧
        t ≤ 7 * (abs L s).size + 7) s := by
  obtain ⟨hu, hv, huv⟩ := hvalid
  obtain ⟨m, hm⟩ : ∃ m, s.mem L.size.base = m + 1 :=
    ⟨s.mem L.size.base - 1, by simp only [abs_size] at hu; omega⟩
  set W : Fin (m + 1) → Fin (m + 1) → ℕ := fun a b => L.mat s.mem a b with hW_def
  have habs : abs L s = ⟨m + 1, W⟩ := by rw [abs, hm]; rfl
  obtain ⟨-, -, hW, hdeg, htot⟩ := hs.cells habs
  rw [habs] at hu hv ⊢
  simp only at hu hv
  set u' : Fin (m + 1) := ⟨u, hu⟩
  set v' : Fin (m + 1) := ⟨v, hv⟩
  have huv' : u' ≠ v' := Fin.ne_of_val_ne huv
  rw [show contractGraph ⟨m + 1, W⟩ u v = ⟨m, contractMatrix W u' v'⟩ from
    contractGraph_fin W u' v']
  have hk : m + 1 ≤ L.capacity := hm ▸ hs.size_le
  have hS : Fits w (totalDoubledWeight W) := htot ▸ hs.total_fits
  have htot' := totalDoubledWeight_contractMatrix hW huv'
  -- read the size, then update the degrees and the total
  rw [contract, wp_lift_bind]
  refine ⟨hs.lt_frontier L.size_mem_footprint, ?_⟩
  dsimp only [StateTransitionSpec.stepFn, step_read, charge_read, Nat.add_zero]
  rw [hm, Nat.add_sub_cancel, wp_bind]
  have hdu : s.mem (L.degree.base + u) = rowDeg W u' := hdeg u'
  have hdv : s.mem (L.degree.base + v) = rowDeg W v' := hdeg v'
  have hx : s.mem ((L.row u).base + v) = W u' v' := rfl
  refine wp_mergeDegrees hs (by omega) (by omega) (S := totalDoubledWeight (contractMatrix W u' v'))
    (D := rowDeg (mergePair W u' v') u') (by rw [htot, hx]; omega)
    (by rw [hx, hdu, hdv, rowDeg_mergePair_u hW huv', hW.1 v' u'])
    (hS.of_le (by omega)) (hS.of_le (rowDeg_mergePair_le_totalDoubledWeight hW huv' huv')) ?_
  -- merge
  rw [wp_bind]
  refine wp_mono ?_ (wp_mergeLoop (M := L.mat s.mem) hu hv huv hk (fun c hc hcu hcv => ?_)
    (m + 1) 0 _ (by omega) hs.weight_le fun i j hi hj => ?_)
  rotate_left
  · have h := mergePair_le_totalDoubledWeight hW huv' huv' (b := ⟨c, hc⟩) (Fin.ne_of_val_ne hcv)
    rw [mergePair_left huv' (Fin.ne_of_val_ne hcu) (Fin.ne_of_val_ne hcv)] at h
    exact hS.of_le h
  · rw [mergedTo_zero, Layout.mat_update_of_not_owns (L.not_owns_degree (by omega)) _ hi hj,
      Layout.mat_update_of_not_owns L.not_owns_total _ hi hj]
  -- shrink
  rintro _ s₂ t₂ ⟨hf₂, hfr₂, hm₂, ht₂⟩
  refine wp_mono ?_ (wp_shrink hs hW (fun _ _ => rfl) huv' hk hS hf₂ (fun a ha => ?_) ?_ ?_
    (by simpa using hm₂))
  · rintro _ s' t ⟨hf, hfr, habs', hs', ht⟩
    exact ⟨hf, hfr, habs', hs', by omega⟩
  · have hout := L.not_owns_of_not_mem ha
    rw [hfr₂ a hout.1]
    dsimp only
    rw [Function.update_of_ne (hout.2.2.2 u (by omega)), Function.update_of_ne hout.2.2.1]
  · rw [hfr₂ _ L.not_owns_total]
    dsimp only
    rw [Function.update_of_ne (L.total_ne_degree u), Function.update_self]
  · intro a ha
    rw [hfr₂ _ (L.not_owns_degree (by omega))]
    dsimp only
    have hda : s.mem (L.degree.base + a) = rowDeg W a := hdeg a
    by_cases hau : a = u'
    · subst hau
      exact Function.update_self _ _ _
    · rw [Function.update_of_ne (fun h => hau (Fin.ext (show (a : ℕ) = u by omega))),
        Function.update_of_ne (L.total_ne_degree a).symm, hda,
        rowDeg_mergePair_other hW huv' hau ha]

end Cslib.Algorithms.Lean.Karger.Memory
