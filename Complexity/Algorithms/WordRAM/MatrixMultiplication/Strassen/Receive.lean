/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.Progress
import Mathlib.Tactic.FinCases

/-!
# Native returned-child partial sums

A returned Strassen child contributes to one or two real output quarters. These internal
lemmas compose the actual in-place coefficient loops, derive the next partial sum and
preserve the returned child product. Their footprints protect original inputs and frames.
Every coefficient operation is charged; zero-contribution quarters require no write.
-/

public section

namespace Cslib.Algorithms.WordRAM.Strassen

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- The literal accumulation prefix of each actual return stage, before its next push/pop.
The stage composition theorem accounts for the source's right-associated sequencing. -/
@[expose] def returnedUpdates : Fin 7 → Code .standard 64
  | 0 => .seq (accumulate 0 false) (accumulate 3 false)
  | 1 => .seq (accumulate 2 false) (accumulate 3 true)
  | 2 => .seq (accumulate 1 false) (accumulate 3 false)
  | 3 => .seq (accumulate 0 false) (accumulate 2 false)
  | 4 => .seq (accumulate 0 true) (accumulate 1 false)
  | 5 => accumulate 3 false
  | 6 => accumulate 0 false

/-- Five children require two accumulations; the last two require one each. -/
@[expose] def receiveBudget (phase : Fin 7) (q : ℕ) : ℕ :=
  if phase.val < 5 then 52 * q + 20 else 26 * q + 10

/-- The actual continuation after a returned child's contributions: next child or parent pop. -/
@[expose] def afterReturn : Fin 7 → Code .standard 64
  | 0 => prepareChild 1
  | 1 => prepareChild 2
  | 2 => prepareChild 3
  | 3 => prepareChild 4
  | 4 => prepareChild 5
  | 5 => prepareChild 6
  | 6 => pop

private theorem seq_right {w U T : ℕ} {c₁ c₂ c₃ : Code .standard 64} {x y z : Data 64}
    (h₁ : ExecWithin w (.seq c₁ c₂) x y U) (h₂ : ExecWithin w c₃ y z T) :
    ExecWithin w (.seq c₁ (.seq c₂ c₃)) x z (U + T) := by
  obtain ⟨m, hm, he⟩ := h₁
  obtain ⟨n, hn, hf⟩ := h₂
  cases he with
  | seq ha hb =>
    exact ⟨_, by omega, .seq ha (.seq hb hf)⟩

/-- Reassemble the exact right-associated source stage from its real returned-product
updates and next push/pop. Sequencing changes no charged instruction count. -/
theorem exec_stage_return {w U T : ℕ} (phase : Fin 7) {x y z : Data 64}
    (hupdates : ExecWithin w (returnedUpdates phase) x y U)
    (hafter : ExecWithin w (afterReturn phase) y z T) :
    ExecWithin w (stage ⟨phase.val + 1, by omega⟩) x z (U + T) := by
  fin_cases phase
  all_goals first
    | exact seq_right hupdates hafter
    | exact hupdates.seq hafter

/-- A child with one nonzero output contribution needs exactly one native coefficient loop. -/
theorem exec_receive_one {w p k A B a b out scratch frames frame : ℕ}
    (phase : Fin 7) (t : Fin 4) (subtract : Bool) (x : Data 64) (u v : ℕ → ℤ)
    (hx : NodeHeader p (k + 1) a b out scratch frames frame x)
    (hc : ChildBuffers p k scratch x)
    (hl : NodeLayout p (k + 1) a b out scratch frames frame)
    (hu : ∀ i < 4 ^ (k + 1) * p, (u i).natAbs ≤ A)
    (hv : ∀ i < 4 ^ (k + 1) * p, (v i).natAbs ≤ B)
    (hsign : Cslib.Algorithms.MatrixMultiplication.Strassen.contribution phase t =
      if subtract then -1 else 1)
    (hzero : ∀ s, s ≠ t →
      Cslib.Algorithms.MatrixMultiplication.Strassen.contribution phase s = 0)
    (hout : ∀ s j, j < 4 ^ k * p → x.mem (out + s.val * (4 ^ k * p) + j) = encode
      (Cslib.Algorithms.MatrixMultiplication.Strassen.partialValue p k phase.val u v s j))
    (hprod : ∀ j < 4 ^ k * p, x.mem (scratch + 2 * (4 ^ k * p) + j) = encode
      (Cslib.Algorithms.MatrixMultiplication.Strassen.childProduct p k u v phase j))
    (hmag : GenericRAM.Signed.Fits w (magnitudeBound p A B (k + 1) : ℤ))
    (haddr : Fits (w + 2) (addressBound frames frame (k + 1))) :
    ∃ y, ExecWithin (w + 2) (accumulate t.val subtract) x y (26 * (4 ^ k * p) + 10) ∧
      NodeHeader p (k + 1) a b out scratch frames frame y ∧
      ChildBuffers p k scratch y ∧
      (∀ s j, j < 4 ^ k * p → y.mem (out + s.val * (4 ^ k * p) + j) = encode
        (Cslib.Algorithms.MatrixMultiplication.Strassen.partialValue
          p k (phase.val + 1) u v s j)) ∧
      (∀ j < 4 ^ k * p, y.mem (scratch + 2 * (4 ^ k * p) + j) = encode
        (Cslib.Algorithms.MatrixMultiplication.Strassen.childProduct p k u v phase j)) ∧
      ∀ d, (d < out ∨ out + 4 ^ (k + 1) * p ≤ d) → y.mem d = x.mem d := by
  obtain ⟨y, hy, yh, yc, values, productValues, memory⟩ := exec_accumulate_progress
    phase (fun _ => false) t subtract x u v hx hc hl hu hv rfl hsign
    (by simpa only [progressValue, Bool.false_eq_true, ite_false] using hout) hprod hmag haddr
  refine ⟨y, hy, yh, yc, ?_, productValues, ?_⟩
  · intro s j hj
    rw [values s j hj, progressValue_eq_next]
    intro hd
    apply hzero s
    intro he
    subst s
    simp only [Function.update_self] at hd
    contradiction
  · intro d hd
    apply memory d
    have ht := Nat.mul_le_mul_right (4 ^ k * p) (Nat.succ_le_of_lt t.isLt)
    rw [Nat.succ_mul] at ht
    have hsize : 4 ^ (k + 1) * p = 4 * (4 ^ k * p) := by rw [pow_succ]; ring
    rw [hsize] at hd
    omega

/-- A child with two distinct nonzero output contributions executes both actual loops.
The second loop uses the first loop's real final state, product and register frame. -/
theorem exec_receive_two {w p k A B a b out scratch frames frame : ℕ}
    (phase : Fin 7) (t₁ t₂ : Fin 4) (subtract₁ subtract₂ : Bool)
    (x : Data 64) (u v : ℕ → ℤ)
    (hx : NodeHeader p (k + 1) a b out scratch frames frame x)
    (hc : ChildBuffers p k scratch x)
    (hl : NodeLayout p (k + 1) a b out scratch frames frame)
    (hu : ∀ i < 4 ^ (k + 1) * p, (u i).natAbs ≤ A)
    (hv : ∀ i < 4 ^ (k + 1) * p, (v i).natAbs ≤ B)
    (hne : t₂ ≠ t₁)
    (hsign₁ : Cslib.Algorithms.MatrixMultiplication.Strassen.contribution phase t₁ =
      if subtract₁ then -1 else 1)
    (hsign₂ : Cslib.Algorithms.MatrixMultiplication.Strassen.contribution phase t₂ =
      if subtract₂ then -1 else 1)
    (hzero : ∀ s, s ≠ t₁ → s ≠ t₂ →
      Cslib.Algorithms.MatrixMultiplication.Strassen.contribution phase s = 0)
    (hout : ∀ s j, j < 4 ^ k * p → x.mem (out + s.val * (4 ^ k * p) + j) = encode
      (Cslib.Algorithms.MatrixMultiplication.Strassen.partialValue p k phase.val u v s j))
    (hprod : ∀ j < 4 ^ k * p, x.mem (scratch + 2 * (4 ^ k * p) + j) = encode
      (Cslib.Algorithms.MatrixMultiplication.Strassen.childProduct p k u v phase j))
    (hmag : GenericRAM.Signed.Fits w (magnitudeBound p A B (k + 1) : ℤ))
    (haddr : Fits (w + 2) (addressBound frames frame (k + 1))) :
    ∃ y, ExecWithin (w + 2) (.seq (accumulate t₁.val subtract₁)
        (accumulate t₂.val subtract₂)) x y (52 * (4 ^ k * p) + 20) ∧
      NodeHeader p (k + 1) a b out scratch frames frame y ∧
      ChildBuffers p k scratch y ∧
      (∀ s j, j < 4 ^ k * p → y.mem (out + s.val * (4 ^ k * p) + j) = encode
        (Cslib.Algorithms.MatrixMultiplication.Strassen.partialValue
          p k (phase.val + 1) u v s j)) ∧
      (∀ j < 4 ^ k * p, y.mem (scratch + 2 * (4 ^ k * p) + j) = encode
        (Cslib.Algorithms.MatrixMultiplication.Strassen.childProduct p k u v phase j)) ∧
      ∀ d, (d < out ∨ out + 4 ^ (k + 1) * p ≤ d) → y.mem d = x.mem d := by
  obtain ⟨s, hs, sh, sc, values₁, product₁, memory₁⟩ := exec_accumulate_progress
    phase (fun _ => false) t₁ subtract₁ x u v hx hc hl hu hv rfl hsign₁
    (by simpa only [progressValue, Bool.false_eq_true, ite_false] using hout) hprod hmag haddr
  obtain ⟨y, hy, yh, yc, values₂, product₂, memory₂⟩ := exec_accumulate_progress
    phase (Function.update (fun _ => false) t₁ true) t₂ subtract₂ s u v sh sc hl hu hv
    (by simp only [Function.update_of_ne hne]) hsign₂ values₁ product₁ hmag haddr
  refine ⟨y, (hs.seq hy).mono (by omega), yh, yc, ?_, product₂, ?_⟩
  · intro t j hj
    rw [values₂ t j hj, progressValue_eq_next]
    intro hd
    apply hzero t
    · intro he
      subst t
      simp only [Function.update_of_ne (Ne.symm hne), Function.update_self] at hd
      contradiction
    · intro he
      subst t
      simp only [Function.update_self] at hd
      contradiction
  · intro d hd
    have ht₁ := Nat.mul_le_mul_right (4 ^ k * p) (Nat.succ_le_of_lt t₁.isLt)
    have ht₂ := Nat.mul_le_mul_right (4 ^ k * p) (Nat.succ_le_of_lt t₂.isLt)
    rw [Nat.succ_mul] at ht₁ ht₂
    have hsize : 4 ^ (k + 1) * p = 4 * (4 ^ k * p) := by rw [pow_succ]; ring
    rw [hsize] at hd
    exact (memory₂ d (by omega)).trans (memory₁ d (by omega))

/-- All seven literal return prefixes advance the existing finite partial-sum invariant.
The exact twelve coefficient loops, rather than fourteen uniform worst cases, are charged. -/
theorem exec_returnedUpdates {w p k A B a b out scratch frames frame : ℕ}
    (phase : Fin 7) (x : Data 64) (u v : ℕ → ℤ)
    (hx : NodeHeader p (k + 1) a b out scratch frames frame x)
    (hc : ChildBuffers p k scratch x)
    (hl : NodeLayout p (k + 1) a b out scratch frames frame)
    (hu : ∀ i < 4 ^ (k + 1) * p, (u i).natAbs ≤ A)
    (hv : ∀ i < 4 ^ (k + 1) * p, (v i).natAbs ≤ B)
    (hout : ∀ s j, j < 4 ^ k * p → x.mem (out + s.val * (4 ^ k * p) + j) = encode
      (Cslib.Algorithms.MatrixMultiplication.Strassen.partialValue p k phase.val u v s j))
    (hprod : ∀ j < 4 ^ k * p, x.mem (scratch + 2 * (4 ^ k * p) + j) = encode
      (Cslib.Algorithms.MatrixMultiplication.Strassen.childProduct p k u v phase j))
    (hmag : GenericRAM.Signed.Fits w (magnitudeBound p A B (k + 1) : ℤ))
    (haddr : Fits (w + 2) (addressBound frames frame (k + 1))) :
    ∃ y, ExecWithin (w + 2) (returnedUpdates phase) x y (receiveBudget phase (4 ^ k * p)) ∧
      NodeHeader p (k + 1) a b out scratch frames frame y ∧
      ChildBuffers p k scratch y ∧
      (∀ s j, j < 4 ^ k * p → y.mem (out + s.val * (4 ^ k * p) + j) = encode
        (Cslib.Algorithms.MatrixMultiplication.Strassen.partialValue
          p k (phase.val + 1) u v s j)) ∧
      (∀ j < 4 ^ k * p, y.mem (scratch + 2 * (4 ^ k * p) + j) = encode
        (Cslib.Algorithms.MatrixMultiplication.Strassen.childProduct p k u v phase j)) ∧
      ∀ d, (d < out ∨ out + 4 ^ (k + 1) * p ≤ d) → y.mem d = x.mem d := by
  fin_cases phase
  all_goals simp only [returnedUpdates, receiveBudget]
  all_goals first
    | exact exec_receive_two 0 0 3 false false x u v hx hc hl hu hv
        (by decide) (by decide) (by decide) (by decide) hout hprod hmag haddr
    | exact exec_receive_two 1 2 3 false true x u v hx hc hl hu hv
        (by decide) (by decide) (by decide) (by decide) hout hprod hmag haddr
    | exact exec_receive_two 2 1 3 false false x u v hx hc hl hu hv
        (by decide) (by decide) (by decide) (by decide) hout hprod hmag haddr
    | exact exec_receive_two 3 0 2 false false x u v hx hc hl hu hv
        (by decide) (by decide) (by decide) (by decide) hout hprod hmag haddr
    | exact exec_receive_two 4 0 1 true false x u v hx hc hl hu hv
        (by decide) (by decide) (by decide) (by decide) hout hprod hmag haddr
    | exact exec_receive_one 5 3 false x u v hx hc hl hu hv
        (by decide) (by decide) hout hprod hmag haddr
    | exact exec_receive_one 6 0 false x u v hx hc hl hu hv
        (by decide) (by decide) hout hprod hmag haddr

end Cslib.Algorithms.WordRAM.Strassen
