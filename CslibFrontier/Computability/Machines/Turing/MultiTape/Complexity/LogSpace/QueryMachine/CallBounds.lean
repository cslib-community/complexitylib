/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.CallSpace

/-!
# Space bounds at every clock of calls and call loops

A space bound for a query machine must hold at every physical clock, including the clocks spent
inside a callee, not only at call boundaries. This file proves such bounds once for the two
shapes that machines built from `Turing.QueryMachine.withCalls` repeat: one state-returning call,
and a counter loop of bounded runs that may stop early. The lemmas are distilled from Christian
Reitwiessner's per-machine proofs of these bounds for block-computation searches, gate vectors,
the packed interpolation loop and the packed tree-evaluation controller.

## Main results

* `Turing.QueryMachine.withCalls_runFrom_call_encoding_le`: every clock of one call is encoded
  in `2 * C + D + 2` bits when both boundary callers fit `C` bits and every callee state fits
  `D` bits.
* `Turing.QueryMachine.exists_runFrom_search_encoding_le`: a counter loop of bounded runs, each
  either advancing the counter or stopping, is one run with the same bound at every clock.
* `Turing.QueryMachine.exists_runFrom_chain_encoding_le`: the same for a loop that never stops
  early.
-/

public section

namespace Turing.QueryMachine

variable {σ τ : Type} (M : QueryMachine σ) (N : QueryMachine τ)
  (request : σ → Option τ) (resume : σ → τ → σ) (w : List Bool)
  (encS : σ ↪ List Bool) (encT : τ ↪ List Bool)

/-- One state-returning call is encoded in `2 * C + D + 2` bits at every clock from its request
through its return, when the requesting and resumed callers fit `C` bits and every callee state
up to the callee's first halt fits `D` bits. -/
theorem withCalls_runFrom_call_encoding_le {s : σ} {start : τ} {T C D : ℕ}
    (hs : M.halted s = false) (hrequest : request s = some start)
    (hpre : ∀ i < T, N.halted (N.runFrom w start i) = false)
    (hhalt : N.halted (N.runFrom w start T) = true)
    (hcaller : (encS s).length ≤ C)
    (hresume : (encS (resume s (N.runFrom w start T))).length ≤ C)
    (hcallee : ∀ i ≤ T, (encT (N.runFrom w start i)).length ≤ D)
    (t : ℕ) (ht : t ≤ T + 2) :
    (encWithCalls encS encT ((M.withCalls N request resume).runFrom w (.inl s) t)).length ≤
      2 * C + D + 2 := by
  by_cases hzero : t = 0
  · subst t
    rw [runFrom_zero, withCalls_encoding_inl_length]
    omega
  by_cases hfinal : t = T + 2
  · subst t
    rw [withCalls_runFrom_call M N request resume w s start T hs hrequest hpre hhalt,
      withCalls_encoding_inl_length]
    omega
  rw [show t = 1 + (t - 1) by omega, runFrom_add,
    show (M.withCalls N request resume).runFrom w (.inl s) 1 = .inr (s, start) from
      withCalls_step_call M N request resume w s start hs hrequest,
    withCalls_runFrom_subroutine_prefix M N request resume w s start (t - 1)
      (fun i hi => hpre i (by omega)),
    withCalls_encoding_inr_length]
  have := hcallee (t - 1) (by omega)
  omega

variable {M} {w}

/-- A counter loop from `lo` towards `hi` is one run whose every clock is encoded in `B` bits.
Each step from `c j` is a run encoded in `B` bits that either advances to `c (j + 1)`, when
`hit j = none`, or stops at `found j a`, when `hit j = some a`. The loop reaches `c hi` with no
hit in between, or stops at the first hit. -/
theorem exists_runFrom_search_encoding_le {α : Type*} (enc : σ ↪ List Bool) {B : ℕ}
    (c : ℕ → σ) (hit : ℕ → Option α) (found : ℕ → α → σ) {lo hi : ℕ} (hle : lo ≤ hi)
    (hlo : (enc (c lo)).length ≤ B)
    (hnone : ∀ j, lo ≤ j → j < hi → hit j = none → ∃ T,
      M.runFrom w (c j) T = c (j + 1) ∧ ∀ t ≤ T, (enc (M.runFrom w (c j) t)).length ≤ B)
    (hsome : ∀ j a, lo ≤ j → j < hi → hit j = some a → ∃ T,
      M.runFrom w (c j) T = found j a ∧ ∀ t ≤ T, (enc (M.runFrom w (c j) t)).length ≤ B) :
    ∃ T, ((M.runFrom w (c lo) T = c hi ∧ ∀ j, lo ≤ j → j < hi → hit j = none) ∨
        ∃ j a, lo ≤ j ∧ j < hi ∧ hit j = some a ∧ M.runFrom w (c lo) T = found j a) ∧
      ∀ t ≤ T, (enc (M.runFrom w (c lo) t)).length ≤ B := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hle
  clear hle
  induction n generalizing lo with
  | zero =>
    refine ⟨0, .inl ⟨rfl, fun j hj hj' => absurd hj' (by omega)⟩, fun t ht => ?_⟩
    rw [Nat.le_zero.mp ht]
    exact hlo
  | succ n ih =>
    have hstep (T : ℕ) (target : σ) (hT : M.runFrom w (c lo) T = target)
        (hTB : ∀ t ≤ T, (enc (M.runFrom w (c lo) t)).length ≤ B) (U : ℕ)
        (hUB : ∀ t ≤ U, (enc (M.runFrom w target t)).length ≤ B) :
        ∀ t ≤ T + U, (enc (M.runFrom w (c lo) t)).length ≤ B := by
      intro t ht
      by_cases htT : t ≤ T
      · exact hTB t htT
      · rw [show t = T + (t - T) by omega, runFrom_add, hT]
        exact hUB (t - T) (by omega)
    cases hj : hit lo with
    | some a =>
      obtain ⟨T, hT, hTB⟩ := hsome lo a le_rfl (by omega) hj
      exact ⟨T, .inr ⟨lo, a, le_rfl, by omega, hj, hT⟩, hTB⟩
    | none =>
      obtain ⟨T, hT, hTB⟩ := hnone lo le_rfl (by omega) hj
      obtain ⟨U, hU, hUB⟩ := ih (lo := lo + 1) (by rw [← hT]; exact hTB T le_rfl)
        (fun j h₁ h₂ => hnone j (by omega) (by omega))
        (fun j a h₁ h₂ => hsome j a (by omega) (by omega))
      rw [show lo + (n + 1) = lo + 1 + n by omega]
      refine ⟨T + U, ?_, hstep T _ hT hTB U hUB⟩
      rw [runFrom_add, hT]
      refine hU.imp (fun h => ⟨h.1, fun j h₁ h₂ => ?_⟩) ?_
      · rcases Nat.eq_or_lt_of_le h₁ with rfl | h₁
        · exact hj
        · exact h.2 j h₁ h₂
      · rintro ⟨j, a, h₁, h₂, h₃, h₄⟩
        exact ⟨j, a, by omega, h₂, h₃, h₄⟩

/-- A loop of runs from `c j` to `c (j + 1)` for `j < n`, each encoded in `B` bits at every
clock, is one run from `c 0` to `c n` encoded in `B` bits at every clock. -/
theorem exists_runFrom_chain_encoding_le (enc : σ ↪ List Bool) {B : ℕ} (c : ℕ → σ) (n : ℕ)
    (h0 : (enc (c 0)).length ≤ B)
    (hstep : ∀ j < n, ∃ T,
      M.runFrom w (c j) T = c (j + 1) ∧ ∀ t ≤ T, (enc (M.runFrom w (c j) t)).length ≤ B) :
    ∃ T, M.runFrom w (c 0) T = c n ∧ ∀ t ≤ T, (enc (M.runFrom w (c 0) t)).length ≤ B := by
  obtain ⟨T, ⟨hT, -⟩ | ⟨_, a, -⟩, hB⟩ :=
    exists_runFrom_search_encoding_le enc c (fun _ => (none : Option Empty)) (fun _ a => a.elim)
      (Nat.zero_le n) h0 (fun j _ hj _ => hstep j hj) (fun _ a => a.elim)
  · exact ⟨T, hT, hB⟩
  · exact a.elim

end Turing.QueryMachine
