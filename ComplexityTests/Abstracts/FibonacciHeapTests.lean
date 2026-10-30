/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract tests)

import ComplexityAbstracts.FibonacciHeapAbstract

/-!
# Non-vacuity tests for `ComplexityAbstracts.FibonacciHeapAbstract`

Instantiates both `fibonacciHeap_amortized` and `fibonacciHeap_amortized_reusable` on a concrete
non-empty operation sequence exercising all five priority-queue operations and checks memory
confinement outside `[base, base + 11 * n_max + 1)`.
-/

namespace ComplexityTests.Abstracts.FibonacciHeapTests

open ComplexityAbstracts.FibonacciHeapAbstract

/-- Concrete 6-operation sequence on capacity `n_max = 2` exercising all five `Op` constructors:
two insertions fill all `2` handles with key `30` (and satellite values `100`, `200`), so handle
`0` is guaranteed to hold key `30` regardless of which handle the relational specification
allocated first. -/
def sampleOps : List (Op 2) :=
  [.insert 30 100, .insert 30 200, .decreaseKey 0 10, .get 0, .extractMin, .isEmpty]

theorem sampleOps_valid : ValidSeq 50 500 (emptyQueue 2) sampleOps := by
  refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
  rintro q₁ _ ⟨h₁, _, rfl, rfl⟩
  fin_cases h₁
  · refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
    rintro q₂ _ ⟨h₂, hh₂, rfl, rfl⟩
    fin_cases h₂
    · simp [Function.update] at hh₂
    · refine ⟨⟨30, 100, rfl, by decide⟩, ?_⟩
      exact fun _ _ _ =>
        ⟨trivial, fun _ _ _ => ⟨trivial, fun _ _ _ => ⟨trivial, fun _ _ _ => trivial⟩⟩⟩
  · refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
    rintro q₂ _ ⟨h₂, hh₂, rfl, rfl⟩
    fin_cases h₂
    · refine ⟨⟨30, 200, rfl, by decide⟩, ?_⟩
      exact fun _ _ _ =>
        ⟨trivial, fun _ _ _ => ⟨trivial, fun _ _ _ => ⟨trivial, fun _ _ _ => trivial⟩⟩⟩
    · simp [Function.update] at hh₂

private theorem unchanged_trans {base len : ℕ} {m₁ m₂ m₃ : ℕ → ℕ}
    (h₁ : UnchangedOutside base len m₁ m₂) (h₂ : UnchangedOutside base len m₂ m₃) :
    UnchangedOutside base len m₁ m₃ :=
  fun a ha => (h₂ a ha).trans (h₁ a ha)

private theorem runsOps_unchanged {r n_max w : ℕ} {p : Program r} {base len : ℕ}
    {q q' : Queue n_max} {reg reg' : Fin r → ℕ} {mem mem' : ℕ → ℕ} {ops : List (Op n_max)}
    {total extLog : ℕ}
    (h : RunsOps w p base len q reg mem ops q' reg' mem' total extLog) :
    UnchangedOutside base len mem mem' := by
  induction h with
  | nil => intro _ _; rfl
  | cons _ _ _ _ hmod _ ih => exact unchanged_trans hmod ih

/-- Non-vacuity of `fibonacciHeap_amortized` (`O(1)` fresh initialization): runs `sampleOps` on
`[10, 33)` (`11 * 2 + 1 = 23` words) at word size `10` with sentinel `77` outside `[10, 33)`,
preserving `mem_f 9 = 77` and `mem_f 33 = 77`. -/
example :
    ∃ r, ∃ p_init p_op : Program r, ∃ K t₀ t_init q_f reg_f mem_f t_ops extLog,
      let mem₀ : ℕ → ℕ := fun a => if a < 10 ∨ 33 ≤ a then 77 else 0
      Runs 10 p_init ⟨0, initRegs 2 10, mem₀⟩ t₀ t_init ∧
      (∃ out, step 10 p_init t₀ = .halt out) ∧
      RunsOps 10 p_op 10 23 (emptyQueue 2) t₀.reg t₀.mem sampleOps q_f reg_f mem_f t_ops extLog ∧
      mem_f 9 = 77 ∧
      mem_f 33 = 77 ∧
      t_init + 1 ≤ K ∧
      t_ops ≤ K * (5 + extLog) ∧
      extLog ≤ 2 := by
  obtain ⟨r, p_init, p_op, K, hfib⟩ := fibonacciHeap_amortized
  let mem₀ : ℕ → ℕ := fun a => if a < 10 ∨ 33 ≤ a then 77 else 0
  have hmem : ∀ a, mem₀ a < 2 ^ 10 := fun a => by dsimp only [mem₀]; split_ifs <;> decide
  have hzero : ∀ a, 10 ≤ a → a < 10 + (11 * 2 + 1) → mem₀ a = 0 := fun a h1 h2 => by
    dsimp only [mem₀]
    have : ¬(a < 10 ∨ 33 ≤ a) := by omega
    simp [this]
  obtain ⟨t₀, t_init, q_f, reg_f, mem_f, t_ops, extLog,
      hr₀, hh₀, hu₀, hruns, ht_init, ht_ops, hext⟩ :=
    hfib 2 50 500 10 10 mem₀ sampleOps (by decide) (by decide) (by decide) hmem hzero
      sampleOps_valid
  have hu_all := unchanged_trans hu₀ (runsOps_unchanged hruns)
  have hm9 : mem_f 9 = 77 := hu_all 9 (Or.inl (by decide))
  have hm33 : mem_f 33 = 77 := hu_all 33 (Or.inr (by decide))
  have hlog : Nat.log 2 2 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)
  simp only [sampleOps, numQueries, numInserts, numDecreaseKeys, numExtractMins, hlog]
    at ht_ops hext
  exact ⟨r, p_init, p_op, K, t₀, t_init, q_f, reg_f, mem_f, t_ops, extLog,
    hr₀, hh₀, hruns, hm9, hm33, ht_init, ht_ops, hext⟩

/-- Non-vacuity of `fibonacciHeap_amortized_reusable` (`O(n_max + 1)` clear initialization): runs
`sampleOps` on `[10, 33)` starting from dirty memory `mem₀ = fun _ => 99` everywhere, preserving
`mem_f 9 = 99` and `mem_f 33 = 99`. -/
example :
    ∃ r, ∃ p_init p_op : Program r, ∃ K t₀ t_init q_f reg_f mem_f t_ops extLog,
      Runs 10 p_init ⟨0, initRegs 2 10, fun _ => 99⟩ t₀ t_init ∧
      (∃ out, step 10 p_init t₀ = .halt out) ∧
      RunsOps 10 p_op 10 23 (emptyQueue 2) t₀.reg t₀.mem sampleOps q_f reg_f mem_f t_ops extLog ∧
      mem_f 9 = 99 ∧
      mem_f 33 = 99 ∧
      t_init + 1 ≤ K * 3 ∧
      t_ops ≤ K * (5 + extLog) ∧
      extLog ≤ 2 := by
  obtain ⟨r, p_init, p_op, K, hfib⟩ := fibonacciHeap_amortized_reusable
  obtain ⟨t₀, t_init, q_f, reg_f, mem_f, t_ops, extLog,
      hr₀, hh₀, hu₀, hruns, ht_init, ht_ops, hext⟩ :=
    hfib 2 50 500 10 10 (fun _ => 99) sampleOps (by decide) (by decide) (by decide)
      (fun _ => by decide) sampleOps_valid
  have hu_all := unchanged_trans hu₀ (runsOps_unchanged hruns)
  have hm9 : mem_f 9 = 99 := hu_all 9 (Or.inl (by decide))
  have hm33 : mem_f 33 = 99 := hu_all 33 (Or.inr (by decide))
  have hlog : Nat.log 2 2 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)
  simp only [sampleOps, numQueries, numInserts, numDecreaseKeys, numExtractMins, hlog]
    at ht_ops hext
  exact ⟨r, p_init, p_op, K, t₀, t_init, q_f, reg_f, mem_f, t_ops, extLog,
    hr₀, hh₀, hruns, hm9, hm33, ht_init, ht_ops, hext⟩

end ComplexityTests.Abstracts.FibonacciHeapTests
