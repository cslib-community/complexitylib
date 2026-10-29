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
confinement outside `[base, base + 9 n + 1)`.
-/

namespace ComplexityTests.Abstracts.FibonacciHeapTests

open ComplexityAbstracts.FibonacciHeapAbstract

/-- Concrete 6-operation sequence on `Fin 4` exercising all five `Op` constructors. -/
def sampleOps : List (Op 4) :=
  [.insert 2 30, .insert 1 30, .decreaseKey 2 10, .getKey 2, .extractMin, .isEmpty]

theorem sampleOps_valid : ValidSeq 50 (emptyQueue 4) sampleOps := by
  refine ⟨⟨rfl, by decide⟩, ⟨⟨by decide, by decide⟩, ⟨⟨⟨30, rfl, by decide⟩, by decide⟩,
    ⟨trivial, ⟨trivial, ⟨trivial, trivial⟩⟩⟩⟩⟩⟩

private theorem unchanged_trans {base len : ℕ} {m₁ m₂ m₃ : ℕ → ℕ}
    (h₁ : UnchangedOutside base len m₁ m₂) (h₂ : UnchangedOutside base len m₂ m₃) :
    UnchangedOutside base len m₁ m₃ :=
  fun a ha => (h₂ a ha).trans (h₁ a ha)

private theorem runsOps_unchanged {r n w : ℕ} {p : Program r} {base len : ℕ}
    {q : Queue n} {reg reg' : Fin r → ℕ} {mem mem' : ℕ → ℕ} {ops : List (Op n)} {total : ℕ}
    (h : RunsOps w p base len q reg mem ops reg' mem' total) :
    UnchangedOutside base len mem mem' := by
  induction h with
  | nil => intro _ _; rfl
  | cons _ _ _ hmod _ ih => exact unchanged_trans hmod ih

/-- Non-vacuity of `fibonacciHeap_amortized` (`O(1)` fresh initialization): runs `sampleOps` on
`[10, 47)` at word size `10` with sentinel `77` outside `[10, 47)`, preserving `mem_f 9 = 77` and
`mem_f 47 = 77`. -/
example :
    ∃ r, ∃ p_init p_op : Program r, ∃ K t₀ t_init reg_f mem_f t_ops,
      let mem₀ : ℕ → ℕ := fun a => if a < 10 ∨ 47 ≤ a then 77 else 0
      Runs 10 p_init ⟨0, initRegs 4 10, mem₀⟩ t₀ t_init ∧
      (∃ out, step 10 p_init t₀ = .halt out) ∧
      RunsOps 10 p_op 10 37 (emptyQueue 4) t₀.reg t₀.mem sampleOps reg_f mem_f t_ops ∧
      mem_f 9 = 77 ∧
      mem_f 47 = 77 ∧
      t_init + 1 ≤ K ∧
      t_ops ≤ K * 8 := by
  obtain ⟨r, p_init, p_op, K, hfib⟩ := fibonacciHeap_amortized
  let mem₀ : ℕ → ℕ := fun a => if a < 10 ∨ 47 ≤ a then 77 else 0
  have hmem : ∀ a, mem₀ a < 2 ^ 10 := fun a => by dsimp only [mem₀]; split_ifs <;> decide
  have hzero : ∀ a, 10 ≤ a → a < 10 + (9 * 4 + 1) → mem₀ a = 0 := fun a h1 h2 => by
    dsimp only [mem₀]
    have : ¬(a < 10 ∨ 47 ≤ a) := by omega
    simp [this]
  obtain ⟨t₀, t_init, reg_f, mem_f, t_ops, hr₀, hh₀, hu₀, hruns, ht_init, ht_ops⟩ :=
    hfib 4 50 10 10 mem₀ sampleOps (by decide) (by decide) hmem hzero sampleOps_valid
  have hu_all := unchanged_trans hu₀ (runsOps_unchanged hruns)
  have hm9 : mem_f 9 = 77 := hu_all 9 (Or.inl (by decide))
  have hm47 : mem_f 47 = 77 := hu_all 47 (Or.inr (by decide))
  have hlog : Nat.log 2 4 = 2 := Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)
  simp only [sampleOps, numQueries, numInserts, numDecreaseKeys, numExtractMins, hlog] at ht_ops
  exact ⟨r, p_init, p_op, K, t₀, t_init, reg_f, mem_f, t_ops, hr₀, hh₀, hruns,
    hm9, hm47, ht_init, ht_ops⟩

/-- Non-vacuity of `fibonacciHeap_amortized_reusable` (`O(n)` clear initialization): runs
`sampleOps` on `[10, 47)` starting from dirty memory `mem₀ = fun _ => 99` everywhere, preserving
`mem_f 9 = 99` and `mem_f 47 = 99`. -/
example :
    ∃ r, ∃ p_init p_op : Program r, ∃ K t₀ t_init reg_f mem_f t_ops,
      Runs 10 p_init ⟨0, initRegs 4 10, fun _ => 99⟩ t₀ t_init ∧
      (∃ out, step 10 p_init t₀ = .halt out) ∧
      RunsOps 10 p_op 10 37 (emptyQueue 4) t₀.reg t₀.mem sampleOps reg_f mem_f t_ops ∧
      mem_f 9 = 99 ∧
      mem_f 47 = 99 ∧
      t_init + 1 ≤ K * 5 ∧
      t_ops ≤ K * 8 := by
  obtain ⟨r, p_init, p_op, K, hfib⟩ := fibonacciHeap_amortized_reusable
  obtain ⟨t₀, t_init, reg_f, mem_f, t_ops, hr₀, hh₀, hu₀, hruns, ht_init, ht_ops⟩ :=
    hfib 4 50 10 10 (fun _ => 99) sampleOps (by decide) (by decide) (fun _ => by decide)
      sampleOps_valid
  have hu_all := unchanged_trans hu₀ (runsOps_unchanged hruns)
  have hm9 : mem_f 9 = 99 := hu_all 9 (Or.inl (by decide))
  have hm47 : mem_f 47 = 99 := hu_all 47 (Or.inr (by decide))
  have hlog : Nat.log 2 4 = 2 := Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)
  simp only [sampleOps, numQueries, numInserts, numDecreaseKeys, numExtractMins, hlog] at ht_ops
  exact ⟨r, p_init, p_op, K, t₀, t_init, reg_f, mem_f, t_ops, hr₀, hh₀, hruns,
    hm9, hm47, ht_init, ht_ops⟩

end ComplexityTests.Abstracts.FibonacciHeapTests
