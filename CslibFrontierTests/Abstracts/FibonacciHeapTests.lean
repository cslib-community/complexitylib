/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract tests)

import CslibFrontierAbstracts.FibonacciHeapAbstract

/-!
# Non-vacuity tests for `CslibFrontierAbstracts.FibonacciHeapAbstract`

Instantiates both `fibonacciHeap_amortized` and `fibonacciHeap_amortized_reusable` on a concrete
adaptive handle-passing client (`sampleClient` on capacity `n_max = 4`) exercising all five
priority-queue operations—including `decreaseKey` on a non-full heap (`size = 2 < 4`) to a key
strictly above the current global minimum—and checks memory confinement outside
`[base, base + 11 * n_max + 1)`.
-/

namespace ComplexityTests.Abstracts.FibonacciHeapTests

open ComplexityAbstracts.FibonacciHeapAbstract

/-- Concrete 7-operation adaptive client on capacity `n_max = 4` exercising all five `Op`
constructors on a non-full heap (`size ≤ 2 < 4`):
1. `insert 30 100` allocates some handle `h₁`;
2. `insert 10 200` inserts a smaller key `10` while keeping two handles unused;
3. `decreaseKey h₁ 20` lowers `h₁`'s key from `30` to `20` (still strictly above the global minimum
   `10`);
4. `get h₁` queries `h₁`;
5. `decreaseKey h₁ 5` lowers `h₁`'s key below `10`;
6. `extractMin` removes the minimum entry;
7. `isEmpty` queries emptiness. -/
def sampleClient : Client 4 :=
  .step (.insert 30 100) fun
    | none => .done
    | some h₁ =>
      .step (.insert 10 200) fun _ =>
      .step (.decreaseKey h₁ 20) fun () =>
      .step (.get h₁) fun _ =>
      .step (.decreaseKey h₁ 5) fun () =>
      .step .extractMin fun _ =>
      .step .isEmpty fun _ => .done

private theorem size_update_single (h₁ : Fin 4) :
    size (Function.update (emptyQueue 4) h₁ (some (30, 100))) < 4 := by
  fin_cases h₁ <;> decide

theorem sampleClient_valid : ValidClient 50 500 (emptyQueue 4) sampleClient := by
  refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
  rintro q₁ _ ⟨h₁, _, rfl, rfl⟩
  refine ⟨⟨size_update_single h₁, by decide, by decide⟩, ?_⟩
  rintro q₂ _ ⟨h₂, hh₂, rfl, rfl⟩
  have hne : h₁ ≠ h₂ := by
    intro heq
    subst heq
    simp [Function.update] at hh₂
  have hq₂ : Function.update (Function.update (emptyQueue 4) h₁ (some (30, 100))) h₂
      (some (10, 200)) h₁ = some (30, 100) := by
    rw [Function.update_of_ne hne, Function.update_self]
  refine ⟨⟨30, 100, hq₂, by decide⟩, ?_⟩
  rintro q₃ _ ⟨⟨u₀, v₀, hq₂', rfl⟩, rfl⟩
  cases hq₂.symm.trans hq₂'
  refine ⟨trivial, ?_⟩
  rintro _ _ ⟨rfl, rfl⟩
  refine ⟨⟨20, 100, Function.update_self .., by decide⟩, ?_⟩
  exact fun _ _ _ => ⟨trivial, fun _ _ _ => ⟨trivial, fun _ _ _ => trivial⟩⟩

private theorem unchanged_trans {base len : ℕ} {m₁ m₂ m₃ : ℕ → ℕ}
    (h₁ : UnchangedOutside base len m₁ m₂) (h₂ : UnchangedOutside base len m₂ m₃) :
    UnchangedOutside base len m₁ m₃ :=
  fun a ha => (h₂ a ha).trans (h₁ a ha)

private theorem runsClient_unchanged {r n_max w : ℕ} {p : Program r} {base len : ℕ}
    {q q' : Queue n_max} {reg reg' : Fin r → ℕ} {mem mem' : ℕ → ℕ}
    {c : Client n_max} {ops : List (Op n_max)} {total extLog : ℕ}
    (h : RunsClient w p base len q reg mem c ops q' reg' mem' total extLog) :
    UnchangedOutside base len mem mem' := by
  induction h with
  | done => intro _ _; rfl
  | step _ _ _ _ hmod _ ih => exact unchanged_trans hmod ih

private theorem runsClient_sampleClient_trace {r w : ℕ} {p : Program r} {base len : ℕ}
    {reg reg' : Fin r → ℕ} {mem mem' : ℕ → ℕ}
    {ops : List (Op 4)} {q' : Queue 4} {total extLog : ℕ}
    (h : RunsClient w p base len (emptyQueue 4) reg mem sampleClient ops q' reg' mem' total
      extLog) :
    ∃ h₁ : Fin 4,
      ops = [.insert 30 100, .insert 10 200, .decreaseKey h₁ 20, .get h₁, .decreaseKey h₁ 5,
        .extractMin, .isEmpty] := by
  cases h with
  | step _ _ hs₁ _ _ hrest =>
    rcases hs₁ with ⟨h₁, _, rfl, rfl⟩
    cases hrest with
    | step _ _ _ _ _ hrest =>
      cases hrest with
      | step _ _ _ _ _ hrest =>
        cases hrest with
        | step _ _ _ _ _ hrest =>
          cases hrest with
          | step _ _ _ _ _ hrest =>
            cases hrest with
            | step _ _ _ _ _ hrest =>
              cases hrest with
              | step _ _ _ _ _ hrest =>
                cases hrest with
                | done => exact ⟨h₁, rfl⟩

/-- Non-vacuity of `fibonacciHeap_amortized` (`O(1)` fresh initialization): runs adaptive
`sampleClient` on `[10, 55)` (`11 * 4 + 1 = 45` words) at word size `10` with sentinel `77` outside
`[10, 55)`, preserving `mem_f 9 = 77` and `mem_f 55 = 77`. -/
example :
    ∃ r, ∃ p_init p_op : Program r, ∃ K t₀ t_init h₁ ops q_f reg_f mem_f t_ops extLog,
      let mem₀ : ℕ → ℕ := fun a => if a < 10 ∨ 55 ≤ a then 77 else 0
      ops = [.insert 30 100, .insert 10 200, .decreaseKey h₁ 20, .get h₁, .decreaseKey h₁ 5,
        .extractMin, .isEmpty] ∧
      Runs 10 p_init ⟨0, initRegs 4 10, mem₀⟩ t₀ t_init ∧
      (∃ out, step 10 p_init t₀ = .halt out) ∧
      RunsClient 10 p_op 10 45 (emptyQueue 4) t₀.reg t₀.mem sampleClient ops q_f reg_f mem_f
        t_ops extLog ∧
      mem_f 9 = 77 ∧
      mem_f 55 = 77 ∧
      t_init + 1 ≤ K ∧
      t_ops ≤ K * (6 + extLog) ∧
      extLog ≤ 3 := by
  obtain ⟨r, p_init, p_op, K, hfib⟩ := fibonacciHeap_amortized
  let mem₀ : ℕ → ℕ := fun a => if a < 10 ∨ 55 ≤ a then 77 else 0
  have hmem : ∀ a, mem₀ a < 2 ^ 10 := fun a => by dsimp only [mem₀]; split_ifs <;> decide
  have hzero : ∀ a, 10 ≤ a → a < 10 + (11 * 4 + 1) → mem₀ a = 0 := fun a h1 h2 => by
    dsimp only [mem₀]
    have : ¬(a < 10 ∨ 55 ≤ a) := by omega
    simp [this]
  obtain ⟨t₀, t_init, ops, q_f, reg_f, mem_f, t_ops, extLog,
      hr₀, hh₀, hu₀, hruns, ht_init, ht_ops, hext⟩ :=
    hfib 4 50 500 10 10 mem₀ sampleClient (by decide) (by decide) (by decide) hmem hzero
      sampleClient_valid
  obtain ⟨h₁, hops⟩ := runsClient_sampleClient_trace hruns
  have hu_all := unchanged_trans hu₀ (runsClient_unchanged hruns)
  have hm9 : mem_f 9 = 77 := hu_all 9 (Or.inl (by decide))
  have hm55 : mem_f 55 = 77 := hu_all 55 (Or.inr (by decide))
  have hlog : Nat.log 2 4 = 2 := Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)
  simp only [hops, numQueries, numInserts, numDecreaseKeys, numExtractMins, hlog]
    at ht_ops hext
  exact ⟨r, p_init, p_op, K, t₀, t_init, h₁, ops, q_f, reg_f, mem_f, t_ops, extLog,
    hops, hr₀, hh₀, hruns, hm9, hm55, ht_init, ht_ops, hext⟩

/-- Non-vacuity of `fibonacciHeap_amortized_reusable` (`O(n_max + 1)` clear initialization): runs
adaptive `sampleClient` on `[10, 55)` starting from dirty memory `mem₀ = fun _ => 99` everywhere,
preserving `mem_f 9 = 99` and `mem_f 55 = 99`. -/
example :
    ∃ r, ∃ p_init p_op : Program r, ∃ K t₀ t_init h₁ ops q_f reg_f mem_f t_ops extLog,
      ops = [.insert 30 100, .insert 10 200, .decreaseKey h₁ 20, .get h₁, .decreaseKey h₁ 5,
        .extractMin, .isEmpty] ∧
      Runs 10 p_init ⟨0, initRegs 4 10, fun _ => 99⟩ t₀ t_init ∧
      (∃ out, step 10 p_init t₀ = .halt out) ∧
      RunsClient 10 p_op 10 45 (emptyQueue 4) t₀.reg t₀.mem sampleClient ops q_f reg_f mem_f
        t_ops extLog ∧
      mem_f 9 = 99 ∧
      mem_f 55 = 99 ∧
      t_init + 1 ≤ K * 5 ∧
      t_ops ≤ K * (6 + extLog) ∧
      extLog ≤ 3 := by
  obtain ⟨r, p_init, p_op, K, hfib⟩ := fibonacciHeap_amortized_reusable
  obtain ⟨t₀, t_init, ops, q_f, reg_f, mem_f, t_ops, extLog,
      hr₀, hh₀, hu₀, hruns, ht_init, ht_ops, hext⟩ :=
    hfib 4 50 500 10 10 (fun _ => 99) sampleClient (by decide) (by decide) (by decide)
      (fun _ => by decide) sampleClient_valid
  obtain ⟨h₁, hops⟩ := runsClient_sampleClient_trace hruns
  have hu_all := unchanged_trans hu₀ (runsClient_unchanged hruns)
  have hm9 : mem_f 9 = 99 := hu_all 9 (Or.inl (by decide))
  have hm55 : mem_f 55 = 99 := hu_all 55 (Or.inr (by decide))
  have hlog : Nat.log 2 4 = 2 := Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)
  simp only [hops, numQueries, numInserts, numDecreaseKeys, numExtractMins, hlog]
    at ht_ops hext
  exact ⟨r, p_init, p_op, K, t₀, t_init, h₁, ops, q_f, reg_f, mem_f, t_ops, extLog,
    hops, hr₀, hh₀, hruns, hm9, hm55, ht_init, ht_ops, hext⟩

end ComplexityTests.Abstracts.FibonacciHeapTests
