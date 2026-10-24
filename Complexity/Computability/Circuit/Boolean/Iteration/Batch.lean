/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.Iteration.InputTime
public import Complexity.Computability.Circuit.Boolean.Iteration.SharedDictionary
public import Complexity.Computability.Circuit.Replication
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Batched fixed powers with one shared dictionary

A circuit with `r * n` inputs and outputs applies `f^[T]` to each of `r` independent `n`-bit
states (`blockMap`). All members share one checkpoint table: the orbit prefixes of all members
are looked up in one batched dictionary, and each member finishes on its own. For `r ≤ 2 ^ n` and
`0 < L ≤ 2 ^ n` this costs at most `100000 * batchBudget n s (2 ^ n) r L` gates
(`batched_fixed_power`), where
`batchBudget n s M r L = r * L * s + (n + 1) ^ 3 * (r * L + M / L + 1)`;
the storage term `M / L` is paid once rather than `r` times. Balancing `L` gives
`300000 * (r * A + √((n + 1) ^ 3 * 2 ^ n * r * A))` with `A = s + (n + 1) ^ 3`
(`batched_fixed_power_optimized`).

With a separate `m`-bit time for each member, binary powering with the batched powers costs
`m * (100000 * batchBudget n s (2 ^ n) r L + 4 * r * n)` (`batched_variable_time`), and
`m * (300000 * optimizedBatchBudget n s (2 ^ n) r + 4 * r * n)` balanced
(`batched_variable_time_optimized`). These input-time circuits specialize the shared
binary-powering rule in `Iteration.InputTime` to the batched fixed-power circuits proved here.

The circuits are native De Morgan circuits: every NOT, AND and OR gate and every constant is
charged, while wiring and fanout are free. The checkpoints are chosen nonconstructively, so the
circuits exist for each parameter choice; nothing here bounds the time to construct them.

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.batchBudget`: the batched size tradeoff.
* `Cslib.Circuits.Boolean.Iteration.optimizedBatchBudget`: its balanced square-root form.

## Main results

* `Cslib.Circuits.Boolean.Iteration.synthesis_batched_power`: the shared-dictionary construction.
* `Cslib.Circuits.Boolean.Iteration.batched_fixed_power`,
  `Cslib.Circuits.Boolean.Iteration.batched_fixed_power_optimized`: batched fixed powers.
* `Cslib.Circuits.Boolean.Iteration.synthesis_batched_binary_powering`: binary powering of
  batches, with one time per member.
* `Cslib.Circuits.Boolean.Iteration.batched_variable_time`,
  `Cslib.Circuits.Boolean.Iteration.batched_variable_time_optimized`: batched input times.

## References

* Adapted from lean/Proofs/{BatchPowers,BatchVariableTime}.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

variable {n m r a M : ℕ}

/-- The batched tradeoff `r * L * s + (n + 1) ^ 3 * (r * L + M / L + 1)` for `r` trajectories of
`n`-bit states, a transition circuit of size `s`, `M` relevant states and parameter `L`. -/
def batchBudget (n s M r L : ℕ) : ℕ :=
  r * L * s + (n + 1) ^ 3 * (r * L + M / L + 1)

/-- A single trajectory has the fixed-power tradeoff. -/
theorem batchBudget_one (n s M L : ℕ) : batchBudget n s M 1 L = powerBudget n s M L := by
  simp only [batchBudget, powerBudget, Nat.one_mul]

/-- A synthesis of every member's output block gives a circuit for the block map. -/
private theorem exists_circuit_blockMap {k : ℕ} {g : BitString n → BitString k} {C : ℕ}
    (h : Synthesis interpretation (inputs (r * n))
      (⋃ member, wires fun x => g (directProductInput x member)) C) :
    ∃ out : Circuit signature (r * n) (r * k),
      out.Computes interpretation (blockMap g r) ∧ out.size ≤ C := by
  refine (h.mono Set.Subset.rfl ?_ le_rfl).exists_circuit_outputs
  rintro _ ⟨i, rfl⟩
  exact Set.mem_iUnion.mpr ⟨(finProdFinEquiv.symm i).1, (finProdFinEquiv.symm i).2, rfl⟩

/-! ### Batched fixed powers -/

/-- **Shared-dictionary powers.** Let `cp` be injective checkpoints such that every orbit repeats
among its first `L` states or reaches a checkpoint in fewer than `2 L` steps, and let
`2 L ≤ T`. Then `f^[T]` of `r` available states costs one orbit prefix of `2 L` steps per member,
one shared lookup of all prefix states against the `M` checkpoints, and one finishing step and
one checkpoint-free fixed-power circuit per member. -/
theorem synthesis_batched_power (c : Circuit signature n n) (s : Set (BooleanFunction a))
    (init : BitString a → Fin r → BitString n)
    (hi : ∀ member bit, (fun x => init x member bit) ∈ s)
    (hc : ∀ b : Bool, (fun _ : BitString a => b) ∈ s)
    (T L : ℕ) (hL : 0 < L) (hLN : L ≤ 2 ^ n) (hT : 2 * L ≤ T)
    (cp : Fin M → BitString n) (hcp : Function.Injective cp)
    (hcover : ∀ x, FunctionalGraph.Repeats (c.eval interpretation) x L ∨
      ∃ t < 2 * L, ∃ j, (c.eval interpretation)^[t] x = cp j) :
    Synthesis interpretation s
      (⋃ member, wires fun x => (c.eval interpretation)^[T] (init x member))
      (r * (2 * L * c.size) +
        48 * (r * (2 * L + 1) + M + 1) * (Nat.clog 2 (r * (2 * L + 1) + M) + 1) ^ 2 *
          (n + (n + 1) + 1) +
        r * ((2 * L + 1) * (4 * ((n + 2) + n + 1)) + 2 * L * c.size +
          200 * (2 * L + 1) * (n + (n + 2) + 1) ^ 2 + 40000 * powerBudget n c.size 0 L +
          4 * n)) := by
  let f := c.eval interpretation
  let K := 2 * L
  let orbit := fun member => Synthesis.stages (fun j => wires fun x => f^[j] (init x member)) K
  have hall : Synthesis interpretation s (⋃ member, orbit member) (r * (K * c.size)) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using
      Synthesis.iUnion orbit (fun _ => K * c.size)
        fun member => Synthesis.orbit c (fun x => init x member) (hi member) K
  let s1 := s ∪ ⋃ member, orbit member
  let queries : BitString a → Fin (r * (K + 1)) → BitString n := fun x q =>
    f^[(finProdFinEquiv.symm q).2.val] (init x (finProdFinEquiv.symm q).1)
  have hquery (x : BitString a) (member : Fin r) (j : Fin (K + 1)) :
      queries x (finProdFinEquiv (member, j)) = f^[j.val] (init x member) := by
    simp only [queries, Equiv.symm_apply_apply]
  let stored : Fin M → BitString (n + 1) := fun j => Fin.cons true (f^[T - K] (cp j))
  have hdict := synthesis_lookupOr s1 cp stored queries fun q bit =>
    Or.inr (Set.mem_iUnion.mpr ⟨(finProdFinEquiv.symm q).1, Synthesis.subset_stages _
      (Nat.le_of_lt_succ (finProdFinEquiv.symm q).2.isLt) ⟨bit, rfl⟩⟩)
  let s2 := s1 ∪ ⋃ q, wires fun x => lookupOr cp stored (queries x q)
  have hresult (member : Fin r) (j : Fin (K + 1)) (bit : Fin (n + 1)) :
      (fun x => lookupOr cp stored (f^[j.val] (init x member)) bit) ∈ s2 :=
    Or.inr (Set.mem_iUnion.mpr ⟨finProdFinEquiv (member, j), bit, funext fun x => by
      simp only [hquery]⟩)
  obtain ⟨fallback, hfall, hfs⟩ := exists_repeat_power c T L hL hLN hT
  let flags := fun member x (j : Fin (K + 1)) =>
    lookupOr cp stored (f^[j.val] (init x member)) 0
  let payloads := fun member x (j : Fin (K + 1)) (bit : Fin n) =>
    lookupOr cp stored (f^[j.val] (init x member)) bit.succ
  let finished := fun member x => finishHit (w := n + 2) f K (flags member x)
    (payloads member x) (fallback.eval interpretation (init x member))
  have hfinish (member : Fin r) : Synthesis interpretation s2 (wires (finished member))
      ((K + 1) * (4 * ((n + 2) + n + 1)) + K * c.size + 200 * (K + 1) * (n + (n + 2) + 1) ^ 2 +
        fallback.size + 4 * n) :=
    synthesis_finishHit c s2 K (flags member) (payloads member) _
      (fun j => hresult member j 0) (fun j bit => hresult member j bit.succ)
      (fun b => Or.inl (Or.inl (hc b)))
      (Synthesis.circuit (I := interpretation) (s := s2) fallback (fun i x => init x member i)
        fun i => Or.inl (Or.inl (hi member i)))
  have hcorrect (member : Fin r) (x : BitString a) :
      finished member x = f^[T] (init x member) := by
    have hfit : K < 2 ^ (n + 2) := by
      simp only [K, Nat.pow_succ]
      omega
    apply finishHit_correct f T K _ _ _ _ hfit hT
    · intro j hj
      obtain ⟨h, hh, -⟩ := (decide_eq_true_iff.mp hj : ∃ h, cp h = _ ∧ stored h 0 = true)
      funext bit
      change lookupOr cp stored _ bit.succ = _
      rw [lookupOr_of_eq stored hcp hh]
      simp only [stored, Fin.cons_succ, hh]
    · intro hnone
      rcases hcover (init x member) with hr | ⟨t, ht, h, hh⟩
      · exact hfall _ hr
      · have hj := hnone ⟨t, by omega⟩
        simp only [flags, lookupOr, decide_eq_false_iff_not] at hj
        exact absurd ⟨h, hh.symm, rfl⟩ hj
  have hfam := Synthesis.iUnion (fun member => wires (finished member)) _ hfinish
  refine (hall.trans (hdict.trans hfam)).mono Set.Subset.rfl ?_ ?_
  · intro g hg
    obtain ⟨member, bit, rfl⟩ := Set.mem_iUnion.mp hg
    exact Set.mem_iUnion.mpr ⟨member, bit, funext fun x => congrFun (hcorrect member x) bit⟩
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    have hm : (K + 1) * (4 * ((n + 2) + n + 1)) + K * c.size +
        200 * (K + 1) * (n + (n + 2) + 1) ^ 2 + fallback.size + 4 * n ≤
          (2 * L + 1) * (4 * ((n + 2) + n + 1)) + 2 * L * c.size +
            200 * (2 * L + 1) * (n + (n + 2) + 1) ^ 2 + 40000 * powerBudget n c.size 0 L +
              4 * n := by
      simp only [K]
      omega
    have := Nat.mul_le_mul_left r hm
    simp only [K] at this ⊢
    omega

/-- The construction cost is within `100000` times the batched tradeoff. -/
private theorem batch_construction_cost (n s M r L : ℕ) (hrN : r ≤ 2 ^ n) (hL : 0 < L)
    (hLN : L ≤ 2 ^ n) (hM : M ≤ 2 ^ n / L) :
    2 + (r * (2 * L * s) +
        48 * (r * (2 * L + 1) + M + 1) * (Nat.clog 2 (r * (2 * L + 1) + M) + 1) ^ 2 *
          (n + (n + 1) + 1) +
        r * ((2 * L + 1) * (4 * ((n + 2) + n + 1)) + 2 * L * s +
          200 * (2 * L + 1) * (n + (n + 2) + 1) ^ 2 + 40000 * powerBudget n s 0 L + 4 * n)) ≤
      100000 * batchBudget n s (2 ^ n) r L := by
  set N := 2 ^ n with hNdef
  set d := Nat.clog 2 (r * (2 * L + 1) + M)
  set P := (n + 1) ^ 3
  have hN : 1 ≤ N := Nat.one_le_two_pow
  have hMN : M ≤ N := hM.trans (Nat.div_le_self _ _)
  have hd : d ≤ 2 * n + 2 := by
    apply Nat.clog_le_of_le_pow
    have he : 2 ^ (2 * n + 2) = 4 * N * N := by
      rw [hNdef, show 2 * n + 2 = n + n + 2 by omega, pow_add, pow_add]
      ring
    rw [he]
    have hp := Nat.mul_le_mul hrN hLN
    nlinarith
  have hP : 1 ≤ P := Nat.one_le_pow _ _ (by omega)
  have hn1 : n + 1 ≤ P := by
    simpa only [pow_one] using Nat.pow_le_pow_right (show 0 < n + 1 by omega) (by decide : 1 ≤ 3)
  have hn2 : (n + 1) ^ 2 ≤ P := Nat.pow_le_pow_right (by omega) (by decide)
  -- the shared dictionary
  have hwidth : (d + 1) ^ 2 * (n + (n + 1) + 1) ≤ 18 * P := by
    have h1 : (d + 1) ^ 2 ≤ 9 * (n + 1) ^ 2 := by
      have := Nat.pow_le_pow_left (show d + 1 ≤ 3 * (n + 1) by omega) 2
      nlinarith
    calc (d + 1) ^ 2 * (n + (n + 1) + 1) ≤ 9 * (n + 1) ^ 2 * (2 * (n + 1)) := by
          gcongr; omega
      _ = 18 * P := by simp only [P]; ring
  have hrecords : r * (2 * L + 1) + M + 1 ≤ 3 * (r * L) + N / L + 1 := by nlinarith
  have hdict : 48 * (r * (2 * L + 1) + M + 1) * (d + 1) ^ 2 * (n + (n + 1) + 1) ≤
      864 * P * (3 * (r * L) + N / L + 1) := by
    calc 48 * (r * (2 * L + 1) + M + 1) * (d + 1) ^ 2 * (n + (n + 1) + 1)
        = 48 * (r * (2 * L + 1) + M + 1) * ((d + 1) ^ 2 * (n + (n + 1) + 1)) := by ring
      _ ≤ 48 * (3 * (r * L) + N / L + 1) * (18 * P) := by gcongr
      _ = _ := by ring
  -- one member
  have hmember : (2 * L + 1) * (4 * ((n + 2) + n + 1)) +
      200 * (2 * L + 1) * (n + (n + 2) + 1) ^ 2 + 40000 * (P * (L + 0 + 1)) + 4 * n ≤
        85440 * (L * P) := by
    have h1 : (2 * L + 1) * (4 * ((n + 2) + n + 1)) ≤ 36 * (L * P) := by
      have := Nat.mul_le_mul (show 2 * L + 1 ≤ 3 * L by omega)
        (show 4 * ((n + 2) + n + 1) ≤ 12 * P by omega)
      nlinarith
    have h2 : 200 * (2 * L + 1) * (n + (n + 2) + 1) ^ 2 ≤ 5400 * (L * P) := by
      have hs : (n + (n + 2) + 1) ^ 2 ≤ 9 * P := by
        have := Nat.pow_le_pow_left (show n + (n + 2) + 1 ≤ 3 * (n + 1) by omega) 2
        nlinarith
      have := Nat.mul_le_mul (show 2 * L + 1 ≤ 3 * L by omega) hs
      nlinarith
    have h3 : 40000 * (P * (L + 0 + 1)) ≤ 80000 * (L * P) := by nlinarith
    have h4 : 4 * n ≤ 4 * (L * P) := by nlinarith
    omega
  have hmembers := Nat.mul_le_mul_left r hmember
  simp only [powerBudget, Nat.zero_div] at hmembers ⊢
  change _ ≤ 100000 * (r * L * s + P * (r * L + N / L + 1))
  change 2 + (r * (2 * L * s) + 48 * (r * (2 * L + 1) + M + 1) * (d + 1) ^ 2 *
    (n + (n + 1) + 1) + r * ((2 * L + 1) * (4 * ((n + 2) + n + 1)) + 2 * L * s +
      200 * (2 * L + 1) * (n + (n + 2) + 1) ^ 2 + 40000 * (L * s + P * (L + 0 + 1)) +
        4 * n)) ≤ _
  nlinarith [Nat.zero_le (r * L * s), Nat.zero_le (P * (N / L)), Nat.zero_le (r * (L * P))]

/-- **Batched fixed powers.** For `r ≤ 2 ^ n` and `0 < L ≤ 2 ^ n`, some circuit of size at most
`100000 * batchBudget n c.size (2 ^ n) r L` applies `T` steps of `c` to each of `r` independent
states. -/
theorem batched_fixed_power (c : Circuit signature n n) (r T L : ℕ) (hrN : r ≤ 2 ^ n)
    (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit signature (r * n) (r * n),
      out.Computes interpretation (blockMap (c.eval interpretation)^[T] r) ∧
      out.size ≤ 100000 * batchBudget n c.size (2 ^ n) r L := by
  classical
  let f := c.eval interpretation
  by_cases hT : T < 2 * L
  · have h := Synthesis.iUnion (I := interpretation) (s := inputs (r * n))
      (fun member => Synthesis.stages
        (fun j => wires fun x => f^[j] (directProductInput x member)) T)
      (fun _ => T * c.size) fun member => Synthesis.orbit c (fun x => directProductInput x member)
        (fun i => Set.mem_range.mpr ⟨finProdFinEquiv (member, i), rfl⟩) T
    obtain ⟨out, hout, hs⟩ := exists_circuit_blockMap (g := f^[T]) (C := r * (T * c.size)) (by
      refine h.mono Set.Subset.rfl ?_ (by simp)
      intro g hg
      obtain ⟨member, hm⟩ := Set.mem_iUnion.mp hg
      exact Set.mem_iUnion.mpr ⟨member, Synthesis.subset_stages _ le_rfl hm⟩)
    refine ⟨out, hout, hs.trans ?_⟩
    have := Nat.mul_le_mul_left r (Nat.mul_le_mul_right c.size hT.le)
    unfold batchBudget
    nlinarith [Nat.zero_le ((n + 1) ^ 3 * (r * L + 2 ^ n / L + 1))]
  obtain ⟨H, hcard, hcover⟩ := FunctionalGraph.exists_checkpoints_finite f hL
  let cp : Fin H.card → BitString n := fun j => (H.equivFin.symm j).val
  have hcp : Function.Injective cp := fun i j h => H.equivFin.symm.injective (Subtype.ext h)
  have hcov (x : BitString n) : FunctionalGraph.Repeats f x L ∨
      ∃ t < 2 * L, ∃ j, f^[t] x = cp j := by
    rcases hcover x with hrep | ⟨t, ht, hmem⟩
    · exact Or.inl hrep
    · exact Or.inr ⟨t, ht, H.equivFin ⟨_, hmem⟩, by simp [cp]⟩
  let constants : Set (BooleanFunction (r * n)) := {fun _ => false, fun _ => true}
  have hconst : Synthesis interpretation (inputs (r * n)) constants 2 :=
    (Synthesis.const false).union (Synthesis.const true)
  have hs := synthesis_batched_power c (inputs (r * n) ∪ constants)
    (fun x member => directProductInput x member) (fun _ _ => Or.inl ⟨_, rfl⟩)
    (fun b => Or.inr (by cases b <;> simp [constants])) T L hL hLN (by omega) cp hcp hcov
  obtain ⟨out, hout, hsize⟩ := exists_circuit_blockMap (hconst.trans hs)
  refine ⟨out, hout, hsize.trans ?_⟩
  apply batch_construction_cost n c.size H.card r L hrN hL hLN
  simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] using hcard

/-- The balanced batched budget `r * A + √((n + 1) ^ 3 * M * r * A)` with `A = s + (n + 1) ^ 3`. -/
noncomputable def optimizedBatchBudget (n s M r : ℕ) : ℝ :=
  (r * (s + (n + 1) ^ 3) : ℕ) + Real.sqrt ((n + 1 : ℝ) ^ 3 * M * (r * (s + (n + 1) ^ 3) : ℕ))

/-- A single trajectory has the balanced fixed-power budget. -/
theorem optimizedBatchBudget_one (n s M : ℕ) :
    optimizedBatchBudget n s M 1 = optimizedBudget n s M := by
  simp only [optimizedBatchBudget, optimizedBudget, Nat.one_mul]

private theorem exists_batchBudget_le_optimizedBatchBudget (n s M r : ℕ) (hr : 0 < r)
    (hM : M ≤ 2 ^ n) :
    ∃ L : ℕ, 0 < L ∧ L ≤ 2 ^ n ∧
      (batchBudget n s M r L : ℝ) ≤ 3 * optimizedBatchBudget n s M r := by
  have hb : (n + 1) ^ 3 ≤ r * (s + (n + 1) ^ 3) := by
    have := Nat.mul_le_mul_right (s + (n + 1) ^ 3) hr
    omega
  obtain ⟨L, hL, hLN, h⟩ := exists_le_three_mul_add_sqrt (r * (s + (n + 1) ^ 3)) ((n + 1) ^ 3)
    M (2 ^ n) (by positivity) hb hM (by positivity)
  refine ⟨L, hL, hLN, ?_⟩
  have he : batchBudget n s M r L = r * (s + (n + 1) ^ 3) * L + (n + 1) ^ 3 * (M / L + 1) := by
    unfold batchBudget
    ring
  simpa [he, optimizedBatchBudget, Nat.cast_add, Nat.cast_pow] using h

/-- **Square-root batched fixed powers.** -/
theorem batched_fixed_power_optimized (c : Circuit signature n n) (r T : ℕ) (hr : 0 < r)
    (hrN : r ≤ 2 ^ n) :
    ∃ out : Circuit signature (r * n) (r * n),
      out.Computes interpretation (blockMap (c.eval interpretation)^[T] r) ∧
      (out.size : ℝ) ≤ 300000 * optimizedBatchBudget n c.size (2 ^ n) r := by
  obtain ⟨L, hL, hLN, hopt⟩ := exists_batchBudget_le_optimizedBatchBudget n c.size (2 ^ n) r hr
    le_rfl
  obtain ⟨out, hout, hs⟩ := batched_fixed_power c r T L hrN hL hLN
  refine ⟨out, hout, ?_⟩
  have hs' : (out.size : ℝ) ≤ 100000 * (batchBudget n c.size (2 ^ n) r L : ℝ) := by
    exact_mod_cast hs
  linarith

/-! ### Batched input times -/

/-- **Batched input times.** For `r ≤ 2 ^ n` and `0 < L ≤ 2 ^ n`, some circuit of size at most
`m * (100000 * batchBudget n c.size (2 ^ n) r L + 4 * (r * n))` iterates `c` on each of `r`
independent states for that member's own number of steps, given by `m` input bits. -/
theorem batched_variable_time (c : Circuit signature n n) (r m L : ℕ) (hrN : r ≤ 2 ^ n)
    (hL : 0 < L) (hLN : L ≤ 2 ^ n) :
    ∃ out : Circuit signature (r * (n + m)) (r * n),
      out.Computes interpretation (blockMap (inputTimeIterate (c.eval interpretation) m) r) ∧
      out.size ≤ m * (100000 * batchBudget n c.size (2 ^ n) r L + 4 * (r * n)) :=
  exists_circuit_blockMap (synthesis_batched_binary_powering (c.eval interpretation) _
    (fun j _ => batched_fixed_power c r (2 ^ j) L hrN hL hLN) (inputs (r * (n + m)))
    (fun x member i => directProductInput x member (Fin.castAdd m i))
    (fun x member j => directProductInput x member (Fin.natAdd n j))
    (fun _ _ => ⟨_, rfl⟩) fun _ _ => ⟨_, rfl⟩)

/-- **Square-root batched input times.** -/
theorem batched_variable_time_optimized (c : Circuit signature n n) (r m : ℕ) (hr : 0 < r)
    (hrN : r ≤ 2 ^ n) :
    ∃ out : Circuit signature (r * (n + m)) (r * n),
      out.Computes interpretation (blockMap (inputTimeIterate (c.eval interpretation) m) r) ∧
      (out.size : ℝ) ≤ m * (300000 * optimizedBatchBudget n c.size (2 ^ n) r + 4 * (r * n)) := by
  obtain ⟨L, hL, hLN, hopt⟩ := exists_batchBudget_le_optimizedBatchBudget n c.size (2 ^ n) r hr
    le_rfl
  obtain ⟨out, hout, hs⟩ := batched_variable_time c r m L hrN hL hLN
  refine ⟨out, hout, ?_⟩
  have hs' : (out.size : ℝ) ≤
      m * (100000 * (batchBudget n c.size (2 ^ n) r L : ℝ) + 4 * (r * n)) := by
    exact_mod_cast hs
  exact hs'.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

end Cslib.Circuits.Boolean.Iteration
