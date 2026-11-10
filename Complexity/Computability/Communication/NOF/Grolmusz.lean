/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Communication.NOF.GeneralizedInnerProduct

/-!
# Grolmusz's protocol for the generalized inner product

The Babai–Nisan–Szegedy bound (`NOF.Protocol.two_mul_le_four_pow_mul_of_ecomplexityFun_gip_le`)
says that `k` players need `Ω(n / 4 ^ k)` bits to compute the generalized inner product of `n`-bit
strings. Grolmusz [Grolmusz1994] showed that the exponential decay in `k` is real: there is a
deterministic number-on-forehead protocol with `O(k n / 2 ^ k)` bits. We formalize such a
protocol for the players `Fin (k + 1)`, writing `x i r` for the `r`-th bit of player `i`.

**One block of columns.** Think of the input as a `(k + 1) × n` matrix with columns `x · r`, and
suppose fewer than `2 ^ k` columns. Player `0` sees rows `1, …, k`, so it can name a pattern
`z ∈ {0, 1} ^ k` that no column shows on these rows. Let `w t` be the pattern that is `1` on rows
`1, …, t` and agrees with `z` on the others (`NOF.Grolmusz.chain`), so `w 0 = z` and `w k` is all
ones. For `t < k`, player `t + 1` (who sees every row but row `t + 1`) writes the parity of the
number of columns that are `1` on row `0` and agree with `w t` on all rows but `t + 1`, or `0` if
`z` already has a `1` on row `t + 1`. A column with `x 0 r = 1` is counted by player `t + 1`
exactly when it agrees with exactly one of `w t` and `w (t + 1)`, so the `k` bits add up to
`[column = (1, z)] + [column = all ones]` for each column (`NOF.Grolmusz.sum_chainTerm`). No column
equals `(1, z)`, so the bits add up to the generalized inner product.

**Many blocks.** Split the columns into `B` blocks of fewer than `2 ^ k` columns. Player `0` names
a pattern for every block, `k B` bits, and then each player `t + 1` writes a single bit, the sum
over all blocks of its bits above. This is `k (B + 1)` bits
(`NOF.Grolmusz.ecomplexityFun_gip_le_of_block`), and with `n ≤ B (2 ^ k - 1)` blocks of
consecutive columns, `k (n / (2 ^ k - 1) + 2)` bits (`NOF.Grolmusz.ecomplexityFun_gip_le`). This is
`O(k n / 2 ^ k + k)`, against the lower bound `2 n ≤ 4 ^ (k + 1) c`.

We could not consult the original paper, so we do not claim that its protocol or constant is
exactly the one formalized here. What we prove is the bound stated above, which has the
`O(k n / 2 ^ k)` form that Grolmusz's result is cited for.

## Main definitions

* `Cslib.Communication.NOF.Protocol.grolmusz`: the protocol, for an assignment of the columns to
  blocks.

## Main results

* `Cslib.Communication.NOF.Grolmusz.run_grolmusz`: the protocol computes the generalized inner
  product when every block has fewer than `2 ^ k` columns.
* `Cslib.Communication.NOF.Grolmusz.ecomplexityFun_gip_le_of_block`,
  `Cslib.Communication.NOF.Grolmusz.ecomplexityFun_gip_le_of_le_mul`,
  `Cslib.Communication.NOF.Grolmusz.ecomplexityFun_gip_le`: the upper bounds `k (B + 1)` and
  `k (n / (2 ^ k - 1) + 2)`.

## References

* [V. Grolmusz, *The BNS lower bound for multi-party protocols is nearly optimal*][Grolmusz1994]
* [L. Babai, N. Nisan and M. Szegedy, *Multiparty protocols, pseudorandom generators for logspace,
  and time-space trade-offs*][BabaiNisanSzegedy1992]
-/

public section

namespace Cslib.Communication.NOF.Grolmusz

open Finset

variable {k : ℕ}

/-! ### One column -/

/-- The pattern `w t` on rows `1, …, k` (indexed by `Fin k`): `1` on the first `t` rows, `z` on
the others. -/
def chain (z : Fin k → Bool) (t : ℕ) (l : Fin k) : Bool :=
  decide ((l : ℕ) < t) || z l

/-- What player `t + 1` counts for a column `(c₀, c)`: whether `z t = 0`, `c₀ = 1` and `c` agrees
with `chain z t` off row `t`. -/
def chainTerm (z : Fin k → Bool) (c₀ : Bool) (c : Fin k → Bool) (t : Fin k) : Bool :=
  !z t && c₀ && decide (∀ l, l ≠ t → c l = chain z t l)

/-- A product of bits over a finite type is their conjunction. -/
private theorem prod_bool_eq_decide {α : Type*} [Fintype α] (f : α → Bool) :
    ∏ a, f a = decide (∀ a, f a = true) := by
  classical
  by_cases h : ∀ a, f a = true
  · rw [decide_eq_true h, Finset.prod_eq_one fun a _ => h a]
    rfl
  · obtain ⟨a, ha⟩ := not_forall.mp h
    rw [decide_eq_false h, Finset.prod_eq_zero (mem_univ a) (Bool.eq_false_iff.mpr ha)]
    rfl

/-- In the two-element Boolean ring, where `a - b = a + b`, adjacent sums telescope. -/
private theorem sum_range_add_succ (f : ℕ → Bool) (m : ℕ) :
    ∑ t ∈ range m, (f t + f (t + 1)) = f 0 + f m := by
  have h := Finset.sum_range_sub f m
  simp only [BooleanRing.sub_eq_add] at h
  rw [add_comm (f m)] at h
  rw [← h]
  exact Finset.sum_congr rfl fun t _ => add_comm _ _

/-- One step of the chain: player `t + 1` counts a column exactly when it agrees with exactly one
of `w t` and `w (t + 1)`. -/
theorem chainTerm_eq (z : Fin k → Bool) (c₀ : Bool) (c : Fin k → Bool) (t : Fin k) :
    chainTerm z c₀ c t =
      (c₀ && decide (c = chain z t)) + (c₀ && decide (c = chain z (t + 1))) := by
  have hoff : ∀ l, l ≠ t → chain z (t + 1) l = chain z t l := by
    intro l hl
    have : (l : ℕ) ≠ t := fun h => hl (Fin.ext h)
    simp only [chain]
    congr 1
    by_cases h : (l : ℕ) < t
    · simp [h, Nat.lt_succ_of_lt h]
    · simp only [h, decide_false, decide_eq_false_iff_not]
      omega
  have ht : chain z t t = z t := by simp [chain]
  have ht' : chain z (t + 1) t = true := by simp [chain]
  -- Split the agreement with a chain pattern into row `t` and the other rows.
  have split : ∀ w : Fin k → Bool, c = w ↔ c t = w t ∧ ∀ l, l ≠ t → c l = w l := by
    intro w
    constructor
    · rintro rfl
      exact ⟨rfl, fun _ _ => rfl⟩
    · rintro ⟨h₁, h₂⟩
      funext l
      by_cases hl : l = t
      · rw [hl, h₁]
      · exact h₂ l hl
  have h₁ : (c = chain z (t + 1)) ↔ c t = true ∧ ∀ l, l ≠ t → c l = chain z t l := by
    rw [split, ht']
    exact and_congr_right fun _ => forall_congr' fun l => imp_congr_right fun hl => by
      rw [hoff l hl]
  have h₀ : (c = chain z t) ↔ c t = z t ∧ ∀ l, l ≠ t → c l = chain z t l := by
    rw [split, ht]
  simp only [chainTerm, decide_eq_decide.mpr h₀, decide_eq_decide.mpr h₁, Bool.decide_and]
  generalize decide (∀ l, l ≠ t → c l = chain z t l) = P
  cases z t <;> cases c₀ <;> cases c t <;> cases P <;> rfl

/-- **The chain telescopes**: for a column `(c₀, c)` that is not `(1, z)`, the bits of the players
`1, …, k` add up to whether the column is all ones. -/
theorem sum_chainTerm (z : Fin k → Bool) (c₀ : Bool) (c : Fin k → Bool) (hc : c ≠ z) :
    ∑ t, chainTerm z c₀ c t = c₀ * ∏ l, c l := by
  set E : ℕ → Bool := fun t => c₀ && decide (c = chain z t) with hE
  have hsum : ∑ t, chainTerm z c₀ c t = ∑ t ∈ range k, (E t + E (t + 1)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun t => E t + E (t + 1))]
    exact Finset.sum_congr rfl fun t _ => chainTerm_eq z c₀ c t
  have h0 : E 0 = false := by
    have : chain z 0 = z := funext fun l => by simp [chain]
    simp [hE, this, hc]
  have hk : E k = c₀ * ∏ l, c l := by
    have : chain z k = fun _ => true := funext fun l => by simp [chain, l.isLt]
    rw [prod_bool_eq_decide]
    simp only [hE, this, Bool.mul_eq_and]
    congr 1
  rw [hsum, sum_range_add_succ, h0, hk]
  exact zero_add _

/-! ### Player `0`'s patterns -/

/-- A pattern on rows `1, …, k` that no column of `S` shows, if there is one: what player `0`
names for a block `S` of columns, seeing the rows `y : Fin k → BitString n`. -/
noncomputable def missing {n : ℕ} (y : Fin k → BitString n) (S : Finset (Fin n)) : Fin k → Bool :=
  open Classical in
  if h : ∃ z : Fin k → Bool, ∀ r ∈ S, (fun l => y l r) ≠ z then h.choose else fun _ => false

/-- A block of fewer than `2 ^ k` columns misses a pattern. -/
theorem missing_spec {n : ℕ} (y : Fin k → BitString n) {S : Finset (Fin n)} (hS : #S < 2 ^ k) :
    ∀ r ∈ S, (fun l => y l r) ≠ missing y S := by
  have h : ∃ z : Fin k → Bool, ∀ r ∈ S, (fun l => y l r) ≠ z := by
    classical
    have hcard : #(S.image fun r l => y l r) < #(univ : Finset (Fin k → Bool)) := by
      rw [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      exact card_image_le.trans_lt hS
    obtain ⟨z, -, hz⟩ := exists_mem_notMem_of_card_lt_card hcard
    exact ⟨z, fun r hr h => hz (mem_image.mpr ⟨r, hr, h⟩)⟩
  unfold missing
  split
  · next h' => exact h'.choose_spec
  · next h' => exact absurd h h'

/-! ### The protocol -/

variable {n B : ℕ}

/-- Player `t + 1`'s bit, seeing `v`, when player `0` named the patterns `pat`: the sum over the
columns `r` of `chainTerm (pat (blk r)) (x 0 r) (x · r) t`, where player `t + 1` reads `x 0 r` and
`x (l + 1) r` for `l ≠ t` from `v`, and the row `x (t + 1)` it does not see does not matter. -/
def chainBit (blk : Fin n → Fin B) (pat : Fin B → Fin k → Bool) (t : Fin k)
    (v : View (fun _ : Fin (k + 1) => BitString n) t.succ) : Bool :=
  ∑ r, (!pat (blk r) t && v ⟨0, (Fin.succ_ne_zero t).symm⟩ r &&
    decide (∀ l : Fin k, ∀ hl : l ≠ t,
      v ⟨l.succ, fun h => hl (Fin.succ_injective _ h)⟩ r = chain (pat (blk r)) t l))

end Cslib.Communication.NOF.Grolmusz

namespace Cslib.Communication.NOF.Protocol

open Finset Grolmusz

variable {k n B : ℕ}

/-- **Grolmusz's protocol** for the generalized inner product, for an assignment `blk` of the
columns to `B` blocks. Player `0` writes, for every block, a pattern (`Grolmusz.missing`) that no
column of the block shows on rows `1, …, k`, in `k B` bits. Then each player `t + 1` writes the
bit `Grolmusz.chainBit`, and the output is the sum of these `k` bits. -/
noncomputable def grolmusz (blk : Fin n → Fin B) :
    Protocol (fun _ : Fin (k + 1) => BitString n) Bool :=
  open Classical in
  sendBits 0 (B * k)
    (fun v j => missing (fun l => v ⟨l.succ, Fin.succ_ne_zero l⟩)
      (univ.filter (blk · = (finProdFinEquiv.symm j).1)) (finProdFinEquiv.symm j).2)
    fun m => sendEach k Fin.succ
      (chainBit blk fun b l => m (finProdFinEquiv (b, l)))
      fun bits => output (∑ t, bits t)

end Cslib.Communication.NOF.Protocol

namespace Cslib.Communication.NOF.Grolmusz

open Finset

variable {k n B : ℕ}

/-- **Grolmusz's protocol is correct** when every block has fewer than `2 ^ k` columns. -/
theorem run_grolmusz (blk : Fin n → Fin B) (hblk : ∀ b, #(univ.filter (blk · = b)) < 2 ^ k) :
    (Protocol.grolmusz (k := k) blk).run = gip := by
  funext x
  simp only [Protocol.grolmusz, Protocol.run_sendBits, Protocol.run_sendEach,
    Protocol.run_output, Equiv.symm_apply_apply]
  simp only [chainBit, gip, view_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Fin.prod_univ_succ]
  -- Player `0` named for the block of `r` a pattern that column `r` does not show.
  have hr : (fun l => x l.succ r) ≠ missing (fun l => x l.succ) {r' | blk r' = blk r} :=
    missing_spec (fun l => x l.succ) (hblk (blk r)) r (by simp)
  exact (Finset.sum_congr rfl fun t _ => rfl).trans (sum_chainTerm _ (x 0 r) _ hr)

/-- Grolmusz's protocol writes `k B` bits for the patterns and `k` bits for the chain. -/
theorem depth_grolmusz_le (blk : Fin n → Fin B) :
    (Protocol.grolmusz (k := k) blk).depth ≤ k * (B + 1) := by
  have h := Protocol.depth_sendBits_le (i := (0 : Fin (k + 1))) (n := B * k) (d := k + 0)
    (msg := fun v j => missing (fun l => v ⟨l.succ, Fin.succ_ne_zero l⟩)
      (univ.filter (blk · = (finProdFinEquiv.symm j).1)) (finProdFinEquiv.symm j).2)
    (cont := fun m => Protocol.sendEach k Fin.succ
      (chainBit blk fun b l => m (finProdFinEquiv (b, l)))
      fun bits => Protocol.output (∑ t, bits t))
    fun m => Protocol.depth_sendEach_le fun bits => by simp
  calc (Protocol.grolmusz (k := k) blk).depth ≤ B * k + (k + 0) := h
    _ = k * (B + 1) := by ring

/-- **Grolmusz's upper bound, block form** [Grolmusz1994]: if the `n` columns are split into `B`
blocks of fewer than `2 ^ k` columns each, then `k + 1` players compute the generalized inner
product of `n`-bit strings with `k (B + 1)` bits. -/
theorem ecomplexityFun_gip_le_of_block (blk : Fin n → Fin B)
    (hblk : ∀ b, #(univ.filter (blk · = b)) < 2 ^ k) :
    Protocol.ecomplexityFun (gip : (Fin (k + 1) → BitString n) → Bool) ≤ (k * (B + 1) : ℕ) :=
  Protocol.ecomplexityFun_le_iff.mpr ⟨_, run_grolmusz blk hblk, depth_grolmusz_le blk⟩

/-- **Grolmusz's upper bound** [Grolmusz1994]: if `n ≤ B (2 ^ k - 1)`, then `k + 1` players
compute the generalized inner product of `n`-bit strings with `k (B + 1)` bits. The blocks are
runs of `2 ^ k - 1` consecutive columns. -/
theorem ecomplexityFun_gip_le_of_le_mul (hn : n ≤ B * (2 ^ k - 1)) :
    Protocol.ecomplexityFun (gip : (Fin (k + 1) → BitString n) → Bool) ≤ (k * (B + 1) : ℕ) := by
  set s := 2 ^ k - 1 with hs
  have hsk : s < 2 ^ k := by have := @Nat.one_le_two_pow k; omega
  rcases Nat.eq_zero_or_pos s with h0 | hpos
  · -- No columns at all.
    have : n = 0 := by rw [h0, mul_zero] at hn; omega
    subst this
    refine ecomplexityFun_gip_le_of_block (fun r => r.elim0) fun b => ?_
    simp
  · refine ecomplexityFun_gip_le_of_block
      (fun r => ⟨r / s, (Nat.div_lt_iff_lt_mul hpos).mpr (by have := r.isLt; omega)⟩)
      fun b => ?_
    -- The columns of block `b` are `b s + j` for `j < s`.
    refine lt_of_le_of_lt (b := #(range s))
      (card_le_card_of_injOn (fun r => (r : ℕ) % s) ?_ ?_) (by rw [card_range]; exact hsk)
    · intro r _
      simp only [coe_range, Set.mem_Iio]
      exact Nat.mod_lt _ hpos
    · intro r hr r' hr' h
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, Fin.ext_iff] at hr hr'
      have hq : (r : ℕ) / s = r' / s := by rw [hr, hr']
      apply Fin.ext
      rw [← Nat.div_add_mod (r : ℕ) s, ← Nat.div_add_mod (r' : ℕ) s, hq]
      exact congrArg _ h

/-- **Grolmusz's upper bound, explicit form** [Grolmusz1994]: for `k ≥ 1`, `k + 1` players
compute the generalized inner product of `n`-bit strings with `k (n / (2 ^ k - 1) + 2)` bits,
`O(k n / 2 ^ k + k)`. -/
theorem ecomplexityFun_gip_le (hk : k ≠ 0) (n : ℕ) :
    Protocol.ecomplexityFun (gip : (Fin (k + 1) → BitString n) → Bool) ≤
      (k * (n / (2 ^ k - 1) + 2) : ℕ) := by
  have hpos : 0 < 2 ^ k - 1 := by have := Nat.one_lt_two_pow hk; omega
  refine ecomplexityFun_gip_le_of_le_mul (B := n / (2 ^ k - 1) + 1) ?_
  have := Nat.lt_mul_div_succ n hpos
  rw [mul_comm] at this
  exact this.le

end Cslib.Communication.NOF.Grolmusz
