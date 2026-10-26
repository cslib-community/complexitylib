/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Communication.Lifting.Partition
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The deterministic lifting theorem

A protocol of depth `c` for a search problem `R` lifted by the index gadget gives a decision tree
for `R` of depth `d` with `(m / τ) ^ d ≤ 4 ^ c`, whenever `4 ≤ τ`, `τ ^ 2 ≤ m` and
`320 n ^ 2 (⌊log₂ m⌋ + 1) ≤ τ` (`Communication.Lifting.exists_decisionTree_of_solves`). With
`τ = √m` this reads `d log₂ m ≤ 4 c` (`Communication.Lifting.depth_mul_logb_le`). Together with
the simulation of decision trees by protocols (`Communication.Lifting.ecomplexity_lift_le`), the
communication complexity of the lifted problem is `Θ(log m)` times the decision-tree depth of `R`
once `√m ≥ 320 n ^ 2 (⌊log₂ m⌋ + 1)`, which holds for some `m = O(n ^ 4 log² n)`
[Raz and McKenzie][RazMcKenzie1999], [Göös, Pitassi and Watson, Theorem 3][GoosPitassiWatson2018].

The decision tree walks down the protocol (`Communication.Lifting.sim`), keeping a rectangle
`X × Y` of inputs that reach the current node, a set `J` of queried coordinates and their answers
`ρ` (`Communication.Lifting.SimState`) [Mertz and Pitassi, Algorithm 2][MertzPitassi2020]. The
invariants (`Communication.Lifting.SimState.Good`) are:
* every pair in `X × Y` gives the gadget the values `ρ` on `J`, and both sets are fixed on `J`;
* `X` is `τ`-dense on the other coordinates, and `Y` has small deficiency on their blocks;
* `X` is large, which bounds the number of queries.

When Bob speaks, the tree follows the larger half of `Y`. When Alice speaks, it follows the larger
half of `X` and splits it by the density-restoring partition. It chooses a piece `(I, α, P)`
leaving every value on `I` possible for many `y`
(`Communication.Lifting.exists_piece_forall_le_card_filter`), queries the coordinates `I`, and
fixes Bob's blocks of `I` accordingly (`Communication.Lifting.exists_fix_blocks`). At a leaf, the
full-range lemma (`Communication.Lifting.exists_forall_eq_of_isDense`) shows that the protocol's
output answers `R` on every input consistent with the queries. A query of `#I` coordinates
shrinks `X` by a factor of about `τ ^ #I`, while a uniform set would shrink by `m ^ #I`. Since
`X` loses at most a factor `4` per bit sent, `(m / τ) ^ d ≤ 4 ^ c`.

Mertz and Pitassi need only `m ≥ n ^ (1 + ε)`, using the blockwise approximate sunflower lemma in
the full-range lemma. The elementary Janson-type bound used here needs `m` of order `n ^ 4`. Both
are polynomial in `n`, as in the statement of Göös, Pitassi and Watson.

## Main definitions

* `Cslib.Communication.Lifting.SimState`: the state of the simulation.
* `Cslib.Communication.Lifting.sim`: the simulating decision tree.

## Main results

* `Cslib.Communication.Lifting.exists_decisionTree_of_solves`: the lifting theorem.
* `Cslib.Communication.Lifting.depth_mul_logb_le`: the lifting theorem with `τ = √m`.

## References

* [I. Mertz and T. Pitassi, *Lifting: As Easy As 1, 2, 3*][MertzPitassi2020]
* [M. Göös, T. Pitassi and T. Watson, *Deterministic communication vs. partition
  number*][GoosPitassiWatson2018]
* [R. Raz and P. McKenzie, *Separation of the monotone NC hierarchy*][RazMcKenzie1999]
-/

@[expose] public section

namespace Cslib.Communication.Lifting

open Finset

variable {n m : ℕ} {O : Type*}

/-- The larger half of `s` under the bit `f`: at least half of `s` has `f a = bigHalf s f`. -/
def bigHalf {α : Type*} (s : Finset α) (f : α → Bool) : Bool :=
  decide (#s ≤ 2 * #(s.filter fun a => f a = true))

theorem card_le_two_mul_card_filter_bigHalf {α : Type*} (s : Finset α) (f : α → Bool) :
    (#s : ℝ) ≤ 2 * #(s.filter fun a => f a = bigHalf s f) := by
  have hsum := card_filter_add_card_filter_not (s := s) (fun a => f a = true)
  unfold bigHalf
  by_cases h : #s ≤ 2 * #(s.filter fun a => f a = true)
  · simp only [h, decide_true]; exact_mod_cast h
  · simp only [h, decide_false]
    simp only [Bool.not_eq_true] at hsum
    have : #s ≤ 2 * #(s.filter fun a => f a = false) := by omega
    exact_mod_cast this

/-- A set fixed on `J` has at most `m ^ #Jᶜ` pointer vectors. -/
theorem card_le_pow_of_fixed {J : Finset (Fin n)} {X : Finset (Fin n → Fin m)}
    (hX : ∀ x ∈ X, ∀ x' ∈ X, ∀ i ∈ J, x i = x' i) : #X ≤ m ^ #Jᶜ := by
  have hinj : Set.InjOn (fun x : Fin n → Fin m => fun i : (Jᶜ : Finset (Fin n)) => x i)
      (X : Set (Fin n → Fin m)) := by
    intro x hx x' hx' h
    funext i
    by_cases hi : i ∈ J
    · exact hX x hx x' hx' i hi
    · exact congrFun h ⟨i, mem_compl.mpr hi⟩
  calc #X ≤ #(univ : Finset ((Jᶜ : Finset (Fin n)) → Fin m)) :=
        card_le_card_of_injOn _ (fun _ _ => mem_univ _) hinj
    _ = m ^ #Jᶜ := by simp [card_compl]

/-- The state of the simulation: the queried coordinates `J` with answers `ρ`, the rectangle
`X × Y`, and the number `t` of bits simulated so far. -/
structure SimState (n m : ℕ) where
  /-- The queried coordinates. -/
  J : Finset (Fin n)
  /-- The answers to the queries, on `J`. -/
  ρ : Fin n → Bool
  /-- Alice's inputs. -/
  X : Finset (Fin n → Fin m)
  /-- Bob's inputs. -/
  Y : Finset (Fin n → Fin m → Bool)
  /-- The number of bits simulated. -/
  t : ℕ

namespace SimState

/-- The invariants of the simulation of the protocol `p`, with density `τ` and total budget `c`
[Mertz and Pitassi, invariants (i)–(iii)][MertzPitassi2020]. -/
structure Good (τ : ℝ) (c : ℕ) (R : (Fin n → Bool) → O → Prop)
    (p : Protocol (Fin n → Fin m) (Fin n → Fin m → Bool) O) (st : SimState n m) : Prop where
  X_nonempty : st.X.Nonempty
  X_fixed : ∀ x ∈ st.X, ∀ x' ∈ st.X, ∀ i ∈ st.J, x i = x' i
  Y_fixed : ∀ y ∈ st.Y, ∀ y' ∈ st.Y, ∀ i ∈ st.J, y i = y' i
  ind_eq : ∀ x ∈ st.X, ∀ y ∈ st.Y, ∀ i ∈ st.J, y i (x i) = st.ρ i
  dense : IsDense τ st.Jᶜ st.X
  Y_large : (2 : ℝ) ^ (#st.Jᶜ * m) ≤ 2 ^ st.t * (4 * τ) ^ #st.J * #st.Y
  X_large : (m : ℝ) ^ #st.Jᶜ * (m / τ) ^ #st.J ≤ 4 ^ st.t * #st.X
  solves : p.Solves (lift R) st.X st.Y
  budget : st.t + p.depth ≤ c

variable {τ : ℝ} {c : ℕ} {R : (Fin n → Bool) → O → Prop}
  {p : Protocol (Fin n → Fin m) (Fin n → Fin m → Bool) O} {st : SimState n m}

/-- The queries made so far are paid for: `(m / τ) ^ #J ≤ 4 ^ t`. -/
theorem Good.pow_le (h : st.Good τ c R p) : ((m : ℝ) / τ) ^ #st.J ≤ 4 ^ st.t := by
  have hX := card_le_pow_of_fixed h.X_fixed
  have hX' : (#st.X : ℝ) ≤ (m : ℝ) ^ #st.Jᶜ := by exact_mod_cast hX
  have hXpos : (0 : ℝ) < #st.X := by exact_mod_cast card_pos.mpr h.X_nonempty
  have hpos : (0 : ℝ) < (m : ℝ) ^ #st.Jᶜ := by linarith
  have := h.X_large
  have h4 : (0 : ℝ) ≤ 4 ^ st.t := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hX' h4]

/-- The deficiency of `Y` is at most `5 t` bits. -/
theorem Good.two_pow_le (h : st.Good τ c R p) (hτ4 : 4 ≤ τ) (hτm : τ ^ 2 ≤ m) :
    (2 : ℝ) ^ (#st.Jᶜ * m) ≤ 2 ^ (5 * st.t) * #st.Y := by
  have h1 := h.pow_le
  have hτ0 : 0 < τ := by linarith
  have h2 : 4 * τ ≤ ((m : ℝ) / τ) ^ 2 := by
    rw [div_pow, le_div_iff₀ (by positivity)]
    have h4 : τ ^ 4 ≤ (m : ℝ) ^ 2 := by nlinarith [sq_nonneg τ]
    nlinarith [pow_pos hτ0 3]
  have h3 : (4 * τ) ^ #st.J ≤ (16 : ℝ) ^ st.t := by
    calc (4 * τ) ^ #st.J ≤ (((m : ℝ) / τ) ^ 2) ^ #st.J :=
          pow_le_pow_left₀ (by positivity) h2 _
      _ = (((m : ℝ) / τ) ^ #st.J) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ ((4 : ℝ) ^ st.t) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
      _ = 16 ^ st.t := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  calc (2 : ℝ) ^ (#st.Jᶜ * m) ≤ 2 ^ st.t * (4 * τ) ^ #st.J * #st.Y := h.Y_large
    _ ≤ 2 ^ st.t * 16 ^ st.t * #st.Y := by gcongr
    _ = 2 ^ (5 * st.t) * #st.Y := by
        rw [← mul_pow, pow_mul]; norm_num

/-- **At a leaf**, the protocol's output answers `R` on every input consistent with the queries,
by the full-range lemma. -/
theorem Good.output {o : O} (h : st.Good τ c R (.output o)) (hτ4 : 4 ≤ τ) (hτm : τ ^ 2 ≤ m)
    (hτc : 64 * n * (5 * c + 2) ≤ τ) (z : Fin n → Bool) (hz : ∀ i ∈ st.J, z i = st.ρ i) :
    R z o := by
  have hτ0 : 0 < τ := by linarith
  have hJ : (#st.Jᶜ : ℝ) ≤ n := by exact_mod_cast (card_le_univ _).trans_eq (Fintype.card_fin n)
  have ht : (st.t : ℝ) ≤ c := by
    have := h.budget
    simp only [Protocol.depth, add_zero] at this
    exact_mod_cast this
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_forall_eq_of_isDense (r := τ) (D := 5 * st.t) hτ0
    h.X_nonempty (fun x hx x' hx' i hi => h.X_fixed x hx x' hx' i (by simpa using hi)) h.dense
    (fun y hy y' hy' i hi => h.Y_fixed y hy y' hy' i (by simpa using hi)) (h.two_pow_le hτ4 hτm)
    (by
      push_cast
      have : (0 : ℝ) ≤ #st.Jᶜ := by positivity
      nlinarith)
    fun _ => z
  have hind : ind x y = z := by
    funext i
    by_cases hi : i ∈ st.J
    · rw [ind_apply, h.ind_eq x hx y hy i hi, hz i hi]
    · exact hxy i (mem_compl.mpr hi)
  have := h.solves x (mem_coe.mpr hx) y (mem_coe.mpr hy)
  simpa [lift, hind] using this

/-- **When Bob speaks**, following a half of `Y` holding at least half of it keeps the
invariants. -/
theorem Good.bob {send : (Fin n → Fin m → Bool) → Bool} {p₀ p₁ : Protocol _ _ O}
    (h : st.Good τ c R (.bob send p₀ p₁)) (hτ : 0 < τ) (b : Bool)
    (hb : (#st.Y : ℝ) ≤ 2 * #(st.Y.filter fun y => send y = b)) :
    (⟨st.J, st.ρ, st.X, st.Y.filter fun y => send y = b, st.t + 1⟩ : SimState n m).Good τ c R
      (cond b p₁ p₀) where
  X_nonempty := h.X_nonempty
  X_fixed := h.X_fixed
  Y_fixed := fun y hy y' hy' => h.Y_fixed y (filter_subset _ _ hy) y' (filter_subset _ _ hy')
  ind_eq := fun x hx y hy => h.ind_eq x hx y (filter_subset _ _ hy)
  dense := h.dense
  Y_large := by
    have h1 := h.Y_large
    have h2 : (0 : ℝ) ≤ 2 ^ st.t * (4 * τ) ^ #st.J := by positivity
    dsimp only
    rw [pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left hb h2]
  X_large := by
    have h1 := h.X_large
    have : (4 : ℝ) ^ st.t ≤ 4 ^ (st.t + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h0 : (0 : ℝ) ≤ #st.X := by positivity
    dsimp only
    nlinarith
  solves := by
    intro x hx y hy
    have hy' := mem_filter.mp (mem_coe.mp hy)
    have := h.solves x hx y (mem_coe.mpr hy'.1)
    simp only [Protocol.run_bob, hy'.2] at this
    cases b <;> exact this
  budget := by
    have := h.budget
    simp only [Protocol.depth] at this
    cases b <;> simp only [Bool.cond_true, Bool.cond_false] <;> omega

/-- When `I ⊆ Jᶜ`, `(J ∪ I)ᶜ = Jᶜ \ I`, `#(J ∪ I)ᶜ + #I = #Jᶜ`, and `#(J ∪ I) = #J + #I`. -/
private theorem compl_union_and_cards_of_subset_compl {J I : Finset (Fin n)} (hIJ : I ⊆ Jᶜ) :
    (J ∪ I)ᶜ = Jᶜ \ I ∧ #(J ∪ I)ᶜ + #I = #Jᶜ ∧ #(J ∪ I) = #J + #I := by
  have hdisj : Disjoint J I := by
    rw [disjoint_iff_ne]
    rintro a ha b' hb' rfl
    exact (mem_compl.mp (hIJ hb')) ha
  have hcompl : (J ∪ I)ᶜ = Jᶜ \ I := by
    ext i
    simp only [mem_compl, mem_union, mem_sdiff]
    tauto
  refine ⟨hcompl, ?_, card_union_of_disjoint hdisj⟩
  rw [hcompl, card_sdiff_of_subset hIJ, Nat.sub_add_cancel (card_le_card hIJ)]

/-- Under the hypotheses of `Good.alice`, Bob's filtered set `Y'` satisfies the deficiency
invariant for `st.t + 1` and `st.J ∪ q.I`. -/
private theorem Good.alice_Y_large {send : (Fin n → Fin m) → Bool} {p₀ p₁ : Protocol _ _ O}
    (h : st.Good τ c R (.alice send p₀ p₁)) (hτ : 0 < τ) (b : Bool) {L : List (Piece n m)}
    (hL : IsPartition τ st.Jᶜ (st.X.filter fun x => send x = b) L) {q : Piece n m}
    (hqL : q ∈ L) (hq : ∀ β, (#st.Y : ℝ) ≤ #(allowing st.Y q.I q.α β) * (4 * τ) ^ #q.I)
    (ρ' : Fin n → Bool) (η : Fin n → Fin m → Bool)
    (hηcard : (#(allowing st.Y q.I q.α ρ') : ℝ) ≤
      #(st.Y.filter fun y => ∀ i ∈ q.I, y i = η i) * 2 ^ (m * #q.I)) :
    (2 : ℝ) ^ (#(st.J ∪ q.I)ᶜ * m) ≤
      2 ^ (st.t + 1) * (4 * τ) ^ #(st.J ∪ q.I) *
        #(st.Y.filter fun y => ∀ i ∈ q.I, y i = η i) := by
  set Y' := st.Y.filter fun y => ∀ i ∈ q.I, y i = η i
  obtain ⟨-, hcardc, hcardJ⟩ := compl_union_and_cards_of_subset_compl (hL.I_subset q hqL)
  have h1 := h.Y_large
  have h2 := hq ρ'
  rw [hcardJ, ← hcardc] at *
  rw [← hcardc] at h1
  have e1 : (2 : ℝ) ^ ((#(st.J ∪ q.I)ᶜ + #q.I) * m) =
      2 ^ (#(st.J ∪ q.I)ᶜ * m) * 2 ^ (m * #q.I) := by
    rw [← pow_add]
    congr 1
    ring
  rw [e1] at h1
  have hA : (0 : ℝ) ≤ 2 ^ st.t * (4 * τ) ^ #st.J := by positivity
  have hB : (0 : ℝ) ≤ (4 * τ) ^ #q.I := by positivity
  have hY0 : (0 : ℝ) ≤ (4 * τ) ^ #st.J * ((4 * τ) ^ #q.I * #Y') := by positivity
  refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < 2 ^ (m * #q.I))
  calc (2 : ℝ) ^ (#(st.J ∪ q.I)ᶜ * m) * 2 ^ (m * #q.I)
      ≤ 2 ^ st.t * (4 * τ) ^ #st.J * #st.Y := h1
    _ ≤ 2 ^ st.t * (4 * τ) ^ #st.J * (#(allowing st.Y q.I q.α ρ') * (4 * τ) ^ #q.I) :=
      mul_le_mul_of_nonneg_left h2 hA
    _ ≤ 2 ^ st.t * (4 * τ) ^ #st.J * ((4 * τ) ^ #q.I * (#Y' * 2 ^ (m * #q.I))) := by
      refine mul_le_mul_of_nonneg_left ?_ hA
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left hηcard hB
    _ = 2 ^ st.t * ((4 * τ) ^ #st.J * ((4 * τ) ^ #q.I * #Y')) * 2 ^ (m * #q.I) := by ring
    _ ≤ 2 ^ (st.t + 1) * ((4 * τ) ^ #st.J * ((4 * τ) ^ #q.I * #Y')) * 2 ^ (m * #q.I) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      rw [pow_succ]
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) st.t]
    _ = 2 ^ (st.t + 1) * (4 * τ) ^ (#st.J + #q.I) * #Y' * 2 ^ (m * #q.I) := by
      rw [pow_add]
      ring

/-- Under the hypotheses of `Good.alice`, Alice's piece `q.P` satisfies the size invariant for
`st.t + 1` and `st.J ∪ q.I`. -/
private theorem Good.alice_X_large {send : (Fin n → Fin m) → Bool} {p₀ p₁ : Protocol _ _ O}
    (h : st.Good τ c R (.alice send p₀ p₁)) (hτ : 0 < τ) (b : Bool)
    (hb : (#st.X : ℝ) ≤ 2 * #(st.X.filter fun x => send x = b)) {L : List (Piece n m)}
    (hL : IsPartition τ st.Jᶜ (st.X.filter fun x => send x = b) L) {q : Piece n m}
    (hqL : q ∈ L) :
    (m : ℝ) ^ #(st.J ∪ q.I)ᶜ * (m / τ) ^ #(st.J ∪ q.I) ≤ 4 ^ (st.t + 1) * #q.P := by
  obtain ⟨-, hcardc, hcardJ⟩ := compl_union_and_cards_of_subset_compl (hL.I_subset q hqL)
  have hPcard := hL.card_le q hqL
  have h1 := h.X_large
  rw [← hcardc, pow_add] at h1
  rw [hcardJ, pow_add]
  have hmτ : ((m : ℝ) / τ) ^ #q.I * τ ^ #q.I = (m : ℝ) ^ #q.I := by
    rw [← mul_pow, div_mul_cancel₀ _ hτ.ne']
  refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < τ ^ #q.I)
  calc (m : ℝ) ^ #(st.J ∪ q.I)ᶜ * (((m : ℝ) / τ) ^ #st.J * ((m : ℝ) / τ) ^ #q.I) * τ ^ #q.I
      = (m : ℝ) ^ #(st.J ∪ q.I)ᶜ * (m : ℝ) ^ #q.I * ((m : ℝ) / τ) ^ #st.J := by
        rw [← mul_assoc, mul_assoc _ _ (τ ^ #q.I), hmτ]
        ring
    _ ≤ 4 ^ st.t * #st.X := h1
    _ ≤ 4 ^ st.t * (2 * (2 * #q.P * τ ^ #q.I)) := by
        gcongr
        linarith
    _ = 4 ^ (st.t + 1) * #q.P * τ ^ #q.I := by rw [pow_succ]; ring

/-- **When Alice speaks**, following a half of `X` holding at least half of it, restricting to a
good piece `(I, α, P)` of its density-restoring partition, and fixing Bob's blocks of `I` to
blocks `η` giving the answers `ρ'` keeps the invariants. -/
theorem Good.alice {send : (Fin n → Fin m) → Bool} {p₀ p₁ : Protocol _ _ O}
    (h : st.Good τ c R (.alice send p₀ p₁)) (hτ : 0 < τ) (b : Bool)
    (hb : (#st.X : ℝ) ≤ 2 * #(st.X.filter fun x => send x = b)) {L : List (Piece n m)}
    (hL : IsPartition τ st.Jᶜ (st.X.filter fun x => send x = b) L) {q : Piece n m} (hqL : q ∈ L)
    (hq : ∀ β, (#st.Y : ℝ) ≤ #(allowing st.Y q.I q.α β) * (4 * τ) ^ #q.I)
    (ρ' : Fin n → Bool) (hρ' : ∀ i ∈ st.J, ρ' i = st.ρ i) (η : Fin n → Fin m → Bool)
    (hη : ∀ i ∈ q.I, η i (q.α i) = ρ' i)
    (hηcard : (#(allowing st.Y q.I q.α ρ') : ℝ) ≤
      #(st.Y.filter fun y => ∀ i ∈ q.I, y i = η i) * 2 ^ (m * #q.I)) :
    (⟨st.J ∪ q.I, ρ', q.P, st.Y.filter fun y => ∀ i ∈ q.I, y i = η i, st.t + 1⟩ :
      SimState n m).Good τ c R (cond b p₁ p₀) := by
  have hPX : q.P ⊆ st.X := (hL.subset q hqL).trans (filter_subset _ _)
  have hXpos : (0 : ℝ) < #st.X := by exact_mod_cast card_pos.mpr h.X_nonempty
  have hPcard := hL.card_le q hqL
  obtain ⟨hcompl, -, -⟩ := compl_union_and_cards_of_subset_compl (hL.I_subset q hqL)
  refine ⟨?_, ?_, ?_, ?_, ?_,
    h.alice_Y_large hτ b hL hqL hq ρ' η hηcard,
    h.alice_X_large hτ b hb hL hqL, ?_, ?_⟩
  · -- the piece is nonempty
    rw [← card_pos]
    by_contra hP
    rw [Nat.eq_zero_of_not_pos hP, Nat.cast_zero, mul_zero, zero_mul] at hPcard
    linarith
  · intro x hx x' hx' i hi
    rcases mem_union.mp hi with hi | hi
    · exact h.X_fixed x (hPX hx) x' (hPX hx') i hi
    · rw [hL.fixed q hqL x hx i hi, hL.fixed q hqL x' hx' i hi]
  · intro y hy y' hy' i hi
    rcases mem_union.mp hi with hi | hi
    · exact h.Y_fixed y (filter_subset _ _ hy) y' (filter_subset _ _ hy') i hi
    · rw [(mem_filter.mp hy).2 i hi, (mem_filter.mp hy').2 i hi]
  · intro x hx y hy i hi
    rcases mem_union.mp hi with hi | hi
    · rw [h.ind_eq x (hPX hx) y (filter_subset _ _ hy) i hi]
      exact (hρ' i hi).symm
    · rw [(mem_filter.mp hy).2 i hi, hL.fixed q hqL x hx i hi, hη i hi]
  · change IsDense τ (st.J ∪ q.I)ᶜ q.P
    rw [hcompl]
    exact hL.dense q hqL
  · intro x hx y hy
    have hx' := mem_filter.mp (hL.subset q hqL (mem_coe.mp hx))
    have := h.solves x (mem_coe.mpr hx'.1) y (mem_coe.mpr (filter_subset _ _ (mem_coe.mp hy)))
    simp only [Protocol.run_alice, hx'.2] at this
    cases b <;> exact this
  · have := h.budget
    simp only [Protocol.depth] at this
    change st.t + 1 + (cond b p₁ p₀).depth ≤ c
    cases b <;> simp only [Bool.cond_true, Bool.cond_false] <;> omega

end SimState

/-! ### The simulating decision tree -/

/-- The density-restoring partition used by the simulation. -/
noncomputable def partitionOf (τ : ℝ) (F : Finset (Fin n)) (X : Finset (Fin n → Fin m)) :
    List (Piece n m) :=
  @dite _ (∃ L, IsPartition τ F X L) (Classical.dec _) (fun h => h.choose) fun _ => []

theorem isPartition_partitionOf {τ : ℝ} (hτ : 0 < τ) (F : Finset (Fin n))
    (X : Finset (Fin n → Fin m)) : IsPartition τ F X (partitionOf τ F X) := by
  have h := exists_pieces hτ F X
  rw [partitionOf, dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec

/-- A piece leaving every value `β` on its fixed coordinates possible for a `(4 τ) ^ (-#I)`
fraction of `Y`. -/
def GoodPiece (τ : ℝ) (Y : Finset (Fin n → Fin m → Bool)) (q : Piece n m) : Prop :=
  ∀ β : Fin n → Bool, (#Y : ℝ) ≤ #(allowing Y q.I q.α β) * (4 * τ) ^ #q.I

/-- The answers `ρ'` on `I` and `ρ` elsewhere. -/
def mergeAnswers (I : Finset (Fin n)) (ρ' ρ : Fin n → Bool) : Fin n → Bool :=
  fun i => if i ∈ I then ρ' i else ρ i

/-- Bob's blocks fixed in Phase II. -/
noncomputable def fixBlocks (Y : Finset (Fin n → Fin m → Bool)) (I : Finset (Fin n))
    (α : Fin n → Fin m) (β : Fin n → Bool) : Fin n → Fin m → Bool :=
  (exists_fix_blocks Y I α β).choose

namespace SimState

/-- The state after Bob speaks: the larger half of `Y`. -/
def afterBob (st : SimState n m) (send : (Fin n → Fin m → Bool) → Bool) : SimState n m :=
  ⟨st.J, st.ρ, st.X, st.Y.filter fun y => send y = bigHalf st.Y send, st.t + 1⟩

/-- The state after Alice speaks and the coordinates of the piece `q` are queried with answers
`ρ'`. -/
noncomputable def afterAlice (st : SimState n m) (q : Piece n m) (ρ' : Fin n → Bool) :
    SimState n m :=
  ⟨st.J ∪ q.I, mergeAnswers q.I ρ' st.ρ, q.P,
    st.Y.filter fun y => ∀ i ∈ q.I, y i = fixBlocks st.Y q.I q.α (mergeAnswers q.I ρ' st.ρ) i,
    st.t + 1⟩

end SimState

/-- **The simulating decision tree** [Mertz and Pitassi, Algorithm 2][MertzPitassi2020]. -/
noncomputable def sim (τ : ℝ) :
    Protocol (Fin n → Fin m) (Fin n → Fin m → Bool) O → SimState n m → DecisionTree (Fin n) O
  | .output o, _ => .leaf o
  | .bob send p₀ p₁, st =>
    cond (bigHalf st.Y send) (sim τ p₁ (st.afterBob send)) (sim τ p₀ (st.afterBob send))
  | .alice send p₀ p₁, st =>
    @dite _ (∃ q ∈ partitionOf τ st.Jᶜ (st.X.filter fun x => send x = bigHalf st.X send),
        GoodPiece τ st.Y q) (Classical.dec _)
      (fun h => DecisionTree.graft h.choose.I.toList
        (fun ρ' => cond (bigHalf st.X send) (sim τ p₁ (st.afterAlice h.choose ρ'))
          (sim τ p₀ (st.afterAlice h.choose ρ'))) st.ρ)
      fun _ => cond (bigHalf st.X send) (sim τ p₁ st) (sim τ p₀ st)

section Invariants

variable {τ : ℝ} {c : ℕ} {R : (Fin n → Bool) → O → Prop}

/-- The Alice step: the state after the query keeps the invariants. -/
theorem SimState.Good.afterAlice {st : SimState n m} {send : (Fin n → Fin m) → Bool}
    {p₀ p₁ : Protocol _ _ O} (h : st.Good τ c R (.alice send p₀ p₁)) (hτ : 0 < τ)
    {q : Piece n m}
    (hq : q ∈ partitionOf τ st.Jᶜ (st.X.filter fun x => send x = bigHalf st.X send))
    (hgood : GoodPiece τ st.Y q) (ρ' : Fin n → Bool) :
    (st.afterAlice q ρ').Good τ c R (cond (bigHalf st.X send) p₁ p₀) := by
  have hL := isPartition_partitionOf hτ st.Jᶜ (st.X.filter fun x => send x = bigHalf st.X send)
  have hIJ : q.I ⊆ st.Jᶜ := hL.I_subset q hq
  have hspec := (exists_fix_blocks st.Y q.I q.α (mergeAnswers q.I ρ' st.ρ)).choose_spec
  refine h.alice hτ _ (card_le_two_mul_card_filter_bigHalf _ _) hL hq hgood _ ?_ _ hspec.1 hspec.2
  intro i hi
  have : i ∉ q.I := fun h' => mem_compl.mp (hIJ h') hi
  simp [mergeAnswers, this]

/-- Under the invariants, some piece of the partition is good. -/
theorem SimState.Good.exists_goodPiece {st : SimState n m} {send : (Fin n → Fin m) → Bool}
    {p₀ p₁ : Protocol _ _ O} (h : st.Good τ c R (.alice send p₀ p₁)) (hτ4 : 4 ≤ τ)
    (hτm : τ ^ 2 ≤ m) (hτc : 64 * n * (5 * c + 2) ≤ τ) :
    ∃ q ∈ partitionOf τ st.Jᶜ (st.X.filter fun x => send x = bigHalf st.X send),
      GoodPiece τ st.Y q := by
  have hτ : 0 < τ := by linarith
  have hb := card_le_two_mul_card_filter_bigHalf st.X send
  have hXpos : (0 : ℝ) < #st.X := by exact_mod_cast card_pos.mpr h.X_nonempty
  have hne : (st.X.filter fun x => send x = bigHalf st.X send).Nonempty := by
    rw [← card_pos]
    have : (0 : ℝ) < #(st.X.filter fun x => send x = bigHalf st.X send) := by linarith
    exact_mod_cast this
  have hJ : (#st.Jᶜ : ℝ) ≤ n := by exact_mod_cast (card_le_univ _).trans_eq (Fintype.card_fin n)
  have ht : (st.t : ℝ) ≤ c := by
    have := h.budget
    exact_mod_cast (Nat.le_add_right _ _).trans this
  exact exists_piece_forall_le_card_filter (X₀ := st.X) (D := 5 * st.t) hτ
    (isPartition_partitionOf hτ _ _) hne h.dense (filter_subset _ _) hb
    (fun x hx x' hx' i hi => h.X_fixed x (filter_subset _ _ hx) x' (filter_subset _ _ hx') i
      (by simpa using hi))
    (fun y hy y' hy' i hi => h.Y_fixed y hy y' hy' i (by simpa using hi))
    (h.two_pow_le hτ4 hτm) (by
      push_cast
      have : (0 : ℝ) ≤ #st.Jᶜ := by positivity
      nlinarith)

/-- **Correctness of the simulation.** -/
theorem eval_sim (hτ4 : 4 ≤ τ) (hτm : τ ^ 2 ≤ m) (hτc : 64 * n * (5 * c + 2) ≤ τ) :
    ∀ (p : Protocol (Fin n → Fin m) (Fin n → Fin m → Bool) O) (st : SimState n m),
      st.Good τ c R p → ∀ z, (∀ i ∈ st.J, z i = st.ρ i) → R z ((sim τ p st).eval z) := by
  have hτ : 0 < τ := by linarith
  intro p
  induction p with
  | output o => intro st h z hz; exact h.output hτ4 hτm hτc z hz
  | bob send p₀ p₁ ih₀ ih₁ =>
    intro st h z hz
    have key : ∀ b : Bool, (st.afterBob send).Good τ c R (cond b p₁ p₀) →
        R z ((cond b (sim τ p₁ (st.afterBob send)) (sim τ p₀ (st.afterBob send))).eval z) := by
      intro b hb'
      cases b
      · exact ih₀ _ hb' z hz
      · exact ih₁ _ hb' z hz
    exact key _ (h.bob hτ _ (card_le_two_mul_card_filter_bigHalf _ _))
  | alice send p₀ p₁ ih₀ ih₁ =>
    intro st h z hz
    have hq := h.exists_goodPiece hτ4 hτm hτc
    rw [sim, dite_eq_left_of_eq_true (eq_true hq), DecisionTree.eval_graft]
    obtain ⟨hqL, hgood⟩ := hq.choose_spec
    set q := hq.choose
    set ρ' : Fin n → Bool := fun j => if j ∈ q.I.toList then z j else st.ρ j
    have hz' : ∀ i ∈ (st.afterAlice q ρ').J, z i = (st.afterAlice q ρ').ρ i := by
      intro i hi
      simp only [SimState.afterAlice, mergeAnswers, mem_union] at hi ⊢
      by_cases hiI : i ∈ q.I
      · simp [ρ', hiI]
      · simp only [hiI, ite_false]
        exact hz i (hi.resolve_right hiI)
    have key : ∀ b : Bool, (st.afterAlice q ρ').Good τ c R (cond b p₁ p₀) →
        R z ((cond b (sim τ p₁ (st.afterAlice q ρ')) (sim τ p₀ (st.afterAlice q ρ'))).eval z) := by
      intro b hb'
      cases b
      · exact ih₀ _ hb' z hz'
      · exact ih₁ _ hb' z hz'
    exact key _ (h.afterAlice hτ hqL hgood ρ')

/-- Inductive step of `pow_depth_sim` when Alice speaks. -/
private theorem pow_depth_sim_alice (hτ4 : 4 ≤ τ) (hτm : τ ^ 2 ≤ m)
    (hτc : 64 * n * (5 * c + 2) ≤ τ)
    {send : (Fin n → Fin m) → Bool} {p₀ p₁ : Protocol _ _ O}
    (ih₀ : ∀ st : SimState n m, st.Good τ c R p₀ →
      ((m : ℝ) / τ) ^ (#st.J + (sim τ p₀ st).depth) ≤ 4 ^ (st.t + p₀.depth))
    (ih₁ : ∀ st : SimState n m, st.Good τ c R p₁ →
      ((m : ℝ) / τ) ^ (#st.J + (sim τ p₁ st).depth) ≤ 4 ^ (st.t + p₁.depth))
    (st : SimState n m) (h : st.Good τ c R (.alice send p₀ p₁)) :
    ((m : ℝ) / τ) ^ (#st.J + (sim τ (.alice send p₀ p₁) st).depth) ≤
      4 ^ (st.t + (Protocol.alice send p₀ p₁).depth) := by
  have hτ : 0 < τ := by linarith
  have hM : (1 : ℝ) ≤ m / τ := by
    rw [le_div_iff₀ hτ, one_mul]
    nlinarith
  have hq := h.exists_goodPiece hτ4 hτm hτc
  rw [sim, dite_eq_left_of_eq_true (eq_true hq)]
  obtain ⟨hqL, hgood⟩ := hq.choose_spec
  set q := hq.choose
  set k : (Fin n → Bool) → DecisionTree (Fin n) O := fun ρ' =>
    cond (bigHalf st.X send) (sim τ p₁ (st.afterAlice q ρ')) (sim τ p₀ (st.afterAlice q ρ'))
  obtain ⟨ρ₀, -, hρ₀⟩ := exists_mem_eq_sup univ univ_nonempty fun ρ' => (k ρ').depth
  have hdepth := DecisionTree.depth_graft_le q.I.toList k st.ρ (d := (k ρ₀).depth)
    fun ρ' => hρ₀ ▸ le_sup (f := fun ρ' => (k ρ').depth) (mem_univ ρ')
  rw [length_toList] at hdepth
  have hJ : #(st.afterAlice q ρ₀).J = #st.J + #q.I :=
    (SimState.compl_union_and_cards_of_subset_compl ((isPartition_partitionOf hτ st.Jᶜ
      (st.X.filter fun x => send x = bigHalf st.X send)).I_subset q hqL)).2.2
  have key : ∀ b : Bool, (st.afterAlice q ρ₀).Good τ c R (cond b p₁ p₀) →
      ((m : ℝ) / τ) ^ (#st.J + #q.I +
        (cond b (sim τ p₁ (st.afterAlice q ρ₀)) (sim τ p₀ (st.afterAlice q ρ₀))).depth) ≤
        4 ^ (st.t + (Protocol.alice send p₀ p₁).depth) := by
    intro b hb'
    have hle : ∀ d, d ≤ (Protocol.alice send p₀ p₁).depth - 1 → (4 : ℝ) ^ (st.t + 1 + d) ≤
        4 ^ (st.t + (Protocol.alice send p₀ p₁).depth) := fun d hd =>
      pow_le_pow_right₀ (by norm_num) (by simp only [Protocol.depth] at hd ⊢; omega)
    cases b
    · exact (hJ ▸ ih₀ _ hb').trans (hle _ (by simp [Protocol.depth]))
    · exact (hJ ▸ ih₁ _ hb').trans (hle _ (by simp [Protocol.depth]))
  refine le_trans (pow_le_pow_right₀ hM ?_) (key _ (h.afterAlice hτ hqL hgood ρ₀))
  change #st.J + (DecisionTree.graft q.I.toList k st.ρ).depth ≤ #st.J + #q.I + (k ρ₀).depth
  omega

/-- **The number of queries of the simulation**: `(m / τ) ^ (#J + depth) ≤ 4 ^ (t + depth p)`. -/
theorem pow_depth_sim (hτ4 : 4 ≤ τ) (hτm : τ ^ 2 ≤ m) (hτc : 64 * n * (5 * c + 2) ≤ τ) :
    ∀ (p : Protocol (Fin n → Fin m) (Fin n → Fin m → Bool) O) (st : SimState n m),
      st.Good τ c R p → ((m : ℝ) / τ) ^ (#st.J + (sim τ p st).depth) ≤ 4 ^ (st.t + p.depth) := by
  have hτ : 0 < τ := by linarith
  intro p
  induction p with
  | output o =>
    intro st h
    simpa [sim, Protocol.depth] using h.pow_le
  | bob send p₀ p₁ ih₀ ih₁ =>
    intro st h
    have key : ∀ b : Bool, (st.afterBob send).Good τ c R (cond b p₁ p₀) →
        ((m : ℝ) / τ) ^ (#st.J +
          (cond b (sim τ p₁ (st.afterBob send)) (sim τ p₀ (st.afterBob send))).depth) ≤
          4 ^ (st.t + (Protocol.bob send p₀ p₁).depth) := by
      intro b hb'
      have hle : ∀ d, d ≤ (Protocol.bob send p₀ p₁).depth - 1 → (4 : ℝ) ^ (st.t + 1 + d) ≤
          4 ^ (st.t + (Protocol.bob send p₀ p₁).depth) := fun d hd =>
        pow_le_pow_right₀ (by norm_num) (by simp only [Protocol.depth] at hd ⊢; omega)
      cases b
      · exact (ih₀ _ hb').trans (hle _ (by simp [Protocol.depth]))
      · exact (ih₁ _ hb').trans (hle _ (by simp [Protocol.depth]))
    exact key _ (h.bob hτ _ (card_le_two_mul_card_filter_bigHalf _ _))
  | alice send p₀ p₁ ih₀ ih₁ =>
    exact pow_depth_sim_alice hτ4 hτm hτc ih₀ ih₁

end Invariants

/-! ### The lifting theorem -/

/-- The initial state: nothing queried, all inputs. -/
def SimState.init (n m : ℕ) : SimState n m :=
  ⟨∅, fun _ => false, univ, univ, 0⟩

/-- All of `[m]ⁿ` is `τ`-dense when `τ ≤ m`. -/
theorem isDense_univ {τ : ℝ} (hτ : 0 ≤ τ) (hτm : τ ≤ m) (F : Finset (Fin n)) :
    IsDense τ F (univ : Finset (Fin n → Fin m)) := by
  intro I _ _ α
  have h1 : #((univ : Finset (Fin n → Fin m)).filter fun x => ∀ i ∈ I, x i = α i) ≤ m ^ #Iᶜ :=
    card_le_pow_of_fixed fun x hx x' hx' i hi => by
      rw [(mem_filter.mp hx).2 i hi, (mem_filter.mp hx').2 i hi]
  have h1' : (#((univ : Finset (Fin n → Fin m)).filter fun x => ∀ i ∈ I, x i = α i) : ℝ) ≤
      (m : ℝ) ^ #Iᶜ := by exact_mod_cast h1
  have h2 : τ ^ #I ≤ (m : ℝ) ^ #I := pow_le_pow_left₀ hτ hτm _
  have hu : (#(univ : Finset (Fin n → Fin m)) : ℝ) = (m : ℝ) ^ #Iᶜ * (m : ℝ) ^ #I := by
    rw [← pow_add, card_compl, Nat.sub_add_cancel (card_le_univ I)]
    simp
  rw [hu]
  exact mul_le_mul h1' h2 (by positivity) (by positivity)

/-- When `4 ^ p.depth < (m / τ) ^ n` with `4 ≤ τ` and `320 * n ^ 2 * (Nat.log 2 m + 1) ≤ τ`,
the protocol depth satisfies `64 * n * (5 * p.depth + 2) ≤ τ`. -/
private theorem sixtyFour_mul_depth_le_of_four_pow_lt {τ : ℝ} (hτ4 : 4 ≤ τ)
    (hτn : 320 * n ^ 2 * (Nat.log 2 m + 1) ≤ τ)
    {p : Protocol (Fin n → Fin m) (Fin n → Fin m → Bool) O}
    (hc : (4 : ℝ) ^ p.depth < ((m : ℝ) / τ) ^ n) :
    64 * n * (5 * p.depth + 2) ≤ τ := by
  have hτ : 0 < τ := by linarith
  have hcn : 2 * p.depth ≤ n * (Nat.log 2 m + 1) := by
    have h1 : ((m : ℝ) / τ) ^ n ≤ (m : ℝ) ^ n := by
      refine pow_le_pow_left₀ (by positivity) ?_ n
      rw [div_le_iff₀ hτ]
      nlinarith
    have h2 : (m : ℝ) ^ n < 2 ^ (n * (Nat.log 2 m + 1)) := by
      rw [mul_comm, pow_mul]
      have : (m : ℝ) < 2 ^ (Nat.log 2 m + 1) := by
        exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) m
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        rw [pow_zero] at hc
        exact absurd hc (not_lt.mpr (one_le_pow₀ (by norm_num)))
      · exact pow_lt_pow_left₀ this (by positivity) hn.ne'
    have h3 : (2 : ℝ) ^ (2 * p.depth) < 2 ^ (n * (Nat.log 2 m + 1)) := by
      rw [pow_mul]
      norm_num
      linarith
    have := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp h3
    omega
  have h1 : (64 * n * (5 * p.depth + 2) : ℕ) ≤ 320 * n ^ 2 * (Nat.log 2 m + 1) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · nlinarith
  exact le_trans (by exact_mod_cast h1) hτn

/-- **The deterministic lifting theorem** [Raz and McKenzie][RazMcKenzie1999], [Göös, Pitassi and
Watson, Theorem 3][GoosPitassiWatson2018], [Mertz and Pitassi, Lemma 3.1][MertzPitassi2020].
Let `4 ≤ τ`, `τ ^ 2 ≤ m` and `320 n ^ 2 (⌊log₂ m⌋ + 1) ≤ τ`. If a protocol of depth `c` solves
the lifted search problem `lift R` on all inputs, then a decision tree of depth `d` with
`(m / τ) ^ d ≤ 4 ^ c` solves `R`. -/
theorem exists_decisionTree_of_solves {R : (Fin n → Bool) → O → Prop} {τ : ℝ} (hτ4 : 4 ≤ τ)
    (hτm : τ ^ 2 ≤ m) (hτn : 320 * n ^ 2 * (Nat.log 2 m + 1) ≤ τ)
    {p : Protocol (Fin n → Fin m) (Fin n → Fin m → Bool) O}
    (hp : p.Solves (lift R) Set.univ Set.univ) :
    ∃ t : DecisionTree (Fin n) O,
      (∀ z, R z (t.eval z)) ∧ ((m : ℝ) / τ) ^ t.depth ≤ 4 ^ p.depth := by
  have hτ : 0 < τ := by linarith
  have hτm' : τ ≤ m := by nlinarith
  have hm : 0 < m := by
    have : (0 : ℝ) < m := by linarith
    exact_mod_cast this
  have hM : (1 : ℝ) ≤ m / τ := by
    rw [le_div_iff₀ hτ, one_mul]
    exact hτm'
  by_cases hc : ((m : ℝ) / τ) ^ n ≤ 4 ^ p.depth
  · -- the trivial decision tree querying every coordinate
    have htot : ∀ z, ∃ o, R z o := fun z =>
      ⟨_, hp (fun _ => ⟨0, hm⟩) trivial (fun i _ => z i) trivial⟩
    choose f hf using htot
    obtain ⟨t, ht, hdepth⟩ := DecisionTree.exists_computes f
    refine ⟨t, fun z => by rw [ht z]; exact hf z, ?_⟩
    rw [Fintype.card_fin] at hdepth
    exact (pow_le_pow_right₀ hM hdepth).trans hc
  · push Not at hc
    -- the budget is small
    have hτc : 64 * n * (5 * p.depth + 2) ≤ τ :=
      sixtyFour_mul_depth_le_of_four_pow_lt hτ4 hτn hc
    -- the initial state satisfies the invariants
    have hinit : (SimState.init n m).Good τ p.depth R p := by
      refine ⟨univ_nonempty_iff.mpr ⟨fun _ => ⟨0, hm⟩⟩, by simp [SimState.init],
        by simp [SimState.init], by simp [SimState.init], isDense_univ hτ.le hτm' _, ?_, ?_,
        hp.mono (Set.subset_univ _) (Set.subset_univ _), by simp [SimState.init]⟩
      · simp [SimState.init, ← pow_mul, mul_comm]
      · simp [SimState.init]
    refine ⟨sim τ p (SimState.init n m), fun z => eval_sim hτ4 hτm hτc p _ hinit z (by
      simp [SimState.init]), ?_⟩
    simpa [SimState.init] using pow_depth_sim hτ4 hτm hτc p _ hinit

/-- **The deterministic lifting theorem with `τ = √m`.** If `m ≥ 16` and
`320 n ^ 2 (⌊log₂ m⌋ + 1) ≤ √m`, then every protocol of depth `c` solving the lifted search
problem gives a decision tree of depth `d` with `d log₂ m ≤ 4 c`. -/
theorem depth_mul_logb_le {R : (Fin n → Bool) → O → Prop} (hm : 16 ≤ m)
    (hmn : 320 * n ^ 2 * (Nat.log 2 m + 1) ≤ Real.sqrt m)
    {p : Protocol (Fin n → Fin m) (Fin n → Fin m → Bool) O}
    (hp : p.Solves (lift R) Set.univ Set.univ) :
    ∃ t : DecisionTree (Fin n) O, (∀ z, R z (t.eval z)) ∧
      t.depth * Real.logb 2 m ≤ 4 * p.depth := by
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hsq : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm0
  have h4 : (4 : ℝ) ≤ Real.sqrt m := by
    rw [show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hm)
  obtain ⟨t, ht, hdepth⟩ := exists_decisionTree_of_solves h4 hsq.le hmn hp
  refine ⟨t, ht, ?_⟩
  have hspos : 0 < Real.sqrt m := by linarith
  have hdiv : (m : ℝ) / Real.sqrt m = Real.sqrt m := by
    rw [div_eq_iff hspos.ne', ← sq, hsq]
  rw [hdiv] at hdepth
  have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hdepth
  rw [Real.logb_pow, Real.logb_pow] at hlog
  have hsqrt : Real.logb 2 m = 2 * Real.logb 2 (Real.sqrt m) := by
    conv_lhs => rw [← hsq]
    rw [Real.logb_pow]; push_cast; ring
  have : Real.logb 2 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    norm_num
  rw [this] at hlog
  rw [hsqrt]
  linarith

end Cslib.Communication.Lifting
