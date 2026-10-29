/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatPower
import Mathlib.Data.Nat.Size

/-!
# Exhaustive-search reductions

Exponential and subexponential time bounds transfer along Turing reductions that branch over
$2^{\nu(a)}$ polynomial-time subinstances $f(a, r)$ (`r < 2 ^ ν a`), implemented by iterating a
polynomial-time step with a binary counter (`Turing.MultiTapeTM.ComputableInO.iterate`):
* `Cslib.Complexity.DecidableInExpTime.of_computableInPolyTime`: a set decided in polynomial time is
  decidable within exponential time with exponent `0`.
* `Cslib.Complexity.DecidableInExpTime.of_exhaustiveSearch`: if
  $a \in A \iff \exists r < 2^{\nu(a)}, f(a, r) \in B$, $\mu_B(f(a, r)) \le c \cdot \mu_A(a) + c$,
  and $\nu(a) \le \mu_A(a) / M + K$, then a decider for $B$ within time
  $2^{\delta \mu_B(b)} \cdot \mathrm{poly}(|b|)$ gives a decider for $A$ within time
  $2^{(1 / M + c \delta) \mu_A(a)} \cdot \mathrm{poly}(|a|)$.
* `Cslib.Complexity.DecidableInSubexpTime.of_exhaustiveSearch`: when $\nu(a) \le \mu_A(a) / M + K_M$
  for every $M \ge 1$, subexponential time for $B$ in $\mu_B$ gives subexponential time for $A$ in
  $\mu_A$.

## Main results

* `Cslib.Complexity.DecidableInExpTime.of_computableInPolyTime`: polynomial-time predicates have
  exponential-time exponent `0`.
* `Cslib.Complexity.DecidableInExpTime.of_exhaustiveSearch`,
  `Cslib.Complexity.DecidableInSubexpTime.of_exhaustiveSearch`: exponential and subexponential time
  transfer along exhaustive-search reductions.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 2.3][AroraBarak09]
* [R. Impagliazzo, R. Paturi, *On the complexity of k-SAT*][ImpagliazzoPaturi2001]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
  {A : Set α} {B : Set β} {μA : α → ℕ} {μB : β → ℕ}

/-- A set decided by a polynomial-time predicate is decidable within exponential time with exponent
`0` for any parameter `μ`. -/
theorem DecidableInExpTime.of_computableInPolyTime {μ : α → ℕ} {p : α → Bool}
    (hp : ComputableInPolyTime p encA encBool) (hA : ∀ a, a ∈ A ↔ p a = true) :
    DecidableInExpTime A encA μ 0 := by
  obtain ⟨d, _, hp'⟩ := hp.exists_degree
  refine DecidableInExpTime.of_computableInO hp'.inO hA 1 d fun a => ?_
  simp

namespace ExhaustiveSearch

private abbrev State (α : Type) : Type := (α × ℕ) × Bool

private def encState (encA : α ↪ List Bool) : State α ↪ List Bool :=
  encPair (encPair encA encNat) encBool

private def init (a : α) : State α := ((a, 0), false)

private def step (f : α × ℕ → β) (g : β → Bool) (s : State α) : State α :=
  ((s.1.1, s.1.2 + 1), s.2 || g (f s.1))

private def rounds (ν : α → ℕ) (a : α) : ℕ := 2 ^ ν a

private def search (f : α × ℕ → β) (ν : α → ℕ) (g : β → Bool) (a : α) : Bool :=
  ((step f g)^[rounds ν a] (init a)).2

private theorem iterate_step_init (f : α × ℕ → β) (g : β → Bool) (a : α) (k : ℕ) :
    (step f g)^[k] (init a) =
      ((a, k), (List.range k).any fun r => g (f (a, r))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, step, List.range_succ, List.any_append,
      List.any_cons, List.any_nil, Bool.or_false]

private theorem search_eq_true_iff {f : α × ℕ → β} {ν : α → ℕ} {g : β → Bool}
    (hfA : ∀ a, a ∈ A ↔ ∃ r < 2 ^ ν a, f (a, r) ∈ B)
    (hg : ∀ b, g b = true ↔ b ∈ B) (a : α) :
    search f ν g a = true ↔ a ∈ A := by
  rw [search, iterate_step_init, List.any_eq_true, hfA]
  simp only [List.mem_range, hg, rounds]

open ComputableInPolyTime in
private theorem computableInPolyTime_init :
    ComputableInPolyTime init encA (encState encA) := by
  unfold init encState
  fun_prop

open ComputableInPolyTime in
private theorem computableInPolyTime_rounds {ν : α → ℕ}
    (hν : ComputableInPolyTime ν encA encUnary) :
    ComputableInPolyTime (rounds ν) encA encNat :=
  binary_two_pow.comp hν

open ComputableInPolyTime in
private theorem exists_computableInO_step {f : α × ℕ → β}
    (hf : ComputableInPolyTime f (encPair encA encNat) encB)
    {g : β → Bool} {t : β → ℕ}
    (hg : ComputableInO g encB encBool t t) :
    ∃ d, ComputableInO (step f g) (encState encA) (encState encA)
      (fun s => ((encState encA s).length + 1) ^ d + t (f s.1))
      (fun s => ((encState encA s).length + 1) ^ d + t (f s.1)) := by
  obtain ⟨dN, eN, hN⟩ := (show ComputableInPolyTime (fun s : State α => (s.1.1, s.1.2 + 1))
    (encState encA) (encPair encA encNat) by unfold encState; fun_prop).exists_degree
  obtain ⟨dB, eB, hB⟩ := (show ComputableInPolyTime (fun s : State α => s.2)
    (encState encA) encBool by unfold encState; fun_prop).exists_degree
  obtain ⟨dR, eR, hR⟩ := (hf.comp (show ComputableInPolyTime (fun s : State α => s.1)
    (encState encA) (encPair encA encNat) by unfold encState; fun_prop)).exists_degree
  obtain ⟨dO, eO, hO⟩ := bool_or.exists_degree
  set D := dN + dB + dR
  have hN' := (hN.mono (d' := D) (e' := eN) (by omega) le_rfl).inO
  have hB' := (hB.mono (d' := D) (e' := eB) (by omega) le_rfl).inO
  have hR' := (hR.mono (d' := D) (e' := eR) (by omega) le_rfl).inO
  have h := hN'.prod (hO.inO.comp (hB'.prod (hg.comp hR')))
  have h4 (p : Bool × Bool) : (encPair encBool encBool p).length = 4 := by simp
  refine ⟨D, (h.mono (5 ^ dO + 4) (fun s => ?_) (fun s => ?_)).of_enc_eq fun _ => rfl⟩ <;>
  · simp only [Function.comp_apply, h4]
    generalize ((encState encA s).length + 1) ^ D = P
    generalize t (f s.1) = T
    have hF : 1 ≤ (4 + 1) ^ dO := Nat.one_le_pow _ _ (by norm_num)
    generalize (4 + 1) ^ dO = F at hF ⊢
    nlinarith

private theorem exists_state_and_node_bounds {f : α × ℕ → β} {ν : α → ℕ}
    (hf : ComputableInPolyTime f (encPair encA encNat) encB)
    (hν : ComputableInPolyTime ν encA encUnary) :
    ∃ (c_st d_st c_nd d_nd : ℕ),
      (∀ (g : β → Bool) (a : α) (k : ℕ),
        k ≤ rounds ν a →
        (encState encA ((step f g)^[k] (init a))).length ≤ c_st * ((encA a).length + 1) ^ d_st) ∧
      (∀ (a : α),
        (encNat (rounds ν a)).length + 1 ≤ c_st * ((encA a).length + 1) ^ d_st) ∧
      (∀ (a : α) (k : ℕ),
        k ≤ rounds ν a →
        (encB (f (a, k))).length ≤ c_nd * ((encA a).length + 1) ^ d_nd) := by
  obtain ⟨c_ν, d_ν, hν_len⟩ := hν.polyBounded_length.exists_le
  obtain ⟨cb, db, hf_len⟩ := hf.polyBounded_length.exists_le
  set d_st := d_ν + 1
  set c_p := 2 * c_ν + 4
  set c_st := 2 * c_p + 4
  have hpair_le (a : α) {k : ℕ} (hk : k ≤ rounds ν a) :
      (encPair encA encNat (a, k)).length ≤ c_p * ((encA a).length + 1) ^ d_st := by
    set L := (encA a).length
    have hK : (encNat k).length ≤ (encNat (rounds ν a)).length := by
      simpa only [encNat_apply, Nat.size_eq_bits_len] using Nat.size_le_size hk
    rw [rounds, encNat_two_pow, List.length_append, List.length_replicate,
      List.length_singleton] at hK
    have hνa : ν a ≤ c_ν * (L + 1) ^ d_ν := by
      simpa only [encUnary_apply, List.length_replicate] using hν_len a
    have hd1 : (L + 1) ^ d_ν ≤ (L + 1) ^ d_st :=
      Nat.pow_le_pow_right (Nat.succ_pos L) (Nat.le_succ d_ν)
    have hd2 : L + 1 ≤ (L + 1) ^ d_st := by
      simpa only [pow_one] using Nat.pow_le_pow_right (Nat.succ_pos L) (Nat.succ_pos d_ν)
    have hνa' : ν a ≤ c_ν * (L + 1) ^ d_st := hνa.trans (Nat.mul_le_mul_left c_ν hd1)
    simp only [length_encPair, L, c_p]
    nlinarith
  refine ⟨c_st, d_st, cb * (c_p + 1) ^ db, d_st * db,
    fun g a k hk => ?_, fun a => ?_, fun a k hk => ?_⟩
  · rw [iterate_step_init, encState, length_encPair]
    have hp := hpair_le a hk
    have h1 : 1 ≤ ((encA a).length + 1) ^ d_st := Nat.one_le_pow _ _ (Nat.succ_pos _)
    simp only [encBool_apply, List.length_singleton, c_st]
    nlinarith
  · set L := (encA a).length
    rw [rounds, encNat_two_pow, List.length_append, List.length_replicate, List.length_singleton]
    have hνa : ν a ≤ c_ν * (L + 1) ^ d_ν := by
      simpa only [encUnary_apply, List.length_replicate] using hν_len a
    have hd1 : (L + 1) ^ d_ν ≤ (L + 1) ^ d_st :=
      Nat.pow_le_pow_right (Nat.succ_pos L) (Nat.le_succ d_ν)
    have h1 : 1 ≤ (L + 1) ^ d_st := Nat.one_le_pow _ _ (Nat.succ_pos L)
    have hνa' : ν a ≤ c_ν * (L + 1) ^ d_st := hνa.trans (Nat.mul_le_mul_left c_ν hd1)
    simp only [c_st, c_p, L]
    nlinarith
  · have h1 := hf_len (a, k)
    have h2 := hpair_le a hk
    have h3 : (encPair encA encNat (a, k)).length + 1 ≤
        (c_p + 1) * ((encA a).length + 1) ^ d_st := by
      have : 1 ≤ ((encA a).length + 1) ^ d_st := Nat.one_le_pow _ _ (Nat.succ_pos _)
      nlinarith
    calc (encB (f (a, k))).length
        ≤ cb * ((encPair encA encNat (a, k)).length + 1) ^ db := h1
      _ ≤ cb * ((c_p + 1) * ((encA a).length + 1) ^ d_st) ^ db :=
          Nat.mul_le_mul_left cb (Nat.pow_le_pow_left h3 db)
      _ = cb * (c_p + 1) ^ db * ((encA a).length + 1) ^ (d_st * db) := by
          rw [mul_pow, ← pow_mul, ← mul_assoc]

private noncomputable def leafTime (encA : α ↪ List Bool) (μA : α → ℕ)
    (c_mu c_nd d_nd : ℕ) (δ : ℝ) (c e : ℕ) (a : α) : ℕ :=
  ⌈(c : ℝ) * (2 ^ (δ * ((c_mu * μA a + c_mu : ℕ) : ℝ)) *
    ((c_nd * ((encA a).length + 1) ^ d_nd : ℕ) + 1 : ℝ) ^ e) + c⌉₊

end ExhaustiveSearch

open ExhaustiveSearch in
/-- **Exponential-time transfer along an exhaustive search.** If
$f : \alpha \times \mathbb{N} \to \beta$ and $\nu : \alpha \to \mathbb{N}$ are computable in
polynomial time (with $\nu$ in unary), $a \in A \iff \exists r < 2^{\nu(a)},\, f(a, r) \in B$,
$\mu_B(f(a, r)) \le c \cdot \mu_A(a) + c$, and $\nu(a) \le \mu_A(a) / M + K$, then a decider for $B$
within time $2^{\delta \mu_B(b)} \cdot \mathrm{poly}(|b|)$ yields a decider for $A$ within time
$2^{(1 / M + c \delta) \mu_A(a)} \cdot \mathrm{poly}(|a|)$. -/
theorem DecidableInExpTime.of_exhaustiveSearch {f : α × ℕ → β} {ν : α → ℕ}
    (hf : ComputableInPolyTime f (encPair encA encNat) encB)
    (hν : ComputableInPolyTime ν encA encUnary)
    (hfA : ∀ a, a ∈ A ↔ ∃ r < 2 ^ ν a, f (a, r) ∈ B) {c : ℕ}
    (hμ : ∀ a r, μB (f (a, r)) ≤ c * μA a + c) {M K : ℕ}
    (hνM : ∀ a, ν a ≤ μA a / M + K) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : DecidableInExpTime B encB μB δ) :
    DecidableInExpTime A encA μA (1 / M + c * δ) := by
  rcases isEmpty_or_nonempty α with hα | hα
  · exact DecidableInExpTime.of_computableInO (.const false)
      (fun a => hα.elim a) 1 0 (fun a => hα.elim a)
  obtain ⟨a₀⟩ := hα
  have : Inhabited α := ⟨a₀⟩
  obtain ⟨e, h⟩ := h
  obtain ⟨g, t, k_dec, hg, hgB, ht⟩ := h.exists_computableInO
  obtain ⟨d, hstep⟩ := exists_computableInO_step hf hg
  obtain ⟨dn, _, hn⟩ := (computableInPolyTime_rounds hν).exists_degree
  obtain ⟨di, _, hi⟩ := (computableInPolyTime_init (encA := encA)).exists_degree
  obtain ⟨da, _, ha⟩ := (show ComputableInPolyTime (fun s : State α => s.2)
    (encState encA) encBool by unfold encState; fun_prop).exists_degree
  obtain ⟨c_st, d_st, c_nd, d_nd, hst_bound, hrounds_len, hnd_bound⟩ :=
    exists_state_and_node_bounds hf hν
  set stBound : α → ℕ := fun a => c_st * ((encA a).length + 1) ^ d_st
  set ndBound : α → ℕ := fun a => c_nd * ((encA a).length + 1) ^ d_nd
  have hround (a : α) (k : ℕ) (hk : k ≤ rounds ν a) :
      ((encState encA ((step f g)^[k] (init a))).length + 1) ^ d +
        t (f ((step f g)^[k] (init a)).1) ≤
        (stBound a + 1) ^ d + leafTime encA μA c c_nd d_nd δ k_dec e a := by
    have hS : (encState encA ((step f g)^[k] (init a))).length ≤ stBound a :=
      hst_bound g a k hk
    refine Nat.add_le_add (Nat.pow_le_pow_left (by omega) d) ?_
    rw [iterate_step_init]
    dsimp only
    set b := f (a, k)
    have hb_mu : μB b ≤ c * μA a + c := hμ a k
    have hb_enc : (encB b).length ≤ ndBound a := hnd_bound a k hk
    have h₁ : (2 : ℝ) ^ (δ * μB b) ≤ 2 ^ (δ * ((c * μA a + c : ℕ) : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hb_mu) hδ)
    have h₂ : (((encB b).length : ℝ) + 1) ^ e ≤ ((ndBound a : ℝ) + 1) ^ e :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hb_enc 1) e
    have h₃ := mul_le_mul h₁ h₂ (by positivity) (by positivity)
    have h₄ := mul_le_mul_of_nonneg_left h₃ (Nat.cast_nonneg k_dec : (0 : ℝ) ≤ k_dec)
    have h₅ := (ht b).trans (add_le_add h₄ le_rfl)
    exact Nat.cast_le.mp (h₅.trans (Nat.le_ceil _))
  have hstate (a : α) (k : ℕ) (hk : k ≤ rounds ν a) :
      (encState encA ((step f g)^[k] (init a))).length ≤ stBound a :=
    hst_bound g a k hk
  have hiter := ComputableInO.iterate hn.inO hi.inO hstep hround hround hstate
  have hsearch := ha.inO.comp hiter
  set C₁ := (c_st + 1) ^ d + c_st + c_st ^ 2
  set C₃ := (c_st + 1) ^ da
  set E := dn + di + d_st * d + d_st * da + d_nd * e + 2 * d_st
  set C₂ : ℝ := k_dec * 2 ^ (c * δ) * ((c_nd : ℝ) + 1) ^ e + k_dec + 1
  set C₀ : ℝ := 3 + C₃ + (2 ^ K + 1 : ℝ) * (C₁ + C₂)
  refine DecidableInExpTime.of_computableInO hsearch
    (fun a => (search_eq_true_iff hfA (fun b => (hgB b).symm) a).symm) ⌈C₀⌉₊ E fun a => ?_
  set L := (encA a).length
  set N := μA a
  set P := (L + 1) ^ E
  have hP (m : ℕ) (hm : m ≤ E) : (L + 1) ^ m ≤ P := Nat.pow_le_pow_right (Nat.succ_pos L) hm
  have hsb : stBound a = c_st * (L + 1) ^ d_st := rfl
  have hr : rounds ν a + 1 ≤ (2 ^ K + 1) * 2 ^ (N / M) := by
    have h1 := hνM a
    have h2 : rounds ν a ≤ 2 ^ K * 2 ^ (N / M) := by
      calc rounds ν a = 2 ^ ν a := rfl
        _ ≤ 2 ^ (N / M + K) := Nat.pow_le_pow_right two_pos h1
        _ = 2 ^ K * 2 ^ (N / M) := by rw [pow_add, Nat.mul_comm]
    have h3 : 1 ≤ 2 ^ (N / M) := Nat.one_le_two_pow
    nlinarith
  have hpoly : (L + 1) ^ dn + (L + 1) ^ di ≤ 2 * P := by
    have := hP dn (by omega)
    have := hP di (by omega)
    omega
  have hans_le :
      ((encState encA ((step f g)^[rounds ν a] (init a))).length + 1) ^ da ≤ C₃ * P := by
    have h1 := hstate a (rounds ν a) le_rfl
    have h2 : stBound a + 1 ≤ (c_st + 1) * (L + 1) ^ d_st := by
      have : 1 ≤ (L + 1) ^ d_st := Nat.one_le_pow _ _ (Nat.succ_pos L)
      rw [hsb]
      nlinarith
    calc ((encState encA ((step f g)^[rounds ν a] (init a))).length + 1) ^ da
        ≤ (stBound a + 1) ^ da := Nat.pow_le_pow_left (by omega) da
      _ ≤ ((c_st + 1) * (L + 1) ^ d_st) ^ da := Nat.pow_le_pow_left h2 da
      _ = C₃ * (L + 1) ^ (d_st * da) := by simp only [C₃, mul_pow, ← pow_mul]
      _ ≤ C₃ * P := Nat.mul_le_mul_left C₃ (hP (d_st * da) (by omega))
  have hrnd : (stBound a + 1) ^ d + stBound a +
      ((encNat (rounds ν a)).length + 1) ^ 2 ≤ C₁ * P := by
    have h1 : (stBound a + 1) ^ d ≤ (c_st + 1) ^ d * (L + 1) ^ (d_st * d) := by
      have hst1 : stBound a + 1 ≤ (c_st + 1) * (L + 1) ^ d_st := by
        have : 1 ≤ (L + 1) ^ d_st := Nat.one_le_pow _ _ (Nat.succ_pos L)
        rw [hsb]
        nlinarith
      calc (stBound a + 1) ^ d ≤ ((c_st + 1) * (L + 1) ^ d_st) ^ d := Nat.pow_le_pow_left hst1 d
        _ = (c_st + 1) ^ d * (L + 1) ^ (d_st * d) := by rw [mul_pow, ← pow_mul]
    have h2 : ((encNat (rounds ν a)).length + 1) ^ 2 ≤ c_st ^ 2 * (L + 1) ^ (d_st * 2) := by
      have hr_len := hrounds_len a
      calc ((encNat (rounds ν a)).length + 1) ^ 2
          ≤ (c_st * (L + 1) ^ d_st) ^ 2 := Nat.pow_le_pow_left hr_len 2
        _ = c_st ^ 2 * (L + 1) ^ (d_st * 2) := by rw [mul_pow, ← pow_mul]
    have h3 := hP (d_st * d) (by omega)
    have h4 := hP d_st (by omega)
    have h5 := hP (d_st * 2) (by omega)
    calc (stBound a + 1) ^ d + stBound a + ((encNat (rounds ν a)).length + 1) ^ 2
        ≤ (c_st + 1) ^ d * P + c_st * P + c_st ^ 2 * P := by
          have := h1.trans (Nat.mul_le_mul_left ((c_st + 1) ^ d) h3)
          have := (le_of_eq hsb).trans (Nat.mul_le_mul_left c_st h4)
          have := h2.trans (Nat.mul_le_mul_left (c_st ^ 2) h5)
          omega
      _ = C₁ * P := by simp only [C₁]; ring
  set Y : ℝ := 2 ^ ((c * δ) * N)
  have hY : 1 ≤ Y := Real.one_le_rpow (by norm_num) (by positivity)
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast Nat.one_le_pow _ _ (Nat.succ_pos L)
  have hleaf : (leafTime encA μA c c_nd d_nd δ k_dec e a : ℝ) ≤ C₂ * Y * P := by
    have h₁ : (2 : ℝ) ^ (δ * ((c * N + c : ℕ) : ℝ)) = 2 ^ (c * δ) * Y := by
      rw [← Real.rpow_add (by norm_num)]
      congr 1
      push_cast
      ring
    have h₂ : ((ndBound a : ℝ) + 1) ^ e ≤ ((c_nd : ℝ) + 1) ^ e * P := by
      have hnb_le : (ndBound a : ℝ) + 1 ≤ ((c_nd : ℝ) + 1) * ((L : ℝ) + 1) ^ d_nd := by
        have hnb_eq : (ndBound a : ℝ) = c_nd * ((L : ℝ) + 1) ^ d_nd := by
          simp only [ndBound]
          push_cast
          ring
        have hpow1 : (1 : ℝ) ≤ ((L : ℝ) + 1) ^ d_nd :=
          one_le_pow₀ (by linarith [(L.cast_nonneg : (0 : ℝ) ≤ L)])
        nlinarith
      calc ((ndBound a : ℝ) + 1) ^ e ≤ (((c_nd : ℝ) + 1) * ((L : ℝ) + 1) ^ d_nd) ^ e :=
            pow_le_pow_left₀ (by positivity) hnb_le e
        _ = ((c_nd : ℝ) + 1) ^ e * ((L : ℝ) + 1) ^ (d_nd * e) := by rw [mul_pow, ← pow_mul]
        _ ≤ ((c_nd : ℝ) + 1) ^ e * P := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact_mod_cast hP (d_nd * e) (by omega)
    have h₃ := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (k_dec : ℝ) * (2 ^ (δ * ((c * N + c : ℕ) : ℝ)) *
      ((ndBound a : ℝ) + 1) ^ e) + k_dec by positivity)
    unfold leafTime
    change (⌈(k_dec : ℝ) * (2 ^ (δ * ((c * N + c : ℕ) : ℝ)) *
      ((ndBound a : ℝ) + 1) ^ e) + k_dec⌉₊ : ℝ) ≤ _
    rw [h₁] at h₃ ⊢
    have h₄ : (k_dec : ℝ) * (2 ^ (c * δ) * Y * ((ndBound a : ℝ) + 1) ^ e) ≤
        k_dec * 2 ^ (c * δ) * ((c_nd : ℝ) + 1) ^ e * Y * P := by
      have := mul_le_mul_of_nonneg_left h₂ (by positivity : (0 : ℝ) ≤ k_dec * 2 ^ (c * δ) * Y)
      nlinarith
    have h₅ : (k_dec : ℝ) + 1 ≤ ((k_dec : ℝ) + 1) * Y * P := by
      have : (1 : ℝ) ≤ Y * P := one_le_mul_of_one_le_of_one_le hY hP1
      nlinarith
    calc (⌈(k_dec : ℝ) * (2 ^ (c * δ) * Y * ((ndBound a : ℝ) + 1) ^ e) + k_dec⌉₊ : ℝ)
        ≤ (k_dec : ℝ) * (2 ^ (c * δ) * Y * ((ndBound a : ℝ) + 1) ^ e) + k_dec + 1 := h₃.le
      _ ≤ C₂ * Y * P := by simp only [C₂]; nlinarith
  set X : ℝ := 2 ^ ((1 / M : ℝ) * N)
  have hX : ((2 ^ (N / M) : ℕ) : ℝ) ≤ X := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    rw [one_div_mul_eq_div]
    exact Nat.cast_div_le
  have hX1 : 1 ≤ X := Real.one_le_rpow (by norm_num) (by positivity)
  have hXY : X * Y = 2 ^ ((1 / M + c * δ) * N) := by
    rw [← Real.rpow_add (by norm_num)]
    ring_nf
  have hT : ((L + 1) ^ dn + (L + 1) ^ di +
      (rounds ν a + 1) * ((stBound a + 1) ^ d + leafTime encA μA c c_nd d_nd δ k_dec e a +
        stBound a + ((encNat (rounds ν a)).length + 1) ^ 2) +
      ((encState encA ((step f g)^[rounds ν a] (init a))).length + 1) ^ da : ℝ) ≤
      (2 + C₃ : ℝ) * P + (2 ^ K + 1 : ℝ) * X * (C₁ * P + C₂ * Y * P) := by
    have h₁ : ((L + 1) ^ dn + (L + 1) ^ di : ℝ) ≤ 2 * P := by exact_mod_cast hpoly
    have h₁' :
        (((encState encA ((step f g)^[rounds ν a] (init a))).length + 1) ^ da : ℝ) ≤ C₃ * P := by
      exact_mod_cast hans_le
    have h₂ : ((rounds ν a + 1 : ℕ) : ℝ) ≤ (2 ^ K + 1 : ℝ) * X := by
      have : ((rounds ν a + 1 : ℕ) : ℝ) ≤ (((2 ^ K + 1) * 2 ^ (N / M) : ℕ) : ℝ) := by
        exact_mod_cast hr
      rw [Nat.cast_mul] at this
      have hKM : (0 : ℝ) ≤ (2 ^ K + 1 : ℕ) := Nat.cast_nonneg _
      have hmul := mul_le_mul_of_nonneg_left hX hKM
      push_cast at this hmul ⊢
      linarith
    have h₃ : (((stBound a + 1) ^ d + stBound a +
        ((encNat (rounds ν a)).length + 1) ^ 2 : ℕ) : ℝ) ≤ C₁ * P := by exact_mod_cast hrnd
    have h₄ : (((stBound a + 1) ^ d + leafTime encA μA c c_nd d_nd δ k_dec e a + stBound a +
        ((encNat (rounds ν a)).length + 1) ^ 2 : ℕ) : ℝ) ≤ C₁ * P + C₂ * Y * P := by
      push_cast at h₃ ⊢
      linarith
    have h₅ := mul_le_mul h₂ h₄ (by positivity) (by positivity)
    push_cast at h₁ h₁' h₅ ⊢
    linarith
  calc _ ≤ (2 + C₃ : ℝ) * P + (2 ^ K + 1 : ℝ) * X * (C₁ * P + C₂ * Y * P) := by
          exact_mod_cast hT
    _ ≤ C₀ * (X * Y * P) := by
        have hXY1 : 1 ≤ X * Y := one_le_mul_of_one_le_of_one_le hX1 hY
        have hC₂ : 0 ≤ C₂ := by positivity
        have hC₁ : (0 : ℝ) ≤ C₁ := by positivity
        have hC₃ : (0 : ℝ) ≤ C₃ := by positivity
        have hKM : (0 : ℝ) ≤ 2 ^ K + 1 := by positivity
        have hP0 : (0 : ℝ) ≤ P := by positivity
        have a₁ : (P : ℝ) ≤ X * Y * P := le_mul_of_one_le_left hP0 hXY1
        have a₂ : X * P ≤ X * Y * P := by
          have := mul_le_mul_of_nonneg_left hY (by positivity : (0 : ℝ) ≤ X * P)
          linarith [show X * P * Y = X * Y * P by ring]
        have a₃ := mul_le_mul_of_nonneg_left a₂ (mul_nonneg hKM hC₁)
        have a₄ := mul_le_mul_of_nonneg_left a₁ hC₃
        simp only [C₀]
        nlinarith
    _ ≤ ⌈C₀⌉₊ * (2 ^ ((1 / M + c * δ) * N) * ((L : ℝ) + 1) ^ E) := by
        rw [← hXY]
        push_cast [P]
        exact mul_le_mul_of_nonneg_right (Nat.le_ceil C₀) (by positivity)

/-- **Subexponential-time transfer along an exhaustive search with sublinear branch exponent.** If
$f : \alpha \times \mathbb{N} \to \beta$ and $\nu : \alpha \to \mathbb{N}$ are computable in
polynomial time (with $\nu$ in unary), $a \in A \iff \exists r < 2^{\nu(a)},\, f(a, r) \in B$,
$\mu_B(f(a, r)) \le c \cdot \mu_A(a) + c$, and for every $M \ge 1$ there is a constant $K$ with
$\nu(a) \le \mu_A(a) / M + K$, then subexponential time for $B$ in $\mu_B$ gives subexponential time
for $A$ in $\mu_A$. -/
theorem DecidableInSubexpTime.of_exhaustiveSearch {f : α × ℕ → β} {ν : α → ℕ}
    (hf : ComputableInPolyTime f (encPair encA encNat) encB)
    (hν : ComputableInPolyTime ν encA encUnary)
    (hfA : ∀ a, a ∈ A ↔ ∃ r < 2 ^ ν a, f (a, r) ∈ B) {c : ℕ}
    (hμ : ∀ a r, μB (f (a, r)) ≤ c * μA a + c)
    (hνM : ∀ M > 0, ∃ K, ∀ a, ν a ≤ μA a / M + K)
    (h : DecidableInSubexpTime B encB μB) :
    DecidableInSubexpTime A encA μA := by
  intro ε hε
  obtain ⟨M, hM⟩ := exists_nat_gt (2 / ε)
  have hMpos : (0 : ℝ) < M := lt_trans (by positivity) hM
  have hM_nat : 0 < M := Nat.cast_pos.mp hMpos
  obtain ⟨K, hK⟩ := hνM M hM_nat
  have hMε : 1 / (M : ℝ) < ε / 2 := by
    rw [div_lt_iff₀ hMpos]
    rw [div_lt_iff₀ hε] at hM
    linarith
  set δ : ℝ := ε / (2 * (c + 1))
  have hδ : 0 < δ := by positivity
  refine ((h δ hδ).of_exhaustiveSearch hf hν hfA hμ hK hδ.le).mono ?_
  have hcδ : (c : ℝ) * δ ≤ ε / 2 := by
    simp only [δ]
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  linarith

end Cslib.Complexity
