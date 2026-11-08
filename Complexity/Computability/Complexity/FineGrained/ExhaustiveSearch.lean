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
import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
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

/-- **Length bounds for the search.** The states visited by the search and the binary round counter
have length at most `st a`, and every subinstance `f (a, k)` it queries has length at most `nd a`;
both bounds are polynomial in the length of the encoded instance. -/
private theorem exists_search_length_bounds {f : α × ℕ → β} {ν : α → ℕ}
    (hf : ComputableInPolyTime f (encPair encA encNat) encB)
    (hν : ComputableInPolyTime ν encA encUnary) :
    ∃ st nd : α → ℕ,
      PolyBounded (fun a => (encA a).length) st ∧ PolyBounded (fun a => (encA a).length) nd ∧
      (∀ (g : β → Bool) (a : α) (k : ℕ), k ≤ rounds ν a →
        (encState encA ((step f g)^[k] (init a))).length ≤ st a) ∧
      (∀ a, (encNat (rounds ν a)).length ≤ st a) ∧
      (∀ a k, k ≤ rounds ν a → (encB (f (a, k))).length ≤ nd a) := by
  -- `rounds ν a = 2 ^ ν a` has `ν a + 1` binary digits, which bounds every round counter.
  have hrounds (a : α) : (encNat (rounds ν a)).length = ν a + 1 := by
    rw [rounds, encNat_two_pow, List.length_append, List.length_replicate, List.length_singleton]
  have hpair (a : α) {k : ℕ} (hk : k ≤ rounds ν a) :
      (encPair encA encNat (a, k)).length ≤ 2 * (encA a).length + ν a + 2 := by
    have := ComputableTidilyInO.length_encNat_mono hk
    rw [hrounds] at this
    simp only [length_encPair]
    omega
  have hν' : PolyBounded (fun a => (encA a).length) ν := by
    simpa only [encUnary_apply, List.length_replicate] using hν.polyBounded_length
  obtain ⟨cf, df, hf_len⟩ := hf.polyBounded_length.exists_le
  refine ⟨fun a => 2 * (2 * (encA a).length + ν a + 2) + 2,
    fun a => cf * (2 * (encA a).length + ν a + 2 + 1) ^ df, by growth_poly, by growth_poly,
    fun g a k hk => ?_, fun a => by simp only [hrounds]; omega, fun a k hk => ?_⟩
  · have := hpair a hk
    rw [iterate_step_init, encState, length_encPair]
    simp only [encBool_apply, List.length_singleton]
    omega
  · refine (hf_len (a, k)).trans (Nat.mul_le_mul_left cf (Nat.pow_le_pow_left ?_ df))
    have := hpair a hk
    omega

/-- A bound on the time of the decider for `B`, within time `k * (2 ^ (δ * μB b) * (|b| + 1) ^ e)
+ k`, on every subinstance `b` of `a` with `μB b ≤ c * μA a + c` and length at most `nd a`. -/
private noncomputable def leafTime (μA nd : α → ℕ) (c : ℕ) (δ : ℝ) (k e : ℕ) (a : α) : ℕ :=
  ⌈(k : ℝ) * (2 ^ (δ * ((c * μA a + c : ℕ) : ℝ)) * ((nd a : ℝ) + 1) ^ e) + k⌉₊

/-- The decider for `B` runs within `leafTime` on every subinstance of `a` that `leafTime`
accounts for. -/
private theorem le_leafTime {nd : α → ℕ} {c : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) {k e : ℕ} {t : β → ℕ}
    {a : α} {b : β} (ht : (t b : ℝ) ≤ k * (2 ^ (δ * μB b) * ((encB b).length + 1) ^ e) + k)
    (hμ : μB b ≤ c * μA a + c) (hlen : (encB b).length ≤ nd a) :
    t b ≤ leafTime μA nd c δ k e a := by
  have h₁ : (2 : ℝ) ^ (δ * μB b) ≤ 2 ^ (δ * ((c * μA a + c : ℕ) : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hμ) hδ)
  have h₂ : (((encB b).length : ℝ) + 1) ^ e ≤ ((nd a : ℝ) + 1) ^ e := by gcongr
  refine Nat.cast_le.mp (ht.trans ((?_ : _ ≤ _).trans (Nat.le_ceil _)))
  gcongr

/-- **Absorbing the overheads.** A running time `A + R * (B + ℓ)`, with polynomial overheads
`A, B ≤ a * P`, `R ≤ r * X` rounds and leaves within `ℓ ≤ b * Y * P + b'`, is within a constant
times `X * Y * P` when `X, Y, P ≥ 1`. -/
private theorem add_mul_add_le {A B R ℓ X Y P a r b b' : ℝ} (hA : A ≤ a * P) (hB : B ≤ a * P)
    (hR : R ≤ r * X) (hℓ : ℓ ≤ b * Y * P + b') (hR₀ : 0 ≤ R) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hb' : 0 ≤ b') (hX : 1 ≤ X) (hY : 1 ≤ Y) (hP : 1 ≤ P) :
    A + R * (B + ℓ) ≤ (a + r * (a + b + b')) * (X * Y * P) := by
  have hYP : 1 ≤ Y * P := one_le_mul_of_one_le_of_one_le hY hP
  have hP₀ : 0 ≤ P := zero_le_one.trans hP
  -- Each round costs at most `(a + b + b') * (Y * P)`.
  have hBℓ : B + ℓ ≤ (a + b + b') * (Y * P) := by
    have h₁ : a * P ≤ a * (Y * P) := by
      gcongr
      exact le_mul_of_one_le_left hP₀ hY
    have h₂ : b' ≤ b' * (Y * P) := le_mul_of_one_le_right hb' hYP
    linarith
  have h₁ : R * (B + ℓ) ≤ r * X * ((a + b + b') * (Y * P)) :=
    (mul_le_mul_of_nonneg_left hBℓ hR₀).trans (mul_le_mul_of_nonneg_right hR (by positivity))
  have h₂ : a * P ≤ a * (X * Y * P) := by
    gcongr
    exact le_mul_of_one_le_left hP₀ (one_le_mul_of_one_le_of_one_le hX hY)
  linarith

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
  -- The machine counts `rounds ν a = 2 ^ ν a` rounds in binary; round `r` queries the decider `g`
  -- for `B` on `f (a, r)`, and the accumulated answer is read off at the end.
  obtain ⟨e, h⟩ := h
  obtain ⟨g, t, k, hg, hgB, ht⟩ := h.exists_computableInO
  obtain ⟨d, hstep⟩ := exists_computableInO_step hf hg
  obtain ⟨dn, _, hn⟩ := (computableInPolyTime_rounds hν).exists_degree
  obtain ⟨di, _, hi⟩ := (computableInPolyTime_init (encA := encA)).exists_degree
  obtain ⟨da, _, ha⟩ := (show ComputableInPolyTime (fun s : State α => s.2)
    (encState encA) encBool by unfold encState; fun_prop).exists_degree
  obtain ⟨st, nd, hst, hnd, hstate, hrounds_len, hnd_bound⟩ := exists_search_length_bounds hf hν
  have hround (a : α) (j : ℕ) (hj : j ≤ rounds ν a) :
      ((encState encA ((step f g)^[j] (init a))).length + 1) ^ d +
        t (f ((step f g)^[j] (init a)).1) ≤ (st a + 1) ^ d + leafTime μA nd c δ k e a := by
    refine Nat.add_le_add (Nat.pow_le_pow_left (Nat.add_le_add_right (hstate g a j hj) 1) d) ?_
    rw [iterate_step_init]
    exact le_leafTime hδ (ht _) (hμ a j) (hnd_bound a j hj)
  have hsearch := ha.inO.comp
    (ComputableInO.iterate hn.inO hi.inO hstep hround hround (hstate g))
  -- Apart from the number of rounds and the leaves, the running time is polynomial.
  have hpoly : PolyBounded (fun a => (encA a).length) fun a =>
      ((encA a).length + 1) ^ dn + ((encA a).length + 1) ^ di + (st a + 1) ^ da +
        ((st a + 1) ^ d + st a + (st a + 1) ^ 2) + (nd a + 1) ^ e := by
    growth_poly
  obtain ⟨Cp, E, hCp⟩ := hpoly.exists_le
  refine DecidableInExpTime.of_computableInO hsearch
    (fun a => (search_eq_true_iff hfA (fun b => (hgB b).symm) a).symm)
    ⌈(Cp + (2 ^ K + 1) * (Cp + k * 2 ^ (c * δ) * Cp + (k + 1)) : ℝ)⌉₊ E fun a => ?_
  -- The polynomial overheads, the number of rounds and the leaves, bounded separately.
  have hP := hCp a
  have hA : ((encA a).length + 1) ^ dn + ((encA a).length + 1) ^ di +
      ((encState encA ((step f g)^[rounds ν a] (init a))).length + 1) ^ da ≤
      Cp * ((encA a).length + 1) ^ E := by
    have := Nat.pow_le_pow_left (Nat.add_le_add_right (hstate g a (rounds ν a) le_rfl) 1) da
    omega
  have hB : (st a + 1) ^ d + st a + ((encNat (rounds ν a)).length + 1) ^ 2 ≤
      Cp * ((encA a).length + 1) ^ E := by
    have := Nat.pow_le_pow_left (Nat.add_le_add_right (hrounds_len a) 1) 2
    omega
  have hR : ((rounds ν a + 1 : ℕ) : ℝ) ≤ (2 ^ K + 1) * 2 ^ ((1 / M : ℝ) * μA a) := by
    have h₁ : rounds ν a ≤ 2 ^ K * 2 ^ (μA a / M) := by
      rw [rounds, ← pow_add, add_comm K]
      exact Nat.pow_le_pow_right two_pos (hνM a)
    have h₂ : ((2 ^ (μA a / M) : ℕ) : ℝ) ≤ 2 ^ ((1 / M : ℝ) * μA a) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast, one_div_mul_eq_div]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) Nat.cast_div_le
    have h₃ : (1 : ℝ) ≤ ((2 ^ (μA a / M) : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow
    have h₄ : (rounds ν a : ℝ) ≤ 2 ^ K * ((2 ^ (μA a / M) : ℕ) : ℝ) := by exact_mod_cast h₁
    have h₅ := mul_le_mul_of_nonneg_left h₂ (by positivity : (0 : ℝ) ≤ 2 ^ K)
    rw [Nat.cast_succ]
    linarith
  have hleaf : (leafTime μA nd c δ k e a : ℝ) ≤
      k * 2 ^ (c * δ) * Cp * 2 ^ ((c * δ) * μA a) * ((encA a).length + 1) ^ E + (k + 1) := by
    have hexp : (2 : ℝ) ^ (δ * ((c * μA a + c : ℕ) : ℝ)) =
        2 ^ (c * δ) * 2 ^ ((c * δ) * μA a) := by
      rw [← Real.rpow_add (by norm_num)]
      congr 1
      push_cast
      ring
    have hnd : ((nd a : ℝ) + 1) ^ e ≤ Cp * ((encA a).length + 1) ^ E := by
      exact_mod_cast (show (nd a + 1) ^ e ≤ Cp * ((encA a).length + 1) ^ E by omega)
    have hceil := Nat.ceil_lt_add_one (show (0 : ℝ) ≤
      k * (2 ^ (δ * ((c * μA a + c : ℕ) : ℝ)) * ((nd a : ℝ) + 1) ^ e) + k by positivity)
    have := mul_le_mul_of_nonneg_left hnd
      (by positivity : (0 : ℝ) ≤ k * (2 ^ (c * δ) * 2 ^ ((c * δ) * μA a)))
    unfold leafTime
    rw [hexp] at hceil ⊢
    linarith
  have hA' := Nat.cast_le (α := ℝ) |>.mpr hA
  have hB' := Nat.cast_le (α := ℝ) |>.mpr hB
  push_cast at hA' hB' hR
  have key := add_mul_add_le hA' hB' hR hleaf (by positivity) (by positivity) (by positivity)
    (by positivity) (Real.one_le_rpow (by norm_num) (by positivity))
    (Real.one_le_rpow (by norm_num) (by positivity))
    (one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg _)))
  have hXY : (2 : ℝ) ^ ((1 / M + c * δ) * μA a) =
      2 ^ ((1 / M : ℝ) * μA a) * 2 ^ ((c * δ) * μA a) := by
    rw [← Real.rpow_add (by norm_num)]
    congr 1
    ring
  -- `key` is the claimed bound, up to rearranging the running time and rounding the constant up.
  rw [hXY]
  push_cast
  refine (?_ : _ ≤ _).trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity))
  linarith

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
