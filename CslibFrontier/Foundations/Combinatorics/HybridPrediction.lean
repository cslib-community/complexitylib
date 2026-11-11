/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Predicting one of several masked channels from a decoder

Let `E t : Z t → Bool`, for `t < T`, be `T` channels on finite sets. Suppose a decoder `D` recovers
a bit `b` from the `T` pairs `(z t, E t (z t) + b)` for every choice of the inputs `z` and of `b`.
The same `b` masks every channel, so `b` is XOR-shared across them. Then `D` predicts one of the
channels. For some `t`, some fixed pairs `base` at the other positions and some fixed trial bit
`y₀`, the guess `y₀ + D (update base t (z, y₀))` equals `E t z` for at least a
`1 / 2 + 1 / (2 T)` fraction of the inputs `z ∈ Z t` (`exists_card_add_decode_update_eq`).

The proof is Yao's hybrid argument [Yao1982] with the predictor's random choices fixed, done by
counting. It follows the telescoping proof of the next-bit theorem in
[Boneh and Shoup, Section 3.5][BonehShoup2023].
- Hybrid `i` shows `D` the pairs `(z t, E t (z t) + b)` for `t < i` and `(z t, u t)` for `t ≥ i`,
  where the bits `u t` are uniform.
- In hybrid `T`, `D` returns `b` on every sample.
- In hybrid `0`, the masks are uniform, so `D`'s input does not depend on `b`. This is the privacy
  of the XOR sharing, and it means `D` returns `b` on exactly half of the samples.
- Some adjacent pair of hybrids therefore differs by at least `1 / (2 T)`. The predictor for
  channel `i` inserts its trial bit `u i` at position `i` and returns `u i + D (…)`, which is
  correct exactly as often as `1 / 2` plus that difference.
- Averaging over the other coordinates fixes them as `base`.

`Cslib.Crypto.PRG.Generator.exists_half_add_div_le_predictionExperiment` proves the same telescoping
for the output bits of a generator, but it does not apply here. Its predictor guesses an output bit
from the bits before it, with no public side input and no shared secret. Encoding the inputs
`z t` and the secret `b` as generator output would count the bits of every `z t` among the hybrid
positions, which weakens `1 / (2 T)` to roughly `1 / (2 (T + ∑ t, log₂ #(Z t)))`.

## Main results

* `Cslib.exists_card_add_decode_update_eq`: a decoder for an XOR-shared bit predicts one of the
  channels on a `1 / 2 + 1 / (2 T)` fraction of its inputs.

## References

* [A. C. Yao, *Theory and Application of Trapdoor Functions*][Yao1982]
* [D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023]
-/

public section

namespace Cslib

open Finset Function

variable {T : ℕ} {Z : Fin T → Type*}

/-- The samples of the hybrid argument: the secret bit, the channel inputs and the uniform bits. -/
private abbrev Sample (Z : Fin T → Type*) := Bool × (∀ t, Z t) × (Fin T → Bool)

/-- Hybrid `i`: channel `t` shows `E t (z t) + b` for `t < i` and the uniform bit `u t` for
`t ≥ i`. -/
private def hybrid (E : ∀ t, Z t → Bool) (i : ℕ) (ω : Sample Z) : ∀ t, Z t × Bool :=
  fun t => (ω.2.1 t, if (t : ℕ) < i then E t (ω.2.1 t) + ω.1 else ω.2.2 t)

private theorem update_hybrid_self (E : ∀ t, Z t → Bool) (i : Fin T) (b : Bool) (z : ∀ t, Z t)
    (u : Fin T → Bool) : update (hybrid E i (b, z, u)) i (z i, u i) = hybrid E i (b, z, u) :=
  update_eq_self_iff.2 (by simp [hybrid])

private theorem hybrid_update_u (E : ∀ t, Z t → Bool) (i : Fin T) (b : Bool) (z : ∀ t, Z t)
    (u : Fin T → Bool) (y : Bool) :
    hybrid E i (b, z, update u i y) = update (hybrid E i (b, z, u)) i (z i, y) := by
  funext t
  by_cases h : t = i
  · subst h
    simp [hybrid]
  · simp [hybrid, update_of_ne h]

private theorem hybrid_update_z (E : ∀ t, Z t → Bool) (i : Fin T) (b : Bool) (z : ∀ t, Z t)
    (u : Fin T → Bool) (x : Z i) :
    hybrid E i (b, update z i x, u) = update (hybrid E i (b, z, u)) i (x, u i) := by
  funext t
  by_cases h : t = i
  · subst h
    simp [hybrid]
  · simp [hybrid, update_of_ne h]

private theorem hybrid_succ (E : ∀ t, Z t → Bool) (i : Fin T) (b : Bool) (z : ∀ t, Z t)
    (u : Fin T → Bool) :
    hybrid E ((i : ℕ) + 1) (b, z, u) = update (hybrid E i (b, z, u)) i (z i, E i (z i) + b) := by
  funext t
  by_cases h : t = i
  · subst h
    simp [hybrid]
  · have hne : (t : ℕ) ≠ i := fun h' => h (Fin.ext h')
    have hlt : (t : ℕ) < i + 1 ↔ (t : ℕ) < i := by omega
    simp [hybrid, update_of_ne h, hlt]

/-- The two samples that differ in the trial bit `u` contribute the same to both sides. Here
`g y` is the decoder's output with `y` at the predicted position, `e` is the channel's value and
`b` is the secret. -/
private theorem pair_identity (g : Bool → Bool) (u v e b : Bool) (hv : v = !u) :
    ((if u + g u = e then 1 else 0) + (if v + g v = e then 1 else 0) +
      (if g u = b then 1 else 0) + (if g v = b then 1 else 0) : ℕ) =
      1 + 2 * (if g (e + b) = b then 1 else 0) := by
  subst hv
  cases u <;> cases e <;> cases b <;> cases h0 : g false <;> cases h1 : g true <;>
    simp [Bool.add_eq_xor, h0, h1]

variable [∀ t, Fintype (Z t)]

/-- The number of samples on which the decoder returns the secret in hybrid `i`. -/
private def hits (E : ∀ t, Z t → Bool) (D : (∀ t, Z t × Bool) → Bool) (i : ℕ) : ℕ :=
  #{ω : Sample Z | D (hybrid E i ω) = ω.1}

/-- The number of samples on which the trial predictor for channel `i` is correct. -/
private def guesses (E : ∀ t, Z t → Bool) (D : (∀ t, Z t × Bool) → Bool) (i : Fin T) : ℕ :=
  #{ω : Sample Z | ω.2.2 i + D (hybrid E i ω) = E i (ω.2.1 i)}

/-- The trial predictor for channel `i` is correct on half of the samples plus the difference
between hybrids `i + 1` and `i`. -/
private theorem guesses_step (E : ∀ t, Z t → Bool) (D : (∀ t, Z t × Bool) → Bool) (i : Fin T) :
    2 * guesses E D i + 2 * hits E D i =
      Fintype.card (Sample Z) + 2 * hits E D ((i : ℕ) + 1) := by
  let τ : Sample Z → Sample Z := fun ω => (ω.1, ω.2.1, update ω.2.2 i (!ω.2.2 i))
  have hτ : Involutive τ := by
    rintro ⟨b, z, u⟩
    simp [τ]
  let G : Sample Z → ℕ := fun ω => if ω.2.2 i + D (hybrid E i ω) = E i (ω.2.1 i) then 1 else 0
  let H : ℕ → Sample Z → ℕ := fun j ω => if D (hybrid E j ω) = ω.1 then 1 else 0
  have hG : ∑ ω, G (τ ω) = ∑ ω, G ω := Equiv.sum_comp (Involutive.toPerm τ hτ) G
  have hH : ∑ ω, H i (τ ω) = ∑ ω, H i ω := Equiv.sum_comp (Involutive.toPerm τ hτ) (H i)
  have key (b : Bool) (z : ∀ t, Z t) (u : Fin T → Bool) :
      G (b, z, u) + G (τ (b, z, u)) + H i (b, z, u) + H i (τ (b, z, u)) =
        1 + 2 * H ((i : ℕ) + 1) (b, z, u) := by
    simp only [G, H, τ, hybrid_update_u, update_self, hybrid_succ]
    have h := pair_identity (fun y => D (update (hybrid E i (b, z, u)) i (z i, y))) (u i)
      (!u i) (E i (z i)) b rfl
    rw [update_hybrid_self] at h
    exact h
  have htot : ∑ ω, (G ω + G (τ ω) + H i ω + H i (τ ω)) =
      ∑ ω, (1 + 2 * H ((i : ℕ) + 1) ω) :=
    sum_congr rfl fun ⟨b, z, u⟩ _ => key b z u
  simp only [sum_add_distrib, hG, hH, ← mul_sum, sum_const, card_univ, smul_eq_mul,
    mul_one] at htot
  have hg : guesses E D i = ∑ ω, G ω := card_filter _ _
  have hh (j : ℕ) : hits E D j = ∑ ω, H j ω := card_filter _ _
  rw [hg, hh, hh]
  omega

/-- In hybrid `0` the decoder's input does not depend on the secret, so it returns the secret on
exactly half of the samples. -/
private theorem two_mul_hits_zero (E : ∀ t, Z t → Bool) (D : (∀ t, Z t × Bool) → Bool) :
    2 * hits E D 0 = Fintype.card (Sample Z) := by
  let σ : Sample Z → Sample Z := fun ω => (!ω.1, ω.2)
  have hσ : Involutive σ := by
    rintro ⟨b, z, u⟩
    simp [σ]
  let F : Sample Z → ℕ := fun ω => if D (hybrid E 0 ω) = ω.1 then 1 else 0
  have hsum : ∑ ω, F (σ ω) = ∑ ω, F ω := Equiv.sum_comp (Involutive.toPerm σ hσ) F
  have hpair (b : Bool) (z : ∀ t, Z t) (u : Fin T → Bool) : F (b, z, u) + F (σ (b, z, u)) = 1 := by
    have h0 : hybrid E 0 (!b, z, u) = hybrid E 0 (b, z, u) := by
      funext t
      simp [hybrid]
    dsimp only [F, σ]
    rw [h0]
    generalize D (hybrid E 0 (b, z, u)) = d
    cases d <;> cases b <;> simp
  have hF : hits E D 0 = ∑ ω, F ω := card_filter _ _
  calc 2 * hits E D 0 = ∑ ω, (F ω + F (σ ω)) := by rw [sum_add_distrib, hsum, hF, two_mul]
    _ = ∑ _ω : Sample Z, 1 := sum_congr rfl fun ⟨b, z, u⟩ _ => hpair b z u
    _ = Fintype.card (Sample Z) := by simp

/-- In hybrid `T` every channel is masked by the secret, so the decoder always returns it. -/
private theorem hits_top (E : ∀ t, Z t → Bool) (D : (∀ t, Z t × Bool) → Bool)
    (hD : ∀ (z : ∀ t, Z t) b, D (fun t => (z t, E t (z t) + b)) = b) :
    hits E D T = Fintype.card (Sample Z) := by
  rw [hits, filter_true_of_mem, card_univ]
  rintro ⟨b, z, u⟩ -
  have h : hybrid E T (b, z, u) = fun t => (z t, E t (z t) + b) := by
    funext t
    simp [hybrid, t.isLt]
  rw [h]
  exact hD z b

/-- **Predicting a masked channel.** Let `D` recover `b` from the pairs `(z t, E t (z t) + b)`,
`t < T`, for every choice of the inputs `z` and the bit `b`. Then for some channel `t`, some pairs
`base` and some trial bit `y₀`, the guess `y₀ + D (update base t (z, y₀))` equals `E t z` for at
least a `1 / 2 + 1 / (2 T)` fraction of the inputs `z ∈ Z t`. There is a channel: with none, `D`
would return both bits on its one input. -/
theorem exists_card_add_decode_update_eq [∀ t, Nonempty (Z t)]
    (E : ∀ t, Z t → Bool) (D : (∀ t, Z t × Bool) → Bool)
    (hD : ∀ (z : ∀ t, Z t) b, D (fun t => (z t, E t (z t) + b)) = b) :
    ∃ (t : Fin T) (base : ∀ t, Z t × Bool) (y₀ : Bool),
      Fintype.card (Z t) * (T + 1) ≤
        2 * T * #{z : Z t | y₀ + D (update base t (z, y₀)) = E t z} := by
  -- With no channels, `D` would return both bits on its one input.
  have hT : 0 < T := by
    refine Nat.pos_of_ne_zero fun hT0 => ?_
    subst hT0
    have h₀ := hD (fun t => t.elim0) false
    have h₁ := hD (fun t => t.elim0) true
    have : (fun t : Fin 0 => ((fun t => t.elim0 : ∀ t, Z t) t,
        E t ((fun t => t.elim0 : ∀ t, Z t) t) + false)) =
        fun t => ((fun t => t.elim0 : ∀ t, Z t) t, E t ((fun t => t.elim0 : ∀ t, Z t) t) + true) :=
      funext fun t => t.elim0
    rw [this] at h₀
    exact Bool.false_ne_true (h₀.symm.trans h₁)
  -- The hybrid gaps telescope.
  have hsumG : 2 * ∑ i, guesses E D i = (T + 1) * Fintype.card (Sample Z) := by
    have h1 := sum_congr rfl fun i (_ : i ∈ (univ : Finset (Fin T))) => guesses_step E D i
    simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin,
      smul_eq_mul] at h1
    have r1 : ∑ i : Fin T, hits E D i = ∑ i ∈ range T, hits E D i :=
      Fin.sum_univ_eq_sum_range (hits E D) T
    have r2 : ∑ i : Fin T, hits E D ((i : ℕ) + 1) = ∑ i ∈ range T, hits E D (i + 1) :=
      Fin.sum_univ_eq_sum_range (fun i => hits E D (i + 1)) T
    have h2 := sum_range_succ (hits E D) T
    have h3 := sum_range_succ' (hits E D) T
    have h4 := two_mul_hits_zero E D
    have h5 := hits_top E D hD
    linarith
  -- Some channel's predictor beats the average.
  obtain ⟨i, -, hi⟩ := exists_le_of_sum_le (s := univ) (f := fun _ => (T + 1) *
      Fintype.card (Sample Z)) (g := fun i => 2 * T * guesses E D i) ⟨⟨0, hT⟩, mem_univ _⟩ (by
    rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, ← mul_sum, ← hsumG]
    exact le_of_eq (by ring))
  -- Fixing everything but the input of channel `i` keeps the advantage for some fixing.
  have hQ : ∑ ω : Sample Z,
      #{x : Z i | ω.2.2 i + D (update (hybrid E i ω) i (x, ω.2.2 i)) = E i x} =
        Fintype.card (Z i) * guesses E D i := by
    let φ : Sample Z × Z i → Sample Z × Z i :=
      fun p => ((p.1.1, update p.1.2.1 i p.2, p.1.2.2), p.1.2.1 i)
    have hφ : Involutive φ := by
      rintro ⟨⟨b, z, u⟩, x⟩
      simp [φ]
    let F : Sample Z × Z i → ℕ := fun p =>
      if p.1.2.2 i + D (update (hybrid E i p.1) i (p.2, p.1.2.2 i)) = E i p.2 then 1 else 0
    have hpt (b : Bool) (z : ∀ t, Z t) (u : Fin T → Bool) (x : Z i) :
        F (φ ((b, z, u), x)) = if u i + D (hybrid E i (b, z, u)) = E i (z i) then 1 else 0 := by
      dsimp only [F, φ]
      rw [hybrid_update_z, update_idem, update_hybrid_self]
    calc ∑ ω : Sample Z,
          #{x : Z i | ω.2.2 i + D (update (hybrid E i ω) i (x, ω.2.2 i)) = E i x}
        = ∑ ω : Sample Z, ∑ x : Z i, F (ω, x) := by simp only [card_filter, F]
      _ = ∑ p, F p := (Fintype.sum_prod_type F).symm
      _ = ∑ p, F (φ p) := (Equiv.sum_comp (Involutive.toPerm φ hφ) F).symm
      _ = ∑ ω : Sample Z, ∑ _x : Z i,
          if ω.2.2 i + D (hybrid E i ω) = E i (ω.2.1 i) then 1 else 0 := by
        rw [Fintype.sum_prod_type]
        refine sum_congr rfl ?_
        rintro ⟨b, z, u⟩ -
        exact sum_congr rfl fun x _ => hpt b z u x
      _ = Fintype.card (Z i) * guesses E D i := by
        simp only [sum_const, card_univ, smul_eq_mul, guesses, card_filter, mul_sum]
  obtain ⟨ω, -, hω⟩ := exists_le_of_sum_le (s := univ)
    (f := fun _ => Fintype.card (Z i) * (T + 1))
    (g := fun ω => 2 * T *
      #{x : Z i | ω.2.2 i + D (update (hybrid E i ω) i (x, ω.2.2 i)) = E i x})
    univ_nonempty (by
      rw [sum_const, card_univ, smul_eq_mul, ← mul_sum, hQ]
      calc Fintype.card (Sample Z) * (Fintype.card (Z i) * (T + 1))
          = Fintype.card (Z i) * ((T + 1) * Fintype.card (Sample Z)) := by ring
        _ ≤ Fintype.card (Z i) * (2 * T * guesses E D i) := Nat.mul_le_mul_left _ hi
        _ = 2 * T * (Fintype.card (Z i) * guesses E D i) := by ring)
  exact ⟨i, hybrid E i ω, ω.2.2 i, hω⟩

end Cslib
