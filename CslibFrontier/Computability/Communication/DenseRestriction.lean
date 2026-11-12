/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Protocol
public import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-!
# Dense restrictions and the diagonal walk

The composition `U_m ⋄ KW_g` of the universal relation on `m` rows with the Karchmer–Wigderson
game of `g : BitString n → Bool` gives both players a matrix of `m` rows of `n` bits. They must
name a cell where the matrices differ, or reject when the row values `gᵐ` agree
(`composeKW`). Its restriction `R_g(X)` to `X × X` is `ecomplexity (composeKW g) X X`
([ChukhinKulikovMihajlinSmal2026], Section 6, printed p. 12; PDF p. 13, following
[DinurMeir2016]).

Lemma 6.7 (printed p. 18; PDF p. 19) derives composition lower bounds from lower bounds on dense
restrictions. If every `X` of density at least `2^{1-m}` has `CC(R_g(X)) ≥ d > 0`, then
`CC(U_m ⋄ KW_g) ≥ m - 1 + d` (`le_ecomplexity_composeKW`). The walk behind it is general
(`Protocol.exists_diagonal_subprotocol`). Follow a protocol on the diagonal pairs `(Z, Z)` of a
set, always into the child that keeps at least half of them. After `t` steps the remaining set
`X` has at least a `2^{-t}` fraction, and the current subprotocol answers like the original on
`X × X`. `le_ecomplexity_of_dense` packages this for any relation on one type.

This is infrastructure toward the source's Theorems 1.6–1.8. The dense-restriction lower bounds
themselves (Lemmas 6.1–6.5, Theorem 6.6) and those theorems remain open.

## Main definitions

* `Cslib.Communication.composeKW`: the relation `U_m ⋄ KW_g`, with rejection.

## Main results

* `Cslib.Communication.Protocol.exists_diagonal_subprotocol`: the diagonal walk.
* `Cslib.Communication.Protocol.le_ecomplexity_of_dense`: dense lower bounds lift.
* `Cslib.Communication.le_ecomplexity_composeKW`: Lemma 6.7.

## References

* [N. Chukhin, A. S. Kulikov, I. Mihajlin and A. V. Smal, *Solving One of Many Instances is
  Almost as Hard as Solving One*][ChukhinKulikovMihajlinSmal2026]
* [I. Dinur and O. Meir, *Toward the KRW Composition Conjecture: Cubic Formula Lower Bounds via
  Communication Complexity*][DinurMeir2016]
-/

public section

namespace Cslib.Communication

namespace Protocol

variable {U Z : Type*}

/-- **The diagonal walk.** For a protocol `p` with both players' inputs in `U`, a finite set `S`
and `t` steps, some `X ⊆ S` with `|S| ≤ 2 ^ t |X|` and some protocol `q` answer like `p` on
`X × X`. Either `q` is a leaf, or `p` spent `t` bits to reach it. -/
theorem exists_diagonal_subprotocol :
    ∀ (t : ℕ) (p : Protocol U U Z) (S : Finset U), ∃ X ⊆ S, S.card ≤ 2 ^ t * X.card ∧
      ∃ q : Protocol U U Z, (∀ x ∈ X, ∀ y ∈ X, q.run x y = p.run x y) ∧
        (q.depth = 0 ∨ q.depth + t ≤ p.depth)
  | 0, p, S => ⟨S, subset_rfl, by simp, p, fun _ _ _ _ => rfl, .inr (by simp)⟩
  | t + 1, .output z, S => ⟨S, subset_rfl, by
      have := Nat.one_le_two_pow (n := t + 1)
      nlinarith, .output z, fun _ _ _ _ => rfl, .inl rfl⟩
  | t + 1, .alice send p₀ p₁, S => by
    obtain ⟨b, hb⟩ : ∃ b : Bool, S.card ≤ 2 * (S.filter (send · = b)).card := by
      have := Finset.card_filter_add_card_filter_not (s := S) (p := fun x => send x = true)
      simp only [Bool.not_eq_true] at this
      by_cases h : (S.filter (send · = false)).card ≤ (S.filter (send · = true)).card
      · exact ⟨true, by omega⟩
      · exact ⟨false, by omega⟩
    obtain ⟨X, hXS, hX, q, hq, hd⟩ :=
      exists_diagonal_subprotocol t (cond b p₁ p₀) (S.filter (send · = b))
    refine ⟨X, hXS.trans (Finset.filter_subset _ _), ?_, q, fun x hx y hy => ?_, ?_⟩
    · rw [pow_succ]
      nlinarith
    · rw [hq x hx y hy, run_alice, (Finset.mem_filter.1 (hXS hx)).2]
      cases b <;> rfl
    · rcases hd with hd | hd
      · exact .inl hd
      · refine .inr ?_
        have h₀ := le_max_left p₀.depth p₁.depth
        have h₁ := le_max_right p₀.depth p₁.depth
        cases b <;> simp only [Bool.cond_true, Bool.cond_false, depth_alice] at hd ⊢ <;> omega
  | t + 1, .bob send p₀ p₁, S => by
    obtain ⟨b, hb⟩ : ∃ b : Bool, S.card ≤ 2 * (S.filter (send · = b)).card := by
      have := Finset.card_filter_add_card_filter_not (s := S) (p := fun x => send x = true)
      simp only [Bool.not_eq_true] at this
      by_cases h : (S.filter (send · = false)).card ≤ (S.filter (send · = true)).card
      · exact ⟨true, by omega⟩
      · exact ⟨false, by omega⟩
    obtain ⟨X, hXS, hX, q, hq, hd⟩ :=
      exists_diagonal_subprotocol t (cond b p₁ p₀) (S.filter (send · = b))
    refine ⟨X, hXS.trans (Finset.filter_subset _ _), ?_, q, fun x hx y hy => ?_, ?_⟩
    · rw [pow_succ]
      nlinarith
    · rw [hq x hx y hy, run_bob, (Finset.mem_filter.1 (hXS hy)).2]
      cases b <;> rfl
    · rcases hd with hd | hd
      · exact .inl hd
      · refine .inr ?_
        have h₀ := le_max_left p₀.depth p₁.depth
        have h₁ := le_max_right p₀.depth p₁.depth
        cases b <;> simp only [Bool.cond_true, Bool.cond_false, depth_bob] at hd ⊢ <;> omega

/-- **Dense lower bounds lift.** If every `X` with `|U| ≤ 2 ^ t |X|` has `CC(R, X × X) ≥ d`, for
some `d > 0`, then `CC(R) ≥ t + d`: a protocol for `R` is followed for `t` steps on the diagonal,
and the subprotocol reached solves `R` on a dense square. -/
theorem le_ecomplexity_of_dense [Fintype U] {R : U → U → Z → Prop} {t d : ℕ}
    (hd : 0 < d) (h : ∀ X : Finset U, Fintype.card U ≤ 2 ^ t * X.card →
      (d : ℕ∞) ≤ ecomplexity R (X : Set U) (X : Set U)) :
    ((t + d : ℕ) : ℕ∞) ≤ ecomplexity R Set.univ Set.univ := by
  refine le_ecomplexity_iff.2 fun p hp => ?_
  obtain ⟨X, -, hX, q, hq, hqd⟩ := exists_diagonal_subprotocol t p Finset.univ
  have hqs : q.Solves R (X : Set U) (X : Set U) := fun x hx y hy => by
    rw [hq x hx y hy]
    exact hp x trivial y trivial
  have hdq : d ≤ q.depth := by
    have := (h X (by simpa using hX)).trans (ecomplexity_le_depth hqs)
    exact_mod_cast this
  rcases hqd with hqd | hqd
  · omega
  · exact_mod_cast (by omega : t + d ≤ p.depth)

end Protocol

variable {n m : ℕ}

/-- **The composition `U_m ⋄ KW_g`**, with rejection. The players hold matrices `A` and `B` of `m`
rows of `n` bits. An answer `some (i, j)` is valid when `A` and `B` differ in cell `(i, j)`, and
the rejection `none` is valid when every row has the same value of `g` in `A` and in `B`. Its
restriction `R_g(X)` to a set `X` of matrices is `ecomplexity (composeKW g) X X`. -/
@[expose] def composeKW (g : BitString n → Bool) (A B : Fin m → BitString n) :
    Option (Fin m × Fin n) → Prop
  | some c => A c.1 c.2 ≠ B c.1 c.2
  | none => ∀ i, g (A i) = g (B i)

/-- **[ChukhinKulikovMihajlinSmal2026], Lemma 6.7.** If every set `X` of matrices of density at
least `2^{1-m}` (that is, `2^{mn} ≤ 2^{m-1} |X|`) has `CC(R_g(X)) ≥ d > 0`, then
`CC(U_m ⋄ KW_g) ≥ m - 1 + d`. The source's hypotheses that `g` is nonconstant and `m ≥ 1` are not
needed. -/
theorem le_ecomplexity_composeKW {g : BitString n → Bool} {d : ℕ} (hd : 0 < d)
    (h : ∀ X : Finset (Fin m → BitString n),
      2 ^ (m * n) ≤ 2 ^ (m - 1) * X.card →
        (d : ℕ∞) ≤ Protocol.ecomplexity (composeKW g) (X : Set (Fin m → BitString n))
          (X : Set (Fin m → BitString n))) :
    ((m - 1 + d : ℕ) : ℕ∞) ≤ Protocol.ecomplexity (composeKW (m := m) g) Set.univ Set.univ :=
  Protocol.le_ecomplexity_of_dense hd fun X hX => h X (by
    simpa [Fintype.card_fun, Fintype.card_bool, ← pow_mul, mul_comm] using hX)

end Cslib.Communication
