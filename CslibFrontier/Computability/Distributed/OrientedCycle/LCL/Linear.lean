/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.OrientedCycle.LCL.Basic
import CslibFrontier.Foundations.Relation.RelatesWithinSteps
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.FrobeniusNumber
import Mathlib.Tactic.Ring

/-!
# LCL problems without a flexible state on oriented cycles need `Θ(n)` rounds

Let `R : L → L → Prop` be an LCL problem on oriented cycles with finitely many labels
(`CslibFrontier.Computability.Distributed.OrientedCycle.LCL.Basic`). This file proves the last row
of the classification of [Chang, Studený and Suomela][ChangStudenySuomela2023] (Table 1) for
directed cycles.

* **Lower bound** (`Algorithm.SolvesLCL.le_of_forall_not_isFlexible`; their Thm 6.5 via
  Lemma 6.3). If no state of `R` is flexible, every `t`-round algorithm solving `R` on the
  oriented `n`-cycle with identifiers `{0, …, n - 1}` has `n ≤ (|L| + 1) (2t + 1)`.
* **Upper bound** (`LCL.IsSolution.exists_solvesLCL`). If the `n`-cycle has a solution at all,
  some algorithm solves `R` on it in `⌊n / 2⌋` rounds (`LCL.gatherRule`): each node sees the whole
  cycle, finds the node with identifier `0` and outputs the matching rotation of a fixed solution.
  Like the other algorithms here it depends on `n`, and it relies on the identifiers being exactly
  `{0, …, n - 1}`; with a larger identifier range it would locate the minimum identifier instead.

`LCL.IsSolution.exists_solvesLCL_and_le_of_forall_not_isFlexible` packages both directions:
problems without a flexible state have round complexity `Θ(n)` on the cycles where they are
solvable.

Theorem 6.5 of the source also assumes a *repeatable* state, that is, a closed walk `q ⇝ q`. That
assumption only ensures that `R` is solvable on infinitely many cycles, and here it is replaced by
stating the bounds for each `n` on which `R` is solvable. The lower bound needs no solvability
assumption, since `Algorithm.SolvesLCL A R n t` already provides solutions. Only directed cycles
are covered; the source's paths and undirected cycles (Thm 6.7) are not.

## Proof of the lower bound

Fix the identifiers `x₀ v = v.val`. By pigeonhole, two of the `|L| + 1` nodes
`t + i (2t + 1)`, `i ≤ |L|`, get the same output `q`; call them `p < p'`. Their radius-`t` windows
are disjoint and do not wrap around the cycle. Along the solution, the outputs from `p` to `p'`
form a closed walk `q ⇝ q` of length `d = p' - p`. Now move the node at position `p' + t + 1` to
position `p + t + 1`, shifting the nodes in between by one; this permutes the identifiers. The
windows of `p` and of `p' + 1` in the new cycle are those of `p` and `p'` in the old one, so both
still output `q`, which gives a closed walk `q ⇝ q` of length `d + 1`. Closed walks of the coprime
lengths `d` and `d + 1` generate all lengths from `d * d` on (the Chicken McNugget theorem
`frobeniusNumber_pair`), so `q` is flexible (`LCL.IsFlexible.of_consecutive`), a contradiction.

The source moves nodes repeatedly until it reaches a length with no closed walk. A single move
together with the Frobenius number of `{d, d + 1}` suffices here. This is a difference in proof
route, not a new result; it gives the explicit bound above.

## Main definitions

* `Cslib.Distributed.OrientedCycle.LCL.gatherRule`: the gathering rule.

## Main results

* `Cslib.Distributed.OrientedCycle.LCL.IsSolution.relatesInSteps`: along a solution, labels at
  distance `m` are joined by a walk of length `m`.
* `Cslib.Distributed.OrientedCycle.LCL.IsFlexible.of_consecutive`: closed walks of lengths `d` and
  `d + 1` make a state flexible.
* `Cslib.Distributed.OrientedCycle.LocalRule.le_of_forall_not_isFlexible` and
  `Cslib.Distributed.OrientedCycle.Algorithm.SolvesLCL.le_of_forall_not_isFlexible`: the `Ω(n)`
  lower bound.
* `Cslib.Distributed.OrientedCycle.LCL.gatherRule_isSolution`: if `n ≤ 2r + 1`, the gathering
  rule of radius `r` outputs a solution.
* `Cslib.Distributed.OrientedCycle.LCL.IsSolution.exists_solvesLCL`: the `⌊n / 2⌋` upper bound.
* `Cslib.Distributed.OrientedCycle.LCL.IsSolution.exists_solvesLCL_and_le_of_forall_not_isFlexible`:
  `Θ(n)`.

## References

* [Y.-J. Chang, J. Studený and J. Suomela, *Distributed graph problems through an
  automata-theoretic lens*][ChangStudenySuomela2023]
-/

public section

namespace Cslib.Distributed.OrientedCycle.LCL

variable {L : Type*} {R : L → L → Prop}

/-! ### Walks along solutions -/

/-- Along a solution, labels at distance `m` are joined by an `R`-walk of length `m`. -/
theorem IsSolution.relatesInSteps {n : ℕ} {ℓ : ZMod n → L} (h : IsSolution R ℓ) (v : ZMod n)
    (m : ℕ) : Relation.RelatesInSteps R (ℓ v) (ℓ (v + m)) m := by
  induction m with
  | zero =>
    rw [Nat.cast_zero, add_zero]
    exact .refl _
  | succ m ih =>
    refine .tail _ _ _ m ih ?_
    have := h (v + m)
    rwa [add_assoc, ← Nat.cast_succ] at this

/-- Closed walks of two consecutive lengths `d` and `d + 1` make `q` flexible with flexibility
`d * d` (the Frobenius number of `{d, d + 1}` is `d * (d + 1) - d - (d + 1) < d * d`). -/
theorem IsFlexible.of_consecutive {q : L} {d : ℕ} (hd : Relation.RelatesInSteps R q q d)
    (hd1 : Relation.RelatesInSteps R q q (d + 1)) : IsFlexible R q (d * d) := by
  rcases Nat.lt_or_ge d 2 with h2 | h2
  · obtain rfl | rfl : d = 0 ∨ d = 1 := by omega
    · obtain ⟨t', h0, hq⟩ := hd1.succ
      rw [Relation.RelatesInSteps.zero_iff] at h0
      subst h0
      exact fun m _ => IsFlexible.of_loop hq m (Nat.zero_le _)
    · obtain ⟨t', h0, hq⟩ := hd.succ
      rw [Relation.RelatesInSteps.zero_iff] at h0
      subst h0
      exact fun m _ => IsFlexible.of_loop hq m (Nat.zero_le _)
  intro m hm
  have hF := (frobeniusNumber_iff.1 (frobeniusNumber_pair
    (Nat.coprime_self_add_right.2 (Nat.coprime_one_right d)) h2 (by omega))).2 m (by
      have : d * (d + 1) = d * d + d := by ring
      have : 4 ≤ d * d := Nat.mul_le_mul h2 h2
      omega)
  obtain ⟨i, j, hij⟩ := (AddSubmonoid.mem_closure_pair _ _ _).1 hF
  simp only [smul_eq_mul] at hij
  rw [← hij, ← zero_add (i * d)]
  exact ((Relation.RelatesInSteps.refl q).add_mul_of_cycle hd i).add_mul_of_cycle hd1 j

/-! ### The lower bound -/

/-- `(k : ZMod n) + o` is the image of the natural number `k + o ≥ 0`. -/
private theorem natCast_add_intCast {n k : ℕ} {o : ℤ} (h : 0 ≤ (k : ℤ) + o) :
    (k : ZMod n) + (o : ZMod n) = ((((k : ℤ) + o).toNat : ℕ) : ZMod n) := by
  rw [← Int.cast_natCast (R := ZMod n) (((k : ℤ) + o).toNat), Int.toNat_of_nonneg h, Int.cast_add,
    Int.cast_natCast]

/-- The moving step of the lower bound. With identifiers `x₀ v = v.val`, suppose a rule of radius
`t` outputs the same label at nodes `p` and `p'` whose windows are disjoint and do not wrap
around. Moving the node `p' + t + 1` to position `p + t + 1` keeps both windows, now at `p` and
`p' + 1`, so the label has closed walks of lengths `p' - p` and `p' - p + 1`. -/
private theorem isFlexible_of_apply_eq {t n : ℕ} [NeZero n] (F : LocalRule ℕ L t)
    (hF : ∀ x : ZMod n → ℕ, Function.Injective x → (∀ v, x v < n) → IsSolution R (F.apply x))
    {p p' : ℕ} (hp : t ≤ p) (hpp' : p + 2 * t + 1 ≤ p') (hp'n : p' + t + 1 < n)
    (hq : F.apply (fun v : ZMod n => v.val) p = F.apply (fun v : ZMod n => v.val) p') :
    IsFlexible R (F.apply (fun v : ZMod n => v.val) p) ((p' - p) * (p' - p)) := by
  set x₀ : ZMod n → ℕ := fun v => v.val with hx₀def
  have hx₀ : Function.Injective x₀ := ZMod.val_injective n
  have hx₀n : ∀ v, x₀ v < n := fun v => ZMod.val_lt v
  have hval : ∀ k < n, x₀ (k : ZMod n) = k := fun k hk => ZMod.val_cast_of_lt hk
  have h1 := (hF x₀ hx₀ hx₀n).relatesInSteps (p : ZMod n) (p' - p)
  rw [← Nat.cast_add, Nat.add_sub_cancel' (by omega), ← hq] at h1
  set σ : ℕ → ℕ := fun k => if k ≤ p + t then k else if k = p + t + 1 then p' + t + 1
    else if k ≤ p' + t + 1 then k - 1 else k with hσ
  have hσinj : Function.Injective σ := by
    intro a b h
    simp only [hσ] at h
    split_ifs at h <;> omega
  have hσn : ∀ k < n, σ k < n := by
    intro k hk
    simp only [hσ]
    split_ifs <;> omega
  set x₁ : ZMod n → ℕ := fun v => σ v.val with hx₁def
  have hx₁ : Function.Injective x₁ := hσinj.comp (ZMod.val_injective n)
  have hx₁n : ∀ v, x₁ v < n := fun v => hσn _ (ZMod.val_lt v)
  have hval₁ : ∀ k < n, x₁ (k : ZMod n) = σ k := fun k hk => by
    simp only [hx₁def, ZMod.val_cast_of_lt hk]
  have e0 : F.apply x₁ (p : ZMod n) = F.apply x₀ (p : ZMod n) := by
    refine F.toFun_congr fun o ho₁ ho₂ => ?_
    simp only [window]
    rw [natCast_add_intCast (by omega), hval₁ _ (by omega), hval _ (by omega)]
    simp only [hσ]
    split_ifs <;> omega
  have e1 : F.apply x₁ ((p' + 1 : ℕ) : ZMod n) = F.apply x₀ (p' : ZMod n) := by
    refine F.toFun_congr fun o ho₁ ho₂ => ?_
    simp only [window]
    rw [natCast_add_intCast (by omega), natCast_add_intCast (by omega), hval₁ _ (by omega),
      hval _ (by omega)]
    simp only [hσ]
    split_ifs <;> omega
  have h2 := (hF x₁ hx₁ hx₁n).relatesInSteps (p : ZMod n) (p' - p + 1)
  rw [← Nat.cast_add, show p + (p' - p + 1) = p' + 1 by omega, e0, e1, ← hq] at h2
  exact IsFlexible.of_consecutive h1 h2

end Cslib.Distributed.OrientedCycle.LCL

namespace Cslib.Distributed.OrientedCycle

open LCL

/-- **Problems without a flexible state need `Ω(n)` rounds, for rules.** If a rule of radius `t`
solves `R` on the oriented `n`-cycle for every identifier bijection onto `{0, …, n - 1}` and no
state of `R` is flexible, then `n ≤ (|L| + 1) (2t + 1)`. -/
theorem LocalRule.le_of_forall_not_isFlexible {L : Type*} [Fintype L] {R : L → L → Prop}
    {t n : ℕ} (F : LocalRule ℕ L t)
    (hF : ∀ x : ZMod n → ℕ, Function.Injective x → (∀ v, x v < n) → IsSolution R (F.apply x))
    (hR : ∀ q K, ¬IsFlexible R q K) : n ≤ (Fintype.card L + 1) * (2 * t + 1) := by
  by_contra hn
  push Not at hn
  have : NeZero n := ⟨by omega⟩
  obtain ⟨i, j, hij, hq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (Fintype.card L + 1) =>
      F.apply (fun v : ZMod n => v.val) ((t + i * (2 * t + 1) : ℕ) : ZMod n)) (by simp)
  wlog hlt : i < j generalizing i j
  · exact this j i hij.symm hq.symm (lt_of_le_of_ne (not_lt.1 hlt) hij.symm)
  have hj := j.isLt
  have h1 : ((i : ℕ) + 1) * (2 * t + 1) ≤ (j : ℕ) * (2 * t + 1) := Nat.mul_le_mul_right _ hlt
  have h2 : ((j : ℕ) + 1) * (2 * t + 1) ≤ (Fintype.card L + 1) * (2 * t + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  rw [add_one_mul] at h1 h2
  exact hR _ _ (isFlexible_of_apply_eq F hF (p := t + i * (2 * t + 1))
    (p' := t + j * (2 * t + 1)) (by omega) (by omega) (by omega) hq)

/-- **Problems without a flexible state need `Ω(n)` rounds** ([Chang, Studený and
Suomela][ChangStudenySuomela2023], Thm 6.5 and Lemma 6.3, directed cycles). Every `t`-round
algorithm solving `R` on the oriented `n`-cycle has `n ≤ (|L| + 1) (2t + 1)`. -/
theorem Algorithm.SolvesLCL.le_of_forall_not_isFlexible {S L : Type*} [Fintype L]
    {A : Algorithm ℕ S L} {R : L → L → Prop} {n t : ℕ} (hA : A.SolvesLCL R n t)
    (hR : ∀ q K, ¬IsFlexible R q K) : n ≤ (Fintype.card L + 1) * (2 * t + 1) :=
  (A.toLocalRule t).le_of_forall_not_isFlexible (fun x hx hxn => by
    have := hA x hx hxn
    rwa [show A.run x t = (A.toLocalRule t).apply x from funext (A.run_eq_apply x t)] at this) hR

end Cslib.Distributed.OrientedCycle

namespace Cslib.Distributed.OrientedCycle.LCL

/-! ### The upper bound -/

/-- Some index `i < m` with `f i = 0`, chosen if one exists. -/
private noncomputable def zeroIndex {m : ℕ} (f : Fin m → ℕ) : ℕ :=
  if h : ∃ i : Fin m, f i = 0 then (h.choose : ℕ) else 0

private theorem zeroIndex_spec {m : ℕ} {f : Fin m → ℕ} (h : ∃ i : Fin m, f i = 0) :
    ∃ i : Fin m, (i : ℕ) = zeroIndex f ∧ f i = 0 :=
  ⟨h.choose, by simp only [zeroIndex, dite_eq_left h], h.choose_spec⟩

/-- **Gathering.** A node sees the identifiers at offsets `-r, …, r`, finds the offset `j` of the
node with identifier `0` and outputs `ℓ₀ (-j)`: the label of `ℓ₀` at its own position relative to
that node. -/
noncomputable def gatherRule {L : Type*} {n : ℕ} (ℓ₀ : ZMod n → L) (r : ℕ) : LocalRule ℕ L r where
  toFun w := ℓ₀ ((((r : ℤ) - zeroIndex fun i : Fin (2 * r + 1) => w (((i : ℕ) : ℤ) - r)) : ℤ) :
    ZMod n)
  dependsOn w w' h := by
    have : (fun i : Fin (2 * r + 1) => w (((i : ℕ) : ℤ) - r)) =
        fun i : Fin (2 * r + 1) => w' (((i : ℕ) : ℤ) - r) := by
      funext i
      exact h _ ⟨by omega, by have := i.isLt; omega⟩
    simp only [this]

/-- If `2r + 1 ≥ n`, every node sees the whole cycle, and gathering outputs the rotation of the
solution `ℓ₀` that puts the node with identifier `0` at position `0`. -/
theorem gatherRule_isSolution {L : Type*} {R : L → L → Prop} {n r : ℕ} {ℓ₀ : ZMod n → L}
    (h₀ : IsSolution R ℓ₀) (hn : n ≤ 2 * r + 1) {x : ZMod n → ℕ} (hx : Function.Injective x)
    (hxn : ∀ v, x v < n) : IsSolution R ((gatherRule ℓ₀ r).apply x) := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact absurd (hxn 0) (Nat.not_lt_zero _)
  have : NeZero n := ⟨by omega⟩
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, x v₀ = 0 := by
    have hinj : Function.Injective (fun v => (⟨x v, hxn v⟩ : Fin n)) :=
      fun a b hab => hx (congrArg Fin.val hab)
    obtain ⟨v₀, hv₀⟩ := ((Fintype.bijective_iff_injective_and_card _).2
      ⟨hinj, by simp⟩).2 ⟨0, hpos⟩
    exact ⟨v₀, congrArg Fin.val hv₀⟩
  have key : ∀ v, (gatherRule ℓ₀ r).apply x v = ℓ₀ (v - v₀) := by
    intro v
    have hex : ∃ i : Fin (2 * r + 1), window x v (((i : ℕ) : ℤ) - r) = 0 := by
      set k := (v₀ - v).val with hk
      have hkn : k < n := ZMod.val_lt _
      have hk' : (k : ZMod n) = v₀ - v := ZMod.natCast_zmod_val _
      by_cases hkr : k ≤ r
      · refine ⟨⟨k + r, by omega⟩, ?_⟩
        change x (v + ((((k + r : ℕ) : ℤ) - r : ℤ) : ZMod n)) = 0
        rw [show (((k + r : ℕ) : ℤ) - r) = (k : ℤ) by push_cast; ring, Int.cast_natCast, hk',
          add_sub_cancel, hv₀]
      · refine ⟨⟨k + r - n, by omega⟩, ?_⟩
        change x (v + ((((k + r - n : ℕ) : ℤ) - r : ℤ) : ZMod n)) = 0
        rw [show (((k + r - n : ℕ) : ℤ) - r) = (k : ℤ) - n by omega, Int.cast_sub,
          Int.cast_natCast, Int.cast_natCast, ZMod.natCast_self, sub_zero, hk', add_sub_cancel,
          hv₀]
    obtain ⟨i, hi, hi0⟩ := zeroIndex_spec hex
    have hv : v + ((((i : ℕ) : ℤ) - r : ℤ) : ZMod n) = v₀ := hx (hi0.trans hv₀.symm)
    change ℓ₀ ((((r : ℤ) - zeroIndex fun i : Fin (2 * r + 1) =>
      window x v (((i : ℕ) : ℤ) - r)) : ℤ) : ZMod n) = ℓ₀ (v - v₀)
    rw [← hi, ← hv]
    congr 1
    push_cast
    ring
  intro v
  rw [key, key, show v + 1 - v₀ = (v - v₀) + 1 by ring]
  exact h₀ _

/-- **Every solvable problem in `⌊n / 2⌋` rounds.** If the oriented `n`-cycle has a solution, then
some algorithm solves `R` on it in `⌊n / 2⌋` rounds. -/
theorem IsSolution.exists_solvesLCL {L : Type*} {R : L → L → Prop} {n : ℕ} {ℓ₀ : ZMod n → L}
    (h₀ : IsSolution R ℓ₀) : ∃ A : Algorithm ℕ (ℤ → ℕ) L, A.SolvesLCL R n (n / 2) :=
  ⟨(gatherRule ℓ₀ (n / 2)).toAlgorithm, fun x hx hxn => by
    have : (gatherRule ℓ₀ (n / 2)).toAlgorithm.run x (n / 2) = (gatherRule ℓ₀ (n / 2)).apply x :=
      funext fun v => LocalRule.toAlgorithm_run _ x v
    rw [this]
    exact gatherRule_isSolution h₀ (by omega) hx hxn⟩

/-- **Problems without a flexible state have round complexity `Θ(n)`** ([Chang, Studený and
Suomela][ChangStudenySuomela2023], Table 1 and Thm 6.5, directed cycles). If no state of `R` is
flexible and the oriented `n`-cycle has a solution, some algorithm solves `R` on it in `⌊n / 2⌋`
rounds, and every `t`-round algorithm has `n ≤ (|L| + 1) (2t + 1)`. -/
theorem IsSolution.exists_solvesLCL_and_le_of_forall_not_isFlexible {L : Type*} [Fintype L]
    {R : L → L → Prop} (hR : ∀ q K, ¬IsFlexible R q K) {n : ℕ} {ℓ₀ : ZMod n → L}
    (h₀ : IsSolution R ℓ₀) :
    (∃ A : Algorithm ℕ (ℤ → ℕ) L, A.SolvesLCL R n (n / 2)) ∧
      ∀ {S : Type*} (A : Algorithm ℕ S L) (t : ℕ), A.SolvesLCL R n t →
        n ≤ (Fintype.card L + 1) * (2 * t + 1) :=
  ⟨h₀.exists_solvesLCL, fun _ _ hA => hA.le_of_forall_not_isFlexible hR⟩

end Cslib.Distributed.OrientedCycle.LCL
