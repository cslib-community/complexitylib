/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.OrientedCycle.Basic
public import CslibFrontier.Foundations.Combinatorics.ShiftColoring
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Linial's lower bound for colouring oriented cycles

[Linial][Linial1992] proved that a deterministic LOCAL algorithm 3-colouring every oriented
`n`-cycle with identifiers from `{1, …, n}` needs `Ω(log* n)` rounds. We follow the proof of
[Laurinharju and Suomela][LaurinharjuSuomela2014], which gives the explicit bound
`t ≥ (log* n) / 2 - 1`.

A rule of radius `t` sees the identifiers at offsets `-t, …, t`. Restricted to windows of increasing
identifiers it is a colouring of increasing `(2t + 1)`-tuples (`windowColoring`). When the rule
properly colours every cycle, two consecutive nodes whose `2t + 2` identifiers are increasing get
different colours, so this is a shift colouring (`Cslib.IsShiftColoring`). The speedup lemma then
gives `n ≤ 2 ^ 2 ^ ⋯ ^ c` with `2t` exponentials for `c` colours.

The identifiers are a bijection from the nodes onto `{0, …, n - 1}`, the strongest assumption of
this kind: the bound holds even for algorithms that know `n` and need to succeed only on these
inputs. Identifiers from `{1, …, n}` are the same up to a shift by one.

## Main definitions

* `Cslib.Distributed.OrientedCycle.windowColoring`: the colouring of increasing identifier tuples
  induced by a rule.

## Main results

* `Cslib.Distributed.OrientedCycle.LocalRule.le_iterate_of_isProperColoring`: the combinatorial
  bound for rules.
* `Cslib.Distributed.OrientedCycle.Algorithm.le_iterate_of_isProperColoring`: the same bound for
  `t`-round algorithms.
* `Cslib.Distributed.OrientedCycle.Algorithm.ColorsCycle.logStar_le`: `log* n ≤ 2t + log* c` for
  `c` colours.
* `Cslib.Distributed.OrientedCycle.Algorithm.ColorsCycle.logStar_le_of_three`: Linial's lower
  bound `log* n ≤ 2t + 2` for 3-colouring.

## References

* [N. Linial, *Locality in distributed graph algorithms*][Linial1992]
* [J. Laurinharju and J. Suomela, *Brief announcement: Linial's lower bound made
  easy*][LaurinharjuSuomela2014]
-/

public section

namespace Cslib.Distributed.OrientedCycle

/-- The colouring of increasing `(2t + 1)`-tuples induced by a rule of radius `t`: the tuple `b` is
read as the identifiers at offsets `-t, …, t`. -/
def windowColoring {O : Type*} {t : ℕ} (F : LocalRule ℕ O t)
    (b : Fin (2 * t + 1) → ℕ) : O :=
  F.toFun fun j => b (Fin.clamp (j + t).toNat (2 * t))

private theorem le_iterate_two_pow {c : ℕ} (hc : 1 ≤ c) (k : ℕ) : k + 1 ≤ (2 ^ ·)^[k] c := by
  induction k with
  | zero => simpa using hc
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact le_trans (Nat.succ_le_succ ih) (Nat.lt_two_pow_self)

/-- An increasing tuple of identifiers below `n`, placed on consecutive nodes `0, 1, …` of the
oriented `n`-cycle, extends to distinct identifiers below `n` on all nodes. -/
private theorem exists_extension {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) {a : Fin k → ℕ}
    (ha : StrictMono a) (han : ∀ i, a i < n) :
    ∃ x : ZMod n → ℕ, Function.Injective x ∧ (∀ v, x v < n) ∧ ∀ i : Fin k, x (i : ℕ) = a i := by
  have : NeZero n := ⟨hn.ne'⟩
  have hf : Function.Injective fun i : Fin k => ((i : ℕ) : ZMod n) := by
    intro i j h
    have := congrArg ZMod.val h
    rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at this
    exact Fin.val_injective this
  have hg : Function.Injective fun i : Fin k => ((a i : ℕ) : ZMod n) := by
    intro i j h
    have := congrArg ZMod.val h
    rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (han i),
      Nat.mod_eq_of_lt (han j)] at this
    exact ha.injective this
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair _ _ hf hg
  refine ⟨fun v => (σ v).val, ?_, fun v => ZMod.val_lt _, fun i => ?_⟩
  · intro v w h
    exact σ.injective (ZMod.val_injective n h)
  · simp only [hσ, ZMod.val_natCast, Nat.mod_eq_of_lt (han i)]

/-- **Linial's lower bound, combinatorial core** [Linial][Linial1992], following
[Laurinharju and Suomela][LaurinharjuSuomela2014]. If a rule of radius `t` properly colours the
oriented `n`-cycle with colours in `O` for every assignment of distinct identifiers below `n`, then
`n ≤ 2 ^ 2 ^ ⋯ ^ |O|` with `2t` exponentials. -/
theorem LocalRule.le_iterate_of_isProperColoring {O : Type*} [Fintype O] {n t : ℕ}
    (F : LocalRule ℕ O t)
    (hF : ∀ x : ZMod n → ℕ, Function.Injective x → (∀ v, x v < n) →
      IsProperColoring (F.apply x)) :
    n ≤ (2 ^ ·)^[2 * t] (Fintype.card O) := by
  rcases Nat.lt_or_ge n (2 * t + 2) with hsmall | hlarge
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact Nat.zero_le _
    · have : NeZero n := ⟨hn.ne'⟩
      have hO : 1 ≤ Fintype.card O :=
        Fintype.card_pos_iff.2 ⟨F.apply (fun v : ZMod n => v.val) 0⟩
      have := le_iterate_two_pow hO (2 * t)
      omega
  · refine IsShiftColoring.le_iterate (f := windowColoring F) fun a ha han => ?_
    obtain ⟨x, hx, hxn, hxa⟩ := exists_extension (by omega) hlarge ha han
    have h := hF x hx hxn (t : ℕ)
    -- the windows of nodes `t` and `t + 1` are the two halves of `a`
    have hwin : ∀ j : ℤ, -(t : ℤ) ≤ j → j ≤ t →
        window x (t : ZMod n) j = Fin.init a (Fin.clamp (j + t).toNat (2 * t)) ∧
          window x ((t : ZMod n) + 1) j = Fin.tail a (Fin.clamp (j + t).toNat (2 * t)) := by
      intro j hj₁ hj₂
      obtain ⟨m, hm⟩ : ∃ m : ℕ, j + t = m := ⟨(j + t).toNat, by omega⟩
      have hm2 : m ≤ 2 * t := by omega
      have hcl : (Fin.clamp (j + t).toNat (2 * t) : ℕ) = m := by
        simp only [Fin.coe_clamp, hm, Int.toNat_natCast]; omega
      have hmz : (j : ZMod n) + (t : ZMod n) = (m : ZMod n) := by
        have := congrArg (Int.cast : ℤ → ZMod n) hm
        push_cast at this
        exact this
      constructor
      · have hv : (t : ZMod n) + (j : ZMod n) = ((m : ℕ) : ZMod n) := by
          linear_combination hmz
        simp only [window, hv, Fin.init]
        rw [show ((m : ℕ) : ZMod n) = (((⟨m, by omega⟩ : Fin (2 * t + 2)) : ℕ) : ZMod n) from rfl,
          hxa]
        congr 1; ext; simp; omega
      · have hv : (t : ZMod n) + 1 + (j : ZMod n) = ((m + 1 : ℕ) : ZMod n) := by grind
        simp only [window, hv, Fin.tail]
        rw [show ((m + 1 : ℕ) : ZMod n) =
          (((⟨m + 1, by omega⟩ : Fin (2 * t + 2)) : ℕ) : ZMod n) from rfl, hxa]
        congr 1; ext; simp; omega
    have h1 : F.apply x (t : ZMod n) = windowColoring F (Fin.init a) :=
      F.toFun_congr fun j hj₁ hj₂ => (hwin j hj₁ hj₂).1
    have h2 : F.apply x ((t : ZMod n) + 1) = windowColoring F (Fin.tail a) :=
      F.toFun_congr fun j hj₁ hj₂ => (hwin j hj₁ hj₂).2
    rwa [h1, h2] at h

/-- **Linial's lower bound for algorithms.** If a `t`-round algorithm properly colours every
oriented `n`-cycle with distinct identifiers below `n`, using colours in a finite type `O`, then
`n ≤ 2 ^ 2 ^ ⋯ ^ |O|` with `2t` exponentials. -/
theorem Algorithm.le_iterate_of_isProperColoring {S O : Type*} [Fintype O] {n t : ℕ}
    (A : Algorithm ℕ S O)
    (hA : ∀ x : ZMod n → ℕ, Function.Injective x → (∀ v, x v < n) →
      IsProperColoring (A.run x t)) :
    n ≤ (2 ^ ·)^[2 * t] (Fintype.card O) :=
  (A.toLocalRule t).le_iterate_of_isProperColoring fun x hx hxn => by
    have h : A.run x t = (A.toLocalRule t).apply x := funext (A.run_eq_apply x t)
    exact h ▸ hA x hx hxn

/-- Linial's lower bound in terms of `log*`: a `t`-round algorithm properly colouring every oriented
`n`-cycle with distinct identifiers below `n` and colours below `c` has
`log* n ≤ 2t + log* c`. -/
theorem Algorithm.ColorsCycle.logStar_le {S : Type*} {A : Algorithm ℕ S ℕ} {n t c : ℕ}
    (hA : A.ColorsCycle n t c) : Nat.logStar n ≤ 2 * t + Nat.logStar c := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.logStar_of_le_one]
  have : NeZero n := ⟨hn.ne'⟩
  have hval := (hA (fun v : ZMod n => v.val) (ZMod.val_injective n) ZMod.val_lt).2 0
  obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  let B := A.mapOutput fun a => Fin.clamp a c
  have hB : n ≤ (2 ^ ·)^[2 * t] (Fintype.card (Fin (c + 1))) := by
    refine B.le_iterate_of_isProperColoring fun x hx hxn v h => ?_
    obtain ⟨hp, hlt⟩ := hA x hx hxn
    simp only [B, Algorithm.mapOutput_run] at h
    have h' := congrArg Fin.val h
    simp only [Fin.coe_clamp, Nat.min_eq_left (Nat.le_of_lt_succ (hlt _))] at h'
    exact hp v h'
  rw [Fintype.card_fin] at hB
  exact Nat.logStar_le_iff.2 (hB.trans (Nat.iterate_two_pow_le_twoTower _ _))

/-- **Linial's lower bound** [Linial][Linial1992], with the constants of
[Laurinharju and Suomela][LaurinharjuSuomela2014]. A deterministic `t`-round LOCAL algorithm that
properly 3-colours every oriented `n`-cycle with distinct identifiers from `{0, …, n - 1}` satisfies
`log* n ≤ 2t + 2`, that is `t ≥ (log* n) / 2 - 1`. -/
theorem Algorithm.ColorsCycle.logStar_le_of_three {S : Type*} {A : Algorithm ℕ S ℕ} {n t : ℕ}
    (hA : A.ColorsCycle n t 3) : Nat.logStar n ≤ 2 * t + 2 := by
  have h3 : Nat.logStar 3 = 2 := by decide
  simpa [h3] using hA.logStar_le

end Cslib.Distributed.OrientedCycle
