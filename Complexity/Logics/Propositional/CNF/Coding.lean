/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF
public import Complexity.Foundations.Data.BitString.Flip
public import Cslib.Foundations.Data.BitString
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Complexity.Foundations.Data.BitString.Agree
import Complexity.Foundations.GroupTheory.Perm.Last
import Mathlib.Analysis.MeanInequalities

/-!
# The satisfiability coding lemma

The coding lemma of Paturi, Pudlák and Zane [PaturiPudlakZane1999], with exact sums over all
orders of the variables in place of probabilities. Fix a formula `φ` in conjunctive normal form
over `N` variables and an order `σ` of the variables. A variable `v` is *forced* on a solution `x`
(`CNF.forced`) when some clause contains the literal of `v` true under `x` and all its other
literals are on earlier variables and false under `x`. The words agreeing with a solution `x`
off its forced variables are disjoint for distinct solutions: at the first variable where two
solutions differ, a clause forcing it in one of them is false under the other
(`CNF.disjoint_agreeOffForced`). Hence `∑ₓ 2 ^ |forced σ x| ≤ 2 ^ N` for every order
(`CNF.sum_two_pow_card_forced_le`), and by the inequality of arithmetic and geometric means the
same holds with the average number of forced variables over all orders in the exponent
(`CNF.sum_two_rpow_average_card_forced_le`).

If every clause has at most `k` literals and `x` is isolated in direction `i` (flipping bit `i`
of `x` gives no solution), some clause is *critical* for `i` (`CNF.exists_critical`), and `i` is
forced whenever it comes last among the variables of that clause, for at least a `1 / k` fraction
of the orders (`CNF.factorial_le_mul_card_filter_mem_forced`, from
`Equiv.Perm.card_mul_card_filter_forall_le_eq_factorial`). Hence
`∑ₓ 2 ^ (ι(x) / k) ≤ 2 ^ N`, where `ι(x)` is the number of directions in which `x` is isolated
(`CNF.sum_two_rpow_card_isolated_div_le`), and a `k`-CNF has at most `2 ^ ((1 - 1 / k) N)`
solutions isolated in every direction (`CNF.card_isolatedInputs_mul_two_rpow_le`).

## Main definitions

* `Cslib.Logic.PL.CNF.Forces`, `Cslib.Logic.PL.CNF.forced`,
  `Cslib.Logic.PL.CNF.agreeOffForced`: forcing of a variable by a clause under an order of the
  variables, the variables forced on a solution, and the assignments agreeing off the forced
  variables.
* `Cslib.Logic.PL.CNF.Critical`, `Cslib.Logic.PL.CNF.critWidth`: critical clauses for a direction
  at an assignment, and the minimum width of a critical clause.

## Main results

* `Cslib.Logic.PL.CNF.sum_two_pow_card_forced_le`: the coding bound for one order.
* `Cslib.Logic.PL.CNF.sum_two_rpow_average_card_forced_le`: the coding lemma.
* `Cslib.Logic.PL.CNF.sum_two_rpow_card_isolated_div_le`: the coding lemma for `k`-CNFs.
* `Cslib.Logic.PL.CNF.card_isolatedInputs_mul_two_rpow_le`: few isolated solutions.

## References

* [R. Paturi, P. Pudlák, F. Zane, *Satisfiability coding lemma*][PaturiPudlakZane1999]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Finset

variable {N : ℕ}

namespace CNF

/-- The clause `c` forces `v` on `x` for the order `σ`: it contains the literal of `v` true under
`x`, and all its other literals are on variables before `v` (in the order `σ`) and false under
`x`. This is the deletion rule of Paturi, Pudlák and Zane: such a clause is critical for `v` at `x`
and `v` comes last among its variables, so the decoder meets it as a unit clause on `v`. A clause
also containing the literal of `v` false under `x` forces nothing, as the decoder would not see a
unit clause there; the definition rules it out, since that literal would need `σ v < σ v`. -/
def Forces (σ : Equiv.Perm (Fin N)) (x : BitString N) (c : Clause (Fin N)) (v : Fin N) : Prop :=
  (v, x v) ∈ c ∧ ∀ l ∈ c, l ≠ (v, x v) → σ l.1 < σ v ∧ x l.1 ≠ l.2

/-- Whether a clause forces a variable on an assignment for a given order is decidable. -/
instance (σ : Equiv.Perm (Fin N)) (x : BitString N) (c : Clause (Fin N)) (v : Fin N) :
    Decidable (Forces σ x c v) :=
  inferInstanceAs (Decidable (_ ∧ ∀ l ∈ c, _))

/-- The variables forced on `x` for the order `σ`: those forced by some clause. -/
def forced (φ : CNF (Fin N)) (σ : Equiv.Perm (Fin N)) (x : BitString N) : Finset (Fin N) :=
  univ.filter fun v => ∃ c ∈ φ, Forces σ x c v

variable {φ : CNF (Fin N)} {σ : Equiv.Perm (Fin N)}

/-- A variable `v` belongs to `φ.forced σ x` if and only if some clause of `φ` forces `v` on `x`
for `σ`. -/
@[simp] theorem mem_forced {φ : CNF (Fin N)} {σ : Equiv.Perm (Fin N)} {x : BitString N}
    {v : Fin N} : v ∈ φ.forced σ x ↔ ∃ c ∈ φ, Forces σ x c v := by
  simp [forced]

/-- The words agreeing with `x` outside the variables forced on `x`. -/
def agreeOffForced (φ : CNF (Fin N)) (σ : Equiv.Perm (Fin N)) (x : BitString N) :
    Finset (BitString N) :=
  univ.filter fun y => ∀ v ∉ φ.forced σ x, y v = x v

/-- **The words agreeing with distinct solutions off their forced variables are disjoint**: at the
first variable, in the order `σ`, where two solutions differ, one of them is forced, and the clause
forcing it is false under the other solution. -/
theorem disjoint_agreeOffForced {x x' : BitString N} (hx : φ.eval x = true) (hx' : φ.eval x' = true)
    (hne : x ≠ x') : Disjoint (φ.agreeOffForced σ x) (φ.agreeOffForced σ x') := by
  refine disjoint_left.2 fun y hy hy' => ?_
  -- the first variable where `x` and `x'` differ
  have hdiff : (univ.filter fun v => x v ≠ x' v).Nonempty := by
    obtain ⟨v, hv⟩ := Function.ne_iff.1 hne
    exact ⟨v, mem_filter.2 ⟨mem_univ v, hv⟩⟩
  obtain ⟨v, hv, hmin⟩ := exists_min_image _ (fun v => σ v) hdiff
  have hxv : x v ≠ x' v := (mem_filter.1 hv).2
  have hagree : ∀ u, σ u < σ v → x u = x' u := fun u hu => by
    by_contra h
    exact absurd (hmin u (mem_filter.2 ⟨mem_univ u, h⟩)) (not_le.2 hu)
  -- `v` is forced on one of them, by a clause false under the other
  have key : ∀ {a b : BitString N}, φ.eval b = true → a v ≠ b v →
      (∀ u, σ u < σ v → a u = b u) → v ∉ φ.forced σ a := by
    intro a b hb hab hagr hforced
    obtain ⟨c, hc, hvc, hrest⟩ := (mem_filter.1 hforced).2
    obtain ⟨l, hl, hle⟩ := (Clause.eval_eq_true_iff b c).1 ((CNF.eval_eq_true_iff b φ).1 hb c hc)
    obtain ⟨u, e⟩ := l
    by_cases hl' : (u, e) = (v, a v)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hl'
      exact hab hle.symm
    · obtain ⟨hlt, hne'⟩ := hrest (u, e) hl hl'
      exact hne' ((hagr u hlt).trans hle)
  by_cases hfx : v ∈ φ.forced σ x
  · exact key hx' hxv hagree hfx
  · by_cases hfx' : v ∈ φ.forced σ x'
    · exact key hx (Ne.symm hxv) (fun u hu => (hagree u hu).symm) hfx'
    · exact hxv (((mem_filter.1 hy).2 v hfx).symm.trans ((mem_filter.1 hy').2 v hfx'))

/-- `2 ^ |forced σ x|` words agree with `x` off its forced variables. -/
private theorem card_agreeOffForced (x : BitString N) :
    (φ.agreeOffForced σ x).card = 2 ^ (φ.forced σ x).card :=
  BitString.card_filter_forall_notMem_eq _ x

/-- **The coding bound for one order**: the solutions `x` of `φ` satisfy
`∑ₓ 2 ^ |forced σ x| ≤ 2 ^ N`. -/
theorem sum_two_pow_card_forced_le (φ : CNF (Fin N)) (σ : Equiv.Perm (Fin N)) :
    ∑ x ∈ univ.filter fun x : BitString N => φ.eval x = true, 2 ^ (φ.forced σ x).card ≤ 2 ^ N := by
  calc ∑ x ∈ univ.filter fun x : BitString N => φ.eval x = true, 2 ^ (φ.forced σ x).card
      = ∑ x ∈ univ.filter fun x : BitString N => φ.eval x = true, (φ.agreeOffForced σ x).card :=
        sum_congr rfl fun x _ => (card_agreeOffForced x).symm
    _ = ((univ.filter fun x : BitString N => φ.eval x = true).biUnion (φ.agreeOffForced σ)).card :=
        (card_biUnion fun x hx x' hx' hne => disjoint_agreeOffForced (mem_filter.1 hx).2
          (mem_filter.1 hx').2 hne).symm
    _ ≤ (univ : Finset (BitString N)).card := card_le_univ _
    _ = 2 ^ N := by simp

/-! ### Isolated directions are forced often -/

/-- The clause `c` is *critical* for the direction `i` at `x`: it contains the literal of `i` true
under `x`, and all its other literals are on other variables and false under `x`. Flipping bit `i`
of `x` falsifies a critical clause. -/
def Critical (x : BitString N) (c : Clause (Fin N)) (i : Fin N) : Prop :=
  (i, x i) ∈ c ∧ ∀ l ∈ c, l ≠ (i, x i) → l.1 ≠ i ∧ x l.1 ≠ l.2

/-- Whether a clause is critical for a direction at an assignment is decidable. -/
instance (x : BitString N) (c : Clause (Fin N)) (i : Fin N) : Decidable (Critical x c i) :=
  inferInstanceAs (Decidable (_ ∧ ∀ l ∈ c, _))

/-- A direction `i` in which a solution `x` is isolated has a critical clause. -/
theorem exists_critical {x : BitString N} {i : Fin N} (hx : φ.eval x = true)
    (hi : φ.eval (Function.update x i (!x i)) = false) : ∃ c ∈ φ, Critical x c i := by
  obtain ⟨c, hc, hcf⟩ : ∃ c ∈ φ, c.eval (Function.update x i (!x i)) = false := by
    by_contra h
    push Not at h
    rw [← Bool.not_eq_true, CNF.eval_eq_true_iff] at hi
    exact hi fun c hc => Bool.eq_true_of_not_eq_false (h c hc)
  have hfalse : ∀ l ∈ c, Function.update x i (!x i) l.1 ≠ l.2 := fun l hl h => by
    have := (Clause.eval_eq_true_iff _ c).2 ⟨l, hl, h⟩
    rw [hcf] at this
    exact Bool.false_ne_true this
  obtain ⟨⟨u, e⟩, hl, hle⟩ := (Clause.eval_eq_true_iff x c).1 ((CNF.eval_eq_true_iff x φ).1 hx c hc)
  -- the true literal is on `i`
  have hu : u = i := by
    by_contra hui
    exact hfalse _ hl (by rw [Function.update_of_ne hui]; exact hle)
  subst hu
  refine ⟨c, hc, hle ▸ hl, fun l hl' hne => ?_⟩
  have hli : l.1 ≠ u := by
    intro hli
    apply hfalse l hl'
    rw [hli, Function.update_self]
    -- `l = (u, !x u)`, as `l ≠ (u, x u)`
    obtain ⟨v, b⟩ := l
    simp only at hli
    subst hli
    cases b <;> cases hxv : x v <;> simp_all
  exact ⟨hli, fun h => hfalse l hl' (by rw [Function.update_of_ne hli]; exact h)⟩

/-- Criticality depends only on the literals of the clause. -/
theorem critical_congr {x : BitString N} {i : Fin N} {c c' : Clause (Fin N)}
    (h : ∀ l, l ∈ c ↔ l ∈ c') : Critical x c i ↔ Critical x c' i := by
  simp only [Critical, h]

/-- **A clause is critical at few inputs**: for each direction, a clause with `v` variables is
critical at at most `2 ^ (N - v)` inputs, since they all agree on its variables. -/
private theorem card_filter_critical_le (c : Clause (Fin N)) (i : Fin N) :
    #{x : BitString N | Critical x c i} ≤ 2 ^ (N - (c.map Prod.fst).toFinset.card) := by
  set V := (c.map Prod.fst).toFinset
  rcases ({x : BitString N | Critical x c i} : Finset _).eq_empty_or_nonempty with h | ⟨x₀, hx₀⟩
  · rw [h, card_empty]
    exact Nat.zero_le _
  have hx₀ := (mem_filter.1 hx₀).2
  calc #{x : BitString N | Critical x c i}
      ≤ #{y : BitString N | ∀ u ∉ Vᶜ, y u = x₀ u} := card_le_card fun x hx => ?_
    _ = 2 ^ (N - #V) := by
        rw [BitString.card_filter_forall_notMem_eq, card_compl, Fintype.card_fin]
  have hx := (mem_filter.1 hx).2
  refine mem_filter.2 ⟨mem_univ _, fun u hu => ?_⟩
  rw [notMem_compl] at hu
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hu)
  by_cases hli : l = (i, x i)
  · -- the literal of `i` true under `x₀` is in the clause too, so it is `l`
    subst hli
    by_contra hne
    exact (hx.2 (i, x₀ i) hx₀.1 fun h => hne (Prod.mk.inj h).2.symm).1 rfl
  · have h₁ := hx.2 l hl hli
    have h₂ := hx₀.2 l hl fun h => h₁.1 (by rw [h])
    have key : ∀ a b e : Bool, a ≠ e → b ≠ e → a = b := by decide
    exact key _ _ _ h₁.2 h₂.2

/-- A clause with `v` variables is critical for at most `v 2 ^ (N - v)` pairs of an input and a
direction. -/
theorem card_filter_critical_prod_le (c : Clause (Fin N)) :
    #{p : BitString N × Fin N | Critical p.1 c p.2} ≤
      (c.map Prod.fst).toFinset.card * 2 ^ (N - (c.map Prod.fst).toFinset.card) := by
  set V := (c.map Prod.fst).toFinset
  rw [card_eq_sum_card_fiberwise (f := Prod.snd) (t := V) fun p hp =>
    List.mem_toFinset.2 (List.mem_map.2 ⟨_, (mem_filter.1 hp).2.1, rfl⟩)]
  refine (sum_le_sum fun i _ => ?_).trans_eq (by rw [sum_const, smul_eq_mul])
  refine (card_le_card_of_injOn Prod.fst (fun p hp => ?_) fun p hp q hq h => ?_).trans
    (card_filter_critical_le c i)
  · obtain ⟨hp', hpi⟩ := mem_filter.1 hp
    exact mem_filter.2 ⟨mem_univ _, hpi ▸ (mem_filter.1 hp').2⟩
  · exact Prod.ext h (((mem_filter.1 hp).2).trans ((mem_filter.1 hq).2).symm)

/-- **Critical clauses force often.** A direction `i` with a critical clause `c` at `x` is forced
whenever it comes last among the variables of `c`, so for at least a `1 / v` fraction of the
orders, where `v` is the number of variables of `c`. -/
private theorem factorial_le_card_mul_card_filter_mem_forced {x : BitString N} {i : Fin N}
    {c : Clause (Fin N)} (hc : c ∈ φ) (hcrit : Critical x c i) :
    N.factorial ≤ (c.map Prod.fst).toFinset.card *
      (univ.filter fun σ : Equiv.Perm (Fin N) => i ∈ φ.forced σ x).card := by
  obtain ⟨hic, hrest⟩ := hcrit
  set S := (c.map Prod.fst).toFinset
  have hiS : i ∈ S := List.mem_toFinset.2 (List.mem_map.2 ⟨_, hic, rfl⟩)
  have hlast := Equiv.Perm.card_mul_card_filter_forall_le_eq_factorial hiS
  rw [Fintype.card_fin] at hlast
  refine hlast.ge.trans (Nat.mul_le_mul_left _ (card_le_card ?_))
  intro σ hσ
  simp only [mem_filter, mem_univ, true_and] at hσ
  refine mem_filter.2 ⟨mem_univ σ, mem_filter.2 ⟨mem_univ i, c, hc, hic, fun l hl hne => ?_⟩⟩
  obtain ⟨hli, hxl⟩ := hrest l hl hne
  have hle := hσ l.1 (List.mem_toFinset.2 (List.mem_map.2 ⟨l, hl, rfl⟩))
  exact ⟨lt_of_le_of_ne hle fun h => hli (σ.injective h), hxl⟩

/-- **Isolated directions are forced often.** If every clause of `φ` has at most `k` literals,
every direction `i` in which a solution `x` is isolated is forced for at least a `1 / k` fraction
of the orders. -/
theorem factorial_le_mul_card_filter_mem_forced {k : ℕ} (hk : ∀ c ∈ φ, c.length ≤ k)
    {x : BitString N} {i : Fin N} (hx : φ.eval x = true)
    (hi : φ.eval (Function.update x i (!x i)) = false) :
    N.factorial ≤ k * (univ.filter fun σ : Equiv.Perm (Fin N) => i ∈ φ.forced σ x).card := by
  obtain ⟨c, hc, hcrit⟩ := exists_critical hx hi
  have hS : (c.map Prod.fst).toFinset.card ≤ k :=
    (List.toFinset_card_le _).trans ((List.length_map _).trans_le (hk c hc))
  exact (factorial_le_card_mul_card_filter_mem_forced hc hcrit).trans (Nat.mul_le_mul_right _ hS)

/-- Summed over the variables, the orders forcing each count the forced variables of every
order. -/
private theorem sum_card_filter_mem_forced (x : BitString N) :
    ∑ i, (univ.filter fun σ : Equiv.Perm (Fin N) => i ∈ φ.forced σ x).card =
      ∑ σ : Equiv.Perm (Fin N), (φ.forced σ x).card := by
  simp only [card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  simp [-mem_forced]

/-! ### Averaging over the orders -/

/-- **The coding lemma** [Paturi, Pudlák and Zane, Lemma 1 and Fact 3][PaturiPudlakZane1999]: with
`E(x)` the average, over all `N!` orders, of the number of variables forced on a solution `x`, the
solutions satisfy `∑ₓ 2 ^ E(x) ≤ 2 ^ N`. -/
theorem sum_two_rpow_average_card_forced_le (φ : CNF (Fin N)) :
    ∑ x ∈ univ.filter fun x : BitString N => φ.eval x = true,
        (2 : ℝ) ^ ((∑ σ : Equiv.Perm (Fin N), ((φ.forced σ x).card : ℝ)) / N.factorial) ≤
      2 ^ N := by
  have hF : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
  have hP : ((univ : Finset (Equiv.Perm (Fin N))).card : ℝ) = N.factorial := by
    rw [card_univ, Fintype.card_perm, Fintype.card_fin]
  -- `2 ^ (average) ≤ average of 2 ^ ·`, by the weighted inequality of arithmetic and geometric
  -- means
  have hamgm (x : BitString N) :
      (2 : ℝ) ^ ((∑ σ : Equiv.Perm (Fin N), ((φ.forced σ x).card : ℝ)) / N.factorial) ≤
        ∑ σ : Equiv.Perm (Fin N), 1 / N.factorial * (2 : ℝ) ^ (φ.forced σ x).card := by
    have h := Real.geom_mean_le_arith_mean_weighted (s := univ) (fun _ => 1 / (N.factorial : ℝ))
      (fun σ : Equiv.Perm (Fin N) => (2 : ℝ) ^ (φ.forced σ x).card) (fun _ _ => by positivity)
      (by rw [sum_const, nsmul_eq_mul, hP]; field_simp) (fun _ _ => by positivity)
    refine le_trans (le_of_eq ?_) h
    rw [div_eq_mul_one_div, sum_mul, Real.rpow_sum_of_pos (by norm_num)]
    refine prod_congr rfl fun σ _ => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  calc ∑ x ∈ univ.filter fun x : BitString N => φ.eval x = true,
        (2 : ℝ) ^ ((∑ σ : Equiv.Perm (Fin N), ((φ.forced σ x).card : ℝ)) / N.factorial)
      ≤ ∑ x ∈ univ.filter fun x : BitString N => φ.eval x = true,
          ∑ σ : Equiv.Perm (Fin N), 1 / N.factorial * (2 : ℝ) ^ (φ.forced σ x).card :=
        sum_le_sum fun x _ => hamgm x
    _ = ∑ σ : Equiv.Perm (Fin N), 1 / N.factorial *
          ∑ x ∈ univ.filter fun x : BitString N => φ.eval x = true,
            (2 : ℝ) ^ (φ.forced σ x).card := by
        rw [sum_comm]
        simp only [mul_sum]
    _ ≤ ∑ _σ : Equiv.Perm (Fin N), 1 / N.factorial * (2 : ℝ) ^ N := by
        refine sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact_mod_cast sum_two_pow_card_forced_le φ σ
    _ = 2 ^ N := by
        rw [sum_const, nsmul_eq_mul, hP]
        field_simp

/-- **The coding lemma for formulas of width `k`**
[Paturi, Pudlák and Zane, Lemma 2][PaturiPudlakZane1999]: if every clause has at most `k ≥ 1`
literals, the solutions `x` satisfy `∑ₓ 2 ^ (ι(x) / k) ≤ 2 ^ N`, where `ι(x)` is the number of
directions in which `x` is isolated. -/
theorem sum_two_rpow_card_isolated_div_le {k : ℕ} (hk1 : 1 ≤ k) (hk : ∀ c ∈ φ, c.length ≤ k) :
    ∑ x ∈ univ.filter fun x : BitString N => φ.eval x = true,
        (2 : ℝ) ^ (((univ.filter fun i => φ.eval (Function.update x i (!x i)) = false).card : ℝ) /
          k) ≤ 2 ^ N := by
  refine le_trans (sum_le_sum fun x hx => ?_) (sum_two_rpow_average_card_forced_le φ)
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have hx' := (mem_filter.1 hx).2
  -- `ι(x) N! ≤ k ∑_σ |forced σ x|`
  have hcount : (univ.filter fun i => φ.eval (Function.update x i (!x i)) = false).card *
      N.factorial ≤ k * ∑ σ : Equiv.Perm (Fin N), (φ.forced σ x).card := by
    calc (univ.filter fun i => φ.eval (Function.update x i (!x i)) = false).card * N.factorial
        = ∑ i ∈ univ.filter fun i => φ.eval (Function.update x i (!x i)) = false,
            N.factorial := by rw [sum_const, smul_eq_mul]
      _ ≤ ∑ i ∈ univ.filter fun i => φ.eval (Function.update x i (!x i)) = false,
            k * (univ.filter fun σ : Equiv.Perm (Fin N) => i ∈ φ.forced σ x).card :=
          sum_le_sum fun i hi => factorial_le_mul_card_filter_mem_forced hk hx' (mem_filter.1 hi).2
      _ ≤ k * ∑ i : Fin N, (univ.filter fun σ : Equiv.Perm (Fin N) => i ∈ φ.forced σ x).card := by
          rw [← mul_sum]
          exact Nat.mul_le_mul_left _ (sum_le_sum_of_subset (filter_subset _ _))
      _ = k * ∑ σ : Equiv.Perm (Fin N), (φ.forced σ x).card := by
          rw [sum_card_filter_mem_forced]
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
  have hF : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
  rw [div_le_div_iff₀ hkR hF]
  have : ((univ.filter fun i => φ.eval (Function.update x i (!x i)) = false).card : ℝ) *
      N.factorial ≤ k * ∑ σ : Equiv.Perm (Fin N), ((φ.forced σ x).card : ℝ) := by
    exact_mod_cast hcount
  linarith

/-- **Few isolated solutions** [Paturi, Pudlák and Zane, Lemma 4][PaturiPudlakZane1999]: a formula
whose clauses have at most `k ≥ 1` literals has at most `2 ^ ((1 - 1 / k) N)` solutions isolated in
every direction. -/
theorem card_isolatedInputs_mul_two_rpow_le {k : ℕ} (hk1 : 1 ≤ k) (hk : ∀ c ∈ φ, c.length ≤ k) :
    (#(BitString.isolatedInputs φ.eval true) : ℝ) * 2 ^ ((N : ℝ) / k) ≤
      2 ^ N := by
  refine le_trans ?_ (sum_two_rpow_card_isolated_div_le hk1 hk)
  rw [← nsmul_eq_mul, ← sum_const]
  refine (sum_le_sum_of_subset_of_nonneg (fun x hx => mem_filter.2 ⟨mem_univ x,
    (BitString.mem_isolatedInputs.1 hx).1⟩) fun _ _ _ => by positivity).trans'
      (le_of_eq (sum_congr rfl fun x hx => ?_))
  have hall (i : Fin N) : φ.eval (Function.update x i !x i) = false :=
    (BitString.mem_isolatedInputs.1 hx).2 i
  congr 2
  rw [filter_true_of_mem fun i _ => hall i, card_univ, Fintype.card_fin]

/-! ### Weights of solutions -/

/-- The number of variables of a shortest clause critical for the direction `i` at `x`, or `0`
if no clause is. -/
noncomputable def critWidth (φ : CNF (Fin N)) (x : BitString N) (i : Fin N) : ℕ :=
  sInf {v | ∃ c ∈ φ, Critical x c i ∧ (c.map Prod.fst).toFinset.card = v}

/-- When some clause of `φ` is critical for direction `i` at `x`, there is a critical clause whose
number of distinct variables equals `φ.critWidth x i`. -/
theorem exists_critical_card_eq_critWidth {x : BitString N} {i : Fin N}
    (h : ∃ c ∈ φ, Critical x c i) :
    ∃ c ∈ φ, Critical x c i ∧ (c.map Prod.fst).toFinset.card = φ.critWidth x i := by
  obtain ⟨c, hc, hcrit⟩ := h
  exact Nat.sInf_mem (s := {v | ∃ c ∈ φ, Critical x c i ∧ (c.map Prod.fst).toFinset.card = v})
    ⟨_, c, hc, hcrit, rfl⟩

private theorem critWidth_eq_zero {x : BitString N} {i : Fin N} (h : ¬ ∃ c ∈ φ, Critical x c i) :
    φ.critWidth x i = 0 := by
  refine Nat.sInf_eq_zero.2 (Or.inr (Set.eq_empty_iff_forall_notMem.2 fun v hv => ?_))
  obtain ⟨c, hc, hcrit, -⟩ := hv
  exact h ⟨c, hc, hcrit⟩

/-- When some clause of `φ` is critical for direction `i` at `x`, `φ.critWidth x i` is positive. -/
theorem critWidth_pos {x : BitString N} {i : Fin N} (h : ∃ c ∈ φ, Critical x c i) :
    0 < φ.critWidth x i := by
  obtain ⟨c, -, hcrit, hcard⟩ := exists_critical_card_eq_critWidth h
  rw [← hcard]
  exact card_pos.2 ⟨i, List.mem_toFinset.2 (List.mem_map.2 ⟨_, hcrit.1, rfl⟩)⟩

/-- The average number of variables forced on `x` is at least its *weight*
`∑ᵢ 1 / critWidth φ x i`. -/
private theorem sum_inv_critWidth_le (x : BitString N) :
    ∑ i, 1 / (φ.critWidth x i : ℝ) ≤
      (∑ σ : Equiv.Perm (Fin N), ((φ.forced σ x).card : ℝ)) / N.factorial := by
  have hswap : ∑ σ : Equiv.Perm (Fin N), ((φ.forced σ x).card : ℝ) =
      ∑ i, ((univ.filter fun σ : Equiv.Perm (Fin N) => i ∈ φ.forced σ x).card : ℝ) := by
    exact_mod_cast (sum_card_filter_mem_forced x).symm
  have hF : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
  rw [hswap, sum_div]
  refine sum_le_sum fun i _ => ?_
  by_cases h : ∃ c ∈ φ, Critical x c i
  · obtain ⟨c, hc, hcrit, hcard⟩ := exists_critical_card_eq_critWidth h
    have hle := factorial_le_card_mul_card_filter_mem_forced hc hcrit
    rw [hcard] at hle
    have hpos : (0 : ℝ) < φ.critWidth x i := by exact_mod_cast critWidth_pos h
    rw [div_le_div_iff₀ hpos hF, one_mul, mul_comm]
    exact_mod_cast hle
  · rw [critWidth_eq_zero h, Nat.cast_zero, div_zero]
    positivity

/-- **The weighted coding lemma**, after [Paturi, Pudlák and Zane, Lemma 5][PaturiPudlakZane1999]:
the solutions `x` of any formula satisfy `∑ₓ 2 ^ w(x) ≤ 2 ^ N`, where the weight
`w(x) = ∑ᵢ 1 / critWidth φ x i` sums, over the directions in which `x` is isolated, the inverse
number of variables of a shortest critical clause. -/
theorem sum_two_rpow_sum_inv_critWidth_le (φ : CNF (Fin N)) :
    ∑ x ∈ univ.filter fun x : BitString N => φ.eval x = true,
      (2 : ℝ) ^ (∑ i, 1 / (φ.critWidth x i : ℝ)) ≤ 2 ^ N :=
  le_trans (sum_le_sum fun x _ => Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (sum_inv_critWidth_le x)) (sum_two_rpow_average_card_forced_le φ)

/-- **Few solutions of large weight** [Paturi, Pudlák and Zane, Lemma 5][PaturiPudlakZane1999]: at
most `2 ^ (N - μ)` solutions have weight at least `μ`. -/
theorem card_filter_le_sum_inv_critWidth_mul_two_rpow_le (φ : CNF (Fin N)) (μ : ℝ) :
    (#{x : BitString N | φ.eval x = true ∧ μ ≤ ∑ i, 1 / (φ.critWidth x i : ℝ)} : ℝ) * 2 ^ μ ≤
      2 ^ N := by
  refine le_trans ?_ (sum_two_rpow_sum_inv_critWidth_le φ)
  rw [← nsmul_eq_mul, ← sum_const]
  refine (sum_le_sum fun x hx => Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (mem_filter.1 hx).2.2).trans (sum_le_sum_of_subset_of_nonneg (fun x hx => mem_filter.2
      ⟨mem_univ x, (mem_filter.1 hx).2.1⟩) fun _ _ _ => by positivity)

end CNF

end Cslib.Logic.PL
