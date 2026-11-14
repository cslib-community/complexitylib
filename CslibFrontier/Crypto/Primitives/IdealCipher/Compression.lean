/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.IdealCipher
public import CslibFrontier.Crypto.Primitives.Hash.BlockCipherCompression
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.Notation
import CslibFrontier.Languages.Probabilistic.UntilBad.ChooseTwo
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Collision Resistance in the Ideal Cipher Model

We define the collision-resistance game (`collisionGame`) for a compression function built from an
ideal block cipher over `Key` and `Block`, played by a `CollisionFinder`, record the inverse-query
break of `cipherOutput` ([KatzLindell2020], Exercise 7.23(a)), and prove the Ideal-Cipher
collision-resistance upper bound for the Davies–Meyer construction `daviesMeyer`
([KatzLindell2020], Section 7.3.1, Figure 7.11, Theorem 7.5).

Specifically, for any `Q`-query adaptive adversary `A` making forward and inverse ideal-cipher
queries, `daviesMeyer_collisionGame_le` reduces `collisionGame daviesMeyer A` to the forgetful
ideal-cipher oracle via `abs_sub_uniformPerm_forgetful_le` and bounds the forgetful collision
probability via `OracleComp.toOuterMeasure_bad_choose_two_le`, yielding
`Pr[collisionGame daviesMeyer A] ≤ 2 * ((Q + 2).choose 2 : ℝ) * (Fintype.card Block)⁻¹`
(equivalently `((Q + 2) * (Q + 1) : ℝ) * (Fintype.card Block)⁻¹`). The `+ 2` reflects the two
compression-function evaluations on the adversary's output pair.

## Main definitions

* `Cslib.IdealCipher.CollisionFinder`: An ideal-cipher adversary that outputs a candidate
  collision.
* `Cslib.IdealCipher.collides`: The winning test, shared by the game and the Davies–Meyer program.
* `Cslib.IdealCipher.collisionGame`: The collision-resistance game in the Ideal Cipher Model.
* `Cslib.IdealCipher.cipherOutputAdversary`: An explicit inverse-query collision finder for
  `cipherOutput`.
* `Cslib.IdealCipher.daviesMeyerCollisionProgram`: An ideal-cipher oracle program checking whether
  `A` outputs a valid collision under `daviesMeyer`.

## Main results

* `Cslib.IdealCipher.cipherOutputAdversary_wins`: `cipherOutputAdversary` breaks `cipherOutput`
  with probability `1`.
* `Cslib.IdealCipher.collisionGame_daviesMeyer_eq`: Equivalence between `collisionGame daviesMeyer`
  and `daviesMeyerCollisionProgram`.
* `Cslib.IdealCipher.daviesMeyer_collision_difference_bound`: Switching bound between the real
  ideal cipher and the forgetful sampler on `daviesMeyerCollisionProgram`.
* `Cslib.IdealCipher.daviesMeyer_collisionGame_le`,
  `Cslib.IdealCipher.daviesMeyer_collisionGame_mul_le`: Davies–Meyer collision-resistance upper
  bounds in the Ideal Cipher Model ([KatzLindell2020], Theorem 7.5).

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020], Section 7.3.1,
  Figure 7.11, Theorem 7.5, Exercises 7.23 and 7.24.
-/

public section

namespace Cslib.IdealCipher

open OracleComp Cslib.Crypto.BlockCipherCompression Cslib.Probability
open scoped ENNReal BigOperators

/-- A collision finder against a compression function `Key × Block → Block` built from an ideal
cipher: an oracle program with forward and inverse ideal-cipher queries that outputs two candidate
inputs. -/
abbrev CollisionFinder (Key Block : Type) :=
  OracleComp (Spec Key Block) ((Key × Block) × (Key × Block))

/-- The winning test: the inputs `x₁` and `x₂` differ and their digests `h₁` and `h₂` agree. -/
@[expose]
def collides {α β : Type} [DecidableEq α] [DecidableEq β] (x₁ x₂ : α) (h₁ h₂ : β) : Bool :=
  decide (x₁ ≠ x₂ ∧ h₁ = h₂)

section Programs

variable {Key Block : Type}

/-- Wrap an adversary `A` with two final forward queries on its candidate pair and test the
Davies–Meyer digests `E_k(x) + x` with `collides`. -/
@[expose]
noncomputable def daviesMeyerCollisionProgram [DecidableEq Key] [DecidableEq Block] [Add Block]
    (A : CollisionFinder Key Block) : OracleComp (Spec Key Block) Bool := do
  let ((k₁, x₁), (k₂, x₂)) ← A
  let y₁ ← query (k₁, Cslib.RandomPermutation.PermQuery.forward x₁)
  let y₂ ← query (k₂, Cslib.RandomPermutation.PermQuery.forward x₂)
  return collides (k₁, x₁) (k₂, x₂) (y₁ + x₁) (y₂ + x₂)

/-- Appending two forward queries adds `2` to the adversary's query bound. -/
theorem isQueryBounded_daviesMeyerCollisionProgram [DecidableEq Key] [DecidableEq Block] [Add Block]
    {A : CollisionFinder Key Block} {Q : ℕ} (hQ : IsQueryBounded A Q) :
    IsQueryBounded (daviesMeyerCollisionProgram A) (Q + 2) :=
  IsCostBounded.bind hQ fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ =>
    IsCostBounded.bind (IsCostBounded.query _) fun _ =>
      IsCostBounded.bind (IsCostBounded.query _) fun _ =>
        IsCostBounded.pure _ 0

end Programs

section Games

variable {Key Block : Type} [DecidableEq Key] [Fintype Key] [DecidableEq Block]
  [Fintype Block] [Nonempty Block]

/-- The collision-resistance game for a compression function `H` built from a block cipher.
The adversary has oracle access to the ideal cipher `E` and its inverse, and wins when its
candidates `x₁` and `x₂` `collide` under `H E`. -/
@[expose]
noncomputable def collisionGame
    (H : (Key → Equiv.Perm Block) → Key × Block → Block) (A : CollisionFinder Key Block) :
    PMF Bool :=
  (complete fun _ => []).bind fun E =>
    (interpret lazyEvalPerm A E).map fun ((x₁, x₂), _) => collides x₁ x₂ (H E x₁) (H E x₂)

/-- An adversary that finds a collision in `cipherOutput` using two inverse queries. -/
@[expose]
def cipherOutputAdversary (k1 k2 : Key) (y : Block) :
    OracleComp (Spec Key Block) ((Key × Block) × (Key × Block)) := do
  let x1 ← query (k1, Cslib.RandomPermutation.PermQuery.inverse y)
  let x2 ← query (k2, Cslib.RandomPermutation.PermQuery.inverse y)
  return ((k1, x1), (k2, x2))

omit [Nonempty Block] in
/-- **Exercise 7.23(a)** ([KatzLindell2020], Section 7.3.1): `cipherOutputAdversary` finds a
collision for `cipherOutput` with probability `1`. -/
theorem cipherOutputAdversary_wins {k1 k2 : Key} (hk : k1 ≠ k2) (y : Block) :
    collisionGame (cipherOutput (B := Block)) (cipherOutputAdversary k1 k2 y) = PMF.pure true := by
  unfold collisionGame cipherOutputAdversary lazyEvalPerm
  simp only [complete_nil, interpret_bind, interpret_query, interpret_pure]
  simp [bind, StateT.bind, pure, StateT.pure, Cslib.RandomPermutation.evalPerm, collides,
    cipherOutput_symm, hk]

omit [DecidableEq Key] [DecidableEq Block] [Nonempty Block] in
/-- For `daviesMeyer`, `collisionGame` agrees with interpreting `daviesMeyerCollisionProgram A`
against uniformly chosen independent permutations `E : Key → Equiv.Perm Block`. -/
theorem collisionGame_daviesMeyer_eq [DecidableEq Key] [DecidableEq Block] [Add Block]
    (A : CollisionFinder Key Block) :
    collisionGame (daviesMeyer (K := Key) (B := Block)) A =
      (PMF.pi (fun _ : Key => PMF.uniformOfFintype (Equiv.Perm Block))).bind fun E =>
        interpret (fun (q : Query Key Block) =>
          PMF.pure (Cslib.RandomPermutation.evalPerm (E q.1) q.2))
          (daviesMeyerCollisionProgram A) := by
  unfold collisionGame daviesMeyerCollisionProgram
  rw [complete_nil]
  apply congrArg
  ext1 E
  have h_ro := OracleComp.run_interpret_readOnly (fun (q : Query Key Block)
      (P : Key → Equiv.Perm Block) =>
      PMF.pure (Cslib.RandomPermutation.evalPerm (P q.1) q.2)) A E
  have h_lazy : (interpret lazyEvalPerm A).run E =
      (interpret (fun (q : Query Key Block) =>
        PMF.pure (Cslib.RandomPermutation.evalPerm (E q.1) q.2)) A).map (·, E) :=
    h_ro
  change ((interpret lazyEvalPerm A).run E).map _ = _
  rw [h_lazy, PMF.map_comp, interpret_bind, Probability.PMF.monad_bind_eq_bind,
    ← PMF.bind_pure_comp]
  apply congrArg
  ext1 p
  simp only [interpret_bind, interpret_query, interpret_pure,
    Cslib.RandomPermutation.evalPerm_forward, pmf_norm, daviesMeyer]

/-- Switching bound between the real ideal cipher and the forgetful sampler on
`daviesMeyerCollisionProgram A`. -/
theorem daviesMeyer_collision_difference_bound [AddGroup Block]
    {A : CollisionFinder Key Block} {Q : ℕ} (hQ : IsQueryBounded A Q) :
    |Pr[(PMF.pi fun _ : Key => PMF.uniformOfFintype (Equiv.Perm Block)).bind fun P =>
        interpret (fun (q : Query Key Block) =>
          PMF.pure (Cslib.RandomPermutation.evalPerm (P q.1) q.2))
          (daviesMeyerCollisionProgram A)] -
      Pr[((interpret forgetfulAnswer (daviesMeyerCollisionProgram A)).run fun _ => []).map
        Prod.fst]| ≤
      ((Q + 2).choose 2 : ℝ) * (Fintype.card Block : ℝ)⁻¹ := by
  simpa only [PMF.bind_pure, Probability.PMF.monad_bind_eq_bind] using
    abs_sub_uniformPerm_forgetful_le (isQueryBounded_daviesMeyerCollisionProgram hQ)
      (PMF.pure (α := Bool)) true

end Games

section Helpers

private def HasDMCollision {Key Block : Type} [Add Block]
    (st : Key → Cslib.RandomPermutation.Cache Block) : Prop :=
  ∃ (k1 : Key) (i1 : Fin (st k1).length) (k2 : Key) (i2 : Fin (st k2).length),
    (k1, i1.1) ≠ (k2, i2.1) ∧
      (st k1)[i1].2 + (st k1)[i1].1 = (st k2)[i2].2 + (st k2)[i2].1

private theorem not_hasDMCollision_nil {Key Block : Type} [Add Block] :
    ¬ HasDMCollision (fun _ : Key => ([] : Cslib.RandomPermutation.Cache Block)) := by
  rintro ⟨_, i1, _⟩
  exact i1.elim0

private theorem hasDMCollision_of_mem {Key Block : Type} [Add Block]
    {st : Key → Cslib.RandomPermutation.Cache Block}
    {k1 k2 : Key} {x1 x2 y1 y2 : Block}
    (hne : (k1, x1) ≠ (k2, x2)) (heq : y1 + x1 = y2 + x2)
    (h1 : (x1, y1) ∈ st k1) (h2 : (x2, y2) ∈ st k2) :
    HasDMCollision st := by
  obtain ⟨i1, hi1, hget1⟩ := List.mem_iff_getElem.mp h1
  obtain ⟨i2, hi2, hget2⟩ := List.mem_iff_getElem.mp h2
  refine ⟨k1, ⟨i1, hi1⟩, k2, ⟨i2, hi2⟩, ?_, ?_⟩
  · intro h
    obtain ⟨hk, hi⟩ := Prod.mk.inj h
    subst hk
    subst hi
    apply hne
    have hpair : (x1, y1) = (x2, y2) := hget1.symm.trans hget2
    exact congrArg (k1, ·) (Prod.mk.inj hpair).1
  · simp [hget1, hget2, heq]

private theorem mem_of_mem_support_forgetfulAnswer {Key Block : Type}
    [DecidableEq Key] [DecidableEq Block] [Fintype Block] [Nonempty Block]
    {q : Query Key Block} {st st' : Key → Cslib.RandomPermutation.Cache Block} {a : Block}
    (hmem : (a, st') ∈ (forgetfulAnswer q st).support) :
    ∀ k e, e ∈ st k → e ∈ st' k := by
  simp only [forgetfulAnswer, PMF.mem_support_map_iff] at hmem
  obtain ⟨⟨b, c⟩, hbc, h_eq⟩ := hmem
  cases h_eq
  intro k e he
  by_cases hk : k = q.1
  · subst hk
    simp only [Function.update_self]
    cases hq2 : q.2 with
    | forward x =>
      rw [hq2] at hbc
      cases hlook : (st q.1).lookup x with
      | some v =>
        rw [Cslib.RandomPermutation.forgetfulAnswer_forward_of_some hlook,
          PMF.mem_support_pure_iff] at hbc
        cases hbc
        exact he
      | none =>
        rw [Cslib.RandomPermutation.forgetfulAnswer_forward_of_none hlook,
          PMF.mem_support_map_iff] at hbc
        obtain ⟨y, -, hy⟩ := hbc
        cases hy
        exact List.mem_cons_of_mem _ he
    | inverse y =>
      rw [hq2] at hbc
      cases hlook : Cslib.RandomPermutation.invLookup (st q.1) y with
      | some v =>
        rw [Cslib.RandomPermutation.forgetfulAnswer_inverse_of_some hlook,
          PMF.mem_support_pure_iff] at hbc
        cases hbc
        exact he
      | none =>
        rw [Cslib.RandomPermutation.forgetfulAnswer_inverse_of_none hlook,
          PMF.mem_support_map_iff] at hbc
        obtain ⟨x, -, hx⟩ := hbc
        cases hx
        exact List.mem_cons_of_mem _ he
  · simp [Function.update_of_ne hk, he]

private theorem mem_of_mem_support_forgetfulAnswer_forward {Key Block : Type}
    [DecidableEq Key] [DecidableEq Block] [Fintype Block] [Nonempty Block]
    {k : Key} {x y : Block} {st st' : Key → Cslib.RandomPermutation.Cache Block}
    (hmem : (y, st') ∈ (forgetfulAnswer (k, .forward x) st).support) :
    (x, y) ∈ st' k := by
  simp only [forgetfulAnswer, PMF.mem_support_map_iff] at hmem
  obtain ⟨⟨b, c⟩, hbc, h_eq⟩ := hmem
  cases h_eq
  simp only [Function.update_self]
  cases hlook : (st k).lookup x with
  | some v =>
    rw [Cslib.RandomPermutation.forgetfulAnswer_forward_of_some hlook,
      PMF.mem_support_pure_iff] at hbc
    cases hbc
    exact Cslib.RandomPermutation.mem_of_lookup_eq_some hlook
  | none =>
    rw [Cslib.RandomPermutation.forgetfulAnswer_forward_of_none hlook,
      PMF.mem_support_map_iff] at hbc
    obtain ⟨y0, -, hy0⟩ := hbc
    cases hy0
    exact List.mem_cons_self

private theorem hasDMCollision_of_mem_support_daviesMeyerCollisionProgram {Key Block : Type}
    [DecidableEq Key] [DecidableEq Block] [Fintype Block] [Nonempty Block] [Add Block]
    {A : CollisionFinder Key Block} {st₀ st : Key → Cslib.RandomPermutation.Cache Block}
    (hmem : (true, st) ∈
      ((interpret forgetfulAnswer (daviesMeyerCollisionProgram A)).run st₀).support) :
    HasDMCollision st := by
  unfold daviesMeyerCollisionProgram at hmem
  simp only [StateT.run_bind, StateT.run_pure, interpret_bind, interpret_query, interpret_pure,
    Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hmem
  obtain ⟨⟨⟨⟨k1, x1⟩, ⟨k2, x2⟩⟩, stA⟩, -, ⟨y1, st1⟩, hy1, ⟨y2, st2⟩, hy2, hres⟩ := hmem
  obtain ⟨hbool, hst⟩ := Prod.mk.inj hres
  subst hst
  have hcond : (k1, x1) ≠ (k2, x2) ∧ y1 + x1 = y2 + x2 := of_decide_eq_true hbool.symm
  exact hasDMCollision_of_mem hcond.1 hcond.2
    (mem_of_mem_support_forgetfulAnswer hy2 k1 (x1, y1)
      (mem_of_mem_support_forgetfulAnswer_forward hy1))
    (mem_of_mem_support_forgetfulAnswer_forward hy2)

private def dmTargets {Key Block : Type} [Fintype Key] [DecidableEq Block] [Add Block]
    (st : Key → Cslib.RandomPermutation.Cache Block) : Finset Block :=
  Finset.univ.biUnion fun k => (st k).toFinset.image fun e => e.2 + e.1

private theorem card_dmTargets_le {Key Block : Type} [Fintype Key] [DecidableEq Block] [Add Block]
    (st : Key → Cslib.RandomPermutation.Cache Block) :
    (dmTargets st).card ≤ ∑ k : Key, (st k).length :=
  calc (dmTargets st).card
      ≤ ∑ k : Key, ((st k).toFinset.image fun e : Block × Block => e.2 + e.1).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ k : Key, (st k).toFinset.card :=
        Finset.sum_le_sum fun _ _ => Finset.card_image_le
    _ ≤ ∑ k : Key, (st k).length :=
        Finset.sum_le_sum fun k _ => List.toFinset_card_le (st k)

private theorem mem_dmTargets_of_getElem {Key Block : Type} [Fintype Key] [DecidableEq Block]
    [Add Block] {st : Key → Cslib.RandomPermutation.Cache Block}
    (k : Key) (i : Fin (st k).length) :
    (st k)[i].2 + (st k)[i].1 ∈ dmTargets st := by
  refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, Finset.mem_image.mpr ?_⟩
  exact ⟨(st k)[i], List.mem_toFinset.mpr (List.getElem_mem i.2), rfl⟩

private theorem classify_update_idx {Key Block : Type} [DecidableEq Key]
    {st : Key → Cslib.RandomPermutation.Cache Block} (qk : Key) (e : Block × Block)
    (k : Key) (i : Fin (Function.update st qk (e :: st qk) k).length) :
    (k = qk ∧ i.1 = 0 ∧ (Function.update st qk (e :: st qk) k)[i] = e) ∨
      ∃ j : Fin (st k).length,
        (Function.update st qk (e :: st qk) k)[i] = (st k)[j] ∧
        (k = qk → j.1 + 1 = i.1) ∧ (k ≠ qk → j.1 = i.1) := by
  by_cases hk : k = qk
  · subst hk
    rcases i with ⟨n, hn⟩
    cases n with
    | zero =>
      left
      refine ⟨rfl, rfl, ?_⟩
      simp
    | succ m =>
      right
      have hm : m < (st k).length := by simpa using hn
      refine ⟨⟨m, hm⟩, ?_, fun _ => rfl, fun hne => (hne rfl).elim⟩
      simp
  · right
    have hi : i.1 < (st k).length := by simpa [Function.update_of_ne hk] using i.2
    refine ⟨⟨i.1, hi⟩, ?_, fun h => (hk h).elim, fun _ => rfl⟩
    simp [Function.update_of_ne hk]

private theorem dmTargets_of_hasDMCollision_update {Key Block : Type}
    [DecidableEq Key] [Fintype Key] [DecidableEq Block] [Add Block]
    {st : Key → Cslib.RandomPermutation.Cache Block} (hst : ¬ HasDMCollision st)
    (qk : Key) (e : Block × Block)
    (hcol : HasDMCollision (Function.update st qk (e :: st qk))) :
    e.2 + e.1 ∈ dmTargets st := by
  obtain ⟨k1, i1, k2, i2, hne, heq⟩ := hcol
  rcases classify_update_idx qk e k1 i1 with
    ⟨hk1, hi1, hget1⟩ | ⟨j1, hget1, h1_eq, h1_ne⟩
  · rcases classify_update_idx qk e k2 i2 with
      ⟨hk2, hi2, _⟩ | ⟨j2, hget2, _, _⟩
    · exact (hne (Prod.ext (hk1.trans hk2.symm) (hi1.trans hi2.symm))).elim
    · rw [hget1, hget2] at heq
      rw [heq]
      exact mem_dmTargets_of_getElem k2 j2
  · rcases classify_update_idx qk e k2 i2 with
      ⟨_, _, hget2⟩ | ⟨j2, hget2, h2_eq, h2_ne⟩
    · rw [hget1, hget2] at heq
      rw [← heq]
      exact mem_dmTargets_of_getElem k1 j1
    · exfalso
      apply hst
      refine ⟨k1, j1, k2, j2, ?_, ?_⟩
      · intro hkj
        obtain ⟨hk, hj⟩ := Prod.mk.inj hkj
        apply hne
        apply Prod.ext hk
        by_cases hkq : k1 = qk
        · have hk2q : k2 = qk := hk.symm.trans hkq
          have := h1_eq hkq
          have := h2_eq hk2q
          omega
        · have hk2q : k2 ≠ qk := fun h => hkq (hk.trans h)
          have := h1_ne hkq
          have := h2_ne hk2q
          omega
      · rw [← hget1, ← hget2, heq]

private theorem toOuterMeasure_bad_forgetfulAnswer_step {Key Block : Type}
    [DecidableEq Key] [Fintype Key] [DecidableEq Block] [Fintype Block] [Nonempty Block]
    [AddGroup Block] (q : Query Key Block) (st : Key → Cslib.RandomPermutation.Cache Block)
    (hst : ¬ HasDMCollision st) :
    (forgetfulAnswer q st).toOuterMeasure {x | HasDMCollision x.2} ≤
      (∑ k : Key, (st k).length : ℕ) * (Fintype.card Block : ℝ≥0∞)⁻¹ := by
  have hle_sum :
      ∀ (f : Block → Block) (e : Block → Block × Block),
        Function.Injective f →
        (∀ a, (e a).2 + (e a).1 = f a) →
        ((PMF.uniformOfFintype Block).map fun a =>
          (a, Function.update st q.1 (e a :: st q.1))).toOuterMeasure
            {x | HasDMCollision x.2} ≤
          (∑ k : Key, (st k).length : ℕ) * (Fintype.card Block : ℝ≥0∞)⁻¹ := by
    intro f e hinj hfe
    rw [PMF.toOuterMeasure_map_apply]
    have hsub : (fun a : Block => (a, Function.update st q.1 (e a :: st q.1))) ⁻¹'
        {x | HasDMCollision x.2} ⊆ {a : Block | f a ∈ dmTargets st} := by
      intro a ha
      rw [Set.mem_preimage, Set.mem_ofPred_eq] at ha
      rw [Set.mem_ofPred_eq, ← hfe a]
      exact dmTargets_of_hasDMCollision_update hst q.1 (e a) ha
    refine (MeasureTheory.measure_mono hsub).trans ?_
    rw [Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype]
    gcongr
    have hcard_inj : (Finset.univ.filter fun a : Block => f a ∈ dmTargets st).card ≤
        (dmTargets st).card := by
      refine Finset.card_le_card_of_injOn f (fun a ha => ?_) (fun a _ b _ hab => hinj hab)
      simpa using (Finset.mem_filter.mp ha).2
    exact Nat.cast_le.mpr (hcard_inj.trans (card_dmTargets_le st))
  simp only [forgetfulAnswer]
  have hmap_comp : ∀ (p : PMF (Block × Cslib.RandomPermutation.Cache Block)),
      (p.map fun bc => (bc.1, Function.update st q.1 bc.2)).toOuterMeasure
        {x | HasDMCollision x.2} =
      (p.map fun bc => (bc.1, Function.update st q.1 bc.2)).toOuterMeasure
        {x | HasDMCollision x.2} := fun _ => rfl
  cases hq2 : q.2 with
  | forward x =>
    cases hlook : (st q.1).lookup x with
    | some y =>
      rw [Cslib.RandomPermutation.forgetfulAnswer_forward_of_some hlook, PMF.pure_map]
      simp [hst, PMF.toOuterMeasure_pure_apply]
    | none =>
      rw [Cslib.RandomPermutation.forgetfulAnswer_forward_of_none hlook, PMF.map_comp]
      exact hle_sum (fun y => y + x) (fun y => (x, y)) (add_left_injective x) (fun _ => rfl)
  | inverse y =>
    cases hlook : Cslib.RandomPermutation.invLookup (st q.1) y with
    | some x =>
      rw [Cslib.RandomPermutation.forgetfulAnswer_inverse_of_some hlook, PMF.pure_map]
      simp [hst, PMF.toOuterMeasure_pure_apply]
    | none =>
      rw [Cslib.RandomPermutation.forgetfulAnswer_inverse_of_none hlook, PMF.map_comp]
      exact hle_sum (fun x => y + x) (fun x => (x, y)) (add_right_injective y) (fun _ => rfl)

private theorem forgetfulAnswer_size_grow {Key Block : Type}
    [DecidableEq Key] [Fintype Key] [DecidableEq Block] [Fintype Block] [Nonempty Block]
    (q : Query Key Block) (st : Key → Cslib.RandomPermutation.Cache Block)
    (x : Block × (Key → Cslib.RandomPermutation.Cache Block))
    (hmem : x ∈ (forgetfulAnswer q st).support) :
    ∑ k : Key, (x.2 k).length ≤ (∑ k : Key, (st k).length) + 1 := by
  rcases x with ⟨a, st'⟩
  simp only [forgetfulAnswer, PMF.mem_support_map_iff] at hmem
  obtain ⟨⟨b, c⟩, hbc, h_eq⟩ := hmem
  cases h_eq
  have hc_len : c.length ≤ (st q.1).length + 1 := by
    cases hq2 : q.2 with
    | forward x0 =>
      rw [hq2] at hbc
      cases hlook : (st q.1).lookup x0 with
      | some v =>
        rw [Cslib.RandomPermutation.forgetfulAnswer_forward_of_some hlook,
          PMF.mem_support_pure_iff] at hbc
        cases hbc
        exact Nat.le_succ _
      | none =>
        rw [Cslib.RandomPermutation.forgetfulAnswer_forward_of_none hlook,
          PMF.mem_support_map_iff] at hbc
        obtain ⟨y0, -, hy0⟩ := hbc
        cases hy0
        simp
    | inverse y0 =>
      rw [hq2] at hbc
      cases hlook : Cslib.RandomPermutation.invLookup (st q.1) y0 with
      | some v =>
        rw [Cslib.RandomPermutation.forgetfulAnswer_inverse_of_some hlook,
          PMF.mem_support_pure_iff] at hbc
        cases hbc
        exact Nat.le_succ _
      | none =>
        rw [Cslib.RandomPermutation.forgetfulAnswer_inverse_of_none hlook,
          PMF.mem_support_map_iff] at hbc
        obtain ⟨x0, -, hx0⟩ := hbc
        cases hx0
        simp
  have hsum1 : ∑ k : Key, (Function.update st q.1 c k).length =
      c.length + ∑ k ∈ Finset.univ.erase q.1, (st k).length := by
    rw [← Finset.add_sum_erase Finset.univ
      (fun k => (Function.update st q.1 c k).length) (Finset.mem_univ q.1)]
    simp only [Function.update_self]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    simp [Function.update_of_ne (Finset.mem_erase.mp hk).1]
  have hsum2 : ∑ k : Key, (st k).length =
      (st q.1).length + ∑ k ∈ Finset.univ.erase q.1, (st k).length :=
    (Finset.add_sum_erase Finset.univ (fun k => (st k).length) (Finset.mem_univ q.1)).symm
  dsimp only
  omega

private theorem forgetful_daviesMeyer_collision_le {Key Block : Type}
    [DecidableEq Key] [Finite Key] [DecidableEq Block] [Fintype Block] [Nonempty Block]
    [AddGroup Block] {A : CollisionFinder Key Block} {Q : ℕ} (hQ : IsQueryBounded A Q) :
    Pr[((interpret forgetfulAnswer (daviesMeyerCollisionProgram A)).run fun _ => []).map
      Prod.fst] ≤
      ((Q + 2).choose 2 : ℝ) * (Fintype.card Block : ℝ)⁻¹ := by
  let _ := Fintype.ofFinite Key
  have hQ_prog := isQueryBounded_daviesMeyerCollisionProgram hQ
  have hbad := OracleComp.toOuterMeasure_bad_choose_two_le
    (handler := forgetfulAnswer (Key := Key) (Block := Block))
    (bad := HasDMCollision)
    (fun st : Key → Cslib.RandomPermutation.Cache Block => ∑ k : Key, (st k).length)
    (Fintype.card Block : ℝ≥0∞)⁻¹
    (fun q st hst => toOuterMeasure_bad_forgetfulAnswer_step q st hst)
    (fun q st _ x hmem _ => forgetfulAnswer_size_grow q st x hmem)
    hQ_prog not_hasDMCollision_nil
  have h_len0 : ∑ _k : Key, ([] : Cslib.RandomPermutation.Cache Block).length = 0 := by simp
  rw [h_len0, mul_zero, zero_add] at hbad
  set p := (interpret forgetfulAnswer (daviesMeyerCollisionProgram A)).run (fun _ => [])
  have h_apply : (p.map Prod.fst) true ≤ p.toOuterMeasure {x | HasDMCollision x.2} := by
    have h_map : (p.map Prod.fst) true = p.toOuterMeasure {x | x.1 = true} := by
      rw [PMF.map_apply, PMF.toOuterMeasure_apply]
      refine tsum_congr fun ⟨b, st⟩ => ?_
      by_cases hb : b = true
      · simp [hb]
      · simp [hb]
    rw [h_map, PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
    refine tsum_le_tsum fun ⟨b, st⟩ => ?_
    by_cases hmem : (b, st) ∈ p.support
    · by_cases hb : b = true
      · subst hb
        have hcol : HasDMCollision st :=
          hasDMCollision_of_mem_support_daviesMeyerCollisionProgram hmem
        simp [hcol]
      · simp [hb]
    · have hz : p (b, st) = 0 := (PMF.apply_eq_zero_iff _ _).mpr hmem
      simp [Set.indicator_apply, hz]
  have h_enn : (p.map Prod.fst) true ≤
      ((Q + 2).choose 2 : ℕ) * (Fintype.card Block : ℝ≥0∞)⁻¹ :=
    h_apply.trans hbad
  have htop : ((Q + 2).choose 2 : ℕ) * (Fintype.card Block : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_inv] using
    ENNReal.toReal_mono htop h_enn

end Helpers

section MainTheorems

variable {Key Block : Type} [DecidableEq Key] [Fintype Key] [DecidableEq Block]
  [Fintype Block] [Nonempty Block]

/-- **Davies–Meyer Ideal-Cipher Collision Resistance** ([KatzLindell2020], Section 7.3.1,
Theorem 7.5): any `Q`-query adaptive adversary making forward and inverse ideal-cipher queries
finds a collision in `daviesMeyer` with probability at most
`2 * ((Q + 2).choose 2) * (Fintype.card Block)⁻¹`. -/
theorem daviesMeyer_collisionGame_le [AddGroup Block]
    {A : CollisionFinder Key Block} {Q : ℕ} (hQ : IsQueryBounded A Q) :
    Pr[collisionGame (daviesMeyer (K := Key) (B := Block)) A] ≤
      2 * ((Q + 2).choose 2 : ℝ) * (Fintype.card Block : ℝ)⁻¹ := by
  rw [collisionGame_daviesMeyer_eq]
  have h_diff := (abs_sub_le_iff.mp (daviesMeyer_collision_difference_bound hQ)).1
  have h_forg := forgetful_daviesMeyer_collision_le hQ
  linarith

/-- Equivalent product form `((Q + 2) * (Q + 1) : ℝ) * (Fintype.card Block)⁻¹` of
`daviesMeyer_collisionGame_le` ([KatzLindell2020], Theorem 7.5). -/
theorem daviesMeyer_collisionGame_mul_le [AddGroup Block]
    {A : CollisionFinder Key Block} {Q : ℕ} (hQ : IsQueryBounded A Q) :
    Pr[collisionGame (daviesMeyer (K := Key) (B := Block)) A] ≤
      ((Q + 2) * (Q + 1) : ℝ) * (Fintype.card Block : ℝ)⁻¹ := by
  have hchoose : 2 * ((Q + 2).choose 2 : ℝ) = (Q + 2) * (Q + 1) := by
    rw [Nat.cast_choose_two ℝ (Q + 2)]
    push_cast
    ring
  simpa only [hchoose] using daviesMeyer_collisionGame_le hQ

end MainTheorems

end Cslib.IdealCipher
