/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Languages.Probabilistic.Semantics
public import Complexity.Probability.Product
public import Complexity.Probability.Uniform

/-!
# Additive secret sharing and independent family sampling

This module provides two foundational primitives for multi-party protocols in `Cslib.ProbComp`:

1. **Dependent family sampling (`Cslib.ProbComp.pi`):** runs an `m`-tuple of probabilistic programs
   `programs : (i : Fin m) → ProbComp (α i)` in index order and collects the dependent tuple of
   results `(i : Fin m) → α i`. When each coordinate type is finite, `eval (pi programs)` is the
   product distribution `PMF.pi (fun i => eval (programs i))`.
2. **Additive secret sharing (`Cslib.ProbComp.completeShares`,
   `Cslib.ProbComp.sampleAdditiveShares`):**
   deterministically completes `m - 1` shares in an additive commutative group `G` to `m` shares
   summing to `target : G`, and samples uniform additive shares of `target` by drawing the first
   `m - 1` shares uniformly from `Fin (m - 1) → G`. For every proper coalition
   `I : Finset (Fin m)` (`I ≠ Finset.univ`), the marginal distribution of `I`'s shares is uniform
   on `(i : I) → G` and independent of `target` (`eval_restrict_sampleAdditiveShares`).

## Main definitions

* `Cslib.ProbComp.pi`: sequential execution of an `m`-tuple of probabilistic programs.
* `Cslib.ProbComp.completeShares`: deterministic completion of `m - 1` additive shares to `m`
  shares summing to `target`.
* `Cslib.ProbComp.sampleAdditiveShares`: uniform additive share sampler summing to `target`.

## Main results

* `Cslib.ProbComp.mem_support_pi_iff`, `Cslib.ProbComp.eval_pi`,
  `Cslib.ProbComp.eval_pi_congr`, `Cslib.ProbComp.eval_pi_map`: support, product distribution, and
  functorial laws for `ProbComp.pi`.
* `Cslib.ProbComp.sum_completeShares`, `Cslib.ProbComp.sum_sampleAdditiveShares`: additive shares
  sum to `target`.
* `Cslib.ProbComp.eval_restrict_sampleAdditiveShares`: any proper subset of shares is uniformly
  distributed and independent of `target`.
* `Cslib.ProbComp.eq_eval_sampleAdditiveShares_of_sum_of_map_init`: uniqueness of the uniform
  additive share distribution from its sum and first `m - 1` marginals.

## References

* [O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*][Goldreich2004]
-/

@[expose] public section

namespace Cslib.ProbComp

open Probability
open scoped ENNReal

/-! ### Independent family sampling over `Fin m` -/

/-- Run a family of `m` probabilistic programs indexed by `Fin m` in order, returning the
dependent tuple of their results. -/
def pi : {m : ℕ} → {α : Fin m → Type} →
    ((i : Fin m) → ProbComp (α i)) → ProbComp ((i : Fin m) → α i)
  | 0, _, _ => pure (fun i => i.elim0)
  | m + 1, _, programs =>
    programs 0 >>= fun first => Fin.cons first <$> pi (fun i : Fin m => programs i.succ)

@[simp] theorem pi_zero {α : Fin 0 → Type} (programs : (i : Fin 0) → ProbComp (α i)) :
    pi programs = pure (fun i => i.elim0) := rfl

@[simp] theorem pi_succ {m : ℕ} {α : Fin (m + 1) → Type}
    (programs : (i : Fin (m + 1)) → ProbComp (α i)) :
    pi programs =
      (programs 0 >>= fun first => Fin.cons first <$> pi (fun i : Fin m => programs i.succ)) := rfl

/-- A tuple is in the support of `pi programs` if and only if each coordinate is in the support of
its coordinate program. -/
theorem mem_support_pi_iff {m : ℕ} {α : Fin m → Type}
    (programs : (i : Fin m) → ProbComp (α i)) (r : (i : Fin m) → α i) :
    r ∈ (eval (pi programs)).support ↔ ∀ i, r i ∈ (eval (programs i)).support := by
  induction m with
  | zero =>
    have hr : r = fun i => i.elim0 := funext fun i => i.elim0
    subst hr
    simp
  | succ m ih =>
    simp only [pi_succ, eval_bind, eval_map, PMF.mem_support_bind_iff, PMF.mem_support_map_iff, ih]
    constructor
    · rintro ⟨first, hfirst, rest, hrest, rfl⟩ i
      refine Fin.cases ?_ ?_ i
      · simpa using hfirst
      · intro j
        simpa using hrest j
    · intro h
      refine ⟨r 0, h 0, fun j => r j.succ, fun j => h j.succ, ?_⟩
      ext i
      exact Fin.cases rfl (fun _ => rfl) i

/-- Evaluating `pi programs` depends only on the distributions of the individual programs. -/
theorem eval_pi_congr {m : ℕ} {α : Fin m → Type}
    {p q : (i : Fin m) → ProbComp (α i)} (h : ∀ i, eval (p i) = eval (q i)) :
    eval (pi p) = eval (pi q) := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [pi_succ, eval_bind, eval_map, h 0, ih (fun i => h i.succ)]

/-- Mapping each coordinate program commutes with `pi`. -/
theorem eval_pi_map {m : ℕ} {α β : Fin m → Type}
    (programs : (i : Fin m) → ProbComp (α i)) (f : (i : Fin m) → α i → β i) :
    eval (pi (fun i => f i <$> programs i)) =
      (eval (pi programs)).map (fun r i => f i (r i)) := by
  induction m with
  | zero =>
    simp only [pi_zero, eval_pure, PMF.pure_map]
    congr 1
    ext i
    exact i.elim0
  | succ m ih =>
    simp only [pi_succ, eval_bind, eval_map, ih, PMF.bind_map, PMF.map_bind, PMF.map_comp]
    refine congrArg _ (funext fun first => congrArg (PMF.map · _) (funext fun rest => ?_))
    ext i
    exact Fin.cases rfl (fun _ => rfl) i

/-- When each coordinate type is finite, `eval (pi programs)` is the independent product
distribution `PMF.pi`. -/
theorem eval_pi {m : ℕ} {α : Fin m → Type} [∀ i, Finite (α i)]
    (programs : (i : Fin m) → ProbComp (α i)) :
    eval (pi programs) = PMF.pi (fun i => eval (programs i)) := by
  induction m with
  | zero =>
    ext r
    have hr : r = fun i => i.elim0 := funext fun i => i.elim0
    subst hr
    simp
  | succ m ih =>
    rw [pi_succ, eval_bind]
    ext r
    simp only [eval_map, ih, PMF.bind_apply, PMF.map_apply, PMF.pi_apply]
    rw [Fin.prod_univ_succ, tsum_eq_single (r 0)]
    · congr 1
      rw [tsum_eq_single (fun i : Fin m => r i.succ)]
      · rw [ite_eq_left]
        ext i
        exact Fin.cases rfl (fun _ => rfl) i
      · intro b hb
        rw [ite_eq_right]
        intro hEq
        apply hb
        funext i
        simpa using (congrFun hEq (Fin.succ i)).symm
    · intro a ha
      simp only [mul_eq_zero, ENNReal.tsum_eq_zero]
      right
      intro b
      rw [ite_eq_right]
      intro hEq
      exact ha (by simpa using (congrFun hEq 0).symm)

/-- Run the programs in a subset `I : Finset (Fin m)` in index order, returning a dependent tuple
on `I` without running programs outside `I`. -/
def piRestrict : {m : ℕ} → {α : Fin m → Type} → (I : Finset (Fin m)) →
    ((i : I) → ProbComp (α i.1)) → ProbComp ((i : I) → α i.1)
  | 0, _, _, _ => pure (fun i => i.1.elim0)
  | m + 1, α, I, programs =>
    let I' : Finset (Fin m) := Finset.univ.filter (fun j : Fin m => j.succ ∈ I)
    let restProg : (j : I') → ProbComp (α j.1.succ) :=
      fun j => programs ⟨j.1.succ, (Finset.mem_filter.mp j.2).2⟩
    if h0 : (0 : Fin (m + 1)) ∈ I then
      programs ⟨0, h0⟩ >>= fun first =>
        (fun (rest : (j : I') → α j.1.succ) (i : I) =>
          Fin.cases
            (motive := fun k => k ∈ I → α k)
            (fun _ => first)
            (fun j hj => rest ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩)
            i.1 i.2) <$> piRestrict (α := fun k => α k.succ) I' restProg
    else
      (fun (rest : (j : I') → α j.1.succ) (i : I) =>
        Fin.cases
          (motive := fun k => k ∈ I → α k)
          (fun hk => (h0 hk).elim)
          (fun j hj => rest ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩)
          i.1 i.2) <$> piRestrict (α := fun k => α k.succ) I' restProg

/-- Binding `eval (pi programs)` to a continuation that depends only on `I.restrict r` is
equivalent to running only the programs in `I` via `piRestrict`. No finiteness assumption on `α`
is needed. -/
theorem eval_bind_restrict_pi {m : ℕ} {α : Fin m → Type} {β : Type}
    (I : Finset (Fin m)) (programs : (i : Fin m) → ProbComp (α i))
    (k : ((i : I) → α i.1) → PMF β) :
    (eval (pi programs)).bind (fun r => k (I.restrict r)) =
      (eval (piRestrict I (I.restrict programs))).bind k := by
  induction m with
  | zero =>
    simp only [pi_zero, piRestrict, eval_pure, PMF.pure_bind]
    exact congrArg k (funext fun i => i.1.elim0)
  | succ m ih =>
    let I' : Finset (Fin m) := Finset.univ.filter (fun j : Fin m => j.succ ∈ I)
    simp only [pi_succ, piRestrict, eval_bind, eval_map, PMF.bind_bind, PMF.bind_map]
    by_cases h0 : (0 : Fin (m + 1)) ∈ I
    · simp only [dite_eq_left h0, eval_bind, eval_map, PMF.bind_bind, PMF.bind_map,
        Function.comp_def]
      refine congrArg _ (funext fun first => ?_)
      have hih := ih (α := fun j => α j.succ) I' (fun j => programs j.succ) (fun rest =>
        k (fun i =>
          Fin.cases (motive := fun idx => idx ∈ I → α idx)
            (fun _ => first)
            (fun j hj => rest ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩)
            i.1 i.2))
      refine (congrArg (eval _).bind (funext fun rest => ?_)).trans hih
      exact congrArg k (funext fun ⟨i, hi⟩ =>
        Fin.cases (motive := fun idx => ∀ h : idx ∈ I, Fin.cons first rest idx =
          Fin.cases (motive := fun idx => idx ∈ I → α idx) (fun _ => first)
            (fun j hj => I'.restrict rest ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩) idx h)
          (fun _ => rfl) (fun _ _ => rfl) i hi)
    · simp only [dite_eq_right h0, eval_map, PMF.bind_map, Function.comp_def]
      have hconst : ∀ first : α 0,
          (eval (pi fun i : Fin m => programs i.succ)).bind
            (fun x => k (I.restrict (Fin.cons first x))) =
          (eval (piRestrict (α := fun j => α j.succ) I' (fun j => programs j.1.succ))).bind
            (fun rest =>
              k (fun i =>
                Fin.cases (motive := fun idx => idx ∈ I → α idx)
                  (fun hk => (h0 hk).elim)
                  (fun j hj => rest ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩)
                  i.1 i.2)) := by
        intro first
        have hih := ih (α := fun j => α j.succ) I' (fun j => programs j.succ) (fun rest =>
          k (fun i =>
            Fin.cases (motive := fun idx => idx ∈ I → α idx)
              (fun hk => (h0 hk).elim)
              (fun j hj => rest ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩)
              i.1 i.2))
        refine (congrArg (eval _).bind (funext fun rest => ?_)).trans hih
        exact congrArg k (funext fun ⟨i, hi⟩ =>
          Fin.cases (motive := fun idx => ∀ h : idx ∈ I, Fin.cons first rest idx =
            Fin.cases (motive := fun idx => idx ∈ I → α idx) (fun hk => (h0 hk).elim)
              (fun j hj => I'.restrict rest ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩)
                idx h)
            (fun h => (h0 h).elim) (fun _ _ => rfl) i hi)
      rw [congrArg (eval (programs 0)).bind (funext hconst), PMF.bind_const]
      rfl

/-- Restricting `eval (pi programs)` to a subset `I : Finset (Fin m)` has the same law as
`piRestrict I (I.restrict programs)`. -/
theorem eval_map_restrict_pi {m : ℕ} {α : Fin m → Type}
    (I : Finset (Fin m)) (programs : (i : Fin m) → ProbComp (α i)) :
    (eval (pi programs)).map I.restrict = eval (piRestrict I (I.restrict programs)) := by
  simpa only [PMF.map, Function.comp_def, PMF.bind_pure] using
    eval_bind_restrict_pi I programs PMF.pure

/-! ### Additive secret sharing in a finite commutative group -/

/-- The last index `⟨m - 1, _⟩` of `Fin m` for `m ≠ 0`. -/
def lastFin (m : ℕ) [NeZero m] : Fin m :=
  ⟨m - 1, Nat.sub_lt (Nat.pos_of_neZero m) Nat.one_pos⟩

/-- Embed `Fin (m - 1)` into `Fin m` as the first `m - 1` indices. -/
def castInit (m : ℕ) (k : Fin (m - 1)) : Fin m :=
  ⟨k.1, Nat.lt_of_lt_of_le k.2 (Nat.sub_le m 1)⟩

/-- Extract the first `m - 1` coordinates of an `m`-tuple. -/
def initOfShares (m : ℕ) {G : Type} (s : Fin m → G) : Fin (m - 1) → G :=
  fun k => s (castInit m k)

/-- Deterministically complete `m - 1` shares `init : Fin (m - 1) → G` to `Fin m → G` summing
to `target`, setting the last coordinate to `target - ∑ j : Fin (m - 1), init j`. -/
@[nolint unusedArguments]
def completeShares (m : ℕ) [NeZero m] {G : Type} [AddCommGroup G]
    (target : G) (init : Fin (m - 1) → G) : Fin m → G :=
  fun i =>
    if h : i.1 < m - 1 then
      init ⟨i.1, h⟩
    else
      target - ∑ j : Fin (m - 1), init j

@[simp] theorem completeShares_castInit (m : ℕ) [NeZero m] {G : Type} [AddCommGroup G]
    (target : G) (init : Fin (m - 1) → G) (k : Fin (m - 1)) :
    completeShares m target init (castInit m k) = init k := by
  simp [completeShares, castInit, k.2]

@[simp] theorem initOfShares_completeShares (m : ℕ) [NeZero m] {G : Type} [AddCommGroup G]
    (target : G) (init : Fin (m - 1) → G) :
    initOfShares m (completeShares m target init) = init := by
  ext k
  exact completeShares_castInit m target init k

@[simp] theorem completeShares_lastFin (m : ℕ) [NeZero m] {G : Type} [AddCommGroup G]
    (target : G) (init : Fin (m - 1) → G) :
    completeShares m target init (lastFin m) = target - ∑ j : Fin (m - 1), init j := by
  simp [completeShares, lastFin]

private theorem sum_univ_eq_add_lastFin (m : ℕ) [NeZero m] {G : Type} [AddCommMonoid G]
    (f : Fin m → G) :
    ∑ i : Fin m, f i = (∑ k : Fin (m - 1), f (castInit m k)) + f (lastFin m) := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (lastFin m))]
  congr 1
  symm
  refine Finset.sum_bij (fun (k : Fin (m - 1)) _ => castInit m k) ?_ ?_ ?_ ?_
  · intro k _
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    intro h
    exact ne_of_lt k.2 (congrArg Fin.val h)
  · intro k₁ _ k₂ _ h
    exact Fin.ext (congrArg (Fin.val : Fin m → ℕ) h)
  · intro i hi
    rw [Finset.mem_erase] at hi
    have hne : i.1 ≠ m - 1 := fun h => hi.1 (Fin.ext h)
    have hlt : i.1 < m - 1 := Nat.lt_of_le_of_ne (Nat.le_sub_one_of_lt i.2) hne
    exact ⟨⟨i.1, hlt⟩, Finset.mem_univ _, rfl⟩
  · intro _ _
    rfl

@[simp] theorem sum_completeShares (m : ℕ) [NeZero m] {G : Type} [AddCommGroup G]
    (target : G) (init : Fin (m - 1) → G) :
    ∑ i : Fin m, completeShares m target init i = target := by
  rw [sum_univ_eq_add_lastFin m (completeShares m target init)]
  simp [add_sub_cancel]

/-- Any `m`-tuple `s` summing to `target` is recovered from its first `m - 1` coordinates by
`completeShares m target`. -/
theorem completeShares_initOfShares (m : ℕ) [NeZero m] {G : Type} [AddCommGroup G]
    {target : G} {s : Fin m → G} (hs : ∑ i : Fin m, s i = target) :
    completeShares m target (initOfShares m s) = s := by
  ext i
  by_cases h : i.1 < m - 1
  · simp [completeShares, h, initOfShares, castInit]
  · have hi : i = lastFin m := by
      ext
      simp only [lastFin]
      omega
    subst hi
    rw [completeShares_lastFin, sub_eq_iff_eq_add', ← hs]
    exact sum_univ_eq_add_lastFin m s

theorem completeShares_add (m : ℕ) [NeZero m] {G : Type} [AddCommGroup G]
    (target₁ target₂ : G) (init₁ init₂ : Fin (m - 1) → G) :
    completeShares m (target₁ + target₂) (init₁ + init₂) =
      completeShares m target₁ init₁ + completeShares m target₂ init₂ := by
  ext i
  by_cases h : i.1 < m - 1
  · simp [completeShares, h]
  · simp [completeShares, h, Finset.sum_add_distrib, add_sub_add_comm]

/-- Sample uniform additive shares `s : Fin m → G` conditioned on `∑ i, s i = target`. -/
noncomputable def sampleAdditiveShares (m : ℕ) [NeZero m]
    {G : Type} [AddCommGroup G] [Fintype G] (target : G) : ProbComp (Fin m → G) :=
  completeShares m target <$> ProbComp.uniform (Fin (m - 1) → G)

theorem sum_sampleAdditiveShares {m : ℕ} [NeZero m]
    {G : Type} [AddCommGroup G] [Fintype G] (target : G)
    {s : Fin m → G} (hs : s ∈ (ProbComp.eval (sampleAdditiveShares m target)).support) :
    ∑ i : Fin m, s i = target := by
  simp only [sampleAdditiveShares, eval_map, PMF.mem_support_map_iff] at hs
  obtain ⟨init, _, rfl⟩ := hs
  exact sum_completeShares m target init

theorem mem_support_sampleAdditiveShares_iff {m : ℕ} [NeZero m]
    {G : Type} [AddCommGroup G] [Fintype G] (target : G) (s : Fin m → G) :
    s ∈ (ProbComp.eval (sampleAdditiveShares m target)).support ↔ ∑ i : Fin m, s i = target := by
  constructor
  · exact sum_sampleAdditiveShares target
  · intro hs
    simp only [sampleAdditiveShares, eval_map, eval_uniform, PMF.mem_support_map_iff]
    refine ⟨initOfShares m s, ?_, completeShares_initOfShares m hs⟩
    simp [PMF.mem_support_iff]

/-- Any distribution `p` on `Fin m → G` supported on tuples summing to `target` whose first
`m - 1` coordinates are uniformly distributed equals `eval (sampleAdditiveShares m target)`. -/
theorem eq_eval_sampleAdditiveShares_of_sum_of_map_init {m : ℕ} [NeZero m]
    {G : Type} [AddCommGroup G] [Fintype G] {target : G} {p : PMF (Fin m → G)}
    (hsum : ∀ s ∈ p.support, ∑ i : Fin m, s i = target)
    (hinit : p.map (initOfShares m) = PMF.uniformOfFintype (Fin (m - 1) → G)) :
    p = eval (sampleAdditiveShares m target) := by
  calc p = p.map id := (PMF.map_id p).symm
    _ = p.map (completeShares m target ∘ initOfShares m) := by
      refine PMF.map_congr_on_support p _ _ fun s hs => ?_
      exact (completeShares_initOfShares m (hsum s hs)).symm
    _ = (p.map (initOfShares m)).map (completeShares m target) := (PMF.map_comp _ _ _).symm
    _ = eval (sampleAdditiveShares m target) := by
      rw [hinit, sampleAdditiveShares, eval_map, eval_uniform]

/-- For any proper coalition `I ≠ Finset.univ`, the marginal distribution of `I`'s shares is
uniform on `(i : I) → G` and independent of `target`. -/
theorem eval_restrict_sampleAdditiveShares {m : ℕ} [NeZero m]
    {G : Type} [AddCommGroup G] [Fintype G]
    (I : Finset (Fin m)) (hI : I ≠ Finset.univ) (target : G) :
    (ProbComp.eval (sampleAdditiveShares m target)).map I.restrict =
      PMF.uniformOfFintype ((i : I) → G) := by
  classical
  rw [sampleAdditiveShares, eval_map, eval_uniform, PMF.map_comp]
  apply Cslib.Probability.PMF.uniformOfFintype_map_of_shift
  intro c
  have hex : ∃ j₀ : Fin m, j₀ ∉ I := by
    by_contra h
    apply hI
    ext i
    simp only [Finset.mem_univ, iff_true]
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨j₀, hj₀⟩ := hex
  let full : Fin m → G := fun i =>
    if hi : i ∈ I then c ⟨i, hi⟩
    else if i = j₀ then -∑ k : I, c k
    else 0
  have hsum : ∑ i : Fin m, full i = 0 := by
    rw [← Finset.sum_subset (Finset.subset_univ (insert j₀ I))]
    · rw [Finset.sum_insert hj₀]
      have h1 : full j₀ = -∑ k : I, c k := by simp [full, hj₀]
      have h2 : ∑ i ∈ I, full i = ∑ k : I, c k := by
        rw [← Finset.sum_attach I]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [full, k.2]
      rw [h1, h2, neg_add_cancel]
    · intro i _ hi
      simp only [Finset.mem_insert, not_or] at hi
      simp [full, hi.1, hi.2]
  have hfull : completeShares m 0 (initOfShares m full) = full :=
    completeShares_initOfShares m hsum
  refine ⟨Equiv.addRight (initOfShares m full), fun init => ?_⟩
  ext ⟨i, hi⟩
  have hadd := congrFun (completeShares_add m target 0 init (initOfShares m full)) i
  change completeShares m target (init + initOfShares m full) i =
    completeShares m target init i + c ⟨i, hi⟩
  rw [add_zero] at hadd
  rw [hadd, Pi.add_apply, hfull]
  simp [full, hi]

/-- Deterministically complete shares on `Finset.univ.erase j₀` to `Fin m → G` summing to `target`,
setting coordinate `j₀` to `target - ∑ k : Finset.univ.erase j₀, sub k`. -/
def completeSharesErase {m : ℕ} {G : Type} [AddCommGroup G]
    (j₀ : Fin m) (target : G) (sub : (i : Finset.univ.erase j₀) → G) : Fin m → G :=
  fun i =>
    if h : i = j₀ then
      target - ∑ k : Finset.univ.erase j₀, sub k
    else
      sub ⟨i, Finset.mem_erase.mpr ⟨h, Finset.mem_univ i⟩⟩

@[simp] theorem restrict_erase_completeSharesErase {m : ℕ} {G : Type} [AddCommGroup G]
    (j₀ : Fin m) (target : G) (sub : (i : Finset.univ.erase j₀) → G) :
    (Finset.univ.erase j₀).restrict (completeSharesErase j₀ target sub) = sub := by
  ext ⟨i, hi⟩
  have hne : i ≠ j₀ := (Finset.mem_erase.mp hi).1
  simp [completeSharesErase, hne]

@[simp] theorem sum_completeSharesErase {m : ℕ} {G : Type} [AddCommGroup G]
    (j₀ : Fin m) (target : G) (sub : (i : Finset.univ.erase j₀) → G) :
    ∑ i : Fin m, completeSharesErase j₀ target sub i = target := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀)]
  have h1 : completeSharesErase j₀ target sub j₀ =
      target - ∑ k : Finset.univ.erase j₀, sub k := by
    simp [completeSharesErase]
  have h2 : ∑ i ∈ Finset.univ.erase j₀, completeSharesErase j₀ target sub i =
      ∑ k : Finset.univ.erase j₀, sub k := by
    rw [← Finset.sum_attach (Finset.univ.erase j₀)]
    refine Finset.sum_congr rfl fun ⟨i, hi⟩ _ => ?_
    have hne : i ≠ j₀ := (Finset.mem_erase.mp hi).1
    simp [completeSharesErase, hne]
  rw [h1, h2, sub_add_cancel]

theorem completeSharesErase_restrict_erase {m : ℕ} {G : Type} [AddCommGroup G]
    (j₀ : Fin m) {target : G} {s : Fin m → G} (hs : ∑ i : Fin m, s i = target) :
    completeSharesErase j₀ target ((Finset.univ.erase j₀).restrict s) = s := by
  ext i
  by_cases h : i = j₀
  · subst h
    simp only [completeSharesErase, ↓reduceDIte]
    rw [sub_eq_iff_eq_add, ← hs, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    congr 1
    rw [← Finset.sum_attach (Finset.univ.erase i)]
    rfl
  · simp [completeSharesErase, h]

/-- For any party `j₀ : Fin m`, `eval (sampleAdditiveShares m target)` is the image of the
uniform distribution on `(i : Finset.univ.erase j₀) → G` under `completeSharesErase j₀ target`. -/
theorem eval_sampleAdditiveShares_eq_map_completeSharesErase {m : ℕ} [NeZero m]
    {G : Type} [AddCommGroup G] [Fintype G] (j₀ : Fin m) (target : G) :
    eval (sampleAdditiveShares m target) =
      (PMF.uniformOfFintype ((i : Finset.univ.erase j₀) → G)).map
        (completeSharesErase j₀ target) := by
  have hI : Finset.univ.erase j₀ ≠ Finset.univ := by
    intro h
    have hj : j₀ ∈ Finset.univ.erase j₀ := h.symm ▸ Finset.mem_univ j₀
    exact (Finset.notMem_erase j₀ Finset.univ) hj
  rw [← eval_restrict_sampleAdditiveShares (Finset.univ.erase j₀) hI target, PMF.map_comp]
  conv_lhs => rw [← PMF.map_id (eval (sampleAdditiveShares m target))]
  refine PMF.map_congr_on_support _ _ _ fun s hs => ?_
  exact (completeSharesErase_restrict_erase j₀ (sum_sampleAdditiveShares target hs)).symm

/-- Any distribution `p` on `Fin m → G` supported on tuples summing to `target` whose marginal on
`Finset.univ.erase j₀` is uniform equals `eval (sampleAdditiveShares m target)`. -/
theorem eq_eval_sampleAdditiveShares_of_sum_of_map_erase {m : ℕ} [NeZero m]
    {G : Type} [AddCommGroup G] [Fintype G] (j₀ : Fin m) {target : G} {p : PMF (Fin m → G)}
    (hsum : ∀ s ∈ p.support, ∑ i : Fin m, s i = target)
    (herase : p.map (Finset.univ.erase j₀).restrict =
      PMF.uniformOfFintype ((i : Finset.univ.erase j₀) → G)) :
    p = eval (sampleAdditiveShares m target) := by
  rw [eval_sampleAdditiveShares_eq_map_completeSharesErase j₀ target, ← herase, PMF.map_comp]
  conv_lhs => rw [← PMF.map_id p]
  refine PMF.map_congr_on_support p _ _ fun s hs => ?_
  exact (completeSharesErase_restrict_erase j₀ (hsum s hs)).symm

end Cslib.ProbComp
