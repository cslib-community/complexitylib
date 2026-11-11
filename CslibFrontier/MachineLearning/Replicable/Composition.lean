/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.BitString.Block
public import CslibFrontier.MachineLearning.Replicable.Basic
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.EventBind
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.ToReal

/-!
# Sample splitting and composition of replicable algorithms

This module provides independent sample splitting for `Probability.PMF.iid` over arbitrary
(possibly infinite) sample spaces and proves composition theorems for shared-seed replicable
algorithms:

* **Sample padding** (`Algorithm.pad`): using only a prefix of a larger sample preserves both the
  marginal output distribution and the disagreement probability.
* **Two-stage adaptive composition** (`Algorithm.seqPair`, `Algorithm.seqBind`): running `A₁` on
  the first `m₁` samples with seed `r₁`, then choosing a second algorithm `run₂ a` from its output
  and running it on `m₂` fresh samples with an independent shared seed `r₂ ~ seed₂`, sums the
  replicability parameters (`ρ₁ + ρ₂`).
* **`k`-fold block composition** (`Algorithm.pi`, `Algorithm.replicate`): running `k` replicable
  algorithms on disjoint blocks of `m` samples with independent shared seeds sums their
  replicability parameters (`∑ j, ρ j`, or `k * ρ` for `replicate`), and its marginal is the
  product/i.i.d. distribution of their marginals.

## Main definitions

* `Cslib.MachineLearning.Replicable.splitSample`: split `m₁ + m₂` samples into two blocks.
* `Cslib.MachineLearning.Replicable.pmfPiFin`: finite-length independent product of `PMF`s without a
  finiteness constraint.
* `Cslib.MachineLearning.Replicable.Algorithm.pad`: pad an algorithm to a larger sample size.
* `Cslib.MachineLearning.Replicable.Algorithm.seqPair`,
  `Cslib.MachineLearning.Replicable.Algorithm.seqBind`: adaptive two-stage composition.
* `Cslib.MachineLearning.Replicable.Algorithm.pi`,
  `Cslib.MachineLearning.Replicable.Algorithm.replicate`: parallel block composition.

## Main results

* `Cslib.MachineLearning.Replicable.iid_map_splitSample`,
  `Cslib.MachineLearning.Replicable.iid_map_block`: independent block decompositions of `iid`.
* `Cslib.MachineLearning.Replicable.IsReplicableFor.pad`,
  `Cslib.MachineLearning.Replicable.IsAccurateFor.pad`: padding invariance.
* `Cslib.MachineLearning.Replicable.IsReplicableFor.seqPair`,
  `Cslib.MachineLearning.Replicable.IsReplicableFor.seqBind`: additive replicability under
  two-stage adaptive composition.
* `Cslib.MachineLearning.Replicable.Algorithm.marginal_replicate`: the marginal of `k` independent
  repetitions is `Probability.PMF.iid (A.marginal D) k`.
* `Cslib.MachineLearning.Replicable.IsReplicableFor.pi`,
  `Cslib.MachineLearning.Replicable.IsReplicableFor.replicate`: additive replicability under
  `k`-fold composition.

## References

* [ImpagliazzoLeiPitassiSorrell2022]
-/

public section

namespace Cslib.MachineLearning.Replicable

open Cslib.Probability
open scoped ENNReal

universe u v w z

section SampleSplitting

variable {X : Type u}

/-- Split a sample of size `m₁ + m₂` into its prefix of size `m₁` and suffix of size `m₂`. -/
@[expose] def splitSample (m₁ m₂ : ℕ) (S : Fin (m₁ + m₂) → X) : (Fin m₁ → X) × (Fin m₂ → X) :=
  (fun i => S (Fin.castAdd m₂ i), fun j => S (Fin.natAdd m₁ j))

/-- Equivalence between a sample of size `m₁ + m₂` and a pair of samples of sizes `m₁`, `m₂`. -/
@[expose] def splitSampleEquiv (m₁ m₂ : ℕ) (X : Type u) :
    (Fin (m₁ + m₂) → X) ≃ (Fin m₁ → X) × (Fin m₂ → X) where
  toFun := splitSample m₁ m₂
  invFun p := Fin.append p.1 p.2
  left_inv S := by
    ext k
    refine Fin.addCases (m := m₁) (n := m₂) (fun i => ?_) (fun j => ?_) k <;>
      simp [splitSample]
  right_inv p := by
    ext i <;> simp [splitSample]

/-- Splitting `m₁ + m₂` i.i.d. draws into two blocks yields two independent i.i.d. draws. -/
theorem iid_map_splitSample (D : PMF X) (m₁ m₂ : ℕ) :
    (Probability.PMF.iid D (m₁ + m₂)).map (splitSample m₁ m₂) =
      (Probability.PMF.iid D m₁).bind fun S₁ =>
        (Probability.PMF.iid D m₂).map fun S₂ => (S₁, S₂) := by
  ext ⟨S₁, S₂⟩
  change ((Probability.PMF.iid D (m₁ + m₂)).map (splitSampleEquiv m₁ m₂ X)) (S₁, S₂) = _
  rw [Probability.PMF.map_equiv_apply, Probability.PMF.iid_apply]
  simp only [splitSampleEquiv, Equiv.coe_fn_symm_mk, Fin.prod_univ_add, Fin.append_left,
    Fin.append_right]
  rw [Probability.PMF.bind_map_prodMk_apply, Probability.PMF.iid_apply, Probability.PMF.iid_apply]

/-- Taking only the first `m` coordinates of `m'` i.i.d. draws (`m ≤ m'`) recovers `iid D m`. -/
theorem iid_map_castLE (D : PMF X) {m m' : ℕ} (h : m ≤ m') :
    (Probability.PMF.iid D m').map (fun S i => S (Fin.castLE h i)) = Probability.PMF.iid D m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have hsub : (fun S : Fin (m + k) → X => fun i => S (Fin.castLE h i)) =
      Prod.fst ∘ splitSample m k := by
    ext S i
    rfl
  rw [hsub, ← PMF.map_comp, iid_map_splitSample, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  change (Probability.PMF.iid D m).bind (fun S₁ => (Probability.PMF.iid D k).map
    (Function.const _ S₁)) = _
  simp only [PMF.map_const, PMF.bind_pure]

/-- Splitting `k * m` i.i.d. draws into `k` blocks of size `m` gives `k` i.i.d. draws of
`iid D m`. -/
theorem iid_map_block (D : PMF X) (k m : ℕ) :
    (Probability.PMF.iid D (k * m)).map (BitString.block (α := X) (m := k) (k := m)) =
      Probability.PMF.iid (Probability.PMF.iid D m) k := by
  ext B
  change ((Probability.PMF.iid D (k * m)).map
    (BitString.blocksEquiv (α := X) (m := k) (k := m))) B = _
  rw [Probability.PMF.map_equiv_apply, Probability.PMF.iid_apply, Probability.PMF.iid_apply]
  have hprod :
      ∏ p : Fin (k * m), D ((BitString.blocksEquiv (α := X) (m := k) (k := m)).symm B p) =
        ∏ jl : Fin k × Fin m, D (B jl.1 jl.2) := by
    refine Fintype.prod_equiv finProdFinEquiv.symm _ _ fun p => ?_
    rfl
  rw [hprod, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Probability.PMF.iid_apply]

end SampleSplitting

/-! ### Finite-length independent products on arbitrary types -/

section PmfPiFin

/-- Independent tuple distribution for a `Fin k`-indexed family of `PMF`s on an arbitrary
(possibly infinite) type `α`. -/
@[expose] noncomputable def pmfPiFin {α : Type w} : {k : ℕ} → (Fin k → PMF α) → PMF (Fin k → α)
  | 0, _ => PMF.pure Fin.elim0
  | _ + 1, p => (p 0).bind fun a => (pmfPiFin fun j => p j.succ).map (Fin.cons a)

theorem pmfPiFin_const {α : Type w} (p : PMF α) :
    ∀ k : ℕ, pmfPiFin (fun _ : Fin k => p) = Probability.PMF.iid p k
  | 0 => rfl
  | k + 1 => by
    simp only [pmfPiFin, Probability.PMF.iid, pmfPiFin_const p k]
    rfl

@[simp] theorem pmfPiFin_apply {α : Type w} :
    ∀ {k : ℕ} (p : Fin k → PMF α) (v : Fin k → α), pmfPiFin p v = ∏ j, p j (v j)
  | 0, p, v => by
    rw [pmfPiFin, Fin.prod_univ_zero, Subsingleton.elim v Fin.elim0, PMF.pure_apply_self]
  | k + 1, p, v => by
    rw [pmfPiFin, PMF.bind_apply, Fin.prod_univ_succ, tsum_eq_single (v 0)]
    · rw [PMF.map_apply, tsum_eq_single (Fin.tail v),
        pmfPiFin_apply (fun j => p j.succ) (Fin.tail v)]
      · simp [Fin.cons_self_tail, Fin.tail]
      · intro w hw
        simp only [ite_eq_right_iff]
        intro h
        exact absurd (by rw [h, Fin.tail_cons]) hw
    · intro a ha
      rw [PMF.map_apply, tsum_eq_zero_iff.mpr, mul_zero]
      intro w
      simp only [ite_eq_right_iff]
      intro h
      exact absurd (by rw [h, Fin.cons_zero]) ha

theorem pmfPiFin_map_eval {α : Type w} :
    ∀ {k : ℕ} (p : Fin k → PMF α) (j : Fin k), (pmfPiFin p).map (fun v => v j) = p j
  | 0, _, j => j.elim0
  | k + 1, p, j => by
    refine Fin.cases ?_ (fun j' => ?_) j
    · simp only [pmfPiFin, PMF.map_bind, PMF.map_comp, Function.comp_def, Fin.cons_zero]
      change (p 0).bind (fun a => (pmfPiFin fun j => p j.succ).map (Function.const _ a)) = p 0
      simp only [PMF.map_const, PMF.bind_pure]
    · simp only [pmfPiFin, PMF.map_bind, PMF.map_comp, Function.comp_def, Fin.cons_succ]
      change (p 0).bind (fun _ => (pmfPiFin fun i => p i.succ).map (fun v => v j')) = p j'.succ
      rw [pmfPiFin_map_eval (fun i => p i.succ) j', PMF.bind_const]

/-- Sequencing a coordinatewise family of kernels across `pmfPiFin` yields `pmfPiFin` of the
bound distributions. -/
theorem pmfPiFin_bind {α : Type w} {γ : Type z} :
    ∀ {k : ℕ} (p : Fin k → PMF α) (K : Fin k → α → PMF γ),
      (pmfPiFin p).bind (fun x => pmfPiFin fun j => K j (x j)) =
        pmfPiFin fun j => (p j).bind (K j)
  | 0, _, _ => by simp only [pmfPiFin, PMF.pure_bind]
  | _ + 1, p, K => by
    rw [pmfPiFin, pmfPiFin, PMF.bind_bind, PMF.bind_bind]
    refine PMF.bind_congr_on_support _ _ _ fun a₀ _ => ?_
    simp only [PMF.bind_map, Function.comp_def, pmfPiFin, Fin.cons_zero, Fin.cons_succ]
    rw [PMF.bind_comm]
    refine PMF.bind_congr_on_support _ _ _ fun b₀ _ => ?_
    rw [← PMF.map_bind, pmfPiFin_bind (fun j => p j.succ) (fun j => K j.succ)]

/-- Independent pairing of two `pmfPiFin` products decomposes as coordinatewise pairing. -/
theorem pmfPiFin_pair {α : Type w} :
    ∀ {k : ℕ} (p q : Fin k → PMF α),
      (pmfPiFin p).bind (fun y₁ => (pmfPiFin q).map fun y₂ => (y₁, y₂)) =
        (pmfPiFin fun j => (p j).bind fun a => (q j).map fun b => (a, b)).map
          (fun v => (fun j => (v j).1, fun j => (v j).2))
  | 0, _, _ => by
    simp only [pmfPiFin, PMF.pure_bind, PMF.pure_map]
    exact congrArg PMF.pure (Prod.ext (funext fun j => j.elim0) (funext fun j => j.elim0))
  | k + 1, p, q => by
    simp only [pmfPiFin, PMF.bind_bind, PMF.map_bind, PMF.bind_map, PMF.map_comp,
      Function.comp_def]
    refine PMF.bind_congr_on_support _ _ _ fun a₀ _ => ?_
    rw [PMF.bind_comm]
    refine PMF.bind_congr_on_support _ _ _ fun b₀ _ => ?_
    have hL :
        (pmfPiFin fun j => p j.succ).bind (fun y₁ =>
          (pmfPiFin fun j => q j.succ).map fun y₂ => (Fin.cons a₀ y₁, Fin.cons b₀ y₂)) =
        ((pmfPiFin fun j => p j.succ).bind fun y₁ =>
          (pmfPiFin fun j => q j.succ).map fun y₂ => (y₁, y₂)).map
          (fun pair : (Fin k → α) × (Fin k → α) =>
            (Fin.cons (α := fun _ => α) a₀ pair.1, Fin.cons (α := fun _ => α) b₀ pair.2)) := by
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
    rw [hL, pmfPiFin_pair (fun j => p j.succ) (fun j => q j.succ), PMF.map_comp]
    refine congrArg (fun f => PMF.map f _) ?_
    funext w
    exact Prod.ext (funext fun j => Fin.cases rfl (fun _ => rfl) j)
      (funext fun j => Fin.cases rfl (fun _ => rfl) j)

/-- Union bound for coordinatewise disagreement under `pmfPiFin` of paired distributions. -/
theorem toOuterMeasure_pmfPiFin_pair_ne {α : Type w} {k : ℕ} (q : Fin k → PMF (α × α)) :
    (pmfPiFin q).toOuterMeasure {v : Fin k → α × α | ∃ j, (v j).1 ≠ (v j).2} ≤
      ∑ j : Fin k, (q j).toOuterMeasure {p : α × α | p.1 ≠ p.2} := by
  have hset : {v : Fin k → α × α | ∃ j, (v j).1 ≠ (v j).2} =
      ⋃ j ∈ (Finset.univ : Finset (Fin k)), {v : Fin k → α × α | (v j).1 ≠ (v j).2} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_univ, exists_true_left]
  rw [hset]
  refine (MeasureTheory.measure_biUnion_finset_le _ _).trans_eq ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← pmfPiFin_map_eval q j, PMF.toOuterMeasure_map_apply]
  rfl

end PmfPiFin

/-! ### Padding, sequential composition, and parallel repetition -/

namespace Algorithm

variable {X : Type u} {Ω : Type v} {α : Type w} {γ : Type z}

/-- Pad an `m`-sample algorithm to `m'` samples (`m ≤ m'`) by reading the first `m` samples. -/
@[expose] noncomputable def pad {m m' : ℕ} (A : Algorithm X Ω α m) (h : m ≤ m') :
    Algorithm X Ω α m' where
  seed := A.seed
  run S r := A.run (fun i => S (Fin.castLE h i)) r

theorem marginal_pad {m m' : ℕ} (A : Algorithm X Ω α m) (h : m ≤ m') (D : PMF X) :
    (A.pad h).marginal D = A.marginal D := by
  rw [marginal_eq_seed_bind, marginal_eq_seed_bind]
  refine PMF.bind_congr_on_support _ _ _ fun r _ => ?_
  dsimp only [pad]
  exact (PMF.bind_map (Probability.PMF.iid D m') (fun S i => S (Fin.castLE h i))
    (fun S => A.run S r)).symm.trans (by rw [iid_map_castLE D h])

theorem disagreeProb_pad {m m' : ℕ} (A : Algorithm X Ω α m) (h : m ≤ m') (D : PMF X) :
    (A.pad h).disagreeProb D = A.disagreeProb D := by
  simp only [disagreeProb]
  refine congrArg
    (fun law : PMF (α × α) => (law.toOuterMeasure {p : α × α | p.1 ≠ p.2}).toReal) ?_
  simp only [pairedOutput, pad]
  refine PMF.bind_congr_on_support _ _ _ fun r _ => ?_
  have h1 :
      (Probability.PMF.iid D m').bind (fun S₁ => (Probability.PMF.iid D m').bind fun S₂ =>
        (A.run (fun i => S₁ (Fin.castLE h i)) r).bind fun y₁ =>
          (A.run (fun i => S₂ (Fin.castLE h i)) r).map fun y₂ => (y₁, y₂)) =
      ((Probability.PMF.iid D m').map (fun S i => S (Fin.castLE h i))).bind fun S₁ =>
        ((Probability.PMF.iid D m').map (fun S i => S (Fin.castLE h i))).bind fun S₂ =>
          (A.run S₁ r).bind fun y₁ => (A.run S₂ r).map fun y₂ => (y₁, y₂) := by
    simp only [PMF.bind_map, Function.comp_def]
  rw [h1, iid_map_castLE D h]

/-- Two-stage adaptive sequential composition outputting both results `(a, b)`:
run `A₁` on the first `m₁` samples with seed `r₁`, then run `run₂ a` on the remaining `m₂`
samples with an independent shared seed `r₂ ~ seed₂`. -/
@[expose] noncomputable def seqPair {Ω₁ Ω₂ : Type*} {m₁ m₂ : ℕ}
    (A₁ : Algorithm X Ω₁ α m₁) (seed₂ : PMF Ω₂)
    (run₂ : α → (Fin m₂ → X) → Ω₂ → PMF γ) :
    Algorithm X (Ω₁ × Ω₂) (α × γ) (m₁ + m₂) where
  seed := A₁.seed.bind fun r₁ => seed₂.map fun r₂ => (r₁, r₂)
  run S r :=
    (A₁.run (splitSample m₁ m₂ S).1 r.1).bind fun a =>
      (run₂ a (splitSample m₁ m₂ S).2 r.2).map fun b => (a, b)

/-- Two-stage adaptive sequential composition returning only the second result `b`. -/
@[expose] noncomputable def seqBind {Ω₁ Ω₂ : Type*} {m₁ m₂ : ℕ}
    (A₁ : Algorithm X Ω₁ α m₁) (seed₂ : PMF Ω₂)
    (run₂ : α → (Fin m₂ → X) → Ω₂ → PMF γ) :
    Algorithm X (Ω₁ × Ω₂) γ (m₁ + m₂) :=
  (A₁.seqPair seed₂ run₂).map Prod.snd

private theorem iid_splitSample_bind {X δ : Type*} (D : PMF X) (m₁ m₂ : ℕ)
    (f : (Fin m₁ → X) × (Fin m₂ → X) → PMF δ) :
    (Probability.PMF.iid D (m₁ + m₂)).bind (fun S => f (splitSample m₁ m₂ S)) =
      (Probability.PMF.iid D m₁).bind fun Spre =>
        (Probability.PMF.iid D m₂).bind fun Ssuf => f (Spre, Ssuf) := by
  calc (Probability.PMF.iid D (m₁ + m₂)).bind (fun S => f (splitSample m₁ m₂ S))
      = ((Probability.PMF.iid D (m₁ + m₂)).map (splitSample m₁ m₂)).bind f :=
        (PMF.bind_map (Probability.PMF.iid D (m₁ + m₂)) (splitSample m₁ m₂) f).symm
    _ = ((Probability.PMF.iid D m₁).bind fun Spre =>
          (Probability.PMF.iid D m₂).map fun Ssuf => (Spre, Ssuf)).bind f := by
        rw [iid_map_splitSample]
    _ = (Probability.PMF.iid D m₁).bind fun Spre =>
          (Probability.PMF.iid D m₂).bind fun Ssuf => f (Spre, Ssuf) := by
        simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]

private theorem bind_comm_two {α β γ δ : Type*} (q : PMF α) (p₁ : PMF β) (p₂ : PMF γ)
    (K : α → β → γ → PMF δ) :
    (q.bind fun a => p₁.bind fun b => p₂.bind fun c => K a b c) =
      p₁.bind fun b => p₂.bind fun c => q.bind fun a => K a b c := by
  rw [PMF.bind_comm]
  exact PMF.bind_congr_on_support _ _ _ fun b _ => PMF.bind_comm q p₂ _

private theorem seqPair_inner_comm {α δ ω σ τ : Type*}
    (seed₂ : PMF ω) (p₁ : PMF σ) (p₂ : PMF τ)
    (q₁ q₂ : σ → PMF α) (K : α → α → τ → τ → ω → PMF δ) :
    (seed₂.bind fun r₂ => p₁.bind fun s₁ => p₂.bind fun t₁ =>
      p₁.bind fun s₂ => p₂.bind fun t₂ =>
        (q₁ s₁).bind fun a₁ => (q₂ s₂).bind fun a₂ => K a₁ a₂ t₁ t₂ r₂) =
      p₁.bind fun s₁ => p₁.bind fun s₂ =>
        (q₁ s₁).bind fun a₁ => (q₂ s₂).bind fun a₂ =>
          seed₂.bind fun r₂ => p₂.bind fun t₁ => p₂.bind fun t₂ => K a₁ a₂ t₁ t₂ r₂ := by
  rw [PMF.bind_comm seed₂ p₁]
  refine PMF.bind_congr_on_support _ _ _ fun s₁ _ => ?_
  have hS₂' (r₂ : ω) (t₁ : τ) (s₂ : σ) :
      (p₂.bind fun t₂ => (q₁ s₁).bind fun a₁ => (q₂ s₂).bind fun a₂ => K a₁ a₂ t₁ t₂ r₂) =
        (q₁ s₁).bind fun a₁ => (q₂ s₂).bind fun a₂ => p₂.bind fun t₂ => K a₁ a₂ t₁ t₂ r₂ :=
    bind_comm_two p₂ (q₁ s₁) (q₂ s₂) (fun t₂ a₁ a₂ => K a₁ a₂ t₁ t₂ r₂)
  have hS₁' (r₂ : ω) :
      (p₂.bind fun t₁ => p₁.bind fun s₂ => p₂.bind fun t₂ =>
        (q₁ s₁).bind fun a₁ => (q₂ s₂).bind fun a₂ => K a₁ a₂ t₁ t₂ r₂) =
        p₁.bind fun s₂ => (q₁ s₁).bind fun a₁ => (q₂ s₂).bind fun a₂ =>
          p₂.bind fun t₁ => p₂.bind fun t₂ => K a₁ a₂ t₁ t₂ r₂ := by
    have hstep1 :
        (p₂.bind fun t₁ => p₁.bind fun s₂ => p₂.bind fun t₂ =>
          (q₁ s₁).bind fun a₁ => (q₂ s₂).bind fun a₂ => K a₁ a₂ t₁ t₂ r₂) =
          p₂.bind fun t₁ => p₁.bind fun s₂ => (q₁ s₁).bind fun a₁ => (q₂ s₂).bind fun a₂ =>
            p₂.bind fun t₂ => K a₁ a₂ t₁ t₂ r₂ :=
      PMF.bind_congr_on_support _ _ _ fun t₁ _ =>
        PMF.bind_congr_on_support _ _ _ fun s₂ _ => hS₂' r₂ t₁ s₂
    rw [hstep1, PMF.bind_comm p₂ p₁]
    refine PMF.bind_congr_on_support _ _ _ fun s₂ _ => ?_
    exact bind_comm_two p₂ (q₁ s₁) (q₂ s₂)
      (fun t₁ a₁ a₂ => p₂.bind fun t₂ => K a₁ a₂ t₁ t₂ r₂)
  have hr₂ := PMF.bind_congr_on_support seed₂ _ _ fun r₂ _ => hS₁' r₂
  rw [hr₂, PMF.bind_comm seed₂ p₁]
  refine PMF.bind_congr_on_support _ _ _ fun s₂ _ => ?_
  exact bind_comm_two seed₂ (q₁ s₁) (q₂ s₂)
    (fun r₂ a₁ a₂ => p₂.bind fun t₁ => p₂.bind fun t₂ => K a₁ a₂ t₁ t₂ r₂)

private theorem pairedOutput_seqPair {Ω₁ Ω₂ : Type*} {m₁ m₂ : ℕ}
    (A₁ : Algorithm X Ω₁ α m₁) (seed₂ : PMF Ω₂)
    (run₂ : α → (Fin m₂ → X) → Ω₂ → PMF γ) (D : PMF X) :
    (A₁.seqPair seed₂ run₂).pairedOutput D =
      (A₁.pairedOutput D).bind fun aa =>
        seed₂.bind fun r₂ =>
          (Probability.PMF.iid D m₂).bind fun S₁' =>
            (Probability.PMF.iid D m₂).bind fun S₂' =>
              (run₂ aa.1 S₁' r₂).bind fun b₁ =>
                (run₂ aa.2 S₂' r₂).map fun b₂ => ((aa.1, b₁), (aa.2, b₂)) := by
  simp only [pairedOutput, seqPair, PMF.bind_bind, PMF.bind_map, PMF.map_bind, PMF.map_comp,
    Function.comp_def]
  refine PMF.bind_congr_on_support _ _ _ fun r₁ _ => ?_
  have h1 :
      (seed₂.bind fun r₂ =>
        (Probability.PMF.iid D (m₁ + m₂)).bind fun S₁ =>
          (Probability.PMF.iid D (m₁ + m₂)).bind fun S₂ =>
            (A₁.run (splitSample m₁ m₂ S₁).1 r₁).bind fun a₁ =>
              (run₂ a₁ (splitSample m₁ m₂ S₁).2 r₂).bind fun b₁ =>
                (A₁.run (splitSample m₁ m₂ S₂).1 r₁).bind fun a₂ =>
                  (run₂ a₂ (splitSample m₁ m₂ S₂).2 r₂).map fun b₂ => ((a₁, b₁), (a₂, b₂))) =
      seed₂.bind fun r₂ =>
        (Probability.PMF.iid D m₁).bind fun S₁pre =>
          (Probability.PMF.iid D m₂).bind fun S₁' =>
            (Probability.PMF.iid D m₁).bind fun S₂pre =>
              (Probability.PMF.iid D m₂).bind fun S₂' =>
                (A₁.run S₁pre r₁).bind fun a₁ =>
                  (A₁.run S₂pre r₁).bind fun a₂ =>
                    (run₂ a₁ S₁' r₂).bind fun b₁ =>
                      (run₂ a₂ S₂' r₂).map fun b₂ => ((a₁, b₁), (a₂, b₂)) := by
    refine PMF.bind_congr_on_support _ _ _ fun r₂ _ => ?_
    rw [iid_splitSample_bind D m₁ m₂ (fun p =>
      (Probability.PMF.iid D (m₁ + m₂)).bind fun S₂ =>
        (A₁.run p.1 r₁).bind fun a₁ =>
          (run₂ a₁ p.2 r₂).bind fun b₁ =>
            (A₁.run (splitSample m₁ m₂ S₂).1 r₁).bind fun a₂ =>
              (run₂ a₂ (splitSample m₁ m₂ S₂).2 r₂).map fun b₂ => ((a₁, b₁), (a₂, b₂)))]
    refine PMF.bind_congr_on_support _ _ _ fun S₁pre _ =>
      PMF.bind_congr_on_support _ _ _ fun S₁' _ => ?_
    rw [iid_splitSample_bind D m₁ m₂ (fun p =>
      (A₁.run S₁pre r₁).bind fun a₁ =>
        (run₂ a₁ S₁' r₂).bind fun b₁ =>
          (A₁.run p.1 r₁).bind fun a₂ =>
            (run₂ a₂ p.2 r₂).map fun b₂ => ((a₁, b₁), (a₂, b₂)))]
    refine PMF.bind_congr_on_support _ _ _ fun S₂pre _ =>
      PMF.bind_congr_on_support _ _ _ fun S₂' _ => ?_
    refine PMF.bind_congr_on_support _ _ _ fun a₁ _ => ?_
    exact PMF.bind_comm (run₂ a₁ S₁' r₂) (A₁.run S₂pre r₁) _
  rw [h1]
  exact seqPair_inner_comm seed₂ (Probability.PMF.iid D m₁) (Probability.PMF.iid D m₂)
    (fun S => A₁.run S r₁) (fun S => A₁.run S r₁)
    (fun a₁ a₂ S₁' S₂' r₂ =>
      (run₂ a₁ S₁' r₂).bind fun b₁ =>
        (run₂ a₂ S₂' r₂).map fun b₂ => ((a₁, b₁), (a₂, b₂)))

theorem disagreeProb_seqPair_le {Ω₁ Ω₂ : Type*} {m₁ m₂ : ℕ}
    (A₁ : Algorithm X Ω₁ α m₁) (seed₂ : PMF Ω₂)
    (run₂ : α → (Fin m₂ → X) → Ω₂ → PMF γ) (D : PMF X) {ρ₂ : ℝ} (hρ₂ : 0 ≤ ρ₂)
    (h₂ : ∀ a, (Algorithm.mk seed₂ (run₂ a)).disagreeProb D ≤ ρ₂) :
    (A₁.seqPair seed₂ run₂).disagreeProb D ≤ A₁.disagreeProb D + ρ₂ := by
  rw [disagreeProb, pairedOutput_seqPair]
  refine (Probability.PMF.toOuterMeasure_bind_failure_toReal_le _ _ {aa | aa.1 = aa.2}
    {p : (α × γ) × (α × γ) | p.1 ≠ p.2} hρ₂ ?_).trans ?_
  · rintro ⟨a₁, a₂⟩ _ (rfl : a₁ = a₂)
    have hmap :
        (seed₂.bind fun r₂ => (Probability.PMF.iid D m₂).bind fun S₁' =>
          (Probability.PMF.iid D m₂).bind fun S₂' =>
            (run₂ a₁ S₁' r₂).bind fun b₁ =>
              (run₂ a₁ S₂' r₂).map fun b₂ => ((a₁, b₁), (a₁, b₂))) =
        ((Algorithm.mk seed₂ (run₂ a₁)).pairedOutput D).map
          (fun bb => ((a₁, bb.1), (a₁, bb.2))) := by
      simp only [pairedOutput, PMF.map_bind, PMF.map_comp, Function.comp_def]
    rw [hmap, PMF.toOuterMeasure_map_apply]
    have hpre : (fun bb : γ × γ => ((a₁, bb.1), (a₁, bb.2))) ⁻¹'
        {p : (α × γ) × (α × γ) | p.1 ≠ p.2} = {bb : γ × γ | bb.1 ≠ bb.2} := by
      ext ⟨b₁, b₂⟩
      simp
    rw [hpre]
    exact h₂ a₁
  · simp only [Set.compl_ofPred, disagreeProb]
    exact le_rfl

/-- Parallel `k`-fold block composition of `A : Fin k → Algorithm X Ω α m` on `k * m` samples
and `k` independent shared seeds. -/
@[expose] noncomputable def pi {k m : ℕ} (A : Fin k → Algorithm X Ω α m) :
    Algorithm X (Fin k → Ω) (Fin k → α) (k * m) where
  seed := pmfPiFin fun j => (A j).seed
  run S r := pmfPiFin fun j => (A j).run (BitString.block (m := k) (k := m) S j) (r j)

/-- Running the same algorithm `A` on `k` disjoint blocks of `m` samples with `k` independent
shared seeds. -/
@[expose] noncomputable def replicate {m : ℕ} (A : Algorithm X Ω α m) (k : ℕ) :
    Algorithm X (Fin k → Ω) (Fin k → α) (k * m) :=
  pi fun _ => A

theorem marginal_pi {k m : ℕ} (A : Fin k → Algorithm X Ω α m) (D : PMF X) :
    (pi A).marginal D = pmfPiFin fun j => (A j).marginal D := by
  rw [marginal_eq_seed_bind]
  simp only [pi]
  have hblocks (r : Fin k → Ω) :
      (Probability.PMF.iid D (k * m)).bind
        (fun S => pmfPiFin fun j => (A j).run (BitString.block (m := k) (k := m) S j) (r j)) =
      pmfPiFin fun j => (Probability.PMF.iid D m).bind fun S => (A j).run S (r j) := by
    have hm := (PMF.bind_map (Probability.PMF.iid D (k * m))
      (BitString.block (α := X) (m := k) (k := m))
      (fun B => pmfPiFin fun j => (A j).run (B j) (r j))).symm
    dsimp only [Function.comp_def] at hm
    rw [hm, iid_map_block, ← pmfPiFin_const]
    exact pmfPiFin_bind (fun _ : Fin k => Probability.PMF.iid D m)
      (fun j S => (A j).run S (r j))
  simp_rw [hblocks]
  rw [pmfPiFin_bind (fun j => (A j).seed)
    (fun j rj => (Probability.PMF.iid D m).bind fun S => (A j).run S rj)]
  refine congrArg pmfPiFin (funext fun j => ?_)
  exact (marginal_eq_seed_bind (A j) D).symm

theorem marginal_replicate {k m : ℕ} (A : Algorithm X Ω α m) (D : PMF X) :
    (replicate A k).marginal D = Probability.PMF.iid (A.marginal D) k := by
  rw [replicate, marginal_pi, pmfPiFin_const]

theorem pairedOutput_pi {k m : ℕ} (A : Fin k → Algorithm X Ω α m) (D : PMF X) :
    (pi A).pairedOutput D =
      (pmfPiFin fun j => (A j).pairedOutput D).map
        (fun v => (fun j => (v j).1, fun j => (v j).2)) := by
  have hsplit (f : (Fin k → Fin m → X) → PMF ((Fin k → α) × (Fin k → α))) :
      (Probability.PMF.iid D (k * m)).bind
        (fun S => f (BitString.block (α := X) (m := k) (k := m) S)) =
        (pmfPiFin fun _ : Fin k => Probability.PMF.iid D m).bind f := by
    have hm := (PMF.bind_map (Probability.PMF.iid D (k * m))
      (BitString.block (α := X) (m := k) (k := m)) f).symm
    dsimp only [Function.comp_def] at hm
    rw [hm, iid_map_block, pmfPiFin_const]
  simp only [pairedOutput, pi]
  calc (pmfPiFin fun j => (A j).seed).bind (fun rs =>
        (Probability.PMF.iid D (k * m)).bind fun S₁ =>
          (Probability.PMF.iid D (k * m)).bind fun S₂ =>
            (pmfPiFin fun j =>
                (A j).run (BitString.block (m := k) (k := m) S₁ j) (rs j)).bind fun y₁ =>
              (pmfPiFin fun j =>
                (A j).run (BitString.block (m := k) (k := m) S₂ j) (rs j)).map fun y₂ => (y₁, y₂))
      = (pmfPiFin fun j => (A j).seed).bind (fun rs =>
          (pmfPiFin fun _ : Fin k => Probability.PMF.iid D m).bind fun B₁ =>
            (pmfPiFin fun _ : Fin k => Probability.PMF.iid D m).bind fun B₂ =>
              (pmfPiFin fun j =>
                ((A j).run (B₁ j) (rs j)).bind fun a =>
                  ((A j).run (B₂ j) (rs j)).map fun b => (a, b)).map
                (fun v => (fun j => (v j).1, fun j => (v j).2))) := by
        refine PMF.bind_congr_on_support _ _ _ fun rs _ => ?_
        rw [hsplit (fun B₁ =>
          (Probability.PMF.iid D (k * m)).bind fun S₂ =>
            (pmfPiFin fun j => (A j).run (B₁ j) (rs j)).bind fun y₁ =>
              (pmfPiFin fun j =>
                (A j).run (BitString.block (m := k) (k := m) S₂ j) (rs j)).map fun y₂ =>
                  (y₁, y₂))]
        refine PMF.bind_congr_on_support _ _ _ fun B₁ _ => ?_
        rw [hsplit (fun B₂ =>
          (pmfPiFin fun j => (A j).run (B₁ j) (rs j)).bind fun y₁ =>
            (pmfPiFin fun j => (A j).run (B₂ j) (rs j)).map fun y₂ => (y₁, y₂))]
        refine PMF.bind_congr_on_support _ _ _ fun B₂ _ => ?_
        exact pmfPiFin_pair (fun j => (A j).run (B₁ j) (rs j))
          (fun j => (A j).run (B₂ j) (rs j))
    _ = ((pmfPiFin fun j => (A j).seed).bind (fun rs =>
          (pmfPiFin fun _ : Fin k => Probability.PMF.iid D m).bind fun B₁ =>
            (pmfPiFin fun _ : Fin k => Probability.PMF.iid D m).bind fun B₂ =>
              pmfPiFin fun j =>
                ((A j).run (B₁ j) (rs j)).bind fun a =>
                  ((A j).run (B₂ j) (rs j)).map fun b => (a, b))).map
          (fun v => (fun j => (v j).1, fun j => (v j).2)) := by
        simp only [← PMF.map_bind]
    _ = (pmfPiFin fun j => (A j).pairedOutput D).map
          (fun v => (fun j => (v j).1, fun j => (v j).2)) := by
        refine congrArg (PMF.map _) ?_
        have hB₂ (rs : Fin k → Ω) (B₁ : Fin k → Fin m → X) :
            ((pmfPiFin fun _ : Fin k => Probability.PMF.iid D m).bind fun B₂ =>
              pmfPiFin fun j =>
                ((A j).run (B₁ j) (rs j)).bind fun a =>
                  ((A j).run (B₂ j) (rs j)).map fun b => (a, b)) =
            pmfPiFin fun j =>
              (Probability.PMF.iid D m).bind fun S₂ =>
                ((A j).run (B₁ j) (rs j)).bind fun a =>
                  ((A j).run S₂ (rs j)).map fun b => (a, b) :=
          pmfPiFin_bind (fun _ : Fin k => Probability.PMF.iid D m) (fun j S₂ =>
            ((A j).run (B₁ j) (rs j)).bind fun a => ((A j).run S₂ (rs j)).map fun b => (a, b))
        simp_rw [hB₂]
        have hB₁ (rs : Fin k → Ω) :
            ((pmfPiFin fun _ : Fin k => Probability.PMF.iid D m).bind fun B₁ =>
              pmfPiFin fun j =>
                (Probability.PMF.iid D m).bind fun S₂ =>
                  ((A j).run (B₁ j) (rs j)).bind fun a =>
                    ((A j).run S₂ (rs j)).map fun b => (a, b)) =
            pmfPiFin fun j =>
              (Probability.PMF.iid D m).bind fun S₁ =>
                (Probability.PMF.iid D m).bind fun S₂ =>
                  ((A j).run S₁ (rs j)).bind fun a =>
                    ((A j).run S₂ (rs j)).map fun b => (a, b) :=
          pmfPiFin_bind (fun _ : Fin k => Probability.PMF.iid D m) (fun j S₁ =>
            (Probability.PMF.iid D m).bind fun S₂ =>
              ((A j).run S₁ (rs j)).bind fun a => ((A j).run S₂ (rs j)).map fun b => (a, b))
        simp_rw [hB₁]
        exact pmfPiFin_bind (fun j => (A j).seed) (fun j rj =>
          (Probability.PMF.iid D m).bind fun S₁ =>
            (Probability.PMF.iid D m).bind fun S₂ =>
              ((A j).run S₁ rj).bind fun a =>
                ((A j).run S₂ rj).map fun b => (a, b))

theorem disagreeProb_pi_le {k m : ℕ} (A : Fin k → Algorithm X Ω α m) (D : PMF X) :
    (pi A).disagreeProb D ≤ ∑ j : Fin k, (A j).disagreeProb D := by
  rw [disagreeProb, pairedOutput_pi, PMF.toOuterMeasure_map_apply]
  have hpre : (fun v : Fin k → α × α => (fun j => (v j).1, fun j => (v j).2)) ⁻¹'
      {p | p.1 ≠ p.2} = {v : Fin k → α × α | ∃ j, (v j).1 ≠ (v j).2} := by
    ext v
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, ne_eq, funext_iff, not_forall]
  rw [hpre]
  calc ((pmfPiFin fun j => (A j).pairedOutput D).toOuterMeasure
        {v : Fin k → α × α | ∃ j, (v j).1 ≠ (v j).2}).toReal
      ≤ (∑ j : Fin k,
          ((A j).pairedOutput D).toOuterMeasure {p : α × α | p.1 ≠ p.2}).toReal :=
        ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun j _ =>
          Probability.PMF.toOuterMeasure_ne_top _ _) (toOuterMeasure_pmfPiFin_pair_ne _)
    _ = ∑ j : Fin k, (A j).disagreeProb D := by
        rw [ENNReal.toReal_sum fun j _ => Probability.PMF.toOuterMeasure_ne_top _ _]
        rfl

theorem disagreeProb_replicate_le {k m : ℕ} (A : Algorithm X Ω α m) (D : PMF X) :
    (replicate A k).disagreeProb D ≤ k * A.disagreeProb D := by
  have h := disagreeProb_pi_le (fun _ : Fin k => A) D
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  exact h

end Algorithm

section Closure

variable {X : Type u} {Ω : Type v} {α : Type w} {γ : Type z}

theorem IsReplicableFor.pad {m m' : ℕ} {A : Algorithm X Ω α m} {𝒟 : Set (PMF X)} {ρ : ℝ}
    (h : IsReplicableFor A 𝒟 ρ) (hm : m ≤ m') :
    IsReplicableFor (A.pad hm) 𝒟 ρ := fun D hD => by
  rw [Algorithm.disagreeProb_pad]
  exact h D hD

theorem IsAccurateFor.pad {m m' : ℕ} {A : Algorithm X Ω α m} {𝒟 : Set (PMF X)}
    {good : PMF X → Set α} {β : ℝ} (h : IsAccurateFor A 𝒟 good β) (hm : m ≤ m') :
    IsAccurateFor (A.pad hm) 𝒟 good β := fun D hD => by
  rw [Algorithm.marginal_pad]
  exact h D hD

theorem IsReplicableFor.seqPair {Ω₁ Ω₂ : Type*} {m₁ m₂ : ℕ}
    {A₁ : Algorithm X Ω₁ α m₁} {seed₂ : PMF Ω₂} {run₂ : α → (Fin m₂ → X) → Ω₂ → PMF γ}
    {𝒟 : Set (PMF X)} {ρ₁ ρ₂ : ℝ} (h₁ : IsReplicableFor A₁ 𝒟 ρ₁) (hρ₂ : 0 ≤ ρ₂)
    (h₂ : ∀ a, IsReplicableFor (Algorithm.mk seed₂ (run₂ a)) 𝒟 ρ₂) :
    IsReplicableFor (A₁.seqPair seed₂ run₂) 𝒟 (ρ₁ + ρ₂) := fun D hD =>
  (Algorithm.disagreeProb_seqPair_le A₁ seed₂ run₂ D hρ₂ fun a => h₂ a D hD).trans
    (add_le_add (h₁ D hD) le_rfl)

theorem IsReplicableFor.seqBind {Ω₁ Ω₂ : Type*} {m₁ m₂ : ℕ}
    {A₁ : Algorithm X Ω₁ α m₁} {seed₂ : PMF Ω₂} {run₂ : α → (Fin m₂ → X) → Ω₂ → PMF γ}
    {𝒟 : Set (PMF X)} {ρ₁ ρ₂ : ℝ} (h₁ : IsReplicableFor A₁ 𝒟 ρ₁) (hρ₂ : 0 ≤ ρ₂)
    (h₂ : ∀ a, IsReplicableFor (Algorithm.mk seed₂ (run₂ a)) 𝒟 ρ₂) :
    IsReplicableFor (A₁.seqBind seed₂ run₂) 𝒟 (ρ₁ + ρ₂) :=
  (IsReplicableFor.seqPair h₁ hρ₂ h₂).map Prod.snd

theorem IsReplicableFor.pi {k m : ℕ} {A : Fin k → Algorithm X Ω α m} {𝒟 : Set (PMF X)}
    {ρ : Fin k → ℝ} (h : ∀ j, IsReplicableFor (A j) 𝒟 (ρ j)) :
    IsReplicableFor (Algorithm.pi A) 𝒟 (∑ j, ρ j) := fun D hD =>
  (Algorithm.disagreeProb_pi_le A D).trans (Finset.sum_le_sum fun j _ => h j D hD)

theorem IsReplicableFor.replicate {k m : ℕ} {A : Algorithm X Ω α m} {𝒟 : Set (PMF X)} {ρ : ℝ}
    (h : IsReplicableFor A 𝒟 ρ) :
    IsReplicableFor (A.replicate k) 𝒟 (k * ρ) := fun D hD =>
  (Algorithm.disagreeProb_replicate_le A D).trans
    (mul_le_mul_of_nonneg_left (h D hD) (Nat.cast_nonneg k))

end Closure

end Cslib.MachineLearning.Replicable
