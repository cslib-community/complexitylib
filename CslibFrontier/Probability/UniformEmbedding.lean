/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.MarkovChain.Mixing
public import CslibFrontier.Probability.StatisticalDistance.ClosedForm
public import Mathlib.Data.Fintype.CardEmbedding
import CslibFrontier.Foundations.Data.Nat.Choose
import CslibFrontier.Foundations.Data.Nat.DescFactorial
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Logic.Embedding.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform random embeddings, collision distance, and random-permutation kernels

General finite-domain probability bounds for uniform random injections `T ↪ α`, uniform product
functions, and coordinatewise random-permutation Markov kernels:

1. **Stationarity and `t`-round contraction of random-permutation tuple kernels**: Applying a
   random permutation `π ← ρ` coordinatewise via `(Equiv.refl T).embeddingCongr π` defines a Markov
   kernel `permTupleKernel ρ` on `T ↪ α` whose stationary law is `PMF.uniformOfFintype (T ↪ α)`
   (`isStationary_permTupleKernel`). Composing `t ≥ 1` independent random permutations within `δ`
   of uniform on `T ↪ α` contracts statistical distance to at most `(1 / 2) * (2 * δ) ^ t`
   (`dist_permTupleKernel_composePermDist_le`, [ArbitmanNaorSegev2010], Section 5.3, Theorem 5.6).
2. **Negative correlation and collision distance of uniform embeddings**: Under
   `e ← PMF.uniformOfFintype (T ↪ α)`, hitting a shared target set `Q : Finset α` on every
   coordinate has probability at most `(#Q / |α|) ^ |T|`
   (`prob_uniformOfFintype_embedding_forall_mem_le`,
   [BenderFarachColtonKuszmaulKuszmaulLiu2022], Section 5.3), hitting per-coordinate target sets
   `Q i` when `2 * |T| ^ 2 ≤ |α|` has probability at most `2 * ∏ i, (#(Q i) / |α|)`
   (`prob_uniformOfFintype_embedding_forall_mem_perKey_le`), and forgetting injectivity into
   `T → α` is within `|T| * (|T| - 1) / (2 * |α|)` of `PMF.uniformOfFintype (T → α)`
   (`dist_uniform_embedding_to_fun`).

## Main definitions

* `Cslib.Probability.permTupleKernel`: Markov kernel on `T ↪ α` induced by `ρ : PMF (Equiv.Perm α)`.
* `Cslib.Probability.composePermDist`: left-to-right composition of `t` independent random
  permutations.

## Main results

* `Cslib.Probability.isStationary_permTupleKernel`,
  `Cslib.Probability.dist_permTupleKernel_composePermDist_le`: stationarity of uniform embeddings
  and `(1 / 2) * (2 * δ) ^ t` contraction.
* `Cslib.Probability.prob_uniformOfFintype_embedding_forall_mem_le`,
  `Cslib.Probability.prob_uniformOfFintype_embedding_forall_mem_perKey_le`,
  `Cslib.Probability.prob_not_injective_uniform_le`,
  `Cslib.Probability.dist_uniform_embedding_to_fun`,
  `Cslib.Probability.prob_uniformOfFintype_pi_prod_forall_mem`: without-replacement tail bounds,
  collision probability, embedding-vs-function statistical distance, and uniform product-set
  probability.

## References

* [Y. Arbitman, M. Naor and G. Segev, *Backyard Cuckoo Hashing: Constant Worst-Case Operations
  with a Succinct Representation*][ArbitmanNaorSegev2010]
* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul and M. Liu, *On the Optimal
  Time/Space Tradeoff for Hash Tables*][BenderFarachColtonKuszmaulKuszmaulLiu2022]
-/

public section

namespace Cslib.Probability

open Cslib.Probability.PMF Finset Fintype
open scoped BigOperators ENNReal Cslib.Probability.PMF

/-! ## Section 1: Random-permutation kernels on `T ↪ α` and `t`-round contraction -/

/-- Markov kernel on `T ↪ α` induced by applying `π ← ρ` coordinatewise via
`(Equiv.refl T).embeddingCongr π`. -/
noncomputable def permTupleKernel {T α : Type*} (ρ : PMF (Equiv.Perm α)) (x : T ↪ α) :
    PMF (T ↪ α) :=
  ρ.map fun π => (Equiv.refl T).embeddingCongr π x

theorem permTupleKernel_eq {T α : Type*} (ρ : PMF (Equiv.Perm α)) (x : T ↪ α) :
    permTupleKernel ρ x = ρ.map fun π => (Equiv.refl T).embeddingCongr π x := by
  unfold permTupleKernel; rfl

/-- The uniform distribution on `T ↪ α` is stationary under `permTupleKernel ρ` for every
`ρ : PMF (Equiv.Perm α)`. -/
theorem isStationary_permTupleKernel {T α : Type*} [Fintype T] [Fintype α]
    [Nonempty (T ↪ α)] (ρ : PMF (Equiv.Perm α)) :
    (MarkovChain.mk (permTupleKernel (T := T) ρ)).IsStationary
      (PMF.uniformOfFintype (T ↪ α)) := by
  have hmap (x : T ↪ α) :
      (ρ.map fun π => (Equiv.refl T).embeddingCongr π x) =
        ρ.bind (fun π => PMF.pure ((Equiv.refl T).embeddingCongr π x)) :=
    (PMF.bind_pure_comp _ ρ).symm
  change (PMF.uniformOfFintype (T ↪ α)).bind
    (fun x => ρ.map fun π => (Equiv.refl T).embeddingCongr π x) = _
  simp_rw [hmap]
  rw [PMF.bind_comm]
  have hinner (π : Equiv.Perm α) :
      (PMF.uniformOfFintype (T ↪ α)).bind
        (fun x => PMF.pure ((Equiv.refl T).embeddingCongr π x)) =
        PMF.uniformOfFintype (T ↪ α) :=
    (PMF.bind_pure_comp (⇑((Equiv.refl T).embeddingCongr π)) _).trans
      (PMF.uniformOfFintype_map_equiv _)
  simp_rw [hinner]
  exact PMF.bind_const ρ _

/-- Left-to-right composition `π₀.trans (π₁.trans ⋯)` of `t` independent random permutations. -/
noncomputable def composePermDist {α : Type*} :
    (t : ℕ) → (Fin t → PMF (Equiv.Perm α)) → PMF (Equiv.Perm α)
  | 0, _ => PMF.pure (Equiv.refl α)
  | t + 1, ρs =>
    (composePermDist t (fun i => ρs i.castSucc)).bind fun π₁ =>
      (ρs (Fin.last t)).map fun π₂ => π₁.trans π₂

@[simp] theorem composePermDist_zero {α : Type*} (ρs : Fin 0 → PMF (Equiv.Perm α)) :
    composePermDist 0 ρs = PMF.pure (Equiv.refl α) := by
  unfold composePermDist; rfl

@[simp] theorem composePermDist_succ {α : Type*} (t : ℕ)
    (ρs : Fin (t + 1) → PMF (Equiv.Perm α)) :
    composePermDist (t + 1) ρs =
      (composePermDist t (fun i => ρs i.castSucc)).bind fun π₁ =>
        (ρs (Fin.last t)).map fun π₂ => π₁.trans π₂ := by
  conv_lhs => unfold composePermDist

theorem permTupleKernel_composePermDist_succ {T α : Type*} (t : ℕ)
    (ρs : Fin (t + 1) → PMF (Equiv.Perm α)) (x : T ↪ α) :
    permTupleKernel (composePermDist (t + 1) ρs) x =
      (permTupleKernel (composePermDist t (fun i => ρs i.castSucc)) x).bind
        (permTupleKernel (ρs (Fin.last t))) := by
  unfold permTupleKernel
  simp only [composePermDist, PMF.map_bind, PMF.bind_map]
  refine congrArg ((composePermDist t (fun i => ρs i.castSucc)).bind ·) (funext fun π₁ => ?_)
  simp only [PMF.map_comp, Function.comp_def]
  exact congrArg (ρs (Fin.last t)).map (funext fun π₂ => by ext i; simp)

private theorem permTupleKernel_composePermDist_eq_prod_ofFn {T α : Type*} :
    ∀ (t : ℕ) (ρs : Fin t → PMF (Equiv.Perm α)),
      MarkovChain.mk (permTupleKernel (T := T) (composePermDist t ρs)) =
        (List.ofFn fun i => MarkovChain.mk (permTupleKernel (T := T) (ρs i))).prod
  | 0, ρs => by
    ext1 x
    simp only [permTupleKernel_eq, composePermDist_zero, PMF.pure_map, List.ofFn_zero,
      List.prod_nil, MarkovChain.one_apply, Equiv.embeddingCongr_refl, Equiv.refl_apply]
  | t + 1, ρs => by
    have hsnoc :
        (List.ofFn fun i : Fin (t + 1) => MarkovChain.mk (permTupleKernel (T := T) (ρs i))) =
          (List.ofFn fun i : Fin t =>
              MarkovChain.mk (permTupleKernel (T := T) (ρs i.castSucc))) ++
            [MarkovChain.mk (permTupleKernel (T := T) (ρs (Fin.last t)))] := by
      rw [List.ofFn_succ', List.concat_eq_append]
    rw [hsnoc, List.prod_append, List.prod_singleton,
      ← permTupleKernel_composePermDist_eq_prod_ofFn t (fun i => ρs i.castSucc)]
    ext1 x
    exact permTupleKernel_composePermDist_succ t ρs x

/-- **`t`-round stationary statistical-distance contraction** ([ArbitmanNaorSegev2010],
`arXiv:0912.5424v3`, Section 5.3, Theorem 5.6, PDF p. 25 / printed p. 24): composing `t ≥ 1`
independent random permutations, each within statistical distance `δ` of uniform on `T ↪ α`,
yields a random permutation within `(1 / 2) * (2 * δ) ^ t` of uniform on `T ↪ α`. -/
theorem dist_permTupleKernel_composePermDist_le {T α : Type*}
    [Fintype T] [Fintype α] [Nonempty (T ↪ α)]
    {t : ℕ} (ht : 1 ≤ t) (ρs : Fin t → PMF (Equiv.Perm α)) {δ : ℝ}
    (hδ : ∀ (i : Fin t) (x : T ↪ α),
      dist (permTupleKernel (ρs i) x) (PMF.uniformOfFintype (T ↪ α)) ≤ δ)
    (x : T ↪ α) :
    dist (permTupleKernel (composePermDist t ρs) x) (PMF.uniformOfFintype (T ↪ α)) ≤
      (1 / 2 : ℝ) * (2 * δ) ^ t := by
  have heq := congrArg (fun M : MarkovChain (T ↪ α) => M x)
    (permTupleKernel_composePermDist_eq_prod_ofFn t ρs)
  dsimp only at heq
  rw [heq]
  exact MarkovChain.dist_prod_ofFn_le ht
    (fun i => MarkovChain.mk (permTupleKernel (ρs i)))
    (fun i => isStationary_permTupleKernel (ρs i)) hδ x

/-! ## Section 2: Without-replacement negative correlation, collisions, and product sets -/

/-- **Without-replacement multiplicative upper bound**
([BenderFarachColtonKuszmaulKuszmaulLiu2022], `arXiv:2111.00602v2`, Section 5.3, PDF p. 36 /
printed p. 35): for a uniform random injection `e ← PMF.uniformOfFintype (T ↪ α)`
(`Fintype.card T ≤ Fintype.card α`, `Nonempty α`) and any target set `Q : Finset α`, the
probability that `e i ∈ Q` for all `i : T` is at most `(#Q / |α|) ^ |T|`. -/
theorem prob_uniformOfFintype_embedding_forall_mem_le {T α : Type*}
    [Fintype T] [Fintype α] [Nonempty α]
    (hT : Fintype.card T ≤ Fintype.card α) (Q : Finset α) :
    haveI : Nonempty (T ↪ α) := Function.Embedding.nonempty_of_card_le hT
    ((PMF.uniformOfFintype (T ↪ α)).toOuterMeasure {e : T ↪ α | ∀ i : T, e i ∈ Q}).toReal ≤
      ((#Q : ℝ) / (Fintype.card α : ℝ)) ^ Fintype.card T := by
  classical
  have : Nonempty (T ↪ α) := Function.Embedding.nonempty_of_card_le hT
  let E : Set (T ↪ α) := {e : T ↪ α | ∀ i : T, e i ∈ Q}
  let toSub : {e : T ↪ α // e ∈ E} ↪ (T ↪ Q) :=
    { toFun := fun ⟨e, he⟩ =>
        ⟨fun i => ⟨e i, he i⟩, fun i j h => e.injective (congrArg Subtype.val h)⟩
      inj' := fun ⟨_, _⟩ ⟨_, _⟩ h =>
        Subtype.ext (DFunLike.ext _ _ fun i => congrArg Subtype.val (DFunLike.congr_fun h i)) }
  have hcard_good : #(univ.filter (· ∈ E)) ≤ (#Q).descFactorial (Fintype.card T) := by
    calc #(univ.filter (· ∈ E))
        = Fintype.card {e : T ↪ α // e ∈ E} := (Fintype.card_subtype _).symm
      _ ≤ Fintype.card (T ↪ Q) := Fintype.card_le_of_injective toSub toSub.injective
      _ = (#Q).descFactorial (Fintype.card T) := by rw [Fintype.card_embedding_eq, Fintype.card_coe]
  change ((PMF.uniformOfFintype (T ↪ α)).toOuterMeasure E).toReal ≤ _
  rw [toOuterMeasure_uniformOfFintype_toReal]
  have hcard_emb : Fintype.card (T ↪ α) = (Fintype.card α).descFactorial (Fintype.card T) :=
    Fintype.card_embedding_eq
  have hdesc_pos : 0 < (Fintype.card α).descFactorial (Fintype.card T) :=
    hcard_emb ▸ Fintype.card_pos
  have hα_pos : (0 : ℝ) < (Fintype.card α : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  rw [hcard_emb, div_pow, div_le_div_iff₀ (Nat.cast_pos.mpr hdesc_pos) (pow_pos hα_pos _)]
  have hnat :
      #(univ.filter (· ∈ E)) * Fintype.card α ^ Fintype.card T ≤
        (#Q) ^ Fintype.card T * (Fintype.card α).descFactorial (Fintype.card T) :=
    (Nat.mul_le_mul_right _ hcard_good).trans
      (Nat.descFactorial_mul_pow_le (card_le_univ Q) (Fintype.card T))
  exact_mod_cast hnat

/-- **Per-coordinate without-replacement upper bound**: for any per-coordinate target sets
`Q : T → Finset α` and `2 * |T| ^ 2 ≤ |α|`, a uniform injection `e ← PMF.uniformOfFintype (T ↪ α)`
lands in `∏ᵢ Q i` with probability at most `2 * ∏ᵢ (#(Q i) / |α|)`. -/
theorem prob_uniformOfFintype_embedding_forall_mem_perKey_le {T α : Type*}
    [Fintype T] [Fintype α] [Nonempty α]
    (hcard2 : 2 * (Fintype.card T) ^ 2 ≤ Fintype.card α) (Q : T → Finset α) :
    haveI : Nonempty (T ↪ α) := Function.Embedding.nonempty_of_card_le (by nlinarith)
    ((PMF.uniformOfFintype (T ↪ α)).toOuterMeasure {e : T ↪ α | ∀ i : T, e i ∈ Q i}).toReal ≤
      2 * ∏ i : T, ((#(Q i) : ℝ) / (Fintype.card α : ℝ)) := by
  classical
  have hT : Fintype.card T ≤ Fintype.card α := by nlinarith
  have : Nonempty (T ↪ α) := Function.Embedding.nonempty_of_card_le hT
  let E : Set (T ↪ α) := {e : T ↪ α | ∀ i : T, e i ∈ Q i}
  let toPi : {e : T ↪ α // e ∈ E} ↪ ((i : T) → Q i) :=
    { toFun := fun ⟨e, he⟩ i => ⟨e i, he i⟩
      inj' := fun ⟨_, _⟩ ⟨_, _⟩ h =>
        Subtype.ext (DFunLike.ext _ _ fun i => congrArg Subtype.val (congrFun h i)) }
  have hcard_good : #(univ.filter (· ∈ E)) ≤ ∏ i : T, #(Q i) := by
    calc #(univ.filter (· ∈ E))
        = Fintype.card {e : T ↪ α // e ∈ E} := (Fintype.card_subtype _).symm
      _ ≤ Fintype.card ((i : T) → Q i) := Fintype.card_le_of_injective toPi toPi.injective
      _ = ∏ i : T, #(Q i) := by simp [Fintype.card_pi]
  change ((PMF.uniformOfFintype (T ↪ α)).toOuterMeasure E).toReal ≤ _
  rw [toOuterMeasure_uniformOfFintype_toReal, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_univ, ← mul_div_assoc]
  have hcard_emb : Fintype.card (T ↪ α) = (Fintype.card α).descFactorial (Fintype.card T) :=
    Fintype.card_embedding_eq
  have hdesc_pos : 0 < (Fintype.card α).descFactorial (Fintype.card T) :=
    hcard_emb ▸ Fintype.card_pos
  have hα_pos : (0 : ℝ) < (Fintype.card α : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  rw [hcard_emb, div_le_div_iff₀ (Nat.cast_pos.mpr hdesc_pos) (pow_pos hα_pos _)]
  have hnat :
      #(univ.filter (· ∈ E)) * Fintype.card α ^ Fintype.card T ≤
        (2 * ∏ i : T, #(Q i)) * (Fintype.card α).descFactorial (Fintype.card T) := by
    calc #(univ.filter (· ∈ E)) * Fintype.card α ^ Fintype.card T
        ≤ (∏ i : T, #(Q i)) * (2 * (Fintype.card α).descFactorial (Fintype.card T)) :=
          Nat.mul_le_mul hcard_good (Nat.pow_le_two_mul_descFactorial hcard2)
      _ = (2 * ∏ i : T, #(Q i)) * (Fintype.card α).descFactorial (Fintype.card T) := by ring
  exact_mod_cast hnat

private theorem ratio_not_injective_fun_le (T α : Type*) [Fintype T] [DecidableEq T]
    [Fintype α] [Nonempty α]
    [DecidablePred fun f : T → α => ¬ Function.Injective f] :
    (#(univ.filter fun f : T → α => ¬ Function.Injective f) : ℝ) /
        (Fintype.card (T → α) : ℝ) ≤
      ((Fintype.card T * (Fintype.card T - 1) : ℕ) : ℝ) / (2 * (Fintype.card α : ℝ)) := by
  classical
  let j : (T ↪ α) → (T → α) := fun e i => e i
  have hj : Function.Injective j := fun _ _ h => DFunLike.ext' h
  have hpart : #(univ.filter fun f : T → α => ¬ Function.Injective f) +
      Fintype.card (T ↪ α) = Fintype.card (T → α) := by
    have heq : (univ.filter fun f : T → α => ¬ Function.Injective f) = univ \ univ.image j := by
      ext f
      rw [mem_filter, mem_sdiff, mem_image]
      refine ⟨fun ⟨_, h⟩ => ⟨mem_univ f, fun ⟨e, _, he⟩ => h (he ▸ e.injective)⟩,
        fun ⟨_, h⟩ => ⟨mem_univ f, fun hfinj => h ⟨⟨f, hfinj⟩, mem_univ _, rfl⟩⟩⟩
    have hcard_im : #(univ.image j) = Fintype.card (T ↪ α) :=
      (card_image_of_injective univ hj).trans card_univ
    rw [heq, ← hcard_im]
    exact card_sdiff_add_card_eq_card (subset_univ _)
  rw [Fintype.card_embedding_eq, Fintype.card_fun] at hpart
  rw [Fintype.card_fun]
  set A := Fintype.card α
  set r := Fintype.card T
  set bad := #(univ.filter fun f : T → α => ¬ Function.Injective f)
  have hA_pos : (0 : ℝ) < (A : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  rcases Nat.eq_zero_or_pos r with hr0 | hr
  · have hbad0 : bad = 0 := by
      have h1 := hpart
      rw [hr0, pow_zero, Nat.descFactorial_zero] at h1
      omega
    simp [hbad0, hr0]
  · rw [Nat.cast_pow, div_le_div_iff₀ (pow_pos hA_pos r) (by positivity)]
    have htop := Nat.two_mul_pow_le_two_mul_descFactorial_add A r
    have hnat : bad * (2 * A) ≤ r * (r - 1) * A ^ r := by
      have h2bad : 2 * bad ≤ r * (r - 1) * A ^ (r - 1) := by omega
      calc bad * (2 * A)
          = (2 * bad) * A := by ring
        _ ≤ (r * (r - 1) * A ^ (r - 1)) * A := Nat.mul_le_mul_right A h2bad
        _ = r * (r - 1) * (A ^ (r - 1) * A) := by ring
        _ = r * (r - 1) * A ^ r := by rw [← pow_succ, Nat.sub_add_cancel hr]
    exact_mod_cast hnat

/-- Birthday collision bound for a uniform random function `f ← PMF.uniformOfFintype (T → α)`. -/
theorem prob_not_injective_uniform_le (T α : Type*) [Fintype T] [DecidableEq T]
    [Fintype α] [Nonempty α] :
    ((PMF.uniformOfFintype (T → α)).toOuterMeasure
      {f : T → α | ¬ Function.Injective f}).toReal ≤
      ((Fintype.card T * (Fintype.card T - 1) : ℕ) : ℝ) / (2 * (Fintype.card α : ℝ)) := by
  classical
  let E : Set (T → α) := {f | ¬ Function.Injective f}
  change ((PMF.uniformOfFintype (T → α)).toOuterMeasure E).toReal ≤ _
  rw [toOuterMeasure_uniformOfFintype_toReal]
  have hfilt : univ.filter (· ∈ E) =
      univ.filter (fun f : T → α => ¬ Function.Injective f) :=
    filter_congr fun _ _ => Iff.rfl
  rw [hfilt]
  exact ratio_not_injective_fun_le T α

/-- Statistical distance between a uniform random injection `T ↪ α` (coerced to `T → α`) and a
uniform random function `T → α` is at most `|T| * (|T| - 1) / (2 * |α|)`. -/
theorem dist_uniform_embedding_to_fun {T α : Type*} [Fintype T] [DecidableEq T]
    [Fintype α] [Nonempty α] (hcard : Fintype.card T ≤ Fintype.card α) :
    haveI : Nonempty (T ↪ α) := Function.Embedding.nonempty_of_card_le hcard
    dist ((PMF.uniformOfFintype (T ↪ α)).map (fun e : T ↪ α => (e : T → α)))
      (PMF.uniformOfFintype (T → α)) ≤
      ((Fintype.card T * (Fintype.card T - 1) : ℕ) : ℝ) / (2 * (Fintype.card α : ℝ)) := by
  classical
  have : Nonempty (T ↪ α) := Function.Embedding.nonempty_of_card_le hcard
  let j : (T ↪ α) → (T → α) := fun e i => e i
  have hj : Function.Injective j := fun _ _ h => DFunLike.ext' h
  let InjSet : Finset (T → α) := univ.image j
  have hInj_ne : InjSet.Nonempty := univ_nonempty.image j
  have hmap_eq : (PMF.uniformOfFintype (T ↪ α)).map j = PMF.uniformOfFinset InjSet hInj_ne := by
    ext f
    simp only [PMF.map_apply, PMF.uniformOfFintype_apply, PMF.uniformOfFinset_apply,
      tsum_fintype, InjSet, card_image_of_injective univ hj, card_univ]
    by_cases hf : f ∈ univ.image j
    · obtain ⟨e, _, rfl⟩ := mem_image.mp hf
      simp only [hf, ↓reduceIte, eq_comm (a := j e), hj.eq_iff, Fintype.sum_ite_eq']
    · have hnone : ∀ e : T ↪ α, f ≠ j e := fun e h => hf (h ▸ mem_image_of_mem j (mem_univ e))
      simp [hf, hnone]
  have hunif_eq : PMF.uniformOfFintype (T → α) =
      PMF.uniformOfFinset (univ : Finset (T → α)) univ_nonempty := by
    ext f
    simp [PMF.uniformOfFintype_apply, PMF.uniformOfFinset_apply]
  rw [hmap_eq, hunif_eq, dist_uniformOfFinset_of_card_le hInj_ne univ_nonempty (card_le_univ _),
    card_univ]
  have hsub : #(univ \ InjSet) ≤ #(univ.filter fun f : T → α => ¬ Function.Injective f) := by
    refine card_le_card fun f hf => ?_
    rw [mem_sdiff] at hf
    rw [mem_filter]
    exact ⟨mem_univ f, fun hfinj => hf.2 (mem_image.mpr ⟨⟨f, hfinj⟩, mem_univ _, rfl⟩)⟩
  exact (div_le_div_of_nonneg_right (Nat.cast_le.mpr hsub) (Nat.cast_nonneg _)).trans
    (ratio_not_injective_fun_le T α)

/-- Exact product-event probability under `PMF.uniformOfFintype (T → α × β)`. -/
theorem prob_uniformOfFintype_pi_prod_forall_mem {T α β : Type*}
    [Fintype T] [DecidableEq T] [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (B : T → Finset α) (A : T → Finset β) :
    ((PMF.uniformOfFintype (T → α × β)).toOuterMeasure
      {f : T → α × β | ∀ i : T, (f i).1 ∈ B i ∧ (f i).2 ∈ A i}).toReal =
      ∏ i : T, (((#(B i) : ℝ) / (Fintype.card α : ℝ)) *
        ((#(A i) : ℝ) / (Fintype.card β : ℝ))) := by
  classical
  let E : Set (T → α × β) := {f | ∀ i : T, (f i).1 ∈ B i ∧ (f i).2 ∈ A i}
  change ((PMF.uniformOfFintype (T → α × β)).toOuterMeasure E).toReal = _
  rw [toOuterMeasure_uniformOfFintype_toReal]
  have hfilt : univ.filter (· ∈ E) = Fintype.piFinset (fun i : T => B i ×ˢ A i) := by
    ext f
    simp [E, Fintype.mem_piFinset]
  rw [hfilt, Fintype.card_piFinset, Fintype.card_pi]
  simp only [Finset.card_product, Fintype.card_prod, Nat.cast_prod, Nat.cast_mul, div_mul_div_comm]
  rw [Finset.prod_div_distrib]

end Cslib.Probability
