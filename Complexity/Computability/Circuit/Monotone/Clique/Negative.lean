/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Monotone.Clique.Positive
public import Mathlib.Data.Fintype.BigOperators

/-!
# Negative errors of clique approximators

On the complete multipartite graph of a colouring `c` with `r` colours, a set of vertices has all
edges inside exactly when `c` is injective on it (`Cslib.Circuits.Clique.contains_ofColoring_iff`).
The approximate interpretation is wrong on such an input only when the approximator says `true`
and the exact value is `false`. Disjunctions and conjunctions of sets make no such errors; only
plucking does, when the colouring is injective on the core of a sunflower but on none of its
petals.

For such a colouring, every petal contains two vertices of the same colour, one of them outside the
core and so private to the petal. Choosing such a pair for every petal fixes the colour of one
private vertex per petal in terms of the colours of the others, which leaves at most
`(w ^ 2) ^ p * r ^ (n - p)` colourings (`card_sunflowerBad_le`). A plucking normalisation makes at
most as many plucks as the family has sets (`Cslib.relatesInSteps_pluckNormalForm`), which bounds
the errors of a gate (`Cslib.Circuits.Monotone.Negative.scheme`).

On the other hand, a nonempty approximator accepts at least half of the colourings when `r` is at
least twice the number `w ^ 2` of pairs inside a set (`half_le_card_acceptedColorings`).

## Main definitions

* `Cslib.Circuits.Monotone.Negative.collisionPairs`,
  `Cslib.Circuits.Monotone.Negative.Profile`: collision pairs in a petal and profiles of collision
  pairs across a sunflower.
* `Cslib.Circuits.Monotone.Negative.sunflowerBad`,
  `Cslib.Circuits.Monotone.Negative.pluckErrorCap`: colourings injective on a sunflower core but on
  none of its petals, and the per-pluck negative error bound.
* `Cslib.Circuits.Monotone.Negative.stepExceptions`,
  `Cslib.Circuits.Monotone.Negative.errorCost`,
  `Cslib.Circuits.Monotone.Negative.exceptions`: negative errors of a step, per-operation negative
  error cost, and negative gate exceptions.
* `Cslib.Circuits.Monotone.Negative.scheme`: the approximation scheme on multipartite graphs.
* `Cslib.Circuits.Monotone.Negative.acceptedColorings`: colourings accepted by a family of vertex
  sets.

## Main results

* `Cslib.Circuits.Monotone.Negative.card_sunflowerBad_le`: the colourings injective on the core of
  a sunflower but on none of its petals.
* `Cslib.Circuits.Monotone.Negative.half_le_card_acceptedColorings`: a nonempty approximator
  accepts many colourings.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*, Chapter 9][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits.Monotone.Negative

open Cslib.Circuits.Clique Finset Relation Approximator

variable {n r p w : ℕ}

/-! ### Colourings bad for a sunflower -/

/-- The ordered pairs of distinct vertices of `s` whose first vertex is outside `K`. -/
def collisionPairs (K s : Finset (Fin n)) : Finset (Fin n × Fin n) :=
  ((s \ K) ×ˢ s).filter fun uv => uv.1 ≠ uv.2

/-- An ordered pair of vertices belongs to `collisionPairs K s` if and only if its first vertex lies
in `s \ K`, its second vertex lies in `s`, and the two vertices are distinct. -/
@[simp] theorem mem_collisionPairs {K s : Finset (Fin n)} {uv : Fin n × Fin n} :
    uv ∈ collisionPairs K s ↔ uv.1 ∈ s ∧ uv.1 ∉ K ∧ uv.2 ∈ s ∧ uv.1 ≠ uv.2 := by
  simp [collisionPairs, and_assoc]

private theorem card_collisionPairs_le {K s : Finset (Fin n)} (hs : s.card ≤ w) :
    (collisionPairs K s).card ≤ w ^ 2 :=
  calc (collisionPairs K s).card ≤ ((s \ K) ×ˢ s).card := card_le_card (filter_subset _ _)
    _ = (s \ K).card * s.card := card_product _ _
    _ ≤ w * w := Nat.mul_le_mul ((card_le_card sdiff_subset).trans hs) hs
    _ = w ^ 2 := (pow_two w).symm

/-- A choice of a collision pair in every petal. -/
abbrev Profile (S : Finset (Finset (Fin n))) (K : Finset (Fin n)) : Type :=
  ∀ s : S, collisionPairs K s.1

private theorem card_profile_le {S : Finset (Finset (Fin n))} {K : Finset (Fin n)}
    (hS : ∀ s ∈ S, s.card ≤ w) : Fintype.card (Profile S K) ≤ (w ^ 2) ^ S.card := by
  rw [Fintype.card_pi]
  calc ∏ s : S, Fintype.card (collisionPairs K s.1) ≤ ∏ _s : S, w ^ 2 :=
        prod_le_prod fun s _ => (Fintype.card_coe _).trans_le (card_collisionPairs_le (hS s s.2))
    _ = (w ^ 2) ^ S.card := by simp

/-- The first vertices of the pairs of a profile. -/
private def selected {S : Finset (Finset (Fin n))} {K : Finset (Fin n)} (π : Profile S K) :
    Finset (Fin n) :=
  univ.image fun s => (π s).1.1

/-- When distinct members of `S` meet only inside `K`, as the petals of a sunflower with core `K`
do, the first vertex of a collision pair is private to its petal. -/
theorem fst_injective {S : Finset (Finset (Fin n))} {K : Finset (Fin n)}
    (hS : (S : Set (Finset (Fin n))).Pairwise fun s t => s ∩ t ⊆ K)
    (π : Profile S K) : Function.Injective fun s : S => (π s).1.1 := by
  intro s t hst
  by_contra hne
  have hst' : (π s).1.1 = (π t).1.1 := hst
  have hs := mem_collisionPairs.1 (π s).2
  have ht := mem_collisionPairs.1 (π t).2
  exact hs.2.1 (hS s.2 t.2 (fun e => hne (Subtype.ext e)) (mem_inter.2 ⟨hs.1, hst' ▸ ht.1⟩))

private theorem card_selected {S : Finset (Finset (Fin n))} {K : Finset (Fin n)}
    (hS : (S : Set (Finset (Fin n))).Pairwise fun s t => s ∩ t ⊆ K)
    (π : Profile S K) : (selected π).card = S.card := by
  rw [selected, card_image_of_injective _ (fst_injective hS π), card_univ, Fintype.card_coe]

/-- The second vertex of a collision pair is not selected. -/
private theorem snd_notMem_selected {S : Finset (Finset (Fin n))} {K : Finset (Fin n)}
    (hS : (S : Set (Finset (Fin n))).Pairwise fun s t => s ∩ t ⊆ K)
    (π : Profile S K) (s : S) : (π s).1.2 ∉ selected π := by
  intro h
  obtain ⟨t, -, hts⟩ := mem_image.1 h
  have hs := mem_collisionPairs.1 (π s).2
  have ht := mem_collisionPairs.1 (π t).2
  by_cases hst : s = t
  · subst hst
    exact hs.2.2.2 hts
  · exact ht.2.1 (hS s.2 t.2 (fun e => hst (Subtype.ext e))
      (mem_inter.2 ⟨hts ▸ hs.2.2.1, ht.1⟩))

/-- The colourings giving both vertices of every pair of a profile the same colour. -/
private def profileColorings (r : ℕ) {S : Finset (Finset (Fin n))} {K : Finset (Fin n)}
    (π : Profile S K) : Finset (Coloring n r) :=
  univ.filter fun c => ∀ s, c (π s).1.1 = c (π s).1.2

/-- The colourings of a profile are determined by their colours outside the selected vertices. -/
private theorem card_profileColorings_le {S : Finset (Finset (Fin n))} {K : Finset (Fin n)}
    (hS : (S : Set (Finset (Fin n))).Pairwise fun s t => s ∩ t ⊆ K) (π : Profile S K) :
    (profileColorings r π).card ≤ r ^ (n - S.card) := by
  let O := univ \ selected π
  let f : profileColorings r π → O → Fin r := fun c v => c.1 v.1
  have hf : Function.Injective f := by
    intro c d hcd
    refine Subtype.ext (funext fun v => ?_)
    by_cases hv : v ∈ selected π
    · obtain ⟨s, -, rfl⟩ := mem_image.1 hv
      have hc := (mem_filter.1 c.2).2 s
      have hd := (mem_filter.1 d.2).2 s
      rw [hc, hd]
      exact congrFun hcd ⟨_, mem_sdiff.2 ⟨mem_univ _, snd_notMem_selected hS π s⟩⟩
    · exact congrFun hcd ⟨v, mem_sdiff.2 ⟨mem_univ _, hv⟩⟩
  have := Fintype.card_le_of_injective f hf
  rwa [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe,
    card_univ_sdiff, Fintype.card_fin, card_selected hS π] at this

/-- A colouring injective on `K` but not on `s` has a collision pair in `s`. -/
private theorem exists_collisionPair {c : Coloring n r} {K s : Finset (Fin n)}
    (hK : Set.InjOn c K) (hs : ¬Set.InjOn c s) :
    ∃ uv : collisionPairs K s, c uv.1.1 = c uv.1.2 := by
  simp only [Set.InjOn, not_forall] at hs
  obtain ⟨u, hu, v, hv, hc, huv⟩ := hs
  by_cases huK : u ∈ K
  · have hvK : v ∉ K := fun hvK => huv (hK huK hvK hc)
    exact ⟨⟨(v, u), mem_collisionPairs.2 ⟨hv, hvK, hu, Ne.symm huv⟩⟩, hc.symm⟩
  · exact ⟨⟨(u, v), mem_collisionPairs.2 ⟨hu, huK, hv, huv⟩⟩, hc⟩

/-- The colourings injective on the core of a sunflower but on none of its petals. -/
def sunflowerBad (r : ℕ) (S : Finset (Finset (Fin n))) (K : Finset (Fin n)) :
    Finset (Coloring n r) :=
  univ.filter fun c => Set.InjOn c K ∧ ∀ s ∈ S, ¬Set.InjOn c s

/-- The number of negative errors charged to one pluck. -/
def pluckErrorCap (n r p w : ℕ) : ℕ := (w ^ 2) ^ p * r ^ (n - p)

/-- **Bad colourings of a sunflower.** At most `(w ^ 2) ^ p * r ^ (n - p)` colourings are injective
on the core of a sunflower with `p` petals of at most `w` vertices but on none of the petals. The
petals need only meet inside the core, not exactly in it. -/
theorem card_sunflowerBad_le {S : Finset (Finset (Fin n))} {K : Finset (Fin n)}
    (hSp : S.card = p) (hS : (S : Set (Finset (Fin n))).Pairwise fun s t => s ∩ t ⊆ K)
    (hSw : ∀ s ∈ S, s.card ≤ w) :
    (sunflowerBad r S K).card ≤ pluckErrorCap n r p w := by
  classical
  have hcover : sunflowerBad r S K ⊆ (univ : Finset (Profile S K)).biUnion (profileColorings r) :=
    fun c hc => by
      obtain ⟨hK, hs⟩ := (mem_filter.1 hc).2
      choose π hπ using fun s : S => exists_collisionPair hK (hs s.1 s.2)
      exact mem_biUnion.2 ⟨π, mem_univ _, mem_filter.2 ⟨mem_univ _, hπ⟩⟩
  calc (sunflowerBad r S K).card
      ≤ ∑ π : Profile S K, (profileColorings r π).card :=
        (card_le_card hcover).trans card_biUnion_le
    _ ≤ ∑ _π : Profile S K, r ^ (n - S.card) :=
        sum_le_sum fun π _ => card_profileColorings_le hS π
    _ = Fintype.card (Profile S K) * r ^ (n - S.card) := by rw [sum_const, card_univ, smul_eq_mul]
    _ ≤ (w ^ 2) ^ S.card * r ^ (n - S.card) := Nat.mul_le_mul_right _ (card_profile_le hSw)
    _ = pluckErrorCap n r p w := by rw [hSp, pluckErrorCap]

/-! ### Errors of plucking -/

/-- The colourings accepted by `G` but not by `F`. -/
noncomputable def stepExceptions (r : ℕ) (F G : Finset (Finset (Fin n))) : Finset (Coloring n r) :=
  univ.filter fun c => Accepts G (ofColoring c) ∧ ¬Accepts F (ofColoring c)

/-- A colouring belongs to `stepExceptions r F G` if and only if `ofColoring c` is accepted by `G`
and rejected by `F`. -/
@[simp] theorem mem_stepExceptions {F G : Finset (Finset (Fin n))} {c : Coloring n r} :
    c ∈ stepExceptions r F G ↔ Accepts G (ofColoring c) ∧ ¬Accepts F (ofColoring c) := by
  simp [stepExceptions]

/-- One pluck makes at most `pluckErrorCap n r p w` negative errors. -/
private theorem card_stepExceptions_le_of_pluck {F G : Finset (Finset (Fin n))} (h : Pluck p F G)
    (hF : ∀ s ∈ F, s.card ≤ w) : (stepExceptions r F G).card ≤ pluckErrorCap n r p w := by
  obtain ⟨S, hSF, hSp, K, hSK, rfl⟩ := h
  refine (card_le_card fun c hc => ?_).trans
    (card_sunflowerBad_le hSp (hSK.imp fun _ _ h => h.subset) fun s hs => hF s (hSF hs))
  obtain ⟨⟨t, ht, hct⟩, hF'⟩ := mem_stepExceptions.1 hc
  refine mem_filter.2 ⟨mem_univ _, ?_, fun s hs hcs =>
    hF' ⟨s, hSF hs, contains_ofColoring_iff.2 hcs⟩⟩
  rcases mem_insert.1 ht with rfl | ht
  · exact contains_ofColoring_iff.1 hct
  · exact absurd ⟨t, (mem_sdiff.1 ht).1, hct⟩ hF'

/-- The negative exceptions between `F` and `H` are contained in the union of those between `F` and
`G` and those between `G` and `H`. -/
theorem stepExceptions_subset (r : ℕ) (F G H : Finset (Finset (Fin n))) :
    stepExceptions r F H ⊆ stepExceptions r F G ∪ stepExceptions r G H := fun c hc => by
  obtain ⟨hH, hF⟩ := mem_stepExceptions.1 hc
  by_cases hG : Accepts G (ofColoring c)
  · exact mem_union_left _ (mem_stepExceptions.2 ⟨hG, hF⟩)
  · exact mem_union_right _ (mem_stepExceptions.2 ⟨hH, hG⟩)

/-- `m` plucks make at most `m` times `pluckErrorCap n r p w` negative errors. -/
private theorem card_stepExceptions_le_of_relatesInSteps (hp : 2 ≤ p)
    {F G : Finset (Finset (Fin n))}
    {m : ℕ} (h : RelatesInSteps (Pluck p) F G m) (hF : ∀ s ∈ F, s.card ≤ w) :
    (stepExceptions r F G).card ≤ m * pluckErrorCap n r p w := by
  induction h with
  | refl => simp [stepExceptions]
  | tail G H m hFG hGH ih =>
    calc (stepExceptions r F H).card
        ≤ (stepExceptions r F G ∪ stepExceptions r G H).card :=
          card_le_card (stepExceptions_subset r F G H)
      _ ≤ m * pluckErrorCap n r p w + pluckErrorCap n r p w :=
          (card_union_le _ _).trans (Nat.add_le_add ih (card_stepExceptions_le_of_pluck hGH
            (forall_card_le_of_relatesInSteps_pluck hp hFG hF)))
      _ = (m + 1) * pluckErrorCap n r p w := (Nat.succ_mul _ _).symm

/-- A plucking normalisation makes at most as many errors as `pluckErrorCap n r p w` times the
number of sets of the family. -/
theorem card_stepExceptions_pluckNormalForm_le (hp : 2 ≤ p) {F : Finset (Finset (Fin n))}
    (hF : ∀ s ∈ F, s.card ≤ w) :
    (stepExceptions r F (pluckNormalForm p F)).card ≤ F.card * pluckErrorCap n r p w :=
  let ⟨_, hm, h⟩ := relatesInSteps_pluckNormalForm hp F
  (card_stepExceptions_le_of_relatesInSteps hp h hF).trans (Nat.mul_le_mul_right _ hm)

/-! ### The approximation scheme -/

/-- The number of negative errors charged to each operation. -/
def errorCost (n r p w : ℕ) : signature.Op → ℕ
  | .const _ => pluckErrorCap n r p w
  | .or => 2 * sunflowerBound p w * pluckErrorCap n r p w
  | .and => sunflowerBound p w ^ 2 * pluckErrorCap n r p w

/-- The number of pre-plucked terms produced by `op`, multiplied by `pluckErrorCap n r p w`, is at
most `errorCost n r p w op`. -/
theorem card_gateTerms_le (op : Op) (A : Fin (signature.Arity op) → Approximator n p w) :
    (gateTerms w op fun i => (A i).terms).card * pluckErrorCap n r p w ≤
      errorCost n r p w op := by
  cases op with
  | const b =>
    rw [errorCost]
    refine (Nat.mul_le_mul_right _ ?_).trans_eq (one_mul _)
    cases b <;> simp [gateTerms]
  | or =>
    refine Nat.mul_le_mul_right _ ((card_filter_le _ _).trans ((card_union_le _ _).trans ?_))
    beta_reduce
    have := (A 0).card_le
    have := (A 1).card_le
    omega
  | and =>
    refine Nat.mul_le_mul_right _ ((card_filter_le _ _).trans (card_image_le.trans ?_))
    rw [card_product, pow_two]
    exact Nat.mul_le_mul (A 0).card_le (A 1).card_le

/-- The negative errors of a gate: those of plucking the sets produced at the gate. -/
noncomputable def exceptions (r : ℕ) (op : Op) (A : Fin (signature.Arity op) → Approximator n p w) :
    Finset (Coloring n r) :=
  stepExceptions r (gateTerms w op fun i => (A i).terms)
    (pluckNormalForm p (gateTerms w op fun i => (A i).terms))

variable [Fact (2 ≤ p)]

/-- Away from its exceptions, a gate is negatively correct on multipartite graphs. -/
theorem gate_correct (op : Op) (A : Fin (signature.Arity op) → Approximator n p w)
    (c : Coloring n r) (hc : c ∉ exceptions r op A) :
    (Approximator.interpretation op A).decode (ofColoring c) ≤
      Monotone.interpretation op fun i => (A i).decode (ofColoring c) := by
  rw [Bool.le_iff_imp, decode_eq_true, terms_interpretation]
  intro h
  have hG : Accepts (gateTerms w op fun i => (A i).terms) (ofColoring c) :=
    not_not.1 fun hG => hc (mem_stepExceptions.2 ⟨h, hG⟩)
  obtain ⟨s, hs, hcs⟩ := hG
  cases op with
  | const b => cases b <;> simp_all [gateTerms]
  | or =>
    rw [interpretation_or, Bool.or_eq_true, decode_eq_true, decode_eq_true]
    rcases mem_union.1 (mem_filter.1 hs).1 with hs | hs
    · exact Or.inl ⟨s, hs, hcs⟩
    · exact Or.inr ⟨s, hs, hcs⟩
  | and =>
    rw [interpretation_and, Bool.and_eq_true, decode_eq_true, decode_eq_true]
    obtain ⟨⟨t, u⟩, htu, rfl⟩ := mem_image.1 (mem_filter.1 hs).1
    obtain ⟨ht, hu⟩ := mem_product.1 htu
    have hj := Contains.of_join (x := ofColoring c) (s := t) (t := u) hcs
    exact ⟨⟨t, ht, hj.1⟩, ⟨u, hu, hj.2⟩⟩

/-- **Negative errors.** The approximation scheme on the complete multipartite graphs of
colourings with `r` colours: the approximate value is at most the exact one away from the errors
of plucking. -/
noncomputable def scheme (hw : 2 ≤ w) :
    Approximation.Scheme Monotone.interpretation (Approximator.interpretation (n := n) (p := p))
      (fun (A : Approximator n p w) (c : Coloring n r) => A.decode (ofColoring c))
      ofColoring Approximator.input where
  relation u v := v ≤ u
  relation_trans h h' := h'.trans h
  map_relation op _ _ h := interpretation_mono op h
  errorCost := errorCost n r p w
  exceptions := exceptions r
  input_correct c i := by rw [decode_input hw]
  gate_correct := gate_correct
  exceptions_card_le op A := (card_stepExceptions_pluckNormalForm_le Fact.out
    fun _ => card_le_of_mem_gateTerms).trans (card_gateTerms_le op A)

/-! ### Approximators accept many colourings -/

/-- The colourings accepted by a family of vertex sets. -/
noncomputable def acceptedColorings (r : ℕ) (F : Finset (Finset (Fin n))) : Finset (Coloring n r) :=
  univ.filter fun c => Accepts F (ofColoring c)

/-- At most `w ^ 2 * r ^ (n - 1)` colourings are not injective on a set of at most `w`
vertices. -/
private theorem card_filter_not_injOn_le {s : Finset (Fin n)} (hs : s.card ≤ w) :
    (univ.filter fun c : Coloring n r => ¬Set.InjOn c s).card ≤ w ^ 2 * r ^ (n - 1) := by
  have hS : (({s} : Finset (Finset (Fin n))) : Set (Finset (Fin n))).Pairwise
      fun t u => t ∩ u ⊆ ∅ := fun t ht u hu htu => by
    rw [coe_singleton, Set.mem_singleton_iff] at ht hu
    exact absurd (ht.trans hu.symm) htu
  refine (card_le_card fun c hc => ?_).trans ((card_sunflowerBad_le (card_singleton s) hS
    fun t ht => (mem_singleton.1 ht) ▸ hs).trans_eq (by simp [pluckErrorCap]))
  exact mem_filter.2 ⟨mem_univ _, by simp, fun t ht => (mem_singleton.1 ht) ▸ (mem_filter.1 hc).2⟩

/-- **Approximators accept many colourings.** If `r` is at least twice `w ^ 2`, every nonempty
family of sets of at most `w` vertices accepts at least half of the colourings. -/
theorem half_le_card_acceptedColorings (hn : 0 < n) (hr : 2 * w ^ 2 ≤ r)
    {F : Finset (Finset (Fin n))} (hF : ∀ s ∈ F, s.card ≤ w) (hne : F.Nonempty) :
    r ^ n ≤ 2 * (acceptedColorings r F).card := by
  obtain ⟨s, hs⟩ := hne
  have hbad := card_filter_not_injOn_le (r := r) (hF s hs)
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (Coloring n r)))
    fun c => Set.InjOn c s
  rw [card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at hsplit
  have hacc : (univ.filter fun c : Coloring n r => Set.InjOn c s).card ≤
      (acceptedColorings r F).card :=
    card_le_card fun c hc => mem_filter.2 ⟨mem_univ _, s, hs,
      contains_ofColoring_iff.2 (mem_filter.1 hc).2⟩
  have hpow : 2 * (w ^ 2 * r ^ (n - 1)) ≤ r ^ n := by
    calc 2 * (w ^ 2 * r ^ (n - 1)) = 2 * w ^ 2 * r ^ (n - 1) := (Nat.mul_assoc _ _ _).symm
      _ ≤ r * r ^ (n - 1) := Nat.mul_le_mul_right _ hr
      _ = r ^ n := by rw [← pow_succ', Nat.sub_add_cancel hn]
  omega

end Cslib.Circuits.Monotone.Negative
