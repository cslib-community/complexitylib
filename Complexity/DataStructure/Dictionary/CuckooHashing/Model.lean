/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.Spec
public import Complexity.DataStructure.Dictionary.WordRAM.CuckooHashing.HashFamily
public import Complexity.DataStructure.StateTransition.Randomized
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Expect
import Complexity.Probability.PMF.Map

/-!
# Cuckoo hashing as a randomized specification

This is the seed-level model of Pagh and Rodler's two-table cuckoo hashing [PaghRodler2004]. A
model state holds the hash seed, the keys in insertion order, the dictionary they store, and a
flag recording whether the seed was drawn fresh. The tables themselves are not part of the state:
under a seed `θ` they are the replay of the keys, `Scheme.replay θ ks`
(`WordRAM.CuckooHashing.pureReplay`).

A lookup is deterministic. An insertion of a new key keeps the seed when the replay with the new
key still succeeds (`Scheme.Good`), and otherwise rehashes. A rehash draws up to `attempts` fresh
seeds from the uniform law, keeping the first one under which the replay succeeds, and falls back
to a fixed seed (`Scheme.fallback`) if every attempt fails (`Scheme.rehashLaw`). Programs are
finite, so a rehash cannot loop until success. The fallback keeps the operation correct, and its
probability `2⁻ᵃᵗᵗᵉᵐᵖᵗˢ` per rehash is charged in the cost analysis.

`Scheme.dictRefinement` refines the dictionary specification by this model: every answer and the
abstracted dictionary are deterministic, whatever the seeds. All probability is in the costs.
`Scheme.charge` charges each operation with the memory cost of an implementation: a constant per
lookup, the displacement rounds of an insertion, and a rehash constant when the seed fails.

The expected cost of a client is bounded by the pure analysis of `IsCuckooHashPair`
(`Scheme.expectedCost_le`). The proof tracks the law of the model state (`Scheme.DistInv`): among
states with a fresh seed, the seed is uniform on the seeds that survive the current keys, and the
stale states have probability at most `|keys| · 2⁻ᵃᵗᵗᵉᵐᵖᵗˢ`. An oblivious argument is needed,
since a per-state amortized bound cannot hold: an adversary who knew the seed could choose a key
whose insertion fails. The answers do not reveal the seed, so clients of the dictionary are
oblivious.

## Main definitions

* `Scheme`: hash functions over a seed space, eviction cap, rehash attempts and fallback seed.
* `Scheme.replay`, `Scheme.Good`, `Scheme.rounds`: replayed tables, surviving seeds and
  displacement rounds.
* `Model`: seed, keys, dictionary and freshness.
* `Scheme.rehashLaw`, `Scheme.insertLaw`, `Scheme.spec`: the randomized specification.
* `Scheme.dictRefinement`: the dictionary refined by the model.
* `Charges`, `Scheme.charge`, `Scheme.opBound`: model charges and per-operation expected bounds.
* `Scheme.DistInv`: the law of model states along a history.

## Main results

* `Scheme.run_map_dict`: clients of the model answer as the dictionary does.
* `Scheme.distInv_init`, `Scheme.DistInv.insert_present`, `Scheme.DistInv.insert_new`: the law
  invariant at the start and after each insertion.
* `Scheme.DistInv.tsum_charge_le`: the expected charge of one operation is at most `opBound`.
* `Scheme.tsum_expectedCost_le`, `Scheme.expectedCost_le`: the expected charge of any admissible
  client is at most `opBound` per operation.

## References

* [R. Pagh and F. F. Rodler, "Cuckoo hashing"][PaghRodler2004] (8 December 2003 author manuscript,
  Section 2.3, "Analysis", pp. 6–10).
-/

@[expose] public section

namespace Cslib.DataStructure.Dictionary.CuckooHashing

open Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing
open scoped ENNReal

/-- A two-table cuckoo hashing scheme over seeds `Θ`: the two hash functions of each seed, the
eviction cap of an insertion, the number of random rehash attempts, and the seed used for a set of
keys when every attempt fails. -/
structure Scheme (Θ : Type) (U m : ℕ) where
  /-- The hash function into the first table. -/
  hash₁ : Θ → Fin U → Fin m
  /-- The hash function into the second table. -/
  hash₂ : Θ → Fin U → Fin m
  /-- The maximal number of displacement rounds of one insertion. -/
  maxLoop : ℕ
  /-- The number of fresh seeds a rehash tries. -/
  attempts : ℕ
  /-- The seed a rehash falls back to for the given keys. -/
  fallback : List (Fin U) → Θ

/-- A model state: the seed, the keys in insertion order, the stored dictionary, and whether the
seed was drawn fresh rather than set by the fallback. -/
structure Model (Θ : Type) (U : ℕ) where
  /-- The current hash seed. -/
  seed : Θ
  /-- The stored keys in insertion order. -/
  keys : List (Fin U)
  /-- The stored dictionary. -/
  dict : Dictionary.State U
  /-- Whether the seed was drawn fresh. -/
  fresh : Bool

namespace Scheme

variable {Θ : Type} {U m : ℕ} (C : Scheme Θ U m)

/-- The tables after inserting `ks` in order under the seed `θ`, if every insertion settles. -/
def replay (θ : Θ) (ks : List (Fin U)) : Option (PureTable U m) :=
  pureReplay (C.hash₁ θ) (C.hash₂ θ) C.maxLoop ks

/-- The seed `θ` survives the keys `ks`: their replay succeeds. -/
abbrev Good (θ : Θ) (ks : List (Fin U)) : Prop :=
  (C.replay θ ks).isSome

/-- The displacement rounds of inserting `u` into the replay of `ks` under `θ`. -/
def rounds (θ : Θ) (ks : List (Fin U)) (u : Fin U) : ℕ :=
  ((C.replay θ ks).map fun T =>
    evictRounds (C.hash₁ θ) (C.hash₂ θ) C.maxLoop T ⟨u, ks.length⟩).getD 0

theorem replay_append_singleton (θ : Θ) (ks : List (Fin U)) (u : Fin U) :
    C.replay θ (ks ++ [u]) = (C.replay θ ks).bind fun T =>
      pureEvict (C.hash₁ θ) (C.hash₂ θ) C.maxLoop T ⟨u, ks.length⟩ :=
  pureReplay_append_singleton _ _ _ _ _

/-- A seed that survives more keys survives fewer. -/
theorem Good.of_append {θ : Θ} {ks : List (Fin U)} {u : Fin U} (h : C.Good θ (ks ++ [u])) :
    C.Good θ ks := by
  rw [Good, replay_append_singleton] at h
  cases hr : C.replay θ ks with
  | none => simp [hr] at h
  | some _ => simp [Good, hr]

@[simp] theorem good_nil (θ : Θ) : C.Good θ [] := rfl

theorem rounds_le (θ : Θ) (ks : List (Fin U)) (u : Fin U) : C.rounds θ ks u ≤ C.maxLoop := by
  unfold rounds
  cases C.replay θ ks with
  | none => exact Nat.zero_le _
  | some T => exact evictRounds_le _ _ _ _ _

/-! ## The randomized specification -/

variable [Fintype Θ] [Nonempty Θ]

/-- The seed and freshness after a rehash for the keys `ks` with `n` attempts left: draw a uniform
seed, keep it if `ks` replays under it, and otherwise try again; with no attempts left, take the
fallback seed. -/
noncomputable def rehashLaw (ks : List (Fin U)) : ℕ → PMF (Θ × Bool)
  | 0 => PMF.pure (C.fallback ks, false)
  | n + 1 => (Probability.PMF.uniformOfFintype Θ).bind fun θ =>
      if C.Good θ ks then PMF.pure (θ, true) else rehashLaw ks n

omit [Fintype Θ] [Nonempty Θ] in
variable (Θ) in
/-- The model state storing `ks` and `d` after a rehash drew the seed and freshness `x`. -/
def rehashed (ks : List (Fin U)) (d : Dictionary.State U) : Θ × Bool → Model Θ U
  | (θ, f) => ⟨θ, ks, d, f⟩

omit [Fintype Θ] [Nonempty Θ] in
theorem rehashed_injective (ks : List (Fin U)) (d : Dictionary.State U) :
    Function.Injective (rehashed Θ ks d) := by
  rintro ⟨θ, f⟩ ⟨θ', f'⟩ h
  cases h
  rfl

/-- The model state after inserting `u ↦ v`. A present key is updated in place. A new key is
appended; the seed is kept if it survives, and redrawn by `rehashLaw` otherwise. -/
noncomputable def insertLaw (σ : Model Θ U) (u : Fin U) (v : ℕ) : PMF (Model Θ U) :=
  if (σ.dict u).isSome then PMF.pure { σ with dict := Function.update σ.dict u (some v) }
  else if C.Good σ.seed (σ.keys ++ [u]) then
    PMF.pure { σ with keys := σ.keys ++ [u], dict := Function.update σ.dict u (some v) }
  else (C.rehashLaw (σ.keys ++ [u]) C.attempts).map
    (rehashed Θ (σ.keys ++ [u]) (Function.update σ.dict u (some v)))

/-- Cuckoo hashing at the seed level, for values below `V` and at most `n_max` keys. -/
noncomputable abbrev spec (V n_max : ℕ) : RandomizedSpec where
  State := Model Θ U
  Op := Dictionary.Op U
  Result := Dictionary.Op.Result
  law
    | .get u => fun σ => PMF.pure (σ.dict u, σ)
    | .insert u v => fun σ => (C.insertLaw σ u v).map fun σ' => ((), σ')
  valid σ o := Dictionary.valid V n_max σ.dict o

variable {V n_max : ℕ}

@[simp] theorem spec_law_get (u : Fin U) (σ : Model Θ U) :
    (C.spec V n_max).law (.get u) σ = PMF.pure (σ.dict u, σ) := rfl

@[simp] theorem spec_law_insert (u : Fin U) (v : ℕ) (σ : Model Θ U) :
    (C.spec V n_max).law (.insert u v) σ = (C.insertLaw σ u v).map fun σ' => ((), σ') := rfl

/-- Every insertion stores `u ↦ v` in the dictionary, whatever the seeds. -/
theorem map_dict_insertLaw (σ : Model Θ U) (u : Fin U) (v : ℕ) :
    (C.insertLaw σ u v).map Model.dict = PMF.pure (Function.update σ.dict u (some v)) := by
  unfold insertLaw
  split_ifs
  · exact PMF.pure_map _ _
  · exact PMF.pure_map _ _
  · rw [PMF.map_comp]
    exact PMF.map_const _ _

/-! ## The dictionary refined by the model -/

/-- **The dictionary is refined by the model.** Each operation is one call, and the abstraction
reads the dictionary: answers and stored values do not depend on the seeds. -/
noncomputable def dictRefinement (V n_max : ℕ) :
    RandomizedRefinement (Dictionary.spec U V n_max).toRandomized (C.spec V n_max) :=
  .ofLaw (fun o => OracleComp.query o) (fun _ => True) Model.dict
    (fun {_} o _ hv =>
      .liftBind (D := (C.spec V n_max).toSpec) o _ hv fun s' a _ => .pure s' a)
    (fun _ _ _ _ _ _ => trivial)
    (fun {σ} o _ _ => by
      rw [RandomizedSpec.run_query]
      cases o with
      | get u => exact PMF.pure_map _ _
      | insert u v =>
        rw [spec_law_insert, PMF.map_comp]
        change (C.insertLaw σ u v).map (fun σ' => ((), σ'.dict)) = _
        rw [show (fun σ' : Model Θ U => ((), σ'.dict)) = (fun d => ((), d)) ∘ Model.dict from rfl,
          ← PMF.map_comp, map_dict_insertLaw, PMF.pure_map])

@[simp] theorem dictRefinement_abs (σ : Model Θ U) :
    (C.dictRefinement V n_max).abs σ = σ.dict := rfl

/-- **Correctness.** The law of a client of the model, read through the dictionary, is the point
mass at the dictionary's own run. -/
theorem run_map_dict {α : Type} (p : OracleComp (Dictionary.Op.Result (U := U)) α)
    (σ : Model Θ U)
    (hv : (Dictionary.spec U V n_max).ValidHistory σ.dict
      ((Dictionary.spec U V n_max).clientHistory σ.dict p)) :
    ((C.spec V n_max).run p σ).map (fun (a, σ') => (a, σ'.dict)) =
      PMF.pure (DataStructure.eval (Dictionary.spec U V n_max) p σ.dict) := by
  rw [← StateTransitionSpec.run_toRandomized]
  have h := (C.dictRefinement V n_max).run_link p (e := σ) trivial
    (StateTransitionSpec.toRandomized_demonicValid_of_validHistory hv)
  rwa [show link (C.dictRefinement V n_max).methods p = p from
    PFunctor.FreeM.liftM_lift_eq_self p] at h

/-! ## Charges -/

end Scheme

/-- Memory charges of an implementation of the model, per operation. -/
structure Charges where
  /-- A lookup. -/
  get : ℕ
  /-- An insertion of a present key. -/
  present : ℕ
  /-- An insertion of a new key, apart from its displacement rounds and its rehash. -/
  insert : ℕ
  /-- One displacement round. -/
  round : ℕ
  /-- A rehash, in expectation. -/
  rehash : ℕ

namespace Scheme

variable {Θ : Type} {U m : ℕ} (C : Scheme Θ U m)

/-- The charge of an operation at a model state: a constant for a lookup or an update in place;
for a new key, a constant, its displacement rounds, and a rehash if the seed fails. -/
def charge (K : Charges) (σ : Model Θ U) : Dictionary.Op U → ℕ
  | .get _ => K.get
  | .insert u _ =>
    if (σ.dict u).isSome then K.present
    else K.insert + K.round * C.rounds σ.seed σ.keys u +
      if C.Good σ.seed (σ.keys ++ [u]) then 0 else K.rehash

/-- The expected charge of an operation along any history, for a hash pair with expected walk
`Cw` and incremental rehash constant `Cr` (`IsCuckooHashPair`): a lookup costs `K.get`, and an
insertion at most twice its expected walk and rehash charges, plus two units. -/
def opBound (K : Charges) (n_max Cw Cr : ℕ) : Dictionary.Op U → ℕ
  | .get _ => K.get
  | .insert _ _ => max K.present
      (K.insert + 2 * K.round * Cw + 2 * K.rehash * Cr / (max n_max 1 * max C.maxLoop 1) + 2)

/-! ## Keys agreeing with a dictionary -/

/-- Keys in insertion order agreeing with a dictionary: distinct, and exactly its domain. -/
structure Agree (ks : List (Fin U)) (d : Dictionary.State U) : Prop where
  /-- Each key is stored once. -/
  nodup : ks.Nodup
  /-- The keys are the domain. -/
  mem_iff : ∀ u, u ∈ ks ↔ (d u).isSome

omit C in
theorem agree_nil : Agree ([] : List (Fin U)) (Dictionary.empty U) :=
  ⟨List.nodup_nil, fun u => by simp [Dictionary.empty]⟩

omit C in
theorem Agree.length_eq {ks : List (Fin U)} {d : Dictionary.State U} (h : Agree ks d) :
    ks.length = (Dictionary.dom d).card := by
  rw [← List.toFinset_card_of_nodup h.nodup]
  congr 1
  ext u
  simp [h.mem_iff]

omit C in
theorem Agree.update {ks : List (Fin U)} {d : Dictionary.State U} (h : Agree ks d) {u : Fin U}
    (hu : (d u).isSome) (v : ℕ) : Agree ks (Function.update d u (some v)) := by
  refine ⟨h.nodup, fun x => ?_⟩
  by_cases hx : x = u
  · subst hx
    simp [(h.mem_iff x).mpr hu]
  · simp [Function.update_of_ne hx, h.mem_iff]

omit C in
theorem Agree.append {ks : List (Fin U)} {d : Dictionary.State U} (h : Agree ks d) {u : Fin U}
    (hu : d u = none) (v : ℕ) : Agree (ks ++ [u]) (Function.update d u (some v)) := by
  have hnot : u ∉ ks := fun hm => by simpa [hu] using (h.mem_iff u).mp hm
  refine ⟨h.nodup.append (List.nodup_singleton u) (by simpa using hnot), fun x => ?_⟩
  by_cases hx : x = u
  · subst hx
    simp
  · simp [h.mem_iff, hx]

/-! ## The rehash law -/

variable [Fintype Θ] [Nonempty Θ]

/-- Every outcome of a rehash is a surviving seed, when the fallback seed survives. -/
theorem good_of_mem_support_rehashLaw {ks : List (Fin U)} (hfb : C.Good (C.fallback ks) ks)
    {n : ℕ} {x : Θ × Bool} (hx : x ∈ (C.rehashLaw ks n).support) : C.Good x.1 ks := by
  induction n with
  | zero =>
    rw [rehashLaw, PMF.mem_support_pure_iff] at hx
    subst hx
    exact hfb
  | succ n ih =>
    rw [rehashLaw, PMF.mem_support_bind_iff] at hx
    obtain ⟨θ, -, hx⟩ := hx
    split_ifs at hx with hθ
    · rw [PMF.mem_support_pure_iff] at hx
      subst hx
      exact hθ
    · exact ih hx

/-- The fresh outcomes of the next rehash attempt: a fresh surviving seed is drawn with its
uniform weight, and the remaining weight passes to the later attempts. -/
theorem rehashLaw_succ_apply_true {ks : List (Fin U)} {θ : Θ} (hθ : C.Good θ ks) (n : ℕ) :
    C.rehashLaw ks (n + 1) (θ, true) =
      Probability.PMF.uniformOfFintype Θ θ +
        (∑' η, Probability.PMF.uniformOfFintype Θ η * (if C.Good η ks then 0 else 1)) *
          C.rehashLaw ks n (θ, true) := by
  classical
  rw [rehashLaw, PMF.bind_apply]
  calc _ = ∑' η, ((if η = θ then Probability.PMF.uniformOfFintype Θ η else 0) +
        Probability.PMF.uniformOfFintype Θ η * (if C.Good η ks then 0 else 1) *
          C.rehashLaw ks n (θ, true)) := by
        refine tsum_congr fun η => ?_
        by_cases hη : C.Good η ks
        · rw [ite_eq_left hη, ite_eq_left hη, PMF.pure_apply, mul_zero, zero_mul, add_zero]
          by_cases h : η = θ
          · rw [ite_eq_left (by rw [h]), ite_eq_left h, mul_one]
          · rw [ite_eq_right (fun h' => h (Prod.mk.inj h').1.symm), ite_eq_right h, mul_zero]
        · have h : η ≠ θ := fun h => hη (h ▸ hθ)
          rw [ite_eq_right hη, ite_eq_right hη, ite_eq_right h, mul_one, zero_add]
    _ = _ := by
        rw [tsum_add, ENNReal.tsum_mul_right, tsum_eq_single θ fun η h => ite_eq_right h,
          ite_eq_left rfl]

/-- Fresh outcomes of a rehash are uniform on the surviving seeds. -/
theorem rehashLaw_apply_true_eq {ks : List (Fin U)} {θ θ' : Θ} (hθ : C.Good θ ks)
    (hθ' : C.Good θ' ks) (n : ℕ) :
    C.rehashLaw ks n (θ, true) = C.rehashLaw ks n (θ', true) := by
  induction n with
  | zero => simp [rehashLaw, PMF.pure_apply]
  | succ n ih =>
    rw [C.rehashLaw_succ_apply_true hθ, C.rehashLaw_succ_apply_true hθ', ih]
    simp [Probability.PMF.uniformOfFintype_apply]

/-- Every attempt of a rehash fails with probability at most `q` each, so the fallback is taken
with probability at most `q ^ n`. -/
theorem rehashLaw_stale_le {ks : List (Fin U)} {q : ℝ≥0∞}
    (hq : (Probability.PMF.uniformOfFintype Θ).toOuterMeasure {θ | ¬ C.Good θ ks} ≤ q) (n : ℕ) :
    (C.rehashLaw ks n).toOuterMeasure {x | x.2 = false} ≤ q ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, PMF.toOuterMeasure_apply, ← (C.rehashLaw ks 0).tsum_coe]
    exact tsum_le_tsum fun x => Set.indicator_le_self _ _ x
  | succ n ih =>
    rw [rehashLaw, PMF.toOuterMeasure_bind_apply, pow_succ']
    calc _ ≤ ∑' θ, Probability.PMF.uniformOfFintype Θ θ *
          ({θ | ¬ C.Good θ ks}.indicator (fun _ => q ^ n) θ) := by
          refine tsum_le_tsum fun θ => mul_le_mul' le_rfl ?_
          by_cases hθ : C.Good θ ks
          · rw [ite_eq_left hθ,
              Set.indicator_of_notMem (by simpa only [Set.mem_ofPred_eq, not_not])]
            simp
          · rw [ite_eq_right hθ, Set.indicator_of_mem (by simpa only [Set.mem_ofPred_eq])]
            exact ih
      _ = (Probability.PMF.uniformOfFintype Θ).toOuterMeasure {θ | ¬ C.Good θ ks} * q ^ n := by
          rw [PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right]
          refine tsum_congr fun θ => ?_
          by_cases hθ : θ ∈ {θ | ¬ C.Good θ ks}
          · rw [Set.indicator_of_mem hθ, Set.indicator_of_mem hθ]
          · rw [Set.indicator_of_notMem hθ, Set.indicator_of_notMem hθ, mul_zero, zero_mul]
      _ ≤ q * q ^ n := mul_le_mul' hq le_rfl

/-! ## The law of model states -/

/-- The law `μ` of the model state after a history that stored the keys `ks` and the dictionary
`d`. Every state stores them under a surviving seed. Fresh states are uniform on the surviving
seeds, and stale states, whose seed is a fallback, have probability at most
`|ks| · 2⁻ᵃᵗᵗᵉᵐᵖᵗˢ`. -/
structure DistInv (μ : PMF (Model Θ U)) (ks : List (Fin U)) (d : Dictionary.State U) : Prop where
  /-- Every state stores `ks` and `d` under a surviving seed. -/
  support : ∀ σ ∈ μ.support, σ.keys = ks ∧ σ.dict = d ∧ C.Good σ.seed ks
  /-- Fresh states are equally likely for all surviving seeds. -/
  uniform : ∀ θ θ', C.Good θ ks → C.Good θ' ks → μ ⟨θ, ks, d, true⟩ = μ ⟨θ', ks, d, true⟩
  /-- Stale states are rare. -/
  stale : μ.toOuterMeasure {σ | σ.fresh = false} ≤ ks.length * ((2 : ℝ≥0∞) ^ C.attempts)⁻¹

variable {C}

omit [Fintype Θ] [Nonempty Θ] in
theorem DistInv.eq_of_mem_support {μ : PMF (Model Θ U)} {ks : List (Fin U)}
    {d : Dictionary.State U} (h : C.DistInv μ ks d) {σ : Model Θ U} (hσ : σ ∈ μ.support) :
    σ = ⟨σ.seed, ks, d, σ.fresh⟩ := by
  obtain ⟨hk, hd, -⟩ := h.support σ hσ
  rw [← hk, ← hd]

/-- The model starts from a uniform fresh seed with no keys. -/
theorem distInv_init :
    C.DistInv ((Probability.PMF.uniformOfFintype Θ).map fun θ => ⟨θ, [], Dictionary.empty U, true⟩)
      [] (Dictionary.empty U) where
  support σ hσ := by
    obtain ⟨θ, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hσ
    exact ⟨rfl, rfl, C.good_nil θ⟩
  uniform θ θ' _ _ := by
    have hinj : Function.Injective fun θ : Θ => (⟨θ, [], Dictionary.empty U, true⟩ : Model Θ U) :=
      fun a b h => congrArg Model.seed h
    rw [Probability.PMF.map_apply_of_support fun x _ hx => hinj hx,
      Probability.PMF.map_apply_of_support fun x _ hx => hinj hx]
    simp [Probability.PMF.uniformOfFintype_apply]
  stale := by
    rw [PMF.toOuterMeasure_map_apply, List.length_nil, Nat.cast_zero, zero_mul]
    exact le_of_eq (by
      rw [PMF.toOuterMeasure_apply]
      exact tsum_eq_zero_iff.mpr fun θ => Set.indicator_of_notMem (by simp) _)

omit [Fintype Θ] [Nonempty Θ] in
/-- Fresh states: the sum over them is a sum over seeds. -/
theorem DistInv.tsum_fresh {μ : PMF (Model Θ U)} {ks : List (Fin U)} {d : Dictionary.State U}
    (h : C.DistInv μ ks d) (f : Model Θ U → ℝ≥0∞) :
    ∑' σ, μ σ * (if σ.fresh then f σ else 0) =
      ∑' θ, μ ⟨θ, ks, d, true⟩ * f ⟨θ, ks, d, true⟩ := by
  have hinj : Function.Injective fun θ : Θ => (⟨θ, ks, d, true⟩ : Model Θ U) :=
    fun a b h => congrArg Model.seed h
  refine ((hinj.tsum_eq (f := fun σ => μ σ * (if σ.fresh then f σ else 0)) ?_).symm.trans ?_)
  · intro σ hσ
    have hμ : μ σ ≠ 0 := left_ne_zero_of_mul hσ
    have hf : σ.fresh = true := by
      by_contra hf
      exact hσ (by simp [hf])
    refine ⟨σ.seed, ?_⟩
    rw [h.eq_of_mem_support ((PMF.mem_support_iff _ _).mpr hμ), hf]
  · simp

/-- **Fresh states weigh at most twice the uniform law**, when at least half of all seeds
survive. -/
theorem DistInv.apply_fresh_le {μ : PMF (Model Θ U)} {ks : List (Fin U)}
    {d : Dictionary.State U} (h : C.DistInv μ ks d)
    (hhalf : 2⁻¹ ≤ (Probability.PMF.uniformOfFintype Θ).toOuterMeasure {θ | C.Good θ ks})
    (θ : Θ) : μ ⟨θ, ks, d, true⟩ ≤ 2 * Probability.PMF.uniformOfFintype Θ θ := by
  by_cases hθ : C.Good θ ks
  · set c := μ ⟨θ, ks, d, true⟩
    -- the fresh states of surviving seeds all weigh `c`, and weigh at most `1` together
    have hmass : c * ∑' η, ({η | C.Good η ks}.indicator (fun _ => 1) η) ≤ 1 := by
      rw [← ENNReal.tsum_mul_left]
      calc _ ≤ ∑' η, μ ⟨η, ks, d, true⟩ := by
            refine tsum_le_tsum fun η => ?_
            by_cases hη : C.Good η ks
            · rw [Set.indicator_of_mem (by exact hη), mul_one, h.uniform η θ hη hθ]
            · rw [Set.indicator_of_notMem (by exact hη), mul_zero]
              exact zero_le
        _ ≤ ∑' σ, μ σ := tsum_comp_le_tsum_of_injective
            (fun a b h => congrArg Model.seed h) _
        _ = 1 := μ.tsum_coe
    have hcard : (Fintype.card Θ : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hunif : (Probability.PMF.uniformOfFintype Θ).toOuterMeasure {η | C.Good η ks} =
        (Fintype.card Θ : ℝ≥0∞)⁻¹ * ∑' η, ({η | C.Good η ks}.indicator (fun _ => 1) η) := by
      rw [PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_left]
      refine tsum_congr fun η => ?_
      by_cases hη : C.Good η ks
      · rw [Set.indicator_of_mem (by exact hη), Set.indicator_of_mem (by exact hη), mul_one,
          Probability.PMF.uniformOfFintype_apply]
      · rw [Set.indicator_of_notMem (by exact hη), Set.indicator_of_notMem (by exact hη), mul_zero]
    rw [Probability.PMF.uniformOfFintype_apply]
    calc c = c * 1 := (mul_one c).symm
      _ ≤ c * (2 * (2⁻¹ : ℝ≥0∞)) := by rw [ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]
      _ ≤ c * (2 * ((Fintype.card Θ : ℝ≥0∞)⁻¹ *
            ∑' η, ({η | C.Good η ks}.indicator (fun _ => 1) η))) := by
          rw [← hunif]
          gcongr
      _ = 2 * (Fintype.card Θ : ℝ≥0∞)⁻¹ *
            (c * ∑' η, ({η | C.Good η ks}.indicator (fun _ => 1) η)) := by ring
      _ ≤ 2 * (Fintype.card Θ : ℝ≥0∞)⁻¹ * 1 := by gcongr
      _ = _ := mul_one _
  · have : μ ⟨θ, ks, d, true⟩ = 0 := by
      by_contra hne
      exact hθ (h.support _ ((PMF.mem_support_iff _ _).mpr hne)).2.2
    rw [this]
    exact zero_le

/-- **An expectation under the invariant** is at most twice the uniform expectation over
surviving seeds, plus the stale probability times a bound on the expectand. -/
theorem DistInv.tsum_mul_le {μ : PMF (Model Θ U)} {ks : List (Fin U)} {d : Dictionary.State U}
    (h : C.DistInv μ ks d)
    (hhalf : 2⁻¹ ≤ (Probability.PMF.uniformOfFintype Θ).toOuterMeasure {θ | C.Good θ ks})
    (f : Model Θ U → ℝ≥0∞) {W : ℝ≥0∞} (hW : ∀ σ ∈ μ.support, f σ ≤ W) :
    ∑' σ, μ σ * f σ ≤
      2 * ∑' θ, Probability.PMF.uniformOfFintype Θ θ *
          (if C.Good θ ks then f ⟨θ, ks, d, true⟩ else 0) +
        ks.length * ((2 : ℝ≥0∞) ^ C.attempts)⁻¹ * W := by
  have hsplit : ∀ σ : Model Θ U, μ σ * f σ =
      μ σ * (if σ.fresh then f σ else 0) + μ σ * (if σ.fresh then 0 else f σ) := by
    intro σ
    cases σ.fresh <;> simp
  simp only [hsplit]
  rw [tsum_add, h.tsum_fresh]
  gcongr ?_ + ?_
  · rw [← ENNReal.tsum_mul_left]
    refine tsum_le_tsum fun θ => ?_
    by_cases hθ : C.Good θ ks
    · rw [ite_eq_left hθ, ← mul_assoc]
      exact mul_le_mul' (h.apply_fresh_le hhalf θ) le_rfl
    · have : μ ⟨θ, ks, d, true⟩ = 0 := by
        by_contra hne
        exact hθ (h.support _ ((PMF.mem_support_iff _ _).mpr hne)).2.2
      rw [this, zero_mul]
      exact zero_le
  · calc _ ≤ ∑' σ, {σ : Model Θ U | σ.fresh = false}.indicator μ σ * W := by
          refine tsum_le_tsum fun σ => ?_
          by_cases hf : σ.fresh = true
          · rw [hf]
            simp
          · rw [Set.indicator_of_mem (by simpa using hf), ite_eq_right (by simpa using hf)]
            by_cases hσ : σ ∈ μ.support
            · exact mul_le_mul' le_rfl (hW σ hσ)
            · rw [(PMF.apply_eq_zero_iff _ _).mpr hσ, zero_mul, zero_mul]
      _ = μ.toOuterMeasure {σ | σ.fresh = false} * W := by
          rw [ENNReal.tsum_mul_right, PMF.toOuterMeasure_apply]
      _ ≤ _ := mul_le_mul' h.stale le_rfl

/-! ## Survival under a cuckoo hash pair -/

variable {n_max Cw Cr : ℕ}

/-- Under a cuckoo hash pair, a seed fails `n_max` distinct keys with probability at most a
half. -/
theorem not_good_le_half
    (hC : IsCuckooHashPair (Probability.PMF.uniformOfFintype Θ) C.hash₁ C.hash₂ n_max C.maxLoop
      Cw Cr)
    {ks : List (Fin U)} (hnd : ks.Nodup) (hlen : ks.length ≤ n_max) :
    (Probability.PMF.uniformOfFintype Θ).toOuterMeasure {θ | ¬ C.Good θ ks} ≤ 2⁻¹ := by
  have hS : ks.toFinset.card ≤ n_max := (List.toFinset_card_le ks).trans hlen
  refine le_trans (MeasureTheory.measure_mono fun θ hθ => ?_)
    ((hC.rehash_prob_le_half ks.toFinset hS).trans_eq (one_div 2))
  intro hgood
  exact hθ ((mem_survivingSeeds (h₁ := C.hash₁) (h₂ := C.hash₂)).mp
    (mem_survivingSeeds_of_goodForSet hnd (fun u hu => List.mem_toFinset.mpr hu) hgood))

/-- Under a cuckoo hash pair, at least half of all seeds survive `n_max` distinct keys. -/
theorem half_le_good
    (hC : IsCuckooHashPair (Probability.PMF.uniformOfFintype Θ) C.hash₁ C.hash₂ n_max C.maxLoop
      Cw Cr)
    {ks : List (Fin U)} (hnd : ks.Nodup) (hlen : ks.length ≤ n_max) :
    2⁻¹ ≤ (Probability.PMF.uniformOfFintype Θ).toOuterMeasure {θ | C.Good θ ks} := by
  have hsum : (Probability.PMF.uniformOfFintype Θ).toOuterMeasure {θ | C.Good θ ks} +
      (Probability.PMF.uniformOfFintype Θ).toOuterMeasure {θ | ¬ C.Good θ ks} = 1 := by
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← tsum_add,
      ← (Probability.PMF.uniformOfFintype Θ).tsum_coe]
    exact tsum_congr fun θ => Set.indicator_self_add_compl_apply _ _ _
  have h := C.not_good_le_half hC hnd hlen
  refine ENNReal.le_of_add_le_add_right (ENNReal.inv_ne_top.mpr two_ne_zero) ?_
  rw [ENNReal.inv_two_add_inv_two, ← hsum]
  gcongr

omit [Fintype Θ] [Nonempty Θ] in
/-- The displacement rounds of an insertion are at most the worst-case walk of
`IsCuckooHashPair`. -/
theorem rounds_le_cuckooWalkRounds (θ : Θ) {ks : List (Fin U)} (hnd : ks.Nodup) (u : Fin U) :
    C.rounds θ ks u ≤ cuckooWalkRounds (C.hash₁ θ) (C.hash₂ θ) C.maxLoop ks.toFinset u := by
  unfold rounds
  cases hr : C.replay θ ks with
  | none => exact Nat.zero_le _
  | some T =>
    exact evictRounds_le_cuckooWalkRounds
      (pureReplay_validPlacement hnd (fun u hu => List.mem_toFinset.mpr hu) hr) u _

/-! ## One operation -/

variable {V : ℕ}

/-- The law of the model state after one operation from the law `μ`. -/
noncomputable abbrev next (μ : PMF (Model Θ U)) (o : Dictionary.Op U) : PMF (Model Θ U) :=
  (μ.bind fun σ => (C.spec V n_max).law o σ).map Prod.snd

theorem next_get (μ : PMF (Model Θ U)) (u : Fin U) :
    C.next (V := V) (n_max := n_max) μ (.get u) = μ := by
  simp only [next, PMF.map_bind, PMF.pure_map, PMF.bind_pure]

theorem next_insert (μ : PMF (Model Θ U)) (u : Fin U) (v : ℕ) :
    C.next (V := V) (n_max := n_max) μ (.insert u v) = μ.bind fun σ => C.insertLaw σ u v := by
  simp only [next, PMF.map_bind, PMF.map_comp]
  exact congrArg μ.bind (funext fun σ => PMF.map_id _)

/-- Updating a present key keeps the invariant. -/
theorem DistInv.insert_present {μ : PMF (Model Θ U)} {ks : List (Fin U)}
    {d : Dictionary.State U} (h : C.DistInv μ ks d) {u : Fin U} (hu : (d u).isSome) (v : ℕ) :
    C.DistInv (μ.bind fun σ => C.insertLaw σ u v) ks (Function.update d u (some v)) := by
  set g : Model Θ U → Model Θ U := fun σ => { σ with dict := Function.update σ.dict u (some v) }
  have hμ : (μ.bind fun σ => C.insertLaw σ u v) = μ.map g := by
    rw [PMF.map]
    refine Probability.PMF.bind_congr_on_support _ _ _ fun σ hσ => ?_
    rw [h.eq_of_mem_support hσ]
    simp [insertLaw, hu, g]
  rw [hμ]
  refine ⟨fun σ hσ => ?_, fun θ θ' hθ hθ' => ?_, ?_⟩
  · obtain ⟨σ₀, hσ₀, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hσ
    obtain ⟨hk, hd, hg⟩ := h.support σ₀ hσ₀
    exact ⟨hk, by simp [g, hd], hg⟩
  · have key : ∀ η : Θ, (μ.map g) ⟨η, ks, Function.update d u (some v), true⟩ =
        μ ⟨η, ks, d, true⟩ := fun η =>
      Probability.PMF.map_apply_of_support (f := g) (a := ⟨η, ks, d, true⟩) fun x hx hgx => by
        rw [h.eq_of_mem_support hx] at hgx ⊢
        simp only [g, Model.mk.injEq] at hgx
        rw [hgx.1, hgx.2.2.2]
    rw [key, key, h.uniform θ θ' hθ hθ']
  · rw [PMF.toOuterMeasure_map_apply]
    exact h.stale

/-- Weight of a fresh state after inserting a new key: the fresh state that kept its seed, and
the fresh outcomes of the rehashes. -/
theorem DistInv.bind_insertLaw_apply_fresh {μ : PMF (Model Θ U)} {ks : List (Fin U)}
    {d : Dictionary.State U} (h : C.DistInv μ ks d) {u : Fin U} (hu : d u = none) (v : ℕ)
    {θ : Θ} (hθ : C.Good θ (ks ++ [u])) :
    (μ.bind fun σ => C.insertLaw σ u v) ⟨θ, ks ++ [u], Function.update d u (some v), true⟩ =
      μ ⟨θ, ks, d, true⟩ +
        (∑' σ, μ σ * (if C.Good σ.seed (ks ++ [u]) then 0 else 1)) *
          C.rehashLaw (ks ++ [u]) C.attempts (θ, true) := by
  classical
  set a : Model Θ U := ⟨θ, ks, d, true⟩
  set R := C.rehashLaw (ks ++ [u]) C.attempts (θ, true)
  rw [PMF.bind_apply]
  calc _ = ∑' σ, (μ σ * (if σ = a then 1 else 0) +
        μ σ * (if C.Good σ.seed (ks ++ [u]) then 0 else 1) * R) := by
        refine tsum_congr fun σ => ?_
        by_cases hσ : σ ∈ μ.support
        · have hσeq := h.eq_of_mem_support hσ
          have hlaw : C.insertLaw σ u v = if C.Good σ.seed (ks ++ [u]) then
              PMF.pure ⟨σ.seed, ks ++ [u], Function.update d u (some v), σ.fresh⟩
              else (C.rehashLaw (ks ++ [u]) C.attempts).map
                (rehashed Θ (ks ++ [u]) (Function.update d u (some v))) := by
            rw [hσeq]
            simp [insertLaw, hu]
          rw [hlaw]
          by_cases hg : C.Good σ.seed (ks ++ [u])
          · rw [ite_eq_left hg, ite_eq_left hg, mul_zero, zero_mul, add_zero, PMF.pure_apply]
            by_cases hσa : σ = a
            · subst hσa
              simp [a]
            · rw [ite_eq_right hσa, ite_eq_right fun he => hσa ?_]
              rw [hσeq]
              simp only [Model.mk.injEq] at he
              rw [← he.1, ← he.2.2.2]
          · have hσa : σ ≠ a := fun he => hg (he ▸ hθ)
            rw [ite_eq_right hg, ite_eq_right hg, ite_eq_right hσa, mul_zero, zero_add, mul_one,
              show (⟨θ, ks ++ [u], Function.update d u (some v), true⟩ : Model Θ U) =
                rehashed Θ (ks ++ [u]) (Function.update d u (some v)) (θ, true) from rfl,
              Probability.PMF.map_apply_of_support fun x _ hx => rehashed_injective _ _ hx]
        · rw [(PMF.apply_eq_zero_iff _ _).mpr hσ]
          simp
    _ = _ := by
        rw [tsum_add, ENNReal.tsum_mul_right, tsum_eq_single a fun σ hσ => by rw [ite_eq_right hσ,
          mul_zero], ite_eq_left rfl, mul_one]

/-- Inserting a new key keeps the invariant, given a fallback seed that survives and a rehash
that fails with probability at most a half per attempt. -/
theorem DistInv.insert_new {μ : PMF (Model Θ U)} {ks : List (Fin U)}
    {d : Dictionary.State U} (h : C.DistInv μ ks d) {u : Fin U} (hu : d u = none) (v : ℕ)
    (hfb : C.Good (C.fallback (ks ++ [u])) (ks ++ [u]))
    (hhalf : (Probability.PMF.uniformOfFintype Θ).toOuterMeasure
      {θ | ¬ C.Good θ (ks ++ [u])} ≤ 2⁻¹) :
    C.DistInv (μ.bind fun σ => C.insertLaw σ u v) (ks ++ [u]) (Function.update d u (some v)) := by
  have hlaw : ∀ σ ∈ μ.support, C.insertLaw σ u v = if C.Good σ.seed (ks ++ [u]) then
      PMF.pure ⟨σ.seed, ks ++ [u], Function.update d u (some v), σ.fresh⟩
      else (C.rehashLaw (ks ++ [u]) C.attempts).map
        (rehashed Θ (ks ++ [u]) (Function.update d u (some v))) := fun σ hσ => by
    rw [h.eq_of_mem_support hσ]
    simp [insertLaw, hu]
  refine ⟨fun σ hσ => ?_, fun θ θ' hθ hθ' => ?_, ?_⟩
  · obtain ⟨σ₀, hσ₀, hσ⟩ := (PMF.mem_support_bind_iff _ _ _).mp hσ
    rw [hlaw σ₀ hσ₀] at hσ
    split_ifs at hσ with hg
    · rw [PMF.mem_support_pure_iff] at hσ
      subst hσ
      exact ⟨rfl, rfl, hg⟩
    · obtain ⟨x, hx, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hσ
      exact ⟨rfl, rfl, C.good_of_mem_support_rehashLaw hfb hx⟩
  · rw [h.bind_insertLaw_apply_fresh hu v hθ, h.bind_insertLaw_apply_fresh hu v hθ',
      h.uniform θ θ' (Good.of_append C hθ) (Good.of_append C hθ'),
      C.rehashLaw_apply_true_eq hθ hθ']
  · rw [PMF.toOuterMeasure_bind_apply, List.length_append, List.length_singleton, Nat.cast_add,
      Nat.cast_one, add_mul, one_mul]
    calc _ ≤ ∑' σ, μ σ * ({σ : Model Θ U | σ.fresh = false}.indicator (fun _ => 1) σ +
          ((2 : ℝ≥0∞) ^ C.attempts)⁻¹) := by
          refine tsum_le_tsum fun σ => ?_
          by_cases hσ : σ ∈ μ.support
          · refine mul_le_mul' le_rfl ?_
            rw [hlaw σ hσ]
            split_ifs with hg
            · rw [PMF.toOuterMeasure_pure_apply]
              by_cases hf : σ.fresh = false
              · rw [ite_eq_left (by exact hf), Set.indicator_of_mem (by exact hf)]
                exact le_self_add
              · rw [ite_eq_right (by exact hf)]
                exact zero_le
            · rw [PMF.toOuterMeasure_map_apply, ENNReal.inv_pow]
              refine le_add_left ((C.rehashLaw_stale_le hhalf _).trans_eq ?_)
              rfl
          · rw [(PMF.apply_eq_zero_iff _ _).mpr hσ, zero_mul, zero_mul]
      _ = μ.toOuterMeasure {σ | σ.fresh = false} + ((2 : ℝ≥0∞) ^ C.attempts)⁻¹ := by
          simp only [mul_add, tsum_add, ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]
          rw [PMF.toOuterMeasure_apply]
          congr 1
          refine tsum_congr fun σ => ?_
          by_cases hf : σ.fresh = false
          · rw [Set.indicator_of_mem (by exact hf), Set.indicator_of_mem (by exact hf), mul_one]
          · rw [Set.indicator_of_notMem (by exact hf), Set.indicator_of_notMem (by exact hf),
              mul_zero]
      _ ≤ _ := add_le_add_left h.stale _

/-! ## Expected charges -/

/-- `a / b ≤ ⌊a / b⌋ + 1` in `ℝ≥0∞`. -/
private theorem div_le_natDiv_add_one (a b : ℕ) (hb : 0 < b) :
    (a : ℝ≥0∞) / b ≤ ((a / b : ℕ) : ℝ≥0∞) + 1 := by
  refine ENNReal.div_le_of_le_mul ?_
  have h : a < a / b * b + b := Nat.lt_div_mul_add hb
  exact_mod_cast (show a ≤ (a / b + 1) * b by rw [Nat.add_mul, one_mul]; exact h.le)

/-- **The expected charge of one operation** under the invariant is at most `opBound`. -/
theorem DistInv.tsum_charge_le {K : Charges}
    (hC : IsCuckooHashPair (Probability.PMF.uniformOfFintype Θ) C.hash₁ C.hash₂ n_max C.maxLoop
      Cw Cr)
    (hF : n_max * (K.round * C.maxLoop + K.rehash) ≤ 2 ^ C.attempts)
    {μ : PMF (Model Θ U)} {ks : List (Fin U)} {d : Dictionary.State U} (h : C.DistInv μ ks d)
    (hag : Agree ks d) (hlen : ks.length ≤ n_max) {o : Dictionary.Op U}
    (hv : Dictionary.valid V n_max d o) :
    ∑' σ, μ σ * (C.charge K σ o : ℝ≥0∞) ≤ C.opBound K n_max Cw Cr o := by
  -- charges only depend on the state through the support
  have hconst : ∀ c : ℕ, (∀ σ ∈ μ.support, C.charge K σ o = c) →
      ∑' σ, μ σ * (C.charge K σ o : ℝ≥0∞) = c := fun c hc => by
    rw [← one_mul (c : ℝ≥0∞), ← μ.tsum_coe, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun σ => ?_
    by_cases hσ : σ ∈ μ.support
    · rw [hc σ hσ]
    · rw [(PMF.apply_eq_zero_iff _ _).mpr hσ, zero_mul, zero_mul]
  cases o with
  | get u =>
    rw [hconst K.get fun _ _ => rfl]
    rfl
  | insert u v =>
    by_cases hu : (d u).isSome
    · rw [hconst K.present fun σ hσ => by
        rw [h.eq_of_mem_support hσ]
        simp [charge, hu]]
      exact_mod_cast le_max_left _ _
    · have hu' : d u = none := by simpa using hu
      have hnot : u ∉ ks := fun hm => hu ((hag.mem_iff u).mp hm)
      have hlt : ks.length < n_max := by
        rw [hag.length_eq]
        rcases hv.1 with h₁ | h₁
        · exact h₁
        · exact absurd h₁ hu
      set ks' := ks ++ [u]
      set W : ℕ := K.round * C.maxLoop + K.rehash
      set g : Model Θ U → ℝ≥0∞ := fun σ =>
        ((K.round * C.rounds σ.seed ks u + if C.Good σ.seed ks' then 0 else K.rehash : ℕ) : ℝ≥0∞)
      have hcharge : ∀ σ ∈ μ.support, (C.charge K σ (.insert u v) : ℝ≥0∞) = K.insert + g σ := by
        intro σ hσ
        rw [h.eq_of_mem_support hσ]
        simp only [charge, hu', Option.isSome_none, Bool.false_eq_true, ite_false, g]
        push_cast
        ring
      have hgW : ∀ σ ∈ μ.support, g σ ≤ W := by
        intro σ _
        exact Nat.cast_le.mpr (Nat.add_le_add (Nat.mul_le_mul_left _ (C.rounds_le _ _ _))
          (by split_ifs <;> omega))
      -- the uniform expectation of the walk and of the rehash indicator
      have hunif : ∑' θ, Probability.PMF.uniformOfFintype Θ θ *
          (if C.Good θ ks then g ⟨θ, ks, d, true⟩ else 0) ≤
          K.round * Cw + K.rehash * ((Cr : ℝ≥0∞) /
            ((max n_max 1 : ℝ≥0∞) * (max C.maxLoop 1 : ℝ≥0∞))) := by
        have hwalk := hC.expected_walk_le ks.toFinset u
          (by rw [List.toFinset_card_of_nodup hag.nodup]; exact hlt)
          (by simpa using hnot)
        have hstep := hC.step_rehash_prob_le ks u hag.nodup hlt hnot
        calc _ ≤ ∑' θ, (Probability.PMF.uniformOfFintype Θ θ * (K.round *
              (cuckooWalkRounds (C.hash₁ θ) (C.hash₂ θ) C.maxLoop ks.toFinset u : ℝ≥0∞)) +
              K.rehash * {θ | (pureReplay (C.hash₁ θ) (C.hash₂ θ) C.maxLoop ks).isSome ∧
                (pureReplay (C.hash₁ θ) (C.hash₂ θ) C.maxLoop (ks ++ [u])).isNone}.indicator
                  (Probability.PMF.uniformOfFintype Θ) θ) := by
              refine tsum_le_tsum fun θ => ?_
              by_cases hθ : C.Good θ ks
              · rw [ite_eq_left hθ]
                have hr : (C.rounds θ ks u : ℝ≥0∞) ≤
                    cuckooWalkRounds (C.hash₁ θ) (C.hash₂ θ) C.maxLoop ks.toFinset u :=
                  Nat.cast_le.mpr (C.rounds_le_cuckooWalkRounds θ hag.nodup u)
                by_cases hθ' : C.Good θ ks'
                · simp only [g, ite_eq_left hθ', Nat.add_zero, Nat.cast_mul]
                  exact le_add_right (mul_le_mul' le_rfl (mul_le_mul' le_rfl hr))
                · have hmem : θ ∈ {θ | (pureReplay (C.hash₁ θ) (C.hash₂ θ) C.maxLoop ks).isSome ∧
                      (pureReplay (C.hash₁ θ) (C.hash₂ θ) C.maxLoop (ks ++ [u])).isNone} :=
                    ⟨hθ, by simpa [Good, replay] using hθ'⟩
                  simp only [g, ite_eq_right hθ', Nat.cast_add, Nat.cast_mul, mul_add,
                    Set.indicator_of_mem hmem]
                  rw [mul_comm (Probability.PMF.uniformOfFintype Θ θ) (K.rehash : ℝ≥0∞)]
                  exact add_le_add (mul_le_mul' le_rfl (mul_le_mul' le_rfl hr)) le_rfl
              · rw [ite_eq_right hθ, mul_zero]
                exact zero_le
          _ = K.round * ∑' θ, Probability.PMF.uniformOfFintype Θ θ *
                (cuckooWalkRounds (C.hash₁ θ) (C.hash₂ θ) C.maxLoop ks.toFinset u : ℝ≥0∞) +
              K.rehash * (Probability.PMF.uniformOfFintype Θ).toOuterMeasure
                {θ | (pureReplay (C.hash₁ θ) (C.hash₂ θ) C.maxLoop ks).isSome ∧
                  (pureReplay (C.hash₁ θ) (C.hash₂ θ) C.maxLoop (ks ++ [u])).isNone} := by
              rw [tsum_add, PMF.toOuterMeasure_apply, ENNReal.tsum_mul_left]
              congr 1
              rw [← ENNReal.tsum_mul_left]
              exact tsum_congr fun θ => by ring
          _ ≤ _ := by gcongr
      -- the stale states cost at most one unit
      have hstale : (ks.length : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ C.attempts)⁻¹ * W ≤ 1 := by
        have hpow : (2 : ℝ≥0∞) ^ C.attempts ≠ 0 := pow_ne_zero _ two_ne_zero
        have hpow' : (2 : ℝ≥0∞) ^ C.attempts ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
        calc _ = (ks.length * W : ℕ) * ((2 : ℝ≥0∞) ^ C.attempts)⁻¹ := by push_cast; ring
          _ ≤ ((2 ^ C.attempts : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ C.attempts)⁻¹ := by
              gcongr
              exact (Nat.mul_le_mul_right _ hlen).trans hF
          _ = 1 := by push_cast; exact ENNReal.mul_inv_cancel hpow hpow'
      -- the rehash term, rounded up
      have hD : 0 < max n_max 1 * max C.maxLoop 1 := Nat.mul_pos (by omega) (by omega)
      have hrh : 2 * (K.rehash * ((Cr : ℝ≥0∞) /
          ((max n_max 1 : ℝ≥0∞) * (max C.maxLoop 1 : ℝ≥0∞)))) ≤
          ((2 * K.rehash * Cr / (max n_max 1 * max C.maxLoop 1) : ℕ) : ℝ≥0∞) + 1 := by
        refine le_trans (le_of_eq ?_) (div_le_natDiv_add_one _ _ hD)
        push_cast
        rw [(Nat.mono_cast (α := ℝ≥0∞)).map_max, (Nat.mono_cast (α := ℝ≥0∞)).map_max, Nat.cast_one]
        simp only [mul_div_assoc, mul_assoc]
      calc ∑' σ, μ σ * (C.charge K σ (.insert u v) : ℝ≥0∞)
          = ∑' σ, μ σ * (K.insert + g σ) := by
            refine tsum_congr fun σ => ?_
            by_cases hσ : σ ∈ μ.support
            · rw [hcharge σ hσ]
            · rw [(PMF.apply_eq_zero_iff _ _).mpr hσ, zero_mul, zero_mul]
        _ = K.insert + ∑' σ, μ σ * g σ := by
            rw [show ∑' σ, μ σ * ((K.insert : ℝ≥0∞) + g σ) =
                ∑' σ, μ σ * (K.insert : ℝ≥0∞) + ∑' σ, μ σ * g σ from by
                  rw [← tsum_add]; exact tsum_congr fun σ => mul_add _ _ _,
              ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]
        _ ≤ K.insert + (2 * ∑' θ, Probability.PMF.uniformOfFintype Θ θ *
              (if C.Good θ ks then g ⟨θ, ks, d, true⟩ else 0) +
            ks.length * ((2 : ℝ≥0∞) ^ C.attempts)⁻¹ * W) := by
            gcongr
            exact h.tsum_mul_le (C.half_le_good hC hag.nodup hlen) g hgW
        _ ≤ K.insert + (2 * (K.round * Cw + K.rehash * ((Cr : ℝ≥0∞) /
              ((max n_max 1 : ℝ≥0∞) * (max C.maxLoop 1 : ℝ≥0∞)))) + 1) := by gcongr
        _ ≤ ((K.insert + 2 * K.round * Cw +
              2 * K.rehash * Cr / (max n_max 1 * max C.maxLoop 1) + 2 : ℕ) : ℝ≥0∞) := by
            rw [mul_add]
            calc _ ≤ (K.insert : ℝ≥0∞) + (2 * (K.round * Cw) +
                  (((2 * K.rehash * Cr / (max n_max 1 * max C.maxLoop 1) : ℕ) : ℝ≥0∞) + 1) +
                    1) := by
                  gcongr
              _ = _ := by push_cast; ring
        _ ≤ C.opBound K n_max Cw Cr (.insert u v) := by
            exact_mod_cast le_max_right _ _

/-- **Expected charges of a client.** From a law satisfying the invariant, the expected charge of
an admissible client is at most `opBound` per operation of its history. -/
theorem tsum_expectedCost_le (K : Charges)
    (hC : IsCuckooHashPair (Probability.PMF.uniformOfFintype Θ) C.hash₁ C.hash₂ n_max C.maxLoop
      Cw Cr)
    (hfb : ∀ ks : List (Fin U), ks.Nodup → ks.length ≤ n_max → C.Good (C.fallback ks) ks)
    (hF : n_max * (K.round * C.maxLoop + K.rehash) ≤ 2 ^ C.attempts)
    {α : Type} (p : OracleComp (Dictionary.Op.Result (U := U)) α) :
    ∀ {μ : PMF (Model Θ U)} {ks : List (Fin U)} {d : Dictionary.State U}, C.DistInv μ ks d →
      Agree ks d → ks.length ≤ n_max →
      (Dictionary.spec U V n_max).ValidHistory d ((Dictionary.spec U V n_max).clientHistory d p) →
      ∑' σ, μ σ * (C.spec V n_max).expectedCost (C.charge K) p σ ≤
        ((Dictionary.spec U V n_max).totalCost (fun _ => C.opBound K n_max Cw Cr) d
          ((Dictionary.spec U V n_max).clientHistory d p) : ℝ≥0∞) := by
  induction p with
  | pure a =>
    intro μ ks d _ _ _ _
    simp
  | liftBind o k ih =>
    intro μ ks d h hag hlen hv
    obtain ⟨hvo, hvk⟩ := hv
    -- the next law, keys and dictionary
    obtain ⟨ks', hμ', hag', hlen'⟩ : ∃ ks', C.DistInv (C.next (V := V) (n_max := n_max) μ o) ks'
        ((Dictionary.spec U V n_max).stepFn d o).1 ∧
        Agree ks' ((Dictionary.spec U V n_max).stepFn d o).1 ∧ ks'.length ≤ n_max := by
      cases o with
      | get u => exact ⟨ks, by rw [next_get]; exact h, hag, hlen⟩
      | insert u v =>
        rw [next_insert]
        by_cases hu : (d u).isSome
        · exact ⟨ks, h.insert_present hu v, hag.update hu v, hlen⟩
        · have hu' : d u = none := by simpa using hu
          have hlt : ks.length < n_max := by
            rw [hag.length_eq]
            rcases hvo.1 with h₁ | h₁
            · exact h₁
            · exact absurd h₁ hu
          have hag' := hag.append hu' v
          have hlen' : (ks ++ [u]).length ≤ n_max := by simpa using hlt
          exact ⟨ks ++ [u], h.insert_new hu' v (hfb _ hag'.nodup hlen')
            (C.not_good_le_half hC hag'.nodup hlen'), hag', hlen'⟩
    -- the answer is the dictionary's on every outcome
    have hans : ∀ x ∈ (μ.bind fun σ => (C.spec V n_max).law o σ).support,
        x.1 = ((Dictionary.spec U V n_max).stepFn d o).2 := by
      intro x hx
      obtain ⟨σ, hσ, hx⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
      cases o with
      | get u =>
        rw [spec_law_get, PMF.mem_support_pure_iff] at hx
        rw [hx]
        exact congrArg (· u) (h.support σ hσ).2.1
      | insert u v => rfl
    have hrest : ∑' σ, μ σ * ∑' x, (C.spec V n_max).law o σ x *
          (C.spec V n_max).expectedCost (C.charge K) (k x.1) x.2 =
        ∑' σ, C.next (V := V) (n_max := n_max) μ o σ *
          (C.spec V n_max).expectedCost (C.charge K)
            (k ((Dictionary.spec U V n_max).stepFn d o).2) σ := by
      rw [← Probability.PMF.tsum_bind_mul, next, Probability.PMF.tsum_map_mul]
      refine tsum_congr fun x => ?_
      by_cases hx : x ∈ (μ.bind fun σ => (C.spec V n_max).law o σ).support
      · rw [hans x hx]
      · rw [(PMF.apply_eq_zero_iff _ _).mpr hx, zero_mul, zero_mul]
    simp only [RandomizedSpec.expectedCost_liftBind, mul_add]
    rw [tsum_add, hrest]
    change _ ≤ ((C.opBound K n_max Cw Cr o + (Dictionary.spec U V n_max).totalCost
      (fun _ => C.opBound K n_max Cw Cr) ((Dictionary.spec U V n_max).stepFn d o).1
      ((Dictionary.spec U V n_max).clientHistory ((Dictionary.spec U V n_max).stepFn d o).1
        (k ((Dictionary.spec U V n_max).stepFn d o).2)) : ℕ) : ℝ≥0∞)
    rw [Nat.cast_add]
    exact add_le_add (h.tsum_charge_le hC hF hag hlen hvo) (ih _ hμ' hag' hlen' hvk)

/-- **Expected charges from the start.** After drawing a uniform seed, the expected charge of an
admissible client of the model is at most `opBound` per operation of its history. -/
theorem expectedCost_le (K : Charges)
    (hC : IsCuckooHashPair (Probability.PMF.uniformOfFintype Θ) C.hash₁ C.hash₂ n_max C.maxLoop
      Cw Cr)
    (hfb : ∀ ks : List (Fin U), ks.Nodup → ks.length ≤ n_max → C.Good (C.fallback ks) ks)
    (hF : n_max * (K.round * C.maxLoop + K.rehash) ≤ 2 ^ C.attempts)
    {α : Type} (p : OracleComp (Dictionary.Op.Result (U := U)) α)
    (hv : (Dictionary.spec U V n_max).ValidHistory (Dictionary.empty U)
      ((Dictionary.spec U V n_max).clientHistory (Dictionary.empty U) p)) :
    ∑' θ, Probability.PMF.uniformOfFintype Θ θ *
        (C.spec V n_max).expectedCost (C.charge K) p ⟨θ, [], Dictionary.empty U, true⟩ ≤
      ((Dictionary.spec U V n_max).totalCost (fun _ => C.opBound K n_max Cw Cr)
        (Dictionary.empty U) ((Dictionary.spec U V n_max).clientHistory (Dictionary.empty U) p) :
          ℝ≥0∞) := by
  rw [← Probability.PMF.tsum_map_mul]
  exact C.tsum_expectedCost_le K hC hfb hF p C.distInv_init agree_nil (Nat.zero_le _) hv

end Scheme

end Cslib.DataStructure.Dictionary.CuckooHashing
