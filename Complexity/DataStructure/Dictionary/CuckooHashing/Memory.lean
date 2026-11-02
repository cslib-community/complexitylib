/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.CuckooHashing.Memory.Rehash
import Complexity.DataStructure.Dictionary.CuckooHashing
import Complexity.Probability.PMF.Expect
import Complexity.Probability.PMF.Map

/-!
# Cuckoo hashing over the memory oracle

Pagh and Rodler's cuckoo hashing [PaghRodler2004] over `Memory.spec w` with private coins, as a
chain of two hops whose probability is done on the pure model:

1. `Scheme.dictRefinement`: the dictionary `Dictionary.spec U V n_max` refined by the seed-level
   model `Scheme.spec`
   (`Complexity/DataStructure/Dictionary/CuckooHashing/Model.lean`). Answers do not depend on the
   seeds.
2. `Layout.refinement`: the model refined by programs over memory with coins. A lookup probes two
   slots; an insertion runs its eviction walk and, if the walk does not settle, a rehash
   (`Layout.methods`). Each method realizes the model's law exactly (`Layout.methods_spec`), and
   costs at most the model's charge in expectation (`Layout.expectedAmortized`).

`run` allocates a table, draws its hash tables and serves a dictionary client. From any memory
with room for it, `run_correct` shows it answers as the dictionary does, and `expectedCost_run_le`
bounds its expected memory cost by the start plus `Scheme.opBound` per operation, through
`RandomizedRefinement.ExpectedAmortized.client` and the model's `Scheme.expectedCost_le`. The
latter is the only probabilistic argument, and it uses only `IsCuckooHashPair`: the walk and
rehash bounds of `Complexity/DataStructure/Dictionary/CuckooHashing.lean`, reused unchanged.
`run_tableBits` instantiates Pagh and Rodler's parameters, `tableBits` and `maxEvictions`, with
random hash tables (`isCuckooHashPair_uniform`).

The hand-stepped counterpart is
`Complexity/DataStructure/Dictionary/WordRAM/CuckooHashing.lean`, with a regime-switched
polynomial and double-tabulation family. With random hash tables as seeds, a rehash writes `2 U`
cells, so the expected charge of an insertion is `O(1 + U / (n_max · maxEvictions n_max))`
rather than `O(1)`; a memory implementation of that family would remove the `U` term. Executing
the memory programs on the word RAM is the separate realization step.

## Main definitions

* `Memory.Layout.methods`, `Memory.Layout.refinement`: the operations over memory and the
  distributional hop.
* `Memory.Layout.charges`: their charges in the model.
* `Memory.run`: allocate, draw the hash tables, and serve a client.
* `Memory.attemptsFor`: the number of rehash attempts at Pagh and Rodler's parameters.

## Main results

* `Memory.Layout.methods_spec`: each method realizes the model's law.
* `Memory.Layout.expectedAmortized`: memory costs are model charges in expectation.
* `Memory.run_correct`, `Memory.expectedCost_run_le`: correctness and expected cost from
  allocation.
* `Memory.run_tableBits`: both at Pagh and Rodler's parameters.

## References

* [R. Pagh and F. F. Rodler, "Cuckoo hashing"][PaghRodler2004] (8 December 2003 author manuscript,
  Section 2.3, "Analysis", pp. 6–10).
-/

@[expose] public section

namespace Cslib.DataStructure.Dictionary.CuckooHashing.Memory

open Cslib.WordRAM Cslib.DataStructure
open Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing
open Cslib.DataStructure.HashFamily.RandomTable (fill writeFrom tableOf)
open scoped ENNReal

variable {U b : ℕ}

namespace Layout

variable {n_max : ℕ} (L : Layout U b n_max) {w : ℕ} [NeZero U] {maxLoop : ℕ}

/-! ## The distributional hop -/

/-- The stored keys agree with the stored dictionary. -/
theorem Records.agree {s : Memory.State} (h : L.Records s) :
    Scheme.Agree (L.keyList s) (L.abs s).dict := by
  refine ⟨h.nodup, fun u => ?_⟩
  rw [abs_dict, dictOf_eq (by simp)]
  split_ifs with hu <;> simp [hu]

/-- The operations over memory with coins: a lookup, and an insertion followed by a rehash with
`attempts` attempts when its walk does not settle. -/
noncomputable def methods (maxLoop attempts : ℕ) :
    (o : Dictionary.Op U) → ProbOracleComp Memory.Op.Result (Dictionary.Op.Result o)
  | .get u => OracleComp.liftRight (L.getProg u)
  | .insert u v => OracleComp.liftRight (L.insertProg maxLoop u v) >>= fun need =>
      if need then L.rehash maxLoop attempts else pure ()

omit [NeZero U] in
/-- An insertion runs its deterministic part, then the rehash if one is needed. -/
theorem run_methods_insert (attempts : ℕ) (u : Fin U) (v : ℕ) (s : Memory.State) :
    (Memory.spec w).toRandomized.withCoins.run (L.methods maxLoop attempts (.insert u v)) s =
      (Memory.spec w).toRandomized.withCoins.run
        (if (Memory.spec w).clientResult s (L.insertProg maxLoop u v) then
          L.rehash maxLoop attempts else pure ())
        ((Memory.spec w).clientState s (L.insertProg maxLoop u v)) := by
  rw [methods, RandomizedSpec.run_bind, run_liftRight, PMF.pure_bind]

omit [NeZero U] in
private theorem map_unit {σ τ : Type} (μ : PMF (Unit × σ)) (f : σ → τ) :
    μ.map (fun (a, e) => (a, f e)) = (μ.map fun x => f x.2).map fun t => ((), t) := by
  rw [PMF.map_comp]
  rfl

/-- **Each method realizes the model's law.** From the invariant, every admissible operation's
answer and abstracted final state follow the model's law, every outcome satisfies the
invariant, and every call is admissible. -/
theorem methods_spec (hfit : Fits w (L.base + span U b n_max)) (hcap : n_max ≤ 2 ^ b)
    (hloop : 0 < maxLoop) (hb : b ≤ w) {V : ℕ} (hV : Fits w V) (attempts : ℕ)
    {s : Memory.State} (hs : L.Inv maxLoop s) (o : Dictionary.Op U)
    (hv : Dictionary.valid V n_max (L.abs s).dict o) :
    ((Memory.spec w).toRandomized.withCoins.run (L.methods maxLoop attempts o) s).map
        (fun (a, e) => (a, L.abs e)) =
      ((scheme U b maxLoop attempts).spec V n_max).law o (L.abs s) ∧
    (∀ x ∈ ((Memory.spec w).toRandomized.withCoins.run (L.methods maxLoop attempts o) s).support,
      L.Inv maxLoop x.2 ∧ x.2.frontier = s.frontier) ∧
    (Memory.spec w).toRandomized.withCoins.toSpec.DemonicValid s
      (L.methods maxLoop attempts o) := by
  cases o with
  | get u =>
    obtain ⟨a, s', t, ⟨rfl, rfl, -⟩, hrun, -, hvalid⟩ :=
      exists_run_liftRight_of_wp (fun _ => 1) (L.wp_getProg (w := w) hs u)
    simp only [methods, hrun, PMF.pure_map, PMF.mem_support_pure_iff, forall_eq]
    exact ⟨trivial, ⟨hs, trivial⟩, hvalid⟩
  | insert u v =>
    obtain ⟨hroom, hvV⟩ := hv
    have hfv : Fits w v := hV.of_le hvV.le
    have hag := hs.toRecords.agree
    -- the deterministic part, then the continuation
    have hcont : ∀ {r : Bool} {s₀ : Memory.State},
        (Memory.spec w).toRandomized.withCoins.run
          (OracleComp.liftRight (L.insertProg maxLoop u v)) s = PMF.pure (r, s₀) →
        (Memory.spec w).toRandomized.withCoins.toSpec.DemonicValid s
          (OracleComp.liftRight (L.insertProg maxLoop u v)) →
        (Memory.spec w).toRandomized.withCoins.toSpec.DemonicValid s₀
          (if r then L.rehash maxLoop attempts else pure ()) →
        (Memory.spec w).toRandomized.withCoins.toSpec.DemonicValid s
          (L.methods maxLoop attempts (.insert u v)) := fun {r s₀} hrun hv₁ hv₂ =>
      StateTransitionSpec.DemonicValid.bind hv₁ fun a s' tr hc => by
        have hx := RandomizedSpec.mem_support_run_of_clientRun _ hc
        rw [hrun, PMF.mem_support_pure_iff] at hx
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hx
        exact hv₂
    by_cases hu : u ∈ L.keyList s
    · obtain ⟨r, s₀, t, ⟨rfl, hI, habs, hf, -⟩, hrun, -, hvalid⟩ :=
        exists_run_liftRight_of_wp (fun _ => 1) (L.wp_insertProg_present hs hu hfv)
      have hrun' := L.run_methods_insert (w := w) (maxLoop := maxLoop) attempts u v s
      rw [run_liftRight] at hrun
      obtain ⟨hr, hs₀⟩ := Prod.ext_iff.mp (Probability.PMF.pure_injective hrun)
      simp only at hr hs₀
      rw [hr, hs₀] at hrun'
      simp only [Bool.false_eq_true, ite_false, RandomizedSpec.run_pure] at hrun'
      have hd : ((L.abs s).dict u).isSome := (hag.mem_iff u).mp hu
      refine ⟨?_, fun x hx => ?_, hcont (by rw [run_liftRight, hr, hs₀]) hvalid
        (StateTransitionSpec.DemonicValid.pure _ _)⟩
      · rw [hrun', PMF.pure_map]
        dsimp only
        rw [habs, Scheme.insertLaw, ite_eq_left hd, PMF.pure_map]
      · rw [hrun', PMF.mem_support_pure_iff] at hx
        subst hx
        exact ⟨hI, hf⟩
    · obtain ⟨T, hT, -⟩ := hs.tables
      have hd : (L.abs s).dict u = none := by simpa [hag.mem_iff] using hu
      have hn : L.n s < n_max := by
        rw [← length_keyList, hag.length_eq]
        rcases hroom with h₁ | h₁
        · exact h₁
        · simp [hd] at h₁
      obtain ⟨r, s₀, t, ⟨hr₀, hR₀, habs₀, hI₀, hf₀, -⟩, hrun, -, hvalid⟩ :=
        exists_run_liftRight_of_wp (fun _ => 1) (L.wp_insertProg_new hs hfit hu hn hfv hT)
      have hrun' := L.run_methods_insert (w := w) (maxLoop := maxLoop) attempts u v s
      rw [run_liftRight] at hrun
      obtain ⟨hr, hs₀⟩ := Prod.ext_iff.mp (Probability.PMF.pure_injective hrun)
      simp only at hr hs₀
      rw [hr, hs₀] at hrun'
      have hdu : ((L.abs s).dict u).isSome = false := by rw [hd]; rfl
      by_cases hg : (scheme U b maxLoop attempts).Good (L.seed s) (L.keyList s ++ [u])
      · have hr' : r = false := by
          rw [hr₀]
          simpa [Scheme.Good, Scheme.replay, scheme] using hg
        rw [hr'] at hrun'
        simp only [Bool.false_eq_true, ite_false, RandomizedSpec.run_pure] at hrun'
        refine ⟨?_, fun x hx => ?_, hcont (by rw [run_liftRight, hr, hs₀, hr'])
          hvalid (StateTransitionSpec.DemonicValid.pure _ _)⟩
        · rw [hrun', PMF.pure_map]
          dsimp only
          rw [habs₀, Scheme.insertLaw, hdu,
            ite_eq_right Bool.false_ne_true, ite_eq_left (show (scheme U b maxLoop attempts).Good
              (L.abs s).seed ((L.abs s).keys ++ [u]) from hg), PMF.pure_map]
          rfl
        · rw [hrun', PMF.mem_support_pure_iff] at hx
          subst hx
          exact ⟨hI₀ hr', hf₀⟩
      · have hr' : r = true := by
          rw [hr₀]
          simpa [Scheme.Good, Scheme.replay, scheme] using hg
        rw [hr'] at hrun'
        simp only [ite_true] at hrun'
        have hks₀ : L.keyList s₀ = L.keyList s ++ [u] := congrArg Model.keys habs₀
        have hd₀ : (L.abs s₀).dict = Function.update (L.abs s).dict u (some v) :=
          congrArg Model.dict habs₀
        obtain ⟨hlaw, hsupp⟩ := L.rehash_spec hfit hcap hloop attempts attempts hR₀
        refine ⟨?_, fun x hx => ?_, hcont (by rw [run_liftRight, hr, hs₀, hr'])
          hvalid (by rw [ite_eq_left rfl]; exact L.demonicValid_rehash hfit hcap hloop hb _ hR₀)⟩
        · rw [hrun', map_unit, hlaw, hks₀, hd₀, Scheme.spec_law_insert, Scheme.insertLaw, hdu,
            ite_eq_right Bool.false_ne_true, ite_eq_right (show ¬ (scheme U b maxLoop attempts).Good
              (L.abs s).seed ((L.abs s).keys ++ [u]) from hg)]
          rfl
        · rw [hrun'] at hx
          obtain ⟨hI, hfx⟩ := hsupp x hx
          exact ⟨hI, hfx.trans hf₀⟩

/-- **Cuckoo hashing over memory refines the seed-level model.** The abstraction reads the seed,
the keys, the dictionary and the flag; the invariant asks the tables to encode the replay. -/
noncomputable def refinement (hfit : Fits w (L.base + span U b n_max)) (hcap : n_max ≤ 2 ^ b)
    (hloop : 0 < maxLoop) (hb : b ≤ w) {V : ℕ} (hV : Fits w V) (attempts : ℕ) :
    RandomizedRefinement ((scheme U b maxLoop attempts).spec V n_max)
      (Memory.spec w).toRandomized.withCoins :=
  .ofLaw (fun o => L.methods maxLoop attempts o) (L.Inv maxLoop) L.abs
    (fun {_} o hs hv => (L.methods_spec hfit hcap hloop hb hV attempts hs o hv).2.2)
    (fun {_} o hs hv _ _ hx =>
      ((L.methods_spec hfit hcap hloop hb hV attempts hs o hv).2.1 _ hx).1)
    (fun {_} o hs hv => (L.methods_spec hfit hcap hloop hb hV attempts hs o hv).1)

variable (U b n_max) in
/-- The memory charges of the model operations: seven units per lookup or update in place, ten
per new key, eight per displacement round, and `rehashCost` per rehash. -/
def charges (loop : ℕ) : Charges := ⟨7, 7, 10, 8, rehashCost U b n_max loop⟩

/-- **Memory costs are the model's charges, in expectation.** Under a cuckoo hash pair, every
operation's expected memory cost is at most its model charge, with no potential. -/
theorem expectedAmortized (hfit : Fits w (L.base + span U b n_max)) (hcap : n_max ≤ 2 ^ b)
    (hloop : 0 < maxLoop) (hb : b ≤ w) {V : ℕ} (hV : Fits w V) (attempts : ℕ) {Cw Cr : ℕ}
    (hC : IsCuckooHashPair (Probability.PMF.uniformOfFintype (Seed U b)) Prod.fst Prod.snd
      n_max maxLoop Cw Cr) :
    (L.refinement hfit hcap hloop hb hV attempts).ExpectedAmortized (memCharge w)
      ((scheme U b maxLoop attempts).charge (charges U b n_max maxLoop)) fun _ => 0 where
  step {s} o hs hv := by
    simp only [mul_zero, tsum_zero, add_zero]
    change (Memory.spec w).toRandomized.withCoins.expectedCost (memCharge w)
      (L.methods maxLoop attempts o) s ≤ _
    cases o with
    | get u =>
      obtain ⟨_, _, t, ⟨-, -, ht⟩, -, hcost, -⟩ :=
        exists_run_liftRight_of_wp (fun _ => 1) (L.wp_getProg (w := w) hs u)
      rw [methods, hcost]
      exact_mod_cast ht
    | insert u v =>
      obtain ⟨hroom, hvV⟩ := hv
      have hfv : Fits w v := hV.of_le hvV.le
      have hag := hs.toRecords.agree
      rw [methods, RandomizedSpec.expectedCost_bind]
      by_cases hu : u ∈ L.keyList s
      · obtain ⟨r, s₀, t, ⟨rfl, -, -, -, ht⟩, hrun, hcost, -⟩ :=
          exists_run_liftRight_of_wp (fun _ => 1) (L.wp_insertProg_present hs hu hfv)
        have hd : ((L.abs s).dict u).isSome := (hag.mem_iff u).mp hu
        rw [hcost, hrun, Probability.PMF.tsum_pure_mul]
        dsimp only
        rw [ite_eq_right Bool.false_ne_true, RandomizedSpec.expectedCost_pure, add_zero]
        change (t : ℝ≥0∞) ≤ ((if ((L.abs s).dict u).isSome then 7 else _ : ℕ) : ℝ≥0∞)
        rw [ite_eq_left hd]
        exact_mod_cast ht
      · obtain ⟨T, hT, -⟩ := hs.tables
        have hd : (L.abs s).dict u = none := by simpa [hag.mem_iff] using hu
        have hn : L.n s < n_max := by
          rw [← length_keyList, hag.length_eq]
          rcases hroom with h₁ | h₁
          · exact h₁
          · change ((L.abs s).dict u).isSome = true at h₁
            simp [hd] at h₁
        obtain ⟨r, s₀, t, ⟨hr₀, hR₀, habs₀, -, -, ht⟩, hrun, hcost, -⟩ :=
          exists_run_liftRight_of_wp (fun _ => 1) (L.wp_insertProg_new hs hfit hu hn hfv hT)
        rw [hcost, hrun, Probability.PMF.tsum_pure_mul]
        have hrounds : (scheme U b maxLoop attempts).rounds (L.abs s).seed (L.abs s).keys u =
            evictRounds (L.seed s).1 (L.seed s).2 maxLoop T ⟨u, (L.keyList s).length⟩ := by
          change ((pureReplay (L.seed s).1 (L.seed s).2 maxLoop (L.keyList s)).map _).getD 0 = _
          rw [hT]
          rfl
        have hlen' : (L.keyList s ++ [u]).length ≤ n_max := by simp; omega
        have hks₀ : L.keyList s₀ = L.keyList s ++ [u] := congrArg Model.keys habs₀
        change (t : ℝ≥0∞) + _ ≤ ((if ((L.abs s).dict u).isSome then 7 else
          10 + 8 * (scheme U b maxLoop attempts).rounds (L.abs s).seed (L.abs s).keys u +
            if (scheme U b maxLoop attempts).Good (L.abs s).seed ((L.abs s).keys ++ [u]) then 0
            else rehashCost U b n_max maxLoop : ℕ) : ℝ≥0∞)
        rw [ite_eq_right (show ¬ (((L.abs s).dict u).isSome = true) by simp [hd]), hrounds]
        have hGood : (scheme U b maxLoop attempts).Good (L.seed s) (L.keyList s ++ [u]) ↔
            (pureReplay (L.seed s).1 (L.seed s).2 maxLoop (L.keyList s ++ [u])).isSome = true :=
          Iff.rfl
        dsimp only
        by_cases hg : (scheme U b maxLoop attempts).Good (L.seed s) (L.keyList s ++ [u])
        · have hr' : r = false := by rw [hr₀, hGood.mp hg]; rfl
          rw [hr', ite_eq_right Bool.false_ne_true, RandomizedSpec.expectedCost_pure, add_zero,
            ite_eq_left (show (scheme U b maxLoop attempts).Good (L.abs s).seed
              ((L.abs s).keys ++ [u]) from hg), Nat.add_zero]
          exact_mod_cast ht
        · have hr' : r = true := by rw [hr₀, Bool.eq_false_iff.mpr (mt hGood.mpr hg)]; rfl
          rw [hr', ite_eq_left rfl, ite_eq_right (show ¬ (scheme U b maxLoop attempts).Good
            (L.abs s).seed ((L.abs s).keys ++ [u]) from hg), Nat.cast_add]
          refine add_le_add (by exact_mod_cast ht) ?_
          exact L.expectedCost_rehash_le hfit hcap hloop attempts
            ((scheme U b maxLoop attempts).not_good_le_half hC
              (hks₀ ▸ hR₀.nodup) hlen') attempts hR₀ hks₀

/-! ## From allocation -/

variable (U b n_max) in
/-- The memory after allocating the layout at the frontier of `s` and marking its seed fresh. -/
def initState (s : Memory.State) : Memory.State :=
  ⟨Function.update (clear s.mem s.frontier (span U b n_max)) (s.frontier + 1) 1,
    s.frontier + span U b n_max⟩

variable (U b n_max) in
/-- The layout allocated at the frontier of `s`. -/
abbrev atFrontier (s : Memory.State) : Layout U b n_max := ⟨s.frontier⟩

/-- **The start.** After allocation, the freshness flag and fresh hash tables holding `θ`, the
layout satisfies the invariant and stores no key under the fresh seed `θ`. -/
theorem inv_init (s : Memory.State) (θ : Seed U b) :
    (atFrontier U b n_max s).Inv maxLoop
      ((atFrontier U b n_max s).fillState (initState U b n_max s) θ) ∧
    (atFrontier U b n_max s).abs ((atFrontier U b n_max s).fillState (initState U b n_max s) θ) =
      ⟨θ, [], Dictionary.empty U, true⟩ := by
  set L₀ := atFrontier U b n_max s
  set s₁ : Memory.State := initState U b n_max s with hs₁
  have hmem : ∀ a, a < L₀.h1.base → s.frontier ≤ a → a ≠ s.frontier + 1 →
      (L₀.fillState s₁ θ).mem a = 0 := fun a ha hf hne => by
    rw [L₀.fillState_mem_of_lt s₁ θ ha]
    simp only [hs₁, initState]
    rw [Function.update_of_ne hne]
    exact clear_of_owns ⟨hf, by simp only [h1_base, span, L₀] at ha ⊢; omega⟩
  have hn : L₀.n (L₀.fillState s₁ θ) = 0 :=
    hmem _ (by simp only [h1_base, L₀]; omega) le_rfl (by simp only [L₀]; omega)
  have hkeys : L₀.keyList (L₀.fillState s₁ θ) = [] := by simp [keyList, hn]
  have hvals : L₀.valList (L₀.fillState s₁ θ) = [] := by simp [valList, hn]
  have hfresh : (L₀.fillState s₁ θ).mem (L₀.base + 1) = 1 := by
    rw [L₀.fillState_mem_of_lt s₁ θ (by simp only [h1_base]; omega)]
    exact Function.update_self _ _ _
  have hR : L₀.Records (L₀.fillState s₁ θ) :=
    { allocated := by simp [L₀, s₁, initState]
      count_le := by omega
      keys_lt := fun i hi => by omega
      nodup := by rw [hkeys]; exact List.nodup_nil
      h1_lt := fun u hu => by
        have := L₀.fillState_h1 s₁ θ ⟨u, hu⟩
        simp only at this
        rw [this]
        exact (θ.1 _).2
      h2_lt := fun u hu => by
        have := L₀.fillState_h2 s₁ θ ⟨u, hu⟩
        simp only at this
        rw [this]
        exact (θ.2 _).2 }
  refine ⟨⟨hR, PureTable.empty U (2 ^ b), by rw [seed_fillState, hkeys]; rfl, fun j => ?_⟩, ?_⟩
  · have hj := j.2
    exact ⟨hmem _ (by simp only [t1_base, h1_base, L₀]; omega)
      (by simp only [t1_base, L₀]; omega) (by simp only [t1_base, L₀]; omega),
      hmem _ (by simp only [t2_base, h1_base, L₀]; omega)
      (by simp only [t2_base, L₀]; omega) (by simp only [t2_base, L₀]; omega)⟩
  · simp only [abs, seed_fillState, hkeys, hvals, hfresh]
    refine congrArg₂ _ (funext fun u => rfl) (by decide)

end Layout

variable [NeZero U]

/-- **Cuckoo hashing from allocation.** Allocate the layout, mark the seed fresh, draw the two
hash tables, then serve the dictionary client `p` with `attempts` random attempts per rehash. -/
noncomputable def run (U b n_max maxLoop attempts : ℕ) [NeZero U] {α : Type}
    (p : OracleComp (Dictionary.Op.Result (U := U)) α) : ProbOracleComp Memory.Op.Result α := do
  let base ← OracleComp.liftRight (Memory.alloc (Layout.span U b n_max))
  let L : Layout U b n_max := ⟨base⟩
  OracleComp.liftRight (L.fresh.set 0 1)
  fill L.h1 b 0 U
  fill L.h2 b 0 U
  OracleComp.interpret (L.methods maxLoop attempts) p

variable {n_max w maxLoop attempts : ℕ}

/-- The run from allocation draws a uniform seed, then serves the client from the initial
state. -/
theorem run_run {α : Type} (p : OracleComp (Dictionary.Op.Result (U := U)) α)
    (s : Memory.State) :
    (Memory.spec w).toRandomized.withCoins.run (run U b n_max maxLoop attempts p) s =
      (Probability.PMF.uniformOfFintype (Seed U b)).bind fun θ =>
        (Memory.spec w).toRandomized.withCoins.run
          (OracleComp.interpret ((Layout.atFrontier U b n_max s).methods maxLoop attempts) p)
          ((Layout.atFrontier U b n_max s).fillState (Layout.initState U b n_max s) θ) := by
  rw [run, RandomizedSpec.run_bind, Layout.run_liftRight, PMF.pure_bind]
  dsimp only
  rw [RandomizedSpec.run_bind, Layout.run_liftRight, PMF.pure_bind]
  exact Layout.run_fills_bind _ _ _

omit [NeZero U] in
/-- Every client admissible on the dictionary is admissible on the model. -/
theorem demonicValid_model {V : ℕ} {α : Type}
    (p : OracleComp (Dictionary.Op.Result (U := U)) α)
    (σ : Model (Seed U b) U)
    (hv : (Dictionary.spec U V n_max).ValidHistory σ.dict
      ((Dictionary.spec U V n_max).clientHistory σ.dict p)) :
    ((scheme U b maxLoop attempts).spec V n_max).toSpec.DemonicValid σ p := by
  have h := ((scheme U b maxLoop attempts).dictRefinement V n_max).toRefinement.simulates_demonic
    p (e := σ) trivial (StateTransitionSpec.toRandomized_demonicValid_of_validHistory hv)
  rw [show link ((scheme U b maxLoop attempts).dictRefinement V n_max).methods p = p from
    PFunctor.FreeM.liftM_lift_eq_self p] at h
  exact h.1

/-- **Correctness.** From any memory with room for the table, the run from allocation answers as
the dictionary does, for every admissible client: its result is a point mass. -/
theorem run_correct {s : Memory.State} (hfit : Fits w (s.frontier + Layout.span U b n_max))
    (hcap : n_max ≤ 2 ^ b) (hloop : 0 < maxLoop) (hb : b ≤ w) {V : ℕ} (hV : Fits w V)
    {α : Type} (p : OracleComp (Dictionary.Op.Result (U := U)) α)
    (hv : (Dictionary.spec U V n_max).ValidHistory (Dictionary.empty U)
      ((Dictionary.spec U V n_max).clientHistory (Dictionary.empty U) p)) :
    ((Memory.spec w).toRandomized.withCoins.run (run U b n_max maxLoop attempts p) s).map
        Prod.fst =
      PMF.pure ((Dictionary.spec U V n_max).clientResult (Dictionary.empty U) p) := by
  rw [run_run, PMF.map_bind, ← PMF.bind_const (Probability.PMF.uniformOfFintype (Seed U b))
    (PMF.pure ((Dictionary.spec U V n_max).clientResult (Dictionary.empty U) p))]
  refine congrArg _ (funext fun θ => ?_)
  set L₀ := Layout.atFrontier U b n_max s
  set M := L₀.refinement (maxLoop := maxLoop) hfit hcap hloop hb hV attempts
  obtain ⟨hI, habs⟩ := Layout.inv_init (n_max := n_max) (maxLoop := maxLoop) s θ
  have hσ : M.abs (L₀.fillState (Layout.initState U b n_max s) θ) =
      ⟨θ, [], Dictionary.empty U, true⟩ := habs
  have hlaw := M.run_link p (e := L₀.fillState (Layout.initState U b n_max s) θ) hI
    (by rw [hσ]; exact demonicValid_model p _ hv)
  have hdict := (scheme U b maxLoop attempts).run_map_dict (V := V) (n_max := n_max) p
    ⟨θ, [], Dictionary.empty U, true⟩ hv
  calc _ = (((Memory.spec w).toRandomized.withCoins.run (link M.methods p)
        (L₀.fillState (Layout.initState U b n_max s) θ)).map
          fun (a, e) => (a, M.abs e)).map Prod.fst := by rw [PMF.map_comp]; rfl
    _ = ((((scheme U b maxLoop attempts).spec V n_max).run p ⟨θ, [], Dictionary.empty U,
          true⟩).map fun (a, σ) => (a, σ.dict)).map Prod.fst := by
        rw [hlaw, hσ, PMF.map_comp]
        rfl
    _ = _ := by rw [hdict, PMF.pure_map]; rfl

omit [NeZero U] in
/-- A fill followed by a program costs `2 * U` plus the average cost of the program from the
filled memory. -/
theorem expectedCost_fill_bind_le {β : Type} (blk : Block) (k : Unit → ProbOracleComp
    Memory.Op.Result β) (s : Memory.State) :
    (Memory.spec w).toRandomized.withCoins.expectedCost (memCharge w) (fill blk b 0 U >>= k) s ≤
      ((2 * U : ℕ) : ℝ≥0∞) + ∑' θ, Probability.PMF.uniformOfFintype (Fin U → Fin (2 ^ b)) θ *
        (Memory.spec w).toRandomized.withCoins.expectedCost (memCharge w) (k ())
          (writeFrom blk b 0 U θ s) := by
  rw [RandomizedSpec.expectedCost_bind]
  refine add_le_add (expectedCost_fill_le blk s) (le_of_eq ?_)
  rw [show (∑' x, (Memory.spec w).toRandomized.withCoins.run (fill blk b 0 U) s x *
      (Memory.spec w).toRandomized.withCoins.expectedCost (memCharge w) (k x.1) x.2) =
      ∑' x, (Memory.spec w).toRandomized.withCoins.run (fill blk b 0 U) s x *
        (fun s' => (Memory.spec w).toRandomized.withCoins.expectedCost (memCharge w) (k ()) s')
          x.2 from rfl, ← Probability.PMF.tsum_map_mul, HashFamily.RandomTable.run_fill,
    Probability.PMF.tsum_map_mul]

/-- **The expected memory cost from allocation.** Under a cuckoo hash pair with enough rehash
attempts, the run from allocation costs at most the allocation and the first hash tables, plus
`opBound` per operation of the client's history, in expectation. -/
theorem expectedCost_run_le {s : Memory.State}
    (hfit : Fits w (s.frontier + Layout.span U b n_max)) (hcap : n_max ≤ 2 ^ b)
    (hloop : 0 < maxLoop) (hb : b ≤ w) {V : ℕ} (hV : Fits w V) {Cw Cr : ℕ}
    (hC : IsCuckooHashPair (Probability.PMF.uniformOfFintype (Seed U b)) Prod.fst Prod.snd
      n_max maxLoop Cw Cr)
    (hF : n_max * (8 * maxLoop + Layout.rehashCost U b n_max maxLoop) ≤ 2 ^ attempts)
    {α : Type} (p : OracleComp (Dictionary.Op.Result (U := U)) α)
    (hv : (Dictionary.spec U V n_max).ValidHistory (Dictionary.empty U)
      ((Dictionary.spec U V n_max).clientHistory (Dictionary.empty U) p)) :
    (Memory.spec w).toRandomized.withCoins.expectedCost (memCharge w)
        (run U b n_max maxLoop attempts p) s ≤
      ((Layout.span U b n_max + 2 + 4 * U : ℕ) : ℝ≥0∞) +
        ((Dictionary.spec U V n_max).totalCost
          (fun _ => (scheme U b maxLoop attempts).opBound (Layout.charges U b n_max maxLoop)
            n_max Cw Cr) (Dictionary.empty U)
          ((Dictionary.spec U V n_max).clientHistory (Dictionary.empty U) p) : ℝ≥0∞) := by
  set L₀ := Layout.atFrontier U b n_max s
  set s₁ := Layout.initState U b n_max s
  set C := scheme U b maxLoop attempts
  -- the cost of the client from each initial memory
  have hclient (θ : Seed U b) :
      (Memory.spec w).toRandomized.withCoins.expectedCost (memCharge w)
        (OracleComp.interpret (L₀.methods maxLoop attempts) p) (L₀.fillState s₁ θ) ≤
      (C.spec V n_max).expectedCost (C.charge (Layout.charges U b n_max maxLoop)) p
        ⟨θ, [], Dictionary.empty U, true⟩ := by
    obtain ⟨hI, habs⟩ := Layout.inv_init (n_max := n_max) (maxLoop := maxLoop) s θ
    have h := (L₀.expectedAmortized hfit hcap hloop hb hV attempts hC).client p
      (e := L₀.fillState s₁ θ) hI (by
        change (C.spec V n_max).toSpec.DemonicValid (L₀.abs _) p
        rw [habs]
        exact demonicValid_model p _ hv)
    simp only [mul_zero, tsum_zero, add_zero] at h
    have hσ : (L₀.refinement (maxLoop := maxLoop) hfit hcap hloop hb hV attempts).abs
        (L₀.fillState s₁ θ) = ⟨θ, [], Dictionary.empty U, true⟩ := habs
    rw [hσ] at h
    exact h
  have hfb : ∀ ks : List (Fin U), ks.Nodup → ks.length ≤ n_max → C.Good (C.fallback ks) ks :=
    fun ks hnd hlen => isSome_pureReplay_posMap hnd (by omega) hloop
  have hmodel := C.expectedCost_le (V := V) (Layout.charges U b n_max maxLoop) hC hfb hF p hv
  -- the deterministic start
  have hstart : (Memory.spec w).toRandomized.withCoins.expectedCost (memCharge w)
      (run U b n_max maxLoop attempts p) s =
      ((Layout.span U b n_max + 1 : ℕ) : ℝ≥0∞) +
        (1 + (Memory.spec w).toRandomized.withCoins.expectedCost (memCharge w)
          (fill L₀.h1 b 0 U >>= fun _ => fill L₀.h2 b 0 U >>= fun _ =>
            OracleComp.interpret (L₀.methods maxLoop attempts) p) s₁) := by
    have hfront : Fits w (s.frontier + Layout.span U b n_max) := hfit
    obtain ⟨a, s₀, t, ⟨rfl, rfl, rfl⟩, hrun, hcost, -⟩ :=
      Layout.exists_run_liftRight_of_wp (fun _ => 1)
      (show (Memory.spec w).wp Memory.charge (Memory.alloc (Layout.span U b n_max))
        (fun r s' t => r = s.frontier ∧ s' = ⟨clear s.mem s.frontier (Layout.span U b n_max),
          s.frontier + Layout.span U b n_max⟩ ∧ t = Layout.span U b n_max + 1) s from
        ⟨hfront, rfl, rfl, by simp [Memory.charge]⟩)
    have hset : (Memory.spec w).wp Memory.charge (L₀.fresh.set 0 1) (fun _ s' t => s' = s₁ ∧ t = 1)
        ⟨clear s.mem s.frontier (Layout.span U b n_max), s.frontier + Layout.span U b n_max⟩ := by
      simp only [StateTransitionSpec.wp_lift, Memory.valid_write, Memory.charge_write,
        StateTransitionSpec.stepFn, Memory.step_write]
      refine ⟨⟨by simp only [Layout.fresh_base, L₀, Layout.span]; omega,
        hfront.of_le (by simp only [Layout.span]; omega)⟩, rfl, trivial⟩
    obtain ⟨a', s₁', t', ⟨hs₁', ht'⟩, hrun', hcost', -⟩ :=
      Layout.exists_run_liftRight_of_wp (fun _ => 1) hset
    rw [run, RandomizedSpec.expectedCost_bind, hrun, Probability.PMF.tsum_pure_mul, hcost]
    dsimp only
    rw [RandomizedSpec.expectedCost_bind, hrun', Probability.PMF.tsum_pure_mul, hcost', ht',
      Nat.cast_one]
    dsimp only
    rw [hs₁']
  rw [hstart]
  calc _ ≤ ((Layout.span U b n_max + 1 : ℕ) : ℝ≥0∞) + (1 + (((2 * U : ℕ) : ℝ≥0∞) +
        ∑' θ₁, Probability.PMF.uniformOfFintype (Fin U → Fin (2 ^ b)) θ₁ *
          (((2 * U : ℕ) : ℝ≥0∞) + ∑' θ₂, Probability.PMF.uniformOfFintype (Fin U → Fin (2 ^ b)) θ₂ *
            (C.spec V n_max).expectedCost (C.charge (Layout.charges U b n_max maxLoop)) p
              ⟨(θ₁, θ₂), [], Dictionary.empty U, true⟩))) := by
        gcongr
        refine (expectedCost_fill_bind_le _ _ _).trans (add_le_add le_rfl ?_)
        refine tsum_le_tsum fun θ₁ => mul_le_mul' le_rfl ?_
        refine (expectedCost_fill_bind_le _ _ _).trans (add_le_add le_rfl ?_)
        refine tsum_le_tsum fun θ₂ => mul_le_mul' le_rfl ?_
        exact hclient (θ₁, θ₂)
    _ = ((Layout.span U b n_max + 2 + 4 * U : ℕ) : ℝ≥0∞) +
        ∑' θ, Probability.PMF.uniformOfFintype (Seed U b) θ *
          (C.spec V n_max).expectedCost (C.charge (Layout.charges U b n_max maxLoop)) p
            ⟨θ, [], Dictionary.empty U, true⟩ := by
        simp only [mul_add, tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
        rw [← Probability.PMF.uniformOfFintype_prod, Probability.PMF.tsum_bind_mul]
        simp only [Probability.PMF.tsum_map_mul]
        push_cast
        ring
    _ ≤ _ := by gcongr

/-! ## Pagh and Rodler's parameters -/

variable (U) in
/-- The number of random attempts per rehash at Pagh and Rodler's parameters: enough that the
fallback contributes at most one unit per insertion in expectation. -/
def attemptsFor (n_max : ℕ) : ℕ :=
  Nat.clog 2 (n_max * (8 * maxEvictions n_max +
    Layout.rehashCost U (tableBits n_max) n_max (maxEvictions n_max)))

/-- **Cuckoo hashing over memory, at Pagh and Rodler's parameters.** With tables of
`tableSize n_max ≥ 32 · max n_max 4` slots, at most `maxEvictions n_max` displacement rounds per
insertion and `attemptsFor U n_max` attempts per rehash, the run from allocation answers as the
dictionary does, and costs at most the allocation and the first hash tables plus `opBound` per
operation in expectation: seven units per lookup, and for an insertion
`44 + 6 · rehashCost / (n_max · maxEvictions n_max)` (`isCuckooHashPair_uniform`, with walk
constant `2` and rehash constant `3`). -/
theorem run_tableBits {s : Memory.State}
    (hfit : Fits w (s.frontier + Layout.span U (tableBits n_max) n_max))
    (hb : tableBits n_max ≤ w) {V : ℕ} (hV : Fits w V) {α : Type}
    (p : OracleComp (Dictionary.Op.Result (U := U)) α)
    (hv : (Dictionary.spec U V n_max).ValidHistory (Dictionary.empty U)
      ((Dictionary.spec U V n_max).clientHistory (Dictionary.empty U) p)) :
    ((Memory.spec w).toRandomized.withCoins.run
        (run U (tableBits n_max) n_max (maxEvictions n_max) (attemptsFor U n_max) p) s).map
        Prod.fst =
      PMF.pure ((Dictionary.spec U V n_max).clientResult (Dictionary.empty U) p) ∧
    (Memory.spec w).toRandomized.withCoins.expectedCost (memCharge w)
        (run U (tableBits n_max) n_max (maxEvictions n_max) (attemptsFor U n_max) p) s ≤
      ((Layout.span U (tableBits n_max) n_max + 2 + 4 * U : ℕ) : ℝ≥0∞) +
        ((Dictionary.spec U V n_max).totalCost
          (fun _ => (scheme U (tableBits n_max) (maxEvictions n_max) (attemptsFor U n_max)).opBound
            (Layout.charges U (tableBits n_max) n_max (maxEvictions n_max)) n_max 2 3)
          (Dictionary.empty U)
          ((Dictionary.spec U V n_max).clientHistory (Dictionary.empty U) p) : ℝ≥0∞) := by
  have hcap : n_max ≤ 2 ^ tableBits n_max :=
    (four_mul_le_tableSize n_max).trans' (by omega)
  have hloop : 0 < maxEvictions n_max := maxEvictions_pos n_max
  have hC := Cslib.DataStructure.Dictionary.CuckooHashing.isCuckooHashPair_uniform (U := U)
    (m := 2 ^ tableBits n_max)
    n_max (maxEvictions n_max) (thirtyTwo_mul_max_le_tableSize n_max) le_rfl
    (maxEvictions_le_tableSize n_max)
  refine ⟨run_correct hfit hcap hloop hb hV p hv,
    expectedCost_run_le hfit hcap hloop hb hV hC (Nat.le_pow_clog (by decide) _) p hv⟩

end Cslib.DataStructure.Dictionary.CuckooHashing.Memory
