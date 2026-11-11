/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.RandomPermutation
public import CslibFrontier.Languages.Probabilistic.UntilBad.ChooseTwo
public import CslibFrontier.Languages.Probabilistic.Simulation
public import CslibFrontier.Probability.Product
public import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Uniform

/-!
# Ideal Cipher Model

This module formalizes the Ideal Cipher Model, consisting of independent random
permutations for each key, and defines its exact and forgetful lazy samplers.

## Main definitions
* `Query`: An ideal cipher query, combining a key and a permutation query.
* `Spec`: The ideal cipher specification.
* `lazyEvalPerm`, `answer`, `forgetfulAnswer`: Samplers for evaluating an ideal cipher.

## Main results
* `uniform_interpret_eq_lazy`: Eager random-permutation sampling matches lazy exact caching.
* `identicalUntilBad_exactWithBad_forgetfulWithBad`: Identical-until-bad coupling between exact
  and forgetful samplers.
* `toOuterMeasure_bad_forgetfulWithBad_le`: Quadratic birthday bound on the forgetful bad event.
* `abs_sub_uniformPerm_forgetful_le`: Ideal-cipher switching bound
  `Q.choose 2 * (Fintype.card Block)⁻¹`.

## References
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020], Section 7.3.1.
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 4.7.
-/

public section

namespace Cslib.IdealCipher

open Cslib.RandomPermutation Cslib.Probability Cslib.OracleComp
open scoped ENNReal NNReal BigOperators

variable {Key Block : Type}

/-- A query to the ideal cipher, consisting of a key and a block query. -/
abbrev Query (Key Block : Type) := Key × PermQuery Block

/-- The oracle specification for an ideal cipher. -/
abbrev Spec (Key Block : Type) : OracleSpec (Query Key Block) :=
  fun _ => Block

section Finite
variable [DecidableEq Key] [Fintype Key] [DecidableEq Block] [Fintype Block] [Nonempty Block]

/-- Evaluate an ideal cipher directly with a full permutation state. -/
@[expose]
noncomputable def lazyEvalPerm (q : Query Key Block) : StateT (Key → Equiv.Perm Block) PMF Block :=
  fun P => (·, P) <$> PMF.pure (evalPerm (P q.1) q.2)

/-- Evaluate an ideal cipher with a lazy cache. -/
@[expose]
noncomputable def answer (q : Query Key Block) :
    StateT (Key → Cache Block) PMF Block := fun st =>
  (RandomPermutation.answer q.2 (st q.1)).map fun (b, c) => (b, Function.update st q.1 c)

/-- Evaluate an ideal cipher with a forgetful cache that doesn't check consistency. -/
@[expose]
noncomputable def forgetfulAnswer (q : Query Key Block) :
    StateT (Key → Cache Block) PMF Block := fun st =>
  (RandomPermutation.forgetfulAnswer q.2 (st q.1)).map fun (b, c) => (b, Function.update st q.1 c)

/-- Generates a complete tuple of independent random permutations extending the given cache
function. -/
noncomputable def complete (st : Key → Cache Block) : PMF (Key → Equiv.Perm Block) :=
  PMF.pi (fun k => RandomPermutation.complete (st k))

/-- An exact evaluation step for the ideal cipher model, with a bad flag that triggers
when a duplicate output is sampled. -/
noncomputable def exactWithBad (q : Query Key Block) :
    StateT ((Key → Cache Block) × Bool) PMF Block := fun (st, bad) =>
  (RandomPermutation.exactWithBad q.2 (st q.1, bad)).map fun (b, (c, bad')) =>
    (b, (Function.update st q.1 c, bad'))

/-- A forgetful evaluation step for the ideal cipher model, updating the cache and the bad flag. -/
noncomputable def forgetfulWithBad (q : Query Key Block) :
    StateT ((Key → Cache Block) × Bool) PMF Block := fun (st, bad) =>
  (RandomPermutation.forgetfulWithBad q.2 (st q.1, bad)).map fun (b, (c, bad')) =>
    (b, (Function.update st q.1 c, bad'))

omit [Fintype Block] [DecidableEq Block] [Nonempty Block] in
theorem pi_update_eq_bind_perm [Finite Block] (p : ∀ _k : Key, PMF (Equiv.Perm Block)) (i : Key)
    (q' : PMF (Equiv.Perm Block)) :
    PMF.pi (Function.update p i q') = q'.bind (fun v =>
      PMF.pi (Function.update p i (PMF.pure v))) :=
  by
  have : ∀ _k : Key, Finite (Equiv.Perm Block) := fun _ => inferInstance
  simpa only [Function.update_self, Function.update_idem] using
    (PMF.pi_bind_update (Function.update p i q') i).symm

omit [Fintype Block] [DecidableEq Block] [Nonempty Block] in
theorem pi_bind_eq_bind_pi_update [Finite Block] (p : ∀ _k : Key, PMF (Equiv.Perm Block)) (i : Key)
    {β : Type} (f : (∀ _k : Key, Equiv.Perm Block) → PMF β) :
    (PMF.pi p).bind f = (p i).bind (fun v => (PMF.pi (Function.update p i (PMF.pure v))).bind f) :=
  by
  have : ∀ _k : Key, Finite (Equiv.Perm Block) := fun _ => inferInstance
  have H : PMF.pi p = (p i).bind (fun v => PMF.pi (Function.update p i (PMF.pure v))) := by
    simpa only [Function.update_self, Function.update_idem] using (PMF.pi_bind_update p i).symm
  rw [H, PMF.bind_bind]

theorem bind_map_bind_lemma {α β γ δ : Type} (m : PMF α) (F : α → PMF β) (H : β → PMF γ)
    (proj : α → δ) :
    m.bind (fun x => (F x |>.bind H).map (proj x, ·)) =
    (m.bind (fun x => (F x).map (proj x, ·))).bind (fun y => H y.2 |>.map (y.1, ·)) := by
  rw [PMF.bind_bind]
  apply congrArg
  ext1 x
  rw [PMF.map_bind, PMF.bind_map]
  rfl

omit [Fintype Key] in
theorem answer_preserve_isPartialBijection (q : Query Key Block) (st : Key → Cache Block)
    (hst : ∀ k, IsPartialBijection (st k)) (a : Block) (st' : Key → Cache Block)
    (hmem : (a, st') ∈ (answer q st).support) (k : Key) : IsPartialBijection (st' k) := by
  simp only [answer, PMF.mem_support_map_iff] at hmem
  obtain ⟨⟨b, c'⟩, hmem, heq⟩ := hmem
  cases heq
  change IsPartialBijection (Function.update st q.1 c' k)
  by_cases h : k = q.1
  · subst h
    simp only [Function.update, dite_eq_left]
    exact RandomPermutation.answer_preserve_isPartialBijection q.2 (st q.1) (hst q.1) b c' hmem
  · simp only [Function.update, dite_eq_right h]
    exact hst k

theorem answer_complete (q : Query Key Block) (st : Key → Cache Block)
    (hst : ∀ k, IsPartialBijection (st k)) :
    (answer q st).bind (fun (a, st') => (complete st').map (a, ·)) =
      (complete st).bind (fun P => (fun x => (x, P)) <$> PMF.pure (evalPerm (P q.1) q.2)) := by
  have H_comp (s : Key → Cache Block) :
    complete s = PMF.pi (fun k => RandomPermutation.complete (s k)) := rfl
  have H_ans : answer q st = (RandomPermutation.answer q.2 (st q.1)).map
    (fun (b, c) => (b, Function.update st q.1 c)) := rfl
  rw [H_ans, PMF.bind_map]
  simp_rw [H_comp]
  simp only [Function.comp_def]
  have H_update (c : Cache Block) :
      (fun k => RandomPermutation.complete (Function.update st q.1 c k)) =
      Function.update (fun k => RandomPermutation.complete (st k)) q.1
        (RandomPermutation.complete c) := by
    ext k
    by_cases h : k = q.1
    · subst h; simp [Function.update]
    · simp [Function.update, h]
  have H_LHS : (RandomPermutation.answer q.2 (st q.1)).bind (fun x =>
    (PMF.pi (fun k => RandomPermutation.complete (Function.update st q.1 x.2 k))).map (x.1, ·)) =
      (RandomPermutation.answer q.2 (st q.1)).bind (fun x =>
        ((RandomPermutation.complete x.2).bind (fun v =>
          PMF.pi (Function.update (fun k => RandomPermutation.complete (st k)) q.1
              (PMF.pure v)))).map (x.1, ·)) := by
    apply congrArg
    ext1 ⟨b, c⟩
    rw [H_update c, pi_update_eq_bind_perm]
  rw [H_LHS, bind_map_bind_lemma, RandomPermutation.answer_complete q.2 (st q.1) (hst q.1)]
  have H_RHS : (PMF.pi (fun k => RandomPermutation.complete (st k))).bind
      (fun P => (fun x => (x, P)) <$> PMF.pure (evalPerm (P q.1) q.2)) =
      (RandomPermutation.complete (st q.1)).bind (fun P_q1 =>
        (PMF.pi (Function.update (fun k => RandomPermutation.complete (st k)) q.1
          (PMF.pure P_q1))).map (evalPerm P_q1 q.2, ·)) := by
    rw [pi_bind_eq_bind_pi_update]
    apply congrArg
    ext1 v
    have h1 : (PMF.pi (Function.update (fun k => RandomPermutation.complete (st k)) q.1
      (PMF.pure v))).bind (fun P =>
            PMF.pure (evalPerm (P q.1) q.2, P)) =
           (PMF.pi (Function.update (fun k => RandomPermutation.complete (st k)) q.1
             (PMF.pure v))).bind (fun P =>
            PMF.pure (evalPerm v q.2, P)) := by
      apply PMF.bind_congr_on_support
      intro P hP
      have hP' := (PMF.mem_support_pi_iff _ _).mp hP q.1
      simp only [Function.update_self, PMF.mem_support_pure_iff] at hP'
      rw [hP']
    have h2 : ((PMF.pi (Function.update (fun k => RandomPermutation.complete (st k)) q.1
             (PMF.pure v))).bind (fun P => (fun x => (x, P)) <$> PMF.pure (evalPerm (P q.1) q.2))) =
             ((PMF.pi (Function.update (fun k => RandomPermutation.complete (st k)) q.1
             (PMF.pure v))).bind (fun P => PMF.pure (evalPerm (P q.1) q.2, P))) := by
      apply congrArg
      ext1 P
      exact PMF.pure_bind _ _
    rw [h2, h1]
    exact (PMF.bind_pure_comp _ _).symm
  rw [H_RHS]
  rw [PMF.bind_map]
  apply congrArg
  ext1 P_q1
  exact (PMF.bind_pure_comp _ _).symm

theorem uniform_interpret_eq_lazy {α : Type} (program : OracleComp (Spec Key Block) α) :
    (do
      let P ← PMF.pi (fun _ : Key => PMF.uniformOfFintype (Equiv.Perm Block))
      OracleComp.interpret (fun (q : Query Key Block) => PMF.pure (evalPerm (P q.1) q.2)) program) =
    ((OracleComp.interpret answer program).run (fun _ => [])).map Prod.fst := by
  have h := OracleComp.run_interpret_simulation_of_invariant answer
    lazyEvalPerm complete (fun s => ∀ k, IsPartialBijection (s k))
    (fun q s hs a s' hmem => answer_preserve_isPartialBijection q s hs a s' hmem)
    (fun q s hs => answer_complete q s hs)
    program (fun _ => []) (fun _ => isPartialBijection_nil)
  have h2 := congrArg (PMF.map Prod.fst) h
  have h3 : ((complete (fun _ : Key => [])).bind fun t =>
      (OracleComp.interpret lazyEvalPerm program).run t).map Prod.fst =
    (do let P ← PMF.pi (fun _ : Key => PMF.uniformOfFintype (Equiv.Perm Block))
        OracleComp.interpret (fun (q : Query Key Block) =>
          PMF.pure (evalPerm (P q.1) q.2)) program) := by
    simp only [complete, RandomPermutation.complete_nil, pmf_norm, PMF.map_bind]
    apply congrArg
    ext1 P
    have h_ro := OracleComp.run_interpret_readOnly (fun (q : Query Key Block)
      (P : Key → Equiv.Perm Block) => PMF.pure (evalPerm (P q.1) q.2)) program P
    have h_ro2 := congrArg (PMF.map Prod.fst) h_ro
    change PMF.map Prod.fst _ = _
    have h4 : PMF.map Prod.fst (PMF.map (fun a => (a, P))
      (interpret (fun q => PMF.pure (evalPerm (P q.1) q.2)) program)) =
      interpret (fun q => PMF.pure (evalPerm (P q.1) q.2)) program := by
      rw [PMF.map_comp]
      change PMF.map id _ = _
      exact PMF.map_id _
    exact h_ro2.trans h4
  rw [← h3]
  simpa only [pmf_norm, complete, PMF.map, PMF.bind_const] using h2.symm

omit [Fintype Key] in
theorem identicalUntilBad_exactWithBad_forgetfulWithBad :
    IdenticalUntilBad (spec := Spec Key Block) exactWithBad forgetfulWithBad
      (fun st : (Key → Cache Block) × Bool => st.2 = true) where
  absorb_first a st h_bad st' hmem := by
    obtain ⟨st_map, bad⟩ := st
    have hmem2 : st' ∈ ((RandomPermutation.exactWithBad a.2 (st_map a.1, bad)).map
        fun x => (x.1, Function.update st_map a.1 x.2.1, x.2.2)).support := hmem
    simp only [PMF.mem_support_map_iff] at hmem2
    obtain ⟨⟨b, ⟨c, bad_new⟩⟩, hmem3, rfl⟩ := hmem2
    exact RandomPermutation.identicalUntilBad_exactWithBad_forgetfulWithBad.absorb_first
        a.2 (st_map a.1, bad) h_bad (b, (c, bad_new)) hmem3
  absorb_second a st h_bad st' hmem := by
    obtain ⟨st_map, bad⟩ := st
    have hmem2 : st' ∈ ((RandomPermutation.forgetfulWithBad a.2 (st_map a.1, bad)).map
        fun x => (x.1, Function.update st_map a.1 x.2.1, x.2.2)).support := hmem
    simp only [PMF.mem_support_map_iff] at hmem2
    obtain ⟨⟨b, ⟨c, bad_new⟩⟩, hmem3, rfl⟩ := hmem2
    exact RandomPermutation.identicalUntilBad_exactWithBad_forgetfulWithBad.absorb_second
        a.2 (st_map a.1, bad) h_bad (b, (c, bad_new)) hmem3
  agree a st hst b st' hst' := by
    obtain ⟨st_map, bad⟩ := st
    obtain ⟨st'_map, bad'⟩ := st'
    cases bad
    · cases bad'
      · dsimp [exactWithBad, forgetfulWithBad]
        simp only [PMF.map_apply]
        apply tsum_congr
        intro ⟨b_out, ⟨c_out, bad_out⟩⟩
        split_ifs with h
        · injection h with h1 h2
          injection h2 with h3 h4
          subst h4
          exact RandomPermutation.identicalUntilBad_exactWithBad_forgetfulWithBad.agree a.2
            (st_map a.1, false) Bool.noConfusion b_out (c_out, false) Bool.noConfusion
        · rfl
      · exact (hst' rfl).elim
    · exact (hst rfl).elim


theorem toOuterMeasure_bad_forgetfulWithBad_le {β : Type}
    {program : OracleComp (Spec Key Block) β} {n : ℕ}
    (hn : IsQueryBounded program n) (cache : Key → Cache Block) :
    ((OracleComp.interpret forgetfulWithBad program).run (cache, false)).toOuterMeasure
      {x | let (_, _, bad) := x; bad = true} ≤
      (n * (Finset.univ.sum (fun k => (cache k).length)) + n.choose 2 : ℕ) *
      (Fintype.card Block : ℝ≥0∞)⁻¹ := by
  refine OracleComp.toOuterMeasure_bad_choose_two_le
      (bad := fun st : (Key → Cache Block) × Bool => st.2 = true)
    (fun st : (Key → Cache Block) × Bool => Finset.univ.sum (fun k => (st.1 k).length))
    (Fintype.card Block : ℝ≥0∞)⁻¹ ?_ ?_ hn Bool.noConfusion
  · intro q ⟨c, b⟩ hb
    have hb' : b = false := Bool.eq_false_iff.mpr hb
    subst hb'
    simp only [forgetfulWithBad, PMF.toOuterMeasure_map_apply, Set.preimage_ofPred_eq]
    cases hq : cachedAnswer (c q.1) q.2 with
    | some a => simp [RandomPermutation.forgetfulWithBad, hq, PMF.toOuterMeasure_pure_apply]
    | none =>
      have hpre : (fun a : Block => (a, (PermQuery.toCacheEntry ⟨q.2, a⟩ :: c q.1,
          false || decide (a ∉ freshAnswers (c q.1) q.2)))) ⁻¹'
          {x : Block × (Cache Block × Bool) | x.2.2 = true} =
          {a : Block | a ∉ freshAnswers (c q.1) q.2} := by
        ext a
        simp
      have hcard : (Finset.univ.filter fun a : Block => a ∉ freshAnswers (c q.1) q.2).card
          ≤ (c q.1).length := by
        cases h_q2 : q.2 with
        | forward x =>
          simpa [freshAnswers, invLookup, Option.ne_none_iff_isSome] using
            Cslib.RandomOracle.card_filter_lookup_isSome_le ((c q.1).map Prod.swap)
        | inverse y =>
          simpa [freshAnswers, Option.ne_none_iff_isSome] using
            Cslib.RandomOracle.card_filter_lookup_isSome_le (c q.1)
      simp only [RandomPermutation.forgetfulWithBad, hq]
      rw [PMF.toOuterMeasure_map_apply, hpre, PMF.toOuterMeasure_uniformOfFintype]
      gcongr
      exact (Nat.cast_le.mpr hcard).trans (Nat.cast_le.mpr (Finset.single_le_sum
          (fun (k : Key) _ => Nat.zero_le (List.length (c k))) (Finset.mem_univ q.1)))
  · intro q ⟨c, b⟩ _ p hp hp_bad
    cases hq : cachedAnswer (c q.1) q.2 with
    | some a =>
      simp only [forgetfulWithBad, PMF.mem_support_map_iff] at hp
      obtain ⟨x, hx, rfl⟩ := hp
      simp only [RandomPermutation.forgetfulWithBad, hq, PMF.mem_support_pure_iff] at hx
      cases hx
      have h_update : Function.update c q.1 (c q.1) = c := Function.update_eq_self q.1 c
      simp only [h_update]
      omega
    | none =>
      simp only [forgetfulWithBad, PMF.mem_support_map_iff] at hp
      obtain ⟨x, hx, rfl⟩ := hp
      simp only [RandomPermutation.forgetfulWithBad, hq, PMF.mem_support_map_iff] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      dsimp
      have h_sum1 : ∑ k, List.length (Function.update c q.1
          (PermQuery.toCacheEntry ⟨q.2, a⟩ :: c q.1) k) =
          (List.length (c q.1) + 1) + ∑ k ∈ Finset.univ.erase q.1, List.length (c k) := by
        calc ∑ k, List.length (Function.update c q.1 (PermQuery.toCacheEntry ⟨q.2, a⟩ :: c q.1) k)
          _ = List.length (Function.update c q.1 (PermQuery.toCacheEntry ⟨q.2, a⟩ :: c q.1) q.1) +
            ∑ k ∈ Finset.univ.erase q.1, List.length (Function.update c q.1
              (PermQuery.toCacheEntry ⟨q.2, a⟩ :: c q.1) k) :=
            (Finset.add_sum_erase Finset.univ
            (fun k => List.length (Function.update c q.1
              (PermQuery.toCacheEntry ⟨q.2, a⟩ :: c q.1) k)) (Finset.mem_univ q.1)).symm
          _ = (List.length (c q.1) + 1) + ∑ k ∈ Finset.univ.erase q.1,
            List.length (Function.update c q.1
              (PermQuery.toCacheEntry ⟨q.2, a⟩ :: c q.1) k) := by simp
          _ = (List.length (c q.1) + 1) + ∑ k ∈ Finset.univ.erase q.1, List.length (c k) := by
            congr 1
            apply Finset.sum_congr rfl
            intro k hk
            have hk' : k ≠ q.1 := (Finset.mem_erase.mp hk).1
            simp [hk']
      have h_sum2 : ∑ k, List.length (c k) = List.length (c q.1) +
          ∑ k ∈ Finset.univ.erase q.1, List.length (c k) :=
          (Finset.add_sum_erase Finset.univ (fun k => List.length (c k)) (Finset.mem_univ q.1)).symm
      rw [h_sum1, h_sum2]
      omega

omit [Fintype Key] in
theorem exactWithBad_preserve_isPartialBijection (q : Query Key Block)
    (st : (Key → Cache Block) × Bool) (hst : ∀ k, IsPartialBijection (st.1 k)) (a : Block)
    (st' : (Key → Cache Block) × Bool)
    (hmem : (a, st') ∈ (exactWithBad q st).support) (k : Key) : IsPartialBijection (st'.1 k) := by
  simp only [exactWithBad, PMF.mem_support_map_iff] at hmem
  obtain ⟨⟨b, ⟨c', bad'⟩⟩, hmem, h_eq⟩ := hmem
  cases h_eq
  by_cases h : k = q.1
  · subst h
    simp only [Function.update_self]
    exact RandomPermutation.exactWithBad_preserve_isPartialBijection q.2 (st.1 q.1, st.2)
        (hst q.1) b (c', bad') hmem
  · simp only [Function.update_of_ne h]
    exact hst k

omit [Fintype Key] in
theorem exactWithBad_map_fst (q : Query Key Block) (st : (Key → Cache Block) × Bool)
    (hcache : ∀ k, IsPartialBijection (st.1 k)) :
    (exactWithBad q st).map (fun (a, st') => (a, st'.1)) = answer q st.1 := by
  simp only [exactWithBad, answer, PMF.map_comp]
  have h := congrArg (PMF.map (fun (b, c) => (b, Function.update st.1 q.1 c)))
    (RandomPermutation.exactWithBad_map_fst q.2 (st.1 q.1, st.2) (hcache q.1))
  rw [PMF.map_comp] at h
  exact h

omit [Fintype Key] in
theorem forgetfulWithBad_map_fst (q : Query Key Block) (st : (Key → Cache Block) × Bool) :
    (forgetfulWithBad q st).map (fun (a, st') => (a, st'.1)) = forgetfulAnswer q st.1 := by
  simp only [forgetfulWithBad, forgetfulAnswer, PMF.map_comp]
  have h := congrArg (PMF.map (fun (b, c) => (b, Function.update st.1 q.1 c)))
    (RandomPermutation.forgetfulWithBad_map_fst q.2 (st.1 q.1, st.2))
  rw [PMF.map_comp] at h
  exact h
omit [Fintype Key] in
theorem run_interpret_exactWithBad_map_fst {β : Type}
    (program : OracleComp (Spec Key Block) β) (cache : Key → Cache Block) (bad : Bool)
    (hcache : ∀ k, IsPartialBijection (cache k)) :
    ((OracleComp.interpret exactWithBad program).run (cache, bad)).map
      (fun (a, st') => (a, st'.1)) =
    (OracleComp.interpret answer program).run cache :=
  OracleComp.run_interpret_map_state_of_invariant exactWithBad answer Prod.fst
    (fun s => ∀ k, IsPartialBijection (s.1 k))
    (fun q s hs a s' hmem k => exactWithBad_preserve_isPartialBijection q s hs a s' hmem k)
    (fun q s hs => exactWithBad_map_fst q s hs)
    program (cache, bad) hcache

omit [Fintype Key] in
theorem run_interpret_forgetfulWithBad_map_fst {β : Type}
    (program : OracleComp (Spec Key Block) β) (cache : Key → Cache Block) (bad : Bool) :
    ((OracleComp.interpret forgetfulWithBad program).run (cache, bad)).map
      (fun (a, st') => (a, st'.1)) =
    (OracleComp.interpret forgetfulAnswer program).run cache :=
  OracleComp.run_interpret_map_state forgetfulWithBad forgetfulAnswer Prod.fst
    forgetfulWithBad_map_fst program (cache, bad)




theorem abs_sub_uniformPerm_forgetful_le {β γ : Type}
    {program : OracleComp (Spec Key Block) β} {Q : ℕ}
    (hQ : IsQueryBounded program Q) (next : β → PMF γ) (c : γ) :
    |(((do
        let P ← PMF.pi (fun _ : Key => PMF.uniformOfFintype (Equiv.Perm Block))
        OracleComp.interpret (fun (q : Query Key Block) =>
          PMF.pure (evalPerm (P q.1) q.2)) program).bind next) c).toReal -
      (((((OracleComp.interpret forgetfulAnswer program).run (fun _ => [])).map
        Prod.fst).bind next) c).toReal| ≤
      (Q.choose 2 : ℝ) * (Fintype.card Block : ℝ)⁻¹ := by
  rw [uniform_interpret_eq_lazy,
    ← run_interpret_exactWithBad_map_fst program (fun _ => []) false
        (fun _ => isPartialBijection_nil),
    ← run_interpret_forgetfulWithBad_map_fst program (fun _ => []) false]
  simp only [pmf_norm]
  have hdiff := identicalUntilBad_exactWithBad_forgetfulWithBad.abs_sub_le
    program ((fun _ => []), false) (fun x => next x.1) c
  rw [identicalUntilBad_exactWithBad_forgetfulWithBad.bad_eq] at hdiff
  refine hdiff.trans ?_
  have hbad := toOuterMeasure_bad_forgetfulWithBad_le hQ (fun _ => [])
  have h_len : Finset.univ.sum (fun (k : Key) => ([] : Cache Block).length) = 0 := by simp
  rw [h_len, mul_zero, zero_add] at hbad
  have htop : ((Q.choose 2 : ℕ) : ℝ≥0∞) * (Fintype.card Block : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_inv] using
    ENNReal.toReal_mono htop hbad


end Finite

end Cslib.IdealCipher
