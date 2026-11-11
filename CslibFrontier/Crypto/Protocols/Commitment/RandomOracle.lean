/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Game.CloseTo
public import CslibFrontier.Crypto.Game.CloseTo.RandomOracle
public import CslibFrontier.Crypto.Negligible.Basic
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
public import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
public import CslibFrontier.Languages.Probabilistic.RandomOracle.Programming
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Tactic.Negligible

/-!
# Hash-based commitments in the random oracle model

Hash-based non-interactive commitment `(c, r) := (H(m, r), r)` in the lazy random oracle model
with oracle queries `M × R → Digest` ([BonehShoup2023], Section 8.12; [KatzLindell2020],
Section 6.5):

- **Completeness (`verify_commitOracle`, `eval_verify_commitOracle`)**: committing to `m` with
  opening randomness `r` against the shared memoizing random oracle and immediately verifying
  `(m, c, r)` returns `true` with probability `1` from every initial cache.
- **Concrete ROM hiding (`closeTo_hidingGame_hidingIdeal`, `advantage_hidingGame_le`)**: against
  any two-stage `ProbOracleComp` adversary making at most `q₁` queries before the challenge and
  at most `q₂` queries after receiving the challenge commitment `c = H(m_b, r)` for uniform
  `r ← R`, the distinguishing advantage in `hidingGame` is at most `2 * (q₁ + q₂) / |R|`.
- **Concrete ROM binding (`succProbability_bindingGame_le`)**: any `ProbOracleComp` adversary
  making at most `q` queries wins `bindingGame` (producing a single digest opening to two distinct
  messages `m₀ ≠ m₁` that both verify) with probability at most `(q + 2).choose 2 / |Digest|`,
  by reduction to `RandomOracle.toOuterMeasure_hasOutputCollision_runWith_memoize_uniform_le`.
- **Asymptotic bitstring corollaries (`negligible_advantage_hidingGame`,
  `negligible_succProbability_bindingGame`)**: polynomial query budgets and `2 ^ n ≤ |R n|`,
  `2 ^ n ≤ |Digest n|` yield negligible hiding advantage and binding failure.
- **Deterministic counterexample (`deterministicHidingAttack`,
  `advantage_hidingGame_deterministicHidingAttack`)**: without random salt (`R = Unit`), a
  `1`-query adversary distinguishes distinct messages `m₀ ≠ m₁` with exact advantage
  `1 - |Digest|⁻¹`.

## Main definitions

* `Cslib.Crypto.Protocols.ROMCommitment.oracle`: lazy uniform random oracle `M × R → Digest`.
* `Cslib.Crypto.Protocols.ROMCommitment.commitOracle`,
  `Cslib.Crypto.Protocols.ROMCommitment.verify`: commitment and verification oracle programs.
* `Cslib.Crypto.Protocols.ROMCommitment.HidingAdversary`,
  `Cslib.Crypto.Protocols.ROMCommitment.hidingGame`,
  `Cslib.Crypto.Protocols.ROMCommitment.hidingIdeal`: two-stage ROM hiding experiment and ideal
  challenge-independent game.
* `Cslib.Crypto.Protocols.ROMCommitment.bindingGame`: ROM binding experiment with shared cache.
* `Cslib.Crypto.Protocols.ROMCommitment.deterministicHidingAttack`: explicit attack for
  deterministic commitments (`R = Unit`).

## Main results

* `Cslib.Crypto.Protocols.ROMCommitment.verify_commitOracle`,
  `Cslib.Crypto.Protocols.ROMCommitment.eval_verify_commitOracle`: probability-one completeness.
* `Cslib.Crypto.Protocols.ROMCommitment.closeTo_runWith_memoize_cons`: generic `ProbOracleComp`
  single-entry cache-extension closeness for lazy random oracles.
* `Cslib.Crypto.Protocols.ROMCommitment.closeTo_hidingGame_hidingIdeal`,
  `Cslib.Crypto.Protocols.ROMCommitment.advantage_hidingGame_le`,
  `Cslib.Crypto.Protocols.ROMCommitment.negligible_advantage_hidingGame`: concrete and asymptotic
  ROM hiding bounds.
* `Cslib.Crypto.Protocols.ROMCommitment.succProbability_bindingGame_le`,
  `Cslib.Crypto.Protocols.ROMCommitment.negligible_succProbability_bindingGame`: concrete and
  asymptotic ROM binding bounds via output-collision birthday bounds.
* `Cslib.Crypto.Protocols.ROMCommitment.advantage_hidingGame_deterministicHidingAttack`: exact
  `1 - |Digest|⁻¹` break when `R = Unit`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 8.12.
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020],
  Section 6.5.
-/

public section

namespace Cslib.Crypto.Protocols.ROMCommitment

open Cslib Cslib.OracleComp Cslib.ProbOracleComp Cslib.RandomOracle Cslib.Crypto Cslib.Probability
open scoped ENNReal NNReal

section Helpers

variable {Query Value : Type} [BEq Query] [LawfulBEq Query]

omit [LawfulBEq Query] in
private theorem lookup_isSome_of_mem_support_memoize {dist : Query → PMF Value}
    {k : Query} {cache : List (Query × Value)} {v : Value} {cache' : List (Query × Value)}
    (hstep : (v, cache') ∈ (memoize dist k cache).support) :
    ∀ x, (cache.lookup x).isSome = true → (cache'.lookup x).isSome = true := by
  intro x hx
  rcases (mem_support_memoize_iff dist k cache (v, cache')).mp hstep with
    ⟨-, hc⟩ | ⟨-, -, hc⟩
  · dsimp only at hc
    rw [hc]
    exact hx
  · dsimp only at hc
    rw [hc]
    simp only [List.lookup]
    cases (x == k) with
    | true => rfl
    | false => exact hx

omit [LawfulBEq Query] in
private theorem lookup_isSome_of_mem_support_runWith_memoize {α : Type}
    (dist : Query → PMF Value) (prog : ProbOracleComp (fun _ : Query => Value) α)
    {cache cache' : List (Query × Value)} {res : α}
    (hmem : (res, cache') ∈ (ProbOracleComp.runWith (memoize dist) prog cache).support) :
    ∀ x, (cache.lookup x).isSome = true → (cache'.lookup x).isSome = true := by
  refine ProbOracleComp.runWith_invariant (memoize dist)
    (fun c => ∀ x, (cache.lookup x).isSome = true → (c.lookup x).isSome = true)
    (fun k c hinv ans c' hstep x hx =>
      lookup_isSome_of_mem_support_memoize hstep x (hinv x hx))
    prog cache (fun _ h => h) res cache' hmem

omit [LawfulBEq Query] in
private theorem runWith_memoize_suffix {α : Type} (dist : Query → PMF Value)
    (prog : ProbOracleComp (fun _ : Query => Value) α)
    {cache cache' : List (Query × Value)} {res : α}
    (hmem : (res, cache') ∈ (ProbOracleComp.runWith (memoize dist) prog cache).support) :
    ∃ added, cache' = added ++ cache := by
  refine ProbOracleComp.runWith_invariant (memoize dist)
    (fun c => ∃ added, c = added ++ cache) ?_ prog cache ⟨[], rfl⟩ res cache' hmem
  rintro k c ⟨added, rfl⟩ ans c' hstep
  rcases (mem_support_memoize_iff dist k (added ++ cache) (ans, c')).mp hstep with
    ⟨-, hc⟩ | ⟨-, -, hc⟩
  · dsimp only at hc
    exact ⟨added, hc⟩
  · dsimp only at hc
    exact ⟨(k, ans) :: added, hc⟩

omit [LawfulBEq Query] in
private theorem cache_length_of_mem_support_runWith_memoize {α : Type}
    (dist : Query → PMF Value) {prog : ProbOracleComp (fun _ : Query => Value) α} {q : ℕ}
    (hq : prog.IsQueryBounded q) {cache cache' : List (Query × Value)} {res : α}
    (hmem : (res, cache') ∈ (ProbOracleComp.runWith (memoize dist) prog cache).support) :
    cache'.length ≤ cache.length + q := by
  refine OracleComp.IsCostBounded.measure_le hq _ List.length (fun op c ans c' hstep => ?_) hmem
  cases op with
  | inl n =>
    change (ans, c') ∈ ((ProbComp.unifOracle n).map (·, c)).support at hstep
    obtain ⟨_, _, hpair⟩ := (PMF.mem_support_map_iff _ _ _).mp hstep
    cases hpair
    simp
  | inr k =>
    rcases (mem_support_memoize_iff dist k c (ans, c')).mp hstep with
      ⟨-, hc⟩ | ⟨-, -, hc⟩ <;> (dsimp only at hc; rw [hc]; simp)

private theorem closeTo_runWith_memoize_equiv {α : Type} (dist : Query → PMF Value)
    (target : Query) (value : Value) (prog : ProbOracleComp (fun _ : Query => Value) α)
    {c₁ c₂ : List (Query × Value)}
    (h1 : c₁.lookup target = some value)
    (h2 : c₂.lookup target = none)
    (hdiff : ∀ k ≠ target, c₁.lookup k = c₂.lookup k) :
    CloseTo
      ((ProbOracleComp.runWith (memoize dist) prog c₁).map Prod.fst)
      ((ProbOracleComp.runWith (memoize dist) prog c₂).map Prod.fst)
      ((ProbOracleComp.runWith (memoize dist) prog c₂).toOuterMeasure
        {x | (x.2.lookup target).isSome = true}) := by
  induction prog using ProbOracleComp.induction generalizing c₁ c₂ with
  | pure a =>
    simp only [ProbOracleComp.runWith_pure, PMF.pure_map]
    intro E
    exact le_add_of_nonneg_right zero_le
  | sample_bind n cont ih =>
    simp only [ProbOracleComp.runWith_sample_bind, PMF.map_bind, PMF.toOuterMeasure_bind_apply]
    exact CloseTo.bind_right_tsum _ fun a _ => ih a h1 h2 hdiff
  | query_bind key cont ih =>
    by_cases hkey : key = target
    · subst hkey
      have hprob1 : (ProbOracleComp.runWith (memoize dist)
          (ProbOracleComp.query key >>= cont) c₂).toOuterMeasure
          {x | (x.2.lookup key).isSome = true} = 1 := by
        rw [PMF.toOuterMeasure_apply_eq_one_iff]
        rintro ⟨res, cache'⟩ hmem
        simp only [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query,
          PMF.mem_support_bind_iff] at hmem
        obtain ⟨⟨d, c₂'⟩, hstep, hcont⟩ := hmem
        dsimp only at hcont
        rcases (mem_support_memoize_iff dist key c₂ (d, c₂')).mp hstep with
          ⟨hsome, _⟩ | ⟨-, -, hc⟩
        · dsimp only at hsome
          rw [h2] at hsome
          exact False.elim (Option.some_ne_none _ hsome.symm)
        · dsimp only at hc
          have hlook : (c₂'.lookup key).isSome = true := by rw [hc]; simp
          exact lookup_isSome_of_mem_support_runWith_memoize dist (cont d) hcont key hlook
      rw [hprob1]
      intro E
      exact (Cslib.Probability.PMF.toOuterMeasure_le_one _ E).trans le_add_self
    · have hlookup_eq : c₁.lookup key = c₂.lookup key := hdiff key hkey
      cases hcase : c₂.lookup key with
      | some ans =>
        have hcase1 : c₁.lookup key = some ans := hlookup_eq.trans hcase
        simp only [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query,
          memoize_of_some dist key c₁ ans hcase1, memoize_of_some dist key c₂ ans hcase,
          Probability.PMF.monad_pure_eq_pure, PMF.pure_bind]
        exact ih ans h1 h2 hdiff
      | none =>
        have hcase1 : c₁.lookup key = none := hlookup_eq.trans hcase
        simp only [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query,
          memoize_of_none dist key c₁ hcase1, memoize_of_none dist key c₂ hcase,
          Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
          PMF.bind_bind, PMF.pure_bind, PMF.map_bind, PMF.toOuterMeasure_bind_apply]
        refine CloseTo.bind_right_tsum (dist key) fun ans _ => ?_
        have hkey' : target ≠ key := Ne.symm hkey
        have hb : (target == key) = false := beq_false_of_ne hkey'
        refine ih ans ?_ ?_ ?_
        · simp [List.lookup, hb, h1]
        · simp [List.lookup, hb, h2]
        · intro k hk
          simp only [List.lookup]
          cases hbeq : (k == key) with
          | true => rfl
          | false => exact hdiff k hk

/-- **Prepending a fresh random-oracle cache entry (`ProbOracleComp.runWith`)**: inserting a single
entry `(target, value)` into a cache with `cache.lookup target = none` changes the output marginal
by at most the probability that the unmodified execution queries `target` (equivalently leaves
`target` present in its final cache). -/
theorem closeTo_runWith_memoize_cons {α : Type} (dist : Query → PMF Value)
    {cache : List (Query × Value)} {target : Query} (value : Value)
    (hnone : cache.lookup target = none)
    (prog : ProbOracleComp (fun _ : Query => Value) α) :
    CloseTo
      ((ProbOracleComp.runWith (memoize dist) prog ((target, value) :: cache)).map Prod.fst)
      ((ProbOracleComp.runWith (memoize dist) prog cache).map Prod.fst)
      ((ProbOracleComp.runWith (memoize dist) prog cache).toOuterMeasure
        {x | (x.2.lookup target).isSome = true}) :=
  closeTo_runWith_memoize_equiv dist target value prog
    (by simp) hnone (fun k hk => by
      simp only [List.lookup]
      cases hbeq : (k == target) with
      | true => exact absurd (beq_iff_eq.mp hbeq) hk
      | false => rfl)

end Helpers

section Scheme

variable (M R Digest : Type) [DecidableEq M] [DecidableEq R] [DecidableEq Digest]
  [Fintype Digest] [Nonempty Digest]

/-- Hash query interface for random-oracle commitments on message-salt pairs `M × R`. -/
abbrev HashSpec := fun _ : M × R => Digest

/-- The lazy uniform random oracle for `(M × R) → Digest`. -/
@[expose] noncomputable def oracle : (q : M × R) → StateT (List ((M × R) × Digest)) PMF Digest :=
  memoize (fun _ => PMF.uniformOfFintype Digest)

/-- Commit to message `m : M` with randomness `r : R` by querying the random oracle at `(m, r)`,
returning the commitment digest and opening `r`. -/
@[expose] def commitOracle {M R Digest : Type} (m : M) (r : R) :
    OracleComp (HashSpec M R Digest) (Digest × R) := do
  let c ← OracleComp.query (m, r)
  return (c, r)

/-- Verify a claimed opening `r : R` for message `m : M` and commitment `c : Digest` by checking
`H(m, r) == c`. -/
@[expose] def verify {M R Digest : Type} [DecidableEq Digest] (m : M) (c : Digest) (r : R) :
    OracleComp (HashSpec M R Digest) Bool := do
  let d ← OracleComp.query (m, r)
  return (c == d)

/-- Any initial cache running `commitOracle m r` followed by `verify m c r` against `oracle`
supports only `true` on verification. -/
theorem verify_commitOracle {M R Digest : Type} [DecidableEq M] [DecidableEq R] [DecidableEq Digest]
    [Fintype Digest] [Nonempty Digest] (m : M) (r : R) (cache : List ((M × R) × Digest)) :
    ∀ b cache', (b, cache') ∈
      ((OracleComp.interpret (oracle M R Digest) (do
        let co ← commitOracle m r
        verify m co.1 co.2)).run cache).support → b = true := by
  intro b cache' hmem
  simp only [commitOracle, verify, oracle, bind_assoc, pure_bind,
    OracleComp.run_interpret_bind, OracleComp.run_interpret_query,
    OracleComp.run_interpret_pure, Probability.PMF.monad_bind_eq_bind,
    Probability.PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff,
    PMF.mem_support_pure_iff] at hmem
  obtain ⟨⟨c, cache₁⟩, h₁, ⟨d, cache₂⟩, h₂, hEq⟩ := hmem
  dsimp only at h₁ h₂ hEq
  obtain ⟨rfl, -⟩ := Prod.mk.inj hEq
  have hlook : (cache₁.lookup (m, r)) = some c := by
    rcases (mem_support_memoize_iff _ (m, r) cache (c, cache₁)).mp h₁ with
      ⟨hsome, hcache⟩ | ⟨-, -, hc⟩
    · dsimp only at hsome hcache
      rw [hcache]
      exact hsome
    · dsimp only at hc
      rw [hc]
      simp
  rw [memoize_of_some _ (m, r) cache₁ c hlook] at h₂
  simp only [Probability.PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at h₂
  obtain ⟨hcd, -⟩ := h₂
  simp [hcd]

/-- Committing with `commitOracle m r` and immediately verifying returns `true` with probability
`1` from every initial cache. -/
theorem eval_verify_commitOracle {M R Digest : Type} [DecidableEq M] [DecidableEq R]
    [DecidableEq Digest] [Fintype Digest] [Nonempty Digest]
    (m : M) (r : R) (cache : List ((M × R) × Digest)) :
    (((OracleComp.interpret (oracle M R Digest) (do
      let co ← commitOracle m r
      verify m co.1 co.2)).run cache).map Prod.fst) = PMF.pure true := by
  let μ := ((OracleComp.interpret (oracle M R Digest) (do
    let co ← commitOracle m r
    verify m co.1 co.2)).run cache).map Prod.fst
  change μ = PMF.pure true
  have hfalse : μ false = 0 := by
    rw [PMF.apply_eq_zero_iff]
    intro hmem
    obtain ⟨⟨b, c'⟩, hsupp, hb⟩ := (PMF.mem_support_map_iff _ _ _).mp hmem
    have htrue : b = true := verify_commitOracle m r cache b c' hsupp
    dsimp only at hb
    rw [htrue] at hb
    exact Bool.noConfusion hb
  have hsum : μ false + μ true = 1 := by
    have ht := PMF.tsum_coe μ
    rwa [tsum_fintype, Fintype.sum_bool, add_comm] at ht
  have htrue : μ true = 1 := by simpa [hfalse] using hsum
  ext b
  cases b <;> simp [hfalse, htrue]

end Scheme

section Hiding

/-- A two-stage chosen-message hiding adversary in the random oracle model: stage 1 chooses two
messages `(m₀, m₁)` and a state `st`, and stage 2 receives the challenge digest `c = H(m_b, r)`
and guesses the bit `b`. Both stages share the same random oracle `M × R → Digest`. -/
structure HidingAdversary (M R Digest State : Type) where
  /-- Choose two candidate messages and save internal state. -/
  choose : ProbOracleComp (HashSpec M R Digest) ((M × M) × State)
  /-- Distinguish the challenge commitment using the saved state and shared oracle. -/
  guess : State → Digest → ProbOracleComp (HashSpec M R Digest) Bool

/-- Chosen-message ROM hiding experiment: stage 1 runs with oracle `oracle`, then the challenger
draws uniform salt `r ← R`, evaluates `c = H(m_b, r)` using the same oracle cache, and runs stage
2 on `(st, c)`. -/
@[expose] noncomputable def hidingGame {M R Digest State : Type} [DecidableEq M] [DecidableEq R]
    [Fintype R] [Nonempty R] [Fintype Digest] [Nonempty Digest]
    (adversary : HidingAdversary M R Digest State) (b : Bool) : PMF Bool := do
  let (((m₀, m₁), st), cache₁) ← ProbOracleComp.runWith (oracle M R Digest) adversary.choose []
  let r ← PMF.uniformOfFintype R
  let challenge ← oracle M R Digest (if b then m₁ else m₀, r) cache₁
  let out ← ProbOracleComp.runWith (oracle M R Digest)
    (adversary.guess st challenge.1) challenge.2
  return out.1

/-- Ideal hiding experiment where the challenge digest `c ← Digest` is drawn uniformly and
independently of `(m₀, m₁, r)` and never added to the random-oracle cache. -/
@[expose] noncomputable def hidingIdeal {M R Digest State : Type} [DecidableEq M] [DecidableEq R]
    [Fintype Digest] [Nonempty Digest]
    (adversary : HidingAdversary M R Digest State) : PMF Bool := do
  let (((_, _), st), cache₁) ← ProbOracleComp.runWith (oracle M R Digest) adversary.choose []
  let c ← PMF.uniformOfFintype Digest
  let out ← ProbOracleComp.runWith (oracle M R Digest) (adversary.guess st c) cache₁
  return out.1

private theorem uniformOfFintype_lookup_isSome_le
    {M R Digest : Type} [DecidableEq M] [DecidableEq R]
    [Fintype R] [Nonempty R] (cache : List ((M × R) × Digest)) (m : M) :
    (PMF.uniformOfFintype R).toOuterMeasure {r | (cache.lookup (m, r)).isSome = true} ≤
      (cache.length : ℝ≥0∞) / Fintype.card R := by
  have hsub : {r : R | (cache.lookup (m, r)).isSome = true} ⊆
      {r : R | ∃ e ∈ cache.map (fun entry => (entry.1.2, ())), e.1 = id r} := by
    intro r hr
    obtain ⟨e, he, hm⟩ := List.lookup_isSome_iff.mp hr
    refine ⟨(e.1.2, ()), List.mem_map_of_mem he, ?_⟩
    simp [(beq_iff_eq.mp hm).symm]
  refine (MeasureTheory.measure_mono hsub).trans ?_
  have hle := RandomOracle.toOuterMeasure_exists_mem_fst_eq_le (f := id)
    (μ := PMF.uniformOfFintype R) (δ := (Fintype.card R : ℝ≥0∞)⁻¹)
    (fun r => le_of_eq (by simp [PMF.map_id, PMF.uniformOfFintype_apply]))
    (cache.map (fun entry => (entry.1.2, ())))
  simpa only [List.length_map, div_eq_mul_inv] using hle

private theorem mem_newPrefix_of_lookup_append {Query Value : Type} [BEq Query] [LawfulBEq Query]
    {added base : List (Query × Value)} {q : Query}
    (hbase : base.lookup q = none)
    (happ : ((added ++ base).lookup q).isSome = true) :
    ∃ e ∈ added, e.1 = q := by
  induction added with
  | nil => simp [hbase] at happ
  | cons hd tl ih =>
    simp only [List.cons_append, List.lookup] at happ
    cases hbeq : (q == hd.1) with
    | true => exact ⟨hd, List.mem_cons_self, (beq_iff_eq.mp hbeq).symm⟩
    | false =>
      rw [hbeq] at happ
      obtain ⟨e, he, hq⟩ := ih happ
      exact ⟨e, List.mem_cons_of_mem hd he, hq⟩

/-- **Concrete ROM hiding (`CloseTo` against `hidingIdeal`)**: running a `q₁`-query Stage 1 and
`q₂`-query Stage 2 against `hidingGame adversary b` is within statistical distance `(q₁ + q₂) / |R|`
of `hidingIdeal adversary`, where the challenge is uniform and independent of `(m₀, m₁)`. -/
theorem closeTo_hidingGame_hidingIdeal {M R Digest State : Type} [DecidableEq M] [DecidableEq R]
    [Fintype R] [Nonempty R] [Fintype Digest] [Nonempty Digest]
    (adversary : HidingAdversary M R Digest State) {q₁ q₂ : ℕ}
    (hq₁ : adversary.choose.IsQueryBounded q₁)
    (hq₂ : ∀ st c, (adversary.guess st c).IsQueryBounded q₂) (b : Bool) :
    CloseTo (hidingGame adversary b) (hidingIdeal adversary)
      ((q₁ + q₂ : ℕ) / Fintype.card R) := by
  unfold hidingGame hidingIdeal
  simp only [Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure]
  refine CloseTo.bind_right _ fun ⟨⟨⟨m₀, m₁⟩, st⟩, cache₁⟩ hstage₁ => ?_
  have hlen₁ : cache₁.length ≤ q₁ := by
    simpa only [List.length_nil, zero_add] using
      cache_length_of_mem_support_runWith_memoize _ hq₁ hstage₁
  let m : M := if b then m₁ else m₀
  change CloseTo
    ((PMF.uniformOfFintype R).bind fun r =>
      (oracle M R Digest (m, r) cache₁).bind fun ch =>
        (ProbOracleComp.runWith (oracle M R Digest) (adversary.guess st ch.1) ch.2).map Prod.fst)
    ((PMF.uniformOfFintype Digest).bind fun c =>
      (ProbOracleComp.runWith (oracle M R Digest) (adversary.guess st c) cache₁).map Prod.fst)
    (((q₁ + q₂ : ℕ) : ℝ≥0∞) / Fintype.card R)
  have hideal_eq :
      ((PMF.uniformOfFintype Digest).bind fun c =>
        (ProbOracleComp.runWith (oracle M R Digest) (adversary.guess st c) cache₁).map Prod.fst) =
      ((PMF.uniformOfFintype R).bind fun _ =>
        ((PMF.uniformOfFintype Digest).bind fun c =>
          (ProbOracleComp.runWith (oracle M R Digest) (adversary.guess st c) cache₁).map
            Prod.fst)) := (PMF.bind_const _ _).symm
  rw [hideal_eq]
  let err₁ : R → ℝ≥0∞ := fun r => if (cache₁.lookup (m, r)).isSome then 1 else 0
  let err₂ : R → ℝ≥0∞ := fun r =>
    if (cache₁.lookup (m, r)).isSome then 0 else
      ∑' c : Digest, PMF.uniformOfFintype Digest c *
        (ProbOracleComp.runWith (oracle M R Digest) (adversary.guess st c) cache₁).toOuterMeasure
          {x | (x.2.lookup (m, r)).isSome = true}
  have hstep : CloseTo
      ((PMF.uniformOfFintype R).bind fun r =>
        (oracle M R Digest (m, r) cache₁).bind fun ch =>
          (ProbOracleComp.runWith (oracle M R Digest) (adversary.guess st ch.1) ch.2).map
            Prod.fst)
      ((PMF.uniformOfFintype R).bind fun _ =>
        ((PMF.uniformOfFintype Digest).bind fun c =>
          (ProbOracleComp.runWith (oracle M R Digest) (adversary.guess st c) cache₁).map
            Prod.fst))
      (∑' r : R, PMF.uniformOfFintype R r * (err₁ r + err₂ r)) := by
    refine CloseTo.bind_right_tsum (PMF.uniformOfFintype R) fun r _ => ?_
    cases hlook : cache₁.lookup (m, r) with
    | some _ =>
      have herr : err₁ r + err₂ r = 1 := by dsimp only [err₁, err₂]; rw [hlook]; simp
      rw [herr]
      intro E
      exact (Cslib.Probability.PMF.toOuterMeasure_le_one _ E).trans le_add_self
    | none =>
      have herr : err₁ r + err₂ r = ∑' c : Digest, PMF.uniformOfFintype Digest c *
          (ProbOracleComp.runWith (oracle M R Digest) (adversary.guess st c)
            cache₁).toOuterMeasure {x | (x.2.lookup (m, r)).isSome = true} := by
        dsimp only [err₁, err₂]; rw [hlook]; simp
      rw [herr]
      have hnone : oracle M R Digest (m, r) cache₁ =
          (PMF.uniformOfFintype Digest).map fun c => (c, ((m, r), c) :: cache₁) := by
        rw [oracle, memoize_of_none _ (m, r) cache₁ hlook]
        rfl
      rw [hnone, PMF.bind_map]
      refine CloseTo.bind_right_tsum (PMF.uniformOfFintype Digest) fun c _ => ?_
      exact closeTo_runWith_memoize_cons _ c hlook (adversary.guess st c)
  refine hstep.mono ?_
  have htsum_split :
      (∑' r : R, PMF.uniformOfFintype R r * (err₁ r + err₂ r)) =
        (∑' r : R, PMF.uniformOfFintype R r * err₁ r) +
          (∑' r : R, PMF.uniformOfFintype R r * err₂ r) := by
    simp only [mul_add, tsum_add]
  rw [htsum_split]
  have hsum1 : (∑' r : R, PMF.uniformOfFintype R r * err₁ r) ≤
      (q₁ : ℝ≥0∞) / Fintype.card R := by
    have hcongr : (∑' r : R, PMF.uniformOfFintype R r * err₁ r) =
        (PMF.uniformOfFintype R).toOuterMeasure {r | (cache₁.lookup (m, r)).isSome = true} := by
      rw [PMF.toOuterMeasure_apply]
      refine tsum_congr fun r => ?_
      rw [Set.indicator_apply]
      by_cases h : (cache₁.lookup (m, r)).isSome = true
      · simp only [err₁, Set.mem_ofPred_eq, h, ↓reduceIte, mul_one]
      · simp only [err₁, Set.mem_ofPred_eq, h, Bool.false_eq_true, ↓reduceIte, mul_zero]
    rw [hcongr]
    exact (uniformOfFintype_lookup_isSome_le cache₁ m).trans
      (ENNReal.div_le_div_right (Nat.cast_le.mpr hlen₁) _)
  have hsum2 : (∑' r : R, PMF.uniformOfFintype R r * err₂ r) ≤
      (q₂ : ℝ≥0∞) / Fintype.card R := by
    have hrewrite : ∀ r : R, PMF.uniformOfFintype R r * err₂ r =
        ∑' c : Digest, PMF.uniformOfFintype Digest c *
          (∑' x : Bool × List ((M × R) × Digest),
            ProbOracleComp.runWith (oracle M R Digest) (adversary.guess st c) cache₁ x *
              if cache₁.lookup (m, r) = none ∧ (x.2.lookup (m, r)).isSome = true
              then PMF.uniformOfFintype R r else 0) := by
      intro r
      cases hlook : cache₁.lookup (m, r) with
      | some _ =>
        dsimp only [err₂]; rw [hlook]; simp
      | none =>
        have herr_eq :
            PMF.uniformOfFintype R r * err₂ r =
              ∑' c : Digest, PMF.uniformOfFintype Digest c *
                (PMF.uniformOfFintype R r *
                  (ProbOracleComp.runWith (oracle M R Digest) (adversary.guess st c)
                    cache₁).toOuterMeasure {x | (x.2.lookup (m, r)).isSome = true}) := by
          dsimp only [err₂]
          rw [hlook]
          simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun c => ?_
          rw [mul_left_comm]
        rw [herr_eq]
        refine tsum_congr fun c => ?_
        congr 1
        rw [PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_left]
        refine tsum_congr fun x => ?_
        rw [Set.indicator_apply]
        by_cases hx : (x.2.lookup (m, r)).isSome = true
        · simp only [Set.mem_ofPred_eq, hx, ↓reduceIte, true_and, mul_comm]
        · simp only [Set.mem_ofPred_eq, hx, Bool.false_eq_true, ↓reduceIte, and_false, mul_zero]
    calc
      (∑' r : R, PMF.uniformOfFintype R r * err₂ r)
          = ∑' r : R, ∑' c : Digest, PMF.uniformOfFintype Digest c *
              ∑' x : Bool × List ((M × R) × Digest),
                ProbOracleComp.runWith (oracle M R Digest) (adversary.guess st c) cache₁ x *
                  if cache₁.lookup (m, r) = none ∧ (x.2.lookup (m, r)).isSome = true
                  then PMF.uniformOfFintype R r else 0 := tsum_congr hrewrite
      _ = ∑' c : Digest, PMF.uniformOfFintype Digest c *
            ∑' x : Bool × List ((M × R) × Digest),
              ProbOracleComp.runWith (oracle M R Digest) (adversary.guess st c) cache₁ x *
                ∑' r : R, if cache₁.lookup (m, r) = none ∧ (x.2.lookup (m, r)).isSome = true
                  then PMF.uniformOfFintype R r else 0 := by
            rw [tsum_comm]
            refine tsum_congr fun c => ?_
            rw [ENNReal.tsum_mul_left]
            refine congrArg _ ?_
            rw [tsum_comm]
            refine tsum_congr fun x => by rw [ENNReal.tsum_mul_left]
      _ ≤ ∑' c : Digest, PMF.uniformOfFintype Digest c *
            ∑' x : Bool × List ((M × R) × Digest),
              ProbOracleComp.runWith (oracle M R Digest) (adversary.guess st c) cache₁ x *
                ((q₂ : ℝ≥0∞) / Fintype.card R) := by
            refine tsum_le_tsum fun c => mul_le_mul_of_nonneg_left ?_ zero_le
            refine tsum_le_tsum fun x => ?_
            by_cases hmem : x ∈ (ProbOracleComp.runWith (oracle M R Digest)
                (adversary.guess st c) cache₁).support
            · refine mul_le_mul_of_nonneg_left ?_ zero_le
              obtain ⟨added, hcache'⟩ := runWith_memoize_suffix _ (adversary.guess st c) hmem
              have hlen₂ : x.2.length ≤ cache₁.length + q₂ :=
                cache_length_of_mem_support_runWith_memoize _ (hq₂ st c) hmem
              have hadded_len : added.length ≤ q₂ := by
                have hlen_eq : x.2.length = added.length + cache₁.length := by
                  rw [hcache', List.length_append]
                omega
              let keys := added.map (fun entry => (entry.1.2, ()))
              have hsub : {r : R | cache₁.lookup (m, r) = none ∧
                  (x.2.lookup (m, r)).isSome = true} ⊆
                  {r : R | ∃ e ∈ keys, e.1 = id r} := by
                rintro r ⟨hnone, hsome⟩
                rw [hcache'] at hsome
                obtain ⟨e, he, hm⟩ := mem_newPrefix_of_lookup_append hnone hsome
                refine ⟨(e.1.2, ()), List.mem_map_of_mem he, ?_⟩
                simp [hm]
              have htsum_eq : (∑' r : R,
                  if cache₁.lookup (m, r) = none ∧ (x.2.lookup (m, r)).isSome = true
                  then PMF.uniformOfFintype R r else 0) =
                  (PMF.uniformOfFintype R).toOuterMeasure
                    {r | cache₁.lookup (m, r) = none ∧ (x.2.lookup (m, r)).isSome = true} := by
                rw [PMF.toOuterMeasure_apply]
                refine tsum_congr fun r => ?_
                by_cases hcond : cache₁.lookup (m, r) = none ∧
                    (x.2.lookup (m, r)).isSome = true <;> simp [Set.indicator, hcond]
              rw [htsum_eq]
              refine (MeasureTheory.measure_mono hsub).trans ?_
              have hbound := RandomOracle.toOuterMeasure_exists_mem_fst_eq_le (f := id)
                (μ := PMF.uniformOfFintype R) (δ := (Fintype.card R : ℝ≥0∞)⁻¹)
                (fun r => le_of_eq (by simp [PMF.map_id, PMF.uniformOfFintype_apply])) keys
              have hlen_keys : keys.length ≤ q₂ := by simpa [keys] using hadded_len
              refine hbound.trans ?_
              simpa [div_eq_mul_inv] using
                mul_le_mul_of_nonneg_right (Nat.cast_le (α := ℝ≥0∞).mpr hlen_keys) zero_le
            · simp [(PMF.apply_eq_zero_iff _ _).mpr hmem]
      _ = (q₂ : ℝ≥0∞) / Fintype.card R := by
            have hx1 : ∀ c : Digest, (∑' x : Bool × List ((M × R) × Digest),
                ProbOracleComp.runWith (oracle M R Digest) (adversary.guess st c) cache₁ x *
                  ((q₂ : ℝ≥0∞) / Fintype.card R)) = (q₂ : ℝ≥0∞) / Fintype.card R := by
              intro c
              rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
            simp only [hx1, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  calc
    (∑' r : R, PMF.uniformOfFintype R r * err₁ r) +
        (∑' r : R, PMF.uniformOfFintype R r * err₂ r)
      ≤ (q₁ : ℝ≥0∞) / Fintype.card R + (q₂ : ℝ≥0∞) / Fintype.card R :=
          add_le_add hsum1 hsum2
    _ = ((q₁ + q₂ : ℕ) : ℝ≥0∞) / Fintype.card R := by
          rw [Nat.cast_add, ENNReal.add_div]

/-- **Concrete ROM hiding advantage bound**: any two-stage adversary making at most `q₁` queries
before the challenge and at most `q₂` queries after has distinguishing advantage at most
`2 * (q₁ + q₂) / |R|`. -/
theorem advantage_hidingGame_le {M R Digest State : Type} [DecidableEq M] [DecidableEq R]
    [Fintype R] [Nonempty R] [Fintype Digest] [Nonempty Digest]
    (adversary : HidingAdversary M R Digest State) {q₁ q₂ : ℕ}
    (hq₁ : adversary.choose.IsQueryBounded q₁)
    (hq₂ : ∀ st c, (adversary.guess st c).IsQueryBounded q₂) :
    Game.advantage (hidingGame adversary false) (hidingGame adversary true) ≤
      ((2 * (q₁ + q₂) : ℕ) : ℝ≥0) / Fintype.card R := by
  have h0 := closeTo_hidingGame_hidingIdeal adversary hq₁ hq₂ false
  have h1 := closeTo_hidingGame_hidingIdeal adversary hq₁ hq₂ true
  have htri : CloseTo (hidingGame adversary false) (hidingGame adversary true)
      ((2 * (q₁ + q₂) : ℕ) / Fintype.card R) := by
    refine (h0.trans h1.symm).mono ?_
    have hcalc : ((q₁ + q₂ : ℕ) : ℝ≥0∞) / Fintype.card R +
        ((q₁ + q₂ : ℕ) : ℝ≥0∞) / Fintype.card R =
        ((2 * (q₁ + q₂) : ℕ) : ℝ≥0∞) / Fintype.card R := by
      rw [← ENNReal.add_div, ← two_mul, Nat.cast_mul, Nat.cast_ofNat]
    exact hcalc.le
  rw [← ENNReal.coe_le_coe]
  have hcoe : (((((2 * (q₁ + q₂) : ℕ) : ℝ≥0) / Fintype.card R : ℝ≥0)) : ℝ≥0∞) =
      ((2 * (q₁ + q₂) : ℕ) : ℝ≥0∞) / Fintype.card R := by
    rw [ENNReal.coe_div (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), ENNReal.coe_natCast,
      ENNReal.coe_natCast]
  rw [hcoe]
  exact Game.closeTo_iff_coe_advantage_le.mp htri

/-- **Asymptotic ROM hiding**: for any sequence of schemes with `2 ^ n ≤ |R n|` and polynomially
bounded query schedules `(q₁ n, q₂ n)`, the ROM hiding advantage is `Negligible`. -/
theorem negligible_advantage_hidingGame {M R Digest State : ℕ → Type}
    [∀ n, DecidableEq (M n)] [∀ n, DecidableEq (R n)]
    [∀ n, Fintype (R n)] [∀ n, Nonempty (R n)] [∀ n, Fintype (Digest n)]
    [∀ n, Nonempty (Digest n)]
    (adversary : ∀ n, HidingAdversary (M n) (R n) (Digest n) (State n))
    {q₁ q₂ : ℕ → ℕ}
    (hq₁ : ∀ n, (adversary n).choose.IsQueryBounded (q₁ n))
    (hq₂ : ∀ n st c, ((adversary n).guess st c).IsQueryBounded (q₂ n))
    (hp₁ : PolynomiallyBounded q₁) (hp₂ : PolynomiallyBounded q₂)
    (hsize : ∀ n, 2 ^ n ≤ Fintype.card (R n)) :
    Negligible fun n =>
      Game.advantage (hidingGame (adversary n) false) (hidingGame (adversary n) true) := by
  have hp_num : PolynomiallyBounded (fun n => 2 * (q₁ n + q₂ n)) :=
    (PolynomiallyBounded.const 2).mul (hp₁.add hp₂)
  have hneg : Negligible (fun n => ((2 * (q₁ n + q₂ n) : ℕ) : ℝ≥0) / (2 ^ n : ℝ≥0)) := by
    simpa only [div_eq_mul_inv, inv_pow] using
      (negligible_geometric (ratio := 2⁻¹) (by norm_num)).polynomiallyBounded_mul hp_num
  refine negligible_of_le hneg fun n => (advantage_hidingGame_le (adversary n) (hq₁ n)
    (hq₂ n)).trans ?_
  have hcard : ((2 ^ n : ℕ) : ℝ≥0) ≤ Fintype.card (R n) := Nat.cast_le.mpr (hsize n)
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    div_le_div_of_nonneg_left zero_le (by exact_mod_cast Nat.two_pow_pos n) hcard

/-- Deterministic commitment adversary breaking hiding when `R = Unit` (no random salt):
picks distinct messages `m₀ ≠ m₁`, ignores state, queries `H(m₁, ())`, and checks equality
with the challenge digest. -/
@[expose] def deterministicHidingAttack (M Digest : Type) [DecidableEq Digest] (m₀ m₁ : M) :
    HidingAdversary M Unit Digest Unit where
  choose := pure ((m₀, m₁), ())
  guess _ c := do
    let d ← ProbOracleComp.query (spec := HashSpec M Unit Digest) (m₁, ())
    return (c == d)

theorem isQueryBounded_deterministicHidingAttack (M Digest : Type) [DecidableEq Digest]
    (m₀ m₁ : M) :
    (deterministicHidingAttack M Digest m₀ m₁).choose.IsQueryBounded 0 ∧
      ∀ st c, ((deterministicHidingAttack M Digest m₀ m₁).guess st c).IsQueryBounded 1 := by
  refine ⟨OracleComp.IsCostBounded.pure _ 0, fun _ c => ?_⟩
  exact ((ProbOracleComp.IsQueryBounded.query (spec := HashSpec M Unit Digest) (m₁, ())).bind
    fun d => OracleComp.IsCostBounded.pure (c == d) 0).mono (by omega)

/-- **Deterministic (`R = Unit`) hiding attack**: without salt, `deterministicHidingAttack`
distinguishes `m₀ ≠ m₁` with exact advantage `1 - |Digest|⁻¹` (hence `≥ 1 / 2` whenever
`2 ≤ |Digest|`). -/
theorem advantage_hidingGame_deterministicHidingAttack {M Digest : Type}
    [DecidableEq M] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest]
    {m₀ m₁ : M} (hne : m₀ ≠ m₁) :
    Game.advantage
      (hidingGame (deterministicHidingAttack M Digest m₀ m₁) false)
      (hidingGame (deterministicHidingAttack M Digest m₀ m₁) true) =
      1 - (Fintype.card Digest : ℝ≥0)⁻¹ := by
  have htrue : hidingGame (deterministicHidingAttack M Digest m₀ m₁) true = PMF.pure true := by
    simp only [hidingGame, deterministicHidingAttack, ProbOracleComp.runWith_pure,
      Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
      PMF.pure_bind, ↓reduceIte, oracle, memoize_of_none _ (m₁, ()) [] rfl,
      PMF.bind_bind]
    have hbranch : ∀ c : Digest,
        ((ProbOracleComp.runWith (memoize (fun _ => PMF.uniformOfFintype Digest))
          (ProbOracleComp.query (spec := HashSpec M Unit Digest) (m₁, ()) >>= fun d =>
            pure (c == d)) [((m₁, ()), c)]).map Prod.fst) = PMF.pure true := by
      intro c
      simp only [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query,
        ProbOracleComp.runWith_pure]
      rw [memoize_of_some _ (m₁, ()) [((m₁, ()), c)] c (by simp [List.lookup])]
      simp [Probability.PMF.monad_pure_eq_pure, PMF.pure_bind, PMF.pure_map]
    have hstep :
        ((PMF.uniformOfFintype Digest).bind fun c =>
          ((ProbOracleComp.runWith (memoize (fun _ => PMF.uniformOfFintype Digest))
            (ProbOracleComp.query (spec := HashSpec M Unit Digest) (m₁, ()) >>= fun d =>
              pure (c == d)) [((m₁, ()), c)]).map Prod.fst)) = PMF.pure true := by
      have : (fun c => ((ProbOracleComp.runWith (memoize (fun _ => PMF.uniformOfFintype Digest))
          (ProbOracleComp.query (spec := HashSpec M Unit Digest) (m₁, ()) >>= fun d =>
            pure (c == d)) [((m₁, ()), c)]).map Prod.fst)) = fun _ => PMF.pure true :=
        funext hbranch
      rw [this, PMF.bind_const]
    have hcomm :
        ((PMF.uniformOfFintype Unit).bind fun _ =>
          (PMF.uniformOfFintype Digest).bind fun c =>
            ((ProbOracleComp.runWith (memoize (fun _ => PMF.uniformOfFintype Digest))
              (ProbOracleComp.query (spec := HashSpec M Unit Digest) (m₁, ()) >>= fun d =>
                pure (c == d)) [((m₁, ()), c)]).bind fun out => PMF.pure out.1)) =
          PMF.pure true := by
      rw [PMF.bind_const]
      exact hstep
    exact hcomm
  have hfalse : (hidingGame (deterministicHidingAttack M Digest m₀ m₁) false) true =
      (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
    have hneq : ((m₁, ()) == ((m₀, ()) : M × Unit)) = false := by
      simp [Ne.symm hne]
    simp only [hidingGame, deterministicHidingAttack, ProbOracleComp.runWith_pure,
      Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
      PMF.pure_bind, Bool.false_eq_true, ↓reduceIte, oracle,
      memoize_of_none _ (m₀, ()) [] rfl, PMF.bind_bind]
    have hbranch : ∀ c : Digest,
        ((ProbOracleComp.runWith (memoize (fun _ => PMF.uniformOfFintype Digest))
          (ProbOracleComp.query (spec := HashSpec M Unit Digest) (m₁, ()) >>= fun d =>
            pure (c == d)) [((m₀, ()), c)]).map Prod.fst) =
        (PMF.uniformOfFintype Digest).map (fun d => c == d) := by
      intro c
      simp only [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query,
        ProbOracleComp.runWith_pure, Probability.PMF.monad_bind_eq_bind,
        Probability.PMF.monad_pure_eq_pure, memoize_of_none _ (m₁, ()) [((m₀, ()), c)]
          (by simp [List.lookup, hneq]),
        PMF.bind_bind, PMF.pure_bind, PMF.map_bind, PMF.pure_map]
      rfl
    have hunif_r : (PMF.uniformOfFintype Unit) = PMF.pure () := by
      ext u; cases u; simp [PMF.uniformOfFintype_apply]
    rw [hunif_r, PMF.pure_bind]
    simp only [PMF.bind_apply, tsum_fintype, PMF.uniformOfFintype_apply,
      PMF.pure_apply]
    calc
      ∑ c : Digest, (Fintype.card Digest : ℝ≥0∞)⁻¹ *
          ((ProbOracleComp.runWith (memoize (fun _ => PMF.uniformOfFintype Digest))
            (ProbOracleComp.query (spec := HashSpec M Unit Digest) (m₁, ()) >>= fun d =>
              pure (c == d)) [((m₀, ()), c)]).bind fun out => PMF.pure out.1) true
        = ∑ c : Digest, (Fintype.card Digest : ℝ≥0∞)⁻¹ *
            ((PMF.uniformOfFintype Digest).map (fun d => c == d)) true := by
            refine Finset.sum_congr rfl fun c _ => ?_
            have hbr := hbranch c
            have heq : ((ProbOracleComp.runWith (memoize (fun _ => PMF.uniformOfFintype Digest))
                (ProbOracleComp.query (spec := HashSpec M Unit Digest) (m₁, ()) >>= fun d =>
                  pure (c == d)) [((m₀, ()), c)]).bind fun out => PMF.pure out.1) =
                ((ProbOracleComp.runWith (memoize (fun _ => PMF.uniformOfFintype Digest))
                  (ProbOracleComp.query (spec := HashSpec M Unit Digest) (m₁, ()) >>= fun d =>
                    pure (c == d)) [((m₀, ()), c)]).map Prod.fst) := rfl
            rw [heq, hbr]
      _ = ∑ c : Digest, (Fintype.card Digest : ℝ≥0∞)⁻¹ * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
            refine Finset.sum_congr rfl fun c _ => ?_
            have h1 : ((PMF.uniformOfFintype Digest).map (fun d => c == d)) true =
                (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
              rw [PMF.map_apply, tsum_fintype]
              refine Eq.trans (Finset.sum_congr rfl (g := fun d =>
                  if d = c then (Fintype.card Digest : ℝ≥0∞)⁻¹ else 0) fun d _ => ?_) ?_
              · by_cases hcd : d = c
                · subst hcd; simp [PMF.uniformOfFintype_apply]
                · have hbf : (c == d) = false := beq_false_of_ne (Ne.symm hcd)
                  simp [hcd, hbf]
              · simp
            rw [h1]
      _ = (Fintype.card Digest : ℝ≥0∞) *
            ((Fintype.card Digest : ℝ≥0∞)⁻¹ * (Fintype.card Digest : ℝ≥0∞)⁻¹) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
            have hne0 : (Fintype.card Digest : ℝ≥0∞) ≠ 0 :=
              Nat.cast_ne_zero.mpr Fintype.card_ne_zero
            have hntop : (Fintype.card Digest : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
            rw [← mul_assoc, ENNReal.mul_inv_cancel hne0 hntop, one_mul]
  rw [Game.advantage, htrue]
  have hp0 : Game.succProbability (hidingGame (deterministicHidingAttack M Digest m₀ m₁) false) =
      (Fintype.card Digest : ℝ≥0)⁻¹ := by
    rw [Game.succProbability, ← ENNReal.coe_inj,
      ENNReal.coe_toNNReal ((hidingGame _ false).apply_ne_top true), hfalse,
      ENNReal.coe_inv (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), ENNReal.coe_natCast]
  have hp1 : Game.succProbability (PMF.pure true) = 1 := by
    simp [Game.succProbability]
  have hle : ((Fintype.card Digest : ℝ≥0)⁻¹) ≤ 1 := by
    have h1 : (1 : ℝ≥0) ≤ Fintype.card Digest := Nat.one_le_cast.mpr Fintype.card_pos
    exact inv_le_one_of_one_le₀ h1
  rw [hp0, hp1, ← NNReal.coe_inj, coe_nndist, NNReal.dist_eq, abs_sub_comm,
    abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hle)), NNReal.coe_sub hle, NNReal.coe_one]

end Hiding

section Binding

/-- Joint ROM binding program: runs a binding adversary `forger` returning `(c, (m₀, r₀), (m₁, r₁))`
and runs both oracle verifications `verify m₀ c r₀` and `verify m₁ c r₁` against the shared random
oracle. -/
@[expose] def bindingProgram {M R Digest : Type} [DecidableEq M] [DecidableEq Digest]
    (forger : ProbOracleComp (HashSpec M R Digest) (Digest × (M × R) × (M × R))) :
    ProbOracleComp (HashSpec M R Digest) Bool := do
  let (c, o₀, o₁) ← forger
  let v₀ ← OracleComp.liftRight (spec₁ := unifSpec) (verify o₀.1 c o₀.2)
  let v₁ ← OracleComp.liftRight (spec₁ := unifSpec) (verify o₁.1 c o₁.2)
  return (decide (o₀.1 ≠ o₁.1) && v₀ && v₁)

private theorem liftRight_verify {M R Digest : Type} [DecidableEq Digest]
    (m : M) (c : Digest) (r : R) :
    OracleComp.liftRight (spec₁ := unifSpec)
      (verify m c r : OracleComp (HashSpec M R Digest) Bool) =
      (ProbOracleComp.query (spec := HashSpec M R Digest) (m, r) >>= fun d => pure (c == d)) := by
  simp only [verify, OracleComp.liftRight_bind, OracleComp.liftRight_query,
    OracleComp.liftRight_pure]
  rfl

theorem isQueryBounded_bindingProgram {M R Digest : Type} [DecidableEq M] [DecidableEq Digest]
    (forger : ProbOracleComp (HashSpec M R Digest) (Digest × (M × R) × (M × R))) {q : ℕ}
    (hq : forger.IsQueryBounded q) :
    (bindingProgram forger).IsQueryBounded (q + 2) := by
  have hv (m : M) (c : Digest) (r : R) :
      ProbOracleComp.IsQueryBounded
        (OracleComp.liftRight (spec₁ := unifSpec) (verify m c r)) 1 := by
    rw [liftRight_verify]
    exact ((ProbOracleComp.IsQueryBounded.query (spec := HashSpec M R Digest) (m, r)).bind
      fun d => OracleComp.IsCostBounded.pure (c == d) 0).mono (by omega)
  unfold bindingProgram
  refine ((hq.bind fun (c, o₀, o₁) =>
    ((hv o₀.1 c o₀.2).bind fun _ =>
      ((hv o₁.1 c o₁.2).bind fun _ =>
        OracleComp.IsCostBounded.pure _ 0)))).mono (by omega)

/-- ROM binding game: runs `bindingProgram forger` from the empty random-oracle cache. -/
@[expose] noncomputable def bindingGame {M R Digest : Type} [DecidableEq M] [DecidableEq R]
    [DecidableEq Digest] [Fintype Digest] [Nonempty Digest]
    (forger : ProbOracleComp (HashSpec M R Digest) (Digest × (M × R) × (M × R))) : PMF Bool :=
  (ProbOracleComp.runWith (oracle M R Digest) (bindingProgram forger) []).map Prod.fst

private theorem mem_cache_of_mem_support_memoize {Query Value : Type} [BEq Query]
    (dist : Query → PMF Value) {k : Query} {cache : List (Query × Value)}
    {v : Value} {cache' : List (Query × Value)}
    (hstep : (v, cache') ∈ (memoize dist k cache).support) :
    ∀ e ∈ cache, e ∈ cache' := by
  intro e he
  rcases (mem_support_memoize_iff dist k cache (v, cache')).mp hstep with
    ⟨-, hc⟩ | ⟨-, -, hc⟩
  · dsimp only at hc
    rw [hc]
    exact he
  · dsimp only at hc
    rw [hc]
    exact List.mem_cons_of_mem (k, v) he

private theorem mem_of_mem_support_verify {M R Digest : Type} [DecidableEq M] [DecidableEq R]
    [DecidableEq Digest] [Fintype Digest] [Nonempty Digest]
    {m : M} {c : Digest} {r : R} {cache cache' : List ((M × R) × Digest)} {v : Bool}
    (hmem : (v, cache') ∈ (ProbOracleComp.runWith (oracle M R Digest)
      (OracleComp.liftRight (spec₁ := unifSpec) (verify m c r)) cache).support)
    (hv : v = true) :
    ((m, r), c) ∈ cache' := by
  subst hv
  rw [liftRight_verify, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query] at hmem
  simp only [ProbOracleComp.runWith_pure, PMF.mem_support_bind_iff,
    PMF.mem_support_pure_iff] at hmem
  obtain ⟨⟨d, c₁⟩, hstep, heq⟩ := hmem
  dsimp only at hstep heq
  obtain ⟨hd, hc'⟩ := Prod.mk.inj heq
  rw [hc']
  have hc : c = d := beq_iff_eq.mp hd.symm
  subst hc
  rcases (mem_support_memoize_iff _ (m, r) cache (c, c₁)).mp hstep with
    ⟨hsome, hc₁⟩ | ⟨-, -, hc₁⟩
  · dsimp only at hsome hc₁
    rw [hc₁]
    obtain ⟨before, after, hlist, -⟩ := List.lookup_eq_some_iff.mp hsome
    simp [hlist]
  · dsimp only at hc₁
    rw [hc₁]
    exact List.mem_cons_self

/-- **Concrete ROM binding bound**: any `ProbOracleComp` adversary making at most `q` queries wins
`bindingGame` with probability at most `(q + 2).choose 2 / |Digest|`, directly by reduction to
`RandomOracle.toOuterMeasure_hasOutputCollision_runWith_memoize_uniform_le`. -/
theorem succProbability_bindingGame_le {M R Digest : Type} [DecidableEq M] [DecidableEq R]
    [DecidableEq Digest] [Fintype Digest] [Nonempty Digest]
    (forger : ProbOracleComp (HashSpec M R Digest) (Digest × (M × R) × (M × R))) {q : ℕ}
    (hq : forger.IsQueryBounded q) :
    Game.succProbability (bindingGame forger) ≤
      (((q + 2).choose 2 : ℕ) : ℝ≥0) / Fintype.card Digest := by
  let μ := ProbOracleComp.runWith (oracle M R Digest) (bindingProgram forger) []
  have hcoll : ∀ x ∈ μ.support, x.1 = true → HasOutputCollision x.2 := by
    rintro ⟨bit, cache⟩ hmem rfl
    dsimp only [μ, bindingProgram] at hmem
    rw [ProbOracleComp.runWith_bind, PMF.mem_support_bind_iff] at hmem
    obtain ⟨⟨⟨c, o₀, o₁⟩, cache₁⟩, -, hrest⟩ := hmem
    rw [ProbOracleComp.runWith_bind, PMF.mem_support_bind_iff] at hrest
    obtain ⟨⟨v₀, cache₂⟩, hv₀, hrest₂⟩ := hrest
    rw [ProbOracleComp.runWith_bind, PMF.mem_support_bind_iff] at hrest₂
    obtain ⟨⟨v₁, cache₃⟩, hv₁, hret⟩ := hrest₂
    rw [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff] at hret
    obtain ⟨hbool, hcache⟩ := Prod.mk.inj hret
    dsimp only at hbool hcache
    subst hcache
    have hne_bool : decide (o₀.1 ≠ o₁.1) = true := by
      revert hbool
      cases decide (o₀.1 ≠ o₁.1) <;> cases v₀ <;> cases v₁ <;> simp
    have hv₀_true : v₀ = true := by
      revert hbool
      cases decide (o₀.1 ≠ o₁.1) <;> cases v₀ <;> cases v₁ <;> simp
    have hv₁_true : v₁ = true := by
      revert hbool
      cases decide (o₀.1 ≠ o₁.1) <;> cases v₀ <;> cases v₁ <;> simp
    have hne : o₀.1 ≠ o₁.1 := of_decide_eq_true hne_bool
    have hmem₀_c₂ : (o₀, c) ∈ cache₂ := mem_of_mem_support_verify hv₀ hv₀_true
    have hmem₀ : (o₀, c) ∈ cache := by
      rw [liftRight_verify, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query] at hv₁
      simp only [ProbOracleComp.runWith_pure, PMF.mem_support_bind_iff,
        PMF.mem_support_pure_iff] at hv₁
      obtain ⟨⟨d, c'⟩, hstep, heq'⟩ := hv₁
      dsimp only at hstep heq'
      obtain ⟨-, hc'⟩ := Prod.mk.inj heq'
      rw [hc']
      exact mem_cache_of_mem_support_memoize _ hstep (o₀, c) hmem₀_c₂
    have hmem₁ : (o₁, c) ∈ cache := mem_of_mem_support_verify hv₁ hv₁_true
    refine ⟨(o₀, c), hmem₀, (o₁, c), hmem₁, ?_, rfl⟩
    intro heq_key
    exact hne (congrArg Prod.fst heq_key)
  have hle_enn : (μ.map Prod.fst) true ≤ μ.toOuterMeasure {x | HasOutputCollision x.2} := by
    rw [PMF.map_apply, PMF.toOuterMeasure_apply]
    refine tsum_le_tsum fun x => ?_
    by_cases hmem : x ∈ μ.support
    · by_cases hx : x.1 = true
      · have hc := hcoll x hmem hx
        simp [Set.indicator, hx, hc]
      · simp [Set.indicator, hx]
    · simp [(PMF.apply_eq_zero_iff μ x).mpr hmem]
  have hbd : μ.toOuterMeasure {x | HasOutputCollision x.2} ≤
      (((q + 2).choose 2 : ℕ) : ℝ≥0∞) / Fintype.card Digest := by
    simpa only [μ, oracle] using
      RandomOracle.toOuterMeasure_hasOutputCollision_runWith_memoize_uniform_le
        (isQueryBounded_bindingProgram forger hq)
  rw [← ENNReal.coe_le_coe]
  have hcoe : (((((q + 2).choose 2 : ℕ) : ℝ≥0) / Fintype.card Digest : ℝ≥0) : ℝ≥0∞) =
      (((q + 2).choose 2 : ℕ) : ℝ≥0∞) / Fintype.card Digest := by
    rw [ENNReal.coe_div (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), ENNReal.coe_natCast,
      ENNReal.coe_natCast]
  rw [hcoe, Game.succProbability, ENNReal.coe_toNNReal ((bindingGame forger).apply_ne_top true)]
  exact hle_enn.trans hbd

/-- **Asymptotic ROM binding**: for any sequence of schemes with `2 ^ n ≤ |Digest n|` and
polynomially bounded query budget `q n`, the ROM binding success probability is `Negligible`. -/
theorem negligible_succProbability_bindingGame {M R Digest : ℕ → Type}
    [∀ n, DecidableEq (M n)] [∀ n, DecidableEq (R n)] [∀ n, DecidableEq (Digest n)]
    [∀ n, Fintype (Digest n)] [∀ n, Nonempty (Digest n)]
    (forger : ∀ n, ProbOracleComp (HashSpec (M n) (R n) (Digest n))
      (Digest n × (M n × R n) × (M n × R n)))
    {q : ℕ → ℕ} (hq : ∀ n, (forger n).IsQueryBounded (q n))
    (hp : PolynomiallyBounded q) (hsize : ∀ n, 2 ^ n ≤ Fintype.card (Digest n)) :
    Negligible fun n => Game.succProbability (bindingGame (forger n)) := by
  have hq2 : PolynomiallyBounded (fun n => q n + 2) := hp.add (PolynomiallyBounded.const 2)
  have hchoose : PolynomiallyBounded (fun n => (q n + 2).choose 2) := by
    refine PolynomiallyBounded.mono_of_le (g := fun n => (q n + 2) ^ 2) (hq2.pow 2) fun n => ?_
    change (q n + 2).choose 2 ≤ (q n + 2) ^ 2
    rw [Nat.choose_two_right, sq]
    exact (Nat.div_le_self _ 2).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  have hneg : Negligible (fun n => (((q n + 2).choose 2 : ℕ) : ℝ≥0) / (2 ^ n : ℝ≥0)) := by
    simpa only [div_eq_mul_inv, inv_pow] using
      (negligible_geometric (ratio := 2⁻¹) (by norm_num)).polynomiallyBounded_mul hchoose
  refine negligible_of_le hneg fun n =>
    (succProbability_bindingGame_le (forger n) (hq n)).trans ?_
  have hcard : ((2 ^ n : ℕ) : ℝ≥0) ≤ Fintype.card (Digest n) := Nat.cast_le.mpr (hsize n)
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    div_le_div_of_nonneg_left zero_le (by exact_mod_cast Nat.two_pow_pos n) hcard

end Binding

end Cslib.Crypto.Protocols.ROMCommitment
