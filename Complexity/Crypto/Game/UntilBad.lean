/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.Oracle
public import Complexity.Crypto.Game
public import Complexity.Languages.Probabilistic.Oracle.QueryCount
public import Complexity.Languages.Probabilistic.UntilBad
import Complexity.Probability.PMF

/-!
# Game hops that are identical until bad

Two games that run one program against stateful handlers that agree until a bad state, followed by
the same final step, have advantage at most the probability of reaching a bad state
(`OracleComp.IdenticalUntilBad.advantage_le`, [BonehShoup2023], Theorem 4.7). This is the
two-sided difference lemma `OracleComp.IdenticalUntilBad.abs_sub_le` in the form that composes
with `Game.advantage_triangle`.

When a `WordOracleComp Unit` program interacts with a secret-dependent stateless deterministic
oracle `o₁ τ` whose replies agree with a secret-independent clean oracle `o₂` unless a per-query
bad predicate `isBad τ req` holds (with secret-dependent continuation `next τ`),
`Game.runStatelessOracle_bind_le` and `Game.advantage_runStatelessOracle_bind_le` bound the
resulting `μ.bind` acceptance-probability difference and `Game.advantage` by `Q * δ` (respectively
`Q / q` when each query hits a bad secret with probability at most `q⁻¹`).

## Main definitions

* `Cslib.Crypto.Game.runStatelessOracle`: run a `WordOracleComp Unit α` against a stateless
  deterministic word oracle `o : List Bool → List Bool` and feed its output to `next : α → Game`.
* `Cslib.Crypto.Game.finderPhase2Oracle`, `Cslib.Crypto.Game.runFinderOracle`: stateful witness
  finder oracle handler that answers with `o₂` while recording `some (extract req)` whenever
  `isBad req` holds.

## Main results

* `Cslib.OracleComp.IdenticalUntilBad.advantage_le`: the advantage of an identical-until-bad hop.
* `Cslib.Crypto.Game.runStatelessOracle_pure`,
  `Cslib.Crypto.Game.runStatelessOracle_query_inl`,
  `Cslib.Crypto.Game.runStatelessOracle_query_inr`,
  `Cslib.Crypto.Game.bind_runStatelessOracle_comm`,
  `Cslib.Crypto.Game.advantage_runStatelessOracle_le_of_support`: structural and mixture laws for
  `runStatelessOracle`.
* `Cslib.Crypto.Game.runStatelessOracle_bind_le`,
  `Cslib.Crypto.Game.advantage_runStatelessOracle_bind_le`: stateless-oracle until-bad bounds with a
  secret-dependent continuation and a secret-independent clean oracle.
* `Cslib.Crypto.Game.runStatelessOracle_le_runFinderOracle`: stateless-oracle until-bad bound into
  a witness-finding game (`runFinderOracle`).
* `Cslib.Crypto.Game.advantage_uniform_bind_of_eq_of_ne`: single-exceptional-point advantage bound
  `1 / q` for two `ZMod q`-indexed game families.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Theorem 4.7.
-/

@[expose] public section

namespace Cslib.OracleComp.IdenticalUntilBad

open Crypto

variable {ι σ α : Type} {spec : ι → Type} {first second : (q : ι) → StateT σ PMF (spec q)}
  {bad : σ → Prop}

/-- **The difference lemma** ([BonehShoup2023], Theorem 4.7): games that run a program against
handlers agreeing until a bad state, followed by the same final step, have advantage at most the
probability of reaching a bad state. -/
theorem advantage_le (h : IdenticalUntilBad first second bad) (program : OracleComp spec α)
    (s : σ) (next : α × σ → Game) :
    (Game.advantage (((interpret first program).run s).bind next)
        (((interpret second program).run s).bind next) : ℝ) ≤
      (((interpret first program).run s).toOuterMeasure {x | bad x.2}).toReal := by
  rw [Game.coe_advantage]
  simpa only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal] using
    h.abs_sub_le program s next true

end Cslib.OracleComp.IdenticalUntilBad

namespace Cslib.Crypto.Game

open Probability
open scoped ENNReal NNReal

/-- Run a `WordOracleComp Unit α` against a stateless deterministic oracle
`o : List Bool → List Bool` and feed its output to `next : α → Game`. -/
noncomputable def runStatelessOracle {α : Type} (o : List Bool → List Bool)
    (prog : WordOracleComp Unit α) (next : α → Game) : Game :=
  (ProbComp.eval ((OracleComp.interpret
    (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
      (fun req (s : Unit) => pure (o req.2, s)))
    prog).run ())).bind (fun out => next out.1)

@[simp]
theorem runStatelessOracle_pure {α : Type} (o : List Bool → List Bool)
    (a : α) (next : α → Game) :
    runStatelessOracle o (pure a) next = next a := by
  simp [runStatelessOracle]

theorem runStatelessOracle_query_inl {α : Type} (o : List Bool → List Bool)
    (m : ℕ)
    (k : probOracleSpec (fun _ : Unit × List Bool => List Bool) (Sum.inl m) →
      OracleComp (probOracleSpec (fun _ : Unit × List Bool => List Bool)) α)
    (next : α → Game) :
    runStatelessOracle o (OracleComp.query (Sum.inl m) >>= k) next =
      (PMF.uniformOfFintype (Fin (m + 1))).bind
        (fun x => runStatelessOracle o (k x) next) := by
  simp [runStatelessOracle, ProbOracleComp.handler, StateT.run_bind,
    ProbComp.eval_bind, PMF.bind_bind]

theorem runStatelessOracle_query_inr {α : Type} (o : List Bool → List Bool)
    (req : Unit × List Bool)
    (k : probOracleSpec (fun _ : Unit × List Bool => List Bool) (Sum.inr req) →
      OracleComp (probOracleSpec (fun _ : Unit × List Bool => List Bool)) α)
    (next : α → Game) :
    runStatelessOracle o (OracleComp.query (Sum.inr req) >>= k) next =
      runStatelessOracle o (k (o req.2)) next := by
  rw [runStatelessOracle, OracleComp.interpret_bind, OracleComp.interpret_query,
    ProbOracleComp.handler, StateT.run_bind]
  rfl

/-- **Stateless oracle until-bad bound**: if `prog` makes at most `Q` oracle queries, `o₁ τ req`
agrees with `o₂ req` whenever `isBad τ req = false`, and for every `req` the `μ`-probability of
`isBad τ req = true` is at most `δ`, then replacing `o₁ τ` by `o₂` (with continuation `next τ`)
changes the probability of each outcome `b : Bool` by at most `Q * δ`. -/
theorem runStatelessOracle_bind_le {T α : Type} (μ : PMF T)
    (o₁ : T → List Bool → List Bool) (o₂ : List Bool → List Bool)
    (isBad : T → List Bool → Bool) (next : T → α → Game)
    {Q : ℕ} {δ : ℝ≥0∞}
    {prog : WordOracleComp Unit α} (hq : prog.IsQueryBounded Q)
    (hagree : ∀ τ req, isBad τ req = false → o₁ τ req = o₂ req)
    (hbad : ∀ req, (∑' τ, μ τ * if isBad τ req then (1 : ℝ≥0∞) else 0) ≤ δ)
    (b : Bool) :
    ((μ.bind fun τ => runStatelessOracle (o₁ τ) prog (next τ)) b ≤
      (μ.bind fun τ => runStatelessOracle o₂ prog (next τ)) b + (Q : ℝ≥0∞) * δ) ∧
    ((μ.bind fun τ => runStatelessOracle o₂ prog (next τ)) b ≤
      (μ.bind fun τ => runStatelessOracle (o₁ τ) prog (next τ)) b + (Q : ℝ≥0∞) * δ) := by
  induction hq with
  | pure a Q =>
    simp only [runStatelessOracle_pure]
    exact ⟨le_self_add, le_self_add⟩
  | liftBind q k Q _ ih =>
    rcases q with m | req
    · simp only [Sum.elim_inl, Nat.add_zero]
      have hinl (o : T → List Bool → List Bool) :
          (μ.bind fun τ =>
            runStatelessOracle (o τ) (OracleComp.query (Sum.inl m) >>= k) (next τ)) =
          (PMF.uniformOfFintype (Fin (m + 1))).bind
            (fun x => μ.bind fun τ => runStatelessOracle (o τ) (k x) (next τ)) := by
        rw [show (fun τ =>
            runStatelessOracle (o τ) (OracleComp.query (Sum.inl m) >>= k) (next τ)) = _ from
          funext fun τ => runStatelessOracle_query_inl (o τ) m k (next τ)]
        exact PMF.bind_comm μ (PMF.uniformOfFintype (Fin (m + 1))) _
      rw [hinl o₁, hinl (fun _ => o₂)]
      simp only [PMF.bind_apply]
      have hsum (f g : Fin (m + 1) → ℝ≥0∞) (hle : ∀ x, f x ≤ g x + (Q : ℝ≥0∞) * δ) :
          (∑' x, PMF.uniformOfFintype (Fin (m + 1)) x * f x) ≤
            (∑' x, PMF.uniformOfFintype (Fin (m + 1)) x * g x) + (Q : ℝ≥0∞) * δ := by
        calc ∑' x, PMF.uniformOfFintype (Fin (m + 1)) x * f x
            ≤ ∑' x, PMF.uniformOfFintype (Fin (m + 1)) x * (g x + (Q : ℝ≥0∞) * δ) :=
              tsum_le_tsum fun x => mul_le_mul_of_nonneg_left (hle x) zero_le
          _ = (∑' x, PMF.uniformOfFintype (Fin (m + 1)) x * g x) + (Q : ℝ≥0∞) * δ := by
              simp only [mul_add, tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
      exact ⟨hsum _ _ (fun x => (ih x).1), hsum _ _ (fun x => (ih x).2)⟩
    · simp only [Sum.elim_inr]
      have hinr₁ :
          (fun τ => runStatelessOracle (o₁ τ) (OracleComp.query (Sum.inr req) >>= k) (next τ)) =
            fun τ => runStatelessOracle (o₁ τ) (k (o₁ τ req.2)) (next τ) :=
        funext fun τ => runStatelessOracle_query_inr (o₁ τ) req k (next τ)
      have hinr₂ :
          (fun τ => runStatelessOracle o₂ (OracleComp.query (Sum.inr req) >>= k) (next τ)) =
            fun τ => runStatelessOracle o₂ (k (o₂ req.2)) (next τ) :=
        funext fun τ => runStatelessOracle_query_inr o₂ req k (next τ)
      rw [hinr₁, hinr₂]
      have hstep (f g : T → Game)
          (hfg : ∀ τ, isBad τ req.2 = false → f τ = g τ) :
          (μ.bind f) b ≤ (μ.bind g) b + δ := by
        simp only [PMF.bind_apply]
        calc ∑' τ, μ τ * f τ b
            ≤ ∑' τ, (μ τ * g τ b + μ τ * if isBad τ req.2 then 1 else 0) := by
              refine tsum_le_tsum fun τ => ?_
              by_cases hb : isBad τ req.2 = true
              · simp only [hb, ↓reduceIte, mul_one]
                exact le_add_of_le_right (mul_le_of_le_one_right zero_le (PMF.coe_le_one _ _))
              · simp only [Bool.not_eq_true] at hb
                rw [hfg τ hb]; simp [hb]
          _ = (∑' τ, μ τ * g τ b) + ∑' τ, μ τ * if isBad τ req.2 then 1 else 0 := tsum_add
          _ ≤ (∑' τ, μ τ * g τ b) + δ := add_le_add le_rfl (hbad req.2)
      have hstep1 := hstep
        (fun τ => runStatelessOracle (o₁ τ) (k (o₁ τ req.2)) (next τ))
        (fun τ => runStatelessOracle (o₁ τ) (k (o₂ req.2)) (next τ))
        (fun τ hb => by rw [hagree τ req.2 hb])
      have hstep2 := hstep
        (fun τ => runStatelessOracle (o₁ τ) (k (o₂ req.2)) (next τ))
        (fun τ => runStatelessOracle (o₁ τ) (k (o₁ τ req.2)) (next τ))
        (fun τ hb => by rw [hagree τ req.2 hb])
      have hcast : ((Q + 1 : ℕ) : ℝ≥0∞) * δ = (Q : ℝ≥0∞) * δ + δ := by
        rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      rw [hcast]
      exact ⟨(hstep1.trans (add_le_add (ih (o₂ req.2)).1 le_rfl)).trans_eq (add_assoc _ _ _),
        ((ih (o₂ req.2)).2.trans (add_le_add hstep2 le_rfl)).trans_eq (by ac_rfl)⟩

/-- `Game.advantage` corollary of `runStatelessOracle_bind_le` when `δ = (q : ℝ≥0∞)⁻¹`. -/
theorem advantage_runStatelessOracle_bind_le {T α : Type} (μ : PMF T)
    (o₁ : T → List Bool → List Bool) (o₂ : List Bool → List Bool)
    (isBad : T → List Bool → Bool) (next : T → α → Game)
    {Q q : ℕ} [NeZero q]
    {prog : WordOracleComp Unit α} (hq : prog.IsQueryBounded Q)
    (hagree : ∀ τ req, isBad τ req = false → o₁ τ req = o₂ req)
    (hbad : ∀ req, (∑' τ, μ τ * if isBad τ req then (1 : ℝ≥0∞) else 0) ≤ (q : ℝ≥0∞)⁻¹) :
    Game.advantage
      (μ.bind fun τ => runStatelessOracle (o₁ τ) prog (next τ))
      (μ.bind fun τ => runStatelessOracle o₂ prog (next τ)) ≤
      (Q : ℝ≥0) / (q : ℝ≥0) := by
  have h := runStatelessOracle_bind_le μ o₁ o₂ isBad next hq hagree hbad true
  have hne : (Q : ℝ≥0∞) * (q : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top Q)
      (ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr (NeZero.ne q)))
  have hadv := Game.advantage_le_of_apply_le hne h.1 h.2
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ← div_eq_mul_inv] at hadv
  exact NNReal.coe_le_coe.mp (by simpa only [NNReal.coe_div, NNReal.coe_natCast] using hadv)

/-- An independent outer `PMF.bind` commutes with `runStatelessOracle`. -/
theorem bind_runStatelessOracle_comm {α β : Type} (μ : PMF β)
    (o : List Bool → List Bool) (prog : WordOracleComp Unit α) (next : β → α → Game) :
    (μ.bind fun b => runStatelessOracle o prog (next b)) =
      runStatelessOracle o prog (fun a => μ.bind fun b => next b a) := by
  unfold runStatelessOracle; exact PMF.bind_comm μ _ _

/-- Support-restricted continuation bound for `runStatelessOracle`. -/
theorem advantage_runStatelessOracle_le_of_support {α : Type}
    (o : List Bool → List Bool) (prog : WordOracleComp Unit α)
    (next₁ next₂ : α → Game) {ε : ℝ≥0}
    (h : ∀ out ∈ (ProbComp.eval ((OracleComp.interpret
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
        (fun req (s : Unit) => pure (o req.2, s))) prog).run ())).support,
      Game.advantage (next₁ out.1) (next₂ out.1) ≤ ε) :
    Game.advantage (runStatelessOracle o prog next₁) (runStatelessOracle o prog next₂) ≤ ε :=
  advantage_bind_le_of_support _ _ _ h

/-- Two `ZMod q`-indexed game families that agree outside a single point `x₀` have `Game.advantage`
at most `1 / q` under `PMF.uniformOfFintype (ZMod q)`. -/
theorem advantage_uniform_bind_of_eq_of_ne {q : ℕ} [NeZero q] (x₀ : ZMod q)
    (g₁ g₂ : ZMod q → Game) (heq : ∀ x ≠ x₀, g₁ x = g₂ x) :
    Game.advantage
      ((PMF.uniformOfFintype (ZMod q)).bind g₁)
      ((PMF.uniformOfFintype (ZMod q)).bind g₂) ≤ 1 / (q : ℝ≥0) := by
  let err : ZMod q → Game := fun x => PMF.pure (decide (x = x₀))
  have hadv := advantage_bind_le_succProbability_bind (PMF.uniformOfFintype (ZMod q)) g₁ g₂ err
    fun x => by
      by_cases hx : x = x₀
      · rw [show err x true = 1 by simp [err, hx]]
        exact ⟨le_add_of_le_right (PMF.coe_le_one _ _),
          le_add_of_le_right (PMF.coe_le_one _ _)⟩
      · rw [heq x hx]; exact ⟨le_self_add, le_self_add⟩
  have hsucc :
      Game.succProbability ((PMF.uniformOfFintype (ZMod q)).bind err) = 1 / (q : ℝ≥0) := by
    have happly : (((PMF.uniformOfFintype (ZMod q)).bind err) true) = (q : ℝ≥0∞)⁻¹ := by
      simp only [err, PMF.bind_apply, PMF.pure_apply, true_eq_decide_iff, mul_ite, mul_one,
        mul_zero, tsum_ite_eq, PMF.uniformOfFintype_apply, ZMod.card]
    rw [Game.succProbability, happly, ENNReal.toNNReal_inv, ENNReal.toNNReal_natCast, one_div]
  exact hadv.trans_eq hsucc

/-- Stateful oracle handler that replies with `o₂ request.2` and updates its `Option (List Bool)`
state to `some (extract request.2)` whenever `isBad request.2` holds. -/
def finderPhase2Oracle (o₂ : List Bool → List Bool) (isBad : List Bool → Bool)
    (extract : List Bool → List Bool) (request : Unit × List Bool) :
    StateT (Option (List Bool)) ProbComp (List Bool) :=
  fun s => pure (o₂ request.2, if isBad request.2 then some (extract request.2) else s)

/-- Run `prog` against `finderPhase2Oracle` starting from `s : Option (List Bool)` and test whether
the final state satisfies `isGood`. -/
noncomputable def runFinderOracle {α : Type} (o₂ : List Bool → List Bool)
    (isBad : List Bool → Bool) (extract : List Bool → List Bool)
    (prog : WordOracleComp Unit α) (s : Option (List Bool))
    (isGood : List Bool → Bool) : Game :=
  (ProbComp.eval ((OracleComp.interpret
    (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
      (finderPhase2Oracle o₂ isBad extract))
    prog).run s)).bind (fun out => PMF.pure (out.2.elim false isGood))

@[simp]
theorem runFinderOracle_pure {α : Type} (o₂ : List Bool → List Bool)
    (isBad : List Bool → Bool) (extract : List Bool → List Bool)
    (a : α) (s : Option (List Bool)) (isGood : List Bool → Bool) :
    runFinderOracle o₂ isBad extract (pure a) s isGood = PMF.pure (s.elim false isGood) := by
  simp [runFinderOracle]

theorem runFinderOracle_query_inl {α : Type} (o₂ : List Bool → List Bool)
    (isBad : List Bool → Bool) (extract : List Bool → List Bool)
    (m : ℕ)
    (k : probOracleSpec (fun _ : Unit × List Bool => List Bool) (Sum.inl m) →
      OracleComp (probOracleSpec (fun _ : Unit × List Bool => List Bool)) α)
    (s : Option (List Bool)) (isGood : List Bool → Bool) :
    runFinderOracle o₂ isBad extract (OracleComp.query (Sum.inl m) >>= k) s isGood =
      (PMF.uniformOfFintype (Fin (m + 1))).bind
        (fun x => runFinderOracle o₂ isBad extract (k x) s isGood) := by
  simp [runFinderOracle, ProbOracleComp.handler, StateT.run_bind,
    ProbComp.eval_bind, PMF.bind_bind]

theorem runFinderOracle_query_inr {α : Type} (o₂ : List Bool → List Bool)
    (isBad : List Bool → Bool) (extract : List Bool → List Bool)
    (req : Unit × List Bool)
    (k : probOracleSpec (fun _ : Unit × List Bool => List Bool) (Sum.inr req) →
      OracleComp (probOracleSpec (fun _ : Unit × List Bool => List Bool)) α)
    (s : Option (List Bool)) (isGood : List Bool → Bool) :
    runFinderOracle o₂ isBad extract (OracleComp.query (Sum.inr req) >>= k) s isGood =
      runFinderOracle o₂ isBad extract (k (o₂ req.2))
        (if isBad req.2 then some (extract req.2) else s) isGood := by
  rw [runFinderOracle, OracleComp.interpret_bind, OracleComp.interpret_query,
    ProbOracleComp.handler, StateT.run_bind]
  rfl

/-- Once `s` satisfies `s.elim false isGood = true`, `runFinderOracle` succeeds with
probability `1`. -/
theorem runFinderOracle_true_of_good {α : Type} (o₂ : List Bool → List Bool)
    (isBad : List Bool → Bool) (extract : List Bool → List Bool)
    (isGood : List Bool → Bool)
    (hbad_good : ∀ req, isBad req = true → isGood (extract req) = true)
    (prog : WordOracleComp Unit α) :
    ∀ (s : Option (List Bool)), s.elim false isGood = true →
      runFinderOracle o₂ isBad extract prog s isGood true = 1 := by
  induction prog using OracleComp.induction with
  | pure a =>
    intro s hs
    simp [hs]
  | query_bind q k ih =>
    rcases q with m | req
    · intro s hs
      rw [runFinderOracle_query_inl, PMF.bind_apply]
      simp_rw [ih _ s hs, mul_one, PMF.tsum_coe]
    · intro s hs
      rw [runFinderOracle_query_inr]
      apply ih
      by_cases hb : isBad req.2 = true
      · simp [hb, hbad_good req.2 hb]
      · simp [hb, hs]

/-- **Finder-oracle until-bad bound**: if `o₁ req = o₂ req` whenever `isBad req = false` and every
query with `isBad req = true` satisfies `isGood (extract req) = true`, then the difference between
`runStatelessOracle o₁ prog next` and `runStatelessOracle o₂ prog next` is bounded by the
probability that `runFinderOracle o₂ isBad extract prog none isGood` outputs `true`. -/
theorem runStatelessOracle_le_runFinderOracle {α : Type}
    (o₁ o₂ : List Bool → List Bool) (isBad : List Bool → Bool)
    (extract : List Bool → List Bool) (isGood : List Bool → Bool)
    (hagree : ∀ req, isBad req = false → o₁ req = o₂ req)
    (hbad_good : ∀ req, isBad req = true → isGood (extract req) = true)
    (prog : WordOracleComp Unit α) (next : α → Game) (b : Bool) :
    (runStatelessOracle o₁ prog next b ≤
      runStatelessOracle o₂ prog next b +
        runFinderOracle o₂ isBad extract prog none isGood true) ∧
    (runStatelessOracle o₂ prog next b ≤
      runStatelessOracle o₁ prog next b +
        runFinderOracle o₂ isBad extract prog none isGood true) := by
  induction prog using OracleComp.induction with
  | pure a =>
    simp only [runStatelessOracle_pure, runFinderOracle_pure]
    exact ⟨le_self_add, le_self_add⟩
  | query_bind q k ih =>
    rcases q with m | req
    · rw [runStatelessOracle_query_inl, runStatelessOracle_query_inl, runFinderOracle_query_inl]
      simp only [PMF.bind_apply]
      constructor
      · calc ∑' x, PMF.uniformOfFintype (Fin (m + 1)) x * runStatelessOracle o₁ (k x) next b
            ≤ ∑' x, PMF.uniformOfFintype (Fin (m + 1)) x *
                (runStatelessOracle o₂ (k x) next b +
                  runFinderOracle o₂ isBad extract (k x) none isGood true) :=
              tsum_le_tsum fun x => mul_le_mul_of_nonneg_left (ih x).1 zero_le
          _ = (∑' x, PMF.uniformOfFintype (Fin (m + 1)) x * runStatelessOracle o₂ (k x) next b) +
                ∑' x, PMF.uniformOfFintype (Fin (m + 1)) x *
                  runFinderOracle o₂ isBad extract (k x) none isGood true := by
              simp only [mul_add, tsum_add]
      · calc ∑' x, PMF.uniformOfFintype (Fin (m + 1)) x * runStatelessOracle o₂ (k x) next b
            ≤ ∑' x, PMF.uniformOfFintype (Fin (m + 1)) x *
                (runStatelessOracle o₁ (k x) next b +
                  runFinderOracle o₂ isBad extract (k x) none isGood true) :=
              tsum_le_tsum fun x => mul_le_mul_of_nonneg_left (ih x).2 zero_le
          _ = (∑' x, PMF.uniformOfFintype (Fin (m + 1)) x * runStatelessOracle o₁ (k x) next b) +
                ∑' x, PMF.uniformOfFintype (Fin (m + 1)) x *
                  runFinderOracle o₂ isBad extract (k x) none isGood true := by
              simp only [mul_add, tsum_add]
    · rw [runStatelessOracle_query_inr, runStatelessOracle_query_inr, runFinderOracle_query_inr]
      by_cases hb : isBad req.2 = true
      · simp only [hb, ↓reduceIte]
        have h1 :
            runFinderOracle o₂ isBad extract (k (o₂ req.2)) (some (extract req.2)) isGood true =
              1 :=
          runFinderOracle_true_of_good o₂ isBad extract isGood hbad_good (k (o₂ req.2))
            (some (extract req.2)) (hbad_good req.2 hb)
        rw [h1]
        exact ⟨le_add_of_le_right (PMF.coe_le_one _ _),
          le_add_of_le_right (PMF.coe_le_one _ _)⟩
      · simp only [Bool.not_eq_true] at hb
        simp only [hb, Bool.false_eq_true, ↓reduceIte, hagree req.2 hb]
        exact ih (o₂ req.2)

end Cslib.Crypto.Game
