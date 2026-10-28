/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Oracle.QueryCount
public import Complexity.Probability.Product
import Complexity.Probability.PMF.Bind

/-!
# Fixing private coins of randomized oracle programs

When every external query `q : Query` has a finite reply type `spec q`, a randomized oracle program
`prog : ProbOracleComp spec α` has a finite tree of private coin choices `Coins prog` distributed
according to `coinLaw prog : PMF (Coins prog)`. Fixing `ω : Coins prog` yields a deterministic
oracle program `fixCoins prog ω : OracleComp spec α` with no private sampling calls:

* `fixCoins` preserves every external query-cost budget `OracleComp.IsCostBounded` (and in
  particular `IsQueryBounded` and `QueriesSatisfy`);
* against any deterministic external oracle `table : (q : Query) → spec q`, sampling
  `ω ← coinLaw prog` and interpreting `fixCoins prog ω` reproduces the exact output distribution of
  `prog` (`bind_interpret_fixCoins`);
* consequently, any experiment that samples a deterministic oracle table `t ← μ` independently of
  `prog`'s private coins equals the `coinLaw prog`-mixture of the corresponding deterministic-client
  experiments (`table_bind_interpret_eq_coinLaw_bind`), allowing information-theoretic bounds proved
  for deterministic `OracleComp` adversaries to transfer directly to `ProbOracleComp`.

## Main definitions

* `Cslib.ProbOracleComp.Coins`: finite type of private coin trees for `ProbOracleComp spec α`.
* `Cslib.ProbOracleComp.coinLaw`: distribution over `Coins prog`.
* `Cslib.ProbOracleComp.fixCoins`: deterministic `OracleComp spec α` obtained by fixing
  `ω : Coins prog`.

## Main results

* `Cslib.ProbOracleComp.isCostBounded_fixCoins`,
  `Cslib.ProbOracleComp.isQueryBounded_fixCoins`: fixing private coins preserves query budgets.
* `Cslib.ProbOracleComp.bind_interpret_fixCoins`: averaging `fixCoins prog ω` over `coinLaw prog`
  against any deterministic external table equals interpreting `prog` with private coins.
* `Cslib.ProbOracleComp.table_bind_interpret_eq_coinLaw_bind`: commuting an independent table
  distribution `μ` past `coinLaw prog`.
-/

public section

namespace Cslib.ProbOracleComp

open Probability

variable {Query α : Type} {spec : Query → Type}

/-- Private coin space of a randomized oracle program: each private sample `Fin (k + 1)` pairs the
drawn value with the continuation's coins, and each external query `q` branches over every possible
reply in `spec q`. -/
@[expose] def Coins : ProbOracleComp spec α → Type
  | .pure _ => PUnit
  | .liftBind q cont =>
    match q with
    | .inl k => (c : Fin (k + 1)) × Coins (cont c)
    | .inr q => ∀ y : spec q, Coins (cont y)

/-- When every external reply type `spec q` is finite, `Coins prog` is finite. -/
instance finite_coins [∀ q, Finite (spec q)] (prog : ProbOracleComp spec α) :
    Finite (Coins prog) := by
  induction prog with
  | pure _ => exact inferInstanceAs (Finite PUnit)
  | liftBind q cont ih =>
    cases q with
    | inl _ =>
      have := ih
      exact inferInstanceAs (Finite ((c : _) × Coins (cont c)))
    | inr q =>
      have := ih
      exact inferInstanceAs (Finite (∀ y : spec q, Coins (cont y)))

/-- Product distribution over the private coin choices of `prog`. -/
noncomputable def coinLaw [∀ q, Fintype (spec q)] :
    (prog : ProbOracleComp spec α) → PMF (Coins prog)
  | .pure _ => PMF.pure PUnit.unit
  | .liftBind q cont =>
    match q with
    | .inl k =>
      (ProbComp.unifOracle k).bind fun c =>
        (coinLaw (cont c)).map fun ω => (⟨c, ω⟩ : (c : Fin (k + 1)) × Coins (cont c))
    | .inr _ =>
      Probability.PMF.pi fun y => coinLaw (cont y)

/-- Deterministic oracle program obtained by supplying `ω : Coins prog` for all private samples. -/
@[expose] def fixCoins : (prog : ProbOracleComp spec α) → Coins prog → OracleComp spec α
  | .pure a, _ => .pure a
  | .liftBind q cont, ω =>
    match q, cont, ω with
    | .inl _, cont, ⟨c, ω'⟩ => fixCoins (cont c) ω'
    | .inr q, cont, f => .liftBind q fun y => fixCoins (cont y) (f y)

/-- Fixing private coins preserves any external query cost budget `OracleComp.IsCostBounded`. -/
theorem isCostBounded_fixCoins {cost : Query → ℕ} {prog : ProbOracleComp spec α} {n : ℕ}
    (h : OracleComp.IsCostBounded (Sum.elim (fun _ => 0) cost) prog n) (ω : Coins prog) :
    OracleComp.IsCostBounded cost (fixCoins prog ω) n := by
  induction prog generalizing n with
  | pure a => exact .pure a n
  | liftBind q cont ih =>
    rw [OracleComp.IsCostBounded.liftBind_iff] at h
    cases q with
    | inl _ =>
      rcases ω with ⟨c, ω'⟩
      simpa only [Sum.elim_inl, Nat.sub_zero, fixCoins] using ih c (h.2 c) ω'
    | inr q =>
      dsimp only [fixCoins]
      rw [OracleComp.IsCostBounded.liftBind_iff]
      exact ⟨h.1, fun y => ih y (h.2 y) (ω y)⟩

/-- Fixing private coins preserves `IsQueryBounded`. -/
theorem isQueryBounded_fixCoins {prog : ProbOracleComp spec α} {n : ℕ}
    (h : prog.IsQueryBounded n) (ω : Coins prog) :
    (fixCoins prog ω).IsQueryBounded n :=
  isCostBounded_fixCoins h ω

/-- Against any deterministic external oracle `table`, sampling `ω ← coinLaw prog` and running
`fixCoins prog ω` has the exact output law of `prog`. -/
theorem bind_interpret_fixCoins [∀ q, Fintype (spec q)] (prog : ProbOracleComp spec α)
    (table : (q : Query) → spec q) :
    (coinLaw prog).bind (fun ω =>
      OracleComp.interpret (fun q => PMF.pure (table q)) (fixCoins prog ω)) =
    OracleComp.interpret
      (handler ProbComp.unifOracle (fun q => PMF.pure (table q))) prog := by
  induction prog with
  | pure a =>
    dsimp only [coinLaw, fixCoins]
    simp [OracleComp.interpret_pure, Probability.PMF.monad_pure_eq_pure]
  | liftBind q cont ih =>
    have hbind (r : ℕ ⊕ Query) (k : probOracleSpec spec r → ProbOracleComp spec α) :
        PFunctor.FreeM.liftBind r k = (OracleComp.query r >>= k) := rfl
    cases q with
    | inl k =>
      dsimp only [Coins, coinLaw, fixCoins]
      rw [hbind (.inl k) cont, OracleComp.interpret_bind, OracleComp.interpret_query]
      simp only [handler, PMF.bind_bind, PMF.bind_map, Function.comp_def,
        Probability.PMF.monad_bind_eq_bind]
      congr 1; funext c
      exact ih c
    | inr q =>
      dsimp only [Coins, coinLaw, fixCoins]
      rw [hbind (.inr q) cont, OracleComp.interpret_bind, OracleComp.interpret_query]
      simp only [handler, Probability.PMF.monad_bind_eq_bind, PMF.pure_bind]
      have hstep (f : ∀ y : spec q, Coins (cont y)) :
          OracleComp.interpret (fun r => PMF.pure (table r))
            (PFunctor.FreeM.liftBind q fun y => fixCoins (cont y) (f y)) =
          OracleComp.interpret (fun r => PMF.pure (table r))
            (fixCoins (cont (table q)) (f (table q))) := by
        change OracleComp.interpret (fun r => PMF.pure (table r))
          (OracleComp.query q >>= fun y => fixCoins (cont y) (f y)) = _
        simp [Probability.PMF.monad_bind_eq_bind]
      simp_rw [hstep]
      have heval := Probability.PMF.pi_map_eval (fun y => coinLaw (cont y)) (table q)
      rw [← ih (table q), ← heval, PMF.bind_map]
      rfl

/-- Sampling an external deterministic oracle table `t ← μ` independently of `prog`'s private coins
commutes with fixing `ω ← coinLaw prog`. -/
theorem table_bind_interpret_eq_coinLaw_bind [∀ q, Fintype (spec q)] {τ : Type*} (μ : PMF τ)
    (table : τ → (q : Query) → spec q) (prog : ProbOracleComp spec α) :
    μ.bind (fun t =>
      OracleComp.interpret
        (handler ProbComp.unifOracle (fun q => PMF.pure (table t q))) prog) =
    (coinLaw prog).bind (fun ω =>
      μ.bind (fun t =>
        OracleComp.interpret (fun q => PMF.pure (table t q)) (fixCoins prog ω))) := by
  simp_rw [← fun t => bind_interpret_fixCoins prog (table t)]
  exact PMF.bind_comm μ (coinLaw prog) _

end Cslib.ProbOracleComp
