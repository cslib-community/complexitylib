/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Languages.Probabilistic.QueryCount.Sum
import CslibFrontier.Languages.Probabilistic.RandomOracle.Sum

/-! Two lazy random oracles memoized in two lists: eager tables, per-list invariants and costs. -/

namespace CslibFrontierTests.RandomOracleSum

open Cslib Cslib.Probability OracleComp

/-- The interface of a hash oracle on `Bool` and a challenge oracle on `Bool × Bool`. -/
private abbrev Spec := (fun _ : Bool => Bool) ⊕ₒ (fun _ : Bool × Bool => Bool)

private instance (q : Bool ⊕ (Bool × Bool)) : Fintype (Spec q) := by
  cases q <;> exact inferInstanceAs (Fintype Bool)

private instance (q : Bool ⊕ (Bool × Bool)) : Nonempty (Spec q) := by
  cases q <;> exact ⟨false⟩

/-- Hash, then derive a challenge from the hash value, then hash again. -/
private def mixed : OracleComp Spec (Bool × Bool × Bool) := do
  let root ← query (spec := Spec) (.inl false)
  let chal ← query (spec := Spec) (.inr (root, true))
  let again ← query (spec := Spec) (.inl false)
  return (root, chal, again)

/-- The hash queries of `mixed` alone, as a program over the hash interface. -/
private def hashes : OracleComp (fun _ : Bool => Bool) (Bool × Bool) := do
  let first ← query false
  let second ← query true
  return (first, second)

-- Two lists started empty implement two independent eagerly sampled tables.
example :
    ((interpret (RandomOracle.memoizeSum (fun _ => PMF.uniformOfFintype Bool)
      (fun _ => PMF.uniformOfFintype Bool)) mixed).run ([], [])).map Prod.fst =
      (do
        let table ← PMF.pi (fun q : Bool ⊕ (Bool × Bool) => PMF.uniformOfFintype (Spec q))
        interpret (fun q => PMF.pure (table q)) mixed) := by
  rw [RandomOracle.map_fst_run_interpret_memoizeSum_nil, RandomOracle.interpret_eq_lazy]
  congr 3
  funext q
  cases q <;> rfl

-- A challenge list filled from a constant oracle records only that value, while the hash list,
-- filled by a uniform oracle on the same run, is constrained by nothing.
example (st : List (Bool × Bool) × List ((Bool × Bool) × Bool)) (res : Bool × Bool × Bool)
    (hmem : (res, st) ∈ ((interpret (RandomOracle.memoizeSum
      (fun _ => PMF.uniformOfFintype Bool) (fun _ => PMF.pure true)) mixed).run ([], [])).support) :
    ∀ e ∈ st.2, e.2 = true :=
  (RandomOracle.mem_support_run_interpret_memoizeSum _ _ (fun _ => True)
    (fun tr => ∀ e ∈ tr, e.2 = true) (fun _ _ _ _ _ _ => trivial)
    (fun q tr tr' ans htr hstep => (RandomOracle.memoize_invariant _ (fun _ v => v = true) q tr
      htr (by simp) (ans, tr') hstep).2) mixed ⟨trivial, by simp⟩ hmem).2

-- A hash call leaves the challenge list unchanged.
example (tr₁ : List (Bool × Bool)) (tr₂ : List ((Bool × Bool) × Bool)) (ans : Bool)
    (st : List (Bool × Bool) × List ((Bool × Bool) × Bool))
    (h : (ans, st) ∈ (RandomOracle.memoizeSum (fun _ => PMF.uniformOfFintype Bool)
      (fun _ => PMF.uniformOfFintype Bool) (.inl false) (tr₁, tr₂)).support) :
    st.2 = tr₂ := by
  obtain ⟨_, -, rfl⟩ := RandomOracle.mem_support_memoizeSum_inl.mp h
  rfl

-- An embedded hash program costs nothing under a cost that counts only challenge queries, and
-- its two hash calls stay within budget under a cost that counts only hash queries.
example : IsCostBounded (fun q : Bool ⊕ (Bool × Bool) => q.elim (fun _ => 0) (fun _ => 1))
    (liftLeft (spec₂ := fun _ : Bool × Bool => Bool) hashes) 0 :=
  IsCostBounded.liftLeft_of_cost_inl_eq_zero (fun _ => rfl) hashes

example : IsCostBounded (fun q : Bool ⊕ (Bool × Bool) => q.elim (fun _ => 1) (fun _ => 0))
    (liftLeft (spec₂ := fun _ : Bool × Bool => Bool) hashes) 2 :=
  IsCostBounded.liftLeft (cost₁ := fun _ => 1)
    (((IsCostBounded.query false).bind fun first =>
      (IsCostBounded.query true).bind fun second =>
        IsCostBounded.pure (first, second) 0).mono (by norm_num)) fun _ => le_rfl

end CslibFrontierTests.RandomOracleSum
