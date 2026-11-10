/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.Resolution.TreeLike

/-!
# Prover–Delayer potentials for tree-like resolution

A *partial assignment* `ρ : V → Option Bool` falsifies a clause
(`Cslib.Logic.PL.Clause.FalsifiedBy`) if it sets every literal of the clause to false. Following a
tree-like derivation from its conclusion towards the leaves, a Prover keeps a partial assignment
falsifying the current clause: at a resolution step on `v`, if `v` is unset, either value of `v`
falsifies one of the two premises (`Cslib.Logic.PL.Clause.FalsifiedBy.resolvent_update`). So a
*potential* `μ : (V → Option Bool) → ℕ` that splits at every unset variable,
`μ ρ ≤ μ ρ[v ↦ 0] + μ ρ[v ↦ 1]`, and is at most `1` on partial assignments falsifying a clause of
`φ`, bounds the size of every tree-like derivation of a clause `ρ` falsifies from below
(`Cslib.Logic.PL.CNF.Derivation.potential_le_size`). In particular `μ (fun _ => none)` is at most
the size of every tree-like refutation (`Cslib.Logic.PL.CNF.Derivation.potential_none_le_size`).

This is the potential form of the asymmetric Prover–Delayer game of Beyersdorff, Galesi and Lauria
[BeyersdorffGalesiLauria2010, Theorem 1]: if Delayer can secure `p` points in the `(c₀, c₁)`-game,
with `1 / c₀ + 1 / c₁ = 1`, then every tree-like refutation has at least `2 ^ p` nodes. A Delayer
strategy guaranteeing `p` points gives a real-valued splitting potential with value `2 ^ p` at the
empty assignment, and its ceiling, of value `⌈2 ^ p⌉`, is a potential in the sense used here; the
proof of their theorem is the induction above. Splitting with `μ ρ ≤ μ ρ[v ↦ b]` at a variable whose
value Delayer chooses as `b` is a special case of the split inequality.

## Main definitions

* `Cslib.Logic.PL.Clause.FalsifiedBy`: a partial assignment sets every literal of a clause to false.

## Main results

* `Cslib.Logic.PL.CNF.Derivation.potential_le_size`,
  `Cslib.Logic.PL.CNF.Derivation.potential_none_le_size`: splitting potentials bound the size of
  tree-like derivations and refutations from below.

## References

* [O. Beyersdorff, N. Galesi, M. Lauria, *A lower bound for the pigeonhole principle in tree-like
  Resolution by asymmetric Prover–Delayer games*][BeyersdorffGalesiLauria2010]
-/

public section

namespace Cslib.Logic.PL

variable {V : Type*} [DecidableEq V]

/-- The partial assignment `ρ` **falsifies** the clause `c`: it sets every literal of `c` to false,
that is, it gives the variable of each literal the opposite of the literal's sign. Partial
assignments are encoded as in `Cslib.Logic.PL.CNF.restrictBy`, with `none` for unset variables. -/
@[expose] def Clause.FalsifiedBy (ρ : V → Option Bool) (c : Clause V) : Prop :=
  ∀ l ∈ c, ρ l.1 = some (!l.2)

namespace Clause

variable {ρ : V → Option Bool}

omit [DecidableEq V] in
/-- Every partial assignment falsifies the empty clause. -/
@[simp] theorem falsifiedBy_nil (ρ : V → Option Bool) : FalsifiedBy ρ ([] : Clause V) :=
  fun _ h => absurd h List.not_mem_nil

/-- If `ρ` falsifies the resolvent of `c₁` and `c₂` on `v` and sets `v` to `false`, it falsifies
`c₁`. -/
theorem FalsifiedBy.left_of_resolvent {c₁ c₂ : Clause V} {v : V}
    (h : FalsifiedBy ρ (c₁.resolvent c₂ v)) (hv : ρ v = some false) : FalsifiedBy ρ c₁ := by
  intro l hl
  by_cases hlv : l = (v, true)
  · subst hlv
    exact hv
  · exact h l (mem_resolvent.2 (Or.inl ⟨hl, hlv⟩))

/-- If `ρ` falsifies the resolvent of `c₁` and `c₂` on `v` and sets `v` to `true`, it falsifies
`c₂`. -/
theorem FalsifiedBy.right_of_resolvent {c₁ c₂ : Clause V} {v : V}
    (h : FalsifiedBy ρ (c₁.resolvent c₂ v)) (hv : ρ v = some true) : FalsifiedBy ρ c₂ := by
  intro l hl
  by_cases hlv : l = (v, false)
  · subst hlv
    exact hv
  · exact h l (mem_resolvent.2 (Or.inr ⟨hl, hlv⟩))

/-- Setting a variable that `ρ` leaves unset keeps every clause `ρ` falsifies falsified. -/
theorem FalsifiedBy.update {c : Clause V} (h : FalsifiedBy ρ c) {v : V} (hv : ρ v = none)
    (b : Bool) : FalsifiedBy (Function.update ρ v (some b)) c := by
  intro l hl
  have hne : l.1 ≠ v := by
    intro he
    have := h l hl
    rw [he, hv] at this
    cases this
  rw [Function.update_of_ne hne]
  exact h l hl

/-- **The Prover's step.** If `ρ` falsifies the resolvent of `c₁` and `c₂` on an unset variable
`v`, setting `v` to `false` falsifies `c₁` and setting it to `true` falsifies `c₂`. -/
theorem FalsifiedBy.resolvent_update {c₁ c₂ : Clause V} {v : V}
    (h : FalsifiedBy ρ (c₁.resolvent c₂ v)) (hv : ρ v = none) :
    FalsifiedBy (Function.update ρ v (some false)) c₁ ∧
      FalsifiedBy (Function.update ρ v (some true)) c₂ :=
  ⟨(h.update hv false).left_of_resolvent (Function.update_self ..),
    (h.update hv true).right_of_resolvent (Function.update_self ..)⟩

end Clause

namespace CNF.Derivation

variable {φ : CNF V}

/-- **Prover–Delayer potentials bound tree-like derivations** [BeyersdorffGalesiLauria2010,
Theorem 1]. Let `μ` split at every unset variable, `μ ρ ≤ μ ρ[v ↦ 0] + μ ρ[v ↦ 1]`, and be at most
`1` on partial assignments falsifying a clause of `φ`. Then every tree-like derivation of a clause
that `ρ` falsifies has at least `μ ρ` nodes. -/
theorem potential_le_size (μ : (V → Option Bool) → ℕ)
    (hsplit : ∀ ρ v, ρ v = none →
      μ ρ ≤ μ (Function.update ρ v (some false)) + μ (Function.update ρ v (some true)))
    (hax : ∀ ρ, ∀ c ∈ φ, Clause.FalsifiedBy ρ c → μ ρ ≤ 1) :
    {c : Clause V} → (d : φ.Derivation c) → {ρ : V → Option Bool} → Clause.FalsifiedBy ρ c →
      μ ρ ≤ d.size
  | _, mem hc, _, hρ => (hax _ _ hc hρ).trans_eq (size_mem hc).symm
  | _, resolvent v d₁ d₂ _ _, ρ, hρ => by
    rw [size_resolvent]
    match hv : ρ v with
    | none =>
      obtain ⟨h₁, h₂⟩ := hρ.resolvent_update hv
      have := hsplit ρ v hv
      have := potential_le_size μ hsplit hax d₁ h₁
      have := potential_le_size μ hsplit hax d₂ h₂
      omega
    | some false =>
      have := potential_le_size μ hsplit hax d₁ (hρ.left_of_resolvent hv)
      omega
    | some true =>
      have := potential_le_size μ hsplit hax d₂ (hρ.right_of_resolvent hv)
      omega

/-- **Prover–Delayer potentials bound tree-like refutations**: under the hypotheses of
`potential_le_size`, every tree-like refutation of `φ` has at least `μ (fun _ => none)` nodes. -/
theorem potential_none_le_size (μ : (V → Option Bool) → ℕ)
    (hsplit : ∀ ρ v, ρ v = none →
      μ ρ ≤ μ (Function.update ρ v (some false)) + μ (Function.update ρ v (some true)))
    (hax : ∀ ρ, ∀ c ∈ φ, Clause.FalsifiedBy ρ c → μ ρ ≤ 1) (d : φ.Derivation []) :
    μ (fun _ => none) ≤ d.size :=
  potential_le_size μ hsplit hax d (Clause.falsifiedBy_nil _)

end CNF.Derivation

end Cslib.Logic.PL
