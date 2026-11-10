/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import CslibFrontier.Tactic.SuppCases

/-! # Inverting support memberships with `supp_cases` and `supp_norm` -/

namespace CslibFrontierTests.SuppCases

open Cslib

/-! ### `PMF` -/

-- A bind followed by a map: one witness per bind, and the map's equation is substituted.
example (μ : PMF ℕ) (ν : ℕ → PMF ℕ) (f : ℕ → ℕ) (hf : ∀ n, 0 < f n) (x : ℕ)
    (h : x ∈ (μ.bind fun a => (ν a).map f).support) : 0 < x := by
  supp_cases h
  exact hf _

-- The same with monad notation, naming the parts with an `rcases` pattern.
example (μ : PMF ℕ) (ν : ℕ → PMF ℕ) (x : ℕ) (hμ : ∀ a ∈ μ.support, a ≤ 3)
    (hν : ∀ a, ∀ b ∈ (ν a).support, b ≤ a)
    (h : x ∈ (do let a ← μ; let b ← ν a; pure (a + b) : PMF ℕ).support) : x ≤ 6 := by
  supp_cases h with ⟨a, ha, b, hb, rfl⟩
  have := hμ a ha
  have := hν a b hb
  omega

-- A returned pair is split into its components, which are substituted.
example (μ : PMF ℕ) (y : ℕ) (n : ℕ) (h : (y, n) ∈ (μ.map fun a => (a, 1)).support) :
    n = 1 ∧ y ∈ μ.support := by
  supp_cases h
  exact ⟨rfl, ‹_›⟩

-- A uniform draw contributes no membership hypothesis.
example (x : Bool × Bool)
    (h : x ∈ (do
      let b ← Probability.PMF.uniformOfFintype Bool
      pure (b, !b) : PMF (Bool × Bool)).support) : x.1 ≠ x.2 := by
  supp_cases h with ⟨b, rfl⟩
  cases b <;> decide

-- A conditional splits into one goal per branch; a decided condition selects its branch.
example (c : Prop) [Decidable c] (μ ν : PMF ℕ) (x : ℕ) (hμ : ∀ a ∈ μ.support, a < 5)
    (hν : ∀ a ∈ ν.support, a < 3) (h : x ∈ (if c then μ else ν).support) : x < 5 := by
  supp_cases h with ⟨-, hx⟩ | ⟨-, hx⟩
  · exact hμ x hx
  · exact (hν x hx).trans (by decide)

example (c : Prop) [Decidable c] (hc : c) (μ ν : PMF ℕ) (x : ℕ)
    (h : x ∈ (if c then μ else ν).support) : x ∈ μ.support := by
  supp_cases h [hc]
  assumption

-- An impossible returned value closes the goal.
example (μ : PMF ℕ) (h : (0, 2) ∈ (μ.map fun a => (a, 1)).support) : False := by
  supp_cases h

-- An equation between applications of one constructor is inverted, and the goal is kept.
example (μ : PMF ℕ) (y : ℕ) (h : some y ∈ (μ.map some).support) : y ∈ μ.support := by
  supp_cases h
  assumption

example (μ : PMF ℕ) (y : ℕ) (h : Sum.inl y ∈ (μ.map (Sum.inl (β := Bool))).support) :
    y ∈ μ.support := by
  supp_cases h
  assumption

example (y : ℕ) (h : some y ∈ (PMF.pure (some 5)).support) : y = 5 := by
  supp_cases h
  rfl

-- A value returned in the middle of a sequence is substituted into the rest.
example (μ : PMF ℕ) (ν : ℕ → PMF ℕ) (x : ℕ) (hν : ∀ n, ∀ b ∈ (ν n).support, b ≤ n)
    (h : x ∈ (do let a ← μ; let b ← pure (a + 1); ν (2 * b) : PMF ℕ).support) :
    ∃ a ∈ μ.support, x ≤ 2 * (a + 1) := by
  supp_cases h with ⟨a, ha, hx⟩
  exact ⟨a, ha, hν _ x hx⟩

-- A membership the set cannot rewrite further is kept, under its own name.
example (μ : PMF ℕ) (ν : ℕ → PMF ℕ) (x : ℕ) (h : x ∈ (μ.bind ν).support) :
    ∃ a ∈ μ.support, x ∈ (ν a).support := by
  supp_cases h
  exact ⟨_, ‹_›, ‹_›⟩

/-! ### `OracleComp` and `ProbComp` -/

-- Possible results of a program with a uniform draw: the draw needs no hypothesis.
example (n x : ℕ)
    (h : x ∈ (do let k ← ProbComp.unifFin n; pure (k.val + 1) : ProbComp ℕ).support) :
    1 ≤ x := by
  supp_cases h
  omega

-- Sequencing two programs, as in the structured word-RAM semantics.
example (m₁ : ProbComp (ℕ × ℕ)) (m₂ : ℕ → ProbComp (ℕ × ℕ)) (z : ℕ × ℕ)
    (h₁ : ∀ z ∈ m₁.support, 1 ≤ z.2)
    (h : z ∈ (do
      let z₁ ← m₁
      let z₂ ← m₂ z₁.1
      pure (z₂.1, z₁.2 + z₂.2) : ProbComp (ℕ × ℕ)).support) : 1 ≤ z.2 := by
  supp_cases h with ⟨z₁, hz₁, z₂, -, rfl⟩
  have := h₁ z₁ hz₁
  simp only
  omega

-- A map over a query answered from a restricted set keeps that set's membership.
example {ι : Type} {spec : OracleSpec ι} (possible : (q : ι) → Set (spec q)) (q : ι)
    (f : spec q → ℕ) (x : ℕ)
    (h : x ∈ OracleComp.supportWith possible (f <$> OracleComp.query q)) :
    ∃ a ∈ possible q, f a = x := by
  supp_cases h with ⟨a, ha, rfl⟩
  exact ⟨a, ha, rfl⟩

-- The law of a closed program is inverted through its `PMF` normal form.
example (p : ProbComp ℕ) (x : ℕ) (hp : ∀ a ∈ (ProbComp.eval p).support, a < 4)
    (h : x ∈ (ProbComp.eval (do let a ← p; pure (2 * a))).support) : x < 8 := by
  supp_cases h with ⟨a, ha, rfl⟩
  have := hp a ha
  omega

-- A named program is unfolded by passing its definition.
-- A decided condition selects its branch even under `ProbComp.eval`, which does not split `if`.
example (p : ProbComp ℕ) (n x : ℕ) (hn : n = 3) (hp : ∀ a ∈ (ProbComp.eval p).support, a < 4)
    (h : x ∈ (ProbComp.eval (if n = 3 then (2 * ·) <$> p else pure 0)).support) : x < 8 := by
  supp_cases h [hn] with ⟨a, ha, rfl⟩
  have := hp a ha
  omega

private def double (p : ProbComp ℕ) : ProbComp ℕ := (2 * ·) <$> p

example (p : ProbComp ℕ) (x : ℕ) (h : x ∈ (double p).support) : Even x := by
  supp_cases h [double]
  exact even_two_mul _

-- A distribution bound by a local `let` is unfolded the same way.
example (μ : PMF ℕ) (x : ℕ) : x ∈ (μ.map (2 * ·)).support → Even x := by
  let ν := μ.map (2 * ·)
  intro (h : x ∈ ν.support)
  supp_cases h [ν]
  exact even_two_mul _

/-! ### `supp_norm` on its own -/

example (μ : PMF ℕ) (ν : ℕ → PMF ℕ) (x : ℕ) :
    x ∈ (do let a ← μ; let b ← ν a; pure (a + b) : PMF ℕ).support ↔
      ∃ a ∈ μ.support, ∃ b ∈ (ν a).support, x = a + b := by
  simp only [supp_norm]

/-! ### Failures -/

/--
error: supp_cases: `h` does not state a membership in the support of a distribution or program:
  x < 3
-/
#guard_msgs in
example (x : ℕ) (h : x < 3) : x < 4 := by
  supp_cases h

/--
error: supp_cases: unknown hypothesis `nope`
-/
#guard_msgs in
example (μ : PMF ℕ) (x : ℕ) (h : x ∈ μ.support) : True := by
  supp_cases nope

-- The program is a definition that the simp set cannot see through.
/--
error: supp_cases: the simp set `supp_norm` does not apply to `h`. If the distribution is a definition or a local `let`, unfold it with `supp_cases h [foo]`.
  x ∈ OracleComp.support (double p)
`simp` made no progress
-/
#guard_msgs in
example (p : ProbComp ℕ) (x : ℕ) (h : x ∈ (double p).support) : Even x := by
  supp_cases h

end CslibFrontierTests.SuppCases
