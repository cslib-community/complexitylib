/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Game
public import Complexity.Foundations.Data.BitString.Basic
public import Complexity.Languages.Probabilistic.QueryCount
public import Complexity.Probability.HashFamily
public import Complexity.Probability.HashFamily.Uniform
public import Mathlib.Data.Fintype.Perm
import Complexity.Languages.Probabilistic.RandomOracle
import Complexity.Languages.Probabilistic.RandomPermutation
import Complexity.Languages.Probabilistic.Simulation
import Complexity.Languages.Probabilistic.UntilBad
import Complexity.Probability.BitString
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF.Uniform
import Complexity.Probability.Uniform
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Feistel networks and the Luby–Rackoff theorem

A Feistel round ([BonehShoup2023], Section 4.5; [LubyRackoff1988]) turns an arbitrary function
`f : G → G` on an additive group `G` into a bijection `feistelRoundEquiv f : G × G ≃ G × G` mapping
`(L, R)` to `(R, L + f R)` with explicit inverse `(L', R') ↦ (R' - f L', L')` requiring no
invertibility of `f`. Composing a list of round functions yields the multi-round Feistel cipher
`feistelNetwork`, specialized to the three-round (`feistel3`) and four-round (`feistel4`) networks.
Over any group of exponent two (`∀ x : G, -x = x`, including `BitString n`), swapping the two
halves (`Equiv.prodComm G G`) conjugates `feistelNetwork fs.reverse` to the inverse cipher
`(feistelNetwork fs).symm`.

We prove the **Luby–Rackoff theorem** ([BonehShoup2023], Section 4.5, Theorem 4.9;
[LubyRackoff1988]):

1. **Information-theoretic core with Δ-universal Round 1**: when the first round function is drawn
   from an `ε`-almost-Δ-universal family (`IsDeltaUniversalHash seed₁ h₁ ε`) and the second and
   third round functions are independent uniform random functions on `G`, any adaptive adversary
   `program : OracleComp (fun _ : G × G => G × G) Bool` making at most `Q` queries
   (`IsQueryBounded program Q`) distinguishes the three-round Feistel network from a uniform random
   function on `G × G` with advantage at most
   $$\binom{Q}{2} \cdot \varepsilon + \binom{Q}{2} \cdot \frac{1}{|G|}$$
   (`advantage_feistel3HashIdealGame_randomFunctionGame_le`).
2. **Classical three-round information-theoretic bound**: a uniform random function on `G` is
   `|G|⁻¹`-Δ-universal (`isDeltaUniversalHash_uniformOfFintype`), so three independent uniform
   random round functions have distinguishing advantage against a uniform random function on
   `G × G` at most
   $$\frac{2 \binom{Q}{2}}{|G|} = \frac{Q (Q - 1)}{|G|}$$
   (`advantage_feistel3RandomRoundsGame_randomFunctionGame_le`).
3. **Computational PRF-to-Feistel hybrid reductions (3-round and 4-round) and PRP switching**:
   replacing keyed round functions `F kᵢ` with independent uniform random round functions adds at
   most the sum of the single-round PRF advantages
   (`advantage_feistel3KeyedGame_feistel3RandomRoundsGame_le`,
   `advantage_feistel3KeyedGame_randomFunctionGame_le`, and the four-round bidirectional
   chosen-ciphertext hybrid bound
   `advantage_feistel4StrongKeyedGame_feistel4StrongRandomRoundsGame_le`). Combining with the
   PRP/PRF switching bound on `G × G` (`advantage_idealPermGame_randomFunctionGame_le`) yields the
   pseudorandom-permutation bounds against `idealPermGame`
   (`advantage_feistel3HashIdealGame_idealPermGame_le`,
   `advantage_feistel3RandomRoundsGame_idealPermGame_le`,
   `advantage_feistel3KeyedGame_idealPermGame_le`).
4. **Three-round chosen-ciphertext separation ([BonehShoup2023], Section 4.1.3 and
   Exercise 4.15(b))**: with two forward
   encryption queries and one inverse decryption query, the explicit distinguisher
   `feistel3CCAAttack` accepts any three-round Feistel network with probability `1`
   (`eval_feistel3_feistel3CCAAttack`). When `l₀ = l₁`, the third query asks to invert the first
   ciphertext, so every bidirectional permutation (`feistelStrongOracle π`) and `idealStrongGame`
   also accept with probability `1` (`eval_feistelStrongOracle_feistel3CCAAttack_self`,
   `idealStrongGame_feistel3CCAAttack_self`, `advantage_feistel3CCAAttack_self`). Whenever
   `l₀ ≠ l₁`, coupling `idealStrongGame` with the forgetful bidirectional lazy sampler shows that
   `idealStrongGame` accepts `feistel3CCAAttack l₀ l₁ r₀` with probability at most
   `|G|⁻¹ + 4 * |G × G|⁻¹` (`idealStrongGame_feistel3CCAAttack_true_le`), giving the quantitative
   nonnegligible chosen-ciphertext advantage lower bound
   `1 - |G|⁻¹ - 4 * |G|⁻¹ ^ 2` against `idealStrongGame`
   (`le_advantage_feistel3CCAAttack_idealStrongGame_of_ne`). In addition, when `G` has three
   distinct elements `l₀, l₁, l₂` (`|G| ≥ 3`), the transposition
   `Equiv.swap (l₀, (l₁ - l₀) + r₀) (l₂, r₀)` is rejected deterministically
   (`eval_feistelStrongOracle_swap_feistel3CCAAttack_eq_false`,
   `le_advantage_feistel3CCAAttack_idealStrongGame`,
   `advantage_feistel3CCAAttack_idealStrongGame_pos`), and against the independent-table
   bidirectional benchmark `independentTableStrongGame`, `feistel3CCAAttack l₀ l₁ r₀` accepts with
   probability `|G|⁻¹` and has exact advantage `1 - |G|⁻¹`
   (`eval_independentTableStrongGame_feistel3CCAAttack`,
   `advantage_feistel3CCAAttack_independentTable`).
5. **Four-round strong PRP Luby–Rackoff theorem ([LubyRackoff1988]; see [BonehShoup2023],
   Section 4.1.3 for strongly secure block ciphers)**: when all four round functions
   `f₁, f₂, f₃, f₄ : G → G` are independent uniform random functions, coupling the inner rounds
   `f₂, f₃` to the forgetful bidirectional lazy sampler on `G × G` and bounding outer-round
   collisions for `f₁` (Round 1) and `-f₄` (Round 4 on the swapped cache) shows that any `Q`-query
   adaptive chosen-ciphertext distinguisher has advantage against `idealStrongGame` at most
   $$2 \binom{Q}{2} \cdot \frac{1}{|G|} + 2 \binom{Q}{2} \cdot \frac{1}{|G|^2}$$
   (with the concrete constant coming from this proof;
   `feistel4StrongRandomRoundsGame_apply_le`,
   `idealStrongGame_apply_le_feistel4StrongRandomRoundsGame`,
   `advantage_feistel4StrongRandomRoundsGame_idealStrongGame_le`,
   `advantage_feistel4StrongRandomRoundsGame_bitString_le`). Combined with the four-round PRF
   hybrid reduction, this gives the full four-round strong PRP theorem
   `advantage_feistel4StrongKeyedGame_idealStrongGame_le`.

## Main definitions

* `Cslib.Crypto.LubyRackoff.feistelRound`, `feistelInvRound`, `feistelRoundEquiv`: single Feistel
  round and its bundled equivalence over `[AddGroup G]`.
* `Cslib.Crypto.LubyRackoff.feistelNetwork`, `feistel3`, `feistel4`: multi-round, 3-round, and
  4-round Feistel permutations.
* `Cslib.Crypto.LubyRackoff.feistel3FixedGame`, `feistel3HashIdealGame`,
  `feistel3RandomRoundsGame`, `feistel3KeyedGame`, `randomFunctionGame`, `idealPermGame`: 3-round
  Feistel, ideal random-function, and ideal random-permutation games.
* `Cslib.Crypto.LubyRackoff.feistelStrongOracle`, `idealStrongGame`,
  `independentTableStrongGame`, `feistel4StrongKeyedGame`, `feistel4StrongRandomRoundsGame`,
  `feistel3CCAAttack`: bidirectional (forward + inverse) oracle games and the 3-query CCA attack
  on 3-round Feistel.

## Main results

* `Cslib.Crypto.LubyRackoff.prodComm_trans_feistelNetwork_reverse_trans_prodComm`: swap-reversal
  conjugation identity for Feistel decryption over groups of exponent two.
* `Cslib.Probability.isDeltaUniversalHash_uniformOfFintype`,
  `Cslib.Probability.isDeltaUniversalHash_neg_uniformOfFintype`: a uniform random function
  into `G` and its negation are `|G|⁻¹`-Δ-universal.
* `Cslib.Crypto.LubyRackoff.feistel3HashIdealGame_apply_le`,
  `Cslib.Crypto.LubyRackoff.randomFunctionGame_apply_le_feistel3HashIdealGame`: two-sided
  probability comparisons for 3-round Luby–Rackoff with Δ-universal Round 1.
* `Cslib.Crypto.LubyRackoff.advantage_feistel3HashIdealGame_randomFunctionGame_le`,
  `Cslib.Crypto.LubyRackoff.advantage_feistel3HashIdealGame_idealPermGame_le`: 3-round
  Luby–Rackoff bounds with Δ-universal Round 1 against `randomFunctionGame` and `idealPermGame`.
* `Cslib.Crypto.LubyRackoff.advantage_feistel3RandomRoundsGame_randomFunctionGame_le`,
  `Cslib.Crypto.LubyRackoff.advantage_feistel3RandomRoundsGame_idealPermGame_le`: 3-round
  Luby–Rackoff bounds with three uniform random round functions.
* `Cslib.Crypto.LubyRackoff.advantage_feistel3KeyedGame_randomFunctionGame_le`,
  `Cslib.Crypto.LubyRackoff.advantage_feistel3KeyedGame_idealPermGame_le`: Boneh–Shoup Theorem 4.9
  combining the 3-round PRF hybrid reduction with the information-theoretic PRF and PRP bounds.
* `Cslib.Crypto.LubyRackoff.advantage_feistel4StrongKeyedGame_feistel4StrongRandomRoundsGame_le`,
  `Cslib.Crypto.LubyRackoff.feistel4StrongRandomRoundsGame_apply_le`,
  `Cslib.Crypto.LubyRackoff.idealStrongGame_apply_le_feistel4StrongRandomRoundsGame`,
  `Cslib.Crypto.LubyRackoff.advantage_feistel4StrongRandomRoundsGame_idealStrongGame_le`,
  `Cslib.Crypto.LubyRackoff.advantage_feistel4StrongKeyedGame_idealStrongGame_le`,
  `Cslib.Crypto.LubyRackoff.advantage_feistel4StrongRandomRoundsGame_bitString_le`:
  4-round bidirectional PRF hybrid reduction, information-theoretic random-round collision bound,
  and full 4-round strong PRP Luby–Rackoff theorem.
* `Cslib.Crypto.LubyRackoff.eval_feistel3_feistel3CCAAttack`,
  `Cslib.Crypto.LubyRackoff.advantage_feistel3CCAAttack_self`,
  `Cslib.Crypto.LubyRackoff.idealStrongGame_feistel3CCAAttack_true_le`,
  `Cslib.Crypto.LubyRackoff.le_advantage_feistel3CCAAttack_idealStrongGame_of_ne`,
  `Cslib.Crypto.LubyRackoff.le_advantage_feistel3CCAAttack_idealStrongGame`,
  `Cslib.Crypto.LubyRackoff.advantage_feistel3CCAAttack_independentTable`: the 3-query CCA
  distinguisher against 3-round Feistel.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 4.1.3 and 4.5 (Theorem 4.9 and Exercise 4.15(b)).
* [M. Luby, C. Rackoff, *How to Construct Pseudorandom Permutations from Pseudorandom
  Functions*][LubyRackoff1988].
-/

@[expose] public section

namespace Cslib.Crypto.LubyRackoff

open Cslib.Probability
open scoped ENNReal NNReal

/-! ### Algebraic Feistel permutations -/

section Algebraic

variable {G : Type*} [AddGroup G]

/-- One Feistel round `(L, R) ↦ (R, L + f R)` over an additive group `G`. -/
def feistelRound (f : G → G) (p : G × G) : G × G :=
  (p.2, p.1 + f p.2)

/-- The inverse of one Feistel round `(L', R') ↦ (R' - f L', L')`, requiring no invertibility of
`f`. -/
def feistelInvRound (f : G → G) (p : G × G) : G × G :=
  (p.2 - f p.1, p.1)

@[simp]
theorem feistelRound_fst (f : G → G) (p : G × G) : (feistelRound f p).1 = p.2 := rfl

@[simp]
theorem feistelRound_snd (f : G → G) (p : G × G) : (feistelRound f p).2 = p.1 + f p.2 := rfl

@[simp]
theorem feistelInvRound_fst (f : G → G) (p : G × G) : (feistelInvRound f p).1 = p.2 - f p.1 :=
  rfl

@[simp]
theorem feistelInvRound_snd (f : G → G) (p : G × G) : (feistelInvRound f p).2 = p.1 := rfl

@[simp]
theorem feistelInvRound_feistelRound (f : G → G) (p : G × G) :
    feistelInvRound f (feistelRound f p) = p := by
  ext <;> simp [feistelRound, feistelInvRound]

@[simp]
theorem feistelRound_feistelInvRound (f : G → G) (p : G × G) :
    feistelRound f (feistelInvRound f p) = p := by
  ext <;> simp [feistelRound, feistelInvRound]

/-- A single Feistel round as a permutation of `G × G`. -/
def feistelRoundEquiv (f : G → G) : G × G ≃ G × G where
  toFun := feistelRound f
  invFun := feistelInvRound f
  left_inv := feistelInvRound_feistelRound f
  right_inv := feistelRound_feistelInvRound f

@[simp]
theorem feistelRoundEquiv_apply (f : G → G) (p : G × G) :
    feistelRoundEquiv f p = feistelRound f p := rfl

@[simp]
theorem feistelRoundEquiv_symm_apply (f : G → G) (p : G × G) :
    (feistelRoundEquiv f).symm p = feistelInvRound f p := rfl

/-- Multi-round Feistel network composing a list of round functions from left to right. -/
def feistelNetwork (fs : List (G → G)) : G × G ≃ G × G :=
  fs.foldl (fun e f => e.trans (feistelRoundEquiv f)) (Equiv.refl (G × G))

@[simp]
theorem feistelNetwork_nil : feistelNetwork ([] : List (G → G)) = Equiv.refl (G × G) := rfl

@[simp]
theorem feistelNetwork_singleton (f : G → G) :
    feistelNetwork [f] = feistelRoundEquiv f := rfl

private theorem foldl_feistelRoundEquiv (e : G × G ≃ G × G) (fs : List (G → G)) :
    fs.foldl (fun acc f => acc.trans (feistelRoundEquiv f)) e =
      e.trans (feistelNetwork fs) := by
  induction fs generalizing e with
  | nil => rfl
  | cons f rest ih =>
    simp only [List.foldl_cons, feistelNetwork, Equiv.refl_trans]
    rw [ih (e.trans (feistelRoundEquiv f)), ih (feistelRoundEquiv f)]
    rfl

@[simp]
theorem feistelNetwork_cons (f : G → G) (fs : List (G → G)) :
    feistelNetwork (f :: fs) = (feistelRoundEquiv f).trans (feistelNetwork fs) := by
  simp only [feistelNetwork, List.foldl_cons, Equiv.refl_trans]
  exact foldl_feistelRoundEquiv (feistelRoundEquiv f) fs

theorem feistelNetwork_append (fs₁ fs₂ : List (G → G)) :
    feistelNetwork (fs₁ ++ fs₂) = (feistelNetwork fs₁).trans (feistelNetwork fs₂) := by
  induction fs₁ with
  | nil => rfl
  | cons f rest ih =>
    simp only [List.cons_append, feistelNetwork_cons, ih]
    rfl

/-- Over any group of exponent two (`∀ x : G, -x = x`), swapping the two halves conjugates one
Feistel round to its inverse. -/
theorem prodComm_trans_feistelRoundEquiv_trans_prodComm
    (hneg : ∀ x : G, -x = x) (f : G → G) :
    (Equiv.prodComm G G).trans ((feistelRoundEquiv f).trans (Equiv.prodComm G G)) =
      (feistelRoundEquiv f).symm := by
  ext ⟨a, b⟩ <;> simp [feistelRound, feistelInvRound, sub_eq_add_neg, hneg]

/-- Over any group of exponent two (`∀ x : G, -x = x`), Feistel decryption is Feistel encryption
with the round functions in reverse order, conjugated by swapping the two halves. -/
theorem prodComm_trans_feistelNetwork_reverse_trans_prodComm
    (hneg : ∀ x : G, -x = x) (fs : List (G → G)) :
    (Equiv.prodComm G G).trans ((feistelNetwork fs.reverse).trans (Equiv.prodComm G G)) =
      (feistelNetwork fs).symm := by
  induction fs with
  | nil =>
    ext ⟨a, b⟩ <;> rfl
  | cons f rest ih =>
    rw [List.reverse_cons, feistelNetwork_append, feistelNetwork_singleton, feistelNetwork_cons]
    refine Equiv.ext fun p => ?_
    have hround := Equiv.congr_fun (prodComm_trans_feistelRoundEquiv_trans_prodComm hneg f)
      ((feistelNetwork rest).symm p)
    have hrest := Equiv.congr_fun ih p
    simp only [Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.prodComm_apply] at hround hrest ⊢
    rw [← hround, ← hrest, Prod.swap_swap]

/-- The three-round Feistel permutation `(feistelRoundEquiv f₁).trans ((feistelRoundEquiv f₂).trans
(feistelRoundEquiv f₃))`. -/
def feistel3 (f₁ f₂ f₃ : G → G) : G × G ≃ G × G :=
  (feistelRoundEquiv f₁).trans ((feistelRoundEquiv f₂).trans (feistelRoundEquiv f₃))

/-- The four-round Feistel permutation `(feistel3 f₁ f₂ f₃).trans (feistelRoundEquiv f₄)`. -/
def feistel4 (f₁ f₂ f₃ f₄ : G → G) : G × G ≃ G × G :=
  (feistel3 f₁ f₂ f₃).trans (feistelRoundEquiv f₄)

theorem feistelNetwork_three (f₁ f₂ f₃ : G → G) :
    feistelNetwork [f₁, f₂, f₃] = feistel3 f₁ f₂ f₃ := rfl

theorem feistelNetwork_four (f₁ f₂ f₃ f₄ : G → G) :
    feistelNetwork [f₁, f₂, f₃, f₄] = feistel4 f₁ f₂ f₃ f₄ := rfl

theorem feistel3_apply (f₁ f₂ f₃ : G → G) (p : G × G) :
    feistel3 f₁ f₂ f₃ p =
      (p.2 + f₂ (p.1 + f₁ p.2), (p.1 + f₁ p.2) + f₃ (p.2 + f₂ (p.1 + f₁ p.2))) := rfl

theorem feistel3_symm_apply (f₁ f₂ f₃ : G → G) (vw : G × G) :
    (feistel3 f₁ f₂ f₃).symm vw =
      ((vw.2 - f₃ vw.1) - f₁ (vw.1 - f₂ (vw.2 - f₃ vw.1)),
        vw.1 - f₂ (vw.2 - f₃ vw.1)) := rfl

theorem feistel4_apply (f₁ f₂ f₃ f₄ : G → G) (p : G × G) :
    feistel4 f₁ f₂ f₃ f₄ p = feistelRound f₄ (feistel3 f₁ f₂ f₃ p) := rfl

theorem feistel4_symm_apply (f₁ f₂ f₃ f₄ : G → G) (wz : G × G) :
    (feistel4 f₁ f₂ f₃ f₄).symm wz = (feistel3 f₁ f₂ f₃).symm (feistelInvRound f₄ wz) := rfl

end Algebraic

/-! ### The 3-round Luby–Rackoff theorem -/

section LubyRackoff3

variable {K K₁ G : Type} [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]

/-- The 3-round Feistel game with a fixed first round function `f₁` and independent uniform random
second and third round functions `f₂, f₃ : G → G`. -/
noncomputable def feistel3FixedGame (f₁ : G → G)
    (program : OracleComp (fun _ : G × G => G × G) Bool) : Game := do
  let f₂ ← PMF.uniformOfFintype (G → G)
  let f₃ ← PMF.uniformOfFintype (G → G)
  OracleComp.interpret (fun p => PMF.pure (feistel3 f₁ f₂ f₃ p)) program

/-- The 3-round Feistel game where the first round function is drawn from a keyed hash family
`(seed₁, h₁)` and the second and third round functions are independent uniform random functions. -/
noncomputable def feistel3HashIdealGame (seed₁ : PMF K₁) (h₁ : K₁ → G → G)
    (program : OracleComp (fun _ : G × G => G × G) Bool) : Game := do
  let k₁ ← seed₁
  feistel3FixedGame (h₁ k₁) program

/-- The 3-round Feistel game with three independent uniform random round functions
`f₁, f₂, f₃ : G → G`. -/
noncomputable def feistel3RandomRoundsGame
    (program : OracleComp (fun _ : G × G => G × G) Bool) : Game := do
  let f₁ ← PMF.uniformOfFintype (G → G)
  feistel3FixedGame f₁ program

/-- The ideal random-function game on `G × G`: sample a uniform table `(G × G) → (G × G)` and
answer every query from it. -/
noncomputable def randomFunctionGame
    (program : OracleComp (fun _ : G × G => G × G) Bool) : Game := do
  let table ← PMF.uniformOfFintype (G × G → G × G)
  OracleComp.interpret (fun p => PMF.pure (table p)) program

/-- The ideal random-permutation game on `G × G`: sample a uniform permutation
`π ← PMF.uniformOfFintype (Equiv.Perm (G × G))` and answer every query via `π p`. -/
noncomputable def idealPermGame
    (program : OracleComp (fun _ : G × G => G × G) Bool) : Game := do
  let π ← PMF.uniformOfFintype (Equiv.Perm (G × G))
  OracleComp.interpret (fun p => PMF.pure (π p)) program

/-- Deduplicate queries of an adaptive program by caching the first answer to each query in an
association list. -/
private def dedup {α : Type} (program : OracleComp (fun _ : G × G => G × G) α) :
    OracleComp (fun _ : G × G => G × G) (α × List ((G × G) × (G × G))) :=
  (OracleComp.interpret (memoize OracleComp.query) program).run []

omit [AddGroup G] [Fintype G] [Nonempty G] in
private theorem interpret_dedup {α : Type} (oracle : G × G → PMF (G × G))
    (program : OracleComp (fun _ : G × G => G × G) α) :
    OracleComp.interpret oracle (dedup program) =
      (OracleComp.interpret (memoize oracle) program).run [] := by
  have hhom : IsMonadHom (OracleComp (fun _ : G × G => G × G)) PMF
      (OracleComp.interpret oracle) :=
    PFunctor.FreeM.isMonadHom_liftM (P := ⟨G × G, fun _ => G × G⟩) oracle
  rw [dedup, OracleComp.map_run_interpret hhom]
  simp only [hhom.map_memoize, OracleComp.interpret_query]

set_option linter.unusedFintypeInType false in
omit [AddGroup G] [Nonempty G] in
private theorem map_fst_interpret_dedup_pure {α : Type} (F : G × G → G × G)
    (program : OracleComp (fun _ : G × G => G × G) α) :
    (OracleComp.interpret (fun p => PMF.pure (F p)) (dedup program)).map Prod.fst =
      OracleComp.interpret (fun p => PMF.pure (F p)) program := by
  rw [interpret_dedup, ← RandomOracle.interpret_eq_memoize (fun p => PMF.pure (F p)) program]
  have hpi : Probability.PMF.pi (fun p => PMF.pure (F p)) = PMF.pure F := by
    ext table
    simp only [Probability.PMF.pi_apply, PMF.pure_apply]
    by_cases h : table = F
    · subst h; simp
    · rw [ite_eq_right h]
      obtain ⟨p, hp⟩ := Function.ne_iff.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ p) (ite_eq_right hp)
  simp [hpi]

/-- Evaluate `feistel3 f₁ f₂ f₃ p` by querying a combined round-function oracle
`Bool × G → G` at `(false, p.1 + f₁ p.2)` for `f₂` and `(true, v)` for `f₃`. -/
private def feistel3Query (f₁ : G → G) (p : G × G) :
    OracleComp (fun _ : Bool × G => G) (G × G) := do
  let u := p.1 + f₁ p.2
  let y₂ ← OracleComp.query (spec := fun _ : Bool × G => G) (false, u)
  let v := p.2 + y₂
  let y₃ ← OracleComp.query (spec := fun _ : Bool × G => G) (true, v)
  return (v, u + y₃)

private def splitBoolTable {X Y : Type*} : (Bool × X → Y) ≃ (X → Y) × (X → Y) where
  toFun table := (fun u => table (false, u), fun v => table (true, v))
  invFun fg := fun q => cond q.1 (fg.2 q.2) (fg.1 q.2)
  left_inv table := by
    funext ⟨b, x⟩
    cases b <;> rfl
  right_inv _ := rfl

private noncomputable def lazyRoundHandler (f₁ : G → G) (p : G × G) :
    StateT (List ((Bool × G) × G)) PMF (G × G) :=
  OracleComp.interpret (memoize (fun _ : Bool × G => PMF.uniformOfFintype G)) (feistel3Query f₁ p)

private noncomputable def realRoundHandler (f₁ : G → G) (p : G × G) :
    StateT (List ((Bool × G) × G) × Bool) PMF (G × G) := fun (cache, bad) => do
  let u := p.1 + f₁ p.2
  let (y₂, cache₁) ← memoize (fun _ : Bool × G => PMF.uniformOfFintype G) (false, u) cache
  let v := p.2 + y₂
  let (y₃, cache₂) ← memoize (fun _ : Bool × G => PMF.uniformOfFintype G) (true, v) cache₁
  let w := u + y₃
  let bad' := bad || (cache.lookup (false, u)).isSome || (cache.lookup (true, v)).isSome
  return ((v, w), (cache₂, bad'))

private noncomputable def idealRoundHandler (f₁ : G → G) (p : G × G) :
    StateT (List ((Bool × G) × G) × Bool) PMF (G × G) := fun (cache, bad) => do
  let u := p.1 + f₁ p.2
  let vw ← PMF.uniformOfFintype (G × G)
  let v := vw.1
  let w := vw.2
  let cache₁ := ((false, u), -p.2 + v) :: cache
  let cache₂ := ((true, v), -u + w) :: cache₁
  let bad' := bad || (cache.lookup (false, u)).isSome || (cache.lookup (true, v)).isSome
  return ((v, w), (cache₂, bad'))

private theorem realRoundHandler_map_fst (f₁ : G → G) (p : G × G)
    (st : List ((Bool × G) × G) × Bool) :
    (realRoundHandler f₁ p st).map (fun (ans, st') => (ans, st'.1)) =
      lazyRoundHandler f₁ p st.1 := by
  simp only [realRoundHandler, lazyRoundHandler, feistel3Query, OracleComp.interpret_bind,
    OracleComp.interpret_query, OracleComp.interpret_pure,
    Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
    PMF.map_bind, PMF.pure_map]
  rfl

private theorem feistel3FixedGame_eq_realRoundHandler (f₁ : G → G)
    (program : OracleComp (fun _ : G × G => G × G) Bool) :
    feistel3FixedGame f₁ program =
      (((OracleComp.interpret (realRoundHandler f₁) (dedup program)).run ([], false)).map
        fun x => x.1.1) := by
  have hdrop := OracleComp.run_interpret_map_state (realRoundHandler f₁) (lazyRoundHandler f₁)
    Prod.fst (realRoundHandler_map_fst f₁) (dedup program) ([], false)
  have hdrop' := congrArg (PMF.map fun x => x.1.1) hdrop
  simp only [PMF.map_comp, Function.comp_def] at hdrop'
  rw [hdrop']
  have hlazy := RandomOracle.interpret_eq_memoize (fun _ : Bool × G => PMF.uniformOfFintype G)
    (OracleComp.interpret (feistel3Query f₁) (dedup program))
  rw [Probability.PMF.pi_uniformOfFintype] at hlazy
  have hcomp :
      OracleComp.interpret (memoize (fun _ : Bool × G => PMF.uniformOfFintype G))
        (OracleComp.interpret (feistel3Query f₁) (dedup program)) =
      OracleComp.interpret (lazyRoundHandler f₁) (dedup program) :=
    OracleComp.interpret_interpret _ _ _
  rw [hcomp] at hlazy
  have hlazy' := congrArg (PMF.map Prod.fst) hlazy.symm
  simp only [Probability.PMF.monad_bind_eq_bind, PMF.map_comp, Function.comp_def,
    PMF.map_bind] at hlazy'
  rw [hlazy']
  have htable (table : Bool × G → G) :
      (OracleComp.interpret (fun q => PMF.pure (table q))
        (OracleComp.interpret (feistel3Query f₁) (dedup program))).map Prod.fst =
      OracleComp.interpret
        (fun p => PMF.pure (feistel3 f₁ (fun u => table (false, u)) (fun v => table (true, v)) p))
        program := by
    rw [OracleComp.interpret_interpret]
    have hstep :
        (fun p => OracleComp.interpret (fun q => PMF.pure (table q)) (feistel3Query f₁ p)) =
        (fun p =>
          PMF.pure (feistel3 f₁ (fun u => table (false, u)) (fun v => table (true, v)) p)) := by
      funext p
      simp [feistel3Query, feistel3_apply]
    rw [hstep, map_fst_interpret_dedup_pure]
  simp only [htable]
  have hunif :
      (PMF.uniformOfFintype (Bool × G → G)).map splitBoolTable =
        (PMF.uniformOfFintype (G → G)).bind fun f₂ =>
          (PMF.uniformOfFintype (G → G)).map fun f₃ => (f₂, f₃) := by
    rw [Probability.PMF.uniformOfFintype_map_equiv splitBoolTable,
      Probability.PMF.uniformOfFintype_prod]
  have hbind := congrArg
    (fun d : PMF ((G → G) × (G → G)) =>
      d.bind fun fg => OracleComp.interpret (fun p => PMF.pure (feistel3 f₁ fg.1 fg.2 p)) program)
    hunif.symm
  simpa only [feistel3FixedGame, splitBoolTable, Equiv.coe_fn_mk, PMF.bind_map,
    PMF.bind_bind, Function.comp_def, PMF.monad_bind_eq_bind] using hbind

omit [AddGroup G] [Fintype G] [Nonempty G] in
private theorem lookup_true_cons_false (u v : G) (y₂ : G) (cache : List ((Bool × G) × G)) :
    (((false, u), y₂) :: cache).lookup (true, v) = cache.lookup (true, v) := by
  have h : ((true, v) == (false, u)) = false := rfl
  simp [List.lookup_cons, h]

omit [Fintype G] [DecidableEq G] [Nonempty G] in
private theorem addLeft_apply (a b : G) : Equiv.addLeft a b = a + b := rfl

/-- The real and ideal round handlers agree until a `U`-collision or `V`-collision occurs. -/
private theorem identicalUntilBad_roundHandler (f₁ : G → G) :
    OracleComp.IdenticalUntilBad (realRoundHandler f₁) (idealRoundHandler f₁)
      fun st => st.2 = true where
  agree p st hst ans st' hst' := by
    rcases st with ⟨cache, bad⟩
    rcases st' with ⟨cache', bad'⟩
    have hbad : bad = false := Bool.eq_false_iff.mpr hst
    have hbad' : bad' = false := Bool.eq_false_iff.mpr hst'
    subst hbad hbad'
    cases hu : cache.lookup (false, p.1 + f₁ p.2) with
    | some y₂₀ =>
      have hreal0 : realRoundHandler f₁ p (cache, false) (ans, (cache', false)) = 0 := by
        refine (PMF.apply_eq_zero_iff _ _).mpr fun hmem => ?_
        simp only [realRoundHandler, Probability.PMF.monad_bind_eq_bind,
          Probability.PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff,
          PMF.mem_support_pure_iff] at hmem
        obtain ⟨⟨y₂, c₁⟩, -, ⟨y₃, c₂⟩, -, heq⟩ := hmem
        have h1 := congrArg (fun x => x.2.2) heq
        simp [hu] at h1
      have hideal0 : idealRoundHandler f₁ p (cache, false) (ans, (cache', false)) = 0 := by
        refine (PMF.apply_eq_zero_iff _ _).mpr fun hmem => ?_
        simp only [idealRoundHandler, Probability.PMF.monad_bind_eq_bind,
          Probability.PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff,
          PMF.mem_support_pure_iff] at hmem
        obtain ⟨vw, -, heq⟩ := hmem
        have h1 := congrArg (fun x => x.2.2) heq
        simp [hu] at h1
      rw [hreal0, hideal0]
    | none =>
      have hreal :
          realRoundHandler f₁ p (cache, false) =
            (PMF.uniformOfFintype G).bind fun v =>
              (memoize (fun _ : Bool × G => PMF.uniformOfFintype G) (true, v)
                (((false, p.1 + f₁ p.2), -p.2 + v) :: cache)).bind fun x =>
                  PMF.pure ((v, p.1 + f₁ p.2 + x.1), (x.2, (cache.lookup (true, v)).isSome)) := by
        simp only [realRoundHandler, memoize_of_none _ _ _ hu,
          Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
          PMF.bind_bind, PMF.pure_bind, hu, Option.isSome_none, Bool.false_or]
        conv_rhs =>
          rw [← Probability.PMF.uniformOfFintype_map_equiv (Equiv.addLeft p.2), PMF.bind_map]
        simp only [addLeft_apply, neg_add_cancel_left, Function.comp_def,
          Probability.PMF.uniformOfFintype_map_equiv]
      have hideal :
          idealRoundHandler f₁ p (cache, false) =
            (PMF.uniformOfFintype G).bind fun v =>
              (PMF.uniformOfFintype G).bind fun w =>
                PMF.pure ((v, w),
                  (((true, v), -(p.1 + f₁ p.2) + w) ::
                    ((false, p.1 + f₁ p.2), -p.2 + v) :: cache,
                    (cache.lookup (true, v)).isSome)) := by
        simp only [idealRoundHandler, hu, Option.isSome_none, Bool.false_or,
          Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
          ← Probability.PMF.uniformOfFintype_prod, PMF.bind_bind, PMF.bind_map,
          Function.comp_def]
      rw [hreal, hideal, PMF.bind_apply, PMF.bind_apply]
      refine tsum_congr fun v => congrArg (_ * ·) ?_
      cases hv : cache.lookup (true, v) with
      | some y₃₀ =>
        simp only [Option.isSome_some]
        have h1 :
            ((memoize (fun _ : Bool × G => PMF.uniformOfFintype G) (true, v)
              (((false, p.1 + f₁ p.2), -p.2 + v) :: cache)).bind fun x =>
                PMF.pure ((v, p.1 + f₁ p.2 + x.1), (x.2, true)))
              (ans, (cache', false)) = 0 := by
          refine (PMF.apply_eq_zero_iff _ _).mpr fun hmem => ?_
          rw [PMF.mem_support_bind_iff] at hmem
          obtain ⟨⟨y₃, c₂⟩, -, hmem'⟩ := hmem
          rw [PMF.mem_support_pure_iff] at hmem'
          exact Bool.noConfusion (congrArg (fun x => x.2.2) hmem')
        have h2 :
            ((PMF.uniformOfFintype G).bind fun w =>
              PMF.pure ((v, w),
                (((true, v), -(p.1 + f₁ p.2) + w) ::
                  ((false, p.1 + f₁ p.2), -p.2 + v) :: cache, true)))
              (ans, (cache', false)) = 0 := by
          refine (PMF.apply_eq_zero_iff _ _).mpr fun hmem => ?_
          rw [PMF.mem_support_bind_iff] at hmem
          obtain ⟨w, -, hmem'⟩ := hmem
          rw [PMF.mem_support_pure_iff] at hmem'
          exact Bool.noConfusion (congrArg (fun x => x.2.2) hmem')
        rw [h1, h2]
      | none =>
        simp only [Option.isSome_none]
        have hv' : (((false, p.1 + f₁ p.2), -p.2 + v) :: cache).lookup (true, v) = none := by
          rw [lookup_true_cons_false, hv]
        rw [memoize_of_none _ _ _ hv']
        simp only [Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
          PMF.bind_bind, PMF.pure_bind]
        have heq_w :
            (PMF.uniformOfFintype G).bind (fun y₃ =>
              PMF.pure ((v, p.1 + f₁ p.2 + y₃),
                (((true, v), y₃) :: ((false, p.1 + f₁ p.2), -p.2 + v) :: cache, false))) =
            (PMF.uniformOfFintype G).bind (fun w =>
              PMF.pure ((v, w),
                (((true, v), -(p.1 + f₁ p.2) + w) ::
                  ((false, p.1 + f₁ p.2), -p.2 + v) :: cache, false))) := by
          conv_rhs =>
            rw [← Probability.PMF.uniformOfFintype_map_equiv (Equiv.addLeft (p.1 + f₁ p.2)),
              PMF.bind_map]
          simp only [addLeft_apply, neg_add_cancel_left, Function.comp_def]
        exact DFunLike.congr_fun heq_w (ans, (cache', false))
  absorb_first p st hst x hx := by
    rcases st with ⟨cache, bad⟩
    simp only at hst
    subst hst
    simp only [realRoundHandler, Probability.PMF.monad_bind_eq_bind,
      Probability.PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff] at hx
    obtain ⟨⟨y₂, c₁⟩, -, ⟨y₃, c₂⟩, -, rfl⟩ := hx
    simp
  absorb_second p st hst x hx := by
    rcases st with ⟨cache, bad⟩
    simp only at hst
    subst hst
    simp only [idealRoundHandler, Probability.PMF.monad_bind_eq_bind,
      Probability.PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff] at hx
    obtain ⟨vw, -, rfl⟩ := hx
    simp

/-- Reconstruct the round-function cache of `idealRoundHandler f₁` from the query cache. -/
private def representCache (f₁ : G → G) :
    List ((G × G) × (G × G)) → List ((Bool × G) × G)
  | [] => []
  | (p, (v, w)) :: rest =>
    let u := p.1 + f₁ p.2
    ((true, v), -u + w) :: ((false, u), -p.2 + v) :: representCache f₁ rest

/-- Whether the query cache `qc` triggers a `U`-collision or `V`-collision in
`idealRoundHandler f₁`. -/
private def hasCollision (f₁ : G → G) : List ((G × G) × (G × G)) → Bool
  | [] => false
  | (p, (v, _)) :: rest =>
    let u := p.1 + f₁ p.2
    let cache := representCache f₁ rest
    hasCollision f₁ rest || (cache.lookup (false, u)).isSome || (cache.lookup (true, v)).isSome

private theorem run_idealRoundHandler_memoize {α : Type} (f₁ : G → G)
    (program : OracleComp (fun _ : G × G => G × G) α) (qc : List ((G × G) × (G × G))) :
    ((OracleComp.interpret (idealRoundHandler f₁)
      ((OracleComp.interpret (memoize OracleComp.query) program).run qc)).run
        (representCache f₁ qc, hasCollision f₁ qc)) =
      ((OracleComp.interpret (memoize (fun _ : G × G => PMF.uniformOfFintype (G × G)))
        program).run qc).map
        (fun (a, qc') => ((a, qc'), (representCache f₁ qc', hasCollision f₁ qc'))) := by
  induction program using PFunctor.FreeM.induction generalizing qc with
  | pure a =>
    simp [PMF.pure_map]
  | lift_bind p cont ih =>
    change ((OracleComp.interpret (idealRoundHandler f₁)
      ((OracleComp.interpret (memoize OracleComp.query) (OracleComp.query p >>= cont)).run qc)).run
        (representCache f₁ qc, hasCollision f₁ qc)) =
      ((OracleComp.interpret (memoize (fun _ : G × G => PMF.uniformOfFintype (G × G)))
        (OracleComp.query p >>= cont)).run qc).map _
    simp only [OracleComp.interpret_bind, OracleComp.interpret_query, StateT.run_bind]
    change (((OracleComp.interpret (idealRoundHandler f₁) (memoize OracleComp.query p qc)).run
        (representCache f₁ qc, hasCollision f₁ qc)).bind fun p_1 =>
      (OracleComp.interpret (idealRoundHandler f₁)
        ((OracleComp.interpret (memoize OracleComp.query) (cont p_1.1.1)).run p_1.1.2)).run p_1.2) =
      (((memoize (fun _ : G × G => PMF.uniformOfFintype (G × G)) p qc).bind fun p =>
        (OracleComp.interpret (memoize (fun _ : G × G => PMF.uniformOfFintype (G × G)))
          (cont p.1)).run p.2).map
        fun (a, qc') => ((a, qc'), (representCache f₁ qc', hasCollision f₁ qc')))
    cases h : qc.lookup p with
    | some r =>
      rw [memoize_of_some _ _ _ _ h, memoize_of_some _ _ _ _ h]
      simp only [OracleComp.interpret_pure, StateT.run_pure,
        Probability.PMF.monad_pure_eq_pure, PMF.pure_bind]
      exact ih r qc
    | none =>
      rw [memoize_of_none _ _ _ h, memoize_of_none _ _ _ h]
      simp only [OracleComp.interpret_bind, OracleComp.interpret_query,
        OracleComp.interpret_pure, StateT.run_bind, StateT.run_pure,
        Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
        PMF.bind_bind, PMF.pure_bind, PMF.map_bind]
      simp only [StateT.run, idealRoundHandler, Probability.PMF.monad_bind_eq_bind,
        Probability.PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
      refine congrArg (PMF.bind _) (funext fun vw => ?_)
      exact ih vw ((p, vw) :: qc)

private theorem map_fst_run_idealRoundHandler (f₁ : G → G)
    (program : OracleComp (fun _ : G × G => G × G) Bool) :
    (((OracleComp.interpret (idealRoundHandler f₁) (dedup program)).run ([], false)).map
      fun x => x.1.1) = randomFunctionGame program := by
  have h := congrArg (PMF.map fun x => x.1.1) (run_idealRoundHandler_memoize f₁ program [])
  simp only [representCache, hasCollision, PMF.map_comp, Function.comp_def] at h
  rw [dedup, h]
  have hm := RandomOracle.interpret_eq_memoize
    (fun _ : G × G => PMF.uniformOfFintype (G × G)) program
  rw [Probability.PMF.pi_uniformOfFintype] at hm
  exact hm.symm

private theorem toOuterMeasure_bad_idealRoundHandler (f₁ : G → G)
    (program : OracleComp (fun _ : G × G => G × G) Bool) :
    ((OracleComp.interpret (idealRoundHandler f₁) (dedup program)).run ([], false)).toOuterMeasure
      {x | x.2.2 = true} =
    ((OracleComp.interpret (memoize (fun _ : G × G => PMF.uniformOfFintype (G × G)))
      program).run []).toOuterMeasure {x | hasCollision f₁ x.2 = true} := by
  have h := run_idealRoundHandler_memoize f₁ program []
  simp only [representCache, hasCollision] at h
  rw [dedup, h, PMF.toOuterMeasure_map_apply]
  rfl

/-- Whether the query cache `qc` contains two entries with the same Round-1 intermediate value
`u = L + f₁ R`. -/
private def hasUCollision (f₁ : G → G) : List ((G × G) × (G × G)) → Bool
  | [] => false
  | (p, _) :: rest =>
    hasUCollision f₁ rest || rest.any (fun e => decide (p.1 + f₁ p.2 = e.1.1 + f₁ e.1.2))

/-- Whether the query cache `qc` contains two entries with the same Round-2 output `v`. -/
private def hasVCollision : List ((G × G) × (G × G)) → Bool
  | [] => false
  | (_, (v, _)) :: rest =>
    hasVCollision rest || rest.any (fun e => decide (v = e.2.1))

omit [Fintype G] [Nonempty G] in
private theorem isSome_lookup_false_representCache (f₁ : G → G) (u : G)
    (qc : List ((G × G) × (G × G))) :
    ((representCache f₁ qc).lookup (false, u)).isSome =
      qc.any (fun e => decide (u = e.1.1 + f₁ e.1.2)) := by
  induction qc with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨p, ⟨v, w⟩⟩
    simp only [representCache, List.lookup_cons, List.any_cons]
    have htf : ((false, u) == (true, v)) = false := rfl
    rw [htf]
    by_cases h : u = p.1 + f₁ p.2
    · subst h
      simp
    · have hff : ((false, u) == (false, p.1 + f₁ p.2)) = false :=
        beq_eq_false_iff_ne.mpr fun heq => h (Prod.mk.inj heq).2
      simp [hff, h, ih]

omit [Fintype G] [Nonempty G] in
private theorem isSome_lookup_true_representCache (f₁ : G → G) (v : G)
    (qc : List ((G × G) × (G × G))) :
    ((representCache f₁ qc).lookup (true, v)).isSome =
      qc.any (fun e => decide (v = e.2.1)) := by
  induction qc with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨p, ⟨v', w⟩⟩
    simp only [representCache, List.lookup_cons, List.any_cons]
    by_cases h : v = v'
    · subst h
      simp
    · have htt : ((true, v) == (true, v')) = false :=
        beq_eq_false_iff_ne.mpr fun heq => h (Prod.mk.inj heq).2
      have htf : ((true, v) == (false, p.1 + f₁ p.2)) = false := rfl
      simp [htt, htf, h, ih]

omit [Fintype G] [Nonempty G] in
private theorem hasCollision_eq_or (f₁ : G → G) (qc : List ((G × G) × (G × G))) :
    hasCollision f₁ qc = (hasUCollision f₁ qc || hasVCollision qc) := by
  induction qc with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨p, ⟨v, w⟩⟩
    simp only [hasCollision, hasUCollision, hasVCollision, ih,
      isSome_lookup_false_representCache, isSome_lookup_true_representCache]
    ac_rfl

omit [Fintype G] [Nonempty G] in
/-- Bound on a single new query `p` colliding in Round 1 with any entry in `rest`. -/
private theorem toOuterMeasure_any_uCollision_le {seed₁ : PMF K₁} {h₁ : K₁ → G → G} {ε : ℝ≥0∞}
    (hh₁ : IsDeltaUniversalHash seed₁ h₁ ε) (p : G × G)
    (rest : List ((G × G) × (G × G))) (hhead : ∀ e ∈ rest, p ≠ e.1) :
    seed₁.toOuterMeasure
      {k₁ | rest.any (fun e => decide (p.1 + h₁ k₁ p.2 = e.1.1 + h₁ k₁ e.1.2)) = true} ≤
      rest.length * ε := by
  induction rest with
  | nil => simp
  | cons e rest' ih =>
    have hp : p ≠ e.1 := hhead e List.mem_cons_self
    have hrest' : ∀ e' ∈ rest', p ≠ e'.1 := fun e' he' =>
      hhead e' (List.mem_cons_of_mem e he')
    have hpair :
        seed₁.toOuterMeasure {k₁ | p.1 + h₁ k₁ p.2 = e.1.1 + h₁ k₁ e.1.2} ≤ ε := by
      by_cases hr : p.2 = e.1.2
      · have hemp : {k₁ : K₁ | p.1 + h₁ k₁ p.2 = e.1.1 + h₁ k₁ e.1.2} = ∅ := by
          ext k₁
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          intro heq
          rw [hr] at heq
          exact hp (Prod.ext (add_right_cancel heq) hr)
        rw [hemp]
        simp
      · have hiff :
            {k₁ : K₁ | p.1 + h₁ k₁ p.2 = e.1.1 + h₁ k₁ e.1.2} =
              {k₁ : K₁ | h₁ k₁ p.2 - h₁ k₁ e.1.2 = -p.1 + e.1.1} := by
          ext k₁
          simp only [Set.mem_ofPred_eq]
          rw [eq_comm, ← neg_add_eq_iff_eq_add, sub_eq_iff_eq_add, add_assoc, eq_comm]
        rw [hiff]
        exact hh₁ p.2 e.1.2 hr (-p.1 + e.1.1)
    calc seed₁.toOuterMeasure
          {k₁ | (e :: rest').any
            (fun e' => decide (p.1 + h₁ k₁ p.2 = e'.1.1 + h₁ k₁ e'.1.2)) = true}
        ≤ seed₁.toOuterMeasure
          ({k₁ | p.1 + h₁ k₁ p.2 = e.1.1 + h₁ k₁ e.1.2} ∪
            {k₁ | rest'.any
              (fun e' => decide (p.1 + h₁ k₁ p.2 = e'.1.1 + h₁ k₁ e'.1.2)) = true}) := by
          refine seed₁.toOuterMeasure.mono fun k₁ hk₁ => ?_
          simp only [Set.mem_ofPred_eq, List.any_cons, Bool.or_eq_true,
            decide_eq_true_eq] at hk₁
          exact hk₁
      _ ≤ seed₁.toOuterMeasure {k₁ | p.1 + h₁ k₁ p.2 = e.1.1 + h₁ k₁ e.1.2} +
          seed₁.toOuterMeasure
            {k₁ | rest'.any
              (fun e' => decide (p.1 + h₁ k₁ p.2 = e'.1.1 + h₁ k₁ e'.1.2)) = true} :=
          MeasureTheory.measure_union_le _ _
      _ ≤ ε + rest'.length * ε := add_le_add hpair (ih hrest')
      _ = ((e :: rest').length : ℝ≥0∞) * ε := by
          rw [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring

omit [Fintype G] [Nonempty G] in
/-- Over a cache `qc` with pairwise distinct query keys, a `U`-collision occurs under
`IsDeltaUniversalHash seed₁ h₁ ε` with probability at most `qc.length.choose 2 * ε`. -/
private theorem toOuterMeasure_hasUCollision_le {seed₁ : PMF K₁} {h₁ : K₁ → G → G} {ε : ℝ≥0∞}
    (hh₁ : IsDeltaUniversalHash seed₁ h₁ ε) {qc : List ((G × G) × (G × G))}
    (hnodup : qc.Pairwise (fun a b => a.1 ≠ b.1)) :
    seed₁.toOuterMeasure {k₁ | hasUCollision (h₁ k₁) qc = true} ≤
      qc.length.choose 2 * ε := by
  induction qc with
  | nil => simp [hasUCollision]
  | cons entry rest ih =>
    rcases entry with ⟨p, vw⟩
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hnodup
    calc seed₁.toOuterMeasure {k₁ | hasUCollision (h₁ k₁) ((p, vw) :: rest) = true}
        ≤ seed₁.toOuterMeasure
          ({k₁ | hasUCollision (h₁ k₁) rest = true} ∪
            {k₁ | rest.any (fun e => decide (p.1 + h₁ k₁ p.2 = e.1.1 + h₁ k₁ e.1.2)) = true}) := by
          refine seed₁.toOuterMeasure.mono fun k₁ hk₁ => ?_
          simp only [Set.mem_ofPred_eq, hasUCollision, Bool.or_eq_true] at hk₁
          exact hk₁
      _ ≤ seed₁.toOuterMeasure {k₁ | hasUCollision (h₁ k₁) rest = true} +
          seed₁.toOuterMeasure
            {k₁ | rest.any (fun e => decide (p.1 + h₁ k₁ p.2 = e.1.1 + h₁ k₁ e.1.2)) = true} :=
          MeasureTheory.measure_union_le _ _
      _ ≤ rest.length.choose 2 * ε + rest.length * ε :=
          add_le_add (ih htail) (toOuterMeasure_any_uCollision_le hh₁ p rest hhead)
      _ = (((p, vw) :: rest).length.choose 2 : ℝ≥0∞) * ε := by
          rw [List.length_cons, Nat.choose_succ_succ' rest.length 1, Nat.choose_one_right,
            Nat.cast_add]
          ring

private theorem ne_fst_of_lookup_eq_none {K V : Type*} [BEq K] [LawfulBEq K]
    {k : K} {qc : List (K × V)} (hlookup : qc.lookup k = none) :
    ∀ e ∈ qc, k ≠ e.1 := by
  induction qc with
  | nil => intro e he; cases he
  | cons a rest ih =>
    rw [List.lookup_cons] at hlookup
    cases hka : k == a.1 with
    | true => simp [hka] at hlookup
    | false =>
      simp only [hka] at hlookup
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact beq_eq_false_iff_ne.mp hka
      · exact ih hlookup e he

omit [AddGroup G] [Fintype G] [Nonempty G] in
/-- Every cache produced by `memoize` from `qc` on an `n`-query-bounded program has pairwise
distinct keys and length at most `qc.length + n`. -/
private theorem memoize_pairwise_and_length_le {α : Type}
    (distribution : G × G → PMF (G × G))
    {program : OracleComp (fun _ : G × G => G × G) α} {n : ℕ}
    (hn : OracleComp.IsQueryBounded program n)
    {qc : List ((G × G) × (G × G))} (hpair : qc.Pairwise (fun a b => a.1 ≠ b.1))
    {result : α} {qc' : List ((G × G) × (G × G))}
    (hmem : (result, qc') ∈
      ((OracleComp.interpret (memoize distribution) program).run qc).support) :
    qc'.Pairwise (fun a b => a.1 ≠ b.1) ∧ qc'.length ≤ qc.length + n := by
  induction hn generalizing qc with
  | pure a n =>
    change (result, qc') ∈ (PMF.pure (a, qc)).support at hmem
    rw [PMF.mem_support_pure_iff] at hmem
    obtain ⟨_, rfl⟩ := Prod.mk.inj hmem
    exact ⟨hpair, Nat.le_add_right _ _⟩
  | liftBind p cont n _ ih =>
    change (result, qc') ∈
      ((memoize distribution p qc).bind fun y =>
        (OracleComp.interpret (memoize distribution) (cont y.1)).run y.2).support at hmem
    rw [PMF.mem_support_bind_iff] at hmem
    obtain ⟨⟨r, qc₁⟩, hstep, hcont⟩ := hmem
    have hmem' := (RandomOracle.mem_support_memoize_iff _ _ _ (r, qc₁)).mp hstep
    dsimp only at hmem' hcont
    rcases hmem' with ⟨_, rfl⟩ | ⟨hlookup, _, rfl⟩
    · obtain ⟨hp', hlen'⟩ := ih r hpair hcont
      exact ⟨hp', hlen'.trans (by omega)⟩
    · have hpair₁ : ((p, r) :: qc).Pairwise (fun a b => a.1 ≠ b.1) :=
        List.pairwise_cons.mpr ⟨ne_fst_of_lookup_eq_none hlookup, hpair⟩
      obtain ⟨hp', hlen'⟩ := ih r hpair₁ hcont
      rw [List.length_cons] at hlen'
      exact ⟨hp', by omega⟩

omit [AddGroup G] in
/-- Bound on a uniform pair `vw ← PMF.uniformOfFintype (G × G)` having first coordinate `vw.1`
equal to `e.2.1` for some `e ∈ qc`. -/
private theorem toOuterMeasure_any_vCollision_le (qc : List ((G × G) × (G × G))) :
    (PMF.uniformOfFintype (G × G)).toOuterMeasure
      {vw : G × G | qc.any (fun e => decide (vw.1 = e.2.1)) = true} ≤
      qc.length * (Fintype.card G : ℝ≥0∞)⁻¹ := by
  induction qc with
  | nil => simp
  | cons e rest ih =>
    have hsingle :
        (PMF.uniformOfFintype (G × G)).toOuterMeasure {vw : G × G | vw.1 = e.2.1} =
          (Fintype.card G : ℝ≥0∞)⁻¹ := by
      rw [show {vw : G × G | vw.1 = e.2.1} = Prod.fst ⁻¹' {e.2.1} from rfl,
        ← PMF.toOuterMeasure_map_apply, Probability.PMF.uniformOfFintype_prod_map_fst,
        PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply]
    calc (PMF.uniformOfFintype (G × G)).toOuterMeasure
          {vw : G × G | (e :: rest).any (fun e' => decide (vw.1 = e'.2.1)) = true}
        ≤ (PMF.uniformOfFintype (G × G)).toOuterMeasure
          ({vw : G × G | vw.1 = e.2.1} ∪
            {vw : G × G | rest.any (fun e' => decide (vw.1 = e'.2.1)) = true}) := by
          refine (PMF.uniformOfFintype (G × G)).toOuterMeasure.mono fun vw hvw => ?_
          simp only [Set.mem_ofPred_eq, List.any_cons, Bool.or_eq_true,
            decide_eq_true_eq] at hvw
          exact hvw
      _ ≤ (PMF.uniformOfFintype (G × G)).toOuterMeasure {vw : G × G | vw.1 = e.2.1} +
          (PMF.uniformOfFintype (G × G)).toOuterMeasure
            {vw : G × G | rest.any (fun e' => decide (vw.1 = e'.2.1)) = true} :=
          MeasureTheory.measure_union_le _ _
      _ ≤ (Fintype.card G : ℝ≥0∞)⁻¹ + rest.length * (Fintype.card G : ℝ≥0∞)⁻¹ := by
          rw [hsingle]
          exact add_le_add le_rfl ih
      _ = ((e :: rest).length : ℝ≥0∞) * (Fintype.card G : ℝ≥0∞)⁻¹ := by
          rw [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring

omit [AddGroup G] in
/-- Over `n` queries from a cache `qc` with `hasVCollision qc = false`, the probability that
`memoize (fun _ => PMF.uniformOfFintype (G × G))` produces a `V`-collision is at most
`(n * qc.length + n.choose 2) * |G|⁻¹`. -/
private theorem toOuterMeasure_hasVCollision_le {α : Type}
    {program : OracleComp (fun _ : G × G => G × G) α} {n : ℕ}
    (hn : OracleComp.IsQueryBounded program n)
    {qc : List ((G × G) × (G × G))} (hqc : hasVCollision qc = false) :
    ((OracleComp.interpret (memoize (fun _ : G × G => PMF.uniformOfFintype (G × G)))
      program).run qc).toOuterMeasure {x | hasVCollision x.2 = true} ≤
      (n * qc.length + n.choose 2 : ℕ) * (Fintype.card G : ℝ≥0∞)⁻¹ := by
  refine RandomPermutation.toOuterMeasure_bad_choose_two_le
    (bad := fun s : List ((G × G) × (G × G)) => hasVCollision s = true)
    List.length (Fintype.card G : ℝ≥0∞)⁻¹
    (fun p s hs => ?_) (fun p s _ y hy _ => ?_) hn (Bool.eq_false_iff.mp hqc)
  · have hs' : hasVCollision s = false := Bool.eq_false_iff.mpr hs
    cases hlookup : s.lookup p with
    | some r =>
      rw [show memoize (fun _ : G × G => PMF.uniformOfFintype (G × G)) p s = PMF.pure (r, s)
        from memoize_of_some _ _ _ _ hlookup]
      simp [PMF.toOuterMeasure_pure_apply, hs']
    | none =>
      rw [show memoize (fun _ : G × G => PMF.uniformOfFintype (G × G)) p s =
        (PMF.uniformOfFintype (G × G)).map (fun vw => (vw, (p, vw) :: s))
        from memoize_of_none _ _ _ hlookup, PMF.toOuterMeasure_map_apply]
      refine (le_of_eq ?_).trans (toOuterMeasure_any_vCollision_le s)
      congr 1
      ext ⟨v, w⟩
      simp [hasVCollision, hs']
  · rcases y with ⟨r, qc₁⟩
    have hy' := (RandomOracle.mem_support_memoize_iff _ _ _ (r, qc₁)).mp hy
    dsimp only at hy' ⊢
    rcases hy' with ⟨_, rfl⟩ | ⟨_, _, rfl⟩
    · exact Nat.le_succ _
    · rw [List.length_cons]

/-- Bound on the expected bad-event probability in `idealRoundHandler` averaged over
`k₁ ← seed₁`. -/
private theorem tsum_seed_toOuterMeasure_hasCollision_le {seed₁ : PMF K₁} {h₁ : K₁ → G → G}
    {ε : ℝ≥0∞} (hh₁ : IsDeltaUniversalHash seed₁ h₁ ε)
    {program : OracleComp (fun _ : G × G => G × G) Bool} {Q : ℕ}
    (hQ : OracleComp.IsQueryBounded program Q) :
    (∑' k₁, seed₁ k₁ *
      ((OracleComp.interpret (memoize (fun _ : G × G => PMF.uniformOfFintype (G × G)))
        program).run []).toOuterMeasure {x | hasCollision (h₁ k₁) x.2 = true}) ≤
      Q.choose 2 * ε + Q.choose 2 * (Fintype.card G : ℝ≥0∞)⁻¹ := by
  classical
  set idealRun :=
    (OracleComp.interpret (memoize (fun _ : G × G => PMF.uniformOfFintype (G × G)))
      program).run []
  have hsplit (k₁ : K₁) :
      idealRun.toOuterMeasure {x | hasCollision (h₁ k₁) x.2 = true} ≤
        idealRun.toOuterMeasure {x | hasUCollision (h₁ k₁) x.2 = true} +
          idealRun.toOuterMeasure {x | hasVCollision x.2 = true} := by
    calc idealRun.toOuterMeasure {x | hasCollision (h₁ k₁) x.2 = true}
        ≤ idealRun.toOuterMeasure
          ({x | hasUCollision (h₁ k₁) x.2 = true} ∪ {x | hasVCollision x.2 = true}) := by
          refine idealRun.toOuterMeasure.mono fun x hx => ?_
          simp only [Set.mem_ofPred_eq, hasCollision_eq_or, Bool.or_eq_true] at hx
          exact hx
      _ ≤ _ := MeasureTheory.measure_union_le _ _
  have hu :
      (∑' k₁, seed₁ k₁ * idealRun.toOuterMeasure {x | hasUCollision (h₁ k₁) x.2 = true}) ≤
        Q.choose 2 * ε := by
    simp only [PMF.toOuterMeasure_apply]
    have hcomm :
        (∑' k₁, seed₁ k₁ * ∑' x,
          ({x : Bool × List ((G × G) × (G × G)) |
            hasUCollision (h₁ k₁) x.2 = true}.indicator idealRun x)) =
        ∑' x, idealRun x * ∑' k₁,
          ({k₁ : K₁ | hasUCollision (h₁ k₁) x.2 = true}.indicator seed₁ k₁) := by
      simp only [← ENNReal.tsum_mul_left]
      rw [tsum_comm]
      refine tsum_congr fun x => tsum_congr fun k₁ => ?_
      by_cases hx : hasUCollision (h₁ k₁) x.2 = true
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, mul_comm]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero, mul_zero]
    rw [hcomm]
    calc ∑' x, idealRun x * ∑' k₁,
          ({k₁ : K₁ | hasUCollision (h₁ k₁) x.2 = true}.indicator seed₁ k₁)
        ≤ ∑' x, idealRun x * (Q.choose 2 * ε) := by
          refine tsum_le_tsum fun x => ?_
          by_cases hmem : x ∈ idealRun.support
          · refine mul_le_mul_of_nonneg_left ?_ zero_le
            rw [← PMF.toOuterMeasure_apply]
            obtain ⟨hpair, hlen⟩ :=
              memoize_pairwise_and_length_le _ hQ List.Pairwise.nil hmem
            rw [List.length_nil, zero_add] at hlen
            exact (toOuterMeasure_hasUCollision_le hh₁ hpair).trans
              (mul_le_mul_of_nonneg_right
                (Nat.cast_le.mpr (Nat.choose_le_choose 2 hlen)) zero_le)
          · rw [(PMF.apply_eq_zero_iff _ _).mpr hmem, zero_mul, zero_mul]
      _ = Q.choose 2 * ε := by
          rw [ENNReal.tsum_mul_right, idealRun.tsum_coe, one_mul]
  have hv :
      (∑' k₁, seed₁ k₁ * idealRun.toOuterMeasure {x | hasVCollision x.2 = true}) ≤
        Q.choose 2 * (Fintype.card G : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.tsum_mul_right, seed₁.tsum_coe, one_mul]
    have hv0 := toOuterMeasure_hasVCollision_le hQ (qc := []) rfl
    simpa only [List.length_nil, mul_zero, zero_add] using hv0
  calc ∑' k₁, seed₁ k₁ * idealRun.toOuterMeasure {x | hasCollision (h₁ k₁) x.2 = true}
      ≤ ∑' k₁, seed₁ k₁ *
        (idealRun.toOuterMeasure {x | hasUCollision (h₁ k₁) x.2 = true} +
          idealRun.toOuterMeasure {x | hasVCollision x.2 = true}) :=
        tsum_le_tsum fun k₁ => mul_le_mul_of_nonneg_left (hsplit k₁) zero_le
    _ = (∑' k₁, seed₁ k₁ * idealRun.toOuterMeasure {x | hasUCollision (h₁ k₁) x.2 = true}) +
        (∑' k₁, seed₁ k₁ * idealRun.toOuterMeasure {x | hasVCollision x.2 = true}) := by
        simp only [mul_add, tsum_add]
    _ ≤ Q.choose 2 * ε + Q.choose 2 * (Fintype.card G : ℝ≥0∞)⁻¹ := add_le_add hu hv

/-- For every fixed `f₁`, the acceptance probability of `feistel3FixedGame f₁ program` and
`randomFunctionGame program` on outcome `b` differ by at most the collision probability. -/
private theorem feistel3FixedGame_apply_le (f₁ : G → G)
    (program : OracleComp (fun _ : G × G => G × G) Bool) (b : Bool) :
    feistel3FixedGame f₁ program b ≤
      randomFunctionGame program b +
        ((OracleComp.interpret (memoize (fun _ : G × G => PMF.uniformOfFintype (G × G)))
          program).run []).toOuterMeasure {x | hasCollision f₁ x.2 = true} := by
  have h := (identicalUntilBad_roundHandler f₁).bind_apply_le (dedup program) ([], false)
    (fun x => PMF.pure x.1.1) b
  rw [(identicalUntilBad_roundHandler f₁).bad_eq, toOuterMeasure_bad_idealRoundHandler] at h
  rw [feistel3FixedGame_eq_realRoundHandler, ← map_fst_run_idealRoundHandler f₁]
  exact h

private theorem randomFunctionGame_apply_le_feistel3FixedGame (f₁ : G → G)
    (program : OracleComp (fun _ : G × G => G × G) Bool) (b : Bool) :
    randomFunctionGame program b ≤
      feistel3FixedGame f₁ program b +
        ((OracleComp.interpret (memoize (fun _ : G × G => PMF.uniformOfFintype (G × G)))
          program).run []).toOuterMeasure {x | hasCollision f₁ x.2 = true} := by
  have h := (identicalUntilBad_roundHandler f₁).symm.bind_apply_le (dedup program) ([], false)
    (fun x => PMF.pure x.1.1) b
  rw [toOuterMeasure_bad_idealRoundHandler] at h
  rw [feistel3FixedGame_eq_realRoundHandler, ← map_fst_run_idealRoundHandler f₁]
  exact h

/-- **3-round Luby–Rackoff theorem in `ℝ≥0∞` (with Δ-universal Round 1)**: for any adaptive
program making at most `Q` queries, `feistel3HashIdealGame` accepts with probability at most
`randomFunctionGame` plus `Q.choose 2 * ε + Q.choose 2 * |G|⁻¹`. -/
theorem feistel3HashIdealGame_apply_le {seed₁ : PMF K₁} {h₁ : K₁ → G → G} {ε : ℝ≥0∞}
    (hh₁ : IsDeltaUniversalHash seed₁ h₁ ε)
    {program : OracleComp (fun _ : G × G => G × G) Bool} {Q : ℕ}
    (hQ : OracleComp.IsQueryBounded program Q) (b : Bool) :
    feistel3HashIdealGame seed₁ h₁ program b ≤
      randomFunctionGame program b +
        (Q.choose 2 * ε + Q.choose 2 * (Fintype.card G : ℝ≥0∞)⁻¹) := by
  rw [feistel3HashIdealGame, Probability.PMF.monad_bind_eq_bind, PMF.bind_apply]
  calc ∑' k₁, seed₁ k₁ * feistel3FixedGame (h₁ k₁) program b
      ≤ ∑' k₁, seed₁ k₁ * (randomFunctionGame program b +
          ((OracleComp.interpret (memoize (fun _ : G × G => PMF.uniformOfFintype (G × G)))
            program).run []).toOuterMeasure {x | hasCollision (h₁ k₁) x.2 = true}) :=
        tsum_le_tsum fun k₁ =>
          mul_le_mul_of_nonneg_left (feistel3FixedGame_apply_le (h₁ k₁) program b) zero_le
    _ = randomFunctionGame program b +
          ∑' k₁, seed₁ k₁ *
            ((OracleComp.interpret (memoize (fun _ : G × G => PMF.uniformOfFintype (G × G)))
              program).run []).toOuterMeasure {x | hasCollision (h₁ k₁) x.2 = true} := by
        simp only [mul_add, tsum_add, ENNReal.tsum_mul_right, seed₁.tsum_coe, one_mul]
    _ ≤ randomFunctionGame program b +
          (Q.choose 2 * ε + Q.choose 2 * (Fintype.card G : ℝ≥0∞)⁻¹) :=
        add_le_add le_rfl (tsum_seed_toOuterMeasure_hasCollision_le hh₁ hQ)

/-- Reverse inequality for the 3-round Luby–Rackoff bound with Δ-universal Round 1:
`randomFunctionGame` accept probability is bounded by `feistel3HashIdealGame` plus the collision
term. -/
theorem randomFunctionGame_apply_le_feistel3HashIdealGame {seed₁ : PMF K₁} {h₁ : K₁ → G → G}
    {ε : ℝ≥0∞} (hh₁ : IsDeltaUniversalHash seed₁ h₁ ε)
    {program : OracleComp (fun _ : G × G => G × G) Bool} {Q : ℕ}
    (hQ : OracleComp.IsQueryBounded program Q) (b : Bool) :
    randomFunctionGame program b ≤
      feistel3HashIdealGame seed₁ h₁ program b +
        (Q.choose 2 * ε + Q.choose 2 * (Fintype.card G : ℝ≥0∞)⁻¹) := by
  have h1 : randomFunctionGame program b = ∑' k₁, seed₁ k₁ * randomFunctionGame program b := by
    rw [ENNReal.tsum_mul_right, seed₁.tsum_coe, one_mul]
  rw [h1, feistel3HashIdealGame, Probability.PMF.monad_bind_eq_bind, PMF.bind_apply]
  calc ∑' k₁, seed₁ k₁ * randomFunctionGame program b
      ≤ ∑' k₁, seed₁ k₁ * (feistel3FixedGame (h₁ k₁) program b +
          ((OracleComp.interpret (memoize (fun _ : G × G => PMF.uniformOfFintype (G × G)))
            program).run []).toOuterMeasure {x | hasCollision (h₁ k₁) x.2 = true}) :=
        tsum_le_tsum fun k₁ =>
          mul_le_mul_of_nonneg_left
            (randomFunctionGame_apply_le_feistel3FixedGame (h₁ k₁) program b) zero_le
    _ = (∑' k₁, seed₁ k₁ * feistel3FixedGame (h₁ k₁) program b) +
          ∑' k₁, seed₁ k₁ *
            ((OracleComp.interpret (memoize (fun _ : G × G => PMF.uniformOfFintype (G × G)))
              program).run []).toOuterMeasure {x | hasCollision (h₁ k₁) x.2 = true} := by
        simp only [mul_add, tsum_add]
    _ ≤ (∑' k₁, seed₁ k₁ * feistel3FixedGame (h₁ k₁) program b) +
          (Q.choose 2 * ε + Q.choose 2 * (Fintype.card G : ℝ≥0∞)⁻¹) :=
        add_le_add le_rfl (tsum_seed_toOuterMeasure_hasCollision_le hh₁ hQ)

/-- **3-round Luby–Rackoff theorem with Δ-universal Round 1** ([BonehShoup2023], Section 4.5.1;
[LubyRackoff1988]): when Round 1 is drawn from an `ε`-almost-Δ-universal hash family and Rounds 2
and 3 are independent uniform random functions on `G`, any `Q`-query adaptive adversary has
distinguishing advantage against a uniform random function on `G × G` at most
`Q.choose 2 * ε.toReal + Q.choose 2 / |G|`. -/
theorem advantage_feistel3HashIdealGame_randomFunctionGame_le
    {seed₁ : PMF K₁} {h₁ : K₁ → G → G} {ε : ℝ≥0∞} (hh₁ : IsDeltaUniversalHash seed₁ h₁ ε)
    (hε : ε ≠ ⊤) {program : OracleComp (fun _ : G × G => G × G) Bool} {Q : ℕ}
    (hQ : OracleComp.IsQueryBounded program Q) :
    (Game.advantage (feistel3HashIdealGame seed₁ h₁ program)
      (randomFunctionGame program) : ℝ) ≤
      (Q.choose 2 : ℝ) * ε.toReal + (Q.choose 2 : ℝ) * (Fintype.card G : ℝ)⁻¹ := by
  have hcard : (Fintype.card G : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hinv_top : (Fintype.card G : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hcard
  have hB1 : (Q.choose 2 : ℝ≥0∞) * ε ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hε
  have hB2 : (Q.choose 2 : ℝ≥0∞) * (Fintype.card G : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hinv_top
  have hB : (Q.choose 2 : ℝ≥0∞) * ε + (Q.choose 2 : ℝ≥0∞) * (Fintype.card G : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hB1, hB2⟩
  have h := Game.advantage_le_of_apply_le hB
    (feistel3HashIdealGame_apply_le hh₁ hQ true)
    (randomFunctionGame_apply_le_feistel3HashIdealGame hh₁ hQ true)
  simpa only [ENNReal.toReal_add hB1 hB2, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_inv] using h

/-- **Classical 3-round Luby–Rackoff theorem** ([BonehShoup2023], Section 4.5, Theorem 4.9;
[LubyRackoff1988]):
three Feistel rounds with independent uniform random round functions on `G` are indistinguishable
from a uniform random function on `G × G` up to `2 * Q.choose 2 / |G| = Q * (Q - 1) / |G|` for any
`Q`-query adaptive adversary. -/
theorem advantage_feistel3RandomRoundsGame_randomFunctionGame_le
    {program : OracleComp (fun _ : G × G => G × G) Bool} {Q : ℕ}
    (hQ : OracleComp.IsQueryBounded program Q) :
    (Game.advantage (feistel3RandomRoundsGame program)
      (randomFunctionGame program) : ℝ) ≤
      2 * (Q.choose 2 : ℝ) * (Fintype.card G : ℝ)⁻¹ := by
  have hcard : (Fintype.card G : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hinv_top : (Fintype.card G : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hcard
  have h := advantage_feistel3HashIdealGame_randomFunctionGame_le
    (isDeltaUniversalHash_uniformOfFintype (X := G) (G := G)) hinv_top hQ
  simp only [feistel3HashIdealGame, id_eq, ENNReal.toReal_inv, ENNReal.toReal_natCast] at h
  change (Game.advantage (feistel3RandomRoundsGame program)
    (randomFunctionGame program) : ℝ) ≤ _ at h
  linarith [h]

omit [AddGroup G] in
/-- **PRP/PRF switching bound on `G × G`**: for any `Q`-query adaptive adversary, `idealPermGame`
and `randomFunctionGame` have distinguishing advantage at most `Q.choose 2 / |G| ^ 2`. -/
theorem advantage_idealPermGame_randomFunctionGame_le
    {program : OracleComp (fun _ : G × G => G × G) Bool} {Q : ℕ}
    (hQ : OracleComp.IsQueryBounded program Q) :
    (Game.advantage (idealPermGame program) (randomFunctionGame program) : ℝ) ≤
      (Q.choose 2 : ℝ) * ((Fintype.card G : ℝ)⁻¹) ^ 2 := by
  rw [Game.coe_advantage]
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal, idealPermGame,
    randomFunctionGame, Probability.PMF.monad_bind_eq_bind]
  have h := RandomPermutation.abs_sub_uniformPerm_uniformFunc_le hQ PMF.pure true
  simp only [Probability.PMF.monad_bind_eq_bind, PMF.bind_pure] at h
  refine h.trans_eq ?_
  rw [Fintype.card_prod, Nat.cast_mul, mul_inv, sq]

/-- **3-round Luby–Rackoff PRP bound with Δ-universal Round 1**: against a uniform random
permutation on `G × G` (`idealPermGame`), the distinguishing advantage of a `Q`-query adversary is
at most `Q.choose 2 * ε.toReal + Q.choose 2 / |G| + Q.choose 2 / |G| ^ 2`. -/
theorem advantage_feistel3HashIdealGame_idealPermGame_le
    {seed₁ : PMF K₁} {h₁ : K₁ → G → G} {ε : ℝ≥0∞} (hh₁ : IsDeltaUniversalHash seed₁ h₁ ε)
    (hε : ε ≠ ⊤) {program : OracleComp (fun _ : G × G => G × G) Bool} {Q : ℕ}
    (hQ : OracleComp.IsQueryBounded program Q) :
    (Game.advantage (feistel3HashIdealGame seed₁ h₁ program)
      (idealPermGame program) : ℝ) ≤
      (Q.choose 2 : ℝ) * ε.toReal + (Q.choose 2 : ℝ) * (Fintype.card G : ℝ)⁻¹ +
        (Q.choose 2 : ℝ) * ((Fintype.card G : ℝ)⁻¹) ^ 2 := by
  have htri :
      (Game.advantage (feistel3HashIdealGame seed₁ h₁ program) (idealPermGame program) : ℝ) ≤
        (Game.advantage (feistel3HashIdealGame seed₁ h₁ program)
          (randomFunctionGame program) : ℝ) +
        (Game.advantage (randomFunctionGame program) (idealPermGame program) : ℝ) := by
    exact_mod_cast Game.advantage_triangle
      (feistel3HashIdealGame seed₁ h₁ program) (randomFunctionGame program) (idealPermGame program)
  rw [Game.advantage_comm (randomFunctionGame program) (idealPermGame program)] at htri
  have h1 := advantage_feistel3HashIdealGame_randomFunctionGame_le hh₁ hε hQ
  have h2 := advantage_idealPermGame_randomFunctionGame_le hQ
  linarith

/-- **Classical 3-round Luby–Rackoff PRP bound**: three Feistel rounds with independent uniform
random round functions on `G` are indistinguishable from a uniform random permutation on `G × G`
(`idealPermGame`) up to `2 * Q.choose 2 / |G| + Q.choose 2 / |G| ^ 2`. -/
theorem advantage_feistel3RandomRoundsGame_idealPermGame_le
    {program : OracleComp (fun _ : G × G => G × G) Bool} {Q : ℕ}
    (hQ : OracleComp.IsQueryBounded program Q) :
    (Game.advantage (feistel3RandomRoundsGame program)
      (idealPermGame program) : ℝ) ≤
      2 * (Q.choose 2 : ℝ) * (Fintype.card G : ℝ)⁻¹ +
        (Q.choose 2 : ℝ) * ((Fintype.card G : ℝ)⁻¹) ^ 2 := by
  have htri :
      (Game.advantage (feistel3RandomRoundsGame program) (idealPermGame program) : ℝ) ≤
        (Game.advantage (feistel3RandomRoundsGame program) (randomFunctionGame program) : ℝ) +
        (Game.advantage (randomFunctionGame program) (idealPermGame program) : ℝ) := by
    exact_mod_cast Game.advantage_triangle
      (feistel3RandomRoundsGame program) (randomFunctionGame program) (idealPermGame program)
  rw [Game.advantage_comm (randomFunctionGame program) (idealPermGame program)] at htri
  have h1 := advantage_feistel3RandomRoundsGame_randomFunctionGame_le hQ
  have h2 := advantage_idealPermGame_randomFunctionGame_le hQ
  linarith

end LubyRackoff3

/-! ### 3-round PRF-to-Feistel hybrid reductions (Boneh–Shoup Theorem 4.9) -/

/-- A bound uniform in an independently sampled inner parameter survives averaging. -/
private theorem advantage_bind_right_le {α β γ : Type*}
    (p : PMF α) (q : PMF β) (d : PMF γ) (game₁ : α → γ → Game) (game₂ : β → γ → Game)
    {ε : ℝ} (h : ∀ c, (Game.advantage (p.bind (game₁ · c)) (q.bind (game₂ · c)) : ℝ) ≤ ε) :
    (Game.advantage (p.bind fun a => d.bind (game₁ a))
      (q.bind fun b => d.bind (game₂ b)) : ℝ) ≤ ε := by
  rw [PMF.bind_comm p d, PMF.bind_comm q d]
  exact Game.advantage_bind_le d _ _ h

section Hybrid3

variable {K K₁ G : Type} [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]

/-- Single-round PRF real game: sample `k ← keyGen` and answer queries with `F k`. -/
noncomputable def prfSingleRealGame (keyGen : PMF K) (F : K → G → G)
    (B : OracleComp (fun _ : G => G) Bool) : Game := do
  let k ← keyGen
  OracleComp.interpret (fun x => PMF.pure (F k x)) B

/-- Single-round PRF ideal game: sample a uniform random function `f : G → G`. -/
noncomputable def prfSingleIdealGame (B : OracleComp (fun _ : G => G) Bool) : Game := do
  let f ← PMF.uniformOfFintype (G → G)
  OracleComp.interpret (fun x => PMF.pure (f x)) B

/-- The 3-round Feistel game with three independent keyed round functions `F k₁, F k₂, F k₃`. -/
noncomputable def feistel3KeyedGame (keyGen : PMF K) (F : K → G → G)
    (program : OracleComp (fun _ : G × G => G × G) Bool) : Game := do
  let k₁ ← keyGen
  let k₂ ← keyGen
  let k₃ ← keyGen
  OracleComp.interpret (fun p => PMF.pure (feistel3 (F k₁) (F k₂) (F k₃) p)) program

/-- Intermediate hybrid 1: uniform random `f₁` in Round 1, keyed `F k₂, F k₃` in Rounds 2 and 3. -/
private noncomputable def feistel3Hybrid₁ (keyGen : PMF K) (F : K → G → G)
    (program : OracleComp (fun _ : G × G => G × G) Bool) : Game := do
  let f₁ ← PMF.uniformOfFintype (G → G)
  let k₂ ← keyGen
  let k₃ ← keyGen
  OracleComp.interpret (fun p => PMF.pure (feistel3 f₁ (F k₂) (F k₃) p)) program

/-- Intermediate hybrid 2: uniform random `f₁, f₂` in Rounds 1 and 2, keyed `F k₃` in Round 3. -/
private noncomputable def feistel3Hybrid₂ (keyGen : PMF K) (F : K → G → G)
    (program : OracleComp (fun _ : G × G => G × G) Bool) : Game := do
  let f₁ ← PMF.uniformOfFintype (G → G)
  let f₂ ← PMF.uniformOfFintype (G → G)
  let k₃ ← keyGen
  OracleComp.interpret (fun p => PMF.pure (feistel3 f₁ f₂ (F k₃) p)) program

/-- Round-1 PRF reduction distinguisher for fixed `f₂, f₃ : G → G`. -/
def feistel3Reduction₁ (f₂ f₃ : G → G)
    (program : OracleComp (fun _ : G × G => G × G) Bool) :
    OracleComp (fun _ : G => G) Bool :=
  OracleComp.interpret
    (fun p => do
      let y₁ ← OracleComp.query (spec := fun _ : G => G) p.2
      let u := p.1 + y₁
      let v := p.2 + f₂ u
      return (v, u + f₃ v))
    program

/-- Round-2 PRF reduction distinguisher for fixed `f₁, f₃ : G → G`. -/
def feistel3Reduction₂ (f₁ f₃ : G → G)
    (program : OracleComp (fun _ : G × G => G × G) Bool) :
    OracleComp (fun _ : G => G) Bool :=
  OracleComp.interpret
    (fun p => do
      let u := p.1 + f₁ p.2
      let y₂ ← OracleComp.query (spec := fun _ : G => G) u
      let v := p.2 + y₂
      return (v, u + f₃ v))
    program

/-- Round-3 PRF reduction distinguisher for fixed `f₁, f₂ : G → G`. -/
def feistel3Reduction₃ (f₁ f₂ : G → G)
    (program : OracleComp (fun _ : G × G => G × G) Bool) :
    OracleComp (fun _ : G => G) Bool :=
  OracleComp.interpret
    (fun p => do
      let u := p.1 + f₁ p.2
      let v := p.2 + f₂ u
      let y₃ ← OracleComp.query (spec := fun _ : G => G) v
      return (v, u + y₃))
    program

omit [Fintype G] [DecidableEq G] [Nonempty G] in
private theorem interpret_feistel3Reduction₁ (f₁ f₂ f₃ : G → G)
    (program : OracleComp (fun _ : G × G => G × G) Bool) :
    OracleComp.interpret (fun x => PMF.pure (f₁ x)) (feistel3Reduction₁ f₂ f₃ program) =
      OracleComp.interpret (fun p => PMF.pure (feistel3 f₁ f₂ f₃ p)) program := by
  rw [feistel3Reduction₁, OracleComp.interpret_interpret]
  congr 1
  funext p
  simp [feistel3_apply]

omit [Fintype G] [DecidableEq G] [Nonempty G] in
private theorem interpret_feistel3Reduction₂ (f₁ f₂ f₃ : G → G)
    (program : OracleComp (fun _ : G × G => G × G) Bool) :
    OracleComp.interpret (fun x => PMF.pure (f₂ x)) (feistel3Reduction₂ f₁ f₃ program) =
      OracleComp.interpret (fun p => PMF.pure (feistel3 f₁ f₂ f₃ p)) program := by
  rw [feistel3Reduction₂, OracleComp.interpret_interpret]
  congr 1
  funext p
  simp [feistel3_apply]

omit [Fintype G] [DecidableEq G] [Nonempty G] in
private theorem interpret_feistel3Reduction₃ (f₁ f₂ f₃ : G → G)
    (program : OracleComp (fun _ : G × G => G × G) Bool) :
    OracleComp.interpret (fun x => PMF.pure (f₃ x)) (feistel3Reduction₃ f₁ f₂ program) =
      OracleComp.interpret (fun p => PMF.pure (feistel3 f₁ f₂ f₃ p)) program := by
  rw [feistel3Reduction₃, OracleComp.interpret_interpret]
  congr 1
  funext p
  simp [feistel3_apply]

/-- Replacing the three keyed round functions `F k₁, F k₂, F k₃` with independent uniform random
round functions adds at most the sum of the three single-round PRF advantages. -/
theorem advantage_feistel3KeyedGame_feistel3RandomRoundsGame_le
    {keyGen : PMF K} {F : K → G → G}
    {program : OracleComp (fun _ : G × G => G × G) Bool} {ε₁ ε₂ ε₃ : ℝ}
    (h₁ : ∀ f₂ f₃,
      (Game.advantage (prfSingleRealGame keyGen F (feistel3Reduction₁ f₂ f₃ program))
        (prfSingleIdealGame (feistel3Reduction₁ f₂ f₃ program)) : ℝ) ≤ ε₁)
    (h₂ : ∀ f₁ f₃,
      (Game.advantage (prfSingleRealGame keyGen F (feistel3Reduction₂ f₁ f₃ program))
        (prfSingleIdealGame (feistel3Reduction₂ f₁ f₃ program)) : ℝ) ≤ ε₂)
    (h₃ : ∀ f₁ f₂,
      (Game.advantage (prfSingleRealGame keyGen F (feistel3Reduction₃ f₁ f₂ program))
        (prfSingleIdealGame (feistel3Reduction₃ f₁ f₂ program)) : ℝ) ≤ ε₃) :
    (Game.advantage (feistel3KeyedGame keyGen F program)
      (feistel3RandomRoundsGame program) : ℝ) ≤ ε₁ + ε₂ + ε₃ := by
  have hhop1 :
      (Game.advantage (feistel3KeyedGame keyGen F program)
        (feistel3Hybrid₁ keyGen F program) : ℝ) ≤ ε₁ := by
    simp only [feistel3KeyedGame, feistel3Hybrid₁, Probability.PMF.monad_bind_eq_bind]
    refine advantage_bind_right_le _ _ _ _ _ fun k₂ =>
      advantage_bind_right_le _ _ _ _ _ fun k₃ => ?_
    simpa only [prfSingleRealGame, prfSingleIdealGame, interpret_feistel3Reduction₁,
      Probability.PMF.monad_bind_eq_bind] using h₁ (F k₂) (F k₃)
  have hhop2 :
      (Game.advantage (feistel3Hybrid₁ keyGen F program)
        (feistel3Hybrid₂ keyGen F program) : ℝ) ≤ ε₂ := by
    simp only [feistel3Hybrid₁, feistel3Hybrid₂, Probability.PMF.monad_bind_eq_bind]
    refine Game.advantage_bind_le _ _ _ fun f₁ =>
      advantage_bind_right_le _ _ _ _ _ fun k₃ => ?_
    simpa only [prfSingleRealGame, prfSingleIdealGame, interpret_feistel3Reduction₂,
      Probability.PMF.monad_bind_eq_bind] using h₂ f₁ (F k₃)
  have hhop3 :
      (Game.advantage (feistel3Hybrid₂ keyGen F program)
        (feistel3RandomRoundsGame program) : ℝ) ≤ ε₃ := by
    simp only [feistel3Hybrid₂, feistel3RandomRoundsGame, feistel3FixedGame,
      Probability.PMF.monad_bind_eq_bind]
    refine Game.advantage_bind_le _ _ _ fun f₁ =>
      Game.advantage_bind_le _ _ _ fun f₂ => ?_
    simpa only [prfSingleRealGame, prfSingleIdealGame, interpret_feistel3Reduction₃,
      Probability.PMF.monad_bind_eq_bind] using h₃ f₁ f₂
  have htri1 := NNReal.coe_le_coe.mpr (Game.advantage_triangle
    (feistel3KeyedGame keyGen F program) (feistel3Hybrid₁ keyGen F program)
    (feistel3RandomRoundsGame program))
  have htri2 := NNReal.coe_le_coe.mpr (Game.advantage_triangle
    (feistel3Hybrid₁ keyGen F program) (feistel3Hybrid₂ keyGen F program)
    (feistel3RandomRoundsGame program))
  simp only [NNReal.coe_add] at htri1 htri2
  linarith

/-- **The Luby–Rackoff theorem** ([BonehShoup2023], Section 4.5, Theorem 4.9; [LubyRackoff1988]): a
3-round Feistel cipher built from three independently keyed instances of a round function `F` has
distinguishing advantage against a uniform random function on `G × G` at most
`ε₁ + ε₂ + ε₃ + 2 * Q.choose 2 / |G|`. -/
theorem advantage_feistel3KeyedGame_randomFunctionGame_le
    {keyGen : PMF K} {F : K → G → G}
    {program : OracleComp (fun _ : G × G => G × G) Bool} {Q : ℕ}
    (hQ : OracleComp.IsQueryBounded program Q) {ε₁ ε₂ ε₃ : ℝ}
    (h₁ : ∀ f₂ f₃,
      (Game.advantage (prfSingleRealGame keyGen F (feistel3Reduction₁ f₂ f₃ program))
        (prfSingleIdealGame (feistel3Reduction₁ f₂ f₃ program)) : ℝ) ≤ ε₁)
    (h₂ : ∀ f₁ f₃,
      (Game.advantage (prfSingleRealGame keyGen F (feistel3Reduction₂ f₁ f₃ program))
        (prfSingleIdealGame (feistel3Reduction₂ f₁ f₃ program)) : ℝ) ≤ ε₂)
    (h₃ : ∀ f₁ f₂,
      (Game.advantage (prfSingleRealGame keyGen F (feistel3Reduction₃ f₁ f₂ program))
        (prfSingleIdealGame (feistel3Reduction₃ f₁ f₂ program)) : ℝ) ≤ ε₃) :
    (Game.advantage (feistel3KeyedGame keyGen F program)
      (randomFunctionGame program) : ℝ) ≤
      ε₁ + ε₂ + ε₃ + 2 * (Q.choose 2 : ℝ) * (Fintype.card G : ℝ)⁻¹ := by
  have htri := NNReal.coe_le_coe.mpr (Game.advantage_triangle
    (feistel3KeyedGame keyGen F program) (feistel3RandomRoundsGame program)
    (randomFunctionGame program))
  simp only [NNReal.coe_add] at htri
  linarith [advantage_feistel3KeyedGame_feistel3RandomRoundsGame_le h₁ h₂ h₃,
    advantage_feistel3RandomRoundsGame_randomFunctionGame_le hQ]

/-- **The Luby–Rackoff PRP theorem** ([BonehShoup2023], Section 4.5, Theorem 4.9;
[LubyRackoff1988]): a 3-round
Feistel cipher built from three independently keyed instances of a round function `F` has
distinguishing advantage against a uniform random permutation on `G × G` (`idealPermGame`) at most
`ε₁ + ε₂ + ε₃ + 2 * Q.choose 2 / |G| + Q.choose 2 / |G| ^ 2`. -/
theorem advantage_feistel3KeyedGame_idealPermGame_le
    {keyGen : PMF K} {F : K → G → G}
    {program : OracleComp (fun _ : G × G => G × G) Bool} {Q : ℕ}
    (hQ : OracleComp.IsQueryBounded program Q) {ε₁ ε₂ ε₃ : ℝ}
    (h₁ : ∀ f₂ f₃,
      (Game.advantage (prfSingleRealGame keyGen F (feistel3Reduction₁ f₂ f₃ program))
        (prfSingleIdealGame (feistel3Reduction₁ f₂ f₃ program)) : ℝ) ≤ ε₁)
    (h₂ : ∀ f₁ f₃,
      (Game.advantage (prfSingleRealGame keyGen F (feistel3Reduction₂ f₁ f₃ program))
        (prfSingleIdealGame (feistel3Reduction₂ f₁ f₃ program)) : ℝ) ≤ ε₂)
    (h₃ : ∀ f₁ f₂,
      (Game.advantage (prfSingleRealGame keyGen F (feistel3Reduction₃ f₁ f₂ program))
        (prfSingleIdealGame (feistel3Reduction₃ f₁ f₂ program)) : ℝ) ≤ ε₃) :
    (Game.advantage (feistel3KeyedGame keyGen F program)
      (idealPermGame program) : ℝ) ≤
      ε₁ + ε₂ + ε₃ + 2 * (Q.choose 2 : ℝ) * (Fintype.card G : ℝ)⁻¹ +
        (Q.choose 2 : ℝ) * ((Fintype.card G : ℝ)⁻¹) ^ 2 := by
  have htri := NNReal.coe_le_coe.mpr (Game.advantage_triangle
    (feistel3KeyedGame keyGen F program) (feistel3RandomRoundsGame program)
    (idealPermGame program))
  simp only [NNReal.coe_add] at htri
  linarith [advantage_feistel3KeyedGame_feistel3RandomRoundsGame_le h₁ h₂ h₃,
    advantage_feistel3RandomRoundsGame_idealPermGame_le hQ]

/-- Concrete instantiation of the 3-round Luby–Rackoff theorem on `BitString n` (block size `2n`):
the information-theoretic collision error is at most `2 * Q.choose 2 / 2 ^ n`. -/
theorem advantage_feistel3RandomRoundsGame_bitString_le (n : ℕ)
    {program : OracleComp (fun _ : BitString n × BitString n => BitString n × BitString n) Bool}
    {Q : ℕ} (hQ : OracleComp.IsQueryBounded program Q) :
    (Game.advantage (feistel3RandomRoundsGame program)
      (randomFunctionGame program) : ℝ) ≤
      2 * (Q.choose 2 : ℝ) * ((2 : ℝ) ^ n)⁻¹ := by
  have h := advantage_feistel3RandomRoundsGame_randomFunctionGame_le hQ
  simpa only [Fintype.card_pi, Fintype.card_fin, Fintype.card_bool, Finset.prod_const,
    Finset.card_univ, Nat.cast_pow, Nat.cast_ofNat] using h

end Hybrid3

/-! ### Chosen-ciphertext separation for 3 rounds and 4-round bidirectional hybrid security -/

section Strong4AndCCAAttack

variable {K G : Type} [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]

/-- Bidirectional permutation oracle on `G × G`: `(false, p)` evaluates forward encryption `π p`,
and `(true, q)` evaluates inverse decryption `π.symm q`. -/
noncomputable def feistelStrongOracle (π : G × G ≃ G × G) :
    (q : Bool × (G × G)) → PMF (G × G)
  | (false, p) => PMF.pure (π p)
  | (true, q) => PMF.pure (π.symm q)

/-- Ideal bidirectional random-permutation game on `G × G`: sample a uniform permutation
`π ← PMF.uniformOfFintype (Equiv.Perm (G × G))` and answer forward and inverse queries via
`feistelStrongOracle π`. -/
noncomputable def idealStrongGame
    (program : OracleComp (fun _ : Bool × (G × G) => G × G) Bool) : Game := do
  let π ← PMF.uniformOfFintype (Equiv.Perm (G × G))
  OracleComp.interpret (feistelStrongOracle π) program

/-- Bidirectional independent-table game on `Bool × (G × G) → G × G`, where forward and inverse
queries are answered by two independent uniform random functions. -/
noncomputable def independentTableStrongGame
    (program : OracleComp (fun _ : Bool × (G × G) => G × G) Bool) : Game := do
  let table ← PMF.uniformOfFintype (Bool × (G × G) → G × G)
  OracleComp.interpret (fun q => PMF.pure (table q)) program

/-- **The 3-query chosen-ciphertext distinguisher against 3-round Feistel** ([BonehShoup2023],
Exercise 4.15(b)):
1. Query encryption at `(l₀, r₀)` to obtain `(v₀, w₀)`.
2. Query encryption at `(l₁, r₀)` to obtain `(v₁, w₁)`.
3. Query decryption at `(v₀, (l₁ - l₀) + w₀)` to obtain `(l₂, r₂)`.
4. Accept iff `-v₀ + r₂ = -v₁ + r₀`. -/
def feistel3CCAAttack (l₀ l₁ r₀ : G) :
    OracleComp (fun _ : Bool × (G × G) => G × G) Bool := do
  let vw₀ ← OracleComp.query (spec := fun _ : Bool × (G × G) => G × G) (false, (l₀, r₀))
  let vw₁ ← OracleComp.query (spec := fun _ : Bool × (G × G) => G × G) (false, (l₁, r₀))
  let lr₂ ← OracleComp.query (spec := fun _ : Bool × (G × G) => G × G)
    (true, (vw₀.1, (l₁ - l₀) + vw₀.2))
  return decide (-vw₀.1 + lr₂.2 = -vw₁.1 + r₀)

omit [Fintype G] [Nonempty G] in
/-- `feistel3CCAAttack` makes at most 3 oracle queries. -/
theorem isQueryBounded_feistel3CCAAttack (l₀ l₁ r₀ : G) :
    OracleComp.IsQueryBounded (feistel3CCAAttack l₀ l₁ r₀) 3 := by
  refine ((OracleComp.IsCostBounded.query (false, (l₀, r₀))).bind fun vw₀ =>
    ((OracleComp.IsCostBounded.query (false, (l₁, r₀))).bind fun vw₁ =>
      (OracleComp.IsCostBounded.query (true, (vw₀.1, (l₁ - l₀) + vw₀.2))).bind fun lr₂ =>
        OracleComp.IsCostBounded.pure _ 0)).mono (by omega)

omit [Fintype G] [Nonempty G] in
/-- **Every 3-round Feistel network `feistel3 f₁ f₂ f₃` is accepted with probability `1` by
`feistel3CCAAttack`** ([BonehShoup2023], Exercise 4.15(b)), for any round functions `f₁, f₂, f₃`
and any `l₀, l₁, r₀ : G`. -/
theorem eval_feistel3_feistel3CCAAttack (f₁ f₂ f₃ : G → G) (l₀ l₁ r₀ : G) :
    OracleComp.interpret (feistelStrongOracle (feistel3 f₁ f₂ f₃))
      (feistel3CCAAttack l₀ l₁ r₀) = PMF.pure true := by
  simp only [feistel3CCAAttack, feistelStrongOracle, feistel3_apply, feistel3_symm_apply,
    OracleComp.interpret_bind, OracleComp.interpret_query, OracleComp.interpret_pure,
    Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure, PMF.pure_bind]
  have h1 :
      (l₁ - l₀ + (l₀ + f₁ r₀ + f₃ (r₀ + f₂ (l₀ + f₁ r₀)))) - f₃ (r₀ + f₂ (l₀ + f₁ r₀)) =
        l₁ + f₁ r₀ := by
    rw [← add_assoc (l₁ - l₀), add_sub_cancel_right, ← add_assoc, sub_add_cancel]
  have h2 :
      -(r₀ + f₂ (l₀ + f₁ r₀)) +
        ((r₀ + f₂ (l₀ + f₁ r₀)) - f₂ (l₁ + f₁ r₀)) =
      -(r₀ + f₂ (l₁ + f₁ r₀)) + r₀ := by
    rw [sub_eq_add_neg, neg_add_cancel_left, neg_add_rev, neg_add_cancel_right]
  rw [h1, decide_eq_true h2]

omit [Fintype G] [Nonempty G] in
/-- When `l₀ = l₁`, the third query of `feistel3CCAAttack l₀ l₀ r₀` asks to invert the first
ciphertext, so *every* bidirectional permutation `π : G × G ≃ G × G` is accepted with probability
`1`. -/
theorem eval_feistelStrongOracle_feistel3CCAAttack_self (π : G × G ≃ G × G) (l₀ r₀ : G) :
    OracleComp.interpret (feistelStrongOracle π) (feistel3CCAAttack l₀ l₀ r₀) =
      PMF.pure true := by
  simp only [feistel3CCAAttack, feistelStrongOracle, sub_self, zero_add, Prod.mk.eta,
    Equiv.symm_apply_apply, decide_true, OracleComp.interpret_bind, OracleComp.interpret_query,
    OracleComp.interpret_pure, Probability.PMF.monad_bind_eq_bind,
    Probability.PMF.monad_pure_eq_pure, PMF.pure_bind]

omit [Nonempty G] in
/-- At `l₀ = l₁`, the permutation-ideal game `idealStrongGame` accepts `feistel3CCAAttack l₀ l₀ r₀`
with probability `1`. -/
theorem idealStrongGame_feistel3CCAAttack_self (l₀ r₀ : G) :
    idealStrongGame (feistel3CCAAttack l₀ l₀ r₀) = PMF.pure true := by
  simp only [idealStrongGame, Probability.PMF.monad_bind_eq_bind,
    eval_feistelStrongOracle_feistel3CCAAttack_self, PMF.bind_const]

omit [Nonempty G] in
/-- At `l₀ = l₁`, `feistel3CCAAttack l₀ l₀ r₀` has zero advantage between any 3-round Feistel
network and the true bidirectional random-permutation game `idealStrongGame`. -/
theorem advantage_feistel3CCAAttack_self (f₁ f₂ f₃ : G → G) (l₀ r₀ : G) :
    Game.advantage
      (OracleComp.interpret (feistelStrongOracle (feistel3 f₁ f₂ f₃))
        (feistel3CCAAttack l₀ l₀ r₀))
      (idealStrongGame (feistel3CCAAttack l₀ l₀ r₀)) = 0 := by
  rw [eval_feistel3_feistel3CCAAttack, idealStrongGame_feistel3CCAAttack_self, Game.advantage_self]

omit [Fintype G] [Nonempty G] in
/-- When `l₀, l₁, l₂ : G` are pairwise distinct (`|G| ≥ 3`), the transposition
`Equiv.swap (l₀, (l₁ - l₀) + r₀) (l₂, r₀)` fixes `(l₀, r₀)` and `(l₁, r₀)` while mapping
`(l₀, (l₁ - l₀) + r₀)` to `(l₂, r₀)`, so `feistel3CCAAttack l₀ l₁ r₀` rejects it with probability
`1`. -/
theorem eval_feistelStrongOracle_swap_feistel3CCAAttack_eq_false {l₀ l₁ l₂ r₀ : G}
    (h01 : l₀ ≠ l₁) (h02 : l₀ ≠ l₂) (h12 : l₁ ≠ l₂) :
    OracleComp.interpret
      (feistelStrongOracle (Equiv.swap (l₀, (l₁ - l₀) + r₀) (l₂, r₀)))
      (feistel3CCAAttack l₀ l₁ r₀) = PMF.pure false := by
  have hA1 : (l₀, r₀) ≠ (l₀, (l₁ - l₀) + r₀) := fun h =>
    h01 (sub_eq_zero.mp (add_right_cancel ((zero_add r₀).trans (congrArg Prod.snd h))).symm).symm
  have hA2 : (l₀, r₀) ≠ (l₂, r₀) := fun h => h02 (congrArg Prod.fst h)
  have hB1 : (l₁, r₀) ≠ (l₀, (l₁ - l₀) + r₀) := fun h => h01 (congrArg Prod.fst h).symm
  have hB2 : (l₁, r₀) ≠ (l₂, r₀) := fun h => h12 (congrArg Prod.fst h)
  have hne : -l₀ + r₀ ≠ -l₁ + r₀ := fun h =>
    h01 (neg_inj.mp (add_right_cancel h))
  simp only [feistel3CCAAttack, feistelStrongOracle, Equiv.symm_swap,
    OracleComp.interpret_bind, OracleComp.interpret_query, OracleComp.interpret_pure,
    Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure, PMF.pure_bind,
    Equiv.swap_apply_of_ne_of_ne hA1 hA2, Equiv.swap_apply_of_ne_of_ne hB1 hB2,
    Equiv.swap_apply_left, decide_eq_false hne]

omit [Nonempty G] in
/-- When `l₀, l₁, l₂ : G` are pairwise distinct, `idealStrongGame (feistel3CCAAttack l₀ l₁ r₀)`
rejects (`false`) with probability at least `|Equiv.Perm (G × G)|⁻¹`. -/
theorem le_idealStrongGame_feistel3CCAAttack_false {l₀ l₁ l₂ r₀ : G}
    (h01 : l₀ ≠ l₁) (h02 : l₀ ≠ l₂) (h12 : l₁ ≠ l₂) :
    (Fintype.card (Equiv.Perm (G × G)) : ℝ≥0∞)⁻¹ ≤
      idealStrongGame (feistel3CCAAttack l₀ l₁ r₀) false := by
  let π₀ : Equiv.Perm (G × G) := Equiv.swap (l₀, (l₁ - l₀) + r₀) (l₂, r₀)
  rw [idealStrongGame, Probability.PMF.monad_bind_eq_bind, PMF.bind_apply]
  calc (Fintype.card (Equiv.Perm (G × G)) : ℝ≥0∞)⁻¹
      = PMF.uniformOfFintype (Equiv.Perm (G × G)) π₀ *
          OracleComp.interpret (feistelStrongOracle π₀) (feistel3CCAAttack l₀ l₁ r₀) false := by
        rw [PMF.uniformOfFintype_apply,
          eval_feistelStrongOracle_swap_feistel3CCAAttack_eq_false h01 h02 h12,
          PMF.pure_apply_self, mul_one]
    _ ≤ ∑' π : Equiv.Perm (G × G),
          PMF.uniformOfFintype (Equiv.Perm (G × G)) π *
            OracleComp.interpret (feistelStrongOracle π) (feistel3CCAAttack l₀ l₁ r₀) false :=
        le_tsum (f := fun π : Equiv.Perm (G × G) =>
          PMF.uniformOfFintype (Equiv.Perm (G × G)) π *
            OracleComp.interpret (feistelStrongOracle π) (feistel3CCAAttack l₀ l₁ r₀) false) π₀

omit [Nonempty G] in
/-- When `l₀, l₁, l₂ : G` are pairwise distinct (`|G| ≥ 3`), `feistel3CCAAttack l₀ l₁ r₀`
distinguishes any 3-round Feistel network from the true bidirectional random-permutation game
`idealStrongGame` with advantage at least `|Equiv.Perm (G × G)|⁻¹`. -/
theorem le_advantage_feistel3CCAAttack_idealStrongGame (f₁ f₂ f₃ : G → G) {l₀ l₁ l₂ r₀ : G}
    (h01 : l₀ ≠ l₁) (h02 : l₀ ≠ l₂) (h12 : l₁ ≠ l₂) :
    (Fintype.card (Equiv.Perm (G × G)) : ℝ)⁻¹ ≤
      (Game.advantage
        (OracleComp.interpret (feistelStrongOracle (feistel3 f₁ f₂ f₃))
          (feistel3CCAAttack l₀ l₁ r₀))
        (idealStrongGame (feistel3CCAAttack l₀ l₁ r₀)) : ℝ) := by
  set g := idealStrongGame (feistel3CCAAttack l₀ l₁ r₀)
  have hfail := ENNReal.toReal_mono (PMF.apply_ne_top g false)
    (le_idealStrongGame_feistel3CCAAttack_false h01 h02 h12)
  rw [ENNReal.toReal_inv, ENNReal.toReal_natCast] at hfail
  have hsum := congrArg (fun x : ℝ≥0 => (x : ℝ)) g.succProbability_add_failProbability
  simp only [NNReal.coe_add, NNReal.coe_one, Game.succProbability, Game.failProbability,
    ENNReal.coe_toNNReal_eq_toReal] at hsum
  rw [Game.coe_advantage, eval_feistel3_feistel3CCAAttack]
  simp only [Game.coe_succProbability, PMF.pure_apply_self, ENNReal.toReal_one]
  have hnonneg : 0 ≤ (g false).toReal := ENNReal.toReal_nonneg
  rw [abs_of_nonneg (by linarith)]
  linarith

omit [Nonempty G] in
/-- When `l₀, l₁, l₂ : G` are pairwise distinct (`|G| ≥ 3`), `feistel3CCAAttack l₀ l₁ r₀` has
strictly positive distinguishing advantage against the true bidirectional random-permutation game
`idealStrongGame`. -/
theorem advantage_feistel3CCAAttack_idealStrongGame_pos (f₁ f₂ f₃ : G → G) {l₀ l₁ l₂ r₀ : G}
    (h01 : l₀ ≠ l₁) (h02 : l₀ ≠ l₂) (h12 : l₁ ≠ l₂) :
    0 < (Game.advantage
      (OracleComp.interpret (feistelStrongOracle (feistel3 f₁ f₂ f₃))
        (feistel3CCAAttack l₀ l₁ r₀))
      (idealStrongGame (feistel3CCAAttack l₀ l₁ r₀)) : ℝ) := by
  have hpos : (0 : ℝ) < (Fintype.card (Equiv.Perm (G × G)) : ℝ)⁻¹ :=
    inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
  exact hpos.trans_le (le_advantage_feistel3CCAAttack_idealStrongGame f₁ f₂ f₃ h01 h02 h12)

/-- Against the independent-table game `independentTableStrongGame`, `feistel3CCAAttack l₀ l₁ r₀`
accepts with probability `|G|⁻¹`. -/
theorem eval_independentTableStrongGame_feistel3CCAAttack (l₀ l₁ r₀ : G) :
    independentTableStrongGame (feistel3CCAAttack l₀ l₁ r₀) true =
      (Fintype.card G : ℝ≥0∞)⁻¹ := by
  have hprod :
      PMF.uniformOfFintype (Bool × (G × G) → G × G) =
        (PMF.uniformOfFintype (G × G → G × G)).bind fun encTable =>
          (PMF.uniformOfFintype (G × G → G × G)).map fun decTable =>
            splitBoolTable.symm (encTable, decTable) := by
    rw [← Probability.PMF.uniformOfFintype_map_equiv splitBoolTable.symm,
      ← Probability.PMF.uniformOfFintype_prod, PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def]
  have hsplit :
      independentTableStrongGame (feistel3CCAAttack l₀ l₁ r₀) =
        (PMF.uniformOfFintype (G × G → G × G)).bind fun encTable =>
          (PMF.uniformOfFintype (G × G → G × G)).bind fun decTable =>
            let vw₀ := encTable (l₀, r₀)
            let vw₁ := encTable (l₁, r₀)
            let lr₂ := decTable (vw₀.1, (l₁ - l₀) + vw₀.2)
            PMF.pure (decide (-vw₀.1 + lr₂.2 = -vw₁.1 + r₀)) := by
    rw [independentTableStrongGame, Probability.PMF.monad_bind_eq_bind, hprod]
    simp only [feistel3CCAAttack, splitBoolTable, Equiv.coe_fn_symm_mk,
      OracleComp.interpret_bind, OracleComp.interpret_query, OracleComp.interpret_pure,
      Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
      PMF.bind_map, PMF.bind_bind, PMF.pure_bind, Function.comp_def,
      Bool.cond_false, Bool.cond_true]
  rw [hsplit]
  have hinner (encTable : G × G → G × G) :
      ((PMF.uniformOfFintype (G × G → G × G)).bind fun decTable =>
        let vw₀ := encTable (l₀, r₀)
        let vw₁ := encTable (l₁, r₀)
        let lr₂ := decTable (vw₀.1, (l₁ - l₀) + vw₀.2)
        PMF.pure (decide (-vw₀.1 + lr₂.2 = -vw₁.1 + r₀))) =
      (PMF.uniformOfFintype G).map fun y =>
        decide (y = -(encTable (l₁, r₀)).1 + r₀) := by
    set vw₀ := encTable (l₀, r₀)
    set vw₁ := encTable (l₁, r₀)
    set q₃ := (vw₀.1, (l₁ - l₀) + vw₀.2)
    have heval :
        (PMF.uniformOfFintype (G × G → G × G)).map (fun decTable => decTable q₃) =
          PMF.uniformOfFintype (G × G) := by
      rw [← Probability.PMF.pi_uniformOfFintype, Probability.PMF.pi_map_eval]
    have hsnd :
        (PMF.uniformOfFintype (G × G)).map Prod.snd = PMF.uniformOfFintype G := by
      rw [← Probability.PMF.uniformOfFintype_map_equiv (Equiv.prodComm G G), PMF.map_comp]
      exact Probability.PMF.uniformOfFintype_prod_map_fst
    have hshift :
        (PMF.uniformOfFintype G).map (Equiv.addLeft (-vw₀.1)) = PMF.uniformOfFintype G :=
      Probability.PMF.uniformOfFintype_map_equiv (Equiv.addLeft (-vw₀.1))
    calc ((PMF.uniformOfFintype (G × G → G × G)).bind fun decTable =>
          PMF.pure (decide (-vw₀.1 + (decTable q₃).2 = -vw₁.1 + r₀)))
        = (PMF.uniformOfFintype (G × G → G × G)).map
            (fun decTable => decide (-vw₀.1 + (decTable q₃).2 = -vw₁.1 + r₀)) := rfl
      _ = (((PMF.uniformOfFintype (G × G → G × G)).map (fun decTable => decTable q₃)).map
            Prod.snd).map (fun r₂ => decide (-vw₀.1 + r₂ = -vw₁.1 + r₀)) := by
          simp [PMF.map_comp, Function.comp_def]
      _ = ((PMF.uniformOfFintype G).map (Equiv.addLeft (-vw₀.1))).map
          (fun y => decide (y = -vw₁.1 + r₀)) := by
          rw [heval, hsnd, PMF.map_comp]
          rfl
      _ = (PMF.uniformOfFintype G).map (fun y => decide (y = -vw₁.1 + r₀)) := by
          rw [hshift]
  have hprob (t : G) :
      ((PMF.uniformOfFintype G).map (fun y => decide (y = t))) true =
        (Fintype.card G : ℝ≥0∞)⁻¹ := by
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    have hpre : (fun y : G => decide (y = t)) ⁻¹' {true} = {t} := by
      ext y
      simp
    rw [hpre, PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply]
  rw [PMF.bind_apply]
  simp only [hinner, hprob, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- The 3-query CCA attack `feistel3CCAAttack` distinguishes any 3-round Feistel network from
the independent-table game `independentTableStrongGame` with exact advantage `1 - |G|⁻¹`. -/
theorem advantage_feistel3CCAAttack_independentTable (f₁ f₂ f₃ : G → G) (l₀ l₁ r₀ : G) :
    (Game.advantage
      (OracleComp.interpret (feistelStrongOracle (feistel3 f₁ f₂ f₃))
        (feistel3CCAAttack l₀ l₁ r₀))
      (independentTableStrongGame (feistel3CCAAttack l₀ l₁ r₀)) : ℝ) =
      1 - (Fintype.card G : ℝ)⁻¹ := by
  rw [Game.coe_advantage]
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal,
    eval_feistel3_feistel3CCAAttack, eval_independentTableStrongGame_feistel3CCAAttack,
    PMF.pure_apply_self, ENNReal.toReal_one, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  have hle : (Fintype.card G : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast Fintype.card_pos)
  exact abs_of_nonneg (sub_nonneg.mpr hle)

private theorem uniformOfFintype_prod_map_decide_add_snd_true (a t : G) :
    ((PMF.uniformOfFintype (G × G)).map (fun lr : G × G => decide (a + lr.2 = t))) true =
      (Fintype.card G : ℝ≥0∞)⁻¹ := by
  have hsnd :
      (PMF.uniformOfFintype (G × G)).map Prod.snd = PMF.uniformOfFintype G := by
    rw [← Probability.PMF.uniformOfFintype_map_equiv (Equiv.prodComm G G), PMF.map_comp]
    exact Probability.PMF.uniformOfFintype_prod_map_fst
  have hshift :
      (PMF.uniformOfFintype G).map (Equiv.addLeft a) = PMF.uniformOfFintype G :=
    Probability.PMF.uniformOfFintype_map_equiv (Equiv.addLeft a)
  have hmap :
      (PMF.uniformOfFintype (G × G)).map (fun lr : G × G => decide (a + lr.2 = t)) =
        (PMF.uniformOfFintype G).map (fun y => decide (y = t)) := by
    calc (PMF.uniformOfFintype (G × G)).map (fun lr : G × G => decide (a + lr.2 = t))
        = (((PMF.uniformOfFintype (G × G)).map Prod.snd).map (Equiv.addLeft a)).map
            (fun y => decide (y = t)) := by
          simp [PMF.map_comp, Function.comp_def]
      _ = (PMF.uniformOfFintype G).map (fun y => decide (y = t)) := by
          rw [hsnd, hshift]
  rw [hmap, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  have hpre : (fun y : G => decide (y = t)) ⁻¹' {true} = {t} := by
    ext y
    simp
  rw [hpre, PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply]

/-- When `l₀ ≠ l₁`, the true bidirectional random-permutation game `idealStrongGame` accepts
`feistel3CCAAttack l₀ l₁ r₀` with probability at most `|G|⁻¹ + 4 * |G × G|⁻¹`. -/
theorem idealStrongGame_feistel3CCAAttack_true_le {l₀ l₁ : G} (r₀ : G) (h01 : l₀ ≠ l₁) :
    idealStrongGame (feistel3CCAAttack l₀ l₁ r₀) true ≤
      (Fintype.card G : ℝ≥0∞)⁻¹ + 4 * (Fintype.card (G × G) : ℝ≥0∞)⁻¹ := by
  have hint (π : Equiv.Perm (G × G)) :
      OracleComp.interpret (feistelStrongOracle π) (feistel3CCAAttack l₀ l₁ r₀) =
        OracleComp.interpret (fun q => PMF.pure (RandomPermutation.evalPerm π q))
          (RandomPermutation.liftBoolProd (feistel3CCAAttack l₀ l₁ r₀)) := by
    rw [RandomPermutation.liftBoolProd, OracleComp.interpret_interpret]
    congr 1
    funext ⟨b, p⟩
    cases b <;> simp [feistelStrongOracle]
  have hgame :
      idealStrongGame (feistel3CCAAttack l₀ l₁ r₀) =
        (PMF.uniformOfFintype (Equiv.Perm (G × G))).bind fun π =>
          OracleComp.interpret (fun q => PMF.pure (RandomPermutation.evalPerm π q))
            (RandomPermutation.liftBoolProd (feistel3CCAAttack l₀ l₁ r₀)) := by
    simp only [idealStrongGame, Probability.PMF.monad_bind_eq_bind, hint]
  have hswitch := RandomPermutation.uniformPerm_bind_apply_le_forgetful
    (RandomPermutation.isQueryBounded_liftBoolProd (isQueryBounded_feistel3CCAAttack l₀ l₁ r₀))
    PMF.pure true
  simp only [Probability.PMF.monad_bind_eq_bind, PMF.bind_pure] at hswitch
  rw [← hgame] at hswitch
  have hp10 : (l₁, r₀) ≠ (l₀, r₀) := fun h => h01 (congrArg Prod.fst h).symm
  have hforget :
      (((OracleComp.interpret RandomPermutation.forgetfulAnswer
        (RandomPermutation.liftBoolProd (feistel3CCAAttack l₀ l₁ r₀))).run []).map
          Prod.fst) true ≤
        (Fintype.card G : ℝ≥0∞)⁻¹ + (Fintype.card (G × G) : ℝ≥0∞)⁻¹ := by
    have hrun :
        (((OracleComp.interpret RandomPermutation.forgetfulAnswer
          (RandomPermutation.liftBoolProd (feistel3CCAAttack l₀ l₁ r₀))).run []).map Prod.fst) =
          (PMF.uniformOfFintype (G × G)).bind fun vw₀ =>
            (PMF.uniformOfFintype (G × G)).bind fun vw₁ =>
              (RandomPermutation.forgetfulAnswer
                (.inverse (vw₀.1, (l₁ - l₀) + vw₀.2))
                [((l₁, r₀), vw₁), ((l₀, r₀), vw₀)]).map
                (fun x => decide (-vw₀.1 + x.1.2 = -vw₁.1 + r₀)) := by
      simp only [feistel3CCAAttack, RandomPermutation.liftBoolProd,
        RandomPermutation.PermQuery.ofBoolProd,
        OracleComp.interpret_bind, OracleComp.interpret_query, OracleComp.interpret_pure,
        StateT.run_bind, StateT.run_pure]
      dsimp only [StateT.run, RandomPermutation.forgetfulAnswer]
      simp only [List.lookup, beq_eq_false_iff_ne.mpr hp10,
        Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
        PMF.bind_map, PMF.map_bind, PMF.pure_map, Function.comp_def]
      rfl
    rw [hrun, PMF.bind_apply]
    have hvw₀ (vw₀ : G × G) :
        ((PMF.uniformOfFintype (G × G)).bind fun vw₁ =>
          (RandomPermutation.forgetfulAnswer
            (.inverse (vw₀.1, (l₁ - l₀) + vw₀.2))
            [((l₁, r₀), vw₁), ((l₀, r₀), vw₀)]).map
            (fun x => decide (-vw₀.1 + x.1.2 = -vw₁.1 + r₀))) true ≤
          (Fintype.card G : ℝ≥0∞)⁻¹ + (Fintype.card (G × G) : ℝ≥0∞)⁻¹ := by
      set q₃ : G × G := (vw₀.1, (l₁ - l₀) + vw₀.2)
      have hvw₀_ne : vw₀ ≠ q₃ := fun h => by
        have h2 := congrArg Prod.snd h
        dsimp only [q₃] at h2
        exact h01 (sub_eq_zero.mp (add_right_cancel ((zero_add vw₀.2).trans h2)).symm).symm
      rw [PMF.bind_apply]
      have hvw₁ (vw₁ : G × G) :
          (PMF.uniformOfFintype (G × G)) vw₁ *
            ((RandomPermutation.forgetfulAnswer (.inverse q₃)
              [((l₁, r₀), vw₁), ((l₀, r₀), vw₀)]).map
              (fun x => decide (-vw₀.1 + x.1.2 = -vw₁.1 + r₀))) true ≤
          (PMF.uniformOfFintype (G × G)) vw₁ * (Fintype.card G : ℝ≥0∞)⁻¹ +
            ({q₃} : Set (G × G)).indicator (PMF.uniformOfFintype (G × G)) vw₁ := by
        by_cases h13 : vw₁ = q₃
        · rw [Set.indicator_of_mem (Set.mem_singleton_iff.mpr h13)]
          calc (PMF.uniformOfFintype (G × G)) vw₁ *
                ((RandomPermutation.forgetfulAnswer (.inverse q₃)
                  [((l₁, r₀), vw₁), ((l₀, r₀), vw₀)]).map
                  (fun x => decide (-vw₀.1 + x.1.2 = -vw₁.1 + r₀))) true
              ≤ (PMF.uniformOfFintype (G × G)) vw₁ * 1 :=
                mul_le_mul_of_nonneg_left (PMF.coe_le_one _ true) zero_le
            _ = (PMF.uniformOfFintype (G × G)) vw₁ := mul_one _
            _ ≤ (PMF.uniformOfFintype (G × G)) vw₁ * (Fintype.card G : ℝ≥0∞)⁻¹ +
                  (PMF.uniformOfFintype (G × G)) vw₁ := le_add_self
        · rw [Set.indicator_of_notMem (fun h => h13 (Set.mem_singleton_iff.mp h)), add_zero]
          have hinv :
              RandomPermutation.invLookup [((l₁, r₀), vw₁), ((l₀, r₀), vw₀)] q₃ = none := by
            simp [RandomPermutation.invLookup, Ne.symm h13, Ne.symm hvw₀_ne]
          have hnone :
              ((RandomPermutation.forgetfulAnswer (.inverse q₃)
                [((l₁, r₀), vw₁), ((l₀, r₀), vw₀)]).map
                (fun x => decide (-vw₀.1 + x.1.2 = -vw₁.1 + r₀))) true =
                (Fintype.card G : ℝ≥0∞)⁻¹ := by
            dsimp only [RandomPermutation.forgetfulAnswer]
            rw [hinv, PMF.map_comp]
            exact uniformOfFintype_prod_map_decide_add_snd_true (-vw₀.1) (-vw₁.1 + r₀)
          rw [hnone]
      calc ∑' vw₁, (PMF.uniformOfFintype (G × G)) vw₁ *
            ((RandomPermutation.forgetfulAnswer (.inverse q₃)
              [((l₁, r₀), vw₁), ((l₀, r₀), vw₀)]).map
              (fun x => decide (-vw₀.1 + x.1.2 = -vw₁.1 + r₀))) true
          ≤ ∑' vw₁, ((PMF.uniformOfFintype (G × G)) vw₁ * (Fintype.card G : ℝ≥0∞)⁻¹ +
              ({q₃} : Set (G × G)).indicator (PMF.uniformOfFintype (G × G)) vw₁) :=
            tsum_le_tsum hvw₁
        _ = (Fintype.card G : ℝ≥0∞)⁻¹ + (Fintype.card (G × G) : ℝ≥0∞)⁻¹ := by
            rw [tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
              ← PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply_singleton,
              PMF.uniformOfFintype_apply]
    calc ∑' vw₀, (PMF.uniformOfFintype (G × G)) vw₀ *
          ((PMF.uniformOfFintype (G × G)).bind fun vw₁ =>
            (RandomPermutation.forgetfulAnswer
              (.inverse (vw₀.1, (l₁ - l₀) + vw₀.2))
              [((l₁, r₀), vw₁), ((l₀, r₀), vw₀)]).map
              (fun x => decide (-vw₀.1 + x.1.2 = -vw₁.1 + r₀))) true
        ≤ ∑' vw₀, (PMF.uniformOfFintype (G × G)) vw₀ *
            ((Fintype.card G : ℝ≥0∞)⁻¹ + (Fintype.card (G × G) : ℝ≥0∞)⁻¹) :=
          tsum_le_tsum fun vw₀ => mul_le_mul_of_nonneg_left (hvw₀ vw₀) zero_le
      _ = (Fintype.card G : ℝ≥0∞)⁻¹ + (Fintype.card (G × G) : ℝ≥0∞)⁻¹ := by
          rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  have hchoose : ((Nat.choose 3 2 : ℕ) : ℝ≥0∞) = 3 := rfl
  rw [hchoose] at hswitch
  calc idealStrongGame (feistel3CCAAttack l₀ l₁ r₀) true
      ≤ ((Fintype.card G : ℝ≥0∞)⁻¹ + (Fintype.card (G × G) : ℝ≥0∞)⁻¹) +
          3 * (Fintype.card (G × G) : ℝ≥0∞)⁻¹ :=
        hswitch.trans (add_le_add hforget le_rfl)
    _ = (Fintype.card G : ℝ≥0∞)⁻¹ + 4 * (Fintype.card (G × G) : ℝ≥0∞)⁻¹ := by
        ring

/-- **Quantitative nonnegligible CCA advantage lower bound against `idealStrongGame`**
([BonehShoup2023], Section 4.1.3 and Exercise 4.15(b)): whenever `l₀ ≠ l₁`, the 3-query
chosen-ciphertext distinguisher `feistel3CCAAttack l₀ l₁ r₀` distinguishes any 3-round Feistel
network `feistel3 f₁ f₂ f₃` from a uniform random permutation on `G × G` (`idealStrongGame`) with
advantage at least `1 - |G|⁻¹ - 4 * |G|⁻¹ ^ 2`. -/
theorem le_advantage_feistel3CCAAttack_idealStrongGame_of_ne (f₁ f₂ f₃ : G → G) {l₀ l₁ r₀ : G}
    (h01 : l₀ ≠ l₁) :
    1 - (Fintype.card G : ℝ)⁻¹ - 4 * ((Fintype.card G : ℝ)⁻¹) ^ 2 ≤
      (Game.advantage
        (OracleComp.interpret (feistelStrongOracle (feistel3 f₁ f₂ f₃))
          (feistel3CCAAttack l₀ l₁ r₀))
        (idealStrongGame (feistel3CCAAttack l₀ l₁ r₀)) : ℝ) := by
  have hcardG : (Fintype.card G : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcardGG : (Fintype.card (G × G) : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h1_top : (Fintype.card G : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hcardG
  have h2_top : 4 * (Fintype.card (G × G) : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.inv_ne_top.mpr hcardGG)
  have htrue := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨h1_top, h2_top⟩)
    (idealStrongGame_feistel3CCAAttack_true_le r₀ h01)
  rw [ENNReal.toReal_add h1_top h2_top, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    Fintype.card_prod, Nat.cast_mul, mul_inv, ← sq] at htrue
  rw [Game.coe_advantage, eval_feistel3_feistel3CCAAttack]
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal, PMF.pure_apply_self,
    ENNReal.toReal_one]
  have hle_abs :
      1 - (idealStrongGame (feistel3CCAAttack l₀ l₁ r₀) true).toReal ≤
        |1 - (idealStrongGame (feistel3CCAAttack l₀ l₁ r₀) true).toReal| := le_abs_self _
  linarith

/-- 4-round Feistel strong (bidirectional) game with four independent keyed round functions
`F k₁, F k₂, F k₃, F k₄`. -/
noncomputable def feistel4StrongKeyedGame (keyGen : PMF K) (F : K → G → G)
    (program : OracleComp (fun _ : Bool × (G × G) => G × G) Bool) : Game := do
  let k₁ ← keyGen
  let k₂ ← keyGen
  let k₃ ← keyGen
  let k₄ ← keyGen
  OracleComp.interpret (feistelStrongOracle (feistel4 (F k₁) (F k₂) (F k₃) (F k₄))) program

/-- 4-round Feistel strong (bidirectional) game with four independent uniform random round
functions `f₁, f₂, f₃, f₄ : G → G`. -/
noncomputable def feistel4StrongRandomRoundsGame
    (program : OracleComp (fun _ : Bool × (G × G) => G × G) Bool) : Game := do
  let f₁ ← PMF.uniformOfFintype (G → G)
  let f₂ ← PMF.uniformOfFintype (G → G)
  let f₃ ← PMF.uniformOfFintype (G → G)
  let f₄ ← PMF.uniformOfFintype (G → G)
  OracleComp.interpret (feistelStrongOracle (feistel4 f₁ f₂ f₃ f₄)) program

/-- Intermediate strong hybrid 1 for 4-round Feistel. -/
private noncomputable def feistel4StrongHybrid₁ (keyGen : PMF K) (F : K → G → G)
    (program : OracleComp (fun _ : Bool × (G × G) => G × G) Bool) : Game := do
  let f₁ ← PMF.uniformOfFintype (G → G)
  let k₂ ← keyGen
  let k₃ ← keyGen
  let k₄ ← keyGen
  OracleComp.interpret (feistelStrongOracle (feistel4 f₁ (F k₂) (F k₃) (F k₄))) program

/-- Intermediate strong hybrid 2 for 4-round Feistel. -/
private noncomputable def feistel4StrongHybrid₂ (keyGen : PMF K) (F : K → G → G)
    (program : OracleComp (fun _ : Bool × (G × G) => G × G) Bool) : Game := do
  let f₁ ← PMF.uniformOfFintype (G → G)
  let f₂ ← PMF.uniformOfFintype (G → G)
  let k₃ ← keyGen
  let k₄ ← keyGen
  OracleComp.interpret (feistelStrongOracle (feistel4 f₁ f₂ (F k₃) (F k₄))) program

/-- Intermediate strong hybrid 3 for 4-round Feistel. -/
private noncomputable def feistel4StrongHybrid₃ (keyGen : PMF K) (F : K → G → G)
    (program : OracleComp (fun _ : Bool × (G × G) => G × G) Bool) : Game := do
  let f₁ ← PMF.uniformOfFintype (G → G)
  let f₂ ← PMF.uniformOfFintype (G → G)
  let f₃ ← PMF.uniformOfFintype (G → G)
  let k₄ ← keyGen
  OracleComp.interpret (feistelStrongOracle (feistel4 f₁ f₂ f₃ (F k₄))) program

/-- Round-1 bidirectional PRF reduction distinguisher for 4-round Feistel. -/
def feistel4StrongReduction₁ (f₂ f₃ f₄ : G → G)
    (program : OracleComp (fun _ : Bool × (G × G) => G × G) Bool) :
    OracleComp (fun _ : G => G) Bool :=
  OracleComp.interpret
    (fun q => match q with
      | (false, p) => do
        let y₁ ← OracleComp.query (spec := fun _ : G => G) p.2
        let u := p.1 + y₁
        let v := p.2 + f₂ u
        let w := u + f₃ v
        return (w, v + f₄ w)
      | (true, wz) => do
        let v := wz.2 - f₄ wz.1
        let u := wz.1 - f₃ v
        let r := v - f₂ u
        let y₁ ← OracleComp.query (spec := fun _ : G => G) r
        return (u - y₁, r))
    program

/-- Round-2 bidirectional PRF reduction distinguisher for 4-round Feistel. -/
def feistel4StrongReduction₂ (f₁ f₃ f₄ : G → G)
    (program : OracleComp (fun _ : Bool × (G × G) => G × G) Bool) :
    OracleComp (fun _ : G => G) Bool :=
  OracleComp.interpret
    (fun q => match q with
      | (false, p) => do
        let u := p.1 + f₁ p.2
        let y₂ ← OracleComp.query (spec := fun _ : G => G) u
        let v := p.2 + y₂
        let w := u + f₃ v
        return (w, v + f₄ w)
      | (true, wz) => do
        let v := wz.2 - f₄ wz.1
        let u := wz.1 - f₃ v
        let y₂ ← OracleComp.query (spec := fun _ : G => G) u
        let r := v - y₂
        return (u - f₁ r, r))
    program

/-- Round-3 bidirectional PRF reduction distinguisher for 4-round Feistel. -/
def feistel4StrongReduction₃ (f₁ f₂ f₄ : G → G)
    (program : OracleComp (fun _ : Bool × (G × G) => G × G) Bool) :
    OracleComp (fun _ : G => G) Bool :=
  OracleComp.interpret
    (fun q => match q with
      | (false, p) => do
        let u := p.1 + f₁ p.2
        let v := p.2 + f₂ u
        let y₃ ← OracleComp.query (spec := fun _ : G => G) v
        let w := u + y₃
        return (w, v + f₄ w)
      | (true, wz) => do
        let v := wz.2 - f₄ wz.1
        let y₃ ← OracleComp.query (spec := fun _ : G => G) v
        let u := wz.1 - y₃
        let r := v - f₂ u
        return (u - f₁ r, r))
    program

/-- Round-4 bidirectional PRF reduction distinguisher for 4-round Feistel. -/
def feistel4StrongReduction₄ (f₁ f₂ f₃ : G → G)
    (program : OracleComp (fun _ : Bool × (G × G) => G × G) Bool) :
    OracleComp (fun _ : G => G) Bool :=
  OracleComp.interpret
    (fun q => match q with
      | (false, p) => do
        let u := p.1 + f₁ p.2
        let v := p.2 + f₂ u
        let w := u + f₃ v
        let y₄ ← OracleComp.query (spec := fun _ : G => G) w
        return (w, v + y₄)
      | (true, wz) => do
        let y₄ ← OracleComp.query (spec := fun _ : G => G) wz.1
        let v := wz.2 - y₄
        let u := wz.1 - f₃ v
        let r := v - f₂ u
        return (u - f₁ r, r))
    program

omit [Fintype G] [DecidableEq G] [Nonempty G] in
private theorem interpret_feistel4StrongReduction₁ (f₁ f₂ f₃ f₄ : G → G)
    (program : OracleComp (fun _ : Bool × (G × G) => G × G) Bool) :
    OracleComp.interpret (fun x => PMF.pure (f₁ x))
      (feistel4StrongReduction₁ f₂ f₃ f₄ program) =
      OracleComp.interpret (feistelStrongOracle (feistel4 f₁ f₂ f₃ f₄)) program := by
  rw [feistel4StrongReduction₁, OracleComp.interpret_interpret]
  congr 1
  funext ⟨b, p⟩
  cases b <;>
    simp [feistelStrongOracle, feistel4_apply, feistel4_symm_apply, feistelRound, feistelInvRound,
      feistel3_apply, feistel3_symm_apply]

omit [Fintype G] [DecidableEq G] [Nonempty G] in
private theorem interpret_feistel4StrongReduction₂ (f₁ f₂ f₃ f₄ : G → G)
    (program : OracleComp (fun _ : Bool × (G × G) => G × G) Bool) :
    OracleComp.interpret (fun x => PMF.pure (f₂ x))
      (feistel4StrongReduction₂ f₁ f₃ f₄ program) =
      OracleComp.interpret (feistelStrongOracle (feistel4 f₁ f₂ f₃ f₄)) program := by
  rw [feistel4StrongReduction₂, OracleComp.interpret_interpret]
  congr 1
  funext ⟨b, p⟩
  cases b <;>
    simp [feistelStrongOracle, feistel4_apply, feistel4_symm_apply, feistelRound, feistelInvRound,
      feistel3_apply, feistel3_symm_apply]

omit [Fintype G] [DecidableEq G] [Nonempty G] in
private theorem interpret_feistel4StrongReduction₃ (f₁ f₂ f₃ f₄ : G → G)
    (program : OracleComp (fun _ : Bool × (G × G) => G × G) Bool) :
    OracleComp.interpret (fun x => PMF.pure (f₃ x))
      (feistel4StrongReduction₃ f₁ f₂ f₄ program) =
      OracleComp.interpret (feistelStrongOracle (feistel4 f₁ f₂ f₃ f₄)) program := by
  rw [feistel4StrongReduction₃, OracleComp.interpret_interpret]
  congr 1
  funext ⟨b, p⟩
  cases b <;>
    simp [feistelStrongOracle, feistel4_apply, feistel4_symm_apply, feistelRound, feistelInvRound,
      feistel3_apply, feistel3_symm_apply]

omit [Fintype G] [DecidableEq G] [Nonempty G] in
private theorem interpret_feistel4StrongReduction₄ (f₁ f₂ f₃ f₄ : G → G)
    (program : OracleComp (fun _ : Bool × (G × G) => G × G) Bool) :
    OracleComp.interpret (fun x => PMF.pure (f₄ x))
      (feistel4StrongReduction₄ f₁ f₂ f₃ program) =
      OracleComp.interpret (feistelStrongOracle (feistel4 f₁ f₂ f₃ f₄)) program := by
  rw [feistel4StrongReduction₄, OracleComp.interpret_interpret]
  congr 1
  funext ⟨b, p⟩
  cases b <;>
    simp [feistelStrongOracle, feistel4_apply, feistel4_symm_apply, feistelRound, feistelInvRound,
      feistel3_apply, feistel3_symm_apply]

/-- **4-round bidirectional PRF-to-Feistel hybrid theorem**: because Feistel inversion only
evaluates the round functions in the forward direction, replacing four keyed round functions
`F k₁, F k₂, F k₃, F k₄` with independent uniform random round functions against any bidirectional
(chosen-ciphertext) adversary adds at most `ε₁ + ε₂ + ε₃ + ε₄`. -/
theorem advantage_feistel4StrongKeyedGame_feistel4StrongRandomRoundsGame_le
    {keyGen : PMF K} {F : K → G → G}
    {program : OracleComp (fun _ : Bool × (G × G) => G × G) Bool} {ε₁ ε₂ ε₃ ε₄ : ℝ}
    (h₁ : ∀ f₂ f₃ f₄,
      (Game.advantage (prfSingleRealGame keyGen F (feistel4StrongReduction₁ f₂ f₃ f₄ program))
        (prfSingleIdealGame (feistel4StrongReduction₁ f₂ f₃ f₄ program)) : ℝ) ≤ ε₁)
    (h₂ : ∀ f₁ f₃ f₄,
      (Game.advantage (prfSingleRealGame keyGen F (feistel4StrongReduction₂ f₁ f₃ f₄ program))
        (prfSingleIdealGame (feistel4StrongReduction₂ f₁ f₃ f₄ program)) : ℝ) ≤ ε₂)
    (h₃ : ∀ f₁ f₂ f₄,
      (Game.advantage (prfSingleRealGame keyGen F (feistel4StrongReduction₃ f₁ f₂ f₄ program))
        (prfSingleIdealGame (feistel4StrongReduction₃ f₁ f₂ f₄ program)) : ℝ) ≤ ε₃)
    (h₄ : ∀ f₁ f₂ f₃,
      (Game.advantage (prfSingleRealGame keyGen F (feistel4StrongReduction₄ f₁ f₂ f₃ program))
        (prfSingleIdealGame (feistel4StrongReduction₄ f₁ f₂ f₃ program)) : ℝ) ≤ ε₄) :
    (Game.advantage (feistel4StrongKeyedGame keyGen F program)
      (feistel4StrongRandomRoundsGame program) : ℝ) ≤ ε₁ + ε₂ + ε₃ + ε₄ := by
  have hhop1 :
      (Game.advantage (feistel4StrongKeyedGame keyGen F program)
        (feistel4StrongHybrid₁ keyGen F program) : ℝ) ≤ ε₁ := by
    simp only [feistel4StrongKeyedGame, feistel4StrongHybrid₁,
      Probability.PMF.monad_bind_eq_bind]
    refine advantage_bind_right_le _ _ _ _ _ fun k₂ =>
      advantage_bind_right_le _ _ _ _ _ fun k₃ =>
        advantage_bind_right_le _ _ _ _ _ fun k₄ => ?_
    simpa only [prfSingleRealGame, prfSingleIdealGame, interpret_feistel4StrongReduction₁,
      Probability.PMF.monad_bind_eq_bind] using h₁ (F k₂) (F k₃) (F k₄)
  have hhop2 :
      (Game.advantage (feistel4StrongHybrid₁ keyGen F program)
        (feistel4StrongHybrid₂ keyGen F program) : ℝ) ≤ ε₂ := by
    simp only [feistel4StrongHybrid₁, feistel4StrongHybrid₂,
      Probability.PMF.monad_bind_eq_bind]
    refine Game.advantage_bind_le _ _ _ fun f₁ =>
      advantage_bind_right_le _ _ _ _ _ fun k₃ =>
        advantage_bind_right_le _ _ _ _ _ fun k₄ => ?_
    simpa only [prfSingleRealGame, prfSingleIdealGame, interpret_feistel4StrongReduction₂,
      Probability.PMF.monad_bind_eq_bind] using h₂ f₁ (F k₃) (F k₄)
  have hhop3 :
      (Game.advantage (feistel4StrongHybrid₂ keyGen F program)
        (feistel4StrongHybrid₃ keyGen F program) : ℝ) ≤ ε₃ := by
    simp only [feistel4StrongHybrid₂, feistel4StrongHybrid₃,
      Probability.PMF.monad_bind_eq_bind]
    refine Game.advantage_bind_le _ _ _ fun f₁ =>
      Game.advantage_bind_le _ _ _ fun f₂ =>
        advantage_bind_right_le _ _ _ _ _ fun k₄ => ?_
    simpa only [prfSingleRealGame, prfSingleIdealGame, interpret_feistel4StrongReduction₃,
      Probability.PMF.monad_bind_eq_bind] using h₃ f₁ f₂ (F k₄)
  have hhop4 :
      (Game.advantage (feistel4StrongHybrid₃ keyGen F program)
        (feistel4StrongRandomRoundsGame program) : ℝ) ≤ ε₄ := by
    simp only [feistel4StrongHybrid₃, feistel4StrongRandomRoundsGame,
      Probability.PMF.monad_bind_eq_bind]
    refine Game.advantage_bind_le _ _ _ fun f₁ =>
      Game.advantage_bind_le _ _ _ fun f₂ =>
        Game.advantage_bind_le _ _ _ fun f₃ => ?_
    simpa only [prfSingleRealGame, prfSingleIdealGame, interpret_feistel4StrongReduction₄,
      Probability.PMF.monad_bind_eq_bind] using h₄ f₁ f₂ f₃
  have htri1 := NNReal.coe_le_coe.mpr (Game.advantage_triangle
    (feistel4StrongKeyedGame keyGen F program) (feistel4StrongHybrid₁ keyGen F program)
    (feistel4StrongRandomRoundsGame program))
  have htri2 := NNReal.coe_le_coe.mpr (Game.advantage_triangle
    (feistel4StrongHybrid₁ keyGen F program) (feistel4StrongHybrid₂ keyGen F program)
    (feistel4StrongRandomRoundsGame program))
  have htri3 := NNReal.coe_le_coe.mpr (Game.advantage_triangle
    (feistel4StrongHybrid₂ keyGen F program) (feistel4StrongHybrid₃ keyGen F program)
    (feistel4StrongRandomRoundsGame program))
  simp only [NNReal.coe_add] at htri1 htri2 htri3
  linarith

/-! ### 4-round bidirectional random-round collision analysis and strong PRP Luby–Rackoff theorem -/

omit [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] in
private theorem interpret_feistelStrongOracle_eq_liftBoolProd (π : Equiv.Perm (G × G))
    {α : Type} (program : OracleComp (fun _ : Bool × (G × G) => G × G) α) :
    OracleComp.interpret (feistelStrongOracle π) program =
      OracleComp.interpret (fun q => PMF.pure (RandomPermutation.evalPerm π q))
        (RandomPermutation.liftBoolProd program) := by
  rw [RandomPermutation.liftBoolProd, OracleComp.interpret_interpret]
  congr 1
  funext ⟨b, p⟩
  cases b <;> simp [feistelStrongOracle]

/-- 4-round strong Feistel game with fixed outer round functions `f₁, f₄ : G → G` and independent
uniform random inner round functions `f₂, f₃ : G → G`. -/
private noncomputable def feistel4StrongFixedGame (f₁ f₄ : G → G)
    (program : OracleComp (fun _ : Bool × (G × G) => G × G) Bool) : Game := do
  let f₂ ← PMF.uniformOfFintype (G → G)
  let f₃ ← PMF.uniformOfFintype (G → G)
  OracleComp.interpret (feistelStrongOracle (feistel4 f₁ f₂ f₃ f₄)) program

private theorem feistel4StrongRandomRoundsGame_eq_bind_fixed
    (program : OracleComp (fun _ : Bool × (G × G) => G × G) Bool) :
    feistel4StrongRandomRoundsGame program = (do
      let f₁ ← PMF.uniformOfFintype (G → G)
      let f₄ ← PMF.uniformOfFintype (G → G)
      feistel4StrongFixedGame f₁ f₄ program) := by
  simp only [feistel4StrongRandomRoundsGame, feistel4StrongFixedGame,
    Probability.PMF.monad_bind_eq_bind]
  refine congrArg ((PMF.uniformOfFintype (G → G)).bind) (funext fun f₁ => ?_)
  refine (congrArg ((PMF.uniformOfFintype (G → G)).bind)
    (funext fun f₂ => PMF.bind_comm _ _ _)).trans ?_
  exact PMF.bind_comm _ _ _

/-- One step of bidirectional query deduplication over a partial-permutation cache `qc`. -/
private def bidirDedupStep (q : RandomPermutation.PermQuery (G × G)) :
    StateT (RandomPermutation.Cache (G × G))
      (OracleComp (RandomPermutation.PermOracleSpec (G × G))) (G × G) := fun qc =>
  match q with
  | .forward p =>
    match qc.lookup p with
    | some wz => pure (wz, qc)
    | none => do
      let wz ← OracleComp.query (spec := RandomPermutation.PermOracleSpec (G × G)) (.forward p)
      pure (wz, (p, wz) :: qc)
  | .inverse wz =>
    match RandomPermutation.invLookup qc wz with
    | some p => pure (p, qc)
    | none => do
      let p ← OracleComp.query (spec := RandomPermutation.PermOracleSpec (G × G)) (.inverse wz)
      pure (p, (p, wz) :: qc)

omit [AddGroup G] [Fintype G] [Nonempty G] in
private theorem bidirDedupStep_forward_of_some {p wz : G × G}
    {qc : RandomPermutation.Cache (G × G)} (h : qc.lookup p = some wz) :
    bidirDedupStep (.forward p) qc = pure (wz, qc) := by
  simp [bidirDedupStep, h]

omit [AddGroup G] [Fintype G] [Nonempty G] in
private theorem bidirDedupStep_forward_of_none {p : G × G}
    {qc : RandomPermutation.Cache (G × G)} (h : qc.lookup p = none) :
    bidirDedupStep (.forward p) qc = (do
      let wz ← OracleComp.query (spec := RandomPermutation.PermOracleSpec (G × G)) (.forward p)
      pure (wz, (p, wz) :: qc)) := by
  simp [bidirDedupStep, h]

omit [AddGroup G] [Fintype G] [Nonempty G] in
private theorem bidirDedupStep_inverse_of_some {wz p : G × G}
    {qc : RandomPermutation.Cache (G × G)} (h : RandomPermutation.invLookup qc wz = some p) :
    bidirDedupStep (.inverse wz) qc = pure (p, qc) := by
  simp [bidirDedupStep, h]

omit [AddGroup G] [Fintype G] [Nonempty G] in
private theorem bidirDedupStep_inverse_of_none {wz : G × G}
    {qc : RandomPermutation.Cache (G × G)} (h : RandomPermutation.invLookup qc wz = none) :
    bidirDedupStep (.inverse wz) qc = (do
      let p ← OracleComp.query (spec := RandomPermutation.PermOracleSpec (G × G)) (.inverse wz)
      pure (p, (p, wz) :: qc)) := by
  simp [bidirDedupStep, h]

/-- Deduplicate a bidirectional permutation program so that forward queries in `dom(qc)` and
inverse queries in `ran(qc)` are answered from `qc` without calling the underlying oracle. -/
private def bidirDedup {α : Type}
    (program : OracleComp (RandomPermutation.PermOracleSpec (G × G)) α) :
    OracleComp (RandomPermutation.PermOracleSpec (G × G))
      (α × RandomPermutation.Cache (G × G)) :=
  (OracleComp.interpret bidirDedupStep program).run []

omit [AddGroup G] [Fintype G] [Nonempty G] in
private theorem map_fst_interpret_bidirDedupStep_evalPerm {α : Type} (π : Equiv.Perm (G × G))
    (program : OracleComp (RandomPermutation.PermOracleSpec (G × G)) α)
    {qc : RandomPermutation.Cache (G × G)} (hqc : RandomPermutation.AgreesWith qc π) :
    (OracleComp.interpret (fun q => PMF.pure (RandomPermutation.evalPerm π q))
      ((OracleComp.interpret bidirDedupStep program).run qc)).map Prod.fst =
    OracleComp.interpret (fun q => PMF.pure (RandomPermutation.evalPerm π q)) program := by
  induction program using PFunctor.FreeM.induction generalizing qc with
  | pure a =>
    simp [PMF.pure_map]
  | lift_bind q cont ih =>
    change (OracleComp.interpret (fun q => PMF.pure (RandomPermutation.evalPerm π q))
      ((OracleComp.interpret bidirDedupStep (OracleComp.query q >>= cont)).run qc)).map
        Prod.fst =
      OracleComp.interpret (fun q => PMF.pure (RandomPermutation.evalPerm π q))
        (OracleComp.query q >>= cont)
    simp only [OracleComp.interpret_bind, OracleComp.interpret_query, StateT.run_bind,
      Probability.PMF.monad_bind_eq_bind, PMF.pure_bind]
    change (((OracleComp.interpret (fun q => PMF.pure (RandomPermutation.evalPerm π q))
      (bidirDedupStep q qc)).bind fun p_1 =>
        OracleComp.interpret (fun q => PMF.pure (RandomPermutation.evalPerm π q))
          ((OracleComp.interpret bidirDedupStep (cont p_1.1)).run p_1.2)).map Prod.fst) =
      OracleComp.interpret (fun q => PMF.pure (RandomPermutation.evalPerm π q))
        (cont (RandomPermutation.evalPerm π q))
    cases q with
    | forward p =>
      cases h : qc.lookup p with
      | some wz =>
        rw [bidirDedupStep_forward_of_some h]
        simp only [OracleComp.interpret_pure, Probability.PMF.monad_pure_eq_pure,
          PMF.pure_bind, RandomPermutation.evalPerm_forward,
          hqc.apply_of_lookup_eq_some h]
        exact ih wz hqc
      | none =>
        rw [bidirDedupStep_forward_of_none h]
        simp only [OracleComp.interpret_bind, OracleComp.interpret_query,
          OracleComp.interpret_pure, Probability.PMF.monad_bind_eq_bind,
          Probability.PMF.monad_pure_eq_pure, PMF.pure_bind,
          RandomPermutation.evalPerm_forward]
        exact ih (π p) ((RandomPermutation.agreesWith_cons _ _ _).mpr ⟨rfl, hqc⟩)
    | inverse wz =>
      cases h : RandomPermutation.invLookup qc wz with
      | some p =>
        rw [bidirDedupStep_inverse_of_some h]
        simp only [OracleComp.interpret_pure, Probability.PMF.monad_pure_eq_pure,
          PMF.pure_bind, RandomPermutation.evalPerm_inverse,
          hqc.symm_apply_of_invLookup_eq_some h]
        exact ih p hqc
      | none =>
        rw [bidirDedupStep_inverse_of_none h]
        simp only [OracleComp.interpret_bind, OracleComp.interpret_query,
          OracleComp.interpret_pure, Probability.PMF.monad_bind_eq_bind,
          Probability.PMF.monad_pure_eq_pure, PMF.pure_bind,
          RandomPermutation.evalPerm_inverse]
        exact ih (π.symm wz)
          ((RandomPermutation.agreesWith_cons _ _ _).mpr ⟨Equiv.apply_symm_apply π wz, hqc⟩)

omit [AddGroup G] [Fintype G] [Nonempty G] in
private theorem map_fst_interpret_bidirDedup_evalPerm {α : Type} (π : Equiv.Perm (G × G))
    (program : OracleComp (RandomPermutation.PermOracleSpec (G × G)) α) :
    (OracleComp.interpret (fun q => PMF.pure (RandomPermutation.evalPerm π q))
      (bidirDedup program)).map Prod.fst =
    OracleComp.interpret (fun q => PMF.pure (RandomPermutation.evalPerm π q)) program :=
  map_fst_interpret_bidirDedupStep_evalPerm π program (RandomPermutation.agreesWith_nil π)

/-- Express one bidirectional 4-round Feistel call with fixed outer round functions `f₁, f₄` as a
two-query program to the combined Round-2/Round-3 oracle `Bool × G → G`. -/
private def feistel4Query (f₁ f₄ : G → G) :
    RandomPermutation.PermQuery (G × G) → OracleComp (fun _ : Bool × G => G) (G × G)
  | .forward p => do
    let u := p.1 + f₁ p.2
    let y₂ ← OracleComp.query (spec := fun _ : Bool × G => G) (false, u)
    let v := p.2 + y₂
    let y₃ ← OracleComp.query (spec := fun _ : Bool × G => G) (true, v)
    let w := u + y₃
    return (w, v + f₄ w)
  | .inverse wz => do
    let v := wz.2 - f₄ wz.1
    let y₃ ← OracleComp.query (spec := fun _ : Bool × G => G) (true, v)
    let u := wz.1 - y₃
    let y₂ ← OracleComp.query (spec := fun _ : Bool × G => G) (false, u)
    let r := v - y₂
    return (u - f₁ r, r)

/-- Lazy Round-2/Round-3 handler for 4-round Feistel without bad-flag tracking. -/
private noncomputable def lazyRoundHandler4 (f₁ f₄ : G → G)
    (q : RandomPermutation.PermQuery (G × G)) :
    StateT (List ((Bool × G) × G)) PMF (G × G) := fun cache =>
  (OracleComp.interpret (memoize (fun _ : Bool × G => PMF.uniformOfFintype G))
    (feistel4Query f₁ f₄ q)).run cache

/-- Real 4-round handler with bad flag: lazily evaluates `f₂` and `f₃`, setting `bad := true` if
`(false, u)` or `(true, v)` was already present in the round-function cache. -/
private noncomputable def realRoundHandler4 (f₁ f₄ : G → G)
    (q : RandomPermutation.PermQuery (G × G)) :
    StateT (List ((Bool × G) × G) × Bool) PMF (G × G) := fun (cache, bad) =>
  match q with
  | .forward p => do
    let u := p.1 + f₁ p.2
    let bad₁ := bad || (cache.lookup (false, u)).isSome
    let (y₂, cache₁) ← memoize (fun _ : Bool × G => PMF.uniformOfFintype G) (false, u) cache
    let v := p.2 + y₂
    let bad₂ := bad₁ || (cache.lookup (true, v)).isSome
    let (y₃, cache₂) ← memoize (fun _ : Bool × G => PMF.uniformOfFintype G) (true, v) cache₁
    let w := u + y₃
    return ((w, v + f₄ w), (cache₂, bad₂))
  | .inverse wz => do
    let v := wz.2 - f₄ wz.1
    let bad₁ := bad || (cache.lookup (true, v)).isSome
    let (y₃, cache₁) ← memoize (fun _ : Bool × G => PMF.uniformOfFintype G) (true, v) cache
    let u := wz.1 - y₃
    let bad₂ := bad₁ || (cache.lookup (false, u)).isSome
    let (y₂, cache₂) ← memoize (fun _ : Bool × G => PMF.uniformOfFintype G) (false, u) cache₁
    let r := v - y₂
    return ((u - f₁ r, r), (cache₂, bad₂))

private theorem realRoundHandler4_map_fst (f₁ f₄ : G → G)
    (q : RandomPermutation.PermQuery (G × G)) (st : List ((Bool × G) × G) × Bool) :
    (realRoundHandler4 f₁ f₄ q st).map (fun (a, s') => (a, s'.1)) =
      lazyRoundHandler4 f₁ f₄ q st.1 := by
  rcases st with ⟨cache, bad⟩
  cases q with
  | forward p =>
    simp only [realRoundHandler4, lazyRoundHandler4, feistel4Query,
      OracleComp.interpret_bind, OracleComp.interpret_query, OracleComp.interpret_pure,
      Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
      PMF.map_bind, PMF.pure_map]
    rfl
  | inverse wz =>
    simp only [realRoundHandler4, lazyRoundHandler4, feistel4Query,
      OracleComp.interpret_bind, OracleComp.interpret_query, OracleComp.interpret_pure,
      Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
      PMF.map_bind, PMF.pure_map]
    rfl

private theorem feistel4StrongFixedGame_eq_realRoundHandler4 (f₁ f₄ : G → G)
    (program : OracleComp (fun _ : Bool × (G × G) => G × G) Bool) :
    feistel4StrongFixedGame f₁ f₄ program =
      (((OracleComp.interpret (realRoundHandler4 f₁ f₄)
        (bidirDedup (RandomPermutation.liftBoolProd program))).run ([], false)).map
          fun x => x.1.1) := by
  set prog := RandomPermutation.liftBoolProd program
  have hdrop := OracleComp.run_interpret_map_state (realRoundHandler4 f₁ f₄)
    (lazyRoundHandler4 f₁ f₄) Prod.fst (realRoundHandler4_map_fst f₁ f₄) (bidirDedup prog)
    ([], false)
  have hdrop' := congrArg (PMF.map fun x => x.1.1) hdrop
  simp only [PMF.map_comp, Function.comp_def] at hdrop'
  rw [hdrop']
  have hlazy := RandomOracle.interpret_eq_memoize (fun _ : Bool × G => PMF.uniformOfFintype G)
    (OracleComp.interpret (feistel4Query f₁ f₄) (bidirDedup prog))
  rw [Probability.PMF.pi_uniformOfFintype] at hlazy
  have hcomp :
      OracleComp.interpret (memoize (fun _ : Bool × G => PMF.uniformOfFintype G))
        (OracleComp.interpret (feistel4Query f₁ f₄) (bidirDedup prog)) =
      OracleComp.interpret (lazyRoundHandler4 f₁ f₄) (bidirDedup prog) :=
    OracleComp.interpret_interpret _ _ _
  rw [hcomp] at hlazy
  have hlazy' := congrArg (PMF.map Prod.fst) hlazy.symm
  simp only [Probability.PMF.monad_bind_eq_bind, PMF.map_comp, Function.comp_def,
    PMF.map_bind] at hlazy'
  rw [hlazy']
  have htable (table : Bool × G → G) :
      (OracleComp.interpret (fun q => PMF.pure (table q))
        (OracleComp.interpret (feistel4Query f₁ f₄) (bidirDedup prog))).map Prod.fst =
      OracleComp.interpret
        (feistelStrongOracle
          (feistel4 f₁ (fun u => table (false, u)) (fun v => table (true, v)) f₄))
        program := by
    rw [OracleComp.interpret_interpret]
    have hstep :
        (fun q => OracleComp.interpret (fun x => PMF.pure (table x)) (feistel4Query f₁ f₄ q)) =
        (fun q => PMF.pure (RandomPermutation.evalPerm
          (feistel4 f₁ (fun u => table (false, u)) (fun v => table (true, v)) f₄) q)) := by
      funext q
      cases q <;>
        simp [feistel4Query, feistel4_apply, feistel4_symm_apply, feistelRound, feistelInvRound,
          feistel3_apply, feistel3_symm_apply]
    rw [hstep, map_fst_interpret_bidirDedup_evalPerm,
      ← interpret_feistelStrongOracle_eq_liftBoolProd]
  simp only [htable]
  have hunif :
      (PMF.uniformOfFintype (Bool × G → G)).map splitBoolTable =
        (PMF.uniformOfFintype (G → G)).bind fun f₂ =>
          (PMF.uniformOfFintype (G → G)).map fun f₃ => (f₂, f₃) := by
    rw [Probability.PMF.uniformOfFintype_map_equiv splitBoolTable,
      Probability.PMF.uniformOfFintype_prod]
  have hbind := congrArg
    (fun d : PMF ((G → G) × (G → G)) =>
      d.bind fun fg =>
        OracleComp.interpret (feistelStrongOracle (feistel4 f₁ fg.1 fg.2 f₄)) program)
    hunif.symm
  simpa only [feistel4StrongFixedGame, splitBoolTable, Equiv.coe_fn_mk, PMF.bind_map,
    PMF.bind_bind, Function.comp_def, PMF.monad_bind_eq_bind] using hbind

/-- Ideal 4-round handler with bad flag: on `.forward p` draws `wz ← PMF.uniformOfFintype (G × G)`
and reconstructs `v = wz.2 - f₄ wz.1`, `y₂ = -p.2 + v`, `y₃ = -u + wz.1`; on `.inverse wz` draws
`p ← PMF.uniformOfFintype (G × G)` and reconstructs `u = p.1 + f₁ p.2`, `y₃ = -u + wz.1`,
`y₂ = -p.2 + v`. -/
private noncomputable def idealRoundHandler4 (f₁ f₄ : G → G)
    (q : RandomPermutation.PermQuery (G × G)) :
    StateT (List ((Bool × G) × G) × Bool) PMF (G × G) := fun (cache, bad) =>
  match q with
  | .forward p => do
    let u := p.1 + f₁ p.2
    let bad₁ := bad || (cache.lookup (false, u)).isSome
    let wz ← PMF.uniformOfFintype (G × G)
    let v := wz.2 - f₄ wz.1
    let bad₂ := bad₁ || (cache.lookup (true, v)).isSome
    let y₂ := -p.2 + v
    let y₃ := -u + wz.1
    let cache₂ := ((true, v), y₃) :: ((false, u), y₂) :: cache
    return (wz, (cache₂, bad₂))
  | .inverse wz => do
    let v := wz.2 - f₄ wz.1
    let bad₁ := bad || (cache.lookup (true, v)).isSome
    let p ← PMF.uniformOfFintype (G × G)
    let u := p.1 + f₁ p.2
    let bad₂ := bad₁ || (cache.lookup (false, u)).isSome
    let y₃ := -u + wz.1
    let y₂ := -p.2 + v
    let cache₂ := ((false, u), y₂) :: ((true, v), y₃) :: cache
    return (p, (cache₂, bad₂))

omit [AddGroup G] [Fintype G] [Nonempty G] in
private theorem lookup_false_cons_true (v u : G) (y₃ : G) (cache : List ((Bool × G) × G)) :
    (((true, v), y₃) :: cache).lookup (false, u) = cache.lookup (false, u) := by
  have h : ((false, u) == (true, v)) = false := rfl
  simp [List.lookup_cons, h]

omit [Fintype G] [DecidableEq G] [Nonempty G] in
/-- Left subtraction `y ↦ a - y` as an equivalence on `G` with inverse `u ↦ -u + a`. -/
private def subLeftEquiv (a : G) : G ≃ G where
  toFun y := a - y
  invFun u := -u + a
  left_inv y := by
    dsimp
    rw [neg_sub, sub_add_cancel]
  right_inv u := by
    dsimp
    rw [sub_eq_add_neg, neg_add_rev, neg_neg, ← add_assoc, add_neg_cancel, zero_add]

omit [Fintype G] [DecidableEq G] [Nonempty G] in
private theorem subLeftEquiv_apply (a b : G) : subLeftEquiv a b = a - b := rfl

omit [Fintype G] [DecidableEq G] [Nonempty G] in
/-- Output bijection `(v, w) ↦ (w, v + f₄ w)` for a forward 4-round Feistel query. -/
private def forwardOutEquiv (f₄ : G → G) : G × G ≃ G × G where
  toFun vw := (vw.2, vw.1 + f₄ vw.2)
  invFun wz := (wz.2 - f₄ wz.1, wz.1)
  left_inv := fun ⟨v, w⟩ => by simp
  right_inv := fun ⟨w, z⟩ => by simp

omit [Fintype G] [DecidableEq G] [Nonempty G] in
/-- Output bijection `(u, r) ↦ (u - f₁ r, r)` for an inverse 4-round Feistel query. -/
private def inverseOutEquiv (f₁ : G → G) : G × G ≃ G × G where
  toFun ur := (ur.1 - f₁ ur.2, ur.2)
  invFun p := (p.1 + f₁ p.2, p.2)
  left_inv := fun ⟨u, r⟩ => by simp
  right_inv := fun ⟨l, r⟩ => by simp

private theorem realRoundHandler4_forward_of_none (f₁ f₄ : G → G) (p : G × G)
    (cache : List ((Bool × G) × G)) (hu : cache.lookup (false, p.1 + f₁ p.2) = none) :
    realRoundHandler4 f₁ f₄ (.forward p) (cache, false) =
      (PMF.uniformOfFintype G).bind fun v =>
        (memoize (fun _ : Bool × G => PMF.uniformOfFintype G) (true, v)
          (((false, p.1 + f₁ p.2), -p.2 + v) :: cache)).bind fun x =>
            PMF.pure ((p.1 + f₁ p.2 + x.1, v + f₄ (p.1 + f₁ p.2 + x.1)),
              (x.2, (cache.lookup (true, v)).isSome)) := by
  simp only [realRoundHandler4, memoize_of_none _ _ _ hu,
    Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
    PMF.bind_bind, PMF.pure_bind, hu, Option.isSome_none, Bool.false_or]
  conv_rhs =>
    rw [← Probability.PMF.uniformOfFintype_map_equiv (Equiv.addLeft p.2), PMF.bind_map]
  simp only [addLeft_apply, neg_add_cancel_left, Function.comp_def,
    Probability.PMF.uniformOfFintype_map_equiv]

private theorem idealRoundHandler4_forward_of_none (f₁ f₄ : G → G) (p : G × G)
    (cache : List ((Bool × G) × G)) (hu : cache.lookup (false, p.1 + f₁ p.2) = none) :
    idealRoundHandler4 f₁ f₄ (.forward p) (cache, false) =
      (PMF.uniformOfFintype G).bind fun v =>
        (PMF.uniformOfFintype G).bind fun w =>
          PMF.pure ((w, v + f₄ w),
            (((true, v), -(p.1 + f₁ p.2) + w) ::
              ((false, p.1 + f₁ p.2), -p.2 + v) :: cache,
              (cache.lookup (true, v)).isSome)) := by
  simp only [idealRoundHandler4, hu, Option.isSome_none, Bool.false_or,
    Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure]
  rw [← Probability.PMF.uniformOfFintype_map_equiv (forwardOutEquiv f₄),
    ← Probability.PMF.uniformOfFintype_prod, PMF.bind_map, PMF.bind_bind]
  simp only [forwardOutEquiv, Equiv.coe_fn_mk, add_sub_cancel_right,
    PMF.bind_map, Function.comp_def]

private theorem agree_roundHandler4_forward (f₁ f₄ : G → G) (p : G × G)
    (cache cache' : List ((Bool × G) × G)) (ans : G × G) :
    realRoundHandler4 f₁ f₄ (.forward p) (cache, false) (ans, (cache', false)) =
      idealRoundHandler4 f₁ f₄ (.forward p) (cache, false) (ans, (cache', false)) := by
  cases hu : cache.lookup (false, p.1 + f₁ p.2) with
  | some y₂₀ =>
    have hreal0 :
        realRoundHandler4 f₁ f₄ (.forward p) (cache, false) (ans, (cache', false)) = 0 := by
      refine (PMF.apply_eq_zero_iff _ _).mpr fun hmem => ?_
      simp only [realRoundHandler4, Probability.PMF.monad_bind_eq_bind,
        Probability.PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff,
        PMF.mem_support_pure_iff] at hmem
      obtain ⟨⟨y₂, c₁⟩, -, ⟨y₃, c₂⟩, -, heq⟩ := hmem
      have h1 := congrArg (fun x => x.2.2) heq
      simp [hu] at h1
    have hideal0 :
        idealRoundHandler4 f₁ f₄ (.forward p) (cache, false) (ans, (cache', false)) = 0 := by
      refine (PMF.apply_eq_zero_iff _ _).mpr fun hmem => ?_
      simp only [idealRoundHandler4, Probability.PMF.monad_bind_eq_bind,
        Probability.PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff,
        PMF.mem_support_pure_iff] at hmem
      obtain ⟨wz, -, heq⟩ := hmem
      have h1 := congrArg (fun x => x.2.2) heq
      simp [hu] at h1
    rw [hreal0, hideal0]
  | none =>
    rw [realRoundHandler4_forward_of_none f₁ f₄ p cache hu,
      idealRoundHandler4_forward_of_none f₁ f₄ p cache hu, PMF.bind_apply, PMF.bind_apply]
    refine tsum_congr fun v => congrArg (_ * ·) ?_
    cases hv : cache.lookup (true, v) with
    | some y₃₀ =>
      simp only [Option.isSome_some]
      have h1 :
          ((memoize (fun _ : Bool × G => PMF.uniformOfFintype G) (true, v)
            (((false, p.1 + f₁ p.2), -p.2 + v) :: cache)).bind fun x =>
              PMF.pure ((p.1 + f₁ p.2 + x.1, v + f₄ (p.1 + f₁ p.2 + x.1)), (x.2, true)))
            (ans, (cache', false)) = 0 := by
        refine (PMF.apply_eq_zero_iff _ _).mpr fun hmem => ?_
        rw [PMF.mem_support_bind_iff] at hmem
        obtain ⟨⟨y₃, c₂⟩, -, hmem'⟩ := hmem
        rw [PMF.mem_support_pure_iff] at hmem'
        exact Bool.noConfusion (congrArg (fun x => x.2.2) hmem')
      have h2 :
          ((PMF.uniformOfFintype G).bind fun w =>
            PMF.pure ((w, v + f₄ w),
              (((true, v), -(p.1 + f₁ p.2) + w) ::
                ((false, p.1 + f₁ p.2), -p.2 + v) :: cache, true)))
            (ans, (cache', false)) = 0 := by
        refine (PMF.apply_eq_zero_iff _ _).mpr fun hmem => ?_
        rw [PMF.mem_support_bind_iff] at hmem
        obtain ⟨w, -, hmem'⟩ := hmem
        rw [PMF.mem_support_pure_iff] at hmem'
        exact Bool.noConfusion (congrArg (fun x => x.2.2) hmem')
      rw [h1, h2]
    | none =>
      simp only [Option.isSome_none]
      have hv' : (((false, p.1 + f₁ p.2), -p.2 + v) :: cache).lookup (true, v) = none := by
        rw [lookup_true_cons_false, hv]
      rw [memoize_of_none _ _ _ hv']
      simp only [Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
        PMF.bind_bind, PMF.pure_bind]
      have heq_w :
          (PMF.uniformOfFintype G).bind (fun y₃ =>
            PMF.pure ((p.1 + f₁ p.2 + y₃, v + f₄ (p.1 + f₁ p.2 + y₃)),
              (((true, v), y₃) :: ((false, p.1 + f₁ p.2), -p.2 + v) :: cache, false))) =
          (PMF.uniformOfFintype G).bind (fun w =>
            PMF.pure ((w, v + f₄ w),
              (((true, v), -(p.1 + f₁ p.2) + w) ::
                ((false, p.1 + f₁ p.2), -p.2 + v) :: cache, false))) := by
        conv_rhs =>
          rw [← Probability.PMF.uniformOfFintype_map_equiv (Equiv.addLeft (p.1 + f₁ p.2)),
            PMF.bind_map]
        simp only [addLeft_apply, neg_add_cancel_left, Function.comp_def]
      exact DFunLike.congr_fun heq_w (ans, (cache', false))

private theorem realRoundHandler4_inverse_of_none (f₁ f₄ : G → G) (wz : G × G)
    (cache : List ((Bool × G) × G)) (hv : cache.lookup (true, wz.2 - f₄ wz.1) = none) :
    realRoundHandler4 f₁ f₄ (.inverse wz) (cache, false) =
      (PMF.uniformOfFintype G).bind fun u =>
        (memoize (fun _ : Bool × G => PMF.uniformOfFintype G) (false, u)
          (((true, wz.2 - f₄ wz.1), -u + wz.1) :: cache)).bind fun x =>
            PMF.pure ((u - f₁ (wz.2 - f₄ wz.1 - x.1), wz.2 - f₄ wz.1 - x.1),
              (x.2, (cache.lookup (false, u)).isSome)) := by
  simp only [realRoundHandler4, memoize_of_none _ _ _ hv,
    Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
    PMF.bind_bind, PMF.pure_bind, hv, Option.isSome_none, Bool.false_or]
  conv_rhs =>
    rw [← Probability.PMF.uniformOfFintype_map_equiv (subLeftEquiv wz.1), PMF.bind_map]
  simp only [subLeftEquiv_apply, neg_sub, sub_add_cancel, Function.comp_def,
    Probability.PMF.uniformOfFintype_map_equiv]

private theorem idealRoundHandler4_inverse_of_none (f₁ f₄ : G → G) (wz : G × G)
    (cache : List ((Bool × G) × G)) (hv : cache.lookup (true, wz.2 - f₄ wz.1) = none) :
    idealRoundHandler4 f₁ f₄ (.inverse wz) (cache, false) =
      (PMF.uniformOfFintype G).bind fun u =>
        (PMF.uniformOfFintype G).bind fun r =>
          PMF.pure ((u - f₁ r, r),
            (((false, u), -r + (wz.2 - f₄ wz.1)) ::
              ((true, wz.2 - f₄ wz.1), -u + wz.1) :: cache,
              (cache.lookup (false, u)).isSome)) := by
  simp only [idealRoundHandler4, hv, Option.isSome_none, Bool.false_or,
    Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure]
  rw [← Probability.PMF.uniformOfFintype_map_equiv (inverseOutEquiv f₁),
    ← Probability.PMF.uniformOfFintype_prod, PMF.bind_map, PMF.bind_bind]
  simp only [inverseOutEquiv, Equiv.coe_fn_mk, sub_add_cancel,
    PMF.bind_map, Function.comp_def]

private theorem agree_roundHandler4_inverse (f₁ f₄ : G → G) (wz : G × G)
    (cache cache' : List ((Bool × G) × G)) (ans : G × G) :
    realRoundHandler4 f₁ f₄ (.inverse wz) (cache, false) (ans, (cache', false)) =
      idealRoundHandler4 f₁ f₄ (.inverse wz) (cache, false) (ans, (cache', false)) := by
  cases hv : cache.lookup (true, wz.2 - f₄ wz.1) with
  | some y₃₀ =>
    have hreal0 :
        realRoundHandler4 f₁ f₄ (.inverse wz) (cache, false) (ans, (cache', false)) = 0 := by
      refine (PMF.apply_eq_zero_iff _ _).mpr fun hmem => ?_
      simp only [realRoundHandler4, Probability.PMF.monad_bind_eq_bind,
        Probability.PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff,
        PMF.mem_support_pure_iff] at hmem
      obtain ⟨⟨y₃, c₁⟩, -, ⟨y₂, c₂⟩, -, heq⟩ := hmem
      have h1 := congrArg (fun x => x.2.2) heq
      simp [hv] at h1
    have hideal0 :
        idealRoundHandler4 f₁ f₄ (.inverse wz) (cache, false) (ans, (cache', false)) = 0 := by
      refine (PMF.apply_eq_zero_iff _ _).mpr fun hmem => ?_
      simp only [idealRoundHandler4, Probability.PMF.monad_bind_eq_bind,
        Probability.PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff,
        PMF.mem_support_pure_iff] at hmem
      obtain ⟨p, -, heq⟩ := hmem
      have h1 := congrArg (fun x => x.2.2) heq
      simp [hv] at h1
    rw [hreal0, hideal0]
  | none =>
    rw [realRoundHandler4_inverse_of_none f₁ f₄ wz cache hv,
      idealRoundHandler4_inverse_of_none f₁ f₄ wz cache hv, PMF.bind_apply, PMF.bind_apply]
    refine tsum_congr fun u => congrArg (_ * ·) ?_
    cases hu : cache.lookup (false, u) with
    | some y₂₀ =>
      simp only [Option.isSome_some]
      have h1 :
          ((memoize (fun _ : Bool × G => PMF.uniformOfFintype G) (false, u)
            (((true, wz.2 - f₄ wz.1), -u + wz.1) :: cache)).bind fun x =>
              PMF.pure ((u - f₁ (wz.2 - f₄ wz.1 - x.1), wz.2 - f₄ wz.1 - x.1), (x.2, true)))
            (ans, (cache', false)) = 0 := by
        refine (PMF.apply_eq_zero_iff _ _).mpr fun hmem => ?_
        rw [PMF.mem_support_bind_iff] at hmem
        obtain ⟨⟨y₂, c₂⟩, -, hmem'⟩ := hmem
        rw [PMF.mem_support_pure_iff] at hmem'
        exact Bool.noConfusion (congrArg (fun x => x.2.2) hmem')
      have h2 :
          ((PMF.uniformOfFintype G).bind fun r =>
            PMF.pure ((u - f₁ r, r),
              (((false, u), -r + (wz.2 - f₄ wz.1)) ::
                ((true, wz.2 - f₄ wz.1), -u + wz.1) :: cache, true)))
            (ans, (cache', false)) = 0 := by
        refine (PMF.apply_eq_zero_iff _ _).mpr fun hmem => ?_
        rw [PMF.mem_support_bind_iff] at hmem
        obtain ⟨r, -, hmem'⟩ := hmem
        rw [PMF.mem_support_pure_iff] at hmem'
        exact Bool.noConfusion (congrArg (fun x => x.2.2) hmem')
      rw [h1, h2]
    | none =>
      simp only [Option.isSome_none]
      have hu' : (((true, wz.2 - f₄ wz.1), -u + wz.1) :: cache).lookup (false, u) = none := by
        rw [lookup_false_cons_true, hu]
      rw [memoize_of_none _ _ _ hu']
      simp only [Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
        PMF.bind_bind, PMF.pure_bind]
      have heq_r :
          (PMF.uniformOfFintype G).bind (fun y₂ =>
            PMF.pure ((u - f₁ (wz.2 - f₄ wz.1 - y₂), wz.2 - f₄ wz.1 - y₂),
              (((false, u), y₂) :: ((true, wz.2 - f₄ wz.1), -u + wz.1) :: cache, false))) =
          (PMF.uniformOfFintype G).bind (fun r =>
            PMF.pure ((u - f₁ r, r),
              (((false, u), -r + (wz.2 - f₄ wz.1)) ::
                ((true, wz.2 - f₄ wz.1), -u + wz.1) :: cache, false))) := by
        conv_rhs =>
          rw [← Probability.PMF.uniformOfFintype_map_equiv (subLeftEquiv (wz.2 - f₄ wz.1)),
            PMF.bind_map]
        simp only [subLeftEquiv_apply, neg_sub, sub_add_cancel, Function.comp_def]
      exact DFunLike.congr_fun heq_r (ans, (cache', false))

/-- The bidirectional real and ideal 4-round handlers agree until a Round-2 (`u`) or Round-3 (`v`)
input collision occurs. -/
private theorem identicalUntilBad_roundHandler4 (f₁ f₄ : G → G) :
    OracleComp.IdenticalUntilBad (realRoundHandler4 f₁ f₄) (idealRoundHandler4 f₁ f₄)
      fun st => st.2 = true where
  agree q st hst ans st' hst' := by
    rcases st with ⟨cache, bad⟩
    rcases st' with ⟨cache', bad'⟩
    have hbad : bad = false := Bool.eq_false_iff.mpr hst
    have hbad' : bad' = false := Bool.eq_false_iff.mpr hst'
    subst hbad hbad'
    cases q with
    | forward p => exact agree_roundHandler4_forward f₁ f₄ p cache cache' ans
    | inverse wz => exact agree_roundHandler4_inverse f₁ f₄ wz cache cache' ans
  absorb_first q st hst x hx := by
    rcases st with ⟨cache, bad⟩
    simp only at hst
    subst hst
    cases q with
    | forward p =>
      simp only [realRoundHandler4, Probability.PMF.monad_bind_eq_bind,
        Probability.PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff,
        PMF.mem_support_pure_iff] at hx
      obtain ⟨⟨y₂, c₁⟩, -, ⟨y₃, c₂⟩, -, rfl⟩ := hx
      simp
    | inverse wz =>
      simp only [realRoundHandler4, Probability.PMF.monad_bind_eq_bind,
        Probability.PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff,
        PMF.mem_support_pure_iff] at hx
      obtain ⟨⟨y₃, c₁⟩, -, ⟨y₂, c₂⟩, -, rfl⟩ := hx
      simp
  absorb_second q st hst x hx := by
    rcases st with ⟨cache, bad⟩
    simp only at hst
    subst hst
    cases q with
    | forward p =>
      simp only [idealRoundHandler4, Probability.PMF.monad_bind_eq_bind,
        Probability.PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff,
        PMF.mem_support_pure_iff] at hx
      obtain ⟨wz, -, rfl⟩ := hx
      simp
    | inverse wz =>
      simp only [idealRoundHandler4, Probability.PMF.monad_bind_eq_bind,
        Probability.PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff,
        PMF.mem_support_pure_iff] at hx
      obtain ⟨p, -, rfl⟩ := hx
      simp

/-- Swap each `(p, wz)` entry in a permutation cache to `(wz.swap, p)` so Round-4 collisions
become Round-1 `hasUCollision` under `w ↦ -f₄ w`. -/
private def swapCache (qc : List ((G × G) × (G × G))) : List ((G × G) × (G × G)) :=
  qc.map fun e => (e.2.swap, e.1)

/-- Whether the query cache `qc` contains two entries with the same Round-3 input
`v = wz.2 - f₄ wz.1`. -/
private def hasVCollision4 (f₄ : G → G) (qc : List ((G × G) × (G × G))) : Bool :=
  hasUCollision (fun w => -f₄ w) (swapCache qc)

/-- Whether the query cache `qc` contains a Round-1 (`u`) collision or a Round-4 (`v`)
collision. -/
private def hasCollision4 (f₁ f₄ : G → G) (qc : List ((G × G) × (G × G))) : Bool :=
  hasUCollision f₁ qc || hasVCollision4 f₄ qc

/-- Invariant relating the internal Round-2/Round-3 cache and bad flag `(cache, bad)` of
`idealRoundHandler4 f₁ f₄` to the deduplication query cache `qc`. -/
private structure SimInv4 (f₁ f₄ : G → G) (qc : RandomPermutation.Cache (G × G))
    (st : List ((Bool × G) × G) × Bool) : Prop where
  lookup_false (u : G) :
    (st.1.lookup (false, u)).isSome = qc.any (fun e => decide (u = e.1.1 + f₁ e.1.2))
  lookup_true (v : G) :
    (st.1.lookup (true, v)).isSome =
      (swapCache qc).any (fun e => decide (v = e.1.1 + -f₄ e.1.2))
  bad_eq : st.2 = hasCollision4 f₁ f₄ qc

omit [Fintype G] [Nonempty G] in
private theorem simInv4_nil (f₁ f₄ : G → G) : SimInv4 f₁ f₄ [] ([], false) where
  lookup_false _ := rfl
  lookup_true _ := rfl
  bad_eq := rfl

omit [AddGroup G] [Fintype G] [Nonempty G] in
private theorem isSome_lookup_false_cons₂ (u v y₂ y₃ u' : G)
    (cache : List ((Bool × G) × G)) :
    ((((true, v), y₃) :: ((false, u), y₂) :: cache).lookup (false, u')).isSome =
      (decide (u' = u) || (cache.lookup (false, u')).isSome) := by
  rw [lookup_false_cons_true, List.lookup_cons]
  by_cases h : u' = u
  · subst h; simp
  · have hff : ((false, u') == (false, u)) = false :=
      beq_eq_false_iff_ne.mpr fun heq => h (Prod.mk.inj heq).2
    simp [hff, h]

omit [AddGroup G] [Fintype G] [Nonempty G] in
private theorem isSome_lookup_true_cons₂ (u v y₂ y₃ v' : G)
    (cache : List ((Bool × G) × G)) :
    ((((true, v), y₃) :: ((false, u), y₂) :: cache).lookup (true, v')).isSome =
      (decide (v' = v) || (cache.lookup (true, v')).isSome) := by
  rw [List.lookup_cons]
  by_cases h : v' = v
  · subst h; simp
  · have htt : ((true, v') == (true, v)) = false :=
      beq_eq_false_iff_ne.mpr fun heq => h (Prod.mk.inj heq).2
    rw [htt, lookup_true_cons_false]
    simp [h]

omit [AddGroup G] [Fintype G] [Nonempty G] in
private theorem isSome_lookup_false_cons₂' (u v y₂ y₃ u' : G)
    (cache : List ((Bool × G) × G)) :
    ((((false, u), y₂) :: ((true, v), y₃) :: cache).lookup (false, u')).isSome =
      (decide (u' = u) || (cache.lookup (false, u')).isSome) := by
  rw [List.lookup_cons]
  by_cases h : u' = u
  · subst h; simp
  · have hff : ((false, u') == (false, u)) = false :=
      beq_eq_false_iff_ne.mpr fun heq => h (Prod.mk.inj heq).2
    rw [hff, lookup_false_cons_true]
    simp [h]

omit [AddGroup G] [Fintype G] [Nonempty G] in
private theorem isSome_lookup_true_cons₂' (u v y₂ y₃ v' : G)
    (cache : List ((Bool × G) × G)) :
    ((((false, u), y₂) :: ((true, v), y₃) :: cache).lookup (true, v')).isSome =
      (decide (v' = v) || (cache.lookup (true, v')).isSome) := by
  rw [lookup_true_cons_false, List.lookup_cons]
  by_cases h : v' = v
  · subst h; simp
  · have htt : ((true, v') == (true, v)) = false :=
      beq_eq_false_iff_ne.mpr fun heq => h (Prod.mk.inj heq).2
    simp [htt, h]

omit [Fintype G] [Nonempty G] in
private theorem SimInv4.forward {f₁ f₄ : G → G} {qc : RandomPermutation.Cache (G × G)}
    {st : List ((Bool × G) × G) × Bool} (hst : SimInv4 f₁ f₄ qc st) (p wz : G × G) :
    let u := p.1 + f₁ p.2
    let v := wz.2 - f₄ wz.1
    SimInv4 f₁ f₄ ((p, wz) :: qc)
      (((true, v), -u + wz.1) :: ((false, u), -p.2 + v) :: st.1,
        (st.2 || (st.1.lookup (false, u)).isSome) || (st.1.lookup (true, v)).isSome) where
  lookup_false u' := by
    simp [isSome_lookup_false_cons₂, hst.lookup_false]
  lookup_true v' := by
    simp [isSome_lookup_true_cons₂, hst.lookup_true, swapCache, sub_eq_add_neg]
  bad_eq := by
    simp only [hst.bad_eq, hst.lookup_false, hst.lookup_true, hasCollision4, hasUCollision,
      hasVCollision4, swapCache, List.map_cons, Prod.swap, sub_eq_add_neg]
    ac_rfl

omit [Fintype G] [Nonempty G] in
private theorem SimInv4.inverse {f₁ f₄ : G → G} {qc : RandomPermutation.Cache (G × G)}
    {st : List ((Bool × G) × G) × Bool} (hst : SimInv4 f₁ f₄ qc st) (p wz : G × G) :
    let u := p.1 + f₁ p.2
    let v := wz.2 - f₄ wz.1
    SimInv4 f₁ f₄ ((p, wz) :: qc)
      (((false, u), -p.2 + v) :: ((true, v), -u + wz.1) :: st.1,
        (st.2 || (st.1.lookup (true, v)).isSome) || (st.1.lookup (false, u)).isSome) where
  lookup_false u' := by
    simp [isSome_lookup_false_cons₂', hst.lookup_false]
  lookup_true v' := by
    simp [isSome_lookup_true_cons₂', hst.lookup_true, swapCache, sub_eq_add_neg]
  bad_eq := by
    simp only [hst.bad_eq, hst.lookup_false, hst.lookup_true, hasCollision4, hasUCollision,
      hasVCollision4, swapCache, List.map_cons, Prod.swap, sub_eq_add_neg]
    ac_rfl

omit [AddGroup G] in
private theorem forgetfulAnswer_forward_of_some {p wz : G × G}
    {qc : RandomPermutation.Cache (G × G)} (h : qc.lookup p = some wz) :
    RandomPermutation.forgetfulAnswer (.forward p) qc = PMF.pure (wz, qc) := by
  simp [RandomPermutation.forgetfulAnswer, h]

omit [AddGroup G] in
private theorem forgetfulAnswer_forward_of_none {p : G × G}
    {qc : RandomPermutation.Cache (G × G)} (h : qc.lookup p = none) :
    RandomPermutation.forgetfulAnswer (.forward p) qc =
      (PMF.uniformOfFintype (G × G)).map fun wz => (wz, (p, wz) :: qc) := by
  simp [RandomPermutation.forgetfulAnswer, h]

omit [AddGroup G] in
private theorem forgetfulAnswer_inverse_of_some {wz p : G × G}
    {qc : RandomPermutation.Cache (G × G)} (h : RandomPermutation.invLookup qc wz = some p) :
    RandomPermutation.forgetfulAnswer (.inverse wz) qc = PMF.pure (p, qc) := by
  simp [RandomPermutation.forgetfulAnswer, h]

omit [AddGroup G] in
private theorem forgetfulAnswer_inverse_of_none {wz : G × G}
    {qc : RandomPermutation.Cache (G × G)} (h : RandomPermutation.invLookup qc wz = none) :
    RandomPermutation.forgetfulAnswer (.inverse wz) qc =
      (PMF.uniformOfFintype (G × G)).map fun p => (p, (p, wz) :: qc) := by
  simp [RandomPermutation.forgetfulAnswer, h]

private theorem map_run_idealRoundHandler4_bidirDedupStep {α : Type} (f₁ f₄ : G → G)
    (program : OracleComp (RandomPermutation.PermOracleSpec (G × G)) α)
    {qc : RandomPermutation.Cache (G × G)} {st : List ((Bool × G) × G) × Bool}
    (hst : SimInv4 f₁ f₄ qc st) :
    (((OracleComp.interpret (idealRoundHandler4 f₁ f₄)
      ((OracleComp.interpret bidirDedupStep program).run qc)).run st).map
        fun ((a, qc'), st') => ((a, qc'), st'.2)) =
      ((OracleComp.interpret RandomPermutation.forgetfulAnswer program).run qc).map
        (fun (a, qc') => ((a, qc'), hasCollision4 f₁ f₄ qc')) := by
  induction program using PFunctor.FreeM.induction generalizing qc st with
  | pure a =>
    simp [PMF.pure_map, hst.bad_eq]
  | lift_bind q cont ih =>
    change (((OracleComp.interpret (idealRoundHandler4 f₁ f₄)
      ((OracleComp.interpret bidirDedupStep (OracleComp.query q >>= cont)).run qc)).run st).map
        fun ((a, qc'), st') => ((a, qc'), st'.2)) =
      ((OracleComp.interpret RandomPermutation.forgetfulAnswer
        (OracleComp.query q >>= cont)).run qc).map _
    simp only [OracleComp.interpret_bind, OracleComp.interpret_query, StateT.run_bind]
    change ((((OracleComp.interpret (idealRoundHandler4 f₁ f₄) (bidirDedupStep q qc)).run st).bind
      fun p_1 =>
        (OracleComp.interpret (idealRoundHandler4 f₁ f₄)
          ((OracleComp.interpret bidirDedupStep (cont p_1.1.1)).run p_1.1.2)).run p_1.2).map
        fun ((a, qc'), st') => ((a, qc'), st'.2)) =
      (((RandomPermutation.forgetfulAnswer q qc).bind fun p =>
        (OracleComp.interpret RandomPermutation.forgetfulAnswer (cont p.1)).run p.2).map
        fun (a, qc') => ((a, qc'), hasCollision4 f₁ f₄ qc'))
    cases q with
    | forward p =>
      cases h : qc.lookup p with
      | some wz =>
        rw [bidirDedupStep_forward_of_some h, forgetfulAnswer_forward_of_some h]
        simp only [OracleComp.interpret_pure, StateT.run_pure,
          Probability.PMF.monad_pure_eq_pure, PMF.pure_bind]
        exact ih wz hst
      | none =>
        rw [bidirDedupStep_forward_of_none h, forgetfulAnswer_forward_of_none h]
        simp only [OracleComp.interpret_bind, OracleComp.interpret_query,
          OracleComp.interpret_pure, StateT.run_bind, StateT.run_pure,
          Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
          PMF.bind_bind, PMF.pure_bind, PMF.map_bind, PMF.bind_map]
        simp only [StateT.run, idealRoundHandler4, Probability.PMF.monad_bind_eq_bind,
          Probability.PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
        exact congrArg (PMF.bind _) (funext fun wz => ih wz (hst.forward p wz))
    | inverse wz =>
      cases h : RandomPermutation.invLookup qc wz with
      | some p =>
        rw [bidirDedupStep_inverse_of_some h, forgetfulAnswer_inverse_of_some h]
        simp only [OracleComp.interpret_pure, StateT.run_pure,
          Probability.PMF.monad_pure_eq_pure, PMF.pure_bind]
        exact ih p hst
      | none =>
        rw [bidirDedupStep_inverse_of_none h, forgetfulAnswer_inverse_of_none h]
        simp only [OracleComp.interpret_bind, OracleComp.interpret_query,
          OracleComp.interpret_pure, StateT.run_bind, StateT.run_pure,
          Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
          PMF.bind_bind, PMF.pure_bind, PMF.map_bind, PMF.bind_map]
        simp only [StateT.run, idealRoundHandler4, Probability.PMF.monad_bind_eq_bind,
          Probability.PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
        exact congrArg (PMF.bind _) (funext fun p => ih p (hst.inverse p wz))

private theorem map_fst_run_idealRoundHandler4 (f₁ f₄ : G → G)
    (program : OracleComp (RandomPermutation.PermOracleSpec (G × G)) Bool) :
    (((OracleComp.interpret (idealRoundHandler4 f₁ f₄) (bidirDedup program)).run
      ([], false)).map fun x => x.1.1) =
    ((OracleComp.interpret RandomPermutation.forgetfulAnswer program).run []).map Prod.fst := by
  have h := congrArg (PMF.map fun x => x.1.1)
    (map_run_idealRoundHandler4_bidirDedupStep f₁ f₄ program (simInv4_nil f₁ f₄))
  simpa only [bidirDedup, PMF.map_comp, Function.comp_def] using h

private theorem toOuterMeasure_bad_idealRoundHandler4 (f₁ f₄ : G → G)
    (program : OracleComp (RandomPermutation.PermOracleSpec (G × G)) Bool) :
    ((OracleComp.interpret (idealRoundHandler4 f₁ f₄) (bidirDedup program)).run
      ([], false)).toOuterMeasure {x | x.2.2 = true} =
    ((OracleComp.interpret RandomPermutation.forgetfulAnswer program).run []).toOuterMeasure
      {x | hasCollision4 f₁ f₄ x.2 = true} := by
  rw [bidirDedup]
  have h := congrArg (fun d => PMF.toOuterMeasure d {x | x.2 = true})
    (map_run_idealRoundHandler4_bidirDedupStep f₁ f₄ program (simInv4_nil f₁ f₄))
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply] at h
  exact h


omit [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] in
private theorem pairwise_swapCache_of_pairwise_snd {qc : List ((G × G) × (G × G))}
    (hp2 : qc.Pairwise (fun a b => a.2 ≠ b.2)) :
    (swapCache qc).Pairwise (fun a b => a.1 ≠ b.1) := by
  rw [swapCache, List.pairwise_map]
  exact hp2.imp fun h heq => h (Prod.swap_injective heq)

private theorem toOuterMeasure_hasVCollision4_le {qc : List ((G × G) × (G × G))}
    (hp2 : qc.Pairwise (fun a b => a.2 ≠ b.2)) :
    (PMF.uniformOfFintype (G → G)).toOuterMeasure {f₄ | hasVCollision4 f₄ qc = true} ≤
      qc.length.choose 2 * (Fintype.card G : ℝ≥0∞)⁻¹ := by
  have h := toOuterMeasure_hasUCollision_le isDeltaUniversalHash_neg_uniformOfFintype
    (pairwise_swapCache_of_pairwise_snd hp2)
  simpa only [hasVCollision4, swapCache, List.length_map] using h

omit [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] in
private theorem tsum_toOuterMeasure_of_pointwise_le {α β : Type} (μ : PMF α) (d : PMF β)
    (P : α → β → Prop) (M : ℝ≥0∞) (hM : ∀ y, μ.toOuterMeasure {a | P a y} ≤ M) :
    (∑' a, μ a * d.toOuterMeasure {y | P a y}) ≤ M := by
  classical
  simp only [PMF.toOuterMeasure_apply]
  have hcomm :
      (∑' a, μ a * ∑' y, {y | P a y}.indicator d y) =
        ∑' y, d y * ∑' a, {a | P a y}.indicator μ a := by
    simp only [← ENNReal.tsum_mul_left]
    rw [tsum_comm]
    refine tsum_congr fun y => tsum_congr fun a => ?_
    by_cases h : P a y
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, mul_comm]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero, mul_zero]
  rw [hcomm]
  calc ∑' y, d y * ∑' a, {a | P a y}.indicator μ a
      ≤ ∑' y, d y * M :=
        tsum_le_tsum fun y => mul_le_mul_of_nonneg_left (by
          rw [← PMF.toOuterMeasure_apply]
          exact hM y) zero_le
    _ = M := by rw [ENNReal.tsum_mul_right, d.tsum_coe, one_mul]

/-- Local shorthand for a `Q`-bounded partial-bijection trace `c` with pairwise-distinct domain
and range entries. -/
private def IsGoodCache4 (Q : ℕ) (c : RandomPermutation.Cache (G × G)) : Prop :=
  c.Pairwise (fun x y => x.1 ≠ y.1) ∧ c.Pairwise (fun x y => x.2 ≠ y.2) ∧ c.length ≤ Q

private theorem tsum_uniform_toOuterMeasure_hasUCollision_le
    (d : PMF (Bool × RandomPermutation.Cache (G × G))) (Q : ℕ) :
    (∑' f₁ : G → G, PMF.uniformOfFintype (G → G) f₁ *
      d.toOuterMeasure
        {x | IsGoodCache4 Q x.2 ∧ hasUCollision f₁ x.2 = true}) ≤
      Q.choose 2 * (Fintype.card G : ℝ≥0∞)⁻¹ := by
  refine tsum_toOuterMeasure_of_pointwise_le (PMF.uniformOfFintype (G → G)) d
    (fun f₁ x => IsGoodCache4 Q x.2 ∧ hasUCollision f₁ x.2 = true) _ fun x => ?_
  by_cases hg : IsGoodCache4 Q x.2
  · have hsub :
        {f₁ : G → G | IsGoodCache4 Q x.2 ∧ hasUCollision f₁ x.2 = true} ⊆
          {f₁ : G → G | hasUCollision f₁ x.2 = true} := fun _ h => h.2
    exact (MeasureTheory.measure_mono hsub).trans
      ((toOuterMeasure_hasUCollision_le isDeltaUniversalHash_uniformOfFintype hg.1).trans
        (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.choose_le_choose 2 hg.2.2)) zero_le))
  · have hemp :
        {f₁ : G → G | IsGoodCache4 Q x.2 ∧ hasUCollision f₁ x.2 = true} = ∅ := by
      ext f₁
      simp [hg]
    simp [hemp]

private theorem tsum_uniform_toOuterMeasure_hasVCollision4_le
    (d : PMF (Bool × RandomPermutation.Cache (G × G))) (Q : ℕ) :
    (∑' f₄ : G → G, PMF.uniformOfFintype (G → G) f₄ *
      d.toOuterMeasure
        {x | IsGoodCache4 Q x.2 ∧ hasVCollision4 f₄ x.2 = true}) ≤
      Q.choose 2 * (Fintype.card G : ℝ≥0∞)⁻¹ := by
  refine tsum_toOuterMeasure_of_pointwise_le (PMF.uniformOfFintype (G → G)) d
    (fun f₄ x => IsGoodCache4 Q x.2 ∧ hasVCollision4 f₄ x.2 = true) _ fun x => ?_
  by_cases hg : IsGoodCache4 Q x.2
  · have hsub :
        {f₄ : G → G | IsGoodCache4 Q x.2 ∧ hasVCollision4 f₄ x.2 = true} ⊆
          {f₄ : G → G | hasVCollision4 f₄ x.2 = true} := fun _ h => h.2
    exact (MeasureTheory.measure_mono hsub).trans
      ((toOuterMeasure_hasVCollision4_le hg.2.1).trans
        (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.choose_le_choose 2 hg.2.2)) zero_le))
  · have hemp :
        {f₄ : G → G | IsGoodCache4 Q x.2 ∧ hasVCollision4 f₄ x.2 = true} = ∅ := by
      ext f₄
      simp [hg]
    simp [hemp]

private theorem toOuterMeasure_hasCollision4_le (f₁ f₄ : G → G)
    {prog : OracleComp (RandomPermutation.PermOracleSpec (G × G)) Bool} {Q : ℕ}
    (hQ : OracleComp.IsQueryBounded prog Q) :
    ((OracleComp.interpret RandomPermutation.forgetfulAnswer prog).run []).toOuterMeasure
      {x | hasCollision4 f₁ f₄ x.2 = true} ≤
    ((OracleComp.interpret RandomPermutation.forgetfulAnswer prog).run []).toOuterMeasure
      {x | IsGoodCache4 Q x.2 ∧ hasUCollision f₁ x.2 = true} +
    ((OracleComp.interpret RandomPermutation.forgetfulAnswer prog).run []).toOuterMeasure
      {x | IsGoodCache4 Q x.2 ∧ hasVCollision4 f₄ x.2 = true} +
    (Q.choose 2 : ℝ≥0∞) * (Fintype.card (G × G) : ℝ≥0∞)⁻¹ := by
  set d := (OracleComp.interpret RandomPermutation.forgetfulAnswer prog).run []
  have hgood :=
    RandomPermutation.toOuterMeasure_forgetfulAnswer_le_pairwise_and_length_le_add hQ
      (fun c => hasCollision4 f₁ f₄ c = true)
  have hunion :
      d.toOuterMeasure
          {x | (x.2.Pairwise (fun a b => a.1 ≠ b.1) ∧
            x.2.Pairwise (fun a b => a.2 ≠ b.2) ∧ x.2.length ≤ Q) ∧
            hasCollision4 f₁ f₄ x.2 = true} ≤
        d.toOuterMeasure {x | IsGoodCache4 Q x.2 ∧ hasUCollision f₁ x.2 = true} +
          d.toOuterMeasure
            {x | IsGoodCache4 Q x.2 ∧ hasVCollision4 f₄ x.2 = true} := by
    refine (MeasureTheory.measure_mono fun x hx => ?_).trans (MeasureTheory.measure_union_le _ _)
    simp only [Set.mem_ofPred_eq, hasCollision4, Bool.or_eq_true] at hx
    rcases hx with ⟨hg, hu | hv⟩
    · exact Or.inl ⟨hg, hu⟩
    · exact Or.inr ⟨hg, hv⟩
  exact hgood.trans (add_le_add hunion le_rfl)

private theorem tsum_uniform_toOuterMeasure_hasCollision4_le
    {prog : OracleComp (RandomPermutation.PermOracleSpec (G × G)) Bool} {Q : ℕ}
    (hQ : OracleComp.IsQueryBounded prog Q) :
    (∑' f₁ : G → G, PMF.uniformOfFintype (G → G) f₁ *
      ∑' f₄ : G → G, PMF.uniformOfFintype (G → G) f₄ *
        ((OracleComp.interpret RandomPermutation.forgetfulAnswer prog).run []).toOuterMeasure
          {x | hasCollision4 f₁ f₄ x.2 = true}) ≤
      2 * (Q.choose 2 : ℝ≥0∞) * (Fintype.card G : ℝ≥0∞)⁻¹ +
        (Q.choose 2 : ℝ≥0∞) * (Fintype.card (G × G) : ℝ≥0∞)⁻¹ := by
  set d := (OracleComp.interpret RandomPermutation.forgetfulAnswer prog).run []
  set unif := PMF.uniformOfFintype (G → G)
  have hinner (f₁ : G → G) :
      (∑' f₄, unif f₄ * d.toOuterMeasure {x | hasCollision4 f₁ f₄ x.2 = true}) ≤
        d.toOuterMeasure {x | IsGoodCache4 Q x.2 ∧ hasUCollision f₁ x.2 = true} +
          Q.choose 2 * (Fintype.card G : ℝ≥0∞)⁻¹ +
          (Q.choose 2 : ℝ≥0∞) * (Fintype.card (G × G) : ℝ≥0∞)⁻¹ := by
    calc ∑' f₄, unif f₄ * d.toOuterMeasure {x | hasCollision4 f₁ f₄ x.2 = true}
        ≤ ∑' f₄, unif f₄ *
          (d.toOuterMeasure
            {x | IsGoodCache4 Q x.2 ∧ hasUCollision f₁ x.2 = true} +
            d.toOuterMeasure
              {x | IsGoodCache4 Q x.2 ∧ hasVCollision4 f₄ x.2 = true} +
            (Q.choose 2 : ℝ≥0∞) * (Fintype.card (G × G) : ℝ≥0∞)⁻¹) :=
          tsum_le_tsum fun f₄ =>
            mul_le_mul_of_nonneg_left (toOuterMeasure_hasCollision4_le f₁ f₄ hQ) zero_le
      _ = d.toOuterMeasure
            {x | IsGoodCache4 Q x.2 ∧ hasUCollision f₁ x.2 = true} +
          (∑' f₄, unif f₄ * d.toOuterMeasure
            {x | IsGoodCache4 Q x.2 ∧ hasVCollision4 f₄ x.2 = true}) +
          (Q.choose 2 : ℝ≥0∞) * (Fintype.card (G × G) : ℝ≥0∞)⁻¹ := by
          simp only [mul_add, tsum_add, ENNReal.tsum_mul_right, unif.tsum_coe, one_mul]
      _ ≤ _ := add_le_add (add_le_add le_rfl (tsum_uniform_toOuterMeasure_hasVCollision4_le d Q))
          le_rfl
  calc ∑' f₁, unif f₁ * ∑' f₄, unif f₄ * d.toOuterMeasure {x | hasCollision4 f₁ f₄ x.2 = true}
      ≤ ∑' f₁, unif f₁ *
        (d.toOuterMeasure
           {x | IsGoodCache4 Q x.2 ∧ hasUCollision f₁ x.2 = true} +
          Q.choose 2 * (Fintype.card G : ℝ≥0∞)⁻¹ +
          (Q.choose 2 : ℝ≥0∞) * (Fintype.card (G × G) : ℝ≥0∞)⁻¹) :=
        tsum_le_tsum fun f₁ => mul_le_mul_of_nonneg_left (hinner f₁) zero_le
    _ = (∑' f₁, unif f₁ * d.toOuterMeasure
          {x | IsGoodCache4 Q x.2 ∧ hasUCollision f₁ x.2 = true}) +
        Q.choose 2 * (Fintype.card G : ℝ≥0∞)⁻¹ +
        (Q.choose 2 : ℝ≥0∞) * (Fintype.card (G × G) : ℝ≥0∞)⁻¹ := by
        simp only [mul_add, tsum_add, ENNReal.tsum_mul_right, unif.tsum_coe, one_mul]
    _ ≤ Q.choose 2 * (Fintype.card G : ℝ≥0∞)⁻¹ +
        Q.choose 2 * (Fintype.card G : ℝ≥0∞)⁻¹ +
        (Q.choose 2 : ℝ≥0∞) * (Fintype.card (G × G) : ℝ≥0∞)⁻¹ :=
        add_le_add (add_le_add (tsum_uniform_toOuterMeasure_hasUCollision_le d Q) le_rfl) le_rfl
    _ = 2 * (Q.choose 2 : ℝ≥0∞) * (Fintype.card G : ℝ≥0∞)⁻¹ +
        (Q.choose 2 : ℝ≥0∞) * (Fintype.card (G × G) : ℝ≥0∞)⁻¹ := by ring

private theorem feistel4StrongFixedGame_apply_le (f₁ f₄ : G → G)
    (program : OracleComp (fun _ : Bool × (G × G) => G × G) Bool) (b : Bool) :
    feistel4StrongFixedGame f₁ f₄ program b ≤
      (((OracleComp.interpret RandomPermutation.forgetfulAnswer
        (RandomPermutation.liftBoolProd program)).run []).map Prod.fst) b +
      ((OracleComp.interpret RandomPermutation.forgetfulAnswer
        (RandomPermutation.liftBoolProd program)).run []).toOuterMeasure
          {x | hasCollision4 f₁ f₄ x.2 = true} := by
  have h := (identicalUntilBad_roundHandler4 f₁ f₄).bind_apply_le
    (bidirDedup (RandomPermutation.liftBoolProd program)) ([], false)
    (fun x => PMF.pure x.1.1) b
  rw [(identicalUntilBad_roundHandler4 f₁ f₄).bad_eq,
    toOuterMeasure_bad_idealRoundHandler4] at h
  rw [feistel4StrongFixedGame_eq_realRoundHandler4, ← map_fst_run_idealRoundHandler4 f₁ f₄]
  exact h

private theorem forgetfulAnswer_apply_le_feistel4StrongFixedGame (f₁ f₄ : G → G)
    (program : OracleComp (fun _ : Bool × (G × G) => G × G) Bool) (b : Bool) :
    (((OracleComp.interpret RandomPermutation.forgetfulAnswer
      (RandomPermutation.liftBoolProd program)).run []).map Prod.fst) b ≤
    feistel4StrongFixedGame f₁ f₄ program b +
      ((OracleComp.interpret RandomPermutation.forgetfulAnswer
        (RandomPermutation.liftBoolProd program)).run []).toOuterMeasure
          {x | hasCollision4 f₁ f₄ x.2 = true} := by
  have h := (identicalUntilBad_roundHandler4 f₁ f₄).symm.bind_apply_le
    (bidirDedup (RandomPermutation.liftBoolProd program)) ([], false)
    (fun x => PMF.pure x.1.1) b
  rw [toOuterMeasure_bad_idealRoundHandler4] at h
  rw [feistel4StrongFixedGame_eq_realRoundHandler4, ← map_fst_run_idealRoundHandler4 f₁ f₄]
  exact h

omit [AddGroup G] [Nonempty G] in
private theorem idealStrongGame_eq_bind_liftBoolProd
    (program : OracleComp (fun _ : Bool × (G × G) => G × G) Bool) :
    idealStrongGame program =
      ((PMF.uniformOfFintype (Equiv.Perm (G × G))).bind fun π =>
        OracleComp.interpret (fun q => PMF.pure (RandomPermutation.evalPerm π q))
          (RandomPermutation.liftBoolProd program)) := by
  simp only [idealStrongGame, Probability.PMF.monad_bind_eq_bind,
    interpret_feistelStrongOracle_eq_liftBoolProd]

/-- **4-round strong Luby–Rackoff theorem in `ℝ≥0∞` (one-sided)**: for any adaptive
bidirectional program making at most `Q` forward or inverse queries,
`feistel4StrongRandomRoundsGame` accepts with probability at most `idealStrongGame` plus
`2 * Q.choose 2 * |G|⁻¹ + 2 * Q.choose 2 * |G × G|⁻¹`. -/
theorem feistel4StrongRandomRoundsGame_apply_le
    {program : OracleComp (fun _ : Bool × (G × G) => G × G) Bool} {Q : ℕ}
    (hQ : OracleComp.IsQueryBounded program Q) (b : Bool) :
    feistel4StrongRandomRoundsGame program b ≤
      idealStrongGame program b +
        (2 * (Q.choose 2 : ℝ≥0∞) * (Fintype.card G : ℝ≥0∞)⁻¹ +
          2 * (Q.choose 2 : ℝ≥0∞) * (Fintype.card (G × G) : ℝ≥0∞)⁻¹) := by
  set prog := RandomPermutation.liftBoolProd program
  have hQ' := RandomPermutation.isQueryBounded_liftBoolProd hQ
  set forgetVal := (((OracleComp.interpret RandomPermutation.forgetfulAnswer prog).run []).map
    Prod.fst) b
  set unif := PMF.uniformOfFintype (G → G)
  rw [feistel4StrongRandomRoundsGame_eq_bind_fixed, Probability.PMF.monad_bind_eq_bind,
    PMF.bind_apply]
  have hstep :
      (∑' f₁, unif f₁ * (unif.bind fun f₄ => feistel4StrongFixedGame f₁ f₄ program) b) ≤
        forgetVal + (2 * (Q.choose 2 : ℝ≥0∞) * (Fintype.card G : ℝ≥0∞)⁻¹ +
          (Q.choose 2 : ℝ≥0∞) * (Fintype.card (G × G) : ℝ≥0∞)⁻¹) := by
    simp only [PMF.bind_apply]
    calc ∑' f₁, unif f₁ * ∑' f₄, unif f₄ * feistel4StrongFixedGame f₁ f₄ program b
        ≤ ∑' f₁, unif f₁ * ∑' f₄, unif f₄ *
          (forgetVal +
            ((OracleComp.interpret RandomPermutation.forgetfulAnswer prog).run []).toOuterMeasure
              {x | hasCollision4 f₁ f₄ x.2 = true}) :=
          tsum_le_tsum fun f₁ => mul_le_mul_of_nonneg_left
            (tsum_le_tsum fun f₄ => mul_le_mul_of_nonneg_left
              (feistel4StrongFixedGame_apply_le f₁ f₄ program b) zero_le) zero_le
      _ = forgetVal + ∑' f₁, unif f₁ * ∑' f₄, unif f₄ *
            ((OracleComp.interpret RandomPermutation.forgetfulAnswer prog).run []).toOuterMeasure
              {x | hasCollision4 f₁ f₄ x.2 = true} := by
          simp only [mul_add, tsum_add, ENNReal.tsum_mul_right, unif.tsum_coe, one_mul]
      _ ≤ _ := add_le_add le_rfl (tsum_uniform_toOuterMeasure_hasCollision4_le hQ')
  have hperm := RandomPermutation.forgetfulAnswer_bind_apply_le_uniformPerm hQ' PMF.pure b
  simp only [Probability.PMF.monad_bind_eq_bind, PMF.bind_pure] at hperm
  rw [← idealStrongGame_eq_bind_liftBoolProd] at hperm
  calc (∑' f₁, unif f₁ * (unif.bind fun f₄ => feistel4StrongFixedGame f₁ f₄ program) b)
      ≤ (idealStrongGame program b +
          (Q.choose 2 : ℝ≥0∞) * (Fintype.card (G × G) : ℝ≥0∞)⁻¹) +
        (2 * (Q.choose 2 : ℝ≥0∞) * (Fintype.card G : ℝ≥0∞)⁻¹ +
          (Q.choose 2 : ℝ≥0∞) * (Fintype.card (G × G) : ℝ≥0∞)⁻¹) :=
        hstep.trans (add_le_add hperm le_rfl)
    _ = idealStrongGame program b +
        (2 * (Q.choose 2 : ℝ≥0∞) * (Fintype.card G : ℝ≥0∞)⁻¹ +
          2 * (Q.choose 2 : ℝ≥0∞) * (Fintype.card (G × G) : ℝ≥0∞)⁻¹) := by ring

/-- **Reverse 4-round strong Luby–Rackoff inequality in `ℝ≥0∞`**: for any adaptive bidirectional
program making at most `Q` forward or inverse queries, `idealStrongGame` accepts with probability
at most `feistel4StrongRandomRoundsGame` plus
`2 * Q.choose 2 * |G|⁻¹ + 2 * Q.choose 2 * |G × G|⁻¹`. -/
theorem idealStrongGame_apply_le_feistel4StrongRandomRoundsGame
    {program : OracleComp (fun _ : Bool × (G × G) => G × G) Bool} {Q : ℕ}
    (hQ : OracleComp.IsQueryBounded program Q) (b : Bool) :
    idealStrongGame program b ≤
      feistel4StrongRandomRoundsGame program b +
        (2 * (Q.choose 2 : ℝ≥0∞) * (Fintype.card G : ℝ≥0∞)⁻¹ +
          2 * (Q.choose 2 : ℝ≥0∞) * (Fintype.card (G × G) : ℝ≥0∞)⁻¹) := by
  set prog := RandomPermutation.liftBoolProd program
  have hQ' := RandomPermutation.isQueryBounded_liftBoolProd hQ
  set forgetVal := (((OracleComp.interpret RandomPermutation.forgetfulAnswer prog).run []).map
    Prod.fst) b
  set unif := PMF.uniformOfFintype (G → G)
  have h1 : forgetVal = ∑' f₁, unif f₁ * ∑' f₄, unif f₄ * forgetVal := by
    simp only [ENNReal.tsum_mul_right, unif.tsum_coe, one_mul]
  have hstep :
      forgetVal ≤ feistel4StrongRandomRoundsGame program b +
        (2 * (Q.choose 2 : ℝ≥0∞) * (Fintype.card G : ℝ≥0∞)⁻¹ +
          (Q.choose 2 : ℝ≥0∞) * (Fintype.card (G × G) : ℝ≥0∞)⁻¹) := by
    rw [h1, feistel4StrongRandomRoundsGame_eq_bind_fixed, Probability.PMF.monad_bind_eq_bind]
    simp only [PMF.bind_apply]
    calc ∑' f₁, unif f₁ * ∑' f₄, unif f₄ * forgetVal
        ≤ ∑' f₁, unif f₁ * ∑' f₄, unif f₄ *
          (feistel4StrongFixedGame f₁ f₄ program b +
            ((OracleComp.interpret RandomPermutation.forgetfulAnswer prog).run []).toOuterMeasure
              {x | hasCollision4 f₁ f₄ x.2 = true}) :=
          tsum_le_tsum fun f₁ => mul_le_mul_of_nonneg_left
            (tsum_le_tsum fun f₄ => mul_le_mul_of_nonneg_left
              (forgetfulAnswer_apply_le_feistel4StrongFixedGame f₁ f₄ program b) zero_le) zero_le
      _ = (∑' f₁, unif f₁ * ∑' f₄, unif f₄ * feistel4StrongFixedGame f₁ f₄ program b) +
          ∑' f₁, unif f₁ * ∑' f₄, unif f₄ *
            ((OracleComp.interpret RandomPermutation.forgetfulAnswer prog).run []).toOuterMeasure
              {x | hasCollision4 f₁ f₄ x.2 = true} := by
          simp only [mul_add, tsum_add]
      _ ≤ _ := add_le_add le_rfl (tsum_uniform_toOuterMeasure_hasCollision4_le hQ')
  have hperm := RandomPermutation.uniformPerm_bind_apply_le_forgetful hQ' PMF.pure b
  simp only [Probability.PMF.monad_bind_eq_bind, PMF.bind_pure] at hperm
  rw [← idealStrongGame_eq_bind_liftBoolProd] at hperm
  calc idealStrongGame program b
      ≤ (feistel4StrongRandomRoundsGame program b +
          (2 * (Q.choose 2 : ℝ≥0∞) * (Fintype.card G : ℝ≥0∞)⁻¹ +
            (Q.choose 2 : ℝ≥0∞) * (Fintype.card (G × G) : ℝ≥0∞)⁻¹)) +
        (Q.choose 2 : ℝ≥0∞) * (Fintype.card (G × G) : ℝ≥0∞)⁻¹ :=
        hperm.trans (add_le_add hstep le_rfl)
    _ = feistel4StrongRandomRoundsGame program b +
        (2 * (Q.choose 2 : ℝ≥0∞) * (Fintype.card G : ℝ≥0∞)⁻¹ +
          2 * (Q.choose 2 : ℝ≥0∞) * (Fintype.card (G × G) : ℝ≥0∞)⁻¹) := by ring

/-- **4-round strong Luby–Rackoff theorem with random round functions** ([LubyRackoff1988]; see
[BonehShoup2023], Section 4.1.3 for strongly secure block ciphers; the concrete constant comes
from this proof): when all four round functions `f₁, f₂, f₃, f₄ : G → G` are
independent uniform random functions, any `Q`-query adaptive chosen-ciphertext distinguisher has
distinguishing advantage against a uniform random permutation on `G × G` (`idealStrongGame`) at
most `2 * Q.choose 2 * |G|⁻¹ + 2 * Q.choose 2 * (|G|⁻¹) ^ 2`. -/
theorem advantage_feistel4StrongRandomRoundsGame_idealStrongGame_le
    {program : OracleComp (fun _ : Bool × (G × G) => G × G) Bool} {Q : ℕ}
    (hQ : OracleComp.IsQueryBounded program Q) :
    (Game.advantage (feistel4StrongRandomRoundsGame program)
      (idealStrongGame program) : ℝ) ≤
      2 * (Q.choose 2 : ℝ) * (Fintype.card G : ℝ)⁻¹ +
        2 * (Q.choose 2 : ℝ) * ((Fintype.card G : ℝ)⁻¹) ^ 2 := by
  have hcardG : (Fintype.card G : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcardGG : (Fintype.card (G × G) : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hB1 : 2 * (Q.choose 2 : ℝ≥0∞) * (Fintype.card G : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.natCast_ne_top _))
      (ENNReal.inv_ne_top.mpr hcardG)
  have hB2 : 2 * (Q.choose 2 : ℝ≥0∞) * (Fintype.card (G × G) : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.natCast_ne_top _))
      (ENNReal.inv_ne_top.mpr hcardGG)
  have hB : 2 * (Q.choose 2 : ℝ≥0∞) * (Fintype.card G : ℝ≥0∞)⁻¹ +
      2 * (Q.choose 2 : ℝ≥0∞) * (Fintype.card (G × G) : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hB1, hB2⟩
  have h := Game.advantage_le_of_apply_le hB
    (feistel4StrongRandomRoundsGame_apply_le hQ true)
    (idealStrongGame_apply_le_feistel4StrongRandomRoundsGame hQ true)
  rw [ENNReal.toReal_add hB1 hB2, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_natCast,
    ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    Fintype.card_prod, Nat.cast_mul, mul_inv, ← sq] at h
  exact h

/-- **Full 4-round strong PRP Luby–Rackoff theorem** ([LubyRackoff1988]; see [BonehShoup2023],
Section 4.1.3 for strongly secure block ciphers; the concrete constant comes from this proof):
combining the 4-round bidirectional PRF hybrid reduction with the
random-round collision bound shows that a 4-round Feistel network instantiated with four
independent keys from a PRF `F : K → G → G` is a strong (chosen-ciphertext secure)
pseudorandom permutation on `G × G`, with distinguishing advantage at most
`ε₁ + ε₂ + ε₃ + ε₄ + 2 * Q.choose 2 * |G|⁻¹ + 2 * Q.choose 2 * (|G|⁻¹) ^ 2`. -/
theorem advantage_feistel4StrongKeyedGame_idealStrongGame_le
    {keyGen : PMF K} {F : K → G → G}
    {program : OracleComp (fun _ : Bool × (G × G) => G × G) Bool} {Q : ℕ}
    (hQ : OracleComp.IsQueryBounded program Q) {ε₁ ε₂ ε₃ ε₄ : ℝ}
    (h₁ : ∀ f₂ f₃ f₄,
      (Game.advantage (prfSingleRealGame keyGen F (feistel4StrongReduction₁ f₂ f₃ f₄ program))
        (prfSingleIdealGame (feistel4StrongReduction₁ f₂ f₃ f₄ program)) : ℝ) ≤ ε₁)
    (h₂ : ∀ f₁ f₃ f₄,
      (Game.advantage (prfSingleRealGame keyGen F (feistel4StrongReduction₂ f₁ f₃ f₄ program))
        (prfSingleIdealGame (feistel4StrongReduction₂ f₁ f₃ f₄ program)) : ℝ) ≤ ε₂)
    (h₃ : ∀ f₁ f₂ f₄,
      (Game.advantage (prfSingleRealGame keyGen F (feistel4StrongReduction₃ f₁ f₂ f₄ program))
        (prfSingleIdealGame (feistel4StrongReduction₃ f₁ f₂ f₄ program)) : ℝ) ≤ ε₃)
    (h₄ : ∀ f₁ f₂ f₃,
      (Game.advantage (prfSingleRealGame keyGen F (feistel4StrongReduction₄ f₁ f₂ f₃ program))
        (prfSingleIdealGame (feistel4StrongReduction₄ f₁ f₂ f₃ program)) : ℝ) ≤ ε₄) :
    (Game.advantage (feistel4StrongKeyedGame keyGen F program)
      (idealStrongGame program) : ℝ) ≤
      ε₁ + ε₂ + ε₃ + ε₄ + 2 * (Q.choose 2 : ℝ) * (Fintype.card G : ℝ)⁻¹ +
        2 * (Q.choose 2 : ℝ) * ((Fintype.card G : ℝ)⁻¹) ^ 2 := by
  have htri :
      (Game.advantage (feistel4StrongKeyedGame keyGen F program)
        (idealStrongGame program) : ℝ) ≤
      (Game.advantage (feistel4StrongKeyedGame keyGen F program)
        (feistel4StrongRandomRoundsGame program) : ℝ) +
      (Game.advantage (feistel4StrongRandomRoundsGame program)
        (idealStrongGame program) : ℝ) := by
    exact_mod_cast Game.advantage_triangle (feistel4StrongKeyedGame keyGen F program)
      (feistel4StrongRandomRoundsGame program) (idealStrongGame program)
  have hprf := advantage_feistel4StrongKeyedGame_feistel4StrongRandomRoundsGame_le h₁ h₂ h₃ h₄
  have hcoll := advantage_feistel4StrongRandomRoundsGame_idealStrongGame_le hQ
  linarith

/-- Concrete instantiation of the 4-round strong Luby–Rackoff theorem on `BitString n`
(block size `2n`): the information-theoretic chosen-ciphertext collision error is at most
`2 * Q.choose 2 / 2 ^ n + 2 * Q.choose 2 / (2 ^ n) ^ 2`. -/
theorem advantage_feistel4StrongRandomRoundsGame_bitString_le (n : ℕ)
    {program :
      OracleComp (fun _ : Bool × (BitString n × BitString n) => BitString n × BitString n) Bool}
    {Q : ℕ} (hQ : OracleComp.IsQueryBounded program Q) :
    (Game.advantage (feistel4StrongRandomRoundsGame program)
      (idealStrongGame program) : ℝ) ≤
      2 * (Q.choose 2 : ℝ) * ((2 : ℝ) ^ n)⁻¹ +
        2 * (Q.choose 2 : ℝ) * (((2 : ℝ) ^ n)⁻¹) ^ 2 := by
  have h := advantage_feistel4StrongRandomRoundsGame_idealStrongGame_le hQ
  simpa only [Fintype.card_pi, Fintype.card_fin, Fintype.card_bool, Finset.prod_const,
    Finset.card_univ, Nat.cast_pow, Nat.cast_ofNat] using h

end Strong4AndCCAAttack

end Cslib.Crypto.LubyRackoff
