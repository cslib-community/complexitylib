/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Binary
public import Complexity.Init
public import Complexity.Probability.KWiseIndependent
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Sort

/-!
# Double Tabulation and High Independence (`[Thorup2013]`)

This module formalizes the double tabulation hash family and its universal `k`-uniqueness analysis
following Mikkel Thorup, *"Simple Tabulation, Fast Expanders, Double Tabulation, and High
Independence"*, *Proc. 54th IEEE Symposium on Foundations of Computer Science (FOCS 2013)*,
pp. 90–99, 2013 (`arXiv:1311.3121v2`, 16 October 2018) [Thorup2013].

Given keys split into `c` characters from `Φ = Fin (2 ^ b)`, a first-level simple tabulation table
`T₁ : Fin c → Fin d → Fin (2 ^ b) → Fin (2 ^ b)` maps each key `x : Fin c → Fin (2 ^ b)` to an
intermediate `d`-tuple `simpleTabTuple T₁ x : Fin d → Fin (2 ^ b)` by XORing the `c` character
table lookups in each output coordinate `j : Fin d`. Composing `simpleTabTuple T₁` with an
independent second-level simple tabulation table `T₂ : Fin d → Fin (2 ^ b) → Fin (2 ^ M)` yields
the double tabulation hash `doubleTabHash c d b U M T₁ T₂ : Fin U → Fin (2 ^ M)`.

## Source statements and notation mapping

In Thorup [Thorup2013] (`arXiv:1311.3121v2`):
* **`k`-uniqueness (`IsKUnique`, Section 1.1, p. 4)**: For an output alphabet `Ψ = Fin (2 ^ b)`, a
  function `f : U → Ψ ^ d` is *`k`-unique* if every non-empty subset `X ⊆ U` of size `|X| ≤ k` has a
  unique output position character `(j₀, f(x₀)_{j₀})`, i.e., some `x₀ ∈ X` and `j₀ ∈ [d]` such that
  `f(x₀)_{j₀} ≠ f(x)_{j₀}` for all `x ∈ X \ {x₀}`.
* **Siegel's peeling lemma (`isKWiseIndependentHash_of_isKUnique`, Section 1.1, Lemma 2, p. 5;
  Appendix A, p. 19)**: If `f : α → (Fin d → β)` is `k`-unique and `r : Fin d → β → Fin (2 ^ M)` is
  a uniformly random simple tabulation table, then `r ∘ f : α → Fin (2 ^ M)` is `k`-wise
  independent (`IsKWiseIndependentHash k`).
* **Derivable output characters and efficient coding (Section 2, Definition 6, pp. 9–10;
  Eqs. (6)–(7), p. 11)**: For a list `L` of `ℓ` distinct input position characters in
  `[c] × Φ`, an output index `(α, j) ∈ L × [d]` is *derivable* if there exist `x, y ∈ X` whose
  symmetric difference `A = x △ y ⊆ L` has `α` as its last element in `L` and satisfies
  `h(x)_j = h(y)_j` (equivalently `h(α)_j = ⨁_{β ∈ A \ {α}} h(β)_j`). Fixing `L` (`≤ (c |Φ|) ^ ℓ`
  choices) and `q ℓ` equations `(A_r, j_r)` (`≤ (ℓ ^ (2 c) d) ^ (q ℓ)` choices) with distinct
  last-in-`L` output indices determines `q ℓ` entries of `T₁` in terms of earlier entries in `L`,
  leaving at most `|Θ_top| / |Ψ| ^ (q ℓ)` compatible tables `T₁` (Eqs. (6)–(7), p. 11).
* **Many derivable output characters (Section 3, Theorem 7(a) and Lemma 8, p. 12; Lemma 9 and
  Eqs. (8)–(11), pp. 12–13)**: For a violating set `X` (`|X| ≤ k`), order its `ℓ* ≤ c |X|` active
  input position characters `α₁, …, α_{ℓ*}` by decreasing frequency `n₁ ≥ … ≥ n_{ℓ*} ≥ 1`
  (`∑ n_i = c |X|`). Letting `γ_{≤ ℓ}` count pairs `(x, j) ∈ X × [d]` whose symmetric-difference
  witness `x △ y` with `h(x)_j = h(y)_j` lies in the prefix `L_{≤ ℓ} = {α₁, …, α_ℓ}` and letting
  `ϕ_ℓ` count derivable output indices `(α_ℓ, j)` at step `ℓ`, Lemma 8 (p. 12) gives
  `γ_{≤ ℓ*} = d |X|` and Lemma 9 (Eq. (8), p. 12) gives `γ_{≤ ℓ} - γ_{≤ ℓ - 1} ≤ 2 ϕ_ℓ n_ℓ`. By
  summation by parts (Eqs. (9)–(11), pp. 12–13), when `d = 2 q c`, some prefix `L_{≤ ℓ}`
  (`2 ≤ ℓ ≤ c k`) has `∑_{i=1}^ℓ ϕ_i ≥ q ℓ` derivable output characters.
* **Original adaptations**:
  - In Theorem 1(a) and Section 2 (pp. 4, 11), Thorup states the failure probability asymptotically
    as `o(|Φ| ^ 2 / |Ψ| ^ (d / (2 c)))` under `c = |Φ| ^ o(1)` and `(c + d) ^ c = |Ψ| ^ o(1)`.
    Here `card_not_isKUnique_le` and `card_not_isKUnique_eight_mul_le` establish an explicit
    non-asymptotic finite-seed bound for all `c, q, b ≥ 1` and `d = 2 q c` whenever
    `2 * (c * ((c * k) ^ (2 * c) * d) ^ q) ≤ 2 ^ ((q - 1) * b)`.
  - Each non-empty symmetric difference `A ⊆ range(L)` of size `|A| ≤ 2 c` is parameterized in
    Section 4 by a tuple `g : Fin (2 * c) → Fin ℓ` whose image in `Fin ℓ` has maximum index
    `lastIdx g`, giving an exact `Fintype.card` count `(ℓ ^ (2 * c) * d) ^ (q * ℓ)`.

## Main definitions

* `Cslib.Probability.IsKUnique`: `k`-uniqueness of a tuple-valued function `f : α → Fin d → β`
  ([Thorup2013], Section 1.1, p. 4).
* `Cslib.Probability.simpleTabAddHom`, `Cslib.Probability.simpleTabEval`: simple tabulation over an
  additive commutative group and over `Fin (2 ^ M)` via bitwise XOR (`BitString.equivFin M`).
* `Cslib.Probability.charDigits`: base-`2 ^ b` character extraction `Fin U → Fin c → Fin (2 ^ b)`.
* `Cslib.Probability.simpleTabTuple`: first-level simple tabulation
  `(Fin c → Fin d → Fin (2 ^ b) → Fin (2 ^ b)) → (Fin c → Fin (2 ^ b)) → (Fin d → Fin (2 ^ b))`.
* `Cslib.Probability.DoubleTabTopSeed`, `Cslib.Probability.DoubleTabBotSeed`,
  `Cslib.Probability.doubleTabHash`, `Cslib.Probability.doubleTabCodeBound`: seed types, composed
  double tabulation hash `Fin U → Fin (2 ^ M)`, and the per-step code-counting factor
  `c * ((c * k) ^ (2 * c) * d) ^ q`.

## Main results

* `Cslib.Probability.val_equivFin_add`: addition in `BitString M` corresponds to bitwise XOR
  (`^^^`) under `BitString.equivFin M`.
* `Cslib.Probability.isKWiseIndependentHash_of_isKUnique`: Siegel's peeling lemma ([Thorup2013],
  Lemma 2, p. 5 & Appendix A, p. 19).
* `Cslib.Probability.charDigits_injective`: `charDigits c b` is injective when `U ≤ 2 ^ (c * b)`.
* `Cslib.Probability.isKWiseIndependentHash_doubleTabHash_of_isKUnique`: when `T₁` is `k`-unique and
  `U ≤ 2 ^ (c * b)`, `T₂ ↦ doubleTabHash c d b U M T₁ T₂` is `k`-wise independent.
* `Cslib.Probability.card_not_isKUnique_le`,
  `Cslib.Probability.card_not_isKUnique_eight_mul_le`: explicit universal `k`-uniqueness bounds for
  `simpleTabTuple T₁` ([Thorup2013], Theorem 1(a), Section 2 Eqs. (6)–(7), Section 3 Theorem 7(a)
  and Lemmas 8–9).

## References

* [M. Thorup, *Simple Tabulation, Fast Expanders, Double Tabulation,
  and High Independence*][Thorup2013]
-/

public section

namespace Cslib.Probability

open BitString Finset
open scoped BigOperators

/-! ## Section 1: `k`-uniqueness and Siegel's peeling lemma -/

/-- **Addition in `BitString M` is bitwise XOR (`^^^`) on `BitString.equivFin M` coordinates.** -/
theorem val_equivFin_add {M : ℕ} (a b : BitString M) :
    (BitString.equivFin M (a + b)).val =
      (BitString.equivFin M a).val ^^^ (BitString.equivFin M b).val := by
  let ka := BitString.equivFin M a
  let kb := BitString.equivFin M b
  let k : Fin (2 ^ M) := ⟨ka.val ^^^ kb.val, Nat.xor_lt_two_pow ka.isLt kb.isLt⟩
  have hsymm : (BitString.equivFin M).symm k = a + b := by
    ext i
    rw [BitString.equivFin_symm_apply, show (k : ℕ) = ka.val ^^^ kb.val from rfl,
      Nat.testBit_xor, ← BitString.equivFin_symm_apply ka i,
      ← BitString.equivFin_symm_apply kb i, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rfl
  have hk : BitString.equivFin M (a + b) = k := by
    rw [← hsymm, Equiv.apply_symm_apply]
  exact congrArg Fin.val hk

/-- **`k`-uniqueness** ([Thorup2013], Section 1.1, p. 4): a tuple map `f : α → Fin d → β` is
`k`-unique if every non-empty subset `X ⊆ α` of size `#X ≤ k` contains a key `x₀ ∈ X` and output
coordinate `j₀ : Fin d` whose value `f x₀ j₀` differs from `f x j₀` for all other `x ∈ X`. -/
@[expose] def IsKUnique {α β : Type*} {d : ℕ} (k : ℕ) (f : α → Fin d → β) : Prop :=
  ∀ X : Finset α, X.Nonempty → #X ≤ k →
    ∃ x₀ ∈ X, ∃ j₀ : Fin d, ∀ x ∈ X, x ≠ x₀ → f x₀ j₀ ≠ f x j₀

instance {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β] {d : ℕ} (k : ℕ)
    (f : α → Fin d → β) : Decidable (IsKUnique k f) :=
  decidable_of_iff
    (∀ X ∈ (Finset.univ : Finset α).powerset, 0 < #X → #X ≤ k →
      ∃ x₀ ∈ X, ∃ j₀ : Fin d, ∀ x ∈ X, x ≠ x₀ → f x₀ j₀ ≠ f x j₀)
    ⟨fun h X hne hX => h X (Finset.mem_powerset.mpr (Finset.subset_univ X))
      (Finset.card_pos.mpr hne) hX,
     fun h X _ hpos hX => h X (Finset.card_pos.mp hpos) hX⟩

/-- Monotonicity of `IsKUnique` in `k`: if `f` is `k`-unique and `k' ≤ k`, then `f` is
`k'`-unique. -/
theorem IsKUnique.mono {α β : Type*} {d k k' : ℕ} {f : α → Fin d → β}
    (hf : IsKUnique k f) (hk : k' ≤ k) : IsKUnique k' f :=
  fun X hne hX => hf X hne (hX.trans hk)

/-- Precomposing a `k`-unique function `f : α → Fin d → β` with an injective map `g : α' → α`
preserves `k`-uniqueness. -/
theorem IsKUnique.comp_injective {α' α β : Type*} {d k : ℕ} {f : α → Fin d → β}
    (hf : IsKUnique k f) {g : α' → α} (hg : Function.Injective g) :
    IsKUnique k (fun x => f (g x)) := by
  classical
  intro X hne hX
  have hne_img : (X.image g).Nonempty := hne.image g
  have hcard_img : #(X.image g) ≤ k := (Finset.card_image_le).trans hX
  obtain ⟨y₀, hy₀, j₀, huniq⟩ := hf (X.image g) hne_img hcard_img
  obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hy₀
  refine ⟨x₀, hx₀, j₀, fun x hx hne_x => ?_⟩
  exact huniq (g x) (Finset.mem_image_of_mem g hx) (fun heq => hne_x (hg heq))

/-- Simple tabulation evaluation over an additive commutative group `γ` as an additive homomorphism
`(Fin d → β → γ) →+ (α → γ)`. -/
@[expose] def simpleTabAddHom {α β γ : Type*} [AddCommGroup γ] {d : ℕ}
    (f : α → Fin d → β) : (Fin d → β → γ) →+ (α → γ) where
  toFun r x := ∑ j : Fin d, r j (f x j)
  map_zero' := by ext x; simp
  map_add' r₁ r₂ := by ext x; simp [Finset.sum_add_distrib]

/-- Simple tabulation evaluation over `Fin (2 ^ M)`, XORing `(r j (y j)).val` across `j : Fin d` via
`BitString.equivFin M`. -/
@[expose] def simpleTabEval {β : Type*} {d M : ℕ}
    (r : Fin d → β → Fin (2 ^ M)) (y : Fin d → β) : Fin (2 ^ M) :=
  BitString.equivFin M (∑ j : Fin d, (BitString.equivFin M).symm (r j (y j)))

/-- Surjectivity of `T.restrict ∘ simpleTabAddHom f` for `#T ≤ k` when `f` is `k`-unique
(peeling induction on `#T`). -/
private theorem surjective_restrict_simpleTabAddHom {α β γ : Type*}
    [AddCommGroup γ] {d k : ℕ} {f : α → Fin d → β} (hf : IsKUnique k f) :
    ∀ (n : ℕ) (T : Finset α), #T = n → #T ≤ k →
      Function.Surjective (fun r : Fin d → β → γ => T.restrict (simpleTabAddHom f r))
  | 0, T, hcard, _ => by
    intro y
    have hT : T = ∅ := Finset.card_eq_zero.mp hcard
    subst hT
    exact ⟨0, funext fun ⟨x, hx⟩ => (Finset.notMem_empty x hx).elim⟩
  | n + 1, T, hcard, hTk => by
    classical
    intro y
    have hne : T.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x₀, hx₀, j₀, huniq⟩ := hf T hne hTk
    let T' := T.erase x₀
    have hcard' : #T' = n := by
      rw [Finset.card_erase_of_mem hx₀, hcard, Nat.add_sub_cancel]
    let y' : T' → γ := fun x => y ⟨x.1, Finset.mem_of_mem_erase x.2⟩
    obtain ⟨r', hr'⟩ := surjective_restrict_simpleTabAddHom hf n T' hcard' (by omega) y'
    let δ : γ := y ⟨x₀, hx₀⟩ - simpleTabAddHom f r' x₀
    let r : Fin d → β → γ := fun j b => r' j b + if j = j₀ ∧ b = f x₀ j₀ then δ else 0
    refine ⟨r, funext fun ⟨x, hx⟩ => ?_⟩
    have hsum : simpleTabAddHom f r x =
        simpleTabAddHom f r' x + ∑ j : Fin d, (if j = j₀ ∧ f x j = f x₀ j₀ then δ else 0) := by
      simp [r, simpleTabAddHom, Finset.sum_add_distrib]
    by_cases hxx₀ : x = x₀
    · subst hxx₀
      have hite : (∑ j : Fin d, (if j = j₀ ∧ f x j = f x j₀ then δ else 0)) = δ := by
        have hcongr : (∑ j : Fin d, (if j = j₀ ∧ f x j = f x j₀ then δ else 0)) =
            ∑ j : Fin d, (if j = j₀ then δ else 0) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          by_cases hj : j = j₀ <;> simp [hj]
        rw [hcongr]
        simp
      change simpleTabAddHom f r x = y ⟨x, hx⟩
      rw [hsum, hite, add_sub_cancel]
    · have hzero : (∑ j : Fin d, (if j = j₀ ∧ f x j = f x₀ j₀ then δ else 0)) = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        split_ifs with hj
        · exfalso
          rcases hj with ⟨rfl, hfx⟩
          exact huniq x hx hxx₀ hfx.symm
        · rfl
      have hx' : x ∈ T' := Finset.mem_erase.mpr ⟨hxx₀, hx⟩
      have hr'_at : simpleTabAddHom f r' x = y ⟨x, hx⟩ := congrFun hr' ⟨x, hx'⟩
      change simpleTabAddHom f r x = y ⟨x, hx⟩
      rw [hsum, hzero, add_zero, hr'_at]

/-- **Siegel's Peeling Lemma ([Thorup2013], Section 1.1, Lemma 2, p. 5 & Appendix A, p. 19)**:
If `f : α → Fin d → β` is `k`-unique (`IsKUnique k f`), then composing `f` with a uniformly random
simple tabulation table `r : Fin d → β → Fin (2 ^ M)` yields a `k`-wise independent hash family
`α → Fin (2 ^ M)`. -/
theorem isKWiseIndependentHash_of_isKUnique {α β : Type*} [Fintype β] [DecidableEq β]
    {d M k : ℕ} {f : α → Fin d → β} (hf : IsKUnique k f) :
    IsKWiseIndependentHash k (fun (r : Fin d → β → Fin (2 ^ M)) (x : α) =>
      simpleTabEval r (f x)) := by
  have hbits : IsKWiseIndependentHash k
      (fun r : Fin d → β → BitString M => simpleTabAddHom f r) :=
    isKWiseIndependentHash_of_surjective (simpleTabAddHom (γ := BitString M) f)
      (fun T hT => surjective_restrict_simpleTabAddHom hf #T T rfl hT)
  have hseed := hbits.comp_seedEquiv
    (Equiv.piCongrRight fun _ : Fin d =>
      Equiv.piCongrRight fun _ : β => (BitString.equivFin M).symm)
  exact hseed.map_equiv (BitString.equivFin M)

/-! ## Section 2: Base-`2 ^ b` character extraction and double tabulation -/

/-- Base-`2 ^ b` character extraction: splits `u : Fin U` into `c` characters in `Fin (2 ^ b)` via
`(u.val >>> (i.val * b)) &&& (2 ^ b - 1)`. -/
@[expose] def charDigits (c b : ℕ) {U : ℕ} (u : Fin U) (i : Fin c) : Fin (2 ^ b) :=
  ⟨(u.val >>> (i.val * b)) &&& (2 ^ b - 1), by
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (Nat.two_pow_pos b)⟩

/-- **Injectivity of `charDigits`**: when `U ≤ 2 ^ (c * b)`, distinct keys in `Fin U` have distinct
`c`-tuples of `b`-bit characters. -/
theorem charDigits_injective {c b U : ℕ} (hU : U ≤ 2 ^ (c * b)) :
    Function.Injective (charDigits c b (U := U)) := by
  intro u₁ u₂ heq
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < c * b
  · have hb : 0 < b := by
      rcases Nat.eq_zero_or_pos b with rfl | hb
      · simp at ht
      · exact hb
    have hi : t / b < c := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
    have hr : t % b < b := Nat.mod_lt t hb
    have hchar := congrArg (fun f => (f ⟨t / b, hi⟩).val.testBit (t % b)) heq
    dsimp only [charDigits] at hchar
    rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, decide_eq_true hr, Bool.and_true,
      Nat.testBit_shiftRight, Nat.testBit_and, Nat.testBit_two_pow_sub_one, decide_eq_true hr,
      Bool.and_true, Nat.testBit_shiftRight, Nat.mul_comm (t / b) b,
      Nat.div_add_mod] at hchar
    exact hchar
  · have hpow : 2 ^ (c * b) ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) (not_lt.mp ht)
    have h₁ : u₁.val.testBit t = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le u₁.isLt (hU.trans hpow))
    have h₂ : u₂.val.testBit t = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le u₂.isLt (hU.trans hpow))
    rw [h₁, h₂]

/-- Top-level simple tabulation seed space `Fin c → Fin d → Fin (2 ^ b) → Fin (2 ^ b)`. -/
abbrev DoubleTabTopSeed (c d b : ℕ) : Type :=
  Fin c → Fin d → Fin (2 ^ b) → Fin (2 ^ b)

/-- Bottom-level simple tabulation seed space `Fin d → Fin (2 ^ b) → Fin (2 ^ M)`. -/
abbrev DoubleTabBotSeed (d b M : ℕ) : Type :=
  Fin d → Fin (2 ^ b) → Fin (2 ^ M)

/-- First-level simple tabulation (`[Thorup2013]`, Eq. (2), p. 3 & Theorem 1, p. 4): maps each
character tuple `x : Fin c → Fin (2 ^ b)` to an intermediate `d`-tuple `Fin d → Fin (2 ^ b)` by
XORing `T₁ i j (x i)` across `i : Fin c` in each output coordinate `j : Fin d`. -/
@[expose] def simpleTabTuple {c d b : ℕ} (T₁ : DoubleTabTopSeed c d b)
    (x : Fin c → Fin (2 ^ b)) (j : Fin d) : Fin (2 ^ b) :=
  simpleTabEval (fun i a => T₁ i j a) x

/-- **Mikkel Thorup's Double Tabulation hash function ([Thorup2013], Section 1.1, p. 5)**:
extracts `c` base-`2 ^ b` characters from `u : Fin U`, applies `simpleTabTuple T₁` to obtain `d`
intermediate `b`-bit characters, and applies `simpleTabEval T₂` to produce an `M`-bit hash in
`Fin (2 ^ M)`. -/
@[expose] def doubleTabHash (c d b U M : ℕ)
    (T₁ : DoubleTabTopSeed c d b) (T₂ : DoubleTabBotSeed d b M) (u : Fin U) : Fin (2 ^ M) :=
  simpleTabEval T₂ (simpleTabTuple T₁ (charDigits c b u))

/-- When the top-level table `T₁` is `k`-unique (`IsKUnique k (simpleTabTuple T₁)`) and
`U ≤ 2 ^ (c * b)`, the bottom-level family `fun T₂ => doubleTabHash c d b U M T₁ T₂` is `k`-wise
independent ([Thorup2013], Section 1.1, Lemma 2, p. 5). -/
theorem isKWiseIndependentHash_doubleTabHash_of_isKUnique {c d b U M k : ℕ}
    {T₁ : DoubleTabTopSeed c d b} (hU : U ≤ 2 ^ (c * b))
    (huniq : IsKUnique k (simpleTabTuple T₁)) :
    IsKWiseIndependentHash k (fun T₂ : DoubleTabBotSeed d b M => doubleTabHash c d b U M T₁ T₂) :=
  isKWiseIndependentHash_of_isKUnique (huniq.comp_injective (charDigits_injective hU))

/-! ## Section 3: Position-character sets, symmetric differences, and `BitString` XOR laws -/

/-- Set of `c` input position characters `{(i, x i) | i : Fin c}` of a key `x : Fin c → Fin (2 ^ b)`
([Thorup2013], Section 2, p. 9). -/
private def posSet {c b : ℕ} (x : Fin c → Fin (2 ^ b)) : Finset (Fin c × Fin (2 ^ b)) :=
  Finset.univ.image fun i : Fin c => (i, x i)

@[simp]
private theorem mem_posSet {c b : ℕ} {x : Fin c → Fin (2 ^ b)} {α : Fin c × Fin (2 ^ b)} :
    α ∈ posSet x ↔ x α.1 = α.2 := by
  simp only [posSet, Finset.mem_image, Finset.mem_univ, true_and, Prod.ext_iff]
  exact ⟨fun ⟨i, hi, hx⟩ => hi ▸ hx, fun h => ⟨α.1, rfl, h⟩⟩

@[simp]
private theorem card_posSet {c b : ℕ} (x : Fin c → Fin (2 ^ b)) : #(posSet x) = c := by
  unfold posSet
  rw [Finset.card_image_of_injective _ (fun i₁ i₂ h => congrArg Prod.fst h), Finset.card_univ,
    Fintype.card_fin]

/-- Symmetric difference `x △ y = symmDiff (posSet x) (posSet y)` of two keys' position-character
sets ([Thorup2013], Definition 6, p. 10). -/
private def posSymmDiff {c b : ℕ} (x y : Fin c → Fin (2 ^ b)) : Finset (Fin c × Fin (2 ^ b)) :=
  symmDiff (posSet x) (posSet y)

private theorem card_posSymmDiff_le {c b : ℕ} (x y : Fin c → Fin (2 ^ b)) :
    #(posSymmDiff x y) ≤ 2 * c := by
  have hsub : posSymmDiff x y ⊆ posSet x ∪ posSet y := symmDiff_subset_union
  calc #(posSymmDiff x y) ≤ #(posSet x ∪ posSet y) := Finset.card_le_card hsub
    _ ≤ #(posSet x) + #(posSet y) := Finset.card_union_le _ _
    _ = 2 * c := by rw [card_posSet, card_posSet, two_mul]

/-- Any two distinct keys `x ≠ y` differ in at least one coordinate `i : Fin c`, contributing two
distinct position characters `(i, x i) ≠ (i, y i)` to `posSymmDiff x y`. -/
private theorem two_le_card_posSymmDiff_of_ne {c b : ℕ} {x y : Fin c → Fin (2 ^ b)} (hne : x ≠ y) :
    2 ≤ #(posSymmDiff x y) := by
  have hdiff : ∃ i : Fin c, x i ≠ y i := by
    by_contra hall
    push Not at hall
    exact hne (funext hall)
  obtain ⟨i, hxy⟩ := hdiff
  have hx_mem : (i, x i) ∈ posSymmDiff x y := by
    rw [posSymmDiff, Finset.mem_symmDiff, mem_posSet, mem_posSet]
    exact Or.inl ⟨rfl, Ne.symm hxy⟩
  have hy_mem : (i, y i) ∈ posSymmDiff x y := by
    rw [posSymmDiff, Finset.mem_symmDiff, mem_posSet, mem_posSet]
    exact Or.inr ⟨rfl, hxy⟩
  have hpair_ne : (i, x i) ≠ (i, y i) := fun h => hxy (congrArg Prod.snd h)
  have hsub : {(i, x i), (i, y i)} ⊆ posSymmDiff x y := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hx_mem
    · rw [Finset.mem_singleton.mp hp]
      exact hy_mem
  calc 2 = #({(i, x i), (i, y i)} : Finset (Fin c × Fin (2 ^ b))) :=
        (Finset.card_pair hpair_ne).symm
    _ ≤ #(posSymmDiff x y) := Finset.card_le_card hsub

/-- Triangle inclusion for symmetric difference of position-character sets:
`posSymmDiff y z ⊆ posSymmDiff x y ∪ posSymmDiff x z`. -/
private theorem posSymmDiff_subset_union {c b : ℕ} (x y z : Fin c → Fin (2 ^ b)) :
    posSymmDiff y z ⊆ posSymmDiff x y ∪ posSymmDiff x z := by
  intro α hα
  simp only [posSymmDiff, Finset.mem_union, Finset.mem_symmDiff] at hα ⊢
  by_cases hx : α ∈ posSet x <;> tauto

/-- In `BitString b` (where every element has order dividing 2), two finset sums are equal iff the
sum over their symmetric difference is `0`. -/
private theorem sum_bitString_eq_iff_sum_symmDiff_eq_zero {ι : Type*} [DecidableEq ι] {b : ℕ}
    (S₁ S₂ : Finset ι) (g : ι → BitString b) :
    ∑ α ∈ S₁, g α = ∑ α ∈ S₂, g α ↔ ∑ α ∈ symmDiff S₁ S₂, g α = 0 := by
  have hdisj₁ : Disjoint (S₁ \ S₂) (S₁ ∩ S₂) := Finset.disjoint_sdiff_inter S₁ S₂
  have hdisj₂ : Disjoint (S₂ \ S₁) (S₁ ∩ S₂) := by
    rw [Finset.inter_comm]
    exact Finset.disjoint_sdiff_inter S₂ S₁
  have hdisj_symm : Disjoint (S₁ \ S₂) (S₂ \ S₁) := disjoint_sdiff_sdiff
  have hunion₁ : S₁ \ S₂ ∪ S₁ ∩ S₂ = S₁ := Finset.sdiff_union_inter S₁ S₂
  have hunion₂ : S₂ \ S₁ ∪ S₁ ∩ S₂ = S₂ := by
    rw [Finset.inter_comm]
    exact Finset.sdiff_union_inter S₂ S₁
  have hsum₁ : ∑ α ∈ S₁, g α = ∑ α ∈ S₁ \ S₂, g α + ∑ α ∈ S₁ ∩ S₂, g α := by
    conv_lhs => rw [← hunion₁, Finset.sum_union hdisj₁]
  have hsum₂ : ∑ α ∈ S₂, g α = ∑ α ∈ S₂ \ S₁, g α + ∑ α ∈ S₁ ∩ S₂, g α := by
    conv_lhs => rw [← hunion₂, Finset.sum_union hdisj₂]
  have hsymm : ∑ α ∈ symmDiff S₁ S₂, g α = ∑ α ∈ S₁ \ S₂, g α + ∑ α ∈ S₂ \ S₁, g α := by
    change ∑ α ∈ S₁ \ S₂ ∪ S₂ \ S₁, g α = _
    exact Finset.sum_union hdisj_symm
  rw [hsum₁, hsum₂, hsymm, add_right_cancel_iff]
  constructor
  · intro h
    rw [h, BitString.add_self]
  · intro h
    calc ∑ α ∈ S₁ \ S₂, g α
        = ∑ α ∈ S₁ \ S₂, g α + (∑ α ∈ S₁ \ S₂, g α + ∑ α ∈ S₂ \ S₁, g α) := by
          rw [h, add_zero]
      _ = ∑ α ∈ S₂ \ S₁, g α := BitString.add_cancel_left _ _

/-- Two keys `x, y` collide in coordinate `j` under `simpleTabTuple T₁` iff the `BitString b` sum of
`T₁` over `posSymmDiff x y` is `0` ([Thorup2013], Definition 6, p. 10). -/
private theorem simpleTabTuple_eq_iff_sum_posSymmDiff_eq_zero {c d b : ℕ}
    (T₁ : DoubleTabTopSeed c d b) (x y : Fin c → Fin (2 ^ b)) (j : Fin d) :
    simpleTabTuple T₁ x j = simpleTabTuple T₁ y j ↔
      ∑ α ∈ posSymmDiff x y, (BitString.equivFin b).symm (T₁ α.1 j α.2) = 0 := by
  have hsum_posSet (z : Fin c → Fin (2 ^ b)) :
      ∑ α ∈ posSet z, (BitString.equivFin b).symm (T₁ α.1 j α.2) =
        ∑ i : Fin c, (BitString.equivFin b).symm (T₁ i j (z i)) := by
    unfold posSet
    exact Finset.sum_image fun i₁ _ i₂ _ h => congrArg Prod.fst h
  unfold simpleTabTuple simpleTabEval
  rw [(BitString.equivFin b).injective.eq_iff, ← hsum_posSet x, ← hsum_posSet y]
  exact sum_bitString_eq_iff_sum_symmDiff_eq_zero (posSet x) (posSet y) _

/-! ## Section 4: Derivable output characters and Theorem 7(a) (`[Thorup2013]`, §3) -/

/-- Maximum index in `Fin ℓ` attained by a tuple `g : Fin m → Fin ℓ` (`m > 0`). -/
private def lastIdx {m ℓ : ℕ} [NeZero m] (g : Fin m → Fin ℓ) : Fin ℓ :=
  (Finset.univ.image g).max' (Finset.univ_nonempty.image g)

private theorem lastIdx_mem_image {m ℓ : ℕ} [NeZero m] (g : Fin m → Fin ℓ) :
    lastIdx g ∈ Finset.univ.image g :=
  Finset.max'_mem _ _

private theorem le_lastIdx {m ℓ : ℕ} [NeZero m] (g : Fin m → Fin ℓ) (t : Fin m) :
    g t ≤ lastIdx g :=
  Finset.le_max' _ (g t) (Finset.mem_image_of_mem g (Finset.mem_univ t))

/-- Predicate that `T₁` satisfies the efficient code `(L, M)` of length `ℓ` and `q * ℓ` equations
([Thorup2013], Section 2, Definition 6 & Eqs. (6)–(7), pp. 9–11). -/
private def SatisfiesCode {c d b q ℓ : ℕ} [NeZero (2 * c)]
    (T₁ : DoubleTabTopSeed c d b) (L : Fin ℓ → Fin c × Fin (2 ^ b))
    (M : Fin (q * ℓ) → (Fin (2 * c) → Fin ℓ) × Fin d) : Prop :=
  Function.Injective L ∧
    Function.Injective (fun r : Fin (q * ℓ) => (lastIdx (M r).1, (M r).2)) ∧
    ∀ r : Fin (q * ℓ),
      ∑ idx ∈ Finset.univ.image (M r).1,
        (BitString.equivFin b).symm (T₁ (L idx).1 (M r).2 (L idx).2) = 0

private instance {c d b q ℓ : ℕ} [NeZero (2 * c)]
    (T₁ : DoubleTabTopSeed c d b) (L : Fin ℓ → Fin c × Fin (2 ^ b))
    (M : Fin (q * ℓ) → (Fin (2 * c) → Fin ℓ) × Fin d) :
    Decidable (SatisfiesCode T₁ L M) := by
  unfold SatisfiesCode
  infer_instance

/-- Frequency `n_α = #{x ∈ X | α ∈ posSet x}` of an input position character `α` in `X`
([Thorup2013], Section 3, p. 11). -/
private def freq {c b : ℕ} (X : Finset (Fin c → Fin (2 ^ b)))
    (α : Fin c × Fin (2 ^ b)) : ℕ :=
  #(X.filter fun x => α ∈ posSet x)

/-- Active input position characters `⋃_{x ∈ X} posSet x` of `X` ([Thorup2013], Section 3,
p. 11). -/
private def activeChars {c b : ℕ} (X : Finset (Fin c → Fin (2 ^ b))) :
    Finset (Fin c × Fin (2 ^ b)) :=
  X.biUnion posSet

/-- Active input position characters of `X` sorted in decreasing order of frequency `freq X`
([Thorup2013], Section 3, p. 11). -/
private noncomputable def sortedChars {c b : ℕ} (X : Finset (Fin c → Fin (2 ^ b))) :
    List (Fin c × Fin (2 ^ b)) :=
  (activeChars X).toList.mergeSort (fun α β => decide (freq X β ≤ freq X α))

/-- First `r` active input position characters `L_{≤ r}` of `sortedChars X` as a finset. -/
private noncomputable def prefixChars {c b : ℕ} (X : Finset (Fin c → Fin (2 ^ b))) (r : ℕ) :
    Finset (Fin c × Fin (2 ^ b)) :=
  ((sortedChars X).take r).toFinset

private theorem nodup_sortedChars {c b : ℕ} (X : Finset (Fin c → Fin (2 ^ b))) :
    (sortedChars X).Nodup :=
  (List.mergeSort_perm (activeChars X).toList _).nodup_iff.mpr (Finset.nodup_toList _)

private theorem length_sortedChars {c b : ℕ} (X : Finset (Fin c → Fin (2 ^ b))) :
    (sortedChars X).length = #(activeChars X) := by
  rw [sortedChars, List.length_mergeSort, Finset.length_toList]

private theorem mem_sortedChars {c b : ℕ} {X : Finset (Fin c → Fin (2 ^ b))}
    {α : Fin c × Fin (2 ^ b)} :
    α ∈ sortedChars X ↔ α ∈ activeChars X := by
  rw [sortedChars, List.mem_mergeSort, Finset.mem_toList]

private theorem card_activeChars_le {c b : ℕ} (X : Finset (Fin c → Fin (2 ^ b))) :
    #(activeChars X) ≤ c * #X := by
  calc #(activeChars X) = #(X.biUnion posSet) := rfl
    _ ≤ ∑ x ∈ X, #(posSet x) := Finset.card_biUnion_le
    _ = ∑ _x ∈ X, c := Finset.sum_congr rfl fun x _ => card_posSet x
    _ = c * #X := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

private theorem sum_freq_activeChars {c b : ℕ} (X : Finset (Fin c → Fin (2 ^ b))) :
    ∑ α ∈ activeChars X, freq X α = c * #X := by
  simp only [freq, Finset.card_filter]
  rw [Finset.sum_comm]
  have hinner (x : Fin c → Fin (2 ^ b)) (hx : x ∈ X) :
      (∑ α ∈ activeChars X, if α ∈ posSet x then 1 else 0) = c := by
    have hsub : posSet x ⊆ activeChars X := Finset.subset_biUnion_of_mem posSet hx
    rw [← Finset.card_filter, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr hsub, card_posSet]
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul, Nat.mul_comm]

private theorem pos_freq_of_mem_activeChars {c b : ℕ} {X : Finset (Fin c → Fin (2 ^ b))}
    {α : Fin c × Fin (2 ^ b)} (hα : α ∈ activeChars X) :
    1 ≤ freq X α := by
  obtain ⟨x, hx, hxα⟩ := Finset.mem_biUnion.mp hα
  exact Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hxα⟩⟩

private theorem pairwise_sortedChars {c b : ℕ} (X : Finset (Fin c → Fin (2 ^ b))) :
    (sortedChars X).Pairwise (fun α β => freq X β ≤ freq X α) := by
  have htrans : ∀ α β γ : Fin c × Fin (2 ^ b),
      decide (freq X β ≤ freq X α) = true →
      decide (freq X γ ≤ freq X β) = true →
      decide (freq X γ ≤ freq X α) = true :=
    fun _ _ _ h₁ h₂ => decide_eq_true (le_trans (of_decide_eq_true h₂) (of_decide_eq_true h₁))
  have htotal : ∀ α β : Fin c × Fin (2 ^ b),
      (decide (freq X β ≤ freq X α) || decide (freq X α ≤ freq X β)) = true :=
    fun α β => by
      rw [Bool.or_eq_true]
      rcases le_total (freq X β) (freq X α) with h | h
      · exact Or.inl (decide_eq_true h)
      · exact Or.inr (decide_eq_true h)
  simpa [sortedChars, decide_eq_true_eq] using
    List.pairwise_mergeSort htrans htotal (activeChars X).toList

private theorem freq_sortedChars_antitone {c b : ℕ} (X : Finset (Fin c → Fin (2 ^ b)))
    {i j : ℕ} (hi : i < (sortedChars X).length) (hj : j < (sortedChars X).length) (hij : i ≤ j) :
    freq X ((sortedChars X)[j]) ≤ freq X ((sortedChars X)[i]) := by
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · exact List.pairwise_iff_getElem.mp (pairwise_sortedChars X) i j hi hj hlt

/-- `i`-th frequency `n_i` in the decreasing order `sortedChars X` (`0` out of bounds). -/
private noncomputable def sortedFreq {c b : ℕ} (X : Finset (Fin c → Fin (2 ^ b))) (i : ℕ) : ℕ :=
  if hi : i < (sortedChars X).length then freq X ((sortedChars X)[i]) else 0

private theorem sortedFreq_antitone {c b : ℕ} (X : Finset (Fin c → Fin (2 ^ b)))
    {i j : ℕ} (hj : j < (sortedChars X).length) (hij : i ≤ j) :
    sortedFreq X j ≤ sortedFreq X i := by
  have hi : i < (sortedChars X).length := lt_of_le_of_lt hij hj
  simp only [sortedFreq, hi, hj, ↓reduceDIte]
  exact freq_sortedChars_antitone X hi hj hij

private theorem one_le_sortedFreq {c b : ℕ} (X : Finset (Fin c → Fin (2 ^ b)))
    {i : ℕ} (hi : i < (sortedChars X).length) :
    1 ≤ sortedFreq X i := by
  simp only [sortedFreq, hi, ↓reduceDIte]
  exact pos_freq_of_mem_activeChars (mem_sortedChars.mp (List.getElem_mem hi))

private theorem sum_sortedFreq {c b : ℕ} (X : Finset (Fin c → Fin (2 ^ b))) :
    ∑ i ∈ Finset.range (sortedChars X).length, sortedFreq X i = c * #X := by
  have hsum_get : ∑ i ∈ Finset.range (sortedChars X).length, sortedFreq X i =
      ((sortedChars X).map (freq X)).sum := by
    rw [← Fin.sum_univ_eq_sum_range]
    conv_rhs => rw [← List.ofFn_get (sortedChars X), List.map_ofFn, List.sum_ofFn]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [sortedFreq, i.isLt]
  rw [hsum_get]
  unfold sortedChars
  rw [((List.mergeSort_perm (activeChars X).toList _).map (freq X)).sum_eq,
    Finset.sum_map_toList, sum_freq_activeChars]

private theorem card_prefixChars_le {c b : ℕ} (X : Finset (Fin c → Fin (2 ^ b))) (r : ℕ) :
    #(prefixChars X r) ≤ r :=
  (List.toFinset_card_le _).trans (List.length_take_le r _)

private theorem prefixChars_length {c b : ℕ} (X : Finset (Fin c → Fin (2 ^ b))) :
    prefixChars X (sortedChars X).length = activeChars X := by
  ext α
  simp [prefixChars, List.take_length, mem_sortedChars]

private theorem prefixChars_succ {c b : ℕ} (X : Finset (Fin c → Fin (2 ^ b))) {r : ℕ}
    (hr : r < (sortedChars X).length) :
    prefixChars X (r + 1) = insert ((sortedChars X)[r]) (prefixChars X r) := by
  ext α
  simp only [prefixChars, List.mem_toFinset, List.take_add_one, List.mem_append,
    List.getElem?_eq_getElem hr, Option.toList_some, List.mem_singleton, Finset.mem_insert]
  exact Or.comm

private theorem prefixChars_mono {c b : ℕ} (X : Finset (Fin c → Fin (2 ^ b))) {r₁ r₂ : ℕ}
    (h : r₁ ≤ r₂) : prefixChars X r₁ ⊆ prefixChars X r₂ := by
  intro α hα
  simp only [prefixChars, List.mem_toFinset] at hα ⊢
  exact List.Sublist.mem hα (List.take_sublist_take_left h)

/-- Set `Γ_{≤ r}` of pairs `(y, j) ∈ X × Fin d` whose output `simpleTabTuple T₁ y j` collides with
some `x ∈ X \ {y}` such that `posSymmDiff x y ⊆ prefixChars X r` ([Thorup2013], Section 3,
p. 11). -/
private noncomputable def GammaSet {c d b : ℕ} (T₁ : DoubleTabTopSeed c d b)
    (X : Finset (Fin c → Fin (2 ^ b))) (r : ℕ) :
    Finset ((Fin c → Fin (2 ^ b)) × Fin d) :=
  (X ×ˢ Finset.univ).filter fun p =>
    ∃ x ∈ X, x ≠ p.1 ∧ posSymmDiff x p.1 ⊆ prefixChars X r ∧
      simpleTabTuple T₁ x p.2 = simpleTabTuple T₁ p.1 p.2

/-- Count `γ_{≤ r} = #(GammaSet T₁ X r)` ([Thorup2013], Section 3, p. 11). -/
private noncomputable def gamma {c d b : ℕ} (T₁ : DoubleTabTopSeed c d b)
    (X : Finset (Fin c → Fin (2 ^ b))) (r : ℕ) : ℕ :=
  #(GammaSet T₁ X r)

private theorem gammaSet_mono {c d b : ℕ} (T₁ : DoubleTabTopSeed c d b)
    (X : Finset (Fin c → Fin (2 ^ b))) {r₁ r₂ : ℕ} (h : r₁ ≤ r₂) :
    GammaSet T₁ X r₁ ⊆ GammaSet T₁ X r₂ := by
  intro p hp
  simp only [GammaSet, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hp ⊢
  rcases hp with ⟨hpX, x, hxX, hne, hsub, heq⟩
  exact ⟨hpX, x, hxX, hne, hsub.trans (prefixChars_mono X h), heq⟩

private theorem gamma_eq_zero_of_le_one {c d b : ℕ} (T₁ : DoubleTabTopSeed c d b)
    (X : Finset (Fin c → Fin (2 ^ b))) {r : ℕ} (hr : r ≤ 1) :
    gamma T₁ X r = 0 := by
  rw [gamma, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro p hp
  simp only [GammaSet, Finset.mem_filter] at hp
  rcases hp with ⟨_, x, _, hne, hsub, _⟩
  have h2 : 2 ≤ #(posSymmDiff x p.1) := two_le_card_posSymmDiff_of_ne hne
  have h1 : #(posSymmDiff x p.1) ≤ 1 :=
    (Finset.card_le_card hsub).trans ((card_prefixChars_le X r).trans hr)
  omega

/-- **Lemma 8 ([Thorup2013], Section 3, p. 12)**: if `X` violates `k`-uniqueness under
`simpleTabTuple T₁`, then `γ_{≤ ℓ*} = d * #X`. -/
private theorem gamma_length_eq {c d b : ℕ} (T₁ : DoubleTabTopSeed c d b)
    (X : Finset (Fin c → Fin (2 ^ b)))
    (hviol : ∀ y ∈ X, ∀ j : Fin d, ∃ x ∈ X, x ≠ y ∧
      simpleTabTuple T₁ x j = simpleTabTuple T₁ y j) :
    gamma T₁ X (sortedChars X).length = d * #X := by
  have hGamma : GammaSet T₁ X (sortedChars X).length = X ×ˢ Finset.univ := by
    ext ⟨y, j⟩
    simp only [GammaSet, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
      and_iff_left_iff_imp]
    intro hy
    obtain ⟨x, hx, hne, heq⟩ := hviol y hy j
    refine ⟨x, hx, hne, ?_, heq⟩
    rw [prefixChars_length]
    refine symmDiff_subset_union.trans (Finset.union_subset ?_ ?_)
    · exact Finset.subset_biUnion_of_mem posSet hx
    · exact Finset.subset_biUnion_of_mem posSet hy
  rw [gamma, hGamma, Finset.card_product, Finset.card_univ, Fintype.card_fin, Nat.mul_comm]

/-- Set `Φ_r` of output coordinates `j : Fin d` such that `((sortedChars X)[r], j)` is derivable
from `prefixChars X (r + 1)` ([Thorup2013], Section 3, p. 12). -/
private noncomputable def PhiSet {c d b : ℕ} (T₁ : DoubleTabTopSeed c d b)
    (X : Finset (Fin c → Fin (2 ^ b))) (r : ℕ) : Finset (Fin d) :=
  if hr : r < (sortedChars X).length then
    Finset.univ.filter fun j : Fin d =>
      ∃ x ∈ X, ∃ y ∈ X, (sortedChars X)[r] ∈ posSymmDiff x y ∧
        posSymmDiff x y ⊆ prefixChars X (r + 1) ∧
        simpleTabTuple T₁ x j = simpleTabTuple T₁ y j
  else ∅

/-- Count `ϕ_r = #(PhiSet T₁ X r)` of derivable output coordinates for `(sortedChars X)[r]`
([Thorup2013], Section 3, p. 12). -/
private noncomputable def phi {c d b : ℕ} (T₁ : DoubleTabTopSeed c d b)
    (X : Finset (Fin c → Fin (2 ^ b))) (r : ℕ) : ℕ :=
  #(PhiSet T₁ X r)

private theorem phi_zero_eq_zero {c d b : ℕ} (T₁ : DoubleTabTopSeed c d b)
    (X : Finset (Fin c → Fin (2 ^ b))) :
    phi T₁ X 0 = 0 := by
  rw [phi, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro j hj
  unfold PhiSet at hj
  split_ifs at hj with hr
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rcases hj with ⟨x, _, y, _, hmem, hsub, _⟩
    have hne : x ≠ y := by
      intro rfl
      simp [posSymmDiff] at hmem
    have h2 : 2 ≤ #(posSymmDiff x y) := two_le_card_posSymmDiff_of_ne hne
    have h1 : #(posSymmDiff x y) ≤ 1 := (Finset.card_le_card hsub).trans (card_prefixChars_le X 1)
    omega
  · exact Finset.notMem_empty j hj

private theorem exists_witness_of_mem_gammaSet_sdiff {c d b : ℕ}
    (T₁ : DoubleTabTopSeed c d b) (X : Finset (Fin c → Fin (2 ^ b))) {r : ℕ}
    (hr : r < (sortedChars X).length)
    {p : (Fin c → Fin (2 ^ b)) × Fin d}
    (hp : p ∈ GammaSet T₁ X (r + 1) \ GammaSet T₁ X r) :
    p.1 ∈ X ∧ p.2 ∈ PhiSet T₁ X r ∧
      ∃ x ∈ X, x ≠ p.1 ∧ (sortedChars X)[r] ∈ posSymmDiff x p.1 ∧
        posSymmDiff x p.1 ⊆ prefixChars X (r + 1) ∧
        simpleTabTuple T₁ x p.2 = simpleTabTuple T₁ p.1 p.2 := by
  have hp_in : p ∈ GammaSet T₁ X (r + 1) := (Finset.mem_sdiff.mp hp).1
  have hp_out : p ∉ GammaSet T₁ X r := (Finset.mem_sdiff.mp hp).2
  simp only [GammaSet, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    at hp_in hp_out
  rcases hp_in with ⟨hpX, x, hxX, hne, hsub, heq⟩
  have hmem_r : (sortedChars X)[r] ∈ posSymmDiff x p.1 := by
    by_contra hnot
    apply hp_out
    refine ⟨hpX, x, hxX, hne, fun β hβ => ?_, heq⟩
    have hβ' := hsub hβ
    rw [prefixChars_succ X hr, Finset.mem_insert] at hβ'
    rcases hβ' with rfl | hβ'
    · exact (hnot hβ).elim
    · exact hβ'
  have hj_phi : p.2 ∈ PhiSet T₁ X r := by
    simp only [PhiSet, hr, ↓reduceDIte, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨x, hxX, p.1, hpX, hmem_r, hsub, heq⟩
  exact ⟨hpX, hj_phi, x, hxX, hne, hmem_r, hsub, heq⟩

/-- **Lemma 9 ([Thorup2013], Section 3, Eq. (8), pp. 12–13)**: for each step `r < ℓ*`,
`γ_{≤ r + 1} - γ_{≤ r} ≤ 2 * ϕ_r * n_r`. -/
private theorem gamma_succ_sub_le {c d b : ℕ} (T₁ : DoubleTabTopSeed c d b)
    (X : Finset (Fin c → Fin (2 ^ b))) {r : ℕ} (hr : r < (sortedChars X).length) :
    gamma T₁ X (r + 1) - gamma T₁ X r ≤ 2 * (phi T₁ X r * sortedFreq X r) := by
  classical
  let α_r := (sortedChars X)[r]
  let D := GammaSet T₁ X (r + 1) \ GammaSet T₁ X r
  let S_r := X.filter fun x => α_r ∈ posSet x
  have hcard_D : gamma T₁ X (r + 1) - gamma T₁ X r = #D := by
    rw [gamma, gamma, ← Finset.card_sdiff_of_subset (gammaSet_mono T₁ X (Nat.le_succ r))]
  let D₁ := D.filter fun p => α_r ∈ posSet p.1
  let D₂ := D.filter fun p => α_r ∉ posSet p.1
  have hD_le : #D ≤ #D₁ + #D₂ := by
    refine (Finset.card_le_card fun p hp => ?_).trans (Finset.card_union_le D₁ D₂)
    simp only [D₁, D₂, Finset.mem_union, Finset.mem_filter, hp, true_and]
    exact em (α_r ∈ posSet p.1)
  have hD₁_sub : D₁ ⊆ S_r ×ˢ PhiSet T₁ X r := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpD, hp_pos⟩
    have hw := exists_witness_of_mem_gammaSet_sdiff T₁ X hr hpD
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hw.1, hp_pos⟩, hw.2.1⟩
  have hD₁_le : #D₁ ≤ phi T₁ X r * sortedFreq X r := by
    calc #D₁ ≤ #(S_r ×ˢ PhiSet T₁ X r) := Finset.card_le_card hD₁_sub
      _ = phi T₁ X r * sortedFreq X r := by
        simp only [Finset.card_product, sortedFreq, hr, ↓reduceDIte, Nat.mul_comm]
        rfl
  let w : (Fin c → Fin (2 ^ b)) × Fin d → (Fin c → Fin (2 ^ b)) × Fin d := fun p =>
    if hp : p ∈ D then
      (Classical.choose (exists_witness_of_mem_gammaSet_sdiff T₁ X hr hp).2.2, p.2)
    else p
  have hw_maps : ∀ p ∈ D₂, w p ∈ S_r ×ˢ PhiSet T₁ X r := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpD, hp_not⟩
    have hspec := Classical.choose_spec (exists_witness_of_mem_gammaSet_sdiff T₁ X hr hpD).2.2
    rcases hspec with ⟨hxX, _, hmem_symm, _, _⟩
    have hx_pos : α_r ∈ posSet (Classical.choose
        (exists_witness_of_mem_gammaSet_sdiff T₁ X hr hpD).2.2) := by
      rcases Finset.mem_symmDiff.mp hmem_symm with ⟨hx_in, _⟩ | ⟨hy_in, _⟩
      · exact hx_in
      · exact (hp_not hy_in).elim
    simp only [w, hpD, ↓reduceDIte, Finset.mem_product]
    exact ⟨Finset.mem_filter.mpr ⟨hxX, hx_pos⟩,
      (exists_witness_of_mem_gammaSet_sdiff T₁ X hr hpD).2.1⟩
  have hw_inj : Set.InjOn w D₂ := by
    intro p₁ hp₁ p₂ hp₂ heq
    rcases Finset.mem_filter.mp hp₁ with ⟨hp₁D, hp₁_not⟩
    rcases Finset.mem_filter.mp hp₂ with ⟨hp₂D, hp₂_not⟩
    simp only [w, hp₁D, hp₂D, ↓reduceDIte, Prod.ext_iff] at heq
    rcases heq with ⟨hx_eq, hj_eq⟩
    refine Prod.ext ?_ hj_eq
    by_contra hne_yz
    let x₁ := Classical.choose (exists_witness_of_mem_gammaSet_sdiff T₁ X hr hp₁D).2.2
    let x₂ := Classical.choose (exists_witness_of_mem_gammaSet_sdiff T₁ X hr hp₂D).2.2
    have hx₁₂ : x₁ = x₂ := hx_eq
    have hspec₁ : x₁ ∈ X ∧ x₁ ≠ p₁.1 ∧ (sortedChars X)[r] ∈ posSymmDiff x₁ p₁.1 ∧
        posSymmDiff x₁ p₁.1 ⊆ prefixChars X (r + 1) ∧
        simpleTabTuple T₁ x₁ p₁.2 = simpleTabTuple T₁ p₁.1 p₁.2 :=
      Classical.choose_spec (exists_witness_of_mem_gammaSet_sdiff T₁ X hr hp₁D).2.2
    have hspec₂ : x₂ ∈ X ∧ x₂ ≠ p₂.1 ∧ (sortedChars X)[r] ∈ posSymmDiff x₂ p₂.1 ∧
        posSymmDiff x₂ p₂.1 ⊆ prefixChars X (r + 1) ∧
        simpleTabTuple T₁ x₂ p₂.2 = simpleTabTuple T₁ p₂.1 p₂.2 :=
      Classical.choose_spec (exists_witness_of_mem_gammaSet_sdiff T₁ X hr hp₂D).2.2
    rcases hspec₁ with ⟨_, _, _, hsub₁, htab₁⟩
    rcases hspec₂ with ⟨_, _, _, hsub₂, htab₂⟩
    have hp₁_in : p₁ ∈ GammaSet T₁ X r := by
      rw [GammaSet, Finset.mem_filter]
      refine ⟨Finset.mem_product.mpr ⟨(exists_witness_of_mem_gammaSet_sdiff T₁ X hr hp₁D).1,
        Finset.mem_univ _⟩, p₂.1, (exists_witness_of_mem_gammaSet_sdiff T₁ X hr hp₂D).1,
        Ne.symm hne_yz, ?_, ?_⟩
      · intro β hβ
        have hβ_u := posSymmDiff_subset_union x₁ p₂.1 p₁.1 hβ
        have hβ_pre : β ∈ prefixChars X (r + 1) := by
          rcases Finset.mem_union.mp hβ_u with hβ₂ | hβ₁
          · rw [hx₁₂] at hβ₂
            exact hsub₂ hβ₂
          · exact hsub₁ hβ₁
        rw [prefixChars_succ X hr, Finset.mem_insert] at hβ_pre
        rcases hβ_pre with rfl | hβ_pre
        · exfalso
          rcases Finset.mem_symmDiff.mp hβ with ⟨h₂, _⟩ | ⟨h₁, _⟩
          · exact hp₂_not h₂
          · exact hp₁_not h₁
        · exact hβ_pre
      · rw [← hj_eq, ← hx₁₂] at htab₂
        exact htab₂.symm.trans htab₁
    exact (Finset.mem_sdiff.mp hp₁D).2 hp₁_in
  have hD₂_le : #D₂ ≤ phi T₁ X r * sortedFreq X r := by
    calc #D₂ ≤ #(S_r ×ˢ PhiSet T₁ X r) := Finset.card_le_card_of_injOn w hw_maps hw_inj
      _ = phi T₁ X r * sortedFreq X r := by
        simp only [Finset.card_product, sortedFreq, hr, ↓reduceDIte, Nat.mul_comm]
        rfl
  rw [hcard_D]
  omega

/-- Pure-`ℕ` summation by parts (Abel summation) for a non-increasing sequence `b`. -/
private theorem sum_mul_eq_sum_prefix_sub (a b : ℕ → ℕ) :
    ∀ m : ℕ, (∀ i < m, b (i + 1) ≤ b i) →
      ∑ i ∈ Finset.range (m + 1), a i * b i =
        (∑ i ∈ Finset.range m, (∑ j ∈ Finset.range (i + 1), a j) * (b i - b (i + 1))) +
          (∑ j ∈ Finset.range (m + 1), a j) * b m
  | 0, _ => by simp
  | m + 1, hmono => by
    have ih := sum_mul_eq_sum_prefix_sub a b m (fun i hi => hmono i (Nat.lt_succ_of_lt hi))
    have hbm : b (m + 1) ≤ b m := hmono m (Nat.lt_succ_self m)
    let S := ∑ j ∈ Finset.range (m + 1), a j
    have hstep : S * (b m - b (m + 1)) + (S + a (m + 1)) * b (m + 1) =
        S * b m + a (m + 1) * b (m + 1) := by
      rw [Nat.mul_sub_left_distrib, Nat.add_mul, ← Nat.add_assoc,
        Nat.sub_add_cancel (Nat.mul_le_mul_left S hbm)]
    conv_lhs => rw [Finset.sum_range_succ, ih]
    conv_rhs => rw [Finset.sum_range_succ _ m, Finset.sum_range_succ a (m + 1)]
    change (∑ i ∈ Finset.range m, (∑ j ∈ Finset.range (i + 1), a j) * (b i - b (i + 1))) +
        S * b m + a (m + 1) * b (m + 1) =
      (∑ i ∈ Finset.range m, (∑ j ∈ Finset.range (i + 1), a j) * (b i - b (i + 1))) +
        S * (b m - b (m + 1)) + (S + a (m + 1)) * b (m + 1)
    rw [Nat.add_assoc, ← hstep, Nat.add_assoc]

/-- If every prefix `1 ≤ ℓ ≤ ℓ*` has `< q * ℓ` derivable outputs, summation by parts yields
`∑_{i < ℓ*} ϕ_i * n_i < q * ∑_{i < ℓ*} n_i` ([Thorup2013], Section 3, Eqs. (9)–(11),
pp. 12–13). -/
private theorem sum_phi_mul_sortedFreq_lt {c d b q : ℕ} (T₁ : DoubleTabTopSeed c d b)
    (X : Finset (Fin c → Fin (2 ^ b))) (hlen : 0 < (sortedChars X).length)
    (hsmall : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ (sortedChars X).length →
      ∑ i ∈ Finset.range ℓ, phi T₁ X i < q * ℓ) :
    ∑ i ∈ Finset.range (sortedChars X).length, phi T₁ X i * sortedFreq X i <
      q * ∑ i ∈ Finset.range (sortedChars X).length, sortedFreq X i := by
  obtain ⟨m, hm⟩ : ∃ m, (sortedChars X).length = m + 1 := ⟨(sortedChars X).length - 1, by omega⟩
  rw [hm]
  have hmono : ∀ i < m, sortedFreq X (i + 1) ≤ sortedFreq X i := fun i hi =>
    sortedFreq_antitone X (by omega) (Nat.le_succ i)
  have hab₁ := sum_mul_eq_sum_prefix_sub (phi T₁ X) (sortedFreq X) m hmono
  have hab₂ := sum_mul_eq_sum_prefix_sub (fun _ => q) (sortedFreq X) m hmono
  rw [← Finset.mul_sum] at hab₂
  rw [hab₁, hab₂]
  have hsum_le :
      ∑ i ∈ Finset.range m,
          (∑ j ∈ Finset.range (i + 1), phi T₁ X j) * (sortedFreq X i - sortedFreq X (i + 1)) ≤
        ∑ i ∈ Finset.range m,
          (∑ j ∈ Finset.range (i + 1), q) * (sortedFreq X i - sortedFreq X (i + 1)) := by
    refine Finset.sum_le_sum fun i hi => Nat.mul_le_mul_right _ ?_
    have hi_lt : i < m := Finset.mem_range.mp hi
    have hlt := hsmall (i + 1) (by omega) (by omega)
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_comm]
    exact Nat.le_of_lt hlt
  have hlast_lt :
      (∑ j ∈ Finset.range (m + 1), phi T₁ X j) * sortedFreq X m <
        (∑ j ∈ Finset.range (m + 1), q) * sortedFreq X m := by
    have hlt := hsmall (m + 1) (by omega) (by omega)
    have hpos : 0 < sortedFreq X m := one_le_sortedFreq X (by omega)
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_comm (m + 1) q]
    exact Nat.mul_lt_mul_of_pos_right hlt hpos
  exact add_lt_add_of_le_of_lt hsum_le hlast_lt

private theorem gamma_le_two_mul_sum_phi_sortedFreq {c d b : ℕ} (T₁ : DoubleTabTopSeed c d b)
    (X : Finset (Fin c → Fin (2 ^ b))) :
    ∀ r ≤ (sortedChars X).length,
      gamma T₁ X r ≤ 2 * ∑ i ∈ Finset.range r, phi T₁ X i * sortedFreq X i
  | 0, _ => by
    have h0 := gamma_eq_zero_of_le_one T₁ X (by decide : 0 ≤ 1)
    simp [h0]
  | r + 1, hr => by
    have ih := gamma_le_two_mul_sum_phi_sortedFreq T₁ X r (Nat.le_of_succ_le hr)
    have hstep := gamma_succ_sub_le T₁ X (Nat.lt_of_succ_le hr)
    rw [Finset.sum_range_succ, Nat.mul_add]
    omega

/-- **Theorem 7(a) prefix existence ([Thorup2013], Section 3, pp. 12–13)**: when `c ≥ 1`, `q ≥ 1`,
`d = 2 * q * c`, and `X` is a non-empty key set violating `k`-uniqueness, some prefix `L_{≤ ℓ}` of
length `2 ≤ ℓ ≤ ℓ*` has at least `q * ℓ` derivable output characters. -/
private theorem exists_prefix_le_sum_phi {c d b q : ℕ} (hc : 1 ≤ c) (hq : 1 ≤ q)
    (hd : d = 2 * q * c) (T₁ : DoubleTabTopSeed c d b)
    (X : Finset (Fin c → Fin (2 ^ b))) (hX_ne : X.Nonempty)
    (hviol : ∀ y ∈ X, ∀ j : Fin d, ∃ x ∈ X, x ≠ y ∧
      simpleTabTuple T₁ x j = simpleTabTuple T₁ y j) :
    ∃ ℓ, 2 ≤ ℓ ∧ ℓ ≤ (sortedChars X).length ∧ q * ℓ ≤ ∑ i ∈ Finset.range ℓ, phi T₁ X i := by
  have hX_pos : 0 < #X := Finset.card_pos.mpr hX_ne
  have hsum_freq := sum_sortedFreq X
  have hlen_pos : 0 < (sortedChars X).length := by
    by_contra h0
    have hlen0 : (sortedChars X).length = 0 := by omega
    rw [hlen0, Finset.range_zero, Finset.sum_empty] at hsum_freq
    have hcX : 0 < c * #X := Nat.mul_pos hc hX_pos
    omega
  have hex : ∃ ℓ, 1 ≤ ℓ ∧ ℓ ≤ (sortedChars X).length ∧
      q * ℓ ≤ ∑ i ∈ Finset.range ℓ, phi T₁ X i := by
    by_contra! hsmall
    have hlt := sum_phi_mul_sortedFreq_lt T₁ X hlen_pos hsmall
    rw [hsum_freq] at hlt
    have hgamma_eq := gamma_length_eq T₁ X hviol
    have hgamma_le := gamma_le_two_mul_sum_phi_sortedFreq T₁ X (sortedChars X).length le_rfl
    have hdX : d * #X = 2 * (q * (c * #X)) := by
      rw [hd]
      ring
    omega
  rcases hex with ⟨ℓ, hℓ₁, hℓ_hi, hqℓ⟩
  have hℓ₂ : 2 ≤ ℓ := by
    by_contra hlt2
    have hℓ_eq : ℓ = 1 := by omega
    subst hℓ_eq
    rw [Finset.range_one, Finset.sum_singleton, phi_zero_eq_zero] at hqℓ
    omega
  exact ⟨ℓ, hℓ₂, hℓ_hi, hqℓ⟩

private theorem exists_eq_tuple_of_mem_phiSet {c d b ℓ : ℕ} [NeZero (2 * c)]
    (T₁ : DoubleTabTopSeed c d b) (X : Finset (Fin c → Fin (2 ^ b)))
    (hℓ_hi : ℓ ≤ (sortedChars X).length) (r : Fin ℓ) {j : Fin d}
    (hj : j ∈ PhiSet T₁ X r.val) :
    let L : Fin ℓ → Fin c × Fin (2 ^ b) := fun idx =>
      (sortedChars X)[idx.val]'(lt_of_lt_of_le idx.isLt hℓ_hi)
    ∃ g : Fin (2 * c) → Fin ℓ,
      lastIdx g = r ∧
      ∑ idx ∈ Finset.univ.image g,
        (BitString.equivFin b).symm (T₁ (L idx).1 j (L idx).2) = 0 := by
  classical
  intro L
  have hr_lt : r.val < (sortedChars X).length := lt_of_lt_of_le r.isLt hℓ_hi
  have hL_inj : Function.Injective L := fun i₁ i₂ h =>
    Fin.ext ((nodup_sortedChars X).getElem_inj_iff.mp h)
  simp only [PhiSet, hr_lt, ↓reduceDIte, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  rcases hj with ⟨x, _, y, _, hr_mem, hsub, htab⟩
  let B : Finset (Fin ℓ) := Finset.univ.filter fun idx => L idx ∈ posSymmDiff x y
  have hr_B : r ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ r, hr_mem⟩
  have hB_le_r : ∀ idx ∈ B, idx ≤ r := by
    intro idx hidx
    have hLidx : L idx ∈ prefixChars X (r.val + 1) := hsub (Finset.mem_filter.mp hidx).2
    simp only [prefixChars, List.mem_toFinset, List.mem_take_iff_getElem] at hLidx
    rcases hLidx with ⟨i, hi, heq⟩
    have hi_lt : i < r.val + 1 := lt_of_lt_of_le hi (Nat.min_le_left _ _)
    have hidx_eq : i = idx.val := (nodup_sortedChars X).getElem_inj_iff.mp heq
    exact Fin.le_iff_val_le_val.mpr (by omega)
  have hB_img : B.image L = posSymmDiff x y := by
    ext α
    simp only [B, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun ⟨idx, hα, heq⟩ => heq ▸ hα, fun hα => ?_⟩
    have hα_pre : α ∈ prefixChars X (r.val + 1) := hsub hα
    simp only [prefixChars, List.mem_toFinset, List.mem_take_iff_getElem] at hα_pre
    rcases hα_pre with ⟨i, hi, heq⟩
    have hi_lt : i < r.val + 1 := lt_of_lt_of_le hi (Nat.min_le_left _ _)
    exact ⟨⟨i, by omega⟩, heq ▸ hα, heq⟩
  have hB_card : #B ≤ 2 * c := by
    rw [← Finset.card_image_of_injective B hL_inj, hB_img]
    exact card_posSymmDiff_le x y
  let g : Fin (2 * c) → Fin ℓ := fun t =>
    if ht : t.val < B.toList.length then B.toList[t.val] else r
  have hg_img : Finset.univ.image g = B := by
    ext idx
    simp only [Finset.mem_image, Finset.mem_univ, true_and, g]
    constructor
    · rintro ⟨t, rfl⟩
      split_ifs with ht
      · exact Finset.mem_toList.mp (List.getElem_mem ht)
      · exact hr_B
    · intro hidx
      have hmem_list : idx ∈ B.toList := Finset.mem_toList.mpr hidx
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem_list
      have hi_2c : i < 2 * c := lt_of_lt_of_le (Finset.length_toList B ▸ hi) hB_card
      refine ⟨⟨i, hi_2c⟩, ?_⟩
      change (if _ : i < B.toList.length then B.toList[i] else r) = B.toList[i]
      split_ifs
      rfl
  refine ⟨g, ?_, ?_⟩
  · unfold lastIdx
    exact le_antisymm
      (Finset.max'_le _ _ _ fun idx hidx => hB_le_r idx (hg_img ▸ hidx))
      (Finset.le_max' _ r (hg_img.symm ▸ hr_B))
  · rw [hg_img]
    have hsum_img : ∑ α ∈ B.image L, (BitString.equivFin b).symm (T₁ α.1 j α.2) =
        ∑ idx ∈ B, (BitString.equivFin b).symm (T₁ (L idx).1 j (L idx).2) :=
      Finset.sum_image fun _ _ _ _ h => hL_inj h
    rw [← hsum_img, hB_img]
    exact (simpleTabTuple_eq_iff_sum_posSymmDiff_eq_zero T₁ x y j).mp htab

/-- **Violation of `IsKUnique` yields a satisfied efficient code (`[Thorup2013]`, Section 2 &
Theorem 7(a), pp. 10–13)**: if `c ≥ 1`, `q ≥ 1`, `d = 2 * q * c`, and
`¬ IsKUnique k (simpleTabTuple T₁)`, then there exist `2 ≤ ℓ ≤ c * k`,
`L : Fin ℓ → Fin c × Fin (2 ^ b)`, and `M : Fin (q * ℓ) → (Fin (2 * c) → Fin ℓ) × Fin d` such that
`SatisfiesCode T₁ L M`. -/
private theorem exists_satisfiesCode_of_not_isKUnique {c d b q k : ℕ} [NeZero (2 * c)]
    (hc : 1 ≤ c) (hq : 1 ≤ q) (hd : d = 2 * q * c) {T₁ : DoubleTabTopSeed c d b}
    (hnot : ¬ IsKUnique k (simpleTabTuple T₁)) :
    ∃ ℓ ∈ Finset.Icc 2 (c * k),
      ∃ (L : Fin ℓ → Fin c × Fin (2 ^ b)) (M : Fin (q * ℓ) → (Fin (2 * c) → Fin ℓ) × Fin d),
        SatisfiesCode T₁ L M := by
  classical
  unfold IsKUnique at hnot
  push Not at hnot
  rcases hnot with ⟨X, hX_ne, hX_le, hviol_raw⟩
  have hviol : ∀ y ∈ X, ∀ j : Fin d, ∃ x ∈ X, x ≠ y ∧
      simpleTabTuple T₁ x j = simpleTabTuple T₁ y j := by
    intro y hy j
    obtain ⟨x, hx, hne, heq⟩ := hviol_raw y hy j
    exact ⟨x, hx, hne, heq.symm⟩
  obtain ⟨ℓ, hℓ_lo, hℓ_hi, hqℓ⟩ := exists_prefix_le_sum_phi hc hq hd T₁ X hX_ne hviol
  have hℓ_ck : ℓ ≤ c * k :=
    hℓ_hi.trans ((length_sortedChars X).trans_le
      ((card_activeChars_le X).trans (Nat.mul_le_mul_left c hX_le)))
  let L : Fin ℓ → Fin c × Fin (2 ^ b) := fun idx =>
    (sortedChars X)[idx.val]'(lt_of_lt_of_le idx.isLt hℓ_hi)
  have hL_inj : Function.Injective L := fun i₁ i₂ h =>
    Fin.ext ((nodup_sortedChars X).getElem_inj_iff.mp h)
  let AllPairs : Finset (Fin ℓ × Fin d) :=
    Finset.univ.biUnion fun r : Fin ℓ => (PhiSet T₁ X r.val).image fun j => (r, j)
  have hcard_pairs : #AllPairs = ∑ i ∈ Finset.range ℓ, phi T₁ X i := by
    rw [Finset.card_biUnion]
    · rw [← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.ext_iff.mp h).2), phi]
    · intro r₁ _ r₂ _ hne s hs₁ hs₂ p hp
      have h₁ := hs₁ hp
      have h₂ := hs₂ hp
      simp only [Finset.mem_image] at h₁ h₂
      rcases h₁ with ⟨_, _, rfl⟩
      rcases h₂ with ⟨_, _, heq⟩
      exact (hne (Prod.ext_iff.mp heq).1.symm).elim
  have hlen_list : q * ℓ ≤ AllPairs.toList.length := by
    rw [Finset.length_toList, hcard_pairs]
    exact hqℓ
  let p_at (s : Fin (q * ℓ)) : Fin ℓ × Fin d :=
    AllPairs.toList[s.val]'(lt_of_lt_of_le s.isLt hlen_list)
  have hp_mem (s : Fin (q * ℓ)) : (p_at s).2 ∈ PhiSet T₁ X (p_at s).1.val := by
    have hmem : p_at s ∈ AllPairs :=
      Finset.mem_toList.mp (List.getElem_mem (lt_of_lt_of_le s.isLt hlen_list))
    simp only [AllPairs, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image] at hmem
    rcases hmem with ⟨r, j, hj, heq⟩
    have hr : r = (p_at s).1 := (Prod.ext_iff.mp heq).1
    have hj' : j = (p_at s).2 := (Prod.ext_iff.mp heq).2
    exact hr ▸ hj' ▸ hj
  let M : Fin (q * ℓ) → (Fin (2 * c) → Fin ℓ) × Fin d := fun s =>
    (Classical.choose (exists_eq_tuple_of_mem_phiSet T₁ X hℓ_hi (p_at s).1 (hp_mem s)),
      (p_at s).2)
  refine ⟨ℓ, Finset.mem_Icc.mpr ⟨hℓ_lo, hℓ_ck⟩, L, M, hL_inj, ?_, ?_⟩
  · intro s₁ s₂ heq
    have hspec₁ := (Classical.choose_spec
      (exists_eq_tuple_of_mem_phiSet T₁ X hℓ_hi (p_at s₁).1 (hp_mem s₁))).1
    have hspec₂ := (Classical.choose_spec
      (exists_eq_tuple_of_mem_phiSet T₁ X hℓ_hi (p_at s₂).1 (hp_mem s₂))).1
    have hp_eq : p_at s₁ = p_at s₂ :=
      Prod.ext (hspec₁.symm.trans ((Prod.ext_iff.mp heq).1.trans hspec₂)) (Prod.ext_iff.mp heq).2
    exact Fin.ext ((Finset.nodup_toList AllPairs).getElem_inj_iff.mp hp_eq)
  · intro s
    exact (Classical.choose_spec
      (exists_eq_tuple_of_mem_phiSet T₁ X hℓ_hi (p_at s).1 (hp_mem s))).2

/-! ## Section 5: Efficient-code seed counting (`[Thorup2013]`, §2, Eqs. (6)–(7)) -/

/-- Subset satisfaction predicate: `T₁` satisfies the equations of `(L, M)` indexed by `S`. -/
private def SatisfiesSub {c d b q ℓ : ℕ}
    (T₁ : DoubleTabTopSeed c d b) (L : Fin ℓ → Fin c × Fin (2 ^ b))
    (M : Fin (q * ℓ) → (Fin (2 * c) → Fin ℓ) × Fin d)
    (S : Finset (Fin (q * ℓ))) : Prop :=
  ∀ r ∈ S,
    ∑ idx ∈ Finset.univ.image (M r).1,
      (BitString.equivFin b).symm (T₁ (L idx).1 (M r).2 (L idx).2) = 0

private instance {c d b q ℓ : ℕ}
    (T₁ : DoubleTabTopSeed c d b) (L : Fin ℓ → Fin c × Fin (2 ^ b))
    (M : Fin (q * ℓ) → (Fin (2 * c) → Fin ℓ) × Fin d)
    (S : Finset (Fin (q * ℓ))) : Decidable (SatisfiesSub T₁ L M S) := by
  unfold SatisfiesSub
  infer_instance

/-- Updating a single coordinate `(p.1, j₀, p.2)` of `T₁`. -/
private def updateTopSeed {c d b : ℕ} (T₁ : DoubleTabTopSeed c d b)
    (p : Fin c × Fin (2 ^ b)) (j₀ : Fin d) (v : Fin (2 ^ b)) : DoubleTabTopSeed c d b :=
  fun i j a => if (i, a) = p ∧ j = j₀ then v else T₁ i j a

@[simp]
private theorem updateTopSeed_self {c d b : ℕ} (T₁ : DoubleTabTopSeed c d b)
    (p : Fin c × Fin (2 ^ b)) (j₀ : Fin d) (v : Fin (2 ^ b)) :
    updateTopSeed T₁ p j₀ v p.1 j₀ p.2 = v := by
  simp [updateTopSeed]

private theorem updateTopSeed_of_ne {c d b : ℕ} (T₁ : DoubleTabTopSeed c d b)
    (p : Fin c × Fin (2 ^ b)) (j₀ : Fin d) (v : Fin (2 ^ b))
    {i : Fin c} {j : Fin d} {a : Fin (2 ^ b)} (hne : (i, a) ≠ p ∨ j ≠ j₀) :
    updateTopSeed T₁ p j₀ v i j a = T₁ i j a := by
  unfold updateTopSeed
  split_ifs with h
  · rcases hne with h₁ | h₂
    · exact (h₁ h.1).elim
    · exact (h₂ h.2).elim
  · rfl

@[simp]
private theorem updateTopSeed_updateTopSeed {c d b : ℕ} (T₁ : DoubleTabTopSeed c d b)
    (p : Fin c × Fin (2 ^ b)) (j₀ : Fin d) (v₁ v₂ : Fin (2 ^ b)) :
    updateTopSeed (updateTopSeed T₁ p j₀ v₁) p j₀ v₂ = updateTopSeed T₁ p j₀ v₂ := by
  ext i j a
  unfold updateTopSeed
  split_ifs <;> rfl

@[simp]
private theorem updateTopSeed_eq_self {c d b : ℕ} (T₁ : DoubleTabTopSeed c d b)
    (p : Fin c × Fin (2 ^ b)) (j₀ : Fin d) :
    updateTopSeed T₁ p j₀ (T₁ p.1 j₀ p.2) = T₁ := by
  ext i j a
  unfold updateTopSeed
  split_ifs with h
  · rcases h with ⟨hp, rfl⟩
    rcases Prod.ext_iff.mp hp with ⟨rfl, rfl⟩
    rfl
  · rfl

/-- Peeling one equation `r₀ ∈ S` whose `lastIdx (M r₀).1` is maximal on `S` multiplies the number
of compatible tables `T₁` by `2 ^ b` ([Thorup2013], Section 2, p. 11). -/
private theorem card_filter_satisfiesSub_erase {c d b q ℓ : ℕ} [NeZero (2 * c)]
    {L : Fin ℓ → Fin c × Fin (2 ^ b)} (hL : Function.Injective L)
    {M : Fin (q * ℓ) → (Fin (2 * c) → Fin ℓ) × Fin d}
    (hM : Function.Injective (fun r : Fin (q * ℓ) => (lastIdx (M r).1, (M r).2)))
    {S : Finset (Fin (q * ℓ))} {r₀ : Fin (q * ℓ)} (hr₀ : r₀ ∈ S)
    (hmax : ∀ r ∈ S, lastIdx (M r).1 ≤ lastIdx (M r₀).1) :
    #(Finset.univ.filter fun T₁ : DoubleTabTopSeed c d b => SatisfiesSub T₁ L M (S.erase r₀)) =
      2 ^ b * #(Finset.univ.filter fun T₁ : DoubleTabTopSeed c d b => SatisfiesSub T₁ L M S) := by
  classical
  let idx₀ := lastIdx (M r₀).1
  let p₀ := L idx₀
  let j₀ := (M r₀).2
  let I₀ := (Finset.univ.image (M r₀).1).erase idx₀
  let restSum (T₁ : DoubleTabTopSeed c d b) : BitString b :=
    ∑ idx ∈ I₀, (BitString.equivFin b).symm (T₁ (L idx).1 j₀ (L idx).2)
  have hne_other {r : Fin (q * ℓ)} (hr : r ∈ S.erase r₀)
      {idx : Fin ℓ} (hidx : idx ∈ Finset.univ.image (M r).1) :
      L idx ≠ p₀ ∨ (M r).2 ≠ j₀ := by
    by_contra! h
    rcases h with ⟨hLp, hj⟩
    have hidx_eq : idx = idx₀ := hL hLp
    have hle₁ : idx₀ ≤ lastIdx (M r).1 := hidx_eq ▸ Finset.le_max' _ idx hidx
    have hle₂ : lastIdx (M r).1 ≤ idx₀ := hmax r (Finset.mem_of_mem_erase hr)
    have hlast_eq : lastIdx (M r).1 = idx₀ := le_antisymm hle₂ hle₁
    have hr_eq : r = r₀ := hM (Prod.ext hlast_eq hj)
    exact (Finset.ne_of_mem_erase hr) hr_eq
  have hsub_upd (T₁ : DoubleTabTopSeed c d b) (v : Fin (2 ^ b)) :
      SatisfiesSub (updateTopSeed T₁ p₀ j₀ v) L M (S.erase r₀) ↔
        SatisfiesSub T₁ L M (S.erase r₀) := by
    refine forall₂_congr fun r hr => ?_
    have hsum : ∑ idx ∈ Finset.univ.image (M r).1,
        (BitString.equivFin b).symm (updateTopSeed T₁ p₀ j₀ v (L idx).1 (M r).2 (L idx).2) =
      ∑ idx ∈ Finset.univ.image (M r).1,
        (BitString.equivFin b).symm (T₁ (L idx).1 (M r).2 (L idx).2) := by
      refine Finset.sum_congr rfl fun idx hidx => ?_
      rw [updateTopSeed_of_ne T₁ p₀ j₀ v (hne_other hr hidx)]
    rw [hsum]
  have hrest_upd (T₁ : DoubleTabTopSeed c d b) (v : Fin (2 ^ b)) :
      restSum (updateTopSeed T₁ p₀ j₀ v) = restSum T₁ := by
    refine Finset.sum_congr rfl fun idx hidx => ?_
    have hne_idx : idx ≠ idx₀ := Finset.ne_of_mem_erase hidx
    rw [updateTopSeed_of_ne T₁ p₀ j₀ v (Or.inl fun h => hne_idx (hL h))]
  have hr₀_eq (T₁ : DoubleTabTopSeed c d b) :
      (∑ idx ∈ Finset.univ.image (M r₀).1,
        (BitString.equivFin b).symm (T₁ (L idx).1 j₀ (L idx).2) = 0) ↔
      T₁ p₀.1 j₀ p₀.2 = BitString.equivFin b (restSum T₁) := by
    have hmem₀ : idx₀ ∈ Finset.univ.image (M r₀).1 := lastIdx_mem_image (M r₀).1
    rw [← Finset.sum_erase_add _ _ hmem₀]
    change restSum T₁ + (BitString.equivFin b).symm (T₁ p₀.1 j₀ p₀.2) = 0 ↔ _
    constructor
    · intro h
      have hsymm : (BitString.equivFin b).symm (T₁ p₀.1 j₀ p₀.2) = restSum T₁ := by
        calc (BitString.equivFin b).symm (T₁ p₀.1 j₀ p₀.2)
            = restSum T₁ + (restSum T₁ + (BitString.equivFin b).symm (T₁ p₀.1 j₀ p₀.2)) :=
              (BitString.add_cancel_left _ _).symm
          _ = restSum T₁ := by rw [h, add_zero]
      rw [← hsymm, Equiv.apply_symm_apply]
    · intro h
      rw [h, Equiv.symm_apply_apply, BitString.add_self]
  let A := (Finset.univ : Finset (Fin (2 ^ b))) ×ˢ
    (Finset.univ.filter fun T₁ : DoubleTabTopSeed c d b => SatisfiesSub T₁ L M S)
  let B := Finset.univ.filter fun T₁ : DoubleTabTopSeed c d b => SatisfiesSub T₁ L M (S.erase r₀)
  have hbij : #B = #A := by
    refine Finset.card_bij
      (fun T₁ _ => (T₁ p₀.1 j₀ p₀.2, updateTopSeed T₁ p₀ j₀ (BitString.equivFin b (restSum T₁))))
      (fun T₁ hT₁ => ?_) (fun T₁ hT₁ T₁' hT₁' heq => ?_) (fun ⟨v, T₁⟩ hp => ?_)
    · have hsub : SatisfiesSub T₁ L M (S.erase r₀) := (Finset.mem_filter.mp hT₁).2
      refine Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        fun r hr => ?_⟩⟩
      by_cases hrr₀ : r = r₀
      · subst hrr₀
        dsimp only
        rw [hr₀_eq, updateTopSeed_self, hrest_upd]
      · exact ((hsub_upd T₁ _).mpr hsub) r (Finset.mem_erase.mpr ⟨hrr₀, hr⟩)
    · rcases Prod.ext_iff.mp heq with ⟨hval, hupd⟩
      dsimp only at hval hupd
      calc T₁ = updateTopSeed (updateTopSeed T₁ p₀ j₀ (BitString.equivFin b (restSum T₁)))
            p₀ j₀ (T₁ p₀.1 j₀ p₀.2) := by
            rw [updateTopSeed_updateTopSeed, updateTopSeed_eq_self]
        _ = updateTopSeed (updateTopSeed T₁' p₀ j₀ (BitString.equivFin b (restSum T₁')))
            p₀ j₀ (T₁' p₀.1 j₀ p₀.2) := by rw [hupd, hval]
        _ = T₁' := by rw [updateTopSeed_updateTopSeed, updateTopSeed_eq_self]
    · have hS : SatisfiesSub T₁ L M S := (Finset.mem_filter.mp (Finset.mem_product.mp hp).2).2
      have hS_er : SatisfiesSub T₁ L M (S.erase r₀) :=
        fun r hr => hS r (Finset.mem_of_mem_erase hr)
      have hr₀_T₁ : T₁ p₀.1 j₀ p₀.2 = BitString.equivFin b (restSum T₁) :=
        (hr₀_eq T₁).mp (hS r₀ hr₀)
      refine ⟨updateTopSeed T₁ p₀ j₀ v,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hsub_upd T₁ v).mpr hS_er⟩, ?_⟩
      refine Prod.ext (by simp) ?_
      dsimp only
      rw [updateTopSeed_updateTopSeed, hrest_upd, ← hr₀_T₁, updateTopSeed_eq_self]
  rw [hbij, Finset.card_product, Finset.card_univ, Fintype.card_fin]

private theorem card_filter_satisfiesSub_eq {c d b q ℓ : ℕ} [NeZero (2 * c)]
    {L : Fin ℓ → Fin c × Fin (2 ^ b)} (hL : Function.Injective L)
    {M : Fin (q * ℓ) → (Fin (2 * c) → Fin ℓ) × Fin d}
    (hM : Function.Injective (fun r : Fin (q * ℓ) => (lastIdx (M r).1, (M r).2))) :
    ∀ (n : ℕ) (S : Finset (Fin (q * ℓ))), #S = n →
      (2 ^ b) ^ n *
        #(Finset.univ.filter fun T₁ : DoubleTabTopSeed c d b => SatisfiesSub T₁ L M S) =
      Fintype.card (DoubleTabTopSeed c d b)
  | 0, S, hcard => by
    have hS : S = ∅ := Finset.card_eq_zero.mp hcard
    subst hS
    have hall : (Finset.univ.filter fun T₁ : DoubleTabTopSeed c d b =>
        SatisfiesSub T₁ L M ∅) = Finset.univ := by
      ext T₁
      simp [SatisfiesSub]
    rw [hall, pow_zero, one_mul, Finset.card_univ]
  | n + 1, S, hcard => by
    classical
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    let img := S.image fun r => lastIdx (M r).1
    have himg : img.Nonempty := hne.image fun r => lastIdx (M r).1
    obtain ⟨r₀, hr₀, hr₀_eq⟩ := Finset.mem_image.mp (Finset.max'_mem img himg)
    have hmax : ∀ r ∈ S, lastIdx (M r).1 ≤ lastIdx (M r₀).1 := fun r hr => by
      rw [hr₀_eq]
      exact Finset.le_max' img _ (Finset.mem_image_of_mem _ hr)
    have hcard_er : #(S.erase r₀) = n := by
      rw [Finset.card_erase_of_mem hr₀, hcard, Nat.add_sub_cancel]
    have ih := card_filter_satisfiesSub_eq hL hM n (S.erase r₀) hcard_er
    have her := card_filter_satisfiesSub_erase (b := b) hL hM hr₀ hmax
    rw [pow_succ, Nat.mul_assoc, ← her, ih]

/-- **Equation-system seed count ([Thorup2013], Section 2, p. 11)**: for any `(L, M)`, at most
`|Θ_top| / (2 ^ b) ^ (q * ℓ)` top-level tables `T₁` satisfy `SatisfiesCode T₁ L M`. -/
private theorem card_filter_satisfiesCode_le {c d b q ℓ : ℕ} [NeZero (2 * c)]
    (L : Fin ℓ → Fin c × Fin (2 ^ b))
    (M : Fin (q * ℓ) → (Fin (2 * c) → Fin ℓ) × Fin d) :
    (2 ^ b) ^ (q * ℓ) *
      #(Finset.univ.filter fun T₁ : DoubleTabTopSeed c d b => SatisfiesCode T₁ L M) ≤
    Fintype.card (DoubleTabTopSeed c d b) := by
  by_cases hLM : Function.Injective L ∧
      Function.Injective (fun r : Fin (q * ℓ) => (lastIdx (M r).1, (M r).2))
  · have hfilt : (Finset.univ.filter fun T₁ : DoubleTabTopSeed c d b => SatisfiesCode T₁ L M) =
        Finset.univ.filter fun T₁ : DoubleTabTopSeed c d b =>
          SatisfiesSub T₁ L M Finset.univ := by
      ext T₁
      simp [SatisfiesCode, SatisfiesSub, hLM.1, hLM.2]
    rw [hfilt, card_filter_satisfiesSub_eq hLM.1 hLM.2 (q * ℓ) Finset.univ
      (by simp)]
  · have hfilt : (Finset.univ.filter fun T₁ : DoubleTabTopSeed c d b => SatisfiesCode T₁ L M) =
        ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro T₁ hT₁
      have hcode := (Finset.mem_filter.mp hT₁).2
      exact hLM ⟨hcode.1, hcode.2.1⟩
    rw [hfilt, Finset.card_empty, Nat.mul_zero]
    exact Nat.zero_le _

/-- Union bound over all codes `(L, M)` of length `ℓ` ([Thorup2013], Section 2, Eq. (6), p. 11). -/
private theorem card_filter_exists_satisfiesCode_le {c d b q ℓ : ℕ} [NeZero (2 * c)]
    (hq : 1 ≤ q) :
    (2 ^ ((q - 1) * b)) ^ ℓ *
      #(Finset.univ.filter fun T₁ : DoubleTabTopSeed c d b =>
        ∃ (L : Fin ℓ → Fin c × Fin (2 ^ b))
          (M : Fin (q * ℓ) → (Fin (2 * c) → Fin ℓ) × Fin d),
          SatisfiesCode T₁ L M) ≤
    (c * (ℓ ^ (2 * c) * d) ^ q) ^ ℓ * Fintype.card (DoubleTabTopSeed c d b) := by
  classical
  let CodeType := (Fin ℓ → Fin c × Fin (2 ^ b)) × (Fin (q * ℓ) → (Fin (2 * c) → Fin ℓ) × Fin d)
  let E := Finset.univ.filter fun T₁ : DoubleTabTopSeed c d b =>
    ∃ (L : Fin ℓ → Fin c × Fin (2 ^ b)) (M : Fin (q * ℓ) → (Fin (2 * c) → Fin ℓ) × Fin d),
      SatisfiesCode T₁ L M
  have hsub : E ⊆ (Finset.univ : Finset CodeType).biUnion fun p =>
      Finset.univ.filter fun T₁ : DoubleTabTopSeed c d b => SatisfiesCode T₁ p.1 p.2 := by
    intro T₁ hT₁
    rcases (Finset.mem_filter.mp hT₁).2 with ⟨L, M, hcode⟩
    exact Finset.mem_biUnion.mpr ⟨(L, M), Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcode⟩⟩
  have hsum_le : (2 ^ b) ^ (q * ℓ) * #E ≤
      Fintype.card CodeType * Fintype.card (DoubleTabTopSeed c d b) := by
    calc (2 ^ b) ^ (q * ℓ) * #E
        ≤ (2 ^ b) ^ (q * ℓ) * ∑ p : CodeType,
            #(Finset.univ.filter fun T₁ : DoubleTabTopSeed c d b => SatisfiesCode T₁ p.1 p.2) :=
          Nat.mul_le_mul_left _ ((Finset.card_le_card hsub).trans Finset.card_biUnion_le)
      _ = ∑ p : CodeType, (2 ^ b) ^ (q * ℓ) *
            #(Finset.univ.filter fun T₁ : DoubleTabTopSeed c d b => SatisfiesCode T₁ p.1 p.2) :=
          Finset.mul_sum _ _ _
      _ ≤ ∑ _p : CodeType, Fintype.card (DoubleTabTopSeed c d b) :=
          Finset.sum_le_sum fun p _ => card_filter_satisfiesCode_le p.1 p.2
      _ = Fintype.card CodeType * Fintype.card (DoubleTabTopSeed c d b) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hcard_code : Fintype.card CodeType =
      (2 ^ b) ^ ℓ * (c * (ℓ ^ (2 * c) * d) ^ q) ^ ℓ := by
    simp only [CodeType, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
    rw [Nat.mul_pow c (2 ^ b) ℓ, Nat.mul_pow c _ ℓ, ← Nat.pow_mul _ q ℓ]
    ring
  have hpow_lhs : (2 ^ b) ^ (q * ℓ) = (2 ^ b) ^ ℓ * (2 ^ ((q - 1) * b)) ^ ℓ := by
    have hq_split : b * (q * ℓ) = b * ℓ + (q - 1) * b * ℓ := by
      calc b * (q * ℓ) = b * ((1 + (q - 1)) * ℓ) := by rw [Nat.add_sub_of_le hq]
        _ = b * ℓ + (q - 1) * b * ℓ := by ring
    rw [← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_add, hq_split]
  rw [hpow_lhs, hcard_code, Nat.mul_assoc, Nat.mul_assoc] at hsum_le
  have hpos_pow : 0 < (2 ^ b) ^ ℓ := by
    rw [← Nat.pow_mul]
    exact Nat.two_pow_pos (b * ℓ)
  exact Nat.le_of_mul_le_mul_left hsum_le hpos_pow

/-- Geometric-series tail bound in `ℕ`: when `2 * B ≤ W` and `W ^ ℓ * g ℓ ≤ B ^ ℓ * N`,
`W ^ m * ∑_{i < s} g (m + i) ≤ 2 * B ^ m * N`. -/
private theorem tail_sum_bound {B W N : ℕ} (hW : 0 < W) (hBW : 2 * B ≤ W) (g : ℕ → ℕ)
    (hg : ∀ ℓ, W ^ ℓ * g ℓ ≤ B ^ ℓ * N) :
    ∀ (s m : ℕ), W ^ m * (∑ i ∈ Finset.range s, g (m + i)) ≤ 2 * B ^ m * N
  | 0, m => by simp
  | s + 1, m => by
    have ih := tail_sum_bound hW hBW g hg s (m + 1)
    have hsum : ∑ i ∈ Finset.range (s + 1), g (m + i) =
        g m + ∑ i ∈ Finset.range s, g (m + 1 + i) := by
      rw [Finset.sum_range_succ']
      ac_rfl
    rw [hsum, Nat.mul_add]
    have hmul : W * (W ^ m * g m + W ^ m * ∑ i ∈ Finset.range s, g (m + 1 + i)) ≤
        W * (2 * B ^ m * N) := by
      have h₁ : W * (W ^ m * g m) ≤ W * (B ^ m * N) :=
        Nat.mul_le_mul_left W (hg m)
      have h₂ : W * (W ^ m * ∑ i ∈ Finset.range s, g (m + 1 + i)) ≤ W * (B ^ m * N) := by
        calc W * (W ^ m * ∑ i ∈ Finset.range s, g (m + 1 + i))
            = W ^ (m + 1) * ∑ i ∈ Finset.range s, g (m + 1 + i) := by
              rw [← Nat.mul_assoc, ← pow_succ']
          _ ≤ 2 * B ^ (m + 1) * N := ih
          _ = (2 * B) * (B ^ m * N) := by rw [pow_succ']; ring
          _ ≤ W * (B ^ m * N) := Nat.mul_le_mul_right _ hBW
      calc W * (W ^ m * g m + W ^ m * ∑ i ∈ Finset.range s, g (m + 1 + i))
          = W * (W ^ m * g m) + W * (W ^ m * ∑ i ∈ Finset.range s, g (m + 1 + i)) :=
            Nat.mul_add _ _ _
        _ ≤ W * (B ^ m * N) + W * (B ^ m * N) := Nat.add_le_add h₁ h₂
        _ = W * (2 * B ^ m * N) := by ring
    exact Nat.le_of_mul_le_mul_left hmul hW

/-- Per-step efficient-code counting factor `c * ((c * k) ^ (2 * c) * d) ^ q` from
[Thorup2013], Section 2, Eqs. (6)–(7), p. 11. -/
@[expose] def doubleTabCodeBound (c d q k : ℕ) : ℕ :=
  c * ((c * k) ^ (2 * c) * d) ^ q

/-- **Thorup's Universal `k`-Uniqueness Bound ([Thorup2013], Theorem 1(a), Section 2 Eqs. (6)–(7),
and Section 3 Theorem 7(a), pp. 4, 11–13)**:
For `c ≥ 1`, `q ≥ 1`, `d = 2 * q * c`, and `2 * doubleTabCodeBound c d q k ≤ 2 ^ ((q - 1) * b)`,
the number of top-level tables `T₁ : DoubleTabTopSeed c d b` for which `simpleTabTuple T₁` fails to
be `k`-unique satisfies
`(2 ^ ((q - 1) * b)) ^ 2 * #{T₁ | ¬ IsKUnique k (simpleTabTuple T₁)} ≤
  2 * (doubleTabCodeBound c d q k) ^ 2 * Fintype.card (DoubleTabTopSeed c d b)`. -/
theorem card_not_isKUnique_le {c d b q k : ℕ} (hc : 1 ≤ c) (hq : 1 ≤ q) (hd : d = 2 * q * c)
    (hbound : 2 * doubleTabCodeBound c d q k ≤ 2 ^ ((q - 1) * b)) :
    (2 ^ ((q - 1) * b)) ^ 2 *
      #(Finset.univ.filter fun T₁ : DoubleTabTopSeed c d b =>
        ¬ IsKUnique k (simpleTabTuple T₁)) ≤
    2 * (doubleTabCodeBound c d q k) ^ 2 * Fintype.card (DoubleTabTopSeed c d b) := by
  classical
  have : NeZero (2 * c) := ⟨by omega⟩
  let W := 2 ^ ((q - 1) * b)
  let B := doubleTabCodeBound c d q k
  let N := Fintype.card (DoubleTabTopSeed c d b)
  let g (ℓ : ℕ) : ℕ :=
    if ℓ ≤ c * k then
      #(Finset.univ.filter fun T₁ : DoubleTabTopSeed c d b =>
        ∃ (L : Fin ℓ → Fin c × Fin (2 ^ b))
          (M : Fin (q * ℓ) → (Fin (2 * c) → Fin ℓ) × Fin d),
          SatisfiesCode T₁ L M)
    else 0
  have hg (ℓ : ℕ) : W ^ ℓ * g ℓ ≤ B ^ ℓ * N := by
    dsimp only [g]
    split_ifs with hℓ
    · calc W ^ ℓ * #(Finset.univ.filter fun T₁ : DoubleTabTopSeed c d b =>
            ∃ (L : Fin ℓ → Fin c × Fin (2 ^ b))
              (M : Fin (q * ℓ) → (Fin (2 * c) → Fin ℓ) × Fin d),
              SatisfiesCode T₁ L M)
          ≤ (c * (ℓ ^ (2 * c) * d) ^ q) ^ ℓ * N := card_filter_exists_satisfiesCode_le hq
        _ ≤ B ^ ℓ * N := by
          refine Nat.mul_le_mul_right N (Nat.pow_le_pow_left ?_ ℓ)
          exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left
            (Nat.mul_le_mul_right d (Nat.pow_le_pow_left hℓ (2 * c))) q)
    · simp
  let Bad := Finset.univ.filter fun T₁ : DoubleTabTopSeed c d b =>
    ¬ IsKUnique k (simpleTabTuple T₁)
  have hBad_sub : Bad ⊆ (Finset.range (c * k - 1)).biUnion fun i =>
      Finset.univ.filter fun T₁ : DoubleTabTopSeed c d b =>
        ∃ (L : Fin (2 + i) → Fin c × Fin (2 ^ b))
          (M : Fin (q * (2 + i)) → (Fin (2 * c) → Fin (2 + i)) × Fin d),
          SatisfiesCode T₁ L M := by
    intro T₁ hT₁
    obtain ⟨ℓ, hℓ_Icc, L, M, hcode⟩ :=
      exists_satisfiesCode_of_not_isKUnique hc hq hd (Finset.mem_filter.mp hT₁).2
    rcases Finset.mem_Icc.mp hℓ_Icc with ⟨hℓ_lo, hℓ_hi⟩
    have hi_eq : 2 + (ℓ - 2) = ℓ := by omega
    refine Finset.mem_biUnion.mpr ⟨ℓ - 2, Finset.mem_range.mpr (by omega), ?_⟩
    rw [hi_eq]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, L, M, hcode⟩
  have hBad_le : #Bad ≤ ∑ i ∈ Finset.range (c * k - 1), g (2 + i) := by
    refine (Finset.card_le_card hBad_sub).trans (Finset.card_biUnion_le.trans ?_)
    refine Finset.sum_le_sum fun i hi => ?_
    have hi_lt : i < c * k - 1 := Finset.mem_range.mp hi
    have h2i : 2 + i ≤ c * k := by omega
    simp [g, h2i]
  calc W ^ 2 * #Bad
      ≤ W ^ 2 * ∑ i ∈ Finset.range (c * k - 1), g (2 + i) := Nat.mul_le_mul_left _ hBad_le
    _ ≤ 2 * B ^ 2 * N := tail_sum_bound (Nat.two_pow_pos _) hbound g hg (c * k - 1) 2

/-- Specialization of `card_not_isKUnique_le` to `q = 4` (`d = 8 * c`, `[Thorup2013]`, Theorem 1(a),
p. 4): when `2 * doubleTabCodeBound c (8 * c) 4 k ≤ 2 ^ (3 * b)`, at most a
`2 * (doubleTabCodeBound c (8 * c) 4 k) ^ 2 / 2 ^ (6 * b)` fraction of top-level tables fail to be
`k`-unique. -/
theorem card_not_isKUnique_eight_mul_le {c b k : ℕ} (hc : 1 ≤ c)
    (hbound : 2 * doubleTabCodeBound c (8 * c) 4 k ≤ 2 ^ (3 * b)) :
    2 ^ (6 * b) *
      #(Finset.univ.filter fun T₁ : DoubleTabTopSeed c (8 * c) b =>
        ¬ IsKUnique k (simpleTabTuple T₁)) ≤
    2 * (doubleTabCodeBound c (8 * c) 4 k) ^ 2 * Fintype.card (DoubleTabTopSeed c (8 * c) b) := by
  have h := card_not_isKUnique_le (d := 8 * c) (q := 4) hc (by decide) (by ring) hbound
  have hpow : (2 ^ ((4 - 1) * b)) ^ 2 = 2 ^ (6 * b) := by
    rw [← Nat.pow_mul]
    congr 1
    ring
  rwa [hpow] at h

end Cslib.Probability
