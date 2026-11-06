/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Crypto.Protocols.Cipher.LubyRackoff
public import Complexity.Languages.Probabilistic.RandomPermutation
public import Mathlib.Data.Fintype.CardEmbedding
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF.Uniform
import Complexity.Probability.Product
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Block cipher networks: SPNs, unbalanced Feistel networks, periodicity, and Feistel distinguishers

This module complements `Complexity.Crypto.Protocols.Cipher.LubyRackoff` with structural and
concrete-security results on block cipher networks from [KatzLindell2020] and original extensions:

1. **Substitution–permutation networks (SPNs)** ([KatzLindell2020], Section 7.2.1, Proposition 7.3):
   in `Cslib.Crypto.SPN`, key mixing (`spnKeyMixEquiv`), S-box substitution (`spnSubstituteEquiv`),
   sub-block and wire permutations (`spnPermuteEquiv`, `spnBitPermuteEquiv`), single rounds
   (`spnRoundEquiv`), and multi-round SPNs (`spnNetworkEquiv`) are permutations with an explicit
   round-by-round inverse (`spnRoundEquiv_symm`, `spnNetworkEquiv_symm_cons`,
   `bijective_spnNetworkEquiv`).
2. **Unbalanced Feistel networks** (original construction generalizing the balanced Feistel network
   of [KatzLindell2020], Section 7.2.2, Proposition 7.4): alternating rounds on `A × B`
   (`unbalancedFeistelLeftEquiv`, `unbalancedFeistelRightEquiv`), 2- and 4-round networks
   (`unbalancedFeistel2`, `unbalancedFeistel4`), agreement with balanced Feistel (`feistel4`), and
   lifting to `Equiv.Perm (BitString n)` for any block length `n` (`unbalancedFeistel4BitString`).
3. **Degenerate round-function periodicity** ([KatzLindell2020], Exercise 7.10(a),(b)): general
   periodicity reduction (`feistelNetwork_replicate_mod`), period-2 law for `0 : G → G`
   (`feistelNetwork_replicate_zero`), and period-3 law for `id : G → G` when `∀ a : G, -a = a`
   (`feistelNetwork_replicate_id`).
4. **Explicit 1- and 2-round CPA, 3-round repeated-key CPA, and 3-round CCA distinguishers**
   (attacks from [KatzLindell2020], Section 8.6 and Exercises 8.16–8.18; concrete bounds are
   original):
   - **Extension-cache falling-factorial bound** (`card_extPerms_ofFn_mul_descFactorial_le`,
     original): `k`-point `RandomPermutation.extPerms` fiber bound `(|α|)! / (|α|).descFactorial k`.
   - **1-round CPA** (`feistel1CPAAttack`, [KatzLindell2020], Section 8.6): accepts
     `feistelRoundEquiv f` w.p. `1`, `randomFunctionGame` w.p. `|G|⁻¹`, and `idealPermGame` w.p.
     `≤ |G|⁻¹` (original advantage bound `≥ 1 - |G|⁻¹`).
   - **2-round CPA** (`feistel2CPAAttack`, [KatzLindell2020], Exercise 8.16): accepts
     `feistelNetwork [f₁, f₂]` w.p. `1` and `idealPermGame` (`|G| ≥ 2`) w.p.
     `≤ |G| / (|G| ^ 2 - 1) ≤ 2 / 3` (original bound).
   - **3-round repeated-key (`[f, f, f]`) CPA** (`feistel3RepeatedKeyCPAAttack`, [KatzLindell2020],
     Exercise 8.18): accepts `feistel3 f f f` (`∀ a : G, -a = a`) w.p. `1` and `idealPermGame`
     (`|G| ≥ 2`) w.p. `≤ 2 / |G| ^ 2 ≤ 1 / 2` (original bound).
   - **Sharper permutation-fiber bound for 3-round CCA** (attack from [KatzLindell2020],
     Exercise 8.17; original bound `idealStrongGame_feistel3CCAAttack_true_le_inv_card_sub_one`,
     `le_advantage_feistel3CCAAttack_idealStrongGame_of_two_le_card`): refines the lazy-sampling
     bound on `feistel3CCAAttack l₀ l₁ r₀` to `(|G| + 1) / (|G| ^ 2 - 1) = (|G| - 1)⁻¹`.

## Implementation notes

In [KatzLindell2020], Section 8.6 and Exercises 8.16–8.18 state the distinguishers against Feistel
networks instantiated with keyed PRFs `F_{k_i}`. Proving acceptance with probability `1` for every
fixed tuple of round functions `f₁, f₂, f₃ : G → G` immediately implies acceptance with probability
`1` under any key distribution (such as `feistel3KeyedGame` in `LubyRackoff`).

## References

* [J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020],
  Sections 7.2.1–7.2.2, Propositions 7.3–7.4, Exercise 7.10, Section 8.6, and Exercises 8.16–8.18.
* [D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 4.5 and Exercise 4.15.
-/

@[expose] public section

/-! ### Substitution–permutation networks (SPNs) -/

namespace Cslib.Crypto.SPN

variable {boxes width : ℕ} {G : Type*}

/-- The state of a substitution–permutation network with `boxes` sub-blocks in `G`:
a tuple `Fin boxes → G`. -/
abbrev SPNState (boxes : ℕ) (G : Type*) := Fin boxes → G

/-- Parallel S-box substitution layer of an SPN: apply a family of bijective S-boxes
`sboxes : Fin boxes → Equiv.Perm G` independently to each sub-block (`i ↦ sboxes i (state i)`). -/
def spnSubstituteEquiv (sboxes : Fin boxes → Equiv.Perm G) : Equiv.Perm (SPNState boxes G) :=
  Equiv.piCongrRight sboxes

@[simp] theorem spnSubstituteEquiv_apply (sboxes : Fin boxes → Equiv.Perm G)
    (state : SPNState boxes G) (i : Fin boxes) :
    spnSubstituteEquiv sboxes state i = sboxes i (state i) := rfl

@[simp] theorem spnSubstituteEquiv_symm (sboxes : Fin boxes → Equiv.Perm G) :
    (spnSubstituteEquiv sboxes).symm = spnSubstituteEquiv (fun i => (sboxes i).symm) := rfl

/-- Sub-block permutation layer across `Fin boxes`: reindex sub-blocks along
`σ : Equiv.Perm (Fin boxes)`. -/
def spnPermuteEquiv (σ : Equiv.Perm (Fin boxes)) : Equiv.Perm (SPNState boxes G) where
  toFun state i := state (σ.symm i)
  invFun state i := state (σ i)
  left_inv state := by funext i; simp
  right_inv state := by funext i; simp

@[simp] theorem spnPermuteEquiv_apply (σ : Equiv.Perm (Fin boxes)) (state : SPNState boxes G)
    (i : Fin boxes) :
    spnPermuteEquiv σ state i = state (σ.symm i) := rfl

@[simp] theorem spnPermuteEquiv_symm (σ : Equiv.Perm (Fin boxes)) :
    (spnPermuteEquiv (G := G) σ).symm = spnPermuteEquiv σ.symm := rfl

/-- Wire-level bit-permutation (mixing) layer on `SPNState boxes (BitString width)`:
permute the `boxes × width` individual bit coordinates according to
`mix : Equiv.Perm (Fin boxes × Fin width)`. -/
def spnBitPermuteEquiv (mix : Equiv.Perm (Fin boxes × Fin width)) :
    Equiv.Perm (SPNState boxes (BitString width)) where
  toFun state i j := state (mix.symm (i, j)).1 (mix.symm (i, j)).2
  invFun state i j := state (mix (i, j)).1 (mix (i, j)).2
  left_inv state := by funext i j; simp
  right_inv state := by funext i j; simp

@[simp] theorem spnBitPermuteEquiv_apply (mix : Equiv.Perm (Fin boxes × Fin width))
    (state : SPNState boxes (BitString width)) (i : Fin boxes) (j : Fin width) :
    spnBitPermuteEquiv mix state i j = state (mix.symm (i, j)).1 (mix.symm (i, j)).2 := rfl

@[simp] theorem spnBitPermuteEquiv_symm (mix : Equiv.Perm (Fin boxes × Fin width)) :
    (spnBitPermuteEquiv mix).symm = spnBitPermuteEquiv mix.symm := rfl

variable [AddGroup G]

/-- Subkey mixing layer of an SPN: add `subkey : SPNState boxes G` coordinatewise on the right
(`state ↦ state + subkey`), with inverse `state ↦ state - subkey`. -/
def spnKeyMixEquiv (subkey : SPNState boxes G) : Equiv.Perm (SPNState boxes G) where
  toFun state := state + subkey
  invFun state := state - subkey
  left_inv state := add_sub_cancel_right state subkey
  right_inv state := sub_add_cancel state subkey

@[simp] theorem spnKeyMixEquiv_apply (subkey state : SPNState boxes G) :
    spnKeyMixEquiv subkey state = state + subkey := rfl

@[simp] theorem spnKeyMixEquiv_symm_apply (subkey state : SPNState boxes G) :
    (spnKeyMixEquiv subkey).symm state = state - subkey := rfl

/-- A single round of a substitution–permutation network ([KatzLindell2020], Section 7.2.1):
mix in `subkey`, apply parallel S-boxes `sboxes`, and apply `mixLayer`. -/
def spnRoundEquiv (sboxes : Fin boxes → Equiv.Perm G)
    (mixLayer : Equiv.Perm (SPNState boxes G)) (subkey : SPNState boxes G) :
    Equiv.Perm (SPNState boxes G) :=
  (spnKeyMixEquiv subkey).trans ((spnSubstituteEquiv sboxes).trans mixLayer)

@[simp] theorem spnRoundEquiv_apply (sboxes : Fin boxes → Equiv.Perm G)
    (mixLayer : Equiv.Perm (SPNState boxes G)) (subkey state : SPNState boxes G) :
    spnRoundEquiv sboxes mixLayer subkey state =
      mixLayer (spnSubstituteEquiv sboxes (state + subkey)) := rfl

/-- Explicit inverse of a single SPN round: invert `mixLayer`, apply inverse S-boxes
`(sboxes i).symm`, and subtract `subkey`. -/
theorem spnRoundEquiv_symm (sboxes : Fin boxes → Equiv.Perm G)
    (mixLayer : Equiv.Perm (SPNState boxes G)) (subkey : SPNState boxes G) :
    (spnRoundEquiv sboxes mixLayer subkey).symm =
      mixLayer.symm.trans
        ((spnSubstituteEquiv (fun i => (sboxes i).symm)).trans (spnKeyMixEquiv subkey).symm) :=
  rfl

@[simp] theorem spnRoundEquiv_symm_apply (sboxes : Fin boxes → Equiv.Perm G)
    (mixLayer : Equiv.Perm (SPNState boxes G)) (subkey state : SPNState boxes G) :
    (spnRoundEquiv sboxes mixLayer subkey).symm state =
      spnSubstituteEquiv (fun i => (sboxes i).symm) (mixLayer.symm state) - subkey := rfl

/-- Multi-round substitution–permutation network without final post-whitening:
fold `spnRoundEquiv sboxes mixLayer k` left-to-right across `roundKeys`. -/
def spnRoundsEquiv (sboxes : Fin boxes → Equiv.Perm G)
    (mixLayer : Equiv.Perm (SPNState boxes G)) (roundKeys : List (SPNState boxes G)) :
    Equiv.Perm (SPNState boxes G) :=
  roundKeys.foldl (fun acc k => acc.trans (spnRoundEquiv sboxes mixLayer k)) (Equiv.refl _)

@[simp] theorem spnRoundsEquiv_nil (sboxes : Fin boxes → Equiv.Perm G)
    (mixLayer : Equiv.Perm (SPNState boxes G)) :
    spnRoundsEquiv sboxes mixLayer [] = Equiv.refl (SPNState boxes G) := rfl

@[simp] theorem spnRoundsEquiv_cons (sboxes : Fin boxes → Equiv.Perm G)
    (mixLayer : Equiv.Perm (SPNState boxes G)) (k : SPNState boxes G)
    (ks : List (SPNState boxes G)) :
    spnRoundsEquiv sboxes mixLayer (k :: ks) =
      (spnRoundEquiv sboxes mixLayer k).trans (spnRoundsEquiv sboxes mixLayer ks) := by
  have h (e : Equiv.Perm (SPNState boxes G)) (l : List (SPNState boxes G)) :
      l.foldl (fun acc k => acc.trans (spnRoundEquiv sboxes mixLayer k)) e =
        e.trans (spnRoundsEquiv sboxes mixLayer l) := by
    induction l generalizing e with
    | nil => rfl
    | cons k' rest ih => rw [List.foldl_cons, spnRoundsEquiv, List.foldl_cons, ih, ih]; rfl
  exact h (spnRoundEquiv sboxes mixLayer k) ks

@[simp] theorem spnRoundsEquiv_append (sboxes : Fin boxes → Equiv.Perm G)
    (mixLayer : Equiv.Perm (SPNState boxes G)) (ks₁ ks₂ : List (SPNState boxes G)) :
    spnRoundsEquiv sboxes mixLayer (ks₁ ++ ks₂) =
      (spnRoundsEquiv sboxes mixLayer ks₁).trans (spnRoundsEquiv sboxes mixLayer ks₂) := by
  induction ks₁ with
  | nil => rfl
  | cons k ks₁ ih => simp only [List.cons_append, spnRoundsEquiv_cons, ih]; rfl

/-- Full substitution–permutation network ([KatzLindell2020], Section 7.2.1, Proposition 7.3):
execute `spnRoundsEquiv sboxes mixLayer roundKeys` followed by a final post-whitening key-mixing
step `spnKeyMixEquiv finalKey`. -/
def spnNetworkEquiv (sboxes : Fin boxes → Equiv.Perm G)
    (mixLayer : Equiv.Perm (SPNState boxes G)) (roundKeys : List (SPNState boxes G))
    (finalKey : SPNState boxes G) : Equiv.Perm (SPNState boxes G) :=
  (spnRoundsEquiv sboxes mixLayer roundKeys).trans (spnKeyMixEquiv finalKey)

@[simp] theorem spnNetworkEquiv_apply (sboxes : Fin boxes → Equiv.Perm G)
    (mixLayer : Equiv.Perm (SPNState boxes G)) (roundKeys : List (SPNState boxes G))
    (finalKey state : SPNState boxes G) :
    spnNetworkEquiv sboxes mixLayer roundKeys finalKey state =
      spnRoundsEquiv sboxes mixLayer roundKeys state + finalKey := rfl

@[simp] theorem spnNetworkEquiv_symm_nil (sboxes : Fin boxes → Equiv.Perm G)
    (mixLayer : Equiv.Perm (SPNState boxes G)) (finalKey : SPNState boxes G) :
    (spnNetworkEquiv sboxes mixLayer [] finalKey).symm = (spnKeyMixEquiv finalKey).symm := rfl

/-- Decrypting a non-empty SPN (`k :: ks`) undoes the remaining network `(ks, finalKey)` first and
then applies the single-round inverse `(spnRoundEquiv sboxes mixLayer k).symm`. -/
theorem spnNetworkEquiv_symm_cons (sboxes : Fin boxes → Equiv.Perm G)
    (mixLayer : Equiv.Perm (SPNState boxes G)) (k : SPNState boxes G)
    (ks : List (SPNState boxes G)) (finalKey : SPNState boxes G) :
    (spnNetworkEquiv sboxes mixLayer (k :: ks) finalKey).symm =
      (spnNetworkEquiv sboxes mixLayer ks finalKey).symm.trans
        (spnRoundEquiv sboxes mixLayer k).symm := by
  ext state; simp [spnNetworkEquiv]

/-- **Proposition 7.3 of [KatzLindell2020]**: for any bijective S-boxes `sboxes`, any bijective
mixing layer `mixLayer`, and any subkey schedule `(roundKeys, finalKey)`, the resulting
substitution–permutation network `spnNetworkEquiv sboxes mixLayer roundKeys finalKey` is a bijection
on `SPNState boxes G`. -/
theorem bijective_spnNetworkEquiv (sboxes : Fin boxes → Equiv.Perm G)
    (mixLayer : Equiv.Perm (SPNState boxes G)) (roundKeys : List (SPNState boxes G))
    (finalKey : SPNState boxes G) :
    Function.Bijective (spnNetworkEquiv sboxes mixLayer roundKeys finalKey) :=
  (spnNetworkEquiv sboxes mixLayer roundKeys finalKey).bijective

end Cslib.Crypto.SPN

namespace Cslib.Crypto.LubyRackoff

open Cslib.Probability
open scoped ENNReal NNReal BigOperators

/-! ### Unbalanced Feistel networks and arbitrary block-length splitting -/

section UnbalancedFeistel

variable {A B G : Type*}

/-- Left-updating unbalanced Feistel round on `A × B` (original):
`(a, b) ↦ (a + f b, b)` for `f : B → A`. -/
def unbalancedFeistelLeft [AddGroup A] (f : B → A) (p : A × B) : A × B :=
  (p.1 + f p.2, p.2)

/-- Explicit inverse of a left-updating unbalanced Feistel round: `(a, b) ↦ (a - f b, b)`. -/
def unbalancedFeistelLeftInv [AddGroup A] (f : B → A) (p : A × B) : A × B :=
  (p.1 - f p.2, p.2)

/-- Left-updating unbalanced Feistel round bundled as a permutation `Equiv.Perm (A × B)`. -/
def unbalancedFeistelLeftEquiv [AddGroup A] (f : B → A) : Equiv.Perm (A × B) where
  toFun := unbalancedFeistelLeft f
  invFun := unbalancedFeistelLeftInv f
  left_inv := fun ⟨a, b⟩ => by simp [unbalancedFeistelLeft, unbalancedFeistelLeftInv]
  right_inv := fun ⟨a, b⟩ => by simp [unbalancedFeistelLeft, unbalancedFeistelLeftInv]

@[simp] theorem unbalancedFeistelLeftEquiv_apply [AddGroup A] (f : B → A) (p : A × B) :
    unbalancedFeistelLeftEquiv f p = (p.1 + f p.2, p.2) := rfl

@[simp] theorem unbalancedFeistelLeftEquiv_symm_apply [AddGroup A] (f : B → A) (p : A × B) :
    (unbalancedFeistelLeftEquiv f).symm p = (p.1 - f p.2, p.2) := rfl

/-- Right-updating unbalanced Feistel round on `A × B` (original):
`(a, b) ↦ (a, b + g a)` for `g : A → B`. -/
def unbalancedFeistelRight [AddGroup B] (g : A → B) (p : A × B) : A × B :=
  (p.1, p.2 + g p.1)

/-- Explicit inverse of a right-updating unbalanced Feistel round: `(a, b) ↦ (a, b - g a)`. -/
def unbalancedFeistelRightInv [AddGroup B] (g : A → B) (p : A × B) : A × B :=
  (p.1, p.2 - g p.1)

/-- Right-updating unbalanced Feistel round bundled as a permutation `Equiv.Perm (A × B)`. -/
def unbalancedFeistelRightEquiv [AddGroup B] (g : A → B) : Equiv.Perm (A × B) where
  toFun := unbalancedFeistelRight g
  invFun := unbalancedFeistelRightInv g
  left_inv := fun ⟨a, b⟩ => by simp [unbalancedFeistelRight, unbalancedFeistelRightInv]
  right_inv := fun ⟨a, b⟩ => by simp [unbalancedFeistelRight, unbalancedFeistelRightInv]

@[simp] theorem unbalancedFeistelRightEquiv_apply [AddGroup B] (g : A → B) (p : A × B) :
    unbalancedFeistelRightEquiv g p = (p.1, p.2 + g p.1) := rfl

@[simp] theorem unbalancedFeistelRightEquiv_symm_apply [AddGroup B] (g : A → B) (p : A × B) :
    (unbalancedFeistelRightEquiv g).symm p = (p.1, p.2 - g p.1) := rfl

/-- Swapping the two halves (`Equiv.prodComm`) conjugates a left-updating unbalanced Feistel round
into a right-updating unbalanced Feistel round. -/
theorem prodComm_trans_unbalancedFeistelLeftEquiv_trans_prodComm [AddGroup A] (f : B → A) :
    (Equiv.prodComm B A).trans
      ((unbalancedFeistelLeftEquiv f).trans (Equiv.prodComm A B)) =
      unbalancedFeistelRightEquiv f := by
  ext ⟨b, a⟩ <;> rfl

/-- A balanced Feistel round `feistelRoundEquiv f` ([KatzLindell2020], Section 7.2.2,
Proposition 7.4) is a left-updating unbalanced round followed by swapping halves
`Equiv.prodComm G G`. -/
theorem feistelRoundEquiv_eq_unbalancedFeistelLeftEquiv_trans_prodComm [AddGroup G] (f : G → G) :
    feistelRoundEquiv f = (unbalancedFeistelLeftEquiv f).trans (Equiv.prodComm G G) := by
  ext ⟨l, r⟩ <;> rfl

/-- Two-round alternating unbalanced Feistel network on `A × B` (original): update `A` using
`f₁ : B → A`, then update `B` using `f₂ : A → B`. -/
def unbalancedFeistel2 [AddGroup A] [AddGroup B] (f₁ : B → A) (f₂ : A → B) :
    Equiv.Perm (A × B) :=
  (unbalancedFeistelLeftEquiv f₁).trans (unbalancedFeistelRightEquiv f₂)

@[simp] theorem unbalancedFeistel2_apply [AddGroup A] [AddGroup B]
    (f₁ : B → A) (f₂ : A → B) (p : A × B) :
    unbalancedFeistel2 f₁ f₂ p = (p.1 + f₁ p.2, p.2 + f₂ (p.1 + f₁ p.2)) := rfl

@[simp] theorem unbalancedFeistel2_symm_apply [AddGroup A] [AddGroup B] (f₁ : B → A) (f₂ : A → B)
    (p : A × B) :
    (unbalancedFeistel2 f₁ f₂).symm p = (p.1 - f₁ (p.2 - f₂ p.1), p.2 - f₂ p.1) := rfl

/-- When `A = B = G`, the 2-round alternating unbalanced Feistel network `unbalancedFeistel2 f₁ f₂`
coincides with the 2-round balanced Feistel network `feistelNetwork [f₁, f₂]`. -/
theorem unbalancedFeistel2_eq_feistelNetwork [AddGroup G] (f₁ f₂ : G → G) :
    unbalancedFeistel2 f₁ f₂ = feistelNetwork [f₁, f₂] := rfl

/-- Four-round alternating unbalanced Feistel network on `A × B` (original): alternate `f₁ : B → A`,
`f₂ : A → B`, `f₃ : B → A`, and `f₄ : A → B`. -/
def unbalancedFeistel4 [AddGroup A] [AddGroup B]
    (f₁ : B → A) (f₂ : A → B) (f₃ : B → A) (f₄ : A → B) :
    Equiv.Perm (A × B) :=
  (unbalancedFeistel2 f₁ f₂).trans (unbalancedFeistel2 f₃ f₄)

theorem unbalancedFeistel4_apply [AddGroup A] [AddGroup B]
    (f₁ : B → A) (f₂ : A → B) (f₃ : B → A) (f₄ : A → B) (p : A × B) :
    unbalancedFeistel4 f₁ f₂ f₃ f₄ p =
      let u := p.1 + f₁ p.2
      let v := p.2 + f₂ u
      let w := u + f₃ v
      (w, v + f₄ w) := rfl

theorem unbalancedFeistel4_symm_apply [AddGroup A] [AddGroup B]
    (f₁ : B → A) (f₂ : A → B) (f₃ : B → A) (f₄ : A → B) (wz : A × B) :
    (unbalancedFeistel4 f₁ f₂ f₃ f₄).symm wz =
      let v := wz.2 - f₄ wz.1
      let u := wz.1 - f₃ v
      (u - f₁ (v - f₂ u), v - f₂ u) := rfl

/-- When `A = B = G`, the 4-round alternating unbalanced Feistel network
`unbalancedFeistel4 f₁ f₂ f₃ f₄` coincides with the 4-round balanced Feistel network
`feistel4 f₁ f₂ f₃ f₄`. -/
theorem unbalancedFeistel4_eq_feistel4 [AddGroup G] (f₁ f₂ f₃ f₄ : G → G) :
    unbalancedFeistel4 f₁ f₂ f₃ f₄ = feistel4 f₁ f₂ f₃ f₄ := rfl

/-- Split an arbitrary `n`-bit string (`BitString n`) into its first `n / 2` bits and remaining
`n - n / 2` bits, supporting both even and odd block lengths `n` (original). -/
def bitStringHalfSplitEquiv (n : ℕ) :
    BitString n ≃ BitString (n / 2) × BitString (n - n / 2) :=
  (Equiv.arrowCongr (finCongr (Nat.add_sub_of_le (Nat.div_le_self n 2)).symm)
    (Equiv.refl Bool)).trans (Fin.appendEquiv (n / 2) (n - n / 2)).symm

/-- Four-round unbalanced Feistel permutation on `BitString n` for any (even or odd) block size `n`,
constructed from half-block round functions `f₁, f₃ : BitString (n - n / 2) → BitString (n / 2)`
and `f₂, f₄ : BitString (n / 2) → BitString (n - n / 2)` (original). -/
def unbalancedFeistel4BitString (n : ℕ)
    (f₁ : BitString (n - n / 2) → BitString (n / 2))
    (f₂ : BitString (n / 2) → BitString (n - n / 2))
    (f₃ : BitString (n - n / 2) → BitString (n / 2))
    (f₄ : BitString (n / 2) → BitString (n - n / 2)) :
    Equiv.Perm (BitString n) :=
  (bitStringHalfSplitEquiv n).trans
    ((unbalancedFeistel4 f₁ f₂ f₃ f₄).trans (bitStringHalfSplitEquiv n).symm)

end UnbalancedFeistel

/-! ### Degenerate round-function periodicity in Feistel networks -/

section Periodicity

variable {G : Type*} [AddGroup G]

/-- Replicating `a + b` copies of a single round function `f` composes the `a`-round and `b`-round
Feistel networks. -/
theorem feistelNetwork_replicate_add (a b : ℕ) (f : G → G) :
    feistelNetwork (List.replicate (a + b) f) =
      (feistelNetwork (List.replicate a f)).trans (feistelNetwork (List.replicate b f)) := by
  rw [List.replicate_add, feistelNetwork_append]

/-- If `k` identical Feistel rounds of `f` compose to the identity permutation on `G × G`, then
for every `r : ℕ`, `r` rounds of `f` equal `r % k` rounds of `f`. -/
theorem feistelNetwork_replicate_mod {k : ℕ} {f : G → G}
    (hperiod : feistelNetwork (List.replicate k f) = Equiv.refl (G × G)) (r : ℕ) :
    feistelNetwork (List.replicate r f) = feistelNetwork (List.replicate (r % k) f) := by
  have hmul (m : ℕ) : feistelNetwork (List.replicate (k * m) f) = Equiv.refl (G × G) := by
    induction m with
    | zero => rfl
    | succ m ih => rw [Nat.mul_succ, feistelNetwork_replicate_add, ih, hperiod]; rfl
  conv_lhs => rw [← Nat.div_add_mod r k]
  rw [feistelNetwork_replicate_add, hmul (r / k)]
  rfl

/-- A single Feistel round with the identically zero function `0 : G → G` is
`Equiv.prodComm G G`. -/
@[simp] theorem feistelRoundEquiv_zero :
    feistelRoundEquiv (0 : G → G) = Equiv.prodComm G G := by ext ⟨l, r⟩ <;> simp

/-- Two Feistel rounds with the zero round function `0 : G → G` compose to the identity. -/
@[simp] theorem feistelNetwork_replicate_two_zero :
    feistelNetwork (List.replicate 2 (0 : G → G)) = Equiv.refl (G × G) := by
  ext ⟨l, r⟩ <;> simp [List.replicate]

/-- **Period-2 law for zero Feistel rounds** ([KatzLindell2020], Exercise 7.10(a)):
running `r` Feistel rounds with the identically zero round function `0 : G → G` acts as the
identity when `r` is even and swaps the two halves `(l, r) ↦ (r, l)` when `r` is odd. -/
theorem feistelNetwork_replicate_zero (r : ℕ) (p : G × G) :
    feistelNetwork (List.replicate r (0 : G → G)) p =
      if r % 2 = 0 then p else p.swap := by
  rw [feistelNetwork_replicate_mod feistelNetwork_replicate_two_zero r]
  rcases Nat.mod_two_eq_zero_or_one r with h0 | h1
  · rw [h0]; rfl
  · rw [h1]; rcases p with ⟨l, r'⟩; simp [List.replicate]

private theorem add_self_cancel_left_of_neg_eq_self (hneg : ∀ a : G, -a = a) (a b : G) :
    b + (a + b) = a := by
  have h2 (x : G) : x + x = 0 := by simpa [hneg x] using neg_add_cancel x
  calc b + (a + b) = -(b + (a + b)) := (hneg _).symm
    _ = -(a + b) + -b := neg_add_rev b (a + b)
    _ = (a + b) + b := by rw [hneg, hneg]
    _ = a := by rw [add_assoc, h2 b, add_zero]

/-- Over any group of exponent two (`∀ a : G, -a = a`), three Feistel rounds with the identity
round function `id : G → G` compose to the identity permutation on `G × G`
([KatzLindell2020], Exercise 7.10(b)). -/
theorem feistelNetwork_replicate_three_id (hneg : ∀ a : G, -a = a) :
    feistelNetwork (List.replicate 3 (id : G → G)) = Equiv.refl (G × G) := by
  ext ⟨l, r⟩ <;>
    simp [List.replicate, feistelRound, add_self_cancel_left_of_neg_eq_self hneg, add_assoc]

/-- **Period-3 law for identity Feistel rounds** ([KatzLindell2020], Exercise 7.10(b)):
over any group of exponent two (`∀ a : G, -a = a`, such as `BitString n`), running `r` Feistel
rounds with the identity round function `id : G → G` has period `3`:
- `r % 3 = 0`: `(l, r') ↦ (l, r')`,
- `r % 3 = 1`: `(l, r') ↦ (r', l + r')`,
- `r % 3 = 2`: `(l, r') ↦ (l + r', l)`. -/
theorem feistelNetwork_replicate_id (hneg : ∀ a : G, -a = a) (r : ℕ) (p : G × G) :
    feistelNetwork (List.replicate r (id : G → G)) p =
      if r % 3 = 0 then p
      else if r % 3 = 1 then (p.2, p.1 + p.2)
      else (p.1 + p.2, p.1) := by
  rw [feistelNetwork_replicate_mod (feistelNetwork_replicate_three_id hneg) r]
  have hmod : r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2 := by omega
  rcases p with ⟨l, r'⟩
  rcases hmod with h0 | h1 | h2'
  · rw [h0]; rfl
  · rw [h1]; rfl
  · rw [h2']; simp [List.replicate, feistelRound, add_self_cancel_left_of_neg_eq_self hneg]

end Periodicity

/-! ### Extension-cache fiber bounds and explicit Feistel distinguishers -/

section Distinguishers

variable {α : Type} [Fintype α] [DecidableEq α]

private theorem extPerms_ofFn_eq {k : ℕ} (xs ys : Fin k → α) :
    RandomPermutation.extPerms (List.ofFn fun i => (xs i, ys i)) =
      Finset.univ.filter fun π : Equiv.Perm α => ∀ i, π (xs i) = ys i := by
  ext π
  simp [RandomPermutation.extPerms, RandomPermutation.AgreesWith]

private theorem card_extPerms_ofFn_eq {k : ℕ} (xs : Fin k → α) (e e' : Fin k ↪ α) :
    (RandomPermutation.extPerms (List.ofFn fun i => (xs i, e i))).card =
      (RandomPermutation.extPerms (List.ofFn fun i => (xs i, e' i))).card := by
  rw [extPerms_ofFn_eq, extPerms_ofFn_eq]
  let E : {x // x ∈ Set.range e} ≃ {x // x ∈ Set.range e'} :=
    (Equiv.ofInjective e e.injective).symm.trans (Equiv.ofInjective e' e'.injective)
  let σ : Equiv.Perm α := E.extendSubtype
  have hσ (i : Fin k) : σ (e i) = e' i := by
    dsimp [σ]
    rw [Equiv.extendSubtype_apply_of_mem E (e i) ⟨i, rfl⟩]
    have hi : (Equiv.ofInjective e e.injective).symm ⟨e i, ⟨i, rfl⟩⟩ = i :=
      e.injective (Equiv.apply_ofInjective_symm e.injective ⟨e i, ⟨i, rfl⟩⟩)
    simp only [E, Equiv.trans_apply, hi, Equiv.ofInjective_apply]
  refine Finset.card_bij (fun π _ => σ * π) ?_ ?_ ?_
  · intro π hπ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
    intro i; simp [hπ i, hσ]
  · intro π _ ρ _ h; simpa using h
  · intro ρ hρ
    refine ⟨σ⁻¹ * ρ, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ ⊢
    intro i; rw [Equiv.Perm.mul_apply, hρ i, Equiv.Perm.inv_eq_iff_eq, hσ]

private theorem sum_card_extPerms_ofFn {k : ℕ} (xs : Fin k ↪ α) :
    ∑ e : Fin k ↪ α,
      (RandomPermutation.extPerms (List.ofFn fun i => (xs i, e i))).card =
        (Fintype.card α).factorial := by
  rw [← Fintype.card_perm, ← Finset.card_univ,
    Finset.card_eq_sum_card_fiberwise (f := fun π : Equiv.Perm α => xs.trans π.toEmbedding)
      (t := Finset.univ) (by simp)]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [extPerms_ofFn_eq]
  congr 1; ext π
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => by ext i; simp [h i], fun h i => by rw [← h]; simp⟩

/-- **Falling-factorial upper bound on `k`-point `RandomPermutation.extPerms` fibers** (original):
for any `k` distinct domain points `xs : Fin k ↪ α` and any target values `ys : Fin k → α`,
`#(RandomPermutation.extPerms (List.ofFn fun i => (xs i, ys i))) * (Fintype.card α).descFactorial k
  ≤ (Fintype.card α).factorial`. -/
theorem card_extPerms_ofFn_mul_descFactorial_le {k : ℕ} (xs : Fin k ↪ α) (ys : Fin k → α) :
    (RandomPermutation.extPerms (List.ofFn fun i => (xs i, ys i))).card *
      (Fintype.card α).descFactorial k ≤ (Fintype.card α).factorial := by
  by_cases hys : Function.Injective ys
  · have hall : ∀ e : Fin k ↪ α,
        (RandomPermutation.extPerms (List.ofFn fun i => (xs i, e i))).card =
          (RandomPermutation.extPerms (List.ofFn fun i => (xs i, ys i))).card :=
      fun e => card_extPerms_ofFn_eq xs e ⟨ys, hys⟩
    rw [← sum_card_extPerms_ofFn xs]
    simp only [hall, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Fintype.card_embedding_eq, Fintype.card_fin]
    rw [mul_comm]
  · have hempty : RandomPermutation.extPerms (List.ofFn fun i => (xs i, ys i)) = ∅ := by
      rw [extPerms_ofFn_eq]
      ext π
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact fun h => hys fun i j hij => xs.injective (π.injective (by rw [h i, h j, hij]))
    simp [hempty]

private theorem card_filter_perm_one_mul_le (x a : α) :
    ((Finset.univ.filter fun π : Equiv.Perm α => π x = a).card : ℝ) * (Fintype.card α : ℝ) ≤
      (Fintype.card α).factorial := by
  let xs : Fin 1 ↪ α := ⟨![x], fun i j _ => Subsingleton.elim i j⟩
  have h := card_extPerms_ofFn_mul_descFactorial_le xs ![a]
  have he : RandomPermutation.extPerms (List.ofFn fun i : Fin 1 => (xs i, ![a] i)) =
      Finset.univ.filter fun π : Equiv.Perm α => π x = a := by
    rw [extPerms_ofFn_eq]; ext π; simp [xs]; rfl
  rw [he, Nat.descFactorial_one] at h
  exact_mod_cast h

private theorem card_filter_perm_two_mul_le {x y : α} (hxy : x ≠ y) (a b : α) :
    ((Finset.univ.filter fun π : Equiv.Perm α => π x = a ∧ π y = b).card : ℝ) *
      ((Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1)) ≤ (Fintype.card α).factorial := by
  have hinj : Function.Injective ![x, y] := by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  let xs : Fin 2 ↪ α := ⟨![x, y], hinj⟩
  have h := card_extPerms_ofFn_mul_descFactorial_le xs ![a, b]
  have he : RandomPermutation.extPerms (List.ofFn fun i : Fin 2 => (xs i, ![a, b] i)) =
      Finset.univ.filter fun π : Equiv.Perm α => π x = a ∧ π y = b := by
    rw [extPerms_ofFn_eq]; ext π; simp [xs, Fin.forall_fin_two]
  have h1 : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨x⟩
  rw [he, Nat.descFactorial_succ, Nat.descFactorial_one] at h
  have hsub : ((Fintype.card α - 1 : ℕ) : ℝ) = (Fintype.card α : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [← hsub]
  have hcast := (Nat.cast_le (α := ℝ)).mpr h
  push_cast at hcast ⊢
  linarith

private theorem card_filter_perm_three_mul_le {x y z : α}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (a b c : α) (hM : 2 ≤ Fintype.card α) :
    ((Finset.univ.filter fun π : Equiv.Perm α => π x = a ∧ π y = b ∧ π z = c).card : ℝ) *
      ((Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1) * ((Fintype.card α : ℝ) - 2)) ≤
        (Fintype.card α).factorial := by
  have hinj : Function.Injective ![x, y, z] := by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  let xs : Fin 3 ↪ α := ⟨![x, y, z], hinj⟩
  have h := card_extPerms_ofFn_mul_descFactorial_le xs ![a, b, c]
  have he : RandomPermutation.extPerms (List.ofFn fun i : Fin 3 => (xs i, ![a, b, c] i)) =
      Finset.univ.filter fun π : Equiv.Perm α => π x = a ∧ π y = b ∧ π z = c := by
    rw [extPerms_ofFn_eq]; ext π; simp [xs, Fin.forall_fin_succ]
  rw [he, Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_one] at h
  have e1 : ((Fintype.card α - 1 : ℕ) : ℝ) = (Fintype.card α : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have e2 : ((Fintype.card α - 2 : ℕ) : ℝ) = (Fintype.card α : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [← e1, ← e2]
  have hcast := (Nat.cast_le (α := ℝ)).mpr h
  push_cast at hcast ⊢
  linarith

private theorem card_le_of_biUnion_cover {β γ : Type*} [DecidableEq γ]
    (E : Finset γ) (S : Finset β) (F : β → Finset γ) (c : ℝ)
    (hE : E ⊆ S.biUnion F) (hF : ∀ i ∈ S, ((F i).card : ℝ) ≤ c) :
    (E.card : ℝ) ≤ S.card * c := by
  have h1 : (E.card : ℝ) ≤ (S.biUnion F).card := by exact_mod_cast Finset.card_le_card hE
  have h2 : ((S.biUnion F).card : ℝ) ≤ ∑ i ∈ S, ((F i).card : ℝ) := by
    exact_mod_cast Finset.card_biUnion_le
  have h3 : ∑ i ∈ S, ((F i).card : ℝ) ≤ ∑ _i ∈ S, c := Finset.sum_le_sum hF
  simp only [Finset.sum_const, nsmul_eq_mul] at h3
  linarith

private theorem card_erase_erase {x y : α} (hxy : x ≠ y) :
    (((Finset.univ.erase x).erase y).card : ℝ) = (Fintype.card α : ℝ) - 2 := by
  have hy : y ∈ Finset.univ.erase x := by simp [Ne.symm hxy]
  rw [Finset.card_erase_of_mem hy, Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ]
  have h2 : 2 ≤ Fintype.card α := by
    have hle := Finset.card_le_univ ({x, y} : Finset α)
    rwa [Finset.card_pair hxy] at hle
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast; ring

private theorem uniformOfFintype_perm_filter_toReal (P : Equiv.Perm α → Bool) :
    (((PMF.uniformOfFintype (Equiv.Perm α)).bind fun π => PMF.pure (P π)) true).toReal =
      ((Finset.univ.filter fun π => P π = true).card : ℝ) / (Fintype.card α).factorial := by
  have : DecidablePred (· ∈ P ⁻¹' ({true} : Set Bool)) :=
    fun π => inferInstanceAs (Decidable (P π = true))
  change (((PMF.uniformOfFintype (Equiv.Perm α)).map P) true).toReal = _
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
    Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_toReal, Fintype.card_perm]
  simp only [Set.mem_preimage, Set.mem_singleton_iff]

private theorem le_advantage_of_pure_true_of_toReal_le {d₁ d₂ : PMF Bool} {B : ℝ}
    (hd₁ : d₁ = PMF.pure true) (hd₂ : (d₂ true).toReal ≤ B) (hB : B ≤ 1) :
    1 - B ≤ (Game.advantage d₁ d₂ : ℝ) := by
  rw [hd₁, Game.coe_advantage]
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal,
    PMF.pure_apply_self, ENNReal.toReal_one]
  rw [abs_of_nonneg (by linarith)]
  linarith

variable {G : Type} [AddGroup G] [Fintype G] [DecidableEq G]

/-! #### 1-round Feistel CPA distinguisher -/

/-- **The 1-query chosen-plaintext distinguisher against 1-round Feistel** ([KatzLindell2020],
Section 8.6): query `(l₀, r₀)` to obtain `(v, w)` and accept iff `v = r₀`. -/
def feistel1CPAAttack (l₀ r₀ : G) :
    OracleComp (fun _ : G × G => G × G) Bool := do
  let vw ← OracleComp.query (spec := fun _ : G × G => G × G) (l₀, r₀)
  return decide (vw.1 = r₀)

omit [AddGroup G] [Fintype G] in
/-- `feistel1CPAAttack` makes at most 1 oracle query. -/
theorem isQueryBounded_feistel1CPAAttack (l₀ r₀ : G) :
    OracleComp.IsQueryBounded (feistel1CPAAttack l₀ r₀) 1 := by
  refine ((OracleComp.IsCostBounded.query (l₀, r₀)).bind fun vw =>
    OracleComp.IsCostBounded.pure _ 0).mono (by omega)

omit [Fintype G] in
/-- **Every 1-round Feistel network `feistelRoundEquiv f` is accepted with probability `1` by
`feistel1CPAAttack l₀ r₀`** ([KatzLindell2020], Section 8.6), for any round function
`f : G → G`. -/
theorem eval_feistelRoundEquiv_feistel1CPAAttack (f : G → G) (l₀ r₀ : G) :
    OracleComp.interpret (fun p => PMF.pure (feistelRoundEquiv f p))
      (feistel1CPAAttack l₀ r₀) = PMF.pure true := by
  simp [feistel1CPAAttack]

omit [AddGroup G] in
/-- Against `randomFunctionGame`, `feistel1CPAAttack l₀ r₀` accepts with probability `|G|⁻¹`
(original bound). -/
theorem randomFunctionGame_feistel1CPAAttack_true [Nonempty G] (l₀ r₀ : G) :
    randomFunctionGame (feistel1CPAAttack l₀ r₀) true = (Fintype.card G : ℝ≥0∞)⁻¹ := by
  have heval :
      (PMF.uniformOfFintype (G × G → G × G)).map (fun table => table (l₀, r₀)) =
        PMF.uniformOfFintype (G × G) := by
    rw [← Cslib.Probability.PMF.pi_uniformOfFintype, Cslib.Probability.PMF.pi_map_eval]
  have hfst :
      (PMF.uniformOfFintype (G × G)).map Prod.fst = PMF.uniformOfFintype G :=
    Cslib.Probability.PMF.uniformOfFintype_prod_map_fst
  have hgame :
      randomFunctionGame (feistel1CPAAttack l₀ r₀) =
        (PMF.uniformOfFintype G).map (fun v => decide (v = r₀)) := by
    calc randomFunctionGame (feistel1CPAAttack l₀ r₀)
        = (((PMF.uniformOfFintype (G × G → G × G)).map (fun table => table (l₀, r₀))).map
            Prod.fst).map (fun v => decide (v = r₀)) := by
          simp [randomFunctionGame, feistel1CPAAttack, PMF.map_comp, Function.comp_def]; rfl
      _ = (PMF.uniformOfFintype G).map (fun v => decide (v = r₀)) := by rw [heval, hfst]
  rw [hgame, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  have hpre : (fun v : G => decide (v = r₀)) ⁻¹' {true} = {r₀} := by ext v; simp
  rw [hpre, PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply]

/-- `feistel1CPAAttack l₀ r₀` distinguishes any 1-round Feistel network `feistelRoundEquiv f` from
`randomFunctionGame` with exact advantage `1 - |G|⁻¹` (original bound). -/
theorem advantage_feistel1CPAAttack_randomFunctionGame [Nonempty G] (f : G → G) (l₀ r₀ : G) :
    (Game.advantage
      (OracleComp.interpret (fun p => PMF.pure (feistelRoundEquiv f p))
        (feistel1CPAAttack l₀ r₀))
      (randomFunctionGame (feistel1CPAAttack l₀ r₀)) : ℝ) =
      1 - (Fintype.card G : ℝ)⁻¹ := by
  rw [Game.coe_advantage]
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal,
    eval_feistelRoundEquiv_feistel1CPAAttack, randomFunctionGame_feistel1CPAAttack_true,
    PMF.pure_apply_self, ENNReal.toReal_one, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  exact abs_of_nonneg
    (sub_nonneg.mpr (inv_le_one_of_one_le₀ (by exact_mod_cast Fintype.card_pos)))

omit [AddGroup G] in
/-- Against `idealPermGame`, `feistel1CPAAttack l₀ r₀` accepts with probability at most `|G|⁻¹`
(original bound). -/
theorem idealPermGame_feistel1CPAAttack_true_le [Nonempty G] (l₀ r₀ : G) :
    (idealPermGame (feistel1CPAAttack l₀ r₀) true).toReal ≤ (Fintype.card G : ℝ)⁻¹ := by
  have hgame :
      idealPermGame (feistel1CPAAttack l₀ r₀) =
        (PMF.uniformOfFintype (Equiv.Perm (G × G))).bind fun π =>
          PMF.pure (decide ((π (l₀, r₀)).1 = r₀)) := by
    simp [idealPermGame, feistel1CPAAttack, PMF.monad_bind_eq_bind]
  rw [hgame, uniformOfFintype_perm_filter_toReal]
  set M := Fintype.card (G × G)
  set P : ℝ := (M.factorial : ℝ)
  have hP : 0 < P := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hN : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  have hMr : (M : ℝ) = (Fintype.card G : ℝ) * (Fintype.card G : ℝ) := by simp [M, Fintype.card_prod]
  have hMpos : (0 : ℝ) < M := by rw [hMr]; positivity
  have hcover :
      (Finset.univ.filter fun π : Equiv.Perm (G × G) => decide ((π (l₀, r₀)).1 = r₀) = true) ⊆
        (Finset.univ : Finset G).biUnion fun w =>
          Finset.univ.filter fun π : Equiv.Perm (G × G) => π (l₀, r₀) = (r₀, w) := by
    intro π hπ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hπ
    simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
    exact ⟨(π (l₀, r₀)).2, Prod.ext hπ rfl⟩
  have hE := card_le_of_biUnion_cover _ Finset.univ
    (fun w => Finset.univ.filter fun π : Equiv.Perm (G × G) => π (l₀, r₀) = (r₀, w))
    (P / M) hcover
    (fun w _ => by rw [le_div_iff₀ hMpos]; exact card_filter_perm_one_mul_le (l₀, r₀) (r₀, w))
  rw [Finset.card_univ] at hE
  rw [div_le_iff₀ hP]
  exact hE.trans_eq (by rw [hMr]; field_simp)

/-- `feistel1CPAAttack l₀ r₀` distinguishes any 1-round Feistel network `feistelRoundEquiv f` from
`idealPermGame` with advantage at least `1 - |G|⁻¹` (original bound). -/
theorem le_advantage_feistel1CPAAttack_idealPermGame [Nonempty G] (f : G → G) (l₀ r₀ : G) :
    1 - (Fintype.card G : ℝ)⁻¹ ≤
      (Game.advantage
        (OracleComp.interpret (fun p => PMF.pure (feistelRoundEquiv f p))
          (feistel1CPAAttack l₀ r₀))
        (idealPermGame (feistel1CPAAttack l₀ r₀)) : ℝ) :=
  le_advantage_of_pure_true_of_toReal_le
    (eval_feistelRoundEquiv_feistel1CPAAttack f l₀ r₀)
    (idealPermGame_feistel1CPAAttack_true_le l₀ r₀)
    (inv_le_one_of_one_le₀ (by exact_mod_cast Fintype.card_pos))

/-! #### 2-round Feistel CPA distinguisher -/

/-- **The 2-query chosen-plaintext distinguisher against 2-round Feistel** ([KatzLindell2020],
Exercise 8.16):
query `(l₀, r₀)` to obtain `(v₀, w₀)`, query `(l₁, r₀)` to obtain `(v₁, w₁)`, and accept iff
`v₀ - v₁ = l₀ - l₁`. -/
def feistel2CPAAttack (l₀ l₁ r₀ : G) :
    OracleComp (fun _ : G × G => G × G) Bool := do
  let vw₀ ← OracleComp.query (spec := fun _ : G × G => G × G) (l₀, r₀)
  let vw₁ ← OracleComp.query (spec := fun _ : G × G => G × G) (l₁, r₀)
  return decide (vw₀.1 - vw₁.1 = l₀ - l₁)

omit [Fintype G] in
/-- `feistel2CPAAttack` makes at most 2 oracle queries. -/
theorem isQueryBounded_feistel2CPAAttack (l₀ l₁ r₀ : G) :
    OracleComp.IsQueryBounded (feistel2CPAAttack l₀ l₁ r₀) 2 := by
  refine ((OracleComp.IsCostBounded.query (l₀, r₀)).bind fun vw₀ =>
    ((OracleComp.IsCostBounded.query (l₁, r₀)).bind fun vw₁ =>
      OracleComp.IsCostBounded.pure _ 0)).mono (by omega)

omit [Fintype G] [DecidableEq G] in
private theorem add_sub_add_right_cancel (a b c : G) : (a + c) - (b + c) = a - b := by
  rw [sub_eq_add_neg, neg_add_rev, ← add_assoc, add_assoc a c (-c), add_neg_cancel, add_zero,
    ← sub_eq_add_neg]

omit [Fintype G] in
/-- **Every 2-round Feistel network `feistelNetwork [f₁, f₂]` is accepted with probability `1` by
`feistel2CPAAttack l₀ l₁ r₀`** ([KatzLindell2020], Exercise 8.16), for any round functions
`f₁, f₂ : G → G` and any `l₀, l₁, r₀ : G`. -/
theorem eval_feistel2_feistel2CPAAttack (f₁ f₂ : G → G) (l₀ l₁ r₀ : G) :
    OracleComp.interpret (fun p => PMF.pure (feistelNetwork [f₁, f₂] p))
      (feistel2CPAAttack l₀ l₁ r₀) = PMF.pure true := by
  simp only [feistel2CPAAttack, feistelNetwork_cons, feistelNetwork_nil, Equiv.trans_apply,
    feistelRoundEquiv_apply, feistelRound, Equiv.refl_apply,
    OracleComp.interpret_bind, OracleComp.interpret_query, OracleComp.interpret_pure,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.pure_bind,
    add_sub_add_right_cancel, decide_true]

/-- Against `idealPermGame`, when `l₀ ≠ l₁` and `2 ≤ Fintype.card G`, `feistel2CPAAttack l₀ l₁ r₀`
accepts with probability at most `|G| / (|G| ^ 2 - 1)` (original bound). -/
theorem idealPermGame_feistel2CPAAttack_true_le [Nonempty G] {l₀ l₁ : G} (r₀ : G)
    (h01 : l₀ ≠ l₁) (hG : 2 ≤ Fintype.card G) :
    (idealPermGame (feistel2CPAAttack l₀ l₁ r₀) true).toReal ≤
      (Fintype.card G : ℝ) / ((Fintype.card G : ℝ) ^ 2 - 1) := by
  have hgame :
      idealPermGame (feistel2CPAAttack l₀ l₁ r₀) =
        (PMF.uniformOfFintype (Equiv.Perm (G × G))).bind fun π =>
          PMF.pure (decide ((π (l₀, r₀)).1 - (π (l₁, r₀)).1 = l₀ - l₁)) := by
    simp [idealPermGame, feistel2CPAAttack, PMF.monad_bind_eq_bind]
  rw [hgame, uniformOfFintype_perm_filter_toReal]
  have hxy : ((l₀, r₀) : G × G) ≠ (l₁, r₀) := fun h => h01 (congrArg Prod.fst h)
  set M := Fintype.card (G × G)
  set P : ℝ := (M.factorial : ℝ)
  have hP : 0 < P := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hN : (2 : ℝ) ≤ Fintype.card G := by exact_mod_cast hG
  have hMr : (M : ℝ) = (Fintype.card G : ℝ) ^ 2 := by simp [M, Fintype.card_prod, sq]
  have hM1 : (1 : ℝ) < M := by rw [hMr]; nlinarith
  have hcover :
      (Finset.univ.filter fun π : Equiv.Perm (G × G) =>
        decide ((π (l₀, r₀)).1 - (π (l₁, r₀)).1 = l₀ - l₁) = true) ⊆
      (Finset.univ : Finset ((G × G) × G)).biUnion fun aw =>
        Finset.univ.filter fun π : Equiv.Perm (G × G) =>
          π (l₀, r₀) = aw.1 ∧ π (l₁, r₀) = (-(l₀ - l₁) + aw.1.1, aw.2) := by
    intro π hπ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hπ
    simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
    have hv₁ : (π (l₁, r₀)).1 = -(l₀ - l₁) + (π (l₀, r₀)).1 := by
      rw [← hπ, neg_sub, sub_add_cancel]
    exact ⟨(π (l₀, r₀), (π (l₁, r₀)).2), rfl, Prod.ext hv₁ rfl⟩
  have hE := card_le_of_biUnion_cover _ Finset.univ
    (fun aw : (G × G) × G =>
      Finset.univ.filter fun π : Equiv.Perm (G × G) =>
        π (l₀, r₀) = aw.1 ∧ π (l₁, r₀) = (-(l₀ - l₁) + aw.1.1, aw.2))
    (P / (M * (M - 1))) hcover
    (fun aw _ => by
      rw [le_div_iff₀ (by nlinarith)]
      exact card_filter_perm_two_mul_le hxy aw.1 (-(l₀ - l₁) + aw.1.1, aw.2))
  simp only [Finset.card_univ, Fintype.card_prod] at hE
  push_cast at hE
  rw [div_le_iff₀ hP]
  refine hE.trans_eq ?_
  rw [hMr]
  have hsq_ne : (Fintype.card G : ℝ) ^ 2 ≠ 0 := by positivity
  have hsq1_ne : (Fintype.card G : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  field_simp

/-- When `l₀ ≠ l₁` and `2 ≤ Fintype.card G`, `feistel2CPAAttack l₀ l₁ r₀` distinguishes any
2-round Feistel network `feistelNetwork [f₁, f₂]` from `idealPermGame` with advantage at least
`1 - |G| / (|G| ^ 2 - 1)` (`≥ 1 / 3`; attack from [KatzLindell2020], Exercise 8.16, original
bound). -/
theorem le_advantage_feistel2CPAAttack_idealPermGame [Nonempty G] (f₁ f₂ : G → G)
    {l₀ l₁ : G} (r₀ : G) (h01 : l₀ ≠ l₁) (hG : 2 ≤ Fintype.card G) :
    1 - (Fintype.card G : ℝ) / ((Fintype.card G : ℝ) ^ 2 - 1) ≤
      (Game.advantage
        (OracleComp.interpret (fun p => PMF.pure (feistelNetwork [f₁, f₂] p))
          (feistel2CPAAttack l₀ l₁ r₀))
        (idealPermGame (feistel2CPAAttack l₀ l₁ r₀)) : ℝ) := by
  have hN : (2 : ℝ) ≤ Fintype.card G := by exact_mod_cast hG
  exact le_advantage_of_pure_true_of_toReal_le
    (eval_feistel2_feistel2CPAAttack f₁ f₂ l₀ l₁ r₀)
    (idealPermGame_feistel2CPAAttack_true_le r₀ h01 hG)
    (by rw [div_le_iff₀ (by nlinarith)]; nlinarith)

/-! #### 3-round repeated-key (`[f, f, f]`) Feistel CPA distinguisher -/

/-- **The 2-query chosen-plaintext distinguisher against 3-round Feistel with a repeated round
function `[f, f, f]`** ([KatzLindell2020], Exercise 8.18):
query `(x, x)` to obtain `vw`, query `vw.swap = (vw.2, vw.1)` to obtain `lr`, and accept iff
`lr = (x, x)`. -/
def feistel3RepeatedKeyCPAAttack (x : G) :
    OracleComp (fun _ : G × G => G × G) Bool := do
  let vw ← OracleComp.query (spec := fun _ : G × G => G × G) (x, x)
  let lr ← OracleComp.query (spec := fun _ : G × G => G × G) (vw.2, vw.1)
  return decide (lr = (x, x))

omit [AddGroup G] [Fintype G] in
/-- `feistel3RepeatedKeyCPAAttack` makes at most 2 oracle queries. -/
theorem isQueryBounded_feistel3RepeatedKeyCPAAttack (x : G) :
    OracleComp.IsQueryBounded (feistel3RepeatedKeyCPAAttack x) 2 := by
  refine ((OracleComp.IsCostBounded.query (x, x)).bind fun vw =>
    ((OracleComp.IsCostBounded.query (vw.2, vw.1)).bind fun lr =>
      OracleComp.IsCostBounded.pure _ 0)).mono (by omega)

omit [Fintype G] in
/-- **Over any group of exponent two (`∀ a : G, -a = a`), every repeated-key 3-round Feistel
network `feistel3 f f f` is accepted with probability `1` by `feistel3RepeatedKeyCPAAttack x`**
([KatzLindell2020], Exercise 8.18). -/
theorem eval_feistel3_repeated_feistel3RepeatedKeyCPAAttack
    (hneg : ∀ a : G, -a = a) (f : G → G) (x : G) :
    OracleComp.interpret (fun p => PMF.pure (feistel3 f f f p))
      (feistel3RepeatedKeyCPAAttack x) = PMF.pure true := by
  have hrev := prodComm_trans_feistelNetwork_reverse_trans_prodComm hneg [f, f, f]
  have happ := Equiv.congr_fun hrev (feistel3 f f f (x, x))
  change (feistel3 f f f (feistel3 f f f (x, x)).swap).swap =
    (feistel3 f f f).symm (feistel3 f f f (x, x)) at happ
  rw [Equiv.symm_apply_apply] at happ
  have heq : feistel3 f f f ((feistel3 f f f (x, x)).2, (feistel3 f f f (x, x)).1) = (x, x) :=
    Prod.swap_injective happ
  simp [feistel3RepeatedKeyCPAAttack, heq]

omit [AddGroup G] in
/-- Against `idealPermGame`, when `2 ≤ Fintype.card G`, `feistel3RepeatedKeyCPAAttack x` accepts
with probability at most `2 / |G| ^ 2` (`≤ 1 / 2`; original bound). -/
theorem idealPermGame_feistel3RepeatedKeyCPAAttack_true_le [Nonempty G] (x : G)
    (hG : 2 ≤ Fintype.card G) :
    (idealPermGame (feistel3RepeatedKeyCPAAttack x) true).toReal ≤
      2 / (Fintype.card G : ℝ) ^ 2 := by
  have hgame :
      idealPermGame (feistel3RepeatedKeyCPAAttack x) =
        (PMF.uniformOfFintype (Equiv.Perm (G × G))).bind fun π =>
          PMF.pure (decide (π (π (x, x)).swap = (x, x))) := by
    simp [idealPermGame, feistel3RepeatedKeyCPAAttack, Prod.swap, PMF.monad_bind_eq_bind]
  rw [hgame, uniformOfFintype_perm_filter_toReal]
  set p₀ : G × G := (x, x)
  set M := Fintype.card (G × G)
  set P : ℝ := (M.factorial : ℝ)
  have hP : 0 < P := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hN : (2 : ℝ) ≤ Fintype.card G := by exact_mod_cast hG
  have hMr : (M : ℝ) = (Fintype.card G : ℝ) ^ 2 := by simp [M, Fintype.card_prod, sq]
  have hM1 : (4 : ℝ) ≤ M := by rw [hMr]; nlinarith
  have hcover :
      (Finset.univ.filter fun π : Equiv.Perm (G × G) => decide (π (π p₀).swap = p₀) = true) ⊆
        (Finset.univ.filter fun π : Equiv.Perm (G × G) => π p₀ = p₀) ∪
          ((Finset.univ.erase p₀).biUnion fun a =>
            Finset.univ.filter fun π : Equiv.Perm (G × G) => π p₀ = a ∧ π a.swap = p₀) := by
    intro π hπ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hπ
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter,
      true_and, Finset.mem_erase, and_true]
    by_cases h : π p₀ = p₀
    · exact Or.inl h
    · exact Or.inr ⟨π p₀, h, rfl, hπ⟩
  have hA : ((Finset.univ.filter fun π : Equiv.Perm (G × G) => π p₀ = p₀).card : ℝ) ≤ P / M := by
    rw [le_div_iff₀ (by linarith)]; exact card_filter_perm_one_mul_le p₀ p₀
  have hB := card_le_of_biUnion_cover _ (Finset.univ.erase p₀)
    (fun a => Finset.univ.filter fun π : Equiv.Perm (G × G) => π p₀ = a ∧ π a.swap = p₀)
    (P / (M * (M - 1))) (Finset.Subset.refl _)
    (fun a ha => by
      rw [le_div_iff₀ (by nlinarith)]
      refine card_filter_perm_two_mul_le ?_ a p₀
      intro h
      rw [Finset.mem_erase] at ha
      exact ha.1 (Prod.swap_injective (h.symm.trans rfl)))
  have hcard : ((Finset.univ.erase p₀).card : ℝ) = (M : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Nat.cast_sub (Fintype.card_pos_iff.mpr ⟨p₀⟩)]
    simp [M]
  rw [hcard] at hB
  have h3 := (Nat.cast_le (α := ℝ)).mpr
    ((Finset.card_le_card hcover).trans (Finset.card_union_le _ _))
  push_cast at h3
  have hEq : P / (M : ℝ) + ((M : ℝ) - 1) * (P / ((M : ℝ) * ((M : ℝ) - 1))) =
      2 / (Fintype.card G : ℝ) ^ 2 * P := by
    rw [hMr]
    have hsq_ne : (Fintype.card G : ℝ) ^ 2 ≠ 0 := by positivity
    have hsq1_ne : (Fintype.card G : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    field_simp; ring
  rw [div_le_iff₀ hP]
  linarith

/-- Over any group of exponent two (`∀ a : G, -a = a`) with `2 ≤ Fintype.card G`,
`feistel3RepeatedKeyCPAAttack x` distinguishes any repeated-key 3-round Feistel network
`feistel3 f f f` from `idealPermGame` with advantage at least `1 - 2 / |G| ^ 2` (`≥ 1 / 2`; attack
from [KatzLindell2020], Exercise 8.18, original bound). -/
theorem le_advantage_feistel3RepeatedKeyCPAAttack_idealPermGame [Nonempty G]
    (hneg : ∀ a : G, -a = a) (f : G → G) (x : G) (hG : 2 ≤ Fintype.card G) :
    1 - 2 / (Fintype.card G : ℝ) ^ 2 ≤
      (Game.advantage
        (OracleComp.interpret (fun p => PMF.pure (feistel3 f f f p))
          (feistel3RepeatedKeyCPAAttack x))
        (idealPermGame (feistel3RepeatedKeyCPAAttack x)) : ℝ) := by
  have hN : (2 : ℝ) ≤ Fintype.card G := by exact_mod_cast hG
  exact le_advantage_of_pure_true_of_toReal_le
    (eval_feistel3_repeated_feistel3RepeatedKeyCPAAttack hneg f x)
    (idealPermGame_feistel3RepeatedKeyCPAAttack_true_le x hG)
    (by rw [div_le_iff₀ (by nlinarith)]; nlinarith)

/-! #### Sharper permutation-fiber bound for the 3-round CCA distinguisher -/

/-- **Sharper permutation-fiber bound for `feistel3CCAAttack`** (attack from [KatzLindell2020],
Exercise 8.17; original bound): when `l₀ ≠ l₁` and `2 ≤ Fintype.card G`, the true bidirectional
random-permutation game `idealStrongGame` accepts `feistel3CCAAttack l₀ l₁ r₀` with probability at
most `(|G| + 1) / (|G| ^ 2 - 1) = (|G| - 1)⁻¹` (`≤ 1 / 2` for `|G| ≥ 3`). -/
theorem idealStrongGame_feistel3CCAAttack_true_le_inv_card_sub_one [Nonempty G]
    {l₀ l₁ : G} (r₀ : G) (h01 : l₀ ≠ l₁) (hG : 2 ≤ Fintype.card G) :
    (idealStrongGame (feistel3CCAAttack l₀ l₁ r₀) true).toReal ≤
      ((Fintype.card G : ℝ) - 1)⁻¹ := by
  have hgame :
      idealStrongGame (feistel3CCAAttack l₀ l₁ r₀) =
        (PMF.uniformOfFintype (Equiv.Perm (G × G))).bind fun π =>
          let vw₀ := π (l₀, r₀)
          let vw₁ := π (l₁, r₀)
          let lr₂ := π.symm (vw₀.1, (l₁ - l₀) + vw₀.2)
          PMF.pure (decide (-vw₀.1 + lr₂.2 = -vw₁.1 + r₀)) := by
    simp [idealStrongGame, feistel3CCAAttack, feistelStrongOracle, PMF.monad_bind_eq_bind]
  rw [hgame, uniformOfFintype_perm_filter_toReal]
  set x : G × G := (l₀, r₀)
  set y : G × G := (l₁, r₀)
  have hxy : x ≠ y := fun h => h01 (congrArg Prod.fst h)
  let q : G × G → G × G := fun a => (a.1, (l₁ - l₀) + a.2)
  have hq : ∀ a, q a ≠ a := fun a h => by
    have h2 := congrArg Prod.snd h
    dsimp [q] at h2
    exact h01 (sub_eq_zero.mp (add_right_cancel (h2.trans (zero_add a.2).symm))).symm
  set M := Fintype.card (G × G)
  set P : ℝ := (M.factorial : ℝ)
  have hP : 0 < P := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hN : (2 : ℝ) ≤ Fintype.card G := by exact_mod_cast hG
  have hMr : (M : ℝ) = (Fintype.card G : ℝ) ^ 2 := by simp [M, Fintype.card_prod, sq]
  have hM1 : (4 : ℝ) ≤ M := by rw [hMr]; nlinarith
  have hM2 : 2 ≤ M := by exact_mod_cast (show (2 : ℝ) ≤ M by linarith)
  let A : Finset (Equiv.Perm (G × G)) :=
    Finset.univ.biUnion fun a =>
      Finset.univ.filter fun π : Equiv.Perm (G × G) => π x = a ∧ π y = q a
  let F : (G × G) × ((G × G) × G) → Finset (Equiv.Perm (G × G)) :=
    fun t => Finset.univ.filter fun π : Equiv.Perm (G × G) =>
      π x = t.2.1 ∧ π t.1 = q t.2.1 ∧ π y = (r₀ - (-t.2.1.1 + t.1.2), t.2.2)
  let S : Finset ((G × G) × ((G × G) × G)) :=
    ((Finset.univ.erase x).erase y) ×ˢ (Finset.univ ×ˢ Finset.univ)
  have hcover :
      (Finset.univ.filter fun π : Equiv.Perm (G × G) =>
        decide (-(π x).1 + (π.symm (q (π x))).2 = -(π y).1 + r₀) = true) ⊆
        A ∪ S.biUnion F := by
    intro π hπ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hπ
    set c := π.symm (q (π x)) with hc
    have hπc : π c = q (π x) := by simp [c]
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter,
      true_and, A, S, F, Finset.mem_product, Finset.mem_erase, and_true]
    by_cases hcy : c = y
    · exact Or.inl ⟨π x, rfl, by rw [← hcy, hπc]⟩
    · refine Or.inr ⟨(c, π x, (π y).2), ⟨hcy, fun h : c = x => hq (π x) (by rw [← hπc, h])⟩,
        rfl, hπc, Prod.ext ?_ rfl⟩
      have h1 : -(π y).1 = (-(π x).1 + c.2) - r₀ := eq_sub_of_add_eq hπ.symm
      simpa [neg_sub] using congrArg Neg.neg h1
  have hA := card_le_of_biUnion_cover A Finset.univ
    (fun a => Finset.univ.filter fun π : Equiv.Perm (G × G) => π x = a ∧ π y = q a)
    (P / (M * (M - 1))) (Finset.Subset.refl _)
    (fun a _ => by rw [le_div_iff₀ (by nlinarith)]; exact card_filter_perm_two_mul_le hxy a (q a))
  have hB := card_le_of_biUnion_cover (S.biUnion F) S F
    (P / (M * (M - 1) * (M - 2))) (Finset.Subset.refl _)
    (fun t ht => by
      simp only [S, Finset.mem_product, Finset.mem_erase] at ht
      rw [le_div_iff₀ (mul_pos (mul_pos (by linarith) (by linarith)) (by linarith))]
      exact card_filter_perm_three_mul_le (Ne.symm ht.1.2.1) hxy ht.1.1 _ _ _ hM2)
  have hSc : (S.card : ℝ) = ((M : ℝ) - 2) * ((M : ℝ) * (Fintype.card G : ℝ)) := by
    simp only [S, Finset.card_product, Finset.card_univ]; push_cast; rw [card_erase_erase hxy]
  rw [hSc] at hB
  rw [Finset.card_univ] at hA
  have h3 := (Nat.cast_le (α := ℝ)).mpr
    ((Finset.card_le_card hcover).trans (Finset.card_union_le _ _))
  push_cast at h3
  have hEq : (M : ℝ) * (P / ((M : ℝ) * ((M : ℝ) - 1))) +
      ((M : ℝ) - 2) * ((M : ℝ) * (Fintype.card G : ℝ)) *
        (P / ((M : ℝ) * ((M : ℝ) - 1) * ((M : ℝ) - 2))) =
      ((Fintype.card G : ℝ) - 1)⁻¹ * P := by
    rw [hMr]
    have hsq_ne : (Fintype.card G : ℝ) ^ 2 ≠ 0 := by positivity
    have hsq1_ne : (Fintype.card G : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    have hsq2_ne : (Fintype.card G : ℝ) ^ 2 - 2 ≠ 0 := by nlinarith
    have hN1_ne : (Fintype.card G : ℝ) - 1 ≠ 0 := by linarith
    field_simp; ring
  rw [div_le_iff₀ hP]
  linarith

/-- **Sharper chosen-ciphertext advantage lower bound for `feistel3CCAAttack`** (attack from
[KatzLindell2020], Exercise 8.17; original bound): when `l₀ ≠ l₁` and `2 ≤ Fintype.card G`,
`feistel3CCAAttack l₀ l₁ r₀` distinguishes any 3-round Feistel network `feistel3 f₁ f₂ f₃` from
`idealStrongGame` with advantage at least `1 - (|G| - 1)⁻¹` (`≥ 1 / 2` for `|G| ≥ 3`). -/
theorem le_advantage_feistel3CCAAttack_idealStrongGame_of_two_le_card [Nonempty G]
    (f₁ f₂ f₃ : G → G) {l₀ l₁ : G} (r₀ : G) (h01 : l₀ ≠ l₁) (hG : 2 ≤ Fintype.card G) :
    1 - ((Fintype.card G : ℝ) - 1)⁻¹ ≤
      (Game.advantage
        (OracleComp.interpret (feistelStrongOracle (feistel3 f₁ f₂ f₃))
          (feistel3CCAAttack l₀ l₁ r₀))
        (idealStrongGame (feistel3CCAAttack l₀ l₁ r₀)) : ℝ) := by
  have hN : (2 : ℝ) ≤ Fintype.card G := by exact_mod_cast hG
  exact le_advantage_of_pure_true_of_toReal_le
    (eval_feistel3_feistel3CCAAttack f₁ f₂ f₃ l₀ l₁ r₀)
    (idealStrongGame_feistel3CCAAttack_true_le_inv_card_sub_one r₀ h01 hG)
    (inv_le_one_of_one_le₀ (by linarith))

end Distinguishers

end Cslib.Crypto.LubyRackoff
