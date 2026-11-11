/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith
public import CslibFrontier.Computability.TreeEval.Reader.Correct
public import CslibFrontier.Computability.TreeEval.Reader.Arith

/-!
# Tree Evaluation instances of all sizes

`Cslib.TreeEval.Instance` collects the instances of all value lengths and heights, and
`Cslib.TreeEval.encInstance` encodes them injectively by `Cslib.TreeEval.Tree.encode`: the header
determines the value length and the height, and the body determines the tree, as the table of a
gate determines the gate.

## Main definitions

* `Cslib.TreeEval.Instance`: an instance of some value length and height.
* `Cslib.TreeEval.encInstance`: the encoding of instances.

## Main results

* `Cslib.TreeEval.encode_injective`: encoding an instance into a bit string is injective.
* `Cslib.TreeEval.ell_lt_length_encNat_length_encInstance`: for `1 ≤ I.height`, the value length
  `I.ell` is strictly below the binary length of `(encInstance I).length`.
* `Cslib.TreeEval.height_lt_length_encNat_length_encInstance`: for `1 ≤ I.ell`, the height
  `I.height` is strictly below the binary length of `(encInstance I).length`.
-/

@[expose] public section

namespace Cslib.TreeEval

open Turing MultiTapeTM

/-- A Tree Evaluation instance of some value length and height. -/
structure Instance where
  /-- The value length. -/
  ell : ℕ
  /-- The height. -/
  height : ℕ
  /-- The tree. -/
  tree : Tree ell height

open Reader in
/-- The table of a gate determines the gate. -/
theorem table_injective {ℓ : ℕ} {f g : Gate ℓ}
    (h : table f = table g) : f = g := by
  funext a b i
  let k := cubeEquiv ℓ (Sum.elim a b)
  have hk : Sum.elim (lowBits ℓ k) (highBits ℓ k) = Sum.elim a b := by
    rw [← cubeEquiv_symm_apply, Equiv.symm_apply_apply]
  have ha : lowBits ℓ k = a := funext fun j => congrFun hk (Sum.inl j)
  have hb : highBits ℓ k = b := funext fun j => congrFun hk (Sum.inr j)
  have hlt : (k : ℕ) * ℓ + i < tableLength ℓ := by
    have h4 : (k : ℕ) < 4 ^ ℓ := by rw [four_pow_eq]; exact k.isLt
    rw [tableLength]
    nlinarith [i.isLt]
  have := congrArg (fun l : List Bool => l[(k : ℕ) * ℓ + i]?) h
  simp only [table, List.getElem?_ofFn, hlt, dite_true, Option.some.injEq,
    tableBit_mul_add, ha, hb] at this
  exact this

namespace Tree

/-- The body determines the tree. -/
theorem body_injective {ℓ : ℕ} : ∀ {h : ℕ} {T T' : Tree ℓ h}, T.body = T'.body → T = T'
  | _, .leaf v, .leaf v', hb => by
    simp only [body] at hb
    rw [List.ofFn_injective hb]
  | _, .node f l r, .node f' l' r', hb => by
    simp only [body, List.append_assoc] at hb
    obtain ⟨h₁, hb⟩ := List.append_inj hb (by simp)
    obtain ⟨h₂, h₃⟩ := List.append_inj hb (by simp)
    rw [table_injective h₁, body_injective h₂, body_injective h₃]

end Tree

/-- Encoding a Tree Evaluation instance into a bit string is injective. -/
theorem encode_injective {I J : Instance} (h : I.tree.encode = J.tree.encode) : I = J := by
  obtain ⟨ℓ, H, T⟩ := I
  obtain ⟨ℓ', H', T'⟩ := J
  obtain ⟨rfl, rfl, hb⟩ := Tree.header_append_inj h
  cases Tree.body_injective hb; rfl

/-- **The encoding of instances.** -/
def encInstance : Instance ↪ List Bool := ⟨fun I => I.tree.encode, fun _ _ => encode_injective⟩

@[simp] theorem encInstance_apply (I : Instance) : encInstance I = I.tree.encode := rfl

theorem length_encInstance (I : Instance) :
    (encInstance I).length = I.ell + I.height + 2 + bodyLength I.ell I.height := by
  simp

/-- Every encoded instance has at least the two delimiter zeroes of the header. -/
theorem two_le_length_encInstance (I : Instance) : 2 ≤ (encInstance I).length := by
  rw [length_encInstance]; omega

/-- For `1 ≤ I.height`, the value length `I.ell` is strictly less than the binary length of the
encoded instance length. -/
theorem ell_lt_length_encNat_length_encInstance {I : Instance} (hH : 1 ≤ I.height) :
    I.ell < (encNat (encInstance I).length).length := by
  rw [length_encNat_eq_size, Nat.lt_size]
  rcases Nat.eq_zero_or_pos I.ell with hℓ | hℓ
  · have := two_le_length_encInstance I
    rw [hℓ, pow_zero]
    omega
  · have := two_pow_ell_le_bodyLength hℓ hH
    rw [length_encInstance]
    omega

/-- For `1 ≤ I.ell`, the height `I.height` is strictly less than the binary length of the encoded
instance length. -/
theorem height_lt_length_encNat_length_encInstance {I : Instance} (hℓ : 1 ≤ I.ell) :
    I.height < (encNat (encInstance I).length).length := by
  rw [length_encNat_eq_size, Nat.lt_size, length_encInstance]
  have := two_pow_height_le_bodyLength hℓ I.height
  omega

end Cslib.TreeEval
