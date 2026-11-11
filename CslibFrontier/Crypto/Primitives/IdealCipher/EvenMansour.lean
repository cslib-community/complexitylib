/-
Copyright (c) 2024 The Cslib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Jetski
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.RandomPermutation
public import CslibFrontier.Foundations.Data.BitString.Basic

/-!
# Even-Mansour Cipher
public import CslibFrontier.Languages.Probabilistic.IdealCipher

We formalize the 1-key Even-Mansour cipher $E_k(x) = P(x \oplus k) \oplus k$,
where $P$ is an ideal permutation.
-/

public section
open Cslib
open Cslib.RandomPermutation

variable {n : ℕ}

def evenMansour (k : BitString n) (P : BitString n → BitString n) (x : BitString n) : BitString n :=
  P (x + k) + k

def evenMansourInv (k : BitString n) (P_inv : BitString n → BitString n) (y : BitString n) : BitString n :=
  P_inv (y + k) + k

def evenMansourPerm (P : Equiv.Perm (BitString n)) (k : BitString n) : Equiv.Perm (BitString n) where
  toFun := evenMansour k P
  invFun := evenMansourInv k P.symm
  left_inv x := by
    dsimp [evenMansour, evenMansourInv]
    have h1 : P.symm (P (x + k) + k + k) = P.symm (P (x + k)) := by
      rw [add_assoc, BitString.add_self, add_zero]
    rw [h1, Equiv.symm_apply_apply]
    rw [add_assoc, BitString.add_self, add_zero]
  right_inv y := by
    dsimp [evenMansour, evenMansourInv]
    have h1 : P (P.symm (y + k) + k + k) = P (P.symm (y + k)) := by
      rw [add_assoc, BitString.add_self, add_zero]
    rw [h1, Equiv.apply_symm_apply]
    rw [add_assoc, BitString.add_self, add_zero]

