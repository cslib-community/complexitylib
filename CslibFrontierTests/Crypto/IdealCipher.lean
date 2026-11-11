/-
Copyright (c) 2024 The Cslib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Jetski
-/

import CslibFrontier.Crypto.Primitives.IdealCipher.EvenMansour
import CslibFrontier.Foundations.Data.BitString.Basic

open Cslib
open Cslib.RandomPermutation

def testB0 : BitString 3 := fun _ => false
def testB1 : BitString 3 := fun i => i.val == 1

def testP : Equiv.Perm (BitString 3) where
  toFun := fun x => x + testB1
  invFun := fun x => x + testB1
  left_inv := by
    intro x
    simp [add_assoc, BitString.add_self, add_zero]
  right_inv := by
    intro x
    simp [add_assoc, BitString.add_self, add_zero]

def testK : BitString 3 := fun i => i.val == 2

#eval evenMansourPerm testP testK testB0 == testB1
#eval evenMansourPerm testP testK testB1 == testB0
