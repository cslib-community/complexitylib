/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.ChildCursor

public section

open Cslib.Circuits.Frontier.ChildCursor

namespace Cslib.Tests.TensorNetworkChildCursor

/-! Two nodes: node `0` has one mode of weight `1` and budget `2`, so the exponents `0, 1`; node
`1` has two modes of weights `1, 2` and budget `2`, so the exponents `00, 10`. With one point and
two groups the cursor visits eight children. -/

def ws (t : ℕ) : List ℕ := if t = 0 then [1] else [1, 2]
def ps (_ : ℕ) : ℕ := 2

example : cursorList ws ps 2 1 2 =
    [(0, 0, [0], 0), (0, 0, [0], 1), (0, 0, [1], 0), (0, 0, [1], 1),
      (1, 0, [0, 0], 0), (1, 0, [0, 0], 1), (1, 0, [1, 0], 0), (1, 0, [1, 0], 1)] := by
  decide +kernel

/-- The cursor walks the list and stops after the last child. -/
example : cursorStart ws = (0, 0, [0], 0) ∧
    cursorNext ws ps 2 1 2 (0, 0, [0], 1) = some (0, 0, [1], 0) ∧
    cursorNext ws ps 2 1 2 (0, 0, [1], 1) = some (1, 0, [0, 0], 0) ∧
    cursorNext ws ps 2 1 2 (1, 0, [1, 0], 1) = none := by
  decide +kernel

/-- The walk, by index, from the general theorem. -/
example : ∃ h : 0 < (cursorList ws ps 2 1 2).length,
    (cursorList ws ps 2 1 2)[0] = cursorStart ws ∧
    (∀ c (hc : c + 1 < (cursorList ws ps 2 1 2).length),
      cursorNext ws ps 2 1 2 (cursorList ws ps 2 1 2)[c] = some (cursorList ws ps 2 1 2)[c + 1]) ∧
    cursorNext ws ps 2 1 2 ((cursorList ws ps 2 1 2)[(cursorList ws ps 2 1 2).length - 1]) =
      none :=
  cursorList_walk (by norm_num) (by norm_num) (fun _ => by simp [ps])
    (fun t w hw => by unfold ws at hw; split_ifs at hw <;> simp at hw <;> omega) (by norm_num)

/-- With the value `t + Σβ + g + 1` at each child, the call stores `1·2 + 2·3 = 8` for node `0` and
`2·3 + 3·4 = 18` for node `1`. -/
def val (s : State) : ℕ := s.1 + s.2.2.1.sum + s.2.2.2 + 1

example : (runAcc ws ps 2 (· * ·) (· + ·) 1 0 val (cursorList ws ps 2 1 2) (1, 0, [])) =
    (1, 0, [8, 18]) := by
  decide +kernel

end Cslib.Tests.TensorNetworkChildCursor
