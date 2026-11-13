/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Protocol

/-!
# Alternating bit protocols

Every bit protocol can be made alternating by inserting constant messages when the next real
speaker is out of turn. The first player can be specified, and the depth increases by at most a
factor of two. Both branches of each inserted node are the same continuation, so the construction
also alternates on unreachable branches. This structural guarantee supports simulations whose
source-density invariant depends on the next speaker.
-/

@[expose] public section

namespace Cslib.Communication.Protocol

variable {X Y Z : Type*}

/-- Every internal node has the prescribed speaker and its children have the opposite speaker.
`true` means Alice's turn; `false` means Bob's turn. Leaves satisfy either turn. -/
def Alternates : Bool → Protocol X Y Z → Prop
  | _, .output _ => True
  | turn, .alice _ p₀ p₁ => turn = true ∧ Alternates false p₀ ∧ Alternates false p₁
  | turn, .bob _ p₀ p₁ => turn = false ∧ Alternates true p₀ ∧ Alternates true p₁

/-- Insert constant messages so the protocol alternates from the requested first speaker.
`true` starts with Alice and `false` starts with Bob. -/
def alternate : Protocol X Y Z → Bool → Protocol X Y Z
  | .output z, _ => .output z
  | .alice send p₀ p₁, turn =>
    let real := .alice send (alternate p₀ false) (alternate p₁ false)
    if turn then real else .bob (fun _ => false) real real
  | .bob send p₀ p₁, turn =>
    let real := .bob send (alternate p₀ true) (alternate p₁ true)
    if turn then .alice (fun _ => false) real real else real

/-- Inserting dummy messages preserves every output. -/
@[simp] theorem run_alternate (p : Protocol X Y Z) (turn : Bool) (x : X) (y : Y) :
    (p.alternate turn).run x y = p.run x y := by
  induction p generalizing turn with
  | output => rfl
  | alice send p₀ p₁ ih₀ ih₁ => cases turn <;> simp [alternate, ih₀, ih₁]
  | bob send p₀ p₁ ih₀ ih₁ => cases turn <;> simp [alternate, ih₀, ih₁]

/-- The normalized protocol alternates even along unreachable branches. -/
theorem alternates_alternate (p : Protocol X Y Z) (turn : Bool) :
    Alternates turn (p.alternate turn) := by
  induction p generalizing turn with
  | output => trivial
  | alice send p₀ p₁ ih₀ ih₁ => cases turn <;> simp [alternate, Alternates, ih₀, ih₁]
  | bob send p₀ p₁ ih₀ ih₁ => cases turn <;> simp [alternate, Alternates, ih₀, ih₁]

/-- At most one dummy message is inserted per original message. -/
theorem depth_alternate_le (p : Protocol X Y Z) (turn : Bool) :
    (p.alternate turn).depth ≤ 2 * p.depth := by
  induction p generalizing turn with
  | output => simp [alternate]
  | alice send p₀ p₁ ih₀ ih₁ =>
    have h₀ := ih₀ false
    have h₁ := ih₁ false
    cases turn <;> simp [alternate, depth] <;> omega
  | bob send p₀ p₁ ih₀ ih₁ =>
    have h₀ := ih₀ true
    have h₁ := ih₁ true
    cases turn <;> simp [alternate, depth] <;> omega

end Cslib.Communication.Protocol
