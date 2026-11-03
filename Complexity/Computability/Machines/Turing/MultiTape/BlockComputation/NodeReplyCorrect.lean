/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.NodeReply
public import Complexity.Computability.TreeEval.Ary.Packed.RawControllerCorrect
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ImplicitNodeCorrect
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.InitialVectorCorrect
import Complexity.Foundations.Data.List.Lookup

/-!
# Native node replies agree with the existing encoded tree

On typed paths, paid node replies have exactly the existing tree's invalid/leaf/gate tags.
Every coordinate of a leaf reply is the existing packed leaf value. The capacity condition
pays the full runtime leaf-vector length; classification alone never authorizes allocation.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.NodeReply

open Cslib.TreeEval.Ary

/-- The native node reply reports the existing node kind and, for leaves, every packed value. -/
theorem reply_correct_nodeAt {k q s r m : ℕ} {Q : Type}
    (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (w : List Bool)
    (b : ℕ) [NeZero b] (σ limit : ℕ) (path : List (Fin (k * 3 + 1)))
    (hcapacity : r ≤ limit.size) (hb : Encoding.width k s b ≤ r * m) :
    match (encodedTree (MultiTapePTM.ofDeterministic M) w b
        (scheduleOfNat k q σ) e).nodeAt path with
    | .none => (reply M e ((σ, q, path.map Fin.val), (limit, m, r))).1 = 0
    | .gate _ => (reply M e ((σ, q, path.map Fin.val), (limit, m, r))).1 = 2
    | .leaf v => (reply M e ((σ, q, path.map Fin.val), (limit, m, r))).1 = 1 ∧
        ∀ j : Fin r,
          ((reply M e ((σ, q, path.map Fin.val), (limit, m, r))).2).getD j.val 0 =
            (Packed.packBits hb v j).val := by
  have hclass := ImplicitNode.classify_eq_nodeAt (q := q) M e w b σ path
  rw [encodedTree, tree, Descending.nodeAt_tree] at hclass ⊢
  by_cases hlt : path.length < q
  · simp only [Descending.lookup, hlt, ↓reduceIte, ImplicitNode.kind] at hclass ⊢
    simp [reply, hclass]
  · by_cases heq : path.length = q
    · simp only [Descending.lookup, heq, lt_self_iff_false, ↓reduceIte,
        ImplicitNode.kind] at hclass ⊢
      constructor
      · simp [reply, hclass, hcapacity]
      · intro j
        simp only [reply, hclass, hcapacity, ↓reduceIte]
        rw [InitialVector.values_eq_packBits M e limit b hcapacity hb]
        exact List.getD_ofFn_of_lt _ j.isLt 0
    · simp only [Descending.lookup, hlt, heq, ↓reduceIte, ImplicitNode.kind] at hclass ⊢
      simp [reply, hclass]

/-- A call-mode evaluator state receives exactly the existing node-reply contract. -/
theorem reply_correct_call {k q s r m p : ℕ} {Q : Type} [Fact p.Prime]
    (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (w : List Bool)
    (b : ℕ) [NeZero b] (σ limit : ℕ) (hcapacity : r ≤ limit.size)
    (hb : Encoding.width k s b ≤ r * m)
    (E : Gate (k * 3 + 1) (Encoding.width k s b) →
      (Fin (k * 3 + 1) → Fin r → ZMod p) → Fin r → ZMod p)
    (cfg : Iter.Cfg (ZMod p) (k * 3 + 1) r) (c : ZMod p)
    (target : Fin (k * 3 + 1 + 1)) (hmode : cfg.mode = .call c target) :
    Packed.RawController.ReplyCorrect
      (fun bits j => ((Packed.packBits hb bits j).val : ZMod p)) E
      (encodedTree (MultiTapePTM.ofDeterministic M) w b (scheduleOfNat k q σ) e).nodeAt cfg
      (reply M e ((σ, q, (Iter.path cfg.stack).map Fin.val), (limit, m, r))) := by
  rw [Packed.RawController.ReplyCorrect, hmode]
  have hs := reply_correct_nodeAt (q := q) M e w b σ limit (Iter.path cfg.stack) hcapacity hb
  cases hn : (encodedTree (MultiTapePTM.ofDeterministic M) w b
      (scheduleOfNat k q σ) e).nodeAt (Iter.path cfg.stack) with
  | none => simpa only [hn] using hs
  | gate f => simpa only [hn] using hs
  | leaf v =>
    simp only [hn] at hs
    exact ⟨hs.1, fun j => congrArg (fun n : ℕ => (n : ZMod p)) (hs.2 j)⟩

end Turing.MultiTapePTM.BlockComputation.NodeReply
