/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ConcreteEvaluator
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ConcreteSupplierCorrect
public import Complexity.Computability.TreeEval.Ary.Packed.RawControllerOutput

/-!
# The concrete implicit evaluator computes the encoded block tree

The fixed same-input evaluator now has concrete suppliers in both request modes. It realizes
the complete masking procedure with an explicit bound at every physical clock. With the usual
degree condition and an initially zero target, its native register decoder returns the existing
encoded block tree's Boolean value. No supplier assumption remains.

These execution theorems start from actual supplied runtime metadata and a canonical bank.
They do not construct the outer simulator's initializer or time/schedule-guessing loop.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.ConcreteEvaluator

open Cslib.TreeEval.Ary Cslib.TreeEval.Ary.Packed
open QueryReplay

/-- Concrete node and gate suppliers realize the complete masking run, with all-clock space. -/
theorem exists_runFrom_root {k q s p r m : ℕ} {Q : Type} [Finite Q] [Fact p.Prime]
    (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (w : List Bool)
    (b : ℕ) [NeZero b] (σ : ℕ)
    (hcapacity : r ≤ ((2 ^ m) ^ ((k * 3 + 1) * r)).size)
    (hb : Encoding.width k s b ≤ r * m) (hm : 0 < m) (hsp : 2 ^ m ≤ p)
    (h : Fin (2 ^ m) ↪ ZMod p) (hh : ∀ a, h a = (a.val : ZMod p))
    (S : Cslib.TreeEval.Ary.State (ZMod p) (k * 3 + 1) r) (c : ZMod p)
    (target : Fin (k * 3 + 1 + 1)) :
    let ctx : ConcreteSupplier.Context :=
      (w.length, b, σ, q, m, 2 ^ m, (2 ^ m) ^ ((k * 3 + 1) * r))
    let encode := fun bits j => ((Packed.packBits hb bits j).val : ZMod p)
    let extend := Packed.gateExtension h (Packed.packBits hb) (Packed.unpackBits hb)
    let tree := encodedTree (MultiTapePTM.ofDeterministic M) w b (scheduleOfNat k q σ) e
    let initial : State k Q :=
      .inl (ctx, (p, k * 3 + 1, r), RawController.ofCfg (Iter.initialCfg S c target))
    ∃ clock, (machine M e).runFrom w initial clock =
        .inl (ctx, (p, k * 3 + 1, r), RawController.ofCfg
          (⟨procWith encode extend (RawController.units p) tree c target S, [], .ret⟩ :
            Iter.Cfg (ZMod p) (k * 3 + 1) r)) ∧
      ∀ i ≤ clock, (encState ((machine M e).runFrom w initial i)).length ≤
        RawController.Query.queryStateBound (ConcreteSupplier.encContext ctx).length
          p (k * 3 + 1) r q
          (ConcreteSupplier.replySpace k s Q w.length b σ q m (2 ^ m)
            ((2 ^ m) ^ ((k * 3 + 1) * r)) p (k * 3 + 1) r) := by
  apply RawController.Query.exists_runFrom_root_encoded_bound
    ConcreteSupplier.encContext GateReply.encState template (GateReply.machine M e)
    (ConcreteSupplier.start M e) GateReply.answer w _ (by omega)
  intro n req hneed
  exact ConcreteSupplier.exists_first_reply_correct M e w b σ hcapacity hb hm hsp h hh _ req hneed

/-- A zero-target concrete run returns a physical bank whose native decoder yields the root. -/
theorem exists_runFrom_decode_root {k q s p r m : ℕ} {Q : Type} [Finite Q] [Fact p.Prime]
    (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (w : List Bool)
    (b : ℕ) [NeZero b] (σ : ℕ)
    (hcapacity : r ≤ ((2 ^ m) ^ ((k * 3 + 1) * r)).size)
    (hb : Encoding.width k s b ≤ r * m) (hm : 0 < m) (hsp : 2 ^ m ≤ p)
    (h : Fin (2 ^ m) ↪ ZMod p) (hh : ∀ a, h a = (a.val : ZMod p))
    (hdegree : (k * 3 + 1) * r * (2 ^ m - 1) < p - 1)
    (S : Cslib.TreeEval.Ary.State (ZMod p) (k * 3 + 1) r)
    (target : Fin (k * 3 + 1 + 1)) (hzero : S target = 0) :
    let ctx : ConcreteSupplier.Context :=
      (w.length, b, σ, q, m, 2 ^ m, (2 ^ m) ^ ((k * 3 + 1) * r))
    let tree := encodedTree (MultiTapePTM.ofDeterministic M) w b (scheduleOfNat k q σ) e
    let initial : State k Q :=
      .inl (ctx, (p, k * 3 + 1, r), RawController.ofCfg (Iter.initialCfg S 1 target))
    ∃ clock bank, (machine M e).runFrom w initial clock =
        .inl (ctx, (p, k * 3 + 1, r), bank, [], none) ∧
      RawController.Output.decode ((Encoding.width k s b, m, p, r, target.val), bank) =
        List.ofFn tree.eval ∧
      ∀ i ≤ clock, (encState ((machine M e).runFrom w initial i)).length ≤
        RawController.Query.queryStateBound (ConcreteSupplier.encContext ctx).length
          p (k * 3 + 1) r q
          (ConcreteSupplier.replySpace k s Q w.length b σ q m (2 ^ m)
            ((2 ^ m) ^ ((k * 3 + 1) * r)) p (k * 3 + 1) r) := by
  classical
  obtain ⟨clock, hrun, hbound⟩ := exists_runFrom_root M e w b σ hcapacity hb hm hsp h hh S 1 target
  refine ⟨clock, _, hrun, ?_, hbound⟩
  have hdecode := RawController.Output.decode_procWith_zero_target hb hm hsp h hh
    (by simpa only [Fintype.card_fin, ZMod.card] using hdegree)
    (encodedTree (MultiTapePTM.ofDeterministic M) w b (scheduleOfNat k q σ) e) S target hzero
  have hencode : (fun bits j => h (Packed.packBits hb bits j)) =
      (fun bits j => ((Packed.packBits hb bits j).val : ZMod p)) :=
    funext fun _ => funext fun _ => hh _
  rw [hencode] at hdecode
  exact hdecode

end Turing.MultiTapePTM.BlockComputation.ConcreteEvaluator
