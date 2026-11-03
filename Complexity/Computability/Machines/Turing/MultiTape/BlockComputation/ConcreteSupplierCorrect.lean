/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ConcreteSupplier
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ConcreteSupplierSpace
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.NodeReplyCorrect
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.GateReplyBounds
public import Complexity.Computability.TreeEval.Ary.Packed.RawControllerPoint
public import Complexity.Computability.TreeEval.Ary.Packed.RawControllerQuery
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.FirstHalt

/-!
# Concrete replies discharge both evaluator request cases

Actual requests from canonical evaluator states receive the existing node or gate-update
contract. The same original input is used throughout. Neither a tree lookup oracle nor a gate
supplier premise is assumed. A uniform metadata allowance covers every physical clock through
the first halt, including all suspended interpolation calls.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.ConcreteSupplier

open Cslib.TreeEval.Ary Cslib.TreeEval.Ary.Packed
open QueryReplay

private theorem need_call {p d r : ℕ} [Fact p.Prime]
    (S : Cslib.TreeEval.Ary.State (ZMod p) d r) (stack : List (Iter.Frame (ZMod p) d))
    (c : ZMod p) (target : Fin (d + 1)) :
    RawController.need p d r (RawController.ofCfg ⟨S, stack, .call c target⟩) =
      some (0, (Iter.path stack).map Fin.val, [], 0) := by
  have hv := RawController.validBank_ofRegs (Fact.out : p.Prime).two_le S
  simp only [RawController.need, RawController.ofCfg, hv, ↓reduceIte,
    RawController.needCore, RawController.ofMode, RawController.path_ofFrame]

private theorem need_ret {p d r : ℕ} [Fact p.Prime]
    (S : Cslib.TreeEval.Ary.State (ZMod p) d r) (fr : Iter.Frame (ZMod p) d)
    (stack : List (Iter.Frame (ZMod p) d))
    (hu : fr.undo = false) (hc : ¬fr.child.val + 1 < d) :
    RawController.need p d r (RawController.ofCfg ⟨S, fr :: stack, .ret⟩) =
      some (1, (Iter.path stack).map Fin.val,
        RawController.point d r fr.target.val (RawController.ofRegs S), 0) := by
  have hv := RawController.validBank_ofRegs (Fact.out : p.Prime).two_le S
  simp only [RawController.need, RawController.ofCfg, hv, ↓reduceIte,
    RawController.needCore, RawController.ofMode, List.map_cons, RawController.ofFrame,
    hu, hc, decide_false, Bool.false_or, Bool.false_eq_true, RawController.path_ofFrame]

/-- One uniform allowance covers both immediate node replies and routed gate computations. -/
@[expose] noncomputable def replySpace (k s : ℕ) (Q : Type)
    (N b σ q m alphabet limit p d r : ℕ) : ℕ :=
  gateSpace k s Q N b σ q m alphabet limit p d r +
    r * (2 * (MultiTapeTM.encNat p).length + 1) + 9

/-- Every actual canonical request returns at its first halt and satisfies `ReplyCorrect`. -/
theorem exists_first_reply_correct {k q s p r m : ℕ} {Q : Type} [Finite Q] [Fact p.Prime]
    (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (w : List Bool)
    (b : ℕ) [NeZero b] (σ : ℕ)
    (hcapacity : r ≤ ((2 ^ m) ^ ((k * 3 + 1) * r)).size)
    (hb : Encoding.width k s b ≤ r * m) (hm : 0 < m) (hsp : 2 ^ m ≤ p)
    (h : Fin (2 ^ m) ↪ ZMod p) (hh : ∀ a, h a = (a.val : ZMod p))
    (cfg : Iter.Cfg (ZMod p) (k * 3 + 1) r) (req : RawController.Need)
    (hneed : RawController.need p (k * 3 + 1) r (RawController.ofCfg cfg) = some req) :
    let ctx : Context := (w.length, b, σ, q, m, 2 ^ m, (2 ^ m) ^ ((k * 3 + 1) * r))
    let actual := start M e (ctx, (p, k * 3 + 1, r), req)
    ∃ U,
      (∀ t < U, (GateReply.machine M e).halted
        ((GateReply.machine M e).runFrom w actual t) = false) ∧
      (GateReply.machine M e).halted ((GateReply.machine M e).runFrom w actual U) = true ∧
      RawController.ReplyCorrect
        (fun bits j => ((Packed.packBits hb bits j).val : ZMod p))
        (Packed.gateExtension h (Packed.packBits hb) (Packed.unpackBits hb))
        (encodedTree (MultiTapePTM.ofDeterministic M) w b (scheduleOfNat k q σ) e).nodeAt cfg
        (GateReply.answer ((GateReply.machine M e).runFrom w actual U)) ∧
      ∀ t ≤ U, (GateReply.encState ((GateReply.machine M e).runFrom w actual t)).length ≤
        replySpace k s Q w.length b σ q m (2 ^ m)
          ((2 ^ m) ^ ((k * 3 + 1) * r)) p (k * 3 + 1) r := by
  classical
  let limit := (2 ^ m) ^ ((k * 3 + 1) * r)
  let ctx : Context := (w.length, b, σ, q, m, 2 ^ m, limit)
  change ∃ U, _
  rcases cfg with ⟨S, stack, mode⟩
  cases mode with
  | call c target =>
    rw [need_call] at hneed
    cases hneed
    refine ⟨0, ?_, ?_, ?_, ?_⟩
    · intro t ht
      omega
    · rfl
    · change RawController.ReplyCorrect _ _ _ ⟨S, stack, .call c target⟩
        (NodeReply.reply M e ((σ, q, (Iter.path stack).map Fin.val), (limit, m, r)))
      exact NodeReply.reply_correct_call M e w b σ limit hcapacity hb _
        ⟨S, stack, .call c target⟩ c target rfl
    · intro t ht
      have htzero : t = 0 := by omega
      subst t
      have hbound := node_reply_encoding_le M e limit b σ q
        ((Iter.path stack).map Fin.val) hcapacity hb hsp
      change (RawController.encReply (NodeReply.reply M e
        ((σ, q, (Iter.path stack).map Fin.val), (limit, m, r)))).length + 1 ≤ _
      dsimp only [replySpace]
      omega
  | ret =>
    cases stack with
    | nil =>
      have hv := RawController.validBank_ofRegs (Fact.out : p.Prime).two_le S
      simp [RawController.need, RawController.ofCfg, RawController.ofMode, hv,
        RawController.needCore] at hneed
    | cons fr stack =>
      by_cases hguard : fr.undo = false ∧ ¬fr.child.val + 1 < k * 3 + 1
      · rw [need_ret S fr stack hguard.1 hguard.2] at hneed
        cases hneed
        rw [RawController.point_ofRegs]
        obtain ⟨T, values, hhalt, hans, hvalues, hsize⟩ :=
          GateReply.exists_runFrom_nodeAt_padded_bounded
          M e w b σ (Iter.path stack) (fun j => S (Cslib.TreeEval.Ary.reg fr.target j))
          hcapacity hb hm hsp h hh
        obtain ⟨U, hle, hU, hpre, hstate⟩ := QueryMachine.exists_first_halt_le
          (GateReply.machine M e) w _ T hhalt
        refine ⟨U, hpre, hU, ?_, ?_⟩
        · change RawController.ReplyCorrect _ _ _ ⟨S, fr :: stack, .ret⟩
            (GateReply.answer ((GateReply.machine M e).runFrom w
              (GateReply.initial M e ((σ, q, (Iter.path stack).map Fin.val),
                (((w.length, b, 0, 0, m, 0, r * m), (p, 2 ^ m, (k * 3 + 1) * r),
                  List.ofFn (fun a => p + (Cslib.BitString.blocksEquiv.symm
                    (fun j => S (Cslib.TreeEval.Ary.reg fr.target j)) a).val), limit), r))) U))
          rw [hstate]
          simp only [RawController.ReplyCorrect, hguard]
          rw [hans]
          intro j
          cases hn : (encodedTree (MultiTapePTM.ofDeterministic M) w b
              (scheduleOfNat k q σ) e).nodeAt (Iter.path stack) <;>
            simpa only [RawController.expectedGate, hn, Pi.zero_apply] using hvalues j
        · intro t ht
          have hlocal := hsize t (ht.trans hle)
          have huniform := allowance_le_padded (k := k) (s := s) (Q := Q)
            w.length b σ q m (2 ^ m) limit p (k * 3 + 1) r 1 0
            ((Iter.path stack).map Fin.val)
            (Cslib.BitString.blocksEquiv.symm
              (fun j => S (Cslib.TreeEval.Ary.reg fr.target j)))
            (Fact.out : p.Prime).pos
          change (GateReply.encState ((GateReply.machine M e).runFrom w
            (GateReply.initial M e ((σ, q, (Iter.path stack).map Fin.val),
              (((w.length, b, 0, 0, m, 0, r * m), (p, 2 ^ m, (k * 3 + 1) * r),
                List.ofFn (fun a => p + (Cslib.BitString.blocksEquiv.symm
                  (fun j => S (Cslib.TreeEval.Ary.reg fr.target j)) a).val), limit), r))) t)).length
              ≤ _
          apply hlocal.trans
          change GateReply.allowance k s Q
            (gateArgs (ctx, (p, k * 3 + 1, r), (1, (Iter.path stack).map Fin.val,
              List.ofFn (fun a => p + (Cslib.BitString.blocksEquiv.symm
                (fun j => S (Cslib.TreeEval.Ary.reg fr.target j)) a).val), 0))) ≤ _
          exact huniform.trans (by dsimp only [replySpace, limit]; omega)
      · have hv := RawController.validBank_ofRegs (Fact.out : p.Prime).two_le S
        simp_all [RawController.need, RawController.ofCfg, RawController.ofMode,
          RawController.needCore, RawController.ofFrame]

end Turing.MultiTapePTM.BlockComputation.ConcreteSupplier
