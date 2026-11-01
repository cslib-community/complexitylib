/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.GateReplyBounds
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.NodeReply
public import Complexity.Computability.TreeEval.Ary.Packed.RawControllerQuery
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Cases
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum

/-!
# Concrete native requests for the uniform raw evaluator

Node requests return the existing paid node reply. Gate requests initialize the existing routed
gate-vector supplier on the same original input. Runtime alphabet and assignment capacity are
stored explicitly; initialization does not expand binary chunk-width metadata into an alphabet
or a vector. The existing gate-reply machine, answer and encoding serve both request kinds.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.ConcreteSupplier

open MultiTapeTM MultiTapeTM.ComputableInSpace Cslib.TreeEval.Ary.Packed

variable {k s : ℕ} {Q : Type}

/-- Input length, block width, schedule, horizon, chunk width, alphabet and paid capacity. -/
abbrev Context := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ

/-- The raw evaluator's actual request, including its runtime field/arity/count header. -/
abbrev Args := RawController.Query.RequestArgs Context

/-- Seven explicitly retained binary metadata registers. -/
@[expose] noncomputable def encContext : Context ↪ List Bool :=
  encPair encNat (encPair encNat (encPair encNat (encPair encNat
    (encPair encNat (encPair encNat encNat)))))

/-- Reuse the raw evaluator's concrete request encoding. -/
@[expose] noncomputable def encArgs : Args ↪ List Bool :=
  RawController.Query.encRequestArgs encContext

/-- Pass the actual path and paid source-vector metadata to node classification. -/
@[expose] def nodeArgs : Args → NodeReply.Args :=
  fun ((_, _, σ, q, m, _, limit), (_, _, r), (_, path, _, _)) =>
    ((σ, q, path), (limit, m, r))

/-- Pass the actual stored point to routed interpolation, retaining the supplied alphabet. -/
@[expose] def gateArgs : Args → QueryReplay.GateReply.Args :=
  fun ((N, b, σ, q, m, alphabet, limit), (p, d, r), (_, path, point, chunk)) =>
    ((σ, q, path), (((N, b, σ, 0, m, chunk, r * m),
      (p, alphabet, d * r), point, limit), r))

/-- Node replies are immediate; gate requests enter the existing concrete gate supplier. -/
@[expose] def start (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    Args → QueryReplay.GateReply.State k Q := fun args =>
  let (_, _, (tag, _, _, _)) := args
  if tag = 0 then .inl (NodeReply.reply M e (nodeArgs args))
  else if tag = 1 then QueryReplay.GateReply.initial M e (gateArgs args)
  else .inl (0, [])

/-- Node argument extraction is native in actual request storage. -/
theorem nodeArgs_inSpace : ComputableInSpace nodeArgs encArgs NodeReply.encArgs
    (fun a => (encArgs a).length) := by
  have hc := fst encContext (encPair RawController.encParams RawController.encNeed)
  have hr := snd encContext (encPair RawController.encParams RawController.encNeed)
  have hp := hr.fst'
  have hn := hr.snd'
  have hσ := hc.snd'.snd'.fst'
  have hq := hc.snd'.snd'.snd'.fst'
  have hm := hc.snd'.snd'.snd'.snd'.fst'
  have hlimit := hc.snd'.snd'.snd'.snd'.snd'.snd'
  have hpath := hn.snd'.fst'
  have hcount := hp.snd'.snd'
  exact (budget_prod (budget_prod hσ (budget_prod hq hpath))
    (budget_prod hlimit (budget_prod hm hcount))).of_enc_eq fun _ => rfl

/-- Gate argument extraction performs only binary products and retains the actual point. -/
theorem gateArgs_inSpace : ComputableInSpace gateArgs encArgs QueryReplay.GateReply.encArgs
    (fun a => (encArgs a).length) := by
  have hc := fst encContext (encPair RawController.encParams RawController.encNeed)
  have hr := snd encContext (encPair RawController.encParams RawController.encNeed)
  have hp := hr.fst'
  have hn := hr.snd'
  have hN := hc.fst'
  have hb := hc.snd'.fst'
  have hσ := hc.snd'.snd'.fst'
  have hq := hc.snd'.snd'.snd'.fst'
  have hm := hc.snd'.snd'.snd'.snd'.fst'
  have halphabet := hc.snd'.snd'.snd'.snd'.snd'.fst'
  have hlimit := hc.snd'.snd'.snd'.snd'.snd'.snd'
  have hmodulus := hp.fst'
  have hd := hp.snd'.fst'
  have hcount := hp.snd'.snd'
  have hpath := hn.snd'.fst'
  have hpoint := hn.snd'.snd'.fst'
  have hchunk := hn.snd'.snd'.snd'
  have hzero := budget_const (encIn := encArgs) (encB := encNat) 0 (.refl _)
  have hcontext := budget_prod hN (budget_prod hb (budget_prod hσ (budget_prod hzero
    (budget_prod hm (budget_prod hchunk (budget_natMul hcount hm))))))
  have hparameters := budget_prod hmodulus (budget_prod halphabet (budget_natMul hd hcount))
  exact (budget_prod (budget_prod hσ (budget_prod hq hpath))
    (budget_prod (budget_prod hcontext (budget_prod hparameters (budget_prod hpoint hlimit)))
      hcount)).of_enc_eq fun _ => rfl

variable [Finite Q]

/-- Request dispatch and concrete supplier initialization use native linear local space. -/
theorem start_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (start M e) encArgs QueryReplay.GateReply.encState
      (fun a => (encArgs a).length) := by
  have hr := snd encContext (encPair RawController.encParams RawController.encNeed)
  have htag := hr.snd'.fst'
  have hnode := budget_natIsZero htag
  have hgate := budget_natEq htag (budget_const (encB := encNat) 1 (.refl _))
  have hreply := budget_comp_linear (NodeReply.reply_inSpace M e) nodeArgs_inSpace
  have hleft := budget_comp_linear
    (of_inO (ComputableInO.inl RawController.encReply
      (QueryReplay.GateVector.encState (k := k) (Q := Q)))) hreply
  have hright := budget_comp_linear (QueryReplay.GateReply.initial_inSpace M e) gateArgs_inSpace
  have hempty := budget_const (encIn := encArgs)
    (encB := QueryReplay.GateReply.encState (k := k) (Q := Q))
    (.inl (0, [])) (.refl _)
  refine (budget_ite hnode hleft (budget_ite hgate hright hempty)).of_enc_eq ?_
  rintro ⟨context, params, tag, path, point, chunk⟩
  by_cases hz : tag = 0 <;> by_cases ho : tag = 1 <;> simp [start, hz, ho] <;> rfl

end Turing.MultiTapePTM.BlockComputation.ConcreteSupplier
