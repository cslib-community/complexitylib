/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Controller.Request
public import CslibFrontier.Computability.Probabilistic.Oracle.Parameter

/-!
# Separate resource bounds for native quantum controllers

The existing native `IsOraclePPT` certificate bounds request construction and reply access for
the whole adaptive program. Its query bound therefore bounds each operation channel separately.
These are attempted-operation counts: rejected commands still cost one attempt on their channel.
Sharper counts use the same `OracleComp.IsCostBounded` predicate with the four indicator costs.

The finite device's active-register width is an independent resource, supplied when its handler
is instantiated; the inaccessible reference width is not part of that resource. A controller's
classical machine clock does not assert a bound on a separately chosen quantum register or on
the external service's implementation. The pointer-walk client uses exactly three active qubits
and a one-bit classical loop state for every number of rounds.

## Main results

* `Cslib.Probability.IsOraclePPT.device_operation_bounds`: polynomial request-size and separate
  gate, coherent-query, measurement and service bounds from one native controller certificate.
-/

public section

namespace Cslib.Probability

open Cslib.Quantum

/-- A single native certificate bounds each operation channel and every request word. Private
coins cost zero in these budgets; their computation is still charged by the native certificate. -/
theorem IsOraclePPT.device_operation_bounds {Operation α : Type} [DecidableEq Operation]
    {output : α ↪ List Bool}
    {program : ℕ → List Bool → WordOracleComp (DeviceOperation ⊕ Operation) α}
    (h : IsOraclePPT output program) :
    ∃ c d : ℕ, ∀ n input,
      (∀ operation, OracleComp.IsCostBounded
        (Sum.elim (fun _ => 0) (DeviceRequest.operationCost operation))
        (program n input) (c * (n + input.length + 2) ^ d)) ∧
      OracleComp.IsCostBounded (Sum.elim (fun _ => 0) DeviceRequest.serviceCost)
        (program n input) (c * (n + input.length + 2) ^ d) ∧
      (program n input).QueriesSatisfy (fun request =>
        request.2.length ≤ c * (n + input.length + 2) ^ d) := by
  obtain ⟨c, d, hb⟩ := h.query_bounds
  refine ⟨c, d, fun n input => ?_⟩
  obtain ⟨hcalls, hsize⟩ := hb n input
  refine ⟨fun operation => hcalls.of_le ?_, hcalls.of_le ?_, hsize⟩
  · intro q
    cases q with
    | inl _ => exact le_rfl
    | inr request => exact DeviceRequest.operationCost_le_one operation request
  · intro q
    cases q with
    | inl _ => exact le_rfl
    | inr request => exact DeviceRequest.serviceCost_le_one request

end Cslib.Probability
