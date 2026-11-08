/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORNativeDualProbe
public import Complexity.Computability.WordRAM.RegisterParameters
import all Complexity.Computability.WordRAM.Structured

/-!
# Register-selected native bucket scanning

The two bucket addresses are read from preserved registers, so native projected
queries can feed the already certified forward-retention/inverse-preparation scan.
`selectedProbe_exec` reuses its exact execution and original-chain witness proof;
parameter substitution adds no instructions and preserves the complete final data.
This component does not itself compute the queries or certify a full class search.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Quarter

open Cslib.WordRAM

/-- Native-computed address of the retained first-quarter bucket. -/
abbrev selectedForward : Fin 32 := 29
/-- Native-computed address of the scanned inverse fourth-quarter bucket. -/
abbrev selectedBackward : Fin 32 := 30

/-- Retention setup reads its actual selected bucket address from a register. -/
@[expose] def selectedRetainSetup (b n v D : ℕ) : Code .standard 32 :=
  ram[ base ← #b; count ← #n; operators ← #v; Dictionary.table ← #D;
    Dictionary.top ← #0; one ← #1; zero ← #0; address ← selectedForward; link ← *address ]

/-- The forward preparation/retention consumes the register-selected bucket. -/
@[expose] def selectedPrepareRetain (b n v D : ℕ) : Code .standard 32 :=
  .seq prepare (.seq (selectedRetainSetup b n v D) retainLoop)

/-- Separate inverse preparation follows register-selected forward retention. -/
@[expose] def selectedDualPrepare (c n v D b₄ n₄ M t h₄ f₄ N : ℕ) : Code .standard 32 :=
  .seq (selectedPrepareRetain c n v D)
    (.seq (inverseSetup b₄ n₄ M t h₄ f₄ N) Backward.prepare)

/-- The probe head is also loaded from its native-computed address. -/
@[expose] def selectedProbeSetup (b n M v D : ℕ) : Code .standard 32 :=
  ram[ base ← #b; count ← #n; modulus ← #M; operators ← #v;
    Dictionary.table ← #D; one ← #1; zero ← #0; operand ← #0;
    address ← selectedBackward; link ← *address ]

/-- A complete bounded construction/scan with register-selected bucket addresses. -/
@[expose] def selectedProbe (c n v D b₄ n₄ M t h₄ f₄ N b₃ n₃ v₃ : ℕ) : Code .standard 32 :=
  .seq (selectedDualPrepare c n v D b₄ n₄ M t h₄ f₄ N)
    (.seq (selectedProbeSetup b₃ n₃ M v₃ D) probeScan)

private def halfway (c n v D b₄ n₄ M t h₄ f₄ N b₃ n₃ v₃ k : ℕ) : Code .standard 32 :=
  .seq (selectedDualPrepare c n v D b₄ n₄ M t h₄ f₄ N)
    (.seq (probeSetup b₃ n₃ M v₃ D h₄ k) probeScan)

/-- The existing immediate-address run is exactly the selected-address run when
both preserved registers contain those addresses. This is an execution-reuse
lemma, not an original-input endpoint; its clients must compute the registers. -/
theorem selectedProbe_exec {W T c n v D h g b₄ n₄ M t h₄ f₄ N b₃ n₃ v₃ k : ℕ}
    {x y : Data 32} (hf : x.regs selectedForward = h + g)
    (hb : x.regs selectedBackward = h₄ + k)
    (he : ExecWithin W (dualProbe c n v D h g b₄ n₄ M t h₄ f₄ N b₃ n₃ v₃ k) x y T) :
    ExecWithin W (selectedProbe c n v D b₄ n₄ M t h₄ f₄ N b₃ n₃ v₃) x y T := by
  have forward : Code.RegisterParameter selectedForward (h + g)
      (dualProbe c n v D h g b₄ n₄ M t h₄ f₄ N b₃ n₃ v₃ k)
      (halfway c n v D b₄ n₄ M t h₄ f₄ N b₃ n₃ v₃ k) := by
    unfold dualProbe dualPrepare Forward.prepareRetain Forward.retainSetup halfway
      selectedDualPrepare selectedPrepareRetain selectedRetainSetup
    repeat' first
      | exact .same _ (by decide)
      | apply Code.RegisterParameter.same
        simp only [Code.Preserves, Op.dest, ne_eq, Option.some.injEq]
        decide
      | apply Code.RegisterParameter.copy; decide
      | apply Code.RegisterParameter.seq
  have backward : Code.RegisterParameter selectedBackward (h₄ + k)
      (halfway c n v D b₄ n₄ M t h₄ f₄ N b₃ n₃ v₃ k)
      (selectedProbe c n v D b₄ n₄ M t h₄ f₄ N b₃ n₃ v₃) := by
    unfold halfway selectedProbe probeSetup selectedProbeSetup
    repeat' first
      | exact .same _ (by decide)
      | apply Code.RegisterParameter.same
        simp only [Code.Preserves, Op.dest, ne_eq, Option.some.injEq]
        decide
      | apply Code.RegisterParameter.copy; decide
      | apply Code.RegisterParameter.seq
  exact backward.execWithin hb (forward.execWithin hf he)

end Cslib.Cryptanalysis.AddXNOR.Native.Quarter
