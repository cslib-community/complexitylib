/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Complexity.Classes.TFNP.Subclasses.PotentialLineNormalization
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Tests for promised-source normalization of `EOPL` and `SOPL`

Kernel-checked strict-`module` tests (without `import all`, `sorry`, `axiom`, or `native_decide`)
exercising
`CslibFrontier.Computability.Complexity.Classes.TFNP.Subclasses.PotentialLineNormalization`:

1. **Promised line-source instance with nonzero source potential (`V (0 ^ 2) = 5`):** two lines
   `00 → 01` and `10 → 11` on `{0, 1} ^ 2` where `LineSourcePromise` holds (`P (00) = 00 ≠ S (00)`)
   but `PromisedPotentialLine` fails because `V (00) = 5 ≠ 0`; after `(2 + 1) = 3`-bit
   normalization, `PromisedPotentialLine` holds (`V' (000) = 0`), `000 → 100 → 101` and `110 → 111`
   form the active lines, `endOfPotentialLinePromisedRel` accepts `{101, 110, 111}`, and
   `sinkOfPotentialLinePromisedRel` accepts `{101, 111}` while rejecting proper source `110`.
2. **Failed source-promise instances:**
   * **Fixpoint at `0 ^ 2` (`S = id, P = id`):** `endOfPotentialLinePromisedRel` has **no**
     solutions on `{0, 1} ^ 2`, whereas the normalized `3`-bit family satisfies
     `PromisedPotentialLine`, has unique pure `(R1)`/`(R2)` solution `100`, and maps `100` via
     `normalizedViolationBack` to `00` (solving raw `endOfPotentialLineViolationRel` and
     `sinkOfPotentialLineViolationRel`).
   * **Broken source predecessor (`P (00) = 01 ≠ 00`) with active outgoing edge `00 → 01`:**
     `100` is an internal vertex `000 → 100 → 101` of the normalized `3`-bit graph (not a solution),
     `101` is the normalized sink solution, and `normalizedViolationBack` still sends `101` to `00`
     because `LineSourcePromise` fails on the raw instance.
3. **Zero-width (`n = 0`) edge case:** `{0, 1} ^ 0 = {[]}` necessarily violates `LineSourcePromise`
   (`S [] = []`), while its `1`-bit normalization on `{[false], [true]}` satisfies
   `PromisedPotentialLine` (`V' [false] = 0 < V [] + 1 = V' [true]`), has unique solution `[true]`,
   and maps `[true]` back to `[]`.
4. **Equal-potential (`V (S u) = V u`) edge cases:**
   * Along `00 → 01 → 11` with `V (00) = 1 < V (01) = 4 = V (11)`, pruning stops at `01`, the
     normalized `3`-bit instance has unique solution `101` (isolating `111`), and
     `normalizedViolationBack` returns `01` (an `(R2)` witness of the raw instance).
   * Along `00 → 01 → 10 → 11` with `V (00) = 1 < V (01) = 5 = V (10) < V (11) = 8`, `110` is a
     proper-source `(R1)` solution of the normalized `EOPL` instance (not `SOPL`), and
     `normalizedViolationBack` steps back from `110` to `P (10) = 01`, recovering the `(R2)`
     equal-potential violation of the raw instance.
5. **Uniform polynomial-time `#4391` `enc_structure` client:** exercises
   `computableInPolyTime_normalizedPotential*`, `exists_normalizedPotentialBound`, bidirectional
   `SearchReducible` equivalences, and `mem_EOPL_iff_promised_bounded` /
   `mem_SOPL_iff_promised_bounded`.
-/

public section

namespace CslibFrontierTests.TFNPPotentialLineNormalization

open Cslib Cslib.BitString Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime

/-! ### 1. Promised `LineSourcePromise` with nonzero source potential `V (00) = 5` -/

private def n2 : Unit → ℕ := fun _ => 2

private def S2 (p : Unit × List Bool) : List Bool :=
  if p.2 = [false, false] then [false, true]
  else if p.2 = [true, false] then [true, true] else p.2

private def P2 (p : Unit × List Bool) : List Bool :=
  if p.2 = [false, true] then [false, false]
  else if p.2 = [true, true] then [true, false] else p.2

private def V2Shift (p : Unit × List Bool) : ℕ :=
  if p.2 = [false, false] then 5 else if p.2 = [false, true] then 7
  else if p.2 = [true, false] then 10 else 12

/-- Raw family satisfies `LineSourcePromise`, fails `PromisedPotentialLine` (`V (00) = 5`), while
its `3`-bit normalization satisfies `PromisedPotentialLine`. -/
example : LineSourcePromise n2 P2 S2 () ∧ ¬PromisedPotentialLine n2 P2 S2 V2Shift () ∧
    PromisedPotentialLine (normalizedPotentialWidth n2)
      (normalizedPotentialPred n2 P2 S2 V2Shift) (normalizedPotentialSucc n2 P2 S2 V2Shift)
      (normalizedPotential V2Shift) () :=
  ⟨by decide, by decide, promisedPotentialLine_normalized n2 P2 S2 V2Shift ()⟩

/-- Normalized potentials shift `{true} × {0, 1} ^ 2` by `+ 1` and zero `{false} × {0, 1} ^ 2`. -/
example : normalizedPotential V2Shift ((), [false, false, false]) = 0 ∧
    normalizedPotential V2Shift ((), [false, true, false]) = 0 ∧
    normalizedPotential V2Shift ((), [true, false, false]) = 6 ∧
    normalizedPotential V2Shift ((), [true, false, true]) = 8 ∧
    normalizedPotential V2Shift ((), [true, true, false]) = 11 ∧
    normalizedPotential V2Shift ((), [true, true, true]) = 13 := by
  decide

/-- Pure `(R1)/(R2)` solutions of the normalized `3`-bit instance: `101` and `111` solve both `EOPL`
and `SOPL`, `110` solves `EOPL` only, and `000`, `100` (now internal on `000 → 100 → 101`), and
`010` solve neither. -/
example :
    endOfPotentialLinePromisedRel (normalizedPotentialWidth n2)
      (normalizedPotentialPred n2 P2 S2 V2Shift) (normalizedPotentialSucc n2 P2 S2 V2Shift)
      (normalizedPotential V2Shift) () [true, false, true] ∧
    sinkOfPotentialLinePromisedRel (normalizedPotentialWidth n2)
      (normalizedPotentialPred n2 P2 S2 V2Shift) (normalizedPotentialSucc n2 P2 S2 V2Shift)
      (normalizedPotential V2Shift) () [true, false, true] ∧
    endOfPotentialLinePromisedRel (normalizedPotentialWidth n2)
      (normalizedPotentialPred n2 P2 S2 V2Shift) (normalizedPotentialSucc n2 P2 S2 V2Shift)
      (normalizedPotential V2Shift) () [true, true, true] ∧
    sinkOfPotentialLinePromisedRel (normalizedPotentialWidth n2)
      (normalizedPotentialPred n2 P2 S2 V2Shift) (normalizedPotentialSucc n2 P2 S2 V2Shift)
      (normalizedPotential V2Shift) () [true, true, true] ∧
    endOfPotentialLinePromisedRel (normalizedPotentialWidth n2)
      (normalizedPotentialPred n2 P2 S2 V2Shift) (normalizedPotentialSucc n2 P2 S2 V2Shift)
      (normalizedPotential V2Shift) () [true, true, false] ∧
    ¬sinkOfPotentialLinePromisedRel (normalizedPotentialWidth n2)
      (normalizedPotentialPred n2 P2 S2 V2Shift) (normalizedPotentialSucc n2 P2 S2 V2Shift)
      (normalizedPotential V2Shift) () [true, true, false] ∧
    ¬endOfPotentialLinePromisedRel (normalizedPotentialWidth n2)
      (normalizedPotentialPred n2 P2 S2 V2Shift) (normalizedPotentialSucc n2 P2 S2 V2Shift)
      (normalizedPotential V2Shift) () [false, false, false] ∧
    ¬endOfPotentialLinePromisedRel (normalizedPotentialWidth n2)
      (normalizedPotentialPred n2 P2 S2 V2Shift) (normalizedPotentialSucc n2 P2 S2 V2Shift)
      (normalizedPotential V2Shift) () [true, false, false] ∧
    ¬endOfPotentialLinePromisedRel (normalizedPotentialWidth n2)
      (normalizedPotentialPred n2 P2 S2 V2Shift) (normalizedPotentialSucc n2 P2 S2 V2Shift)
      (normalizedPotential V2Shift) () [false, true, false] := by
  decide

/-! ### 2. Failed source-promise instances -/

/-- When `P = id` and `S = id`, `LineSourcePromise` fails and unnormalized
`endOfPotentialLinePromisedRel` has **no** solutions at all on `{0, 1} ^ 2`. -/
example : ¬LineSourcePromise n2 Prod.snd Prod.snd () ∧
    ∀ b₁ b₂ : Bool,
      ¬endOfPotentialLinePromisedRel n2 Prod.snd Prod.snd V2Shift () [b₁, b₂] := by
  decide

/-- After normalization of `(n2, id, id, V2Shift)`, `PromisedPotentialLine` holds, `[true, false,
false]` (`100`) is a pure `(R1)`/`(R2)` solution for both `EOPL` and `SOPL`, and
`normalizedViolationBack` maps it back to `[false, false]` (`00`), solving raw
`endOfPotentialLineViolationRel` and `sinkOfPotentialLineViolationRel`. -/
example :
    PromisedPotentialLine (normalizedPotentialWidth n2)
      (normalizedPotentialPred n2 Prod.snd Prod.snd V2Shift)
      (normalizedPotentialSucc n2 Prod.snd Prod.snd V2Shift)
      (normalizedPotential V2Shift) () ∧
    sinkOfPotentialLinePromisedRel (normalizedPotentialWidth n2)
      (normalizedPotentialPred n2 Prod.snd Prod.snd V2Shift)
      (normalizedPotentialSucc n2 Prod.snd Prod.snd V2Shift)
      (normalizedPotential V2Shift) () [true, false, false] ∧
    normalizedViolationBack n2 Prod.snd Prod.snd V2Shift ((), [true, false, false]) =
      [false, false] ∧
    sinkOfPotentialLineViolationRel n2 Prod.snd Prod.snd V2Shift () [false, false] := by
  unfold sinkOfPotentialLineViolationRel
  decide

/-- Failed source promise via `P (00) = 01 ≠ 00` while `00 → 01` still has `hasPotentialOut = true`:
`100` is internal (`000 → 100 → 101`), `101` is the normalized sink solution, and
`normalizedViolationBack` sends `101` back to `00`. -/
private def P2BadZero (p : Unit × List Bool) : List Bool :=
  if p.2 = [false, false] then [false, true] else P2 p

example : ¬LineSourcePromise n2 P2BadZero S2 () ∧
    hasPotentialOut n2 P2BadZero S2 V2Shift () [false, false] = true ∧
    ¬endOfPotentialLinePromisedRel (normalizedPotentialWidth n2)
      (normalizedPotentialPred n2 P2BadZero S2 V2Shift)
      (normalizedPotentialSucc n2 P2BadZero S2 V2Shift)
      (normalizedPotential V2Shift) () [true, false, false] ∧
    sinkOfPotentialLinePromisedRel (normalizedPotentialWidth n2)
      (normalizedPotentialPred n2 P2BadZero S2 V2Shift)
      (normalizedPotentialSucc n2 P2BadZero S2 V2Shift)
      (normalizedPotential V2Shift) () [true, false, true] ∧
    normalizedViolationBack n2 P2BadZero S2 V2Shift ((), [true, false, true]) = [false, false] ∧
    sinkOfPotentialLineViolationRel n2 P2BadZero S2 V2Shift () [false, false] := by
  unfold sinkOfPotentialLineViolationRel
  decide

/-! ### 3. Zero-width (`n = 0`) edge case -/

private def n0 : Unit → ℕ := fun _ => 0
private def V0 : Unit × List Bool → ℕ := fun _ => 9

/-- At width `n = 0`, `{0, 1} ^ 0 = {[]}` always violates `LineSourcePromise`, whereas the `1`-bit
normalization on `{[false], [true]}` satisfies `PromisedPotentialLine`, has unique pure solution
`[true]` (with `V' [false] = 0 < 10 = V' [true]`), and maps `[true]` back to `[]`. -/
example : ¬LineSourcePromise n0 Prod.snd Prod.snd () ∧
    PromisedPotentialLine (normalizedPotentialWidth n0)
      (normalizedPotentialPred n0 Prod.snd Prod.snd V0)
      (normalizedPotentialSucc n0 Prod.snd Prod.snd V0)
      (normalizedPotential V0) () ∧
    normalizedPotential V0 ((), [false]) = 0 ∧
    normalizedPotential V0 ((), [true]) = 10 ∧
    sinkOfPotentialLinePromisedRel (normalizedPotentialWidth n0)
      (normalizedPotentialPred n0 Prod.snd Prod.snd V0)
      (normalizedPotentialSucc n0 Prod.snd Prod.snd V0)
      (normalizedPotential V0) () [true] ∧
    ¬endOfPotentialLinePromisedRel (normalizedPotentialWidth n0)
      (normalizedPotentialPred n0 Prod.snd Prod.snd V0)
      (normalizedPotentialSucc n0 Prod.snd Prod.snd V0)
      (normalizedPotential V0) () [false] ∧
    normalizedViolationBack n0 Prod.snd Prod.snd V0 ((), [true]) = [] ∧
    sinkOfPotentialLineViolationRel n0 Prod.snd Prod.snd V0 () [] := by
  unfold sinkOfPotentialLineViolationRel
  decide

/-! ### 4. Equal-potential (`V (S u) = V u`) edge cases -/

/-- Path `00 → 01 → 11` with `V (00) = 1 < V (01) = 4 = V (11)`: the equal-potential step
`01 → 11` is pruned, so `101` is the unique normalized promised solution (`111` is isolated), and
`normalizedViolationBack` returns `01`, an `(R2)` violation of the raw instance. -/
private def SChain (p : Unit × List Bool) : List Bool :=
  if p.2 = [false, false] then [false, true]
  else if p.2 = [false, true] then [true, true] else p.2

private def PChain (p : Unit × List Bool) : List Bool :=
  if p.2 = [false, true] then [false, false]
  else if p.2 = [true, true] then [false, true] else p.2

private def VEqSink (p : Unit × List Bool) : ℕ :=
  if p.2 = [false, false] then 1 else if p.2 = [false, true] then 4
  else if p.2 = [true, true] then 4 else 0

example : sinkOfPotentialLinePromisedRel (normalizedPotentialWidth n2)
      (normalizedPotentialPred n2 PChain SChain VEqSink)
      (normalizedPotentialSucc n2 PChain SChain VEqSink)
      (normalizedPotential VEqSink) () [true, false, true] ∧
    ¬endOfPotentialLinePromisedRel (normalizedPotentialWidth n2)
      (normalizedPotentialPred n2 PChain SChain VEqSink)
      (normalizedPotentialSucc n2 PChain SChain VEqSink)
      (normalizedPotential VEqSink) () [true, true, true] ∧
    normalizedViolationBack n2 PChain SChain VEqSink ((), [true, false, true]) = [false, true] ∧
    sinkOfPotentialLineViolationRel n2 PChain SChain VEqSink () [false, true] := by
  unfold sinkOfPotentialLineViolationRel
  decide

/-- Path `00 → 01 → 10 → 11` with `V (00) = 1 < V (01) = 5 = V (10) < V (11) = 8`: pruning removes
`01 → 10`, making `10` a proper source of the pruned graph; `110` solves normalized `EOPL` (not
`SOPL`), and `normalizedViolationBack` steps back from `110` to `P (10) = 01`, recovering the raw
`(R2)` equal-potential violation at `01`. -/
private def SFull (p : Unit × List Bool) : List Bool :=
  if p.2 = [false, false] then [false, true]
  else if p.2 = [false, true] then [true, false]
  else if p.2 = [true, false] then [true, true] else p.2

private def PFull (p : Unit × List Bool) : List Bool :=
  if p.2 = [false, true] then [false, false]
  else if p.2 = [true, false] then [false, true]
  else if p.2 = [true, true] then [true, false] else p.2

private def VEqMid (p : Unit × List Bool) : ℕ :=
  if p.2 = [false, false] then 1 else if p.2 = [false, true] then 5
  else if p.2 = [true, false] then 5 else 8

example : endOfPotentialLinePromisedRel (normalizedPotentialWidth n2)
      (normalizedPotentialPred n2 PFull SFull VEqMid)
      (normalizedPotentialSucc n2 PFull SFull VEqMid)
      (normalizedPotential VEqMid) () [true, true, false] ∧
    ¬sinkOfPotentialLinePromisedRel (normalizedPotentialWidth n2)
      (normalizedPotentialPred n2 PFull SFull VEqMid)
      (normalizedPotentialSucc n2 PFull SFull VEqMid)
      (normalizedPotential VEqMid) () [true, true, false] ∧
    normalizedViolationBack n2 PFull SFull VEqMid ((), [true, true, false]) = [false, true] ∧
    endOfPotentialLineViolationRel n2 PFull SFull VEqMid () [false, true] := by
  unfold endOfPotentialLineViolationRel
  decide

/-! ### 5. Uniform polynomial-time `#4391` `enc_structure` client -/

/-- Parameterized potential-line configuration with unary vertex width and binary potential
offset. -/
structure OffsetLineConfig where
  /-- Vertex bit-width `n` in unary. -/
  width : ℕ
  /-- Additive potential offset in binary (`V (0 ^ n) = offset`). -/
  offset : ℕ

/-- Framed field-tuple encoding of `OffsetLineConfig` (`width` in unary, `offset` in binary). -/
enc_structure encOffsetLineConfig : OffsetLineConfig where
  width : encUnary, offset : encNat

private def famN (c : OffsetLineConfig) : ℕ := c.width

private def famS (p : OffsetLineConfig × List Bool) : List Bool :=
  List.replicate p.1.width true

private def famP (p : OffsetLineConfig × List Bool) : List Bool :=
  zeroVertex p.1.width

private def famV (p : OffsetLineConfig × List Bool) : ℕ :=
  p.1.offset + binaryValue p.2

private theorem hfamN : ComputableInPolyTime famN encOffsetLineConfig encUnary := by
  unfold famN; fun_prop

private theorem hfamS :
    ComputableInPolyTime famS (encPair encOffsetLineConfig encBits) encBits := by
  unfold famS
  exact (bitsReplicate true).comp (hfamN.comp (fst encOffsetLineConfig encBits))

private theorem hfamP :
    ComputableInPolyTime famP (encPair encOffsetLineConfig encBits) encBits := by
  unfold famP
  exact computableInPolyTime_zeroVertex_comp (hfamN.comp (fst encOffsetLineConfig encBits))

private theorem hfamV :
    ComputableInPolyTime famV (encPair encOffsetLineConfig encBits) encNat := by
  unfold famV
  have hoff : ComputableInPolyTime (fun p : OffsetLineConfig × List Bool => p.1.offset)
      (encPair encOffsetLineConfig encBits) encNat := by fun_prop
  exact binary_add' hoff (computableInPolyTime_binaryValue_comp (snd encOffsetLineConfig encBits))

private theorem hfamP_len (c : OffsetLineConfig) (u : List Bool) (_ : u.length = famN c) :
    (famP (c, u)).length = famN c :=
  length_zeroVertex c.width

private theorem hfamS_len (c : OffsetLineConfig) (u : List Bool) (_ : u.length = famN c) :
    (famS (c, u)).length = famN c :=
  List.length_replicate

/-- Bidirectional `SearchReducible` equivalence between the raw family and its promised-source
normalization, plus raw-violation reduction across all `OffsetLineConfig` instances (including
`width = 0` where `LineSourcePromise` fails). -/
example :
    SearchReducible encOffsetLineConfig encOffsetLineConfig
      (endOfPotentialLineRel famN famP famS famV)
      (endOfPotentialLinePromisedRel (normalizedPotentialWidth famN)
        (normalizedPotentialPred famN famP famS famV)
        (normalizedPotentialSucc famN famP famS famV)
        (normalizedPotential famV)) ∧
    SearchReducible encOffsetLineConfig encOffsetLineConfig
      (endOfPotentialLinePromisedRel (normalizedPotentialWidth famN)
        (normalizedPotentialPred famN famP famS famV)
        (normalizedPotentialSucc famN famP famS famV)
        (normalizedPotential famV))
      (endOfPotentialLineRel famN famP famS famV) ∧
    SearchReducible encOffsetLineConfig encOffsetLineConfig
      (endOfPotentialLineViolationRel famN famP famS famV)
      (endOfPotentialLinePromisedRel (normalizedPotentialWidth famN)
        (normalizedPotentialPred famN famP famS famV)
        (normalizedPotentialSucc famN famP famS famV)
        (normalizedPotential famV)) :=
  ⟨endOfPotentialLineRel_searchReducible_promised_normalized hfamS_len,
   promised_normalized_searchReducible_endOfPotentialLineRel hfamS_len,
   endOfPotentialLineViolationRel_searchReducible_promised_normalized
     hfamN hfamP hfamS hfamV hfamP_len hfamS_len⟩

/-- Both `EOPL` and `SOPL` memberships unwrap directly to promised-source families with explicit
unary potential bit-bounds (`mem_EOPL_iff_promised_bounded`, `mem_SOPL_iff_promised_bounded`). -/
example :
    (∃ (n m : OffsetLineConfig → ℕ)
        (P S : OffsetLineConfig × List Bool → List Bool)
        (V : OffsetLineConfig × List Bool → ℕ),
      ComputableInPolyTime n encOffsetLineConfig encUnary ∧
      ComputableInPolyTime m encOffsetLineConfig encUnary ∧
      ComputableInPolyTime P (encPair encOffsetLineConfig encBits) encBits ∧
      ComputableInPolyTime S (encPair encOffsetLineConfig encBits) encBits ∧
      ComputableInPolyTime V (encPair encOffsetLineConfig encBits) encNat ∧
      PreservesWidth n P ∧ PreservesWidth n S ∧
      (∀ c u, u.length = n c → V (c, u) < 2 ^ m c) ∧
      (∀ c, PromisedPotentialLine n P S V c) ∧
      SearchReducible encOffsetLineConfig encOffsetLineConfig
        (endOfPotentialLineRel famN famP famS famV)
        (endOfPotentialLinePromisedRel n P S V)) ∧
    (∃ (n m : OffsetLineConfig → ℕ)
        (P S : OffsetLineConfig × List Bool → List Bool)
        (V : OffsetLineConfig × List Bool → ℕ),
      ComputableInPolyTime n encOffsetLineConfig encUnary ∧
      ComputableInPolyTime m encOffsetLineConfig encUnary ∧
      ComputableInPolyTime P (encPair encOffsetLineConfig encBits) encBits ∧
      ComputableInPolyTime S (encPair encOffsetLineConfig encBits) encBits ∧
      ComputableInPolyTime V (encPair encOffsetLineConfig encBits) encNat ∧
      PreservesWidth n P ∧ PreservesWidth n S ∧
      (∀ c u, u.length = n c → V (c, u) < 2 ^ m c) ∧
      (∀ c, PromisedPotentialLine n P S V c) ∧
      SearchReducible encOffsetLineConfig encOffsetLineConfig
        (sinkOfPotentialLineRel famN famP famS famV)
        (sinkOfPotentialLinePromisedRel n P S V)) :=
  ⟨(mem_EOPL_iff_promised_bounded.mp
      (endOfPotentialLineRel_mem_EOPL hfamN hfamP hfamS hfamV hfamP_len hfamS_len)).2,
   (mem_SOPL_iff_promised_bounded.mp
      (sinkOfPotentialLineRel_mem_SOPL hfamN hfamP hfamS hfamV hfamP_len hfamS_len)).2⟩

end CslibFrontierTests.TFNPPotentialLineNormalization
