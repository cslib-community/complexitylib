/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Crypto.Primitives.Garbling.Basic
import CslibFrontier.Crypto.Primitives.Garbling.Foundations

/-!
# Tests for the abstract garbling-scheme framework

A trivial scheme on length-indexed bit strings is shown valid and well typed, an adversary with an
invalid query has advantage zero, a one-bit gate scheme with shape-only side information separates
`unitSideInfo` from `SideInfo.circ` on a valid `prv.ind` query, its inverters are verified, and the
reductions between indistinguishability and simulation security (`prv` and `obv`) are instantiated.
Importing both `CslibFrontier.Crypto.Primitives.Garbling.Basic` and
`CslibFrontier.Crypto.Primitives.Garbling.Foundations` also checks that the point-and-permute
circuit
garbling API and the abstract BHR12 framework coexist without namespace collisions.
-/

namespace CslibFrontierTests.Crypto.GarblingScheme

open Cslib Cslib.Crypto Cslib.Crypto.Garbling Cslib.Probability
open scoped NNReal

/-- The scheme on bit strings of a given length that garbles nothing: `ev` is the identity, the
garbled function and the encoding information are empty, and the decoding information records the
output length. -/
def identityScheme : Scheme ℕ :=
  ⟨id, id, id, fun _ x => x, fun _ _ _ _ => 0, fun _ n _ => ⟨[], [], List.replicate n false⟩,
    fun _ x => x, fun _ x => x, fun d y => if y.length = d.length then some y else none⟩

theorem eq_of_mem_support_identityScheme {k n : ℕ} {g : Scheme.Garbled}
    (hg : g ∈ (ProbComp.eval (identityScheme.garble k n)).support) :
    g = ⟨[], [], List.replicate n false⟩ := by
  obtain ⟨coins, -, rfl⟩ := identityScheme.mem_support_eval_garble_iff.mp hg
  rfl

theorem identityScheme_isValid : identityScheme.IsValid where
  length _ _ _ _ h _ hg _ hg' := by
    obtain ⟨hn, -, -⟩ := h; cases hn
    rw [eq_of_mem_support_identityScheme hg, eq_of_mem_support_identityScheme hg']
    exact ⟨rfl, rfl, rfl⟩
  nonDegenerate _ _ _ _ h _ _ := by obtain ⟨hn, -, -⟩ := h; cases hn; exact ⟨rfl, rfl⟩
  correct _ _ n x hx g hg := by
    have hx' : x.length = n := hx
    rw [eq_of_mem_support_identityScheme hg]
    change (if x.length = (List.replicate n false).length then some x else none) = some x
    simp [hx']

theorem identityScheme_wellTyped : identityScheme.WellTyped :=
  ⟨fun _ _ hx => hx, fun _ _ n g hg Y y hy => by
    rw [eq_of_mem_support_identityScheme hg] at hy
    change y ∈ (if Y.length = (List.replicate n false).length then some Y else none) at hy
    rw [List.length_replicate] at hy
    split_ifs at hy with h
    · exact Option.mem_some_iff.mp hy ▸ h
    · simp at hy⟩

example : identityScheme.decode [false, false] [true] = none := by decide

/-- An adversary asking for a function with one input on empty inputs. -/
def invalidAdversary : PrvIndAdversary ℕ Unit :=
  ⟨fun _ => pure (⟨⟨1, []⟩, ⟨1, []⟩⟩, ()), fun _ _ => pure true⟩

theorem prvIndAdvantage_invalidAdversary (k : ℕ) :
    prvIndAdvantage identityScheme (SideInfo.circ identityScheme) k invalidAdversary = 0 := by
  refine prvIndAdvantage_eq_zero_of_invalid _ _ _ _ fun pair st hmem => ?_
  simp only [invalidAdversary, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq] at hmem
  obtain ⟨rfl, -⟩ := hmem
  decide

/-- A scheme over `Bool` (`false` = identity gate, `true` = negation gate on one-bit inputs). -/
def gateScheme : Scheme Bool :=
  ⟨fun _ => 1, fun _ => 1, fun _ => 1, fun b x => x.map (fun bit => bit ^^ b),
    fun _ _ _ _ => 0, fun _ b _ => ⟨[b], [], [false]⟩, fun _ x => x,
    fun F x => x.map (fun bit => bit ^^ F.headD false),
    fun d y => if y.length = d.length then some y else none⟩

/-- Side information that reveals only the unit shape `(1, 1, 1)` and hides the gate bit. -/
def unitSideInfo : SideInfo Bool Unit := ⟨fun _ => (), fun _ => 1, fun _ => 1, fun _ => 1⟩

theorem unitSideInfo_compatible : unitSideInfo.Compatible gateScheme := fun _ => ⟨rfl, rfl, rfl⟩

/-- The constant inverter returning the identity gate `false`. -/
def invertUnit : Unit → Bool := fun _ => false

/-- The `ev`-inverter returning the query of the identity gate `false` on the target output `y`. -/
def evInvertUnit : Unit → List Bool → Query Bool := fun _ y => ⟨false, y⟩

theorem unitSideInfo_isInverter : unitSideInfo.IsInverter invertUnit := fun _ => rfl

theorem unitSideInfo_isEvInverter : unitSideInfo.IsEvInverter gateScheme evInvertUnit :=
  fun _ _ hx =>
    ⟨rfl, by simpa [gateScheme, evInvertUnit] using hx, by simp [gateScheme, evInvertUnit]⟩

example : prvIndValid gateScheme unitSideInfo ⟨⟨false, [true]⟩, ⟨true, [false]⟩⟩ := by decide

example :
    ¬ prvIndValid gateScheme (SideInfo.circ gateScheme) ⟨⟨false, [true]⟩, ⟨true, [false]⟩⟩ := by
  decide

example {σ : Type} (k : ℕ) (S : PrvSimulator Unit) (A : PrvIndAdversary Bool σ) :
    prvIndAdvantage gateScheme unitSideInfo k A ≤
      2 * prvSimAdvantage gateScheme unitSideInfo k S (prvIndToSim gateScheme unitSideInfo A) :=
  prvIndAdvantage_le_two_mul_prvSimAdvantage_prvIndToSim _ _ unitSideInfo_compatible k S A

example {σ : Type} (k : ℕ) (B : PrvSimAdversary Bool σ) :
    prvSimAdvantage gateScheme unitSideInfo k (prvSimFromInverter gateScheme k evInvertUnit) B ≤
      prvIndAdvantage gateScheme unitSideInfo k
        (prvSimToInd gateScheme unitSideInfo evInvertUnit B) :=
  prvSimAdvantage_prvSimFromInverter_le _ _ unitSideInfo_compatible unitSideInfo_isEvInverter k B

example {σ : Type} (k : ℕ) (S : ObvSimulator Unit) (A : ObvIndAdversary Bool σ) :
    obvIndAdvantage gateScheme unitSideInfo k A ≤
      2 * obvSimAdvantage gateScheme unitSideInfo k S (obvIndToSim gateScheme unitSideInfo A) :=
  obvIndAdvantage_le_two_mul_obvSimAdvantage_obvIndToSim _ _ unitSideInfo_compatible k S A

example {σ : Type} (k : ℕ) (B : ObvSimAdversary Bool σ) :
    obvSimAdvantage gateScheme unitSideInfo k (obvSimFromInverter gateScheme k invertUnit) B ≤
      obvIndAdvantage gateScheme unitSideInfo k
        (obvSimToInd gateScheme unitSideInfo invertUnit B) :=
  obvSimAdvantage_obvSimFromInverter_le _ _ unitSideInfo_compatible unitSideInfo_isInverter k B

/--
info: 'CslibFrontierTests.Crypto.GarblingScheme.unitSideInfo_isEvInverter' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms unitSideInfo_isEvInverter

/-- info: 'Cslib.Crypto.Garbling.SideInfo.circ_isInverter' does not depend on any axioms -/
#guard_msgs in
#print axioms SideInfo.circ_isInverter

end CslibFrontierTests.Crypto.GarblingScheme
