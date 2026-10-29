/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Probability.PMF.Uniform
import Complexity.Crypto.Protocols.SigmaProtocol.Composition
import Complexity.Crypto.Protocols.SigmaProtocol.Linear
import Complexity.Probability.PMF
import Mathlib.Algebra.Module.ZMod
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for Sigma protocols

Concrete runs over the group `ZMod 11` and over the subgroup of order `11` in `(ZMod 23)ˣ`,
written additively. Each block checks honest conversations, runs the witness extractor on two
conversations with a common commitment, and applies the simulator theorems to the instance.
The protocol definitions are noncomputable only through their distributions; verification and
extraction evaluate by `decide`.
-/

namespace ComplexityTests.Crypto.SigmaProtocol

open Cslib Cslib.Probability Cslib.Crypto.Protocols SigmaProtocol

instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- Challenges are all of `ZMod 11`. -/
abbrev ι : ZMod 11 ↪ ZMod 11 := Function.Embedding.refl _

/-! ### Schnorr in `ZMod 11`

The generator is `2`, the witness `7`, and the statement `7 • 2 = 3`. With commitment
randomness `5`, the commitment is `10`; the challenges `3` and `6` get the responses `4` and
`3`. -/

example : (7 : ZMod 11) • (2 : ZMod 11) = 3 := by decide

example : (schnorr ι (2 : ZMod 11)).Accepts 3 10 3 4 := by decide
example : (schnorr ι (2 : ZMod 11)).Accepts 3 10 6 3 := by decide
example : ¬(schnorr ι (2 : ZMod 11)).Accepts 3 10 6 4 := by decide

/-- The extractor recovers the witness `7`. -/
example : linearExtract ι (3 : ZMod 11) (10 : ZMod 11) 3 (4 : ZMod 11) 6 3 = 7 := by
  decide +kernel

/-- Special soundness certifies the extracted value without computing it. -/
example : linearExtract ι (3 : ZMod 11) (10 : ZMod 11) 3 (4 : ZMod 11) 6 3 • (2 : ZMod 11) = 3 :=
  schnorr_specialSoundness _ _ _ _ _ _ (by decide) (by decide) (by decide)

/-- The simulator, at challenge `3` for the statement `3`, can output the response `4` with the
commitment `4 • 2 - 3 • 3 = 10`, and that conversation is accepting. -/
example : ((10 : ZMod 11), (4 : ZMod 11)) ∈
    (linearSimulate (fun _ : ZMod 11 => LinearMap.toSpanSingleton (ZMod 11) (ZMod 11) 2) id ι
      3 3).support :=
  (PMF.mem_support_map_iff _ _ _).mpr ⟨4, PMF.mem_support_uniformOfFintype 4, by decide⟩

/-- At every challenge and under a uniform challenge, the simulation has the honest law for the
witness `7`. -/
example (c : ZMod 11) :
    linearSimulate (fun _ : ZMod 11 => LinearMap.toSpanSingleton (ZMod 11) (ZMod 11) 2) id ι 3 c =
      (schnorr ι (2 : ZMod 11)).transcript 7 3 c ∧
    (schnorr ι (2 : ZMod 11)).conversation 7 3 = do
      let c ← PMF.uniformOfFintype (ZMod 11)
      let tz ← linearSimulate (fun _ : ZMod 11 => LinearMap.toSpanSingleton (ZMod 11) (ZMod 11) 2)
        id ι 3 c
      return (tz.1, c, tz.2) :=
  ⟨schnorr_specialHVZK.transcript_eq 7 3 (by decide) c,
   schnorr_specialHVZK.conversation_eq (by decide)⟩

/-! ### Schnorr in the subgroup of order `11` of `(ZMod 23)ˣ`

The `11`th roots of unity form a multiplicative group of prime order `11`; `Additive` turns it
into a `ZMod 11`-module, in which `α • g` is `g ^ α`. The generator is `2`, and the statement is
`2 ^ 7 = 13`. With commitment randomness `5` the commitment is `2 ^ 5 = 9`, and the responses to
the challenges `3` and `6` are `4` and `3`, as before. -/

/-- The subgroup of `11`th roots of unity in `(ZMod 23)ˣ`. -/
abbrev Roots : Subgroup (ZMod 23)ˣ := (powMonoidHom 11 : (ZMod 23)ˣ →* (ZMod 23)ˣ).ker

/-- The roots of unity, written additively. -/
abbrev G := Additive Roots

instance : Module (ZMod 11) G := AddCommGroup.zmodModule (by decide)

/-- The root of unity `a`, as an element of `G`. -/
def root (a : ℕ) (ha : Nat.Coprime a 23 := by decide)
    (h : ZMod.unitOfCoprime a ha ∈ Roots := by decide) : G :=
  Additive.ofMul ⟨ZMod.unitOfCoprime a ha, h⟩

example : (7 : ZMod 11) • root 2 = root 13 := by decide

example : (schnorr ι (root 2)).Accepts (root 13) (root 9) 3 4 := by decide
example : (schnorr ι (root 2)).Accepts (root 13) (root 9) 6 3 := by decide

/-- The extractor recovers the discrete logarithm `7` of `13` to the base `2`. -/
example : linearExtract ι (root 13) (root 9) 3 (4 : ZMod 11) 6 3 = 7 := by decide +kernel

example (c : ZMod 11) :
    linearExtract ι (root 13) (root 9) 3 (4 : ZMod 11) 6 3 • root 2 = root 13 ∧
    linearSimulate (fun _ : G => LinearMap.toSpanSingleton (ZMod 11) G (root 2)) id ι (root 13)
      c = (schnorr ι (root 2)).transcript 7 (root 13) c :=
  ⟨schnorr_specialSoundness _ _ _ _ _ _ (by decide) (by decide) (by decide),
   schnorr_specialHVZK.transcript_eq 7 _ (by decide) c⟩

/-! ### Okamoto and Chaum–Pedersen in `ZMod 11`

Okamoto: `3 • 2 + 4 • 5 = 4`; randomness `(1, 2)` gives the commitment `1`, and the challenges
`3` and `5` get `(10, 3)` and `(5, 0)`. Chaum–Pedersen: `(3, 8, 1)` is a Diffie–Hellman triple
for the base `2` with witness `4`; randomness `6` gives the commitment `(1, 7)`, and the
challenges `2` and `7` get `3` and `1`. -/

example : (okamoto ι (2 : ZMod 11) 5).Accepts 4 1 3 (10, 3) := by decide
example : (okamoto ι (2 : ZMod 11) 5).Accepts 4 1 5 (5, 0) := by decide
example : linearExtract ι (4 : ZMod 11) (1 : ZMod 11) 3 ((10, 3) : ZMod 11 × ZMod 11) 5 (5, 0) =
    (3, 4) := by
  decide +kernel

example : (chaumPedersen ι (2 : ZMod 11)).Accepts (3, 8, 1) (1, 7) 2 3 := by decide
example : (chaumPedersen ι (2 : ZMod 11)).Accepts (3, 8, 1) (1, 7) 7 1 := by decide
example : linearExtract ι ((3, 8, 1) : ZMod 11 × ZMod 11 × ZMod 11) ((1, 7) : ZMod 11 × ZMod 11)
    2 (3 : ZMod 11) 7 1 = 4 := by
  decide +kernel

/-- `(3, 8, 2)` is not a Diffie–Hellman triple, so no two of its accepting conversations share a
commitment and have distinct challenges. -/
example (t : ZMod 11 × ZMod 11) (c c' z z' : ZMod 11) (hc : c ≠ c')
    (hz : (chaumPedersen ι (2 : ZMod 11)).Accepts (3, 8, 2) t c z) :
    ¬(chaumPedersen ι (2 : ZMod 11)).Accepts (3, 8, 2) t c' z' := fun hz' => by
  obtain ⟨β, hβ⟩ := chaumPedersen_specialSoundness.exists_witness hc hz hz'
  revert β
  decide

/-! ### A system of two equations in two unknowns

The rows `(2, 5)` and `(1, 0)` with targets `(4, 3)` have the solution `(3, 4)`. Randomness
`(1, 2)` gives the commitment `(1, 1)`, and the challenge `3` gets the response `(10, 3)`. -/

example : (linearSystem ι 2 2).Accepts (![![(2 : ZMod 11), 5], ![1, 0]], ![4, 3]) ![1, 1] 3
    ![10, 3] := by
  decide

/-! ### AND and OR

AND pairs the Schnorr and Chaum–Pedersen commitments above; at the common challenge `3` the
responses are `4` and `7`. For OR, the prover knows the witness `7` of the first statement `3`
but not one for the second statement `5`. It simulates the second side at the challenge `4` with
response `6` and commitment `6 • 2 - 4 • 5 = 3`, and commits honestly with randomness `5` on the
first side. The challenges `9` and `2` split as `5 + 4` and `9 + 4`, with first-side responses
`7` and `2`. -/

example : (andProof (schnorr ι (2 : ZMod 11)) (chaumPedersen ι (2 : ZMod 11))).Accepts
    (3, (3, 8, 1)) (10, (1, 7)) 3 (4, 7) := by
  decide

example : (orProof (schnorr ι (2 : ZMod 11)) (schnorr ι (2 : ZMod 11))
    (linearSimulate (fun _ => LinearMap.toSpanSingleton (ZMod 11) (ZMod 11) 2) id ι)
    (linearSimulate (fun _ => LinearMap.toSpanSingleton (ZMod 11) (ZMod 11) 2) id ι)).Accepts
    (3, 5) (10, 3) 9 (5, 7, 6) := by
  decide

example : (orProof (schnorr ι (2 : ZMod 11)) (schnorr ι (2 : ZMod 11))
    (linearSimulate (fun _ => LinearMap.toSpanSingleton (ZMod 11) (ZMod 11) 2) id ι)
    (linearSimulate (fun _ => LinearMap.toSpanSingleton (ZMod 11) (ZMod 11) 2) id ι)).Accepts
    (3, 5) (10, 3) 2 (9, 2, 6) := by
  decide

/-- The first side's challenges differ, so the OR extractor answers with the first witness. -/
example : orExtract (linearExtract (Y := ZMod 11) ι) (linearExtract (Y := ZMod 11) ι)
    ((3, 5) : ZMod 11 × ZMod 11) ((10, 3) : ZMod 11 × ZMod 11) 9
    ((5, 7, 6) : ZMod 11 × ZMod 11 × ZMod 11) 2 (9, 2, 6) = .inl 7 := by
  decide +kernel

/-- The composite simulators and completeness properties hold for the composite relations. -/
example : (orProof (schnorr ι (2 : ZMod 11)) (schnorr ι (2 : ZMod 11))
    (linearSimulate (fun _ => LinearMap.toSpanSingleton (ZMod 11) (ZMod 11) 2) id ι)
    (linearSimulate (fun _ => LinearMap.toSpanSingleton (ZMod 11) (ZMod 11) 2) id ι)).SpecialHVZK
      (orRelation (fun α u => α • (2 : ZMod 11) = u) fun α u => α • (2 : ZMod 11) = u)
      (orSimulate
        (linearSimulate (fun _ => LinearMap.toSpanSingleton (ZMod 11) (ZMod 11) 2) id ι)
        (linearSimulate (fun _ => LinearMap.toSpanSingleton (ZMod 11) (ZMod 11) 2) id ι)) ∧
    (andProof (schnorr ι (2 : ZMod 11)) (chaumPedersen ι (2 : ZMod 11))).Complete
      fun x y => x.1 • (2 : ZMod 11) = y.1 ∧
        (x.2 • (2 : ZMod 11) = y.2.2.1 ∧ x.2 • y.2.1 = y.2.2.2) :=
  ⟨orProof_specialHVZK schnorr_specialHVZK schnorr_specialHVZK,
   andProof_complete schnorr_complete chaumPedersen_complete⟩

end ComplexityTests.Crypto.SigmaProtocol
