/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.TruncatedPolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends

/-!
# Resources of the truncation-order reduction

The native machine `Cslib.Circuits.Frontier.engineCertificate` of
`Complexity/Computability/Circuit/Frontier/TensorNetwork/TruncatedPolyTime.lean` runs the reduction
of truncation order `ℓ` to contractions over `A_P = (ℤ / 2 ^ P)[U] / (f)`: it streams over the
`N = (ℓ - 1) k + 1` digit points, calling a given certificate of the contraction over `A_P` once per
point, and then interpolates. This file bounds its time and space by those of the calls.

**The loop** (`Cslib.Circuits.Frontier.engineCertificate_le`). If at every point the call takes
time at most `R`, space at most `Q`, and outputs at most `Yb` bits, then the machine takes time at
most `(N + 1) (K (n + Yb + 1) ^ K + R)` and space at most `K (n + Yb + 1) ^ K + Q`, for a constant
`K` and the encoded length `n` of the input. The live state is the binary index, the input and the
values so far (`Cslib.Circuits.Frontier.length_run_engineStep_le`), and `N ≤ n ^ 2 + 1`
(`Cslib.Circuits.Frontier.pointCount_le`).

**The calls.** The input of a call has length at most `9 (n + 1) ^ 2`
(`Cslib.Circuits.Frontier.length_encCore_coreInput_le`): the specialized network copies the
precision, the truncation order, the modulus and the point into every vertex.

**Specialized entries** (`Cslib.Circuits.Frontier.specEntryCertificate_le`). Evaluating a
specialized entry costs the original entry plus a polynomial in the lengths of the input and of the
original entry.

## Main results

* `Cslib.Circuits.Frontier.engineCertificate_le`: time and space of the reduction.
* `Cslib.Circuits.Frontier.length_encCore_coreInput_le`: the size of a call.
* `Cslib.Circuits.Frontier.specEntryCertificate_le`: time and space of specialized entries.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Theorem D.1 (p. 53).
-/

public section

namespace Cslib.Circuits.Frontier

open Turing.MultiTapeTM Cslib.GenericRAM GaloisRingArith

variable {T : Type} {encT : T ↪ List Bool}

/-! ### Sizes -/

/-- A polynomial bound composed with a polynomially bounded size. -/
private theorem polyBounded_comp_poly {α : Type} {size u : α → ℕ} {p : ℕ → ℕ}
    (hp : Cslib.PolynomiallyBounded p) (hu : PolyBounded size u) :
    PolyBounded size fun a => p (u a) :=
  (PolyBounded.of_polynomiallyBounded id hp).comp hu

/-- A list of values, each at most `Yb` bits, is at most `(2 Yb + 1)` bits per value. -/
private theorem length_encList_le_of_forall {vals : List (List ℕ)} {Yb : ℕ}
    (h : ∀ v ∈ vals, (encList encNat v).length ≤ Yb) :
    (encList (encList encNat) vals).length ≤ vals.length * (2 * Yb + 1) := by
  rw [length_encList]
  have h' := List.sum_le_length_nsmul (vals.map fun a => 2 * (encList encNat a).length + 1)
    (2 * Yb + 1) fun x hx => by
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
      have := h v hv
      omega
  rwa [List.length_map, smul_eq_mul] at h'

/-- The length of an input of the reduction, by components. -/
theorem length_encEngine (y : List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T) :
    (encEngine encT y).length = 2 * (encList encNat y.1).length + 1 +
      (2 * y.2.1 + 1 + (2 * y.2.2.1 + 1 +
        (2 * (encNat y.2.2.2.1).length + 1 +
          (DescribedNetwork.encDescribed encT y.2.2.2.2).length))) := by
  simp [encEngine, encTrunc]

/-- **The number of points is at most `n ^ 2 + 1`** for an input of length `n`: the truncation
order is in unary, and there are at most `n` vertices. -/
theorem pointCount_le (y : List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T) :
    DescribedNetwork.pointCount y.2.2.1 y.2.2.2.2 ≤
      (encEngine encT y).length * (encEngine encT y).length + 1 := by
  have hk := DescribedNetwork.length_numEdges_vertices_le (encT := encT) y.2.2.2.2
  have hlen := length_encEngine (encT := encT) y
  have hℓ : y.2.2.1 - 1 ≤ (encEngine encT y).length := by omega
  have hv : y.2.2.2.2.vertices.length ≤ (encEngine encT y).length := by omega
  exact Nat.add_le_add_right (Nat.mul_le_mul hℓ hv) 1

/-- The length of an encoded described network, by components. -/
private theorem length_encDescribed {T' : Type} (encT' : T' ↪ List Bool)
    (G : DescribedNetwork T') :
    (DescribedNetwork.encDescribed encT' G).length =
      2 * G.numEdges + 1 + (encList (encPair (encList encNat) encT') G.vertices).length := by
  simp [DescribedNetwork.encDescribed, DescribedNetwork.equivProd]

/-- A binary-digit point has at most three bits per coordinate. -/
private theorem length_encList_digits_le (e k : ℕ) :
    (encList encNat (FastContraction.digits e k)).length ≤ 3 * e := by
  rw [length_encList]
  have h := List.sum_le_length_nsmul
    ((FastContraction.digits e k).map fun a => 2 * (encNat a).length + 1) 3 fun x hx => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hb
      have := length_encNat_le_self (if k.testBit i then 1 else 0)
      split_ifs at this ⊢ <;> omega
  simpa [FastContraction.digits, mul_comm] using h

/-- Copying the data `d` of a specialization into every vertex adds `2 |d|` bits per vertex, and
at most doubles the rest. -/
private theorem length_encList_spec_le (vs : List (List ℕ × T)) (d : ℕ × ℕ × List ℕ × List ℕ) :
    (encList (encPair (encList encNat) (encSpecDesc encT))
        (vs.map fun v => (v.1, (v.2, d)))).length ≤
      2 * (encList (encPair (encList encNat) encT) vs).length +
        vs.length * (2 * (encSpecData d).length) := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    simp only [length_encList, List.map_cons, List.map_map, List.sum_cons, List.length_cons,
      Function.comp_def, length_encPair, add_one_mul] at ih ⊢
    omega

/-- **The size of a call.** The input of the contraction at a digit point is at most
`9 (n + 1) ^ 2` bits for an input of the reduction of length `n`: the specialized network copies
the precision, the truncation order, the modulus and the point, at most `3 n` bits, into each of
at most `n` vertices. -/
theorem length_encCore_coreInput_le (y : List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T) (k : ℕ) :
    (encCore encT (coreInput y k)).length ≤ 9 * ((encEngine encT y).length + 1) ^ 2 := by
  obtain ⟨fl, P, ℓ, r, G⟩ := y
  have hlen := length_encEngine (encT := encT) (fl, P, ℓ, r, G)
  have hG := length_encDescribed encT G
  have hk := DescribedNetwork.length_numEdges_vertices_le (encT := encT) G
  have hζ := length_encList_digits_le fl.length k
  have hfl := length_le_length_encList encNat fl
  have hspec := length_encList_spec_le (encT := encT) G.vertices
    (P, ℓ, fl, FastContraction.digits fl.length k)
  set L := (encEngine encT (fl, P, ℓ, r, G)).length
  have hd : (encSpecData (P, ℓ, fl, FastContraction.digits fl.length k)).length ≤ 3 * L := by
    simp only [length_encPair, encUnary_apply, List.length_replicate] at hlen ⊢
    omega
  have hkL : G.vertices.length ≤ L := by simp only at hlen; omega
  have hmul : G.vertices.length *
      (2 * (encSpecData (P, ℓ, fl, FastContraction.digits fl.length k)).length) ≤ L * (6 * L) :=
    Nat.mul_le_mul hkL (by omega)
  simp only [coreInput, encCore, length_encPair, encUnary_apply, List.length_replicate,
    length_encDescribed, DescribedNetwork.numEdges_specNet, DescribedNetwork.vertices_specNet]
    at hspec ⊢
  simp only at hlen hG hk
  nlinarith

variable (core : ℕ × List ℕ × ℕ × DescribedNetwork (SpecDesc T) → List ℕ)

/-- The encoding of the state of the loop: the binary index, the input and the values so far. -/
local notation "encS" => encPair encNat (encPair (encEngine encT) (encList (encList encNat)))

/-- **The live state of the loop.** After `j` rounds, if each of the first `j` values is at most
`Yb` bits, the state is at most `2 |j| + 2 n + 2 + j (2 Yb + 1)` bits, for the binary length `|j|`
of `j` and the length `n` of the input. -/
theorem length_run_engineStep_le (y : List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T) {j Yb : ℕ}
    (hY : ∀ k < j, (encList encNat (core (coreInput y k))).length ≤ Yb) :
    (encS (IndexFold.run (engineStep core) j (y, []))).length ≤
      2 * (encNat j).length + 2 * (encEngine encT y).length + 2 + j * (2 * Yb + 1) := by
  rw [run_engineStep]
  have h := length_encList_le_of_forall (vals := (List.range j).map fun k => core (coreInput y k))
    (Yb := Yb) fun v hv => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
      exact hY k (List.mem_range.mp hk)
  simp only [List.length_map, List.length_range] at h
  simp only [length_encPair]
  omega

/-! ### The loop -/

/-- **Time and space of the reduction.** There is `K` such that, on an input `y` of length `n` with
`N = (ℓ - 1) k + 1` points, if at each of the indices `0, …, N` the call takes time at most `R`
and space at most `Q` and outputs at most `Yb` bits, the reduction takes time at most
`(N + 1) (K (n + Yb + 1) ^ K + R)` and space at most `K (n + Yb + 1) ^ K + Q`. (The loop charges
one more round than it runs, at the index `N`.) -/
theorem engineCertificate_le (cc : NativeCertificate core (encCore encT) (encList encNat)) :
    ∃ K : ℕ, ∀ (y : List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T) (R Q Yb : ℕ),
      (∀ k ≤ DescribedNetwork.pointCount y.2.2.1 y.2.2.2.2,
        cc.time (coreInput y k) ≤ R ∧ cc.space (coreInput y k) ≤ Q ∧
          (encList encNat (core (coreInput y k))).length ≤ Yb) →
      (engineCertificate core cc).time y ≤
          (DescribedNetwork.pointCount y.2.2.1 y.2.2.2.2 + 1) *
            (K * ((encEngine encT y).length + Yb + 1) ^ K + R) ∧
        (engineCertificate core cc).space y ≤
          K * ((encEngine encT y).length + Yb + 1) ^ K + Q := by
  -- The polynomial-time pieces.
  have hcN : ComputableInPolyTime
      (fun y : List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T =>
        DescribedNetwork.pointCount y.2.2.1 y.2.2.2.2) (encEngine encT) encNat :=
    ComputableInPolyTime.unary_to_binary.comp pointCount_polyTime
  have hcI : ComputableInPolyTime
      (fun y : List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T => (y, ([] : List (List ℕ))))
      (encEngine encT) (encPair (encEngine encT) (encList (encList encNat))) :=
    ComputableInPolyTime.id'.prod (ComputableInPolyTime.const [])
  have hcA : ComputableInPolyTime
      (fun p : ℕ × ((List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T) × List (List ℕ)) => p.2.1)
      encS (encEngine encT) :=
    (ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _)
  have hcC : ComputableInPolyTime
      (fun p : ℕ × ((List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T) × List (List ℕ)) => p.2.2)
      encS (encList (encList encNat)) :=
    (ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.snd _ _)
  have hcB := ComputableInPolyTime.snoc (encList encNat)
  obtain ⟨pN, hpN, mN, bN⟩ := exists_mono_poly_cert hcN
  obtain ⟨pI, hpI, mI, bI⟩ := exists_mono_poly_cert hcI
  obtain ⟨pA, hpA, mA, bA⟩ := exists_mono_poly_cert hcA
  obtain ⟨pC, hpC, mC, bC⟩ := exists_mono_poly_cert hcC
  obtain ⟨pB, hpB, mB, bB⟩ := exists_mono_poly_cert hcB
  obtain ⟨pD, hpD, mD, bD⟩ := exists_mono_poly_cert (coreInput_polyTime (encT := encT))
  obtain ⟨pR, hpR, mR, bR⟩ := exists_mono_poly_cert (engineRecover_polyTime (encT := encT))
  -- The overhead, as a polynomial in `X = n + Yb`.
  let Sh : ℕ → ℕ := fun X => 7 * (X + 1) ^ 3
  let U : ℕ → ℕ := fun X => pN X + X + pI X + 3 * Sh X + 3 * ((X + 1) ^ 2 + 1) ^ 2 +
    pA (Sh X) + pC (Sh X) + pD (Sh X) + pB (2 * Sh X + 1 + X) + pR (Sh X)
  have hSh : PolyBounded id Sh :=
    (PolyBounded.const 7).mul ((PolyBounded.self.add (PolyBounded.const 1)).pow 3)
  have hU : PolyBounded id U :=
    (((((((((polyBounded_comp_poly hpN PolyBounded.self).add PolyBounded.self).add
      (polyBounded_comp_poly hpI PolyBounded.self)).add ((PolyBounded.const 3).mul hSh)).add
      ((PolyBounded.const 3).mul ((((PolyBounded.self.add (PolyBounded.const 1)).pow 2).add
        (PolyBounded.const 1)).pow 2))).add (polyBounded_comp_poly hpA hSh)).add
      (polyBounded_comp_poly hpC hSh)).add (polyBounded_comp_poly hpD hSh)).add
      (polyBounded_comp_poly hpB ((((PolyBounded.const 2).mul hSh).add (PolyBounded.const 1)).add
        PolyBounded.self))).add (polyBounded_comp_poly hpR hSh)
  obtain ⟨a, d, hUad⟩ := hU.exists_le
  refine ⟨a + d, fun y R Q Yb hcore => ?_⟩
  set L := (encEngine encT y).length with hL
  set N := DescribedNetwork.pointCount y.2.2.1 y.2.2.2.2 with hN
  set X := L + Yb with hX
  have hUX : U X ≤ (a + d) * (X + 1) ^ (a + d) := by
    have h1 := hUad X
    have h2 : (X + 1) ^ d ≤ (X + 1) ^ (a + d) := Nat.pow_le_pow_right (by omega) (by omega)
    simp only [id] at h1
    calc U X ≤ a * (X + 1) ^ d := h1
      _ ≤ (a + d) * (X + 1) ^ (a + d) := Nat.mul_le_mul (by omega) h2
  -- Sizes of the states.
  have hNL : N ≤ L * L + 1 := pointCount_le y
  have hNX : N ≤ (X + 1) ^ 2 := by
    have : L * L ≤ X * X := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  let S := 2 * N + 2 * L + 2 + N * (2 * Yb + 1)
  have hSSh : S ≤ Sh X := by
    have h1 : N * (2 * Yb + 1) ≤ (X + 1) ^ 2 * (2 * X + 2) := Nat.mul_le_mul hNX (by omega)
    have h2 : (X + 1) ^ 2 ≤ (X + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : X + 1 ≤ (X + 1) ^ 3 := by
      calc X + 1 = (X + 1) ^ 1 := (pow_one _).symm
        _ ≤ (X + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have h4 : (X + 1) ^ 2 * (2 * X + 2) = 2 * (X + 1) ^ 3 := by ring
    simp only [Sh, S]
    omega
  have hstate (j : ℕ) (hj : j ≤ N) :
      (encS (IndexFold.run (engineStep core) j (y, []))).length ≤ S := by
    have h := length_run_engineStep_le (encT := encT) core y (j := j) (Yb := Yb)
      fun k hk => (hcore k (by omega)).2.2
    have hj' : (encNat j).length ≤ N := (length_encNat_mono hj).trans (length_encNat_le_self N)
    have hjN : j * (2 * Yb + 1) ≤ N * (2 * Yb + 1) := Nat.mul_le_mul_right _ hj
    omega
  -- The values so far, then the snoc input, are bounded by the state.
  have hsnoc (j : ℕ) (hj : j ≤ N) :
      (encPair (encList (encList encNat)) (encList encNat)
        ((IndexFold.run (engineStep core) j (y, [])).2.2,
          core (coreInput (IndexFold.run (engineStep core) j (y, [])).2.1
            (IndexFold.run (engineStep core) j (y, [])).1))).length ≤ 2 * S + 1 + Yb := by
    have hs := hstate j hj
    have hY := (hcore j hj).2.2
    rw [run_engineStep] at hs ⊢
    simp only [length_encPair] at hs ⊢
    omega
  have hround_time (j : ℕ) (hj : j ≤ N) :
      (IndexFold.roundCertificate (engineStepCertificate core cc)).time
          (IndexFold.run (engineStep core) j (y, [])) ≤
        S + (N + 1) ^ 2 + pA (Sh X) + pC (Sh X) + pD (Sh X) + pB (2 * Sh X + 1 + X) + R := by
    have hs := hstate j hj
    have hsn := hsnoc j hj
    simp only [IndexFold.roundCertificate, engineStepCertificate, NativeCertificate.comp_time,
      NativeCertificate.prod_time]
    have h1 := (bA (IndexFold.run (engineStep core) j (y, []))).1.trans (mA (hs.trans hSSh))
    have h2 := (bC (IndexFold.run (engineStep core) j (y, []))).1.trans (mC (hs.trans hSSh))
    have h3 := (bD (IndexFold.run (engineStep core) j (y, []))).1.trans (mD (hs.trans hSSh))
    have h4 := (bB _).1.trans (mB (hsn.trans (by omega : 2 * S + 1 + Yb ≤ 2 * Sh X + 1 + X)))
    have hidx : (encNat (IndexFold.run (engineStep core) j (y, [])).1).length + 1 ≤ N + 1 := by
      rw [IndexFold.run_index]
      exact Nat.add_le_add_right ((length_encNat_mono hj).trans (length_encNat_le_self N)) 1
    have hsq := Nat.pow_le_pow_left hidx 2
    have hR := (hcore j hj).1
    rw [run_engineStep] at h1 h2 h3 h4 hs hsq ⊢
    simp only [Function.comp_apply] at h1 h2 h3 h4 hs hsq ⊢
    omega
  have hround_space (j : ℕ) (hj : j ≤ N) :
      (IndexFold.roundCertificate (engineStepCertificate core cc)).space
          (IndexFold.run (engineStep core) j (y, [])) ≤
        S + (N + 1) + pA (Sh X) + pC (Sh X) + pD (Sh X) + pB (2 * Sh X + 1 + X) + Q := by
    have hs := hstate j hj
    have hsn := hsnoc j hj
    simp only [IndexFold.roundCertificate, engineStepCertificate, NativeCertificate.comp_space,
      NativeCertificate.prod_space]
    have h1 := (bA (IndexFold.run (engineStep core) j (y, []))).2.trans (mA (hs.trans hSSh))
    have h2 := (bC (IndexFold.run (engineStep core) j (y, []))).2.trans (mC (hs.trans hSSh))
    have h3 := (bD (IndexFold.run (engineStep core) j (y, []))).2.trans (mD (hs.trans hSSh))
    have h4 := (bB _).2.trans (mB (hsn.trans (by omega : 2 * S + 1 + Yb ≤ 2 * Sh X + 1 + X)))
    have hidx : (encNat (IndexFold.run (engineStep core) j (y, [])).1).length ≤ N := by
      rw [IndexFold.run_index]
      exact (length_encNat_mono hj).trans (length_encNat_le_self N)
    have hQ := (hcore j hj).2.1
    rw [run_engineStep] at h1 h2 h3 h4 hs hidx ⊢
    simp only [Function.comp_apply] at h1 h2 h3 h4 hs hidx ⊢
    omega
  -- The trajectory maxima.
  have hmaxT : NativeCertificate.maxRoundTime
      (IndexFold.roundCertificate (engineStepCertificate core cc)) N (0, y, []) ≤
        S + (N + 1) ^ 2 + pA (Sh X) + pC (Sh X) + pD (Sh X) + pB (2 * Sh X + 1 + X) + R :=
    NativeCertificate.maxRoundTime_le _ _ _ fun j hj => hround_time j hj
  have hmaxS : NativeCertificate.maxRoundSpace
      (IndexFold.roundCertificate (engineStepCertificate core cc)) N (0, y, []) ≤
        S + (N + 1) + pA (Sh X) + pC (Sh X) + pD (Sh X) + pB (2 * Sh X + 1 + X) + Q :=
    NativeCertificate.maxRoundSpace_le _ _ _ fun j hj => hround_space j hj
  have hmaxL : NativeCertificate.maxStateLength encS (IndexFold.step (engineStep core)) N
      (0, y, []) ≤ S :=
    NativeCertificate.maxStateLength_le _ _ _ _ fun j hj => hstate j hj
  -- The pieces outside the loop.
  have hLX : L ≤ X := by omega
  have hNt := (bN y).1.trans (mN hLX)
  have hNs := (bN y).2.trans (mN hLX)
  have hIt := (bI y).1.trans (mI hLX)
  have hIs := (bI y).2.trans (mI hLX)
  have hRt := (bR (IndexFold.run (engineStep core) N (y, []))).1.trans
    (mR ((hstate N le_rfl).trans hSSh))
  have hRs := (bR (IndexFold.run (engineStep core) N (y, []))).2.trans
    (mR ((hstate N le_rfl).trans hSSh))
  have hNlen : (encNat N).length ≤ N := length_encNat_le_self N
  have hsq : ((encNat N).length + 1) ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hNsq : (N + 1) ^ 2 ≤ ((X + 1) ^ 2 + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hN1 : N ≤ (N + 1) ^ 2 := by nlinarith
  refine ⟨?_, ?_⟩
  · rw [engineCertificate, NativeCertificate.congr_time, NativeCertificate.comp_time,
      IndexFold.certificate, NativeCertificate.iterate_time]
    simp only [NativeCertificate.prod_time, NativeCertificate.const_time, Function.comp_apply]
    rw [← hN, ← hL]
    set P4 := pA (Sh X) + pC (Sh X) + pD (Sh X) + pB (2 * Sh X + 1 + X)
    set A := pN X + X + pI X + pR (Sh X)
    have hA : A ≤ (N + 1) * A := Nat.le_mul_of_pos_left _ (by omega)
    have hB := Nat.mul_le_mul_left (N + 1) (show
      NativeCertificate.maxRoundTime (IndexFold.roundCertificate (engineStepCertificate core cc))
          N (0, y, []) +
        NativeCertificate.maxStateLength encS (IndexFold.step (engineStep core)) N (0, y, []) +
          ((encNat N).length + 1) ^ 2 ≤ 2 * S + 2 * (N + 1) ^ 2 + P4 + R by omega)
    have hsum : (N + 1) * A + (N + 1) * (2 * S + 2 * (N + 1) ^ 2 + P4 + R) =
        (N + 1) * (A + 2 * S + 2 * (N + 1) ^ 2 + P4 + R) := by ring
    have hC := Nat.mul_le_mul_left (N + 1)
      (show A + 2 * S + 2 * (N + 1) ^ 2 + P4 + R ≤ (a + d) * (X + 1) ^ (a + d) + R by
        simp only [U] at hUX
        omega)
    omega
  · rw [engineCertificate, NativeCertificate.congr_space, NativeCertificate.comp_space,
      IndexFold.certificate, NativeCertificate.iterate_space]
    simp only [NativeCertificate.prod_space, NativeCertificate.const_space, Function.comp_apply]
    rw [← hN, ← hL]
    simp only [U] at hUX
    omega

/-! ### Specialized entries -/

/-- **Time and space of specialized entries.** There is `K` such that, for every entry
certificate `ce`, evaluating the specialized entry at `q = ((t, P, ℓ, fl, ζ), bs)` costs the
original entry at `(t, bs)` plus `K (n + e + 1) ^ K`, in time and in space, for the length `n` of
`q` and the length `e` of the original entry. -/
theorem specEntryCertificate_le :
    ∃ K : ℕ, ∀ (entry : T → List Bool → List ℕ)
      (ce : NativeCertificate (fun q : T × List Bool => entry q.1 q.2) (encPair encT encBits)
        (encList encNat)) (q : SpecDesc T × List Bool),
      (specEntryCertificate entry ce).time q ≤ ce.time (q.1.1, q.2) +
          K * ((encPair (encSpecDesc encT) encBits q).length +
            (encList encNat (entry q.1.1 q.2)).length + 1) ^ K ∧
        (specEntryCertificate entry ce).space q ≤ ce.space (q.1.1, q.2) +
          K * ((encPair (encSpecDesc encT) encBits q).length +
            (encList encNat (entry q.1.1 q.2)).length + 1) ^ K := by
  have hcD : ComputableInPolyTime (fun q : SpecDesc T × List Bool => q.1.2)
      (encPair (encSpecDesc encT) encBits) encSpecData :=
    (ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _)
  have hcE : ComputableInPolyTime (fun q : SpecDesc T × List Bool => (q.1.1, q.2))
      (encPair (encSpecDesc encT) encBits) (encPair encT encBits) :=
    ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _)).prod
      (ComputableInPolyTime.snd _ _)
  obtain ⟨pD, hpD, mD, bD⟩ := exists_mono_poly_cert hcD
  obtain ⟨pE, hpE, mE, bE⟩ := exists_mono_poly_cert hcE
  obtain ⟨pH, hpH, mH, bH⟩ := exists_mono_poly_cert horner_polyTime
  let U : ℕ → ℕ := fun Z => pD Z + pE Z + pH (2 * Z + 1)
  have hU : PolyBounded id U :=
    ((polyBounded_comp_poly hpD PolyBounded.self).add
      (polyBounded_comp_poly hpE PolyBounded.self)).add
      (polyBounded_comp_poly hpH (((PolyBounded.const 2).mul PolyBounded.self).add
        (PolyBounded.const 1)))
  obtain ⟨a, d, hUad⟩ := hU.exists_le
  refine ⟨a + d, fun entry ce q => ?_⟩
  set n := (encPair (encSpecDesc encT) encBits q).length with hn
  set Z := n + (encList encNat (entry q.1.1 q.2)).length with hZ
  have hUZ : U Z ≤ (a + d) * (Z + 1) ^ (a + d) := by
    have h1 := hUad Z
    simp only [id] at h1
    exact h1.trans (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega)))
  have hnZ : n ≤ Z := by omega
  have hH : (encPair encSpecData (encList encNat) (q.1.2, entry q.1.1 q.2)).length ≤ 2 * Z + 1 := by
    have : (encSpecData q.1.2).length ≤ n := by
      simp only [hn, length_encPair]
      omega
    simp only [length_encPair] at this ⊢
    omega
  simp only [U] at hUZ
  have h1 := (bD q).1.trans (mD hnZ)
  have h2 := (bE q).1.trans (mE hnZ)
  have h3 := (bH (q.1.2, entry q.1.1 q.2)).1.trans (mH hH)
  have h1' := (bD q).2.trans (mD hnZ)
  have h2' := (bE q).2.trans (mE hnZ)
  have h3' := (bH (q.1.2, entry q.1.1 q.2)).2.trans (mH hH)
  refine ⟨?_, ?_⟩
  · simp only [specEntryCertificate, NativeCertificate.congr, NativeCertificate.comp_time,
      NativeCertificate.prod_time, Function.comp_apply]
    omega
  · simp only [specEntryCertificate, NativeCertificate.congr, NativeCertificate.comp_space,
      NativeCertificate.prod_space, Function.comp_apply]
    omega

end Cslib.Circuits.Frontier
