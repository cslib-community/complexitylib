/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.GenericRAM.Native.IndexFold
public import Complexity.Foundations.Data.Nat.ResidueSum
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv

/-!
# Streamed sums modulo a computed modulus

`Cslib.Complexity.CountingSimulation.modSum r modulus count c` adds the terms `r (c, 0)`, …,
`r (c, count c - 1)` to an accumulator one at a time, reducing modulo `modulus c` after each
addition. The terms are visited by the binary-index fold `Cslib.GenericRAM.IndexFold`, which keeps
only the index, the context `c` and the accumulator, so the workspace does not grow with the
number of terms.

This is the outer loop of the deterministic counting simulation of #1833: the context is the input
and the clock, the terms are the residues of the contractions of the networks of the movement
schedules, and the modulus is a power of two above the count being recovered
(`Nat.foldl_range_add_mod_eq_of_lt`).

The resource bound (`Cslib.Complexity.CountingSimulation.exists_computableInO_modSum`) is a native
multi-tape certificate: if the number of terms and the modulus are computable in polynomial time,
the terms lie below the modulus, and a certificate computes the term at every summed index within
time `R c` and space `Q c`, then the streamed sum is computable within time
`(count c + 1) * (poly + R c)` and space `poly + Q c`, for a polynomial in the encoded length of the
context. Neither `R` nor `Q` needs to be polynomial.

## Main definitions

* `Cslib.Complexity.CountingSimulation.modSumStep`: one round of the streamed sum.
* `Cslib.Complexity.CountingSimulation.modSum`: the streamed sum modulo the modulus.

## Main results

* `Cslib.Complexity.CountingSimulation.modSum_eq_sum_mod`: the streamed sum is the sum of the terms
  modulo the modulus.
* `Cslib.Complexity.CountingSimulation.exists_computableInO_modSum`: its time and space bounds.
-/

public section

namespace Cslib.Complexity.CountingSimulation

open Turing.MultiTapeTM Cslib.GenericRAM

variable {C : Type}

/-- One round of the streamed sum at index `p.1`, with context `p.2.1` and accumulator `p.2.2`:
below the number of terms, add the term and reduce modulo the modulus; otherwise leave the state
unchanged. -/
def modSumStep (r : C × ℕ → ℕ) (modulus count : C → ℕ) (p : ℕ × (C × ℕ)) : C × ℕ :=
  if p.1 < count p.2.1 then (p.2.1, (p.2.2 + r (p.2.1, p.1)) % modulus p.2.1) else p.2

/-- The terms `r (c, 0)`, …, `r (c, count c - 1)` summed one at a time from zero, reducing modulo
`modulus c` after each addition, by a streaming fold over a binary index. -/
def modSum (r : C × ℕ → ℕ) (modulus count : C → ℕ) (c : C) : ℕ :=
  (IndexFold.run (modSumStep r modulus count) (count c) (c, 0)).2.2

variable {r : C × ℕ → ℕ} {modulus count : C → ℕ}

/-- The state of the streamed sum after `j ≤ count c` rounds: the index `j`, the unchanged context
and the residue of the first `j` terms. -/
theorem run_modSumStep {c : C} {j : ℕ} (hj : j ≤ count c) :
    IndexFold.run (modSumStep r modulus count) j (c, 0) =
      (j, (c, (List.range j).foldl (fun acc i => (acc + r (c, i)) % modulus c) 0)) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [IndexFold.run_succ, ih (by omega)]
    simp only [IndexFold.step, modSumStep, (show j < count c by omega), ↓reduceIte, List.range_succ,
      List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- **The streamed sum is the sum modulo the modulus.** -/
theorem modSum_eq_sum_mod (r : C × ℕ → ℕ) (modulus count : C → ℕ) (c : C) :
    modSum r modulus count c = (∑ i ∈ Finset.range (count c), r (c, i)) % modulus c := by
  have h := Nat.foldl_range_add_mod (fun i => r (c, i)) (modulus c) 0 (count c)
  rw [Nat.zero_mod, Nat.zero_add] at h
  rw [modSum, run_modSumStep le_rfl, h]

private theorem foldl_add_mod_lt {f : ℕ → ℕ} {m : ℕ} (hm : 0 < m) (j : ℕ) :
    (List.range j).foldl (fun acc i => (acc + f i) % m) 0 < m := by
  cases j with
  | zero => exact hm
  | succ j =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact Nat.mod_lt _ hm

private theorem polyBounded_comp_poly {size u : C → ℕ} {p : ℕ → ℕ}
    (hp : Cslib.PolynomiallyBounded p) (hu : PolyBounded size u) :
    PolyBounded size fun c => p (u c) :=
  (PolyBounded.of_polynomiallyBounded id hp).comp hu

/-- **Resource bound of the streamed sum.** Suppose the number of terms and the modulus are
computable in polynomial time, the modulus is positive, every summed term lies below it, and a
native certificate computes the terms within time `R c` and space `Q c` at the summed indices.
Then the streamed sum is computable within time `(count c + 1) * (a * (n + 1) ^ d + R c)` and space
`a * (n + 1) ^ d + Q c`, where `n` is the encoded length of the context and `a`, `d` are constants:
the workspace holds one binary index, the context and an accumulator below the modulus. -/
theorem exists_computableInO_modSum {encC : C ↪ List Bool}
    (hmodulus : ComputableInPolyTime modulus encC encNat)
    (hcount : ComputableInPolyTime count encC encNat)
    (cr : NativeCertificate r (encPair encC encNat) encNat)
    (hpos : ∀ c, 0 < modulus c) (hr : ∀ c i, i < count c → r (c, i) < modulus c)
    (R Q : C → ℕ) (hR : ∀ c i, i < count c → cr.time (c, i) ≤ R c)
    (hQ : ∀ c i, i < count c → cr.space (c, i) ≤ Q c) :
    ∃ a d : ℕ, ComputableInO (modSum r modulus count) encC encNat
      (fun c => (count c + 1) * (a * ((encC c).length + 1) ^ d + R c))
      (fun c => a * ((encC c).length + 1) ^ d + Q c) := by
  -- The polynomial-time pieces of a round.
  have htest : ComputableInPolyTime (fun p : ℕ × (C × ℕ) => decide (p.1 < count p.2.1))
      (encPair encNat (encPair encC encNat)) encBool := by fun_prop
  have hctx : ComputableInPolyTime (fun p : ℕ × (C × ℕ) => p.2.1)
      (encPair encNat (encPair encC encNat)) encC := by fun_prop
  have hacc : ComputableInPolyTime (fun p : ℕ × (C × ℕ) => p.2.2)
      (encPair encNat (encPair encC encNat)) encNat := by fun_prop
  have hswap : ComputableInPolyTime (fun p : ℕ × (C × ℕ) => (p.2.1, p.1))
      (encPair encNat (encPair encC encNat)) (encPair encC encNat) := by fun_prop
  have hmod : ComputableInPolyTime (fun p : ℕ × (C × ℕ) => modulus p.2.1)
      (encPair encNat (encPair encC encNat)) encNat := by fun_prop
  have hno : ComputableInPolyTime (fun p : ℕ × (C × ℕ) => p.2)
      (encPair encNat (encPair encC encNat)) (encPair encC encNat) := by fun_prop
  have hadd : ComputableInPolyTime (fun q : ℕ × ℕ × ℕ => (q.1 + q.2.1) % q.2.2)
      (encPair encNat (encPair encNat encNat)) encNat := by fun_prop
  have hinit : ComputableInPolyTime (fun c : C => (c, 0)) encC (encPair encC encNat) := by
    fun_prop
  -- The round: a test, then either the addition or nothing.
  let yes : NativeCertificate
      (fun p : ℕ × (C × ℕ) => (p.2.1, (p.2.2 + r (p.2.1, p.1)) % modulus p.2.1))
      (encPair encNat (encPair encC encNat)) (encPair encC encNat) :=
    (NativeCertificate.ofPolyTime hctx).prod
      ((NativeCertificate.ofPolyTime hadd).comp
        ((NativeCertificate.ofPolyTime hacc).prod
          ((cr.comp (NativeCertificate.ofPolyTime hswap)).prod
            (NativeCertificate.ofPolyTime hmod))))
  let cstep : NativeCertificate (modSumStep r modulus count)
      (encPair encNat (encPair encC encNat)) (encPair encC encNat) :=
    (NativeCertificate.branch (NativeCertificate.ofPolyTime htest) yes
      (NativeCertificate.ofPolyTime hno)).congr fun p => by
        simp only [modSumStep, decide_eq_true_eq]
  -- Monotone polynomial bounds of the pieces.
  obtain ⟨pT, hpT, mT, bT⟩ := exists_mono_poly_cert htest
  obtain ⟨pC, hpC, mC, bC⟩ := exists_mono_poly_cert hctx
  obtain ⟨pA, hpA, mA, bA⟩ := exists_mono_poly_cert hacc
  obtain ⟨pW, hpW, mW, bW⟩ := exists_mono_poly_cert hswap
  obtain ⟨pM, hpM, mM, bM⟩ := exists_mono_poly_cert hmod
  obtain ⟨pN, hpN, mN, bN⟩ := exists_mono_poly_cert hno
  obtain ⟨pD, hpD, mD, bD⟩ := exists_mono_poly_cert hadd
  obtain ⟨pI, hpI, -, bI⟩ := exists_mono_poly_cert hinit
  obtain ⟨pK, hpK, -, bK⟩ := exists_mono_poly_cert hcount
  -- Sizes: the context, the modulus and the number of terms.
  set L : C → ℕ := fun c => (encC c).length with hL
  set lm : C → ℕ := fun c => (encNat (modulus c)).length with hlm
  set lk : C → ℕ := fun c => (encNat (count c)).length with hlk
  have hLp : PolyBounded L L := PolyBounded.self
  have hlmp : PolyBounded L lm := hmodulus.polyBounded_length
  have hlkp : PolyBounded L lk := hcount.polyBounded_length
  -- A state `(j, (c, acc))` with `j ≤ count c` and `acc < modulus c` has length at most `S c`; the
  -- input of the addition has length at most `S' c`; the accumulator pair at most `B c`.
  let S : C → ℕ := fun c => 2 * lk c + 2 * L c + lm c + 2
  let S' : C → ℕ := fun c => 5 * lm c + 2
  let B : C → ℕ := fun c => 2 * L c + 1 + lm c
  let U : C → ℕ := fun c => pT (S c) + pC (S c) + pA (S c) + pW (S c) + pM (S c) + pD (S' c) +
    pN (S c)
  have hstate (c : C) (j : ℕ) (hj : j ≤ count c) :
      (encPair encNat (encPair encC encNat)
        (IndexFold.run (modSumStep r modulus count) j (c, 0))).length ≤ S c := by
    rw [run_modSumStep hj]
    have hacc := length_encNat_mono (foldl_add_mod_lt (f := fun i => r (c, i)) (hpos c) j).le
    have hj' := length_encNat_mono hj
    simp only [length_encPair, S, L, lm, lk] at hacc hj' ⊢
    omega
  have hround_time (c : C) (j : ℕ) (hj : j ≤ count c) :
      cstep.time (IndexFold.run (modSumStep r modulus count) j (c, 0)) ≤ U c + R c := by
    have hs := hstate c j hj
    rw [run_modSumStep hj] at hs ⊢
    set acc := (List.range j).foldl (fun acc i => (acc + r (c, i)) % modulus c) 0
    simp only [cstep, yes, NativeCertificate.congr, NativeCertificate.branch_time,
      NativeCertificate.prod_time, NativeCertificate.comp_time, Function.comp_apply]
    have h1 := (bT (j, (c, acc))).1.trans (mT hs)
    split_ifs with hlt
    · have hjc : j < count c := of_decide_eq_true hlt
      have hacc_lt : acc < modulus c := foldl_add_mod_lt (hpos c) j
      have hrj := hr c j hjc
      have hq : (encPair encNat (encPair encNat encNat)
          (acc, r (c, j), modulus c)).length ≤ S' c := by
        have := length_encNat_mono hacc_lt.le
        have := length_encNat_mono hrj.le
        simp only [length_encPair, S', lm] at *
        omega
      have h2 := (bC (j, (c, acc))).1.trans (mC hs)
      have h3 := (bA (j, (c, acc))).1.trans (mA hs)
      have h4 := (bW (j, (c, acc))).1.trans (mW hs)
      have h5 := (bM (j, (c, acc))).1.trans (mM hs)
      have h6 := (bD (acc, r (c, j), modulus c)).1.trans (mD hq)
      have h7 := hR c j hjc
      simp only [U]
      omega
    · have h2 := (bN (j, (c, acc))).1.trans (mN hs)
      simp only [U]
      omega
  have hround_space (c : C) (j : ℕ) (hj : j ≤ count c) :
      cstep.space (IndexFold.run (modSumStep r modulus count) j (c, 0)) ≤ U c + Q c := by
    have hs := hstate c j hj
    rw [run_modSumStep hj] at hs ⊢
    set acc := (List.range j).foldl (fun acc i => (acc + r (c, i)) % modulus c) 0
    simp only [cstep, yes, NativeCertificate.congr, NativeCertificate.branch_space,
      NativeCertificate.prod_space, NativeCertificate.comp_space, Function.comp_apply]
    have h1 := (bT (j, (c, acc))).2.trans (mT hs)
    split_ifs with hlt
    · have hjc : j < count c := of_decide_eq_true hlt
      have hacc_lt : acc < modulus c := foldl_add_mod_lt (hpos c) j
      have hrj := hr c j hjc
      have hq : (encPair encNat (encPair encNat encNat)
          (acc, r (c, j), modulus c)).length ≤ S' c := by
        have := length_encNat_mono hacc_lt.le
        have := length_encNat_mono hrj.le
        simp only [length_encPair, S', lm] at *
        omega
      have h2 := (bC (j, (c, acc))).2.trans (mC hs)
      have h3 := (bA (j, (c, acc))).2.trans (mA hs)
      have h4 := (bW (j, (c, acc))).2.trans (mW hs)
      have h5 := (bM (j, (c, acc))).2.trans (mM hs)
      have h6 := (bD (acc, r (c, j), modulus c)).2.trans (mD hq)
      have h7 := hQ c j hjc
      simp only [U]
      omega
    · have h2 := (bN (j, (c, acc))).2.trans (mN hs)
      simp only [U]
      omega
  have hacc_len (c : C) (j : ℕ) (hj : j ≤ count c) :
      (encPair encC encNat (IndexFold.run (modSumStep r modulus count) j (c, 0)).2).length ≤
        B c := by
    rw [run_modSumStep hj]
    have := length_encNat_mono (foldl_add_mod_lt (f := fun i => r (c, i)) (hpos c) j).le
    simp only [length_encPair, B, L, lm] at this ⊢
    omega
  have hrun := IndexFold.computableInO (NativeCertificate.ofPolyTime hcount)
    (NativeCertificate.ofPolyTime hinit) cstep (fun c => U c + R c) (fun c => U c + Q c) B
    hround_time hround_space hacc_len
  have hout := (ComputableInO.snd encC encNat).comp_linear
    ((ComputableInO.snd encNat (encPair encC encNat)).comp_linear hrun)
  -- Collect the polynomial overhead.
  let V : C → ℕ := fun c => pK (L c) + (L c + pI (L c)) + 2 * (2 * lk c + 1 + B c) +
    2 * (lk c + 1) ^ 2 + (lk c + 1) + lk c + U c
  have hSp : PolyBounded L S :=
    ((((PolyBounded.const 2).mul hlkp).add ((PolyBounded.const 2).mul hLp)).add hlmp).add
      (PolyBounded.const 2)
  have hS'p : PolyBounded L S' := ((PolyBounded.const 5).mul hlmp).add (PolyBounded.const 2)
  have hBp : PolyBounded L B :=
    ((((PolyBounded.const 2).mul hLp).add (PolyBounded.const 1))).add hlmp
  have hUp : PolyBounded L U :=
    ((((((polyBounded_comp_poly hpT hSp).add (polyBounded_comp_poly hpC hSp)).add
      (polyBounded_comp_poly hpA hSp)).add (polyBounded_comp_poly hpW hSp)).add
      (polyBounded_comp_poly hpM hSp)).add (polyBounded_comp_poly hpD hS'p)).add
      (polyBounded_comp_poly hpN hSp)
  have hVp : PolyBounded L V :=
    ((((((polyBounded_comp_poly hpK hLp).add (hLp.add (polyBounded_comp_poly hpI hLp))).add
      ((PolyBounded.const 2).mul ((((PolyBounded.const 2).mul hlkp).add
        (PolyBounded.const 1)).add hBp))).add
      ((PolyBounded.const 2).mul ((hlkp.add (PolyBounded.const 1)).pow 2))).add
      (hlkp.add (PolyBounded.const 1))).add hlkp).add hUp
  obtain ⟨a, d, hV⟩ := hVp.exists_le
  refine ⟨a, d, (hout.mono_le (fun c => ?_) fun c => ?_).of_enc_eq fun c => rfl⟩
  · have hK := (bK c).1
    have hI := (bI c).1
    have hVc := hV c
    have hone : 1 ≤ count c + 1 := by omega
    have hmul : V c + R c ≤ (count c + 1) * (V c + R c) := Nat.le_mul_of_pos_left _ hone
    have hmono : (count c + 1) * (V c + R c) ≤ (count c + 1) * (a * (L c + 1) ^ d + R c) :=
      Nat.mul_le_mul_left _ (by omega)
    simp only [V, L, lk] at hK hI hVc hmul hmono ⊢
    nlinarith
  · have hK := (bK c).2
    have hI := (bI c).2
    have hVc := hV c
    simp only [V, L, lk] at hK hI hVc ⊢
    omega

end Cslib.Complexity.CountingSimulation
