/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.IncidenceSparseCounter
import all CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.IncidenceSparseCounter
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog

/-!
# Globally bounded native callback for parity-system counting

Validate the actual sparse-system domain and use direct counting below a fixed exceptional-size
threshold. Outside that domain return zero. This derives global time and workspace bounds for
an actual callback; it does not assume that the unguarded sparse counter has such bounds.
-/

public section

namespace Cslib.Circuits.Frontier.IncidenceNetwork

open Cslib.GenericRAM Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime
open SubexponentialSAT SubexponentialSAT.SparsePolyCounter ExhaustiveCountFallback

/-- Computed sparse-system validation, with fixed degree and density parameters. -/
@[expose] def validSparseSystem (k c : ℕ) (p : ArrayInput) : Bool :=
  validSystem k p && decide (p.2.length ≤ c * p.1) &&
    p.2.all (fun eq => decide (eq.length ≤ Nat.clog 2 p.1 ^ c))

/-- The executable domain check is exactly the sparse-system hypothesis of the native theorem. -/
theorem validSparseSystem_iff (k c : ℕ) (p : ArrayInput) :
    validSparseSystem k c p = true ↔ IncidenceBranching.IsSparseSystem k c p.1 p.2 := by
  simp only [validSparseSystem, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    validSystem_iff]
  constructor
  · rintro ⟨⟨⟨hc, hv, hd⟩, hl⟩, hm⟩
    exact ⟨hv, hc, hl, hm, hd⟩
  · intro h
    exact ⟨⟨⟨h.canonical, h.vars_lt, h.degree_le⟩, h.length_le⟩, h.monomials_le⟩

/-- Direct counting at bounded dimensions, otherwise the actual guarded sharper counter.
The threshold is fixed before the input and does not supply a runtime or desired answer. -/
@[expose] noncomputable def uniformSparseCount (k c N₀ : ℕ) (p : ArrayInput) : ℕ :=
  if p.1 < N₀ then countSystemExhaustive p
  else if validSparseSystem k c p then countSparse k p else 0

/-- Correct at every size on its sparse domain, for every choice of the constant cutoff. -/
theorem uniformSparseCount_eq_rootCount {k c N₀ n : ℕ} {sys : List (List (List ℕ))}
    (hs : IncidenceBranching.IsSparseSystem k c n sys) :
    uniformSparseCount k c N₀ (n, sys) = HeavyBranchFold.rootCount n sys := by
  rw [uniformSparseCount]
  split_ifs with hn hvalid
  · exact countSystemExhaustive_eq_rootCount n sys
  · exact countSparse_eq_rootCount hs.canonical hs.vars_lt hs.degree_le
  · exact False.elim (hvalid ((validSparseSystem_iff k c (n, sys)).mpr hs))

/-- All checks use actual encoded lengths and binary variable indices. -/
@[fun_prop] theorem validSparseSystem_polytime (k c : ℕ) :
    ComputableInPolyTime (validSparseSystem k c) encArrayInput encBool := by
  have hn := fst encUnary (encList (encList (encList encNat)))
  have hs := snd encUnary (encList (encList (encList encNat)))
  have hpow : ComputableInPolyTime (fun p : ArrayInput => Nat.clog 2 p.1 ^ c)
      encArrayInput encUnary := by
    have hlog := (binary_clog_two.comp unary_to_binary).comp hn
    induction c with
    | zero => exact const 1
    | succ c ih => simpa only [pow_succ, Function.comp_def] using unary_mul' ih hlog
  have hlen := (length_list (encList (encList encNat))).comp hs
  have hcap : ComputableInPolyTime (fun p : ArrayInput => c * p.1) encArrayInput encUnary :=
    unary_mul' (const c) hn
  have hmono : ComputableInPolyTime (fun q : ArrayInput × List (List ℕ) =>
      decide (q.2.length ≤ Nat.clog 2 q.1.1 ^ c))
      (encPair encArrayInput (encList (encList encNat))) encBool :=
    unary_le' ((length_list (encList encNat)).comp (snd _ _)) (hpow.comp (fst _ _))
  exact bool_and' (bool_and' (validSystem_polytime k) (unary_le' hlen hcap))
    (allWithInput hs hmono)

private theorem small_polytime (N₀ : ℕ) :
    ComputableInPolyTime (fun p : ArrayInput => decide (p.1 < N₀)) encArrayInput encBool := by
  unfold encArrayInput
  fun_prop

private noncomputable def smallCert (N₀ : ℕ) :
    NativeCertificate (fun p : ArrayInput => decide (p.1 < N₀)) encArrayInput encBool :=
  NativeCertificate.ofPolyTime (small_polytime N₀)

private noncomputable def sparseCert (k c : ℕ) :
    NativeCertificate (validSparseSystem k c) encArrayInput encBool :=
  NativeCertificate.ofPolyTime (validSparseSystem_polytime k c)

private noncomputable def rejectCert :
    NativeCertificate (fun _ : ArrayInput => (0 : ℕ)) encArrayInput encNat :=
  NativeCertificate.ofPolyTime (const 0)

private noncomputable def dispatchCert (k c N₀ : ℕ)
    (base : NativeCertificate (countSparse k) encArrayInput encNat) :
    NativeCertificate (uniformSparseCount k c N₀) encArrayInput encNat :=
  (NativeCertificate.branch (smallCert N₀) countSystemExhaustiveCertificate
    (NativeCertificate.branch (sparseCert k c) base rejectCert)).congr fun p => by
      simp only [uniformSparseCount, decide_eq_true_eq]

/-- One actual callback has global sharp time and global polynomial workspace, including
malformed or nonsparse inputs. Correctness on sparse inputs is proved separately above.
There is no assumed callback runtime/space contract. -/
theorem exists_uniformSparseCount_certificate (k c : ℕ) (hk : 1 ≤ k) :
    ∃ N₀ : ℕ, ∃ (cs : NativeCertificate (uniformSparseCount k c N₀) encArrayInput encNat)
      (D : ℕ), ∀ p : ArrayInput,
      cs.time p ≤ D * ((encArrayInput p).length + 1) ^ D *
        2 ^ (D * Nat.logLogSqrtLogScale p.1) ∧
      cs.space p ≤ D * ((encArrayInput p).length + 1) ^ D := by
  obtain ⟨base, A, n₀, hb⟩ := exists_countSparse_sharp_certificate k c hk
  let N₀ := max n₀ 4
  have hsmall := NativeCertificate.ofPolyTime_isPolynomial (small_polytime N₀)
  have hsparse := NativeCertificate.ofPolyTime_isPolynomial (validSparseSystem_polytime k c)
  have hreject := NativeCertificate.ofPolyTime_isPolynomial
    (show ComputableInPolyTime (fun _ : ArrayInput => (0 : ℕ)) encArrayInput encNat from const 0)
  obtain ⟨P, Q, hP, hQ, hex⟩ := exists_countSystemExhaustive_time_le
  let W (p : ArrayInput) :=
    (smallCert N₀).time p + (smallCert N₀).space p + (sparseCert k c).time p +
      (sparseCert k c).space p + rejectCert.time p + rejectCert.space p +
      ((2 ^ N₀ + 1) * P p + Q p) + countSystemExhaustiveCertificate.space p +
      A * ((encArrayInput p).length + 1) ^ A
  have hAp : PolyBounded (fun p : ArrayInput => (encArrayInput p).length)
      (fun p => A * ((encArrayInput p).length + 1) ^ A) :=
    PolyBounded.of_polynomiallyBounded _ (bound := fun L => A * (L + 1) ^ A) (by fun_prop)
  have hW : PolyBounded (fun p : ArrayInput => (encArrayInput p).length) W :=
    (((((((hsmall.1.add hsmall.2).add hsparse.1).add hsparse.2).add hreject.1).add hreject.2).add
      (((PolyBounded.const (2 ^ N₀ + 1)).mul hP).add hQ)).add
      polyBounded_countSystemExhaustive_space).add hAp
  obtain ⟨C, d, hCd⟩ := hW.exists_le
  let D := A + C + d + 1
  refine ⟨N₀, dispatchCert k c N₀ base, D, fun p => ?_⟩
  have hraw : (dispatchCert k c N₀ base).time p ≤
        W p + A * ((encArrayInput p).length + 1) ^ A * 2 ^ (A * Nat.logLogSqrtLogScale p.1) ∧
      (dispatchCert k c N₀ base).space p ≤ W p := by
    change (smallCert N₀).time p + (if decide (p.1 < N₀) then _ else
      (sparseCert k c).time p + if validSparseSystem k c p then _ else _) ≤ _ ∧
      (smallCert N₀).space p + (if decide (p.1 < N₀) then _ else
      (sparseCert k c).space p + if validSparseSystem k c p then _ else _) ≤ _
    by_cases hn : p.1 < N₀
    · have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hn.le
      have hext := (hex p).trans (Nat.add_le_add_right
        (Nat.mul_le_mul_right (P p) (Nat.add_le_add_right hpow 1)) (Q p))
      simp only [hn, decide_true, ↓reduceIte]
      dsimp only [W]
      constructor <;> omega
    · simp only [hn, decide_false, Bool.false_eq_true, ↓reduceIte]
      by_cases hs : validSparseSystem k c p = true
      · have hn' : n₀ ≤ p.1 := (le_max_left _ _).trans (by omega : N₀ ≤ p.1)
        obtain ⟨ht, hspace⟩ := hb p.1 hn' p.2 ((validSparseSystem_iff k c p).mp hs)
        change base.time p ≤ A * ((encArrayInput p).length + 1) ^ A *
          2 ^ (A * Nat.logLogSqrtLogScale p.1) at ht
        change base.space p ≤ A * ((encArrayInput p).length + 1) ^ A at hspace
        rw [hs]
        simp only [↓reduceIte]
        dsimp only [W]
        constructor <;> omega
      · simp only [hs, Bool.false_eq_true, ↓reduceIte]
        dsimp only [W]
        constructor <;> omega
  let L := (encArrayInput p).length
  let E := Nat.logLogSqrtLogScale p.1
  have hA : A ≤ D := by dsimp only [D]; omega
  have hd : d ≤ D := by dsimp only [D]; omega
  have hcoef : C + A ≤ D := by dsimp only [D]; omega
  have hW' : W p ≤ C * (L + 1) ^ D :=
    (hCd p).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hd))
  have hWT : W p ≤ C * (L + 1) ^ D * 2 ^ (D * E) :=
    hW'.trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
  have hfast : A * (L + 1) ^ A * 2 ^ (A * E) ≤ A * (L + 1) ^ D * 2 ^ (D * E) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hA))
      (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ hA))
  constructor
  · calc _ ≤ C * (L + 1) ^ D * 2 ^ (D * E) + A * (L + 1) ^ D * 2 ^ (D * E) :=
          hraw.1.trans (Nat.add_le_add hWT hfast)
      _ = (C + A) * (L + 1) ^ D * 2 ^ (D * E) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hcoef)
  · exact hraw.2.trans (hW'.trans
      (Nat.mul_le_mul_right _ (by dsimp only [D]; omega)))

end Cslib.Circuits.Frontier.IncidenceNetwork
