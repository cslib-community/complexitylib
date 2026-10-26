/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.Encoding
import ComplexityAbstracts.Computation
import Complexity.Computability.MCSP.Magnification

/-!
# Bridge for the McKay–Murray–Williams hardness magnification formal abstract

Connects the self-contained definitions in `MagnificationAbstract.lean` (plain De Morgan circuits,
the `2 ^ n`-bit truth-table slice of `MCSP[s]`, and plain native-machine definitions of `P`, `NP`,
and `P/poly`) to the theorems in `Complexity.Computability.MCSP.Magnification`.
-/

namespace ComplexityAbstracts.MagnificationBridge

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Complexity Cslib.MCSP
open Turing.MultiTapeTM
open ComplexityTests.Abstracts

/-- A single-output Boolean circuit over the standard De Morgan basis (binary AND/OR, unary NOT,
and Boolean constants). -/
abbrev DeMorganCircuit (n : ℕ) :=
  Circuit signature n 1

/-- The Boolean value computed by a single-output De Morgan circuit `C` on input `x`. -/
def evalCircuit {n : ℕ} (C : DeMorganCircuit n) (x : Fin n → Bool) : Bool :=
  C.eval interpretation x 0

/-- A circuit `C` computes a Boolean function `f : (Fin n → Bool) → Bool` if it agrees with `f` on
every `n`-bit input. -/
def ComputesFunction {n : ℕ} (C : DeMorganCircuit n) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x : Fin n → Bool, evalCircuit C x = f x

theorem computesFunction_iff {n : ℕ} {C : DeMorganCircuit n} {f : (Fin n → Bool) → Bool} :
    ComputesFunction C f ↔ C.Computes interpretation (single f) :=
  Circuit.computes_single_iff.symm

/-- A Boolean function `f : (Fin n → Bool) → Bool` has a De Morgan circuit with at most `k`
operation gates. -/
def HasCircuitOfSize {n : ℕ} (f : (Fin n → Bool) → Bool) (k : ℕ) : Prop :=
  ∃ C : DeMorganCircuit n, ComputesFunction C f ∧ C.size ≤ k

theorem hasCircuitOfSize_iff_complexity_le {n : ℕ} {f : (Fin n → Bool) → Bool} {k : ℕ} :
    HasCircuitOfSize f k ↔ complexity interpretation (single f) ≤ k := by
  rw [complexity_le_iff]
  exact exists_congr fun C => and_congr_left fun _ => computesFunction_iff

/-- The binary number represented by `bits : Fin n → Bool`, with coordinate zero least
significant. -/
def tableIndex (n : ℕ) : (Fin n → Bool) ≃ Fin (2 ^ n) :=
  (Equiv.arrowCongr (Equiv.refl (Fin n)) finTwoEquiv.symm).trans finFunctionFinEquiv

theorem tableIndex_val {n : ℕ} (bits : Fin n → Bool) :
    (tableIndex n bits).val = ∑ i : Fin n, (if bits i then 1 else 0) * 2 ^ i.val := by
  change (finFunctionFinEquiv (fun i => finTwoEquiv.symm (bits i))).val = _
  rw [finFunctionFinEquiv_apply]
  apply Finset.sum_congr rfl
  intro i _
  cases bits i <;> simp [finTwoEquiv]

/-- The `n`-variable Boolean function represented by a `2 ^ n`-bit truth table `T`. -/
def tableFunction {n : ℕ} (T : Fin (2 ^ n) → Bool) (x : Fin n → Bool) : Bool :=
  T (tableIndex n x)

theorem tableFunction_eq_truthTable_symm {n : ℕ} (T : Fin (2 ^ n) → Bool) :
    tableFunction T = (truthTable n).symm T :=
  rfl

/-- A circuit `C : DeMorganCircuit (2 ^ n)` decides `MCSP[s]` on `2 ^ n`-bit truth tables if for
every table `T`, `C` outputs `true` on `T` if and only if `tableFunction T` has a De Morgan circuit
with at most `s n` gates. -/
def DecidesMCSPSlice {n : ℕ} (C : DeMorganCircuit (2 ^ n)) (s : ℕ → ℕ) : Prop :=
  ∀ T : Fin (2 ^ n) → Bool,
    evalCircuit C T = true ↔ HasCircuitOfSize (tableFunction T) (s n)

theorem decidesMCSPSlice_iff {n : ℕ} {C : DeMorganCircuit (2 ^ n)} {s : ℕ → ℕ} :
    DecidesMCSPSlice C s ↔
      C.Computes interpretation (single ((GapMCSP.yesSet s).slice (2 ^ n))) := by
  rw [Circuit.computes_single_iff]
  refine forall_congr' fun T => ?_
  rw [Bool.eq_iff_iff (b := (GapMCSP.yesSet s).slice (2 ^ n) T),
    GapMCSP.slice_yesSet_eq_true_iff, ← hasCircuitOfSize_iff_complexity_le]
  rfl

/-- The class `P` of bit-string languages decidable in polynomial time on a deterministic
multi-tape Turing machine. -/
def P : Set (Set (List Bool)) :=
  {A | ∃ f : List Bool → Bool,
    Computation.PolyTime f Encoding.encBits Encoding.encBool ∧
    ∀ w, w ∈ A ↔ f w = true}

theorem p_eq : P = Cslib.Complexity.P Turing.MultiTapeTM.encBits :=
  rfl

/-- Fixed-length polynomial certificate verification for bit-string languages. -/
def IsVerifier (p : Polynomial ℕ) (V : List Bool × List Bool → Bool)
    (A : Set (List Bool)) : Prop :=
  ∀ x, x ∈ A ↔ ∃ w : List Bool, w.length = p.eval x.length ∧ V (x, w) = true

/-- The class `NP` of bit-string languages verifiable in polynomial time with polynomial-length
binary certificates. -/
def NP : Set (Set (List Bool)) :=
  {A | ∃ (p : Polynomial ℕ) (V : List Bool × List Bool → Bool),
    Computation.PolyTimeVerifier Encoding.encBits V ∧ IsVerifier p V A}

theorem mem_np_iff {A : Set (List Bool)} :
    A ∈ NP ↔ A ∈ Cslib.Complexity.NP Turing.MultiTapeTM.encBits := by
  rw [Cslib.Complexity.mem_NP_iff_exists_computableInTimeAndSpaceOfLength]
  constructor
  · rintro ⟨p, V, ⟨t, s, ht, hs, hV⟩, hA⟩
    exact ⟨p, V, t, s, ht, hs, hV, hA⟩
  · rintro ⟨p, V, t, s, ht, hs, hV, hA⟩
    exact ⟨p, V, ⟨t, s, ht, hs, hV⟩, hA⟩

theorem np_eq : NP = Cslib.Complexity.NP Turing.MultiTapeTM.encBits :=
  Set.ext fun _ => mem_np_iff

/-- The nonuniform class `P/poly` of bit-string languages decided at each input length `m` by a
De Morgan circuit of size bounded by a polynomially bounded function of `m`. -/
def PPoly : Set (Set (List Bool)) :=
  {A | ∃ size : ℕ → ℕ, PolynomiallyBounded size ∧ ∀ m,
    ∃ C : DeMorganCircuit m,
      (∀ x : Fin m → Bool, evalCircuit C x = true ↔ List.ofFn x ∈ A) ∧
      C.size ≤ size m}

theorem mem_ppoly_iff {A : Set (List Bool)} :
    A ∈ PPoly ↔ A ∈ PPolyOn Turing.MultiTapeTM.encBits := by
  let L : Language Bool := A
  have hL : A ∈ PPolyOn Turing.MultiTapeTM.encBits ↔ L ∈ Cslib.Circuits.Boolean.PPoly :=
    mem_PPolyOn_encBits_iff (A := L)
  rw [hL, mem_PPoly_iff_exists_circuits]
  constructor
  · rintro ⟨size, hsize, hC⟩
    choose C hcomp hle using hC
    refine ⟨C, size, hsize, fun m => ⟨hle m, Circuit.computes_single_iff.mpr fun x => ?_⟩⟩
    rw [Bool.eq_iff_iff, Language.slice_eq_true_iff]
    exact hcomp m x
  · rintro ⟨C, size, hsize, hC⟩
    refine ⟨size, hsize, fun m => ⟨C m, fun x => ?_, (hC m).1⟩⟩
    have hx := Circuit.computes_single_iff.mp (hC m).2 x
    change evalCircuit (C m) x = L.slice m x at hx
    rw [hx, Language.slice_eq_true_iff]
    rfl

theorem ppoly_eq : PPoly = PPolyOn Turing.MultiTapeTM.encBits :=
  Set.ext fun _ => mem_ppoly_iff

/-- Transfer of `exists_complexity_yesSet_le_of_NP_subset_PPoly`: if `NP ⊆ PPoly`, then `MCSP[s]`
on `2 ^ n`-bit truth tables has circuits of size `2 ^ n * c * (n + s n + 1) ^ c`. -/
theorem mcsp_circuit_of_np_subset_ppoly (hNP : NP ⊆ PPoly) :
    ∃ c > 0, ∀ (s : ℕ → ℕ) (n : ℕ),
      ∃ C : DeMorganCircuit (2 ^ n),
        DecidesMCSPSlice C s ∧ C.size ≤ 2 ^ n * c * (n + s n + 1) ^ c := by
  rw [np_eq, ppoly_eq] at hNP
  obtain ⟨c, hc_pos, hub⟩ := exists_complexity_yesSet_le_of_NP_subset_PPoly hNP
  refine ⟨c, hc_pos, fun s n => ?_⟩
  obtain ⟨C, hC, hsize⟩ := complexity_le_iff.mp (hub s n)
  exact ⟨C, decidesMCSPSlice_iff.mpr hC, hsize⟩

/-- Transfer of `exists_complexity_yesSet_pow_le_of_NP_subset_PPoly`: if `NP ⊆ PPoly`, then for
every degree `k`, `MCSP[fun m => m ^ k]` on `2 ^ n`-bit truth tables has circuits of size
`2 ^ n * c * (n + 1) ^ c`. -/
theorem mcsp_pow_circuit_of_np_subset_ppoly (hNP : NP ⊆ PPoly) (k : ℕ) :
    ∃ c > 0, ∀ n : ℕ,
      ∃ C : DeMorganCircuit (2 ^ n),
        DecidesMCSPSlice C (fun m => m ^ k) ∧ C.size ≤ 2 ^ n * c * (n + 1) ^ c := by
  rw [np_eq, ppoly_eq] at hNP
  obtain ⟨c, hc_pos, hub⟩ := exists_complexity_yesSet_pow_le_of_NP_subset_PPoly hNP k
  refine ⟨c, hc_pos, fun n => ?_⟩
  obtain ⟨C, hC, hsize⟩ := complexity_le_iff.mp (hub n)
  exact ⟨C, decidesMCSPSlice_iff.mpr hC, hsize⟩

/-- Transfer of `not_NP_subset_PPoly_of_yesSet_pow_hard`: barely superlinear circuit lower bounds
for `MCSP[fun m => m ^ k]` imply `¬ (NP ⊆ PPoly)`. -/
theorem np_not_subset_ppoly_of_mcsp_hard (k : ℕ)
    (h : ∀ c > 0, ∃ n : ℕ, ∀ C : DeMorganCircuit (2 ^ n),
      DecidesMCSPSlice C (fun m => m ^ k) → 2 ^ n * c * (n + 1) ^ c < C.size) :
    ¬ (NP ⊆ PPoly) := by
  intro hNP
  obtain ⟨c, hc_pos, hub⟩ := mcsp_pow_circuit_of_np_subset_ppoly hNP k
  obtain ⟨n, hlb⟩ := h c hc_pos
  obtain ⟨C, hC, hsize⟩ := hub n
  exact (lt_irrefl _) ((hlb C hC).trans_le hsize)

/-- Transfer of `P_ne_NP_of_yesSet_pow_hard`: barely superlinear circuit lower bounds for
`MCSP[fun m => m ^ k]` imply `P ≠ NP`. -/
theorem p_ne_np_of_mcsp_hard (k : ℕ)
    (h : ∀ c > 0, ∃ n : ℕ, ∀ C : DeMorganCircuit (2 ^ n),
      DecidesMCSPSlice C (fun m => m ^ k) → 2 ^ n * c * (n + 1) ^ c < C.size) :
    P ≠ NP := by
  rw [p_eq, np_eq]
  refine P_ne_NP_of_yesSet_pow_hard k fun c hc_pos => ?_
  obtain ⟨n, hlb⟩ := h c hc_pos
  refine ⟨n, ?_⟩
  by_contra! hle
  obtain ⟨C, hC, hsize⟩ := complexity_le_iff.mp hle
  exact (lt_irrefl _) ((hlb C (decidesMCSPSlice_iff.mpr hC)).trans_le hsize)

end ComplexityAbstracts.MagnificationBridge
