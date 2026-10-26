/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.Encoding
import ComplexityAbstracts.Computation
import Complexity.Computability.MCSP.PartialETH
import Cslib.Computability.Circuit.Simulation

/-!
# Bridge for the Partial MCSP ETH-hardness formal abstract

Connects the self-contained definitions in `PartialMCSPAbstract.lean` (plain 3SAT formulas,
parameterized exponential/subexponential time bounds on upstream `Cslib` multi-tape Turing machines,
plain De Morgan circuits, and partial truth-table instances) to the theorems in
`Complexity.Computability.MCSP.PartialETH`, `Complexity.Computability.MCSP.Partial`, and
`Complexity.Computability.MCSP.PartialNP`.
-/

namespace ComplexityAbstracts.PartialMCSPBridge

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Complexity Cslib.Logic.PL
open Turing.MultiTapeTM
open ComplexityTests.Abstracts

/-! ### 3SAT and ETH equivalence -/

/-- Encode a CNF formula over `ℕ` as a list of clauses of `(ℕ × Bool)` literals. -/
def encodeCNF : List (List (ℕ × Bool)) → List Bool :=
  Encoding.encodeList (Encoding.encodeList (Encoding.encodePair Nat.bits (fun b => [b])))

theorem encodeCNF_injective : Function.Injective encodeCNF :=
  Cslib.Complexity.encCNF.injective

/-- Injective framed binary encoding of CNF formulas, matching `Cslib.Complexity.encCNF`. -/
def encCNF : List (List (ℕ × Bool)) ↪ List Bool :=
  ⟨encodeCNF, encodeCNF_injective⟩

/-- Quantifier-based satisfiability of a CNF formula represented as `List (List (ℕ × Bool))`. -/
def Satisfiable (φ : List (List (ℕ × Bool))) : Prop :=
  ∃ τ : ℕ → Bool, ∀ c ∈ φ, ∃ l ∈ c, τ l.1 = l.2

theorem satisfiable_iff (φ : List (List (ℕ × Bool))) :
    Satisfiable φ ↔ CNF.Satisfiable (V := ℕ) φ := by
  simp only [Satisfiable, CNF.Satisfiable, CNF.eval_eq_true_iff, Clause.eval_eq_true_iff]

/-- 3SAT: satisfiable CNF formulas whose clauses have at most three literal occurrences. -/
def ThreeSAT : Set (List (List (ℕ × Bool))) :=
  {φ | (∀ c ∈ φ, c.length ≤ 3) ∧ Satisfiable φ}

theorem threeSAT_eq : ThreeSAT = Cslib.Complexity.ThreeSAT := by
  ext φ
  exact and_congr_right fun _ => satisfiable_iff φ

/-- Number of distinct variables occurring in a CNF formula `φ`. -/
def numVars (φ : List (List (ℕ × Bool))) : ℕ :=
  (φ.flatten.map Prod.fst).toFinset.card

theorem numVars_eq : numVars = CNF.numVars (V := ℕ) :=
  rfl

/-- Parameterized time bound `O(T a)` on upstream `Cslib` deterministic multi-tape Turing
machines. -/
def DecidableInTimeO {α : Type} (A : Set α) (enc : α ↪ List Bool) (T : α → ℝ) : Prop :=
  ∃ c : ℕ, ∃ t s : α → ℕ,
    (∀ a, (t a : ℝ) ≤ c * T a + c) ∧
    Turing.MultiTapeTM.DecidableInTimeAndSpace A enc t s

/-- Parameterized exponential time `O(2 ^ (δ * μ a) * (|enc a| + 1) ^ e)`. -/
def DecidableInExpTime {α : Type} (A : Set α) (enc : α ↪ List Bool) (μ : α → ℕ) (δ : ℝ) : Prop :=
  ∃ e : ℕ, DecidableInTimeO A enc fun a => 2 ^ (δ * μ a) * ((enc a).length + 1) ^ e

/-- Subexponential time in parameter `μ`: decidable in time `2 ^ (δ * μ a) * poly(|enc a|)` for
every `δ > 0`. -/
def DecidableInSubexpTime {α : Type} (A : Set α) (enc : α ↪ List Bool) (μ : α → ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → DecidableInExpTime A enc μ δ

/-- The Exponential Time Hypothesis (`ETH`): for some `δ > 0`, `3SAT` is not decidable in time
`2 ^ (δ * n) * poly(|encCNF φ|)` where `n = numVars φ`. -/
def ETH : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ¬DecidableInExpTime ThreeSAT encCNF numVars δ

theorem eth_iff : ETH ↔ Cslib.Complexity.ETH := by
  simp only [ETH, Cslib.Complexity.ETH, threeSAT_eq, numVars_eq]
  rfl

/-! ### De Morgan circuits and Partial MCSP -/

/-- A single-output Boolean circuit over the De Morgan basis. -/
abbrev DeMorganCircuit (n : ℕ) :=
  Circuit signature n 1

/-- Evaluate a single-output De Morgan circuit `C` on input `x`. -/
def evalCircuit {n : ℕ} (C : DeMorganCircuit n) (x : Fin n → Bool) : Bool :=
  C.eval interpretation x 0

/-- Number of binary AND and OR gates in `C` (NOT and constant gates have weight `0`). -/
def binaryGateCount {n : ℕ} (C : DeMorganCircuit n) : ℕ :=
  C.program.cost (fun op : Cslib.Circuits.Boolean.Op =>
    match op with | .and | .or => 1 | .const _ | .not => 0)

theorem binaryGateCount_eq {n : ℕ} (C : DeMorganCircuit n) :
    binaryGateCount C = C.program.cost binaryCost :=
  rfl

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

/-- Encode an optional Boolean: `none` as `[]` and `some b` as `[true, b]`. -/
def encodeOptionBool (o : Option Bool) : List Bool :=
  o.elim [] (fun b => [true, b])

/-- Encode a raw pair `(tableList, threshold)` with unary threshold. -/
def encodeRawUnary (p : List (Option Bool) × ℕ) : List Bool :=
  Encoding.encodePair (Encoding.encodeList encodeOptionBool)
    (fun s => List.replicate s true) p

/-- Encode a raw pair `(tableList, threshold)` with binary threshold. -/
def encodeRawBinary (p : List (Option Bool) × ℕ) : List Bool :=
  Encoding.encodePair (Encoding.encodeList encodeOptionBool) Nat.bits p

theorem eq_of_encodeRawUnary_eq {n₁ n₂ : ℕ} {T₁ : Fin (2 ^ n₁) → Option Bool}
    {T₂ : Fin (2 ^ n₂) → Option Bool} {s₁ s₂ : ℕ}
    (h : encodeRawUnary (List.ofFn T₁, s₁) = encodeRawUnary (List.ofFn T₂, s₂)) :
    (⟨n₁, T₁, s₁⟩ : PartialMCSP.Instance) = ⟨n₂, T₂, s₂⟩ :=
  PartialMCSP.enc.injective h

theorem eq_of_encodeRawBinary_eq {n₁ n₂ : ℕ} {T₁ : Fin (2 ^ n₁) → Option Bool}
    {T₂ : Fin (2 ^ n₂) → Option Bool} {s₁ s₂ : ℕ}
    (h : encodeRawBinary (List.ofFn T₁, s₁) = encodeRawBinary (List.ofFn T₂, s₂)) :
    (⟨n₁, T₁, s₁⟩ : PartialMCSP.Instance) = ⟨n₂, T₂, s₂⟩ :=
  PartialMCSP.encBinary.injective h

/-! ### Transfer along an instance equivalence -/

theorem decidableInTimeO_of_equiv {α β : Type} (e : α ≃ β)
    {A : Set α} {B : Set β} (hAB : ∀ x, x ∈ A ↔ e x ∈ B)
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} (henc : ∀ x, encA x = encB (e x))
    {TA : α → ℝ} {TB : β → ℝ} (hT : ∀ x, TA x = TB (e x))
    (h : DecidableInTimeO A encA TA) :
    Cslib.Complexity.DecidableInTimeO B encB TB := by
  rcases h with ⟨c, t, s, ht, k, State, hfin, tm, htm⟩
  refine ⟨c, fun y => t (e.symm y), fun y => s (e.symm y),
    fun y => by simpa [hT (e.symm y)] using ht (e.symm y),
    k, State, hfin, tm, fun y => ?_⟩
  have h1 := htm (e.symm y)
  have h2 : indicator A (e.symm y) = indicator B y := by
    classical
    simp only [indicator, hAB (e.symm y), Equiv.apply_symm_apply]
  simpa only [henc (e.symm y), Equiv.apply_symm_apply, h2] using h1

theorem decidableInSubexpTime_of_equiv {α β : Type} (e : α ≃ β)
    {A : Set α} {B : Set β} (hAB : ∀ x, x ∈ A ↔ e x ∈ B)
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} (henc : ∀ x, encA x = encB (e x))
    {μA : α → ℕ} {μB : β → ℕ} (hμ : ∀ x, μA x = μB (e x))
    (h : DecidableInSubexpTime A encA μA) :
    Cslib.Complexity.DecidableInSubexpTime B encB μB := by
  intro δ hδ
  obtain ⟨d, hd⟩ := h δ hδ
  refine ⟨d, decidableInTimeO_of_equiv e hAB henc (fun x => ?_) hd⟩
  simp only [hμ x, henc x]

/-- Agreement of a single-output De Morgan circuit `C` with the partial truth table of `x`. -/
def AgreesWithCslib (x : PartialMCSP.Instance) (C : DeMorganCircuit x.arity) : Prop :=
  ∀ y : Fin x.arity → Bool, ∀ b : Bool,
    x.table (tableIndex x.arity y) = some b → evalCircuit C y = b

theorem mem_partialMCSP_iff (x : PartialMCSP.Instance) :
    (∃ C : DeMorganCircuit x.arity, C.size ≤ x.threshold ∧ AgreesWithCslib x C) ↔
      x ∈ Cslib.PartialMCSP :=
  PartialMCSP.mem_iff_exists_circuit.symm

theorem mem_partialMCSP_binaryGate_iff (x : PartialMCSP.Instance) :
    (∃ C : DeMorganCircuit x.arity, binaryGateCount C ≤ x.threshold ∧ AgreesWithCslib x C) ↔
      x ∈ Cslib.PartialMCSP.BinaryGate :=
  Iff.rfl

/-- Transfer of `ETH.not_decidableInSubexpTime_PartialMCSP` (unary threshold encoding). -/
theorem not_decidableInSubexpTime_partialMCSP {Inst : Type}
    (e : Inst ≃ PartialMCSP.Instance)
    {A : Set Inst} (hA : ∀ x, x ∈ A ↔
      ∃ C : DeMorganCircuit (e x).arity, C.size ≤ (e x).threshold ∧ AgreesWithCslib (e x) C)
    {enc : Inst ↪ List Bool} (henc : ∀ x, enc x = PartialMCSP.enc (e x))
    {μ : Inst → ℕ} (hμ : ∀ x, μ x = (e x).arity * Nat.log 2 (e x).arity)
    (hETH : ETH) :
    ¬DecidableInSubexpTime A enc μ := by
  intro hsub
  have hA' : ∀ x, x ∈ A ↔ e x ∈ Cslib.PartialMCSP :=
    fun x => (hA x).trans (mem_partialMCSP_iff (e x))
  exact (eth_iff.mp hETH).not_decidableInSubexpTime_PartialMCSP
    (decidableInSubexpTime_of_equiv e hA' henc hμ hsub)

/-- Transfer of `ETH.not_decidableInSubexpTime_PartialMCSP_tableSize` (unary threshold encoding). -/
theorem not_decidableInSubexpTime_partialMCSP_tableSize {Inst : Type}
    (e : Inst ≃ PartialMCSP.Instance)
    {A : Set Inst} (hA : ∀ x, x ∈ A ↔
      ∃ C : DeMorganCircuit (e x).arity, C.size ≤ (e x).threshold ∧ AgreesWithCslib (e x) C)
    {enc : Inst ↪ List Bool} (henc : ∀ x, enc x = PartialMCSP.enc (e x))
    {μ : Inst → ℕ}
    (hμ : ∀ x, μ x = Nat.log 2 (2 ^ (e x).arity) * Nat.log 2 (Nat.log 2 (2 ^ (e x).arity)))
    (hETH : ETH) :
    ¬DecidableInSubexpTime A enc μ := by
  intro hsub
  have hA' : ∀ x, x ∈ A ↔ e x ∈ Cslib.PartialMCSP :=
    fun x => (hA x).trans (mem_partialMCSP_iff (e x))
  exact (eth_iff.mp hETH).not_decidableInSubexpTime_PartialMCSP_tableSize
    (decidableInSubexpTime_of_equiv e hA' henc hμ hsub)

/-- Transfer of `ETH.not_decidableInSubexpTime_PartialMCSP_encBinary` (binary threshold
encoding). -/
theorem not_decidableInSubexpTime_partialMCSP_encBinary {Inst : Type}
    (e : Inst ≃ PartialMCSP.Instance)
    {A : Set Inst} (hA : ∀ x, x ∈ A ↔
      ∃ C : DeMorganCircuit (e x).arity, C.size ≤ (e x).threshold ∧ AgreesWithCslib (e x) C)
    {enc : Inst ↪ List Bool} (henc : ∀ x, enc x = PartialMCSP.encBinary (e x))
    {μ : Inst → ℕ} (hμ : ∀ x, μ x = (e x).arity * Nat.log 2 (e x).arity)
    (hETH : ETH) :
    ¬DecidableInSubexpTime A enc μ := by
  intro hsub
  have hA' : ∀ x, x ∈ A ↔ e x ∈ Cslib.PartialMCSP :=
    fun x => (hA x).trans (mem_partialMCSP_iff (e x))
  exact (eth_iff.mp hETH).not_decidableInSubexpTime_PartialMCSP_encBinary
    (decidableInSubexpTime_of_equiv e hA' henc hμ hsub)

/-- Transfer of `ETH.not_decidableInSubexpTime_PartialMCSP_binaryGate` (Ilango's binary-gate cost
measure). -/
theorem not_decidableInSubexpTime_partialMCSPBinaryGate {Inst : Type}
    (e : Inst ≃ PartialMCSP.Instance)
    {A : Set Inst} (hA : ∀ x, x ∈ A ↔
      ∃ C : DeMorganCircuit (e x).arity,
        binaryGateCount C ≤ (e x).threshold ∧ AgreesWithCslib (e x) C)
    {enc : Inst ↪ List Bool} (henc : ∀ x, enc x = PartialMCSP.enc (e x))
    {μ : Inst → ℕ} (hμ : ∀ x, μ x = (e x).arity * Nat.log 2 (e x).arity)
    (hETH : ETH) :
    ¬DecidableInSubexpTime A enc μ := by
  intro hsub
  have hA' : ∀ x, x ∈ A ↔ e x ∈ Cslib.PartialMCSP.BinaryGate :=
    fun x => (hA x).trans (mem_partialMCSP_binaryGate_iff (e x))
  exact (eth_iff.mp hETH).not_decidableInSubexpTime_PartialMCSP_binaryGate
    (decidableInSubexpTime_of_equiv e hA' henc hμ hsub)

/-! ### Transfer of `NP` membership -/

/-- Fixed-length polynomial certificate verification. -/
def IsVerifier {α : Type} (enc : α ↪ List Bool) (p : Polynomial ℕ)
    (V : α × List Bool → Bool) (A : Set α) : Prop :=
  ∀ a, a ∈ A ↔ ∃ w : List Bool, w.length = p.eval (enc a).length ∧ V (a, w) = true

/-- The class `NP` with respect to instance encoding `enc`. -/
def NP {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    Computation.PolyTimeVerifier enc V ∧ IsVerifier enc p V A}

theorem mem_np_of_equiv {α β : Type} (e : α ≃ β)
    {A : Set α} {B : Set β} (hAB : ∀ x, x ∈ A ↔ e x ∈ B)
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} (henc : ∀ x, encA x = encB (e x))
    (hB : B ∈ Cslib.Complexity.NP encB) :
    A ∈ NP encA := by
  rw [Cslib.Complexity.mem_NP_iff_exists_computableInTimeAndSpaceOfLength] at hB
  rcases hB with ⟨p, V, t, s, ht, hs, ⟨k, State, hfin, tm, htm⟩, hver⟩
  refine ⟨p, fun xw => V (e xw.1, xw.2), ⟨t, s, ht, hs, k, State, hfin, tm, fun ⟨x, w⟩ => ?_⟩,
    fun x => ?_⟩
  · have hpair : Encoding.encPair encA Encoding.encBits (x, w) =
        Turing.MultiTapeTM.encPair encB Turing.MultiTapeTM.encBits (e x, w) := by
      change Encoding.frame (encA x) ++ w = frame (encB (e x)) ++ w
      rw [henc x]
      rfl
    have hbool : Encoding.encBool (V (e x, w)) =
        Turing.MultiTapeTM.encBool (V (e x, w)) :=
      rfl
    simpa only [hpair, hbool] using htm (e x, w)
  · rw [hAB x, hver (e x), henc x]

theorem partialMCSP_mem_NP {Inst : Type} (e : Inst ≃ PartialMCSP.Instance)
    {A : Set Inst} (hA : ∀ x, x ∈ A ↔
      ∃ C : DeMorganCircuit (e x).arity, C.size ≤ (e x).threshold ∧ AgreesWithCslib (e x) C)
    {enc : Inst ↪ List Bool} (henc : ∀ x, enc x = PartialMCSP.enc (e x)) :
    A ∈ NP enc :=
  mem_np_of_equiv e (fun x => (hA x).trans (mem_partialMCSP_iff (e x))) henc PartialMCSP.mem_NP

theorem partialMCSP_mem_NP_encBinary {Inst : Type} (e : Inst ≃ PartialMCSP.Instance)
    {A : Set Inst} (hA : ∀ x, x ∈ A ↔
      ∃ C : DeMorganCircuit (e x).arity, C.size ≤ (e x).threshold ∧ AgreesWithCslib (e x) C)
    {enc : Inst ↪ List Bool} (henc : ∀ x, enc x = PartialMCSP.encBinary (e x)) :
    A ∈ NP enc :=
  mem_np_of_equiv e (fun x => (hA x).trans (mem_partialMCSP_iff (e x))) henc
    PartialMCSP.mem_NP_encBinary

end ComplexityAbstracts.PartialMCSPBridge
