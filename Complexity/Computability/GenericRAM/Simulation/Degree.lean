/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.GenericRAM.Simulation.Run
public import Complexity.Computability.GenericRAM.Native.Degree

/-!
# Explicit-degree overhead of the finite-state RAM simulation

When every primitive certificate of a RAM model has degree `D ≥ 3`
(`Model.NativePrimitives.HasDegree`), one step of the native finite-state simulator has degree `D`
in the encoded runtime configuration and state. The `3` is the sparse-memory scan, which is cubic in
the encoded memory (`SparseMemory.scanTime_le_cube`). A clocked run of `n` steps through states of
encoded length at most `B` therefore costs `O(|input| + (n + 1) · ((B + 1) ^ D + (log n + 1) ^ 2))`
machine steps, and whole-run transport inherits this bound with every constant outside the degree.

These are the degree analogues of the `*_isPolynomial` lemmas of
`Complexity.Computability.GenericRAM.Simulation.Run`, which give polynomial bounds of unnamed
degree.

## Main results

* `Cslib.GenericRAM.FiniteState.stepCertificate_hasDegree`,
  `Cslib.GenericRAM.FiniteState.roundCertificate_hasDegree`: one simulated step has degree `D`.
* `Cslib.GenericRAM.FiniteState.runTime_le`, `Cslib.GenericRAM.FiniteState.runSpace_le`: explicit
  bounds on a clocked run from per-round bounds and a bound on the visited states.
* `Cslib.GenericRAM.FiniteState.transport_inO_of_hasDegree`: whole-run transport with time
  `O(… + (steps + 1) · ((B + 1) ^ D + (log steps + 1) ^ 2))`.

## References

* [S. A. Cook and R. A. Reckhow, *Time bounded random access machines*][CookReckhow1973]
-/

@[expose] public section

namespace Cslib.GenericRAM.FiniteState

open Turing.MultiTapeTM NativeCertificate

variable {M : Model.{0, 0, 0, 0}} {r : ℕ} {α : Type} {ei : α ↪ List Bool} {D : ℕ}

namespace Native

variable {s : α → FiniteState M r} {k : α → M.Config} {v : α → M.Value}

theorem fields_hasDegree (enc : M.Encoding) (c : NativeCertificate s ei (encoding enc))
    (hc : c.HasDegree D) : (fields enc c).HasDegree D :=
  post_hasDegree c _ hc

theorem register_hasDegree (enc : M.Encoding) (c : NativeCertificate s ei (encoding enc))
    (i : Fin r) (hc : c.HasDegree D) : (register enc c i).HasDegree D :=
  post_hasDegree _ _ (fst_hasDegree _ (snd_hasDegree _ (fields_hasDegree enc c hc)))

theorem operands_hasDegree (enc : M.Encoding) (c : NativeCertificate s ei (encoding enc))
    {n : ℕ} (args : Fin n → Fin r) (hc : c.HasDegree D) :
    (operands enc c args).HasDegree D :=
  post_hasDegree _ _ (fst_hasDegree _ (snd_hasDegree _ (fields_hasDegree enc c hc)))

theorem setCertificate_hasDegree (enc : M.Encoding)
    (c : NativeCertificate s ei (encoding enc)) (d : Fin r)
    (value : NativeCertificate v ei enc.value) (hc : c.HasDegree D) (hv : value.HasDegree D) :
    (setCertificate enc c d value).HasDegree D := by
  have hfs := fields_hasDegree enc c hc
  exact post_hasDegree _ (pack enc).computes (prod_hasDegree _ _ (fst_hasDegree _ hfs)
    (prod_hasDegree _ _ (post_hasDegree _ _ (prod_hasDegree _ _
      (fst_hasDegree _ (snd_hasDegree _ hfs)) hv)) (snd_hasDegree _ (snd_hasDegree _ hfs))))

theorem moveCertificate_hasDegree (enc : M.Encoding) (N : M.NativePrimitives enc)
    (config : NativeCertificate k ei enc.config) (c : NativeCertificate s ei (encoding enc))
    (d : Fin r) (value : NativeCertificate v ei enc.value) (hD : 1 ≤ D)
    (hN : N.HasDegree D) (hk : config.HasDegree D) (hc : c.HasDegree D)
    (hv : value.HasDegree D) :
    (moveCertificate enc N config c d value).HasDegree D :=
  branch_hasDegree _ _ _
    (comp_hasDegree N.validMove (prod config value) hN.validMove (prod_hasDegree _ _ hk hv))
    (some_hasDegree _ (setCertificate_hasDegree enc c d value hc hv))
    (const_hasDegree none hD)

/-- The raw sparse-memory lookup is cubic in time and linear in space. -/
theorem readRaw_hasDegree (enc : M.Encoding) (hD : 3 ≤ D) :
    (⟨SparseMemory.readTime enc.address enc.value, SparseMemory.readSpace enc.address enc.value,
      SparseMemory.read_inO enc.address enc.value⟩ :
        NativeCertificate
          (fun (((address, memory), defaultValue) :
              (M.Address × SparseMemory M.Address M.Value) × M.Value) =>
            SparseMemory.read defaultValue address memory) _ _).HasDegree D := by
  refine hasDegree_of_space_linear _ (DegreeBounded.mono_deg ⟨32, fun q => ?_⟩ hD)
    ⟨32, fun q => ?_⟩ (by omega)
  · have hq : (SparseMemory.queryEncoding enc.address enc.value q.1).length ≤
        (SparseMemory.readEncoding enc.address enc.value q).length := by
      simp only [SparseMemory.readEncoding, length_encPair]; omega
    have hp := Nat.pow_le_pow_left (Nat.add_le_add_right hq 1) 3
    have ht := SparseMemory.scanTime_le_cube enc.address enc.value q.1
    have he : (SparseMemory.readEncoding enc.address enc.value q).length ≤
        ((SparseMemory.readEncoding enc.address enc.value q).length + 1) ^ 3 := by
      ring_nf; omega
    unfold SparseMemory.readTime
    nlinarith
  · have hs := SparseMemory.scanSpace_le_linear enc.address enc.value q.1
    simp only [SparseMemory.readSpace, SparseMemory.readEncoding,
      length_encPair, pow_one] at hs ⊢
    omega

/-- The raw sparse-memory update is cubic in time and linear in space. -/
theorem writeRaw_hasDegree (enc : M.Encoding) (hD : 3 ≤ D) :
    (⟨SparseMemory.writeTime enc.address enc.value, SparseMemory.writeSpace enc.address enc.value,
      SparseMemory.insert_inO enc.address enc.value⟩ :
        NativeCertificate
          (fun (((address, value), memory) :
              (M.Address × M.Value) × SparseMemory M.Address M.Value) =>
            memory.insert address value) _ _).HasDegree D := by
  refine hasDegree_of_space_linear _ (DegreeBounded.mono_deg ⟨33, fun q => ?_⟩ hD)
    ⟨33, fun q => ?_⟩ (by omega)
  · have hq : (SparseMemory.queryEncoding enc.address enc.value (q.1.1, q.2)).length ≤
        (SparseMemory.writeEncoding enc.address enc.value q).length := by
      simp only [SparseMemory.queryEncoding, SparseMemory.writeEncoding, length_encPair]
      omega
    have hp := Nat.pow_le_pow_left (Nat.add_le_add_right hq 1) 3
    have ht := SparseMemory.scanTime_le_cube enc.address enc.value (q.1.1, q.2)
    have he : (SparseMemory.writeEncoding enc.address enc.value q).length ≤
        ((SparseMemory.writeEncoding enc.address enc.value q).length + 1) ^ 3 := by
      ring_nf; omega
    unfold SparseMemory.writeTime
    nlinarith
  · have hs := SparseMemory.scanSpace_le_linear enc.address enc.value (q.1.1, q.2)
    simp only [SparseMemory.writeSpace, SparseMemory.queryEncoding,
      SparseMemory.writeEncoding, length_encPair, pow_one] at hs ⊢
    omega

theorem readCertificate_hasDegree (enc : M.Encoding)
    (c : NativeCertificate s ei (encoding enc))
    {a : α → M.Address} (address : NativeCertificate a ei enc.address) (hD : 3 ≤ D)
    (hc : c.HasDegree D) (ha : address.HasDegree D) :
    (readCertificate enc c address).HasDegree D := by
  have hfs := fields_hasDegree enc c hc
  exact comp_hasDegree _ _ (readRaw_hasDegree enc hD)
    (prod_hasDegree _ _ (prod_hasDegree _ _ ha
      (snd_hasDegree _ (snd_hasDegree _ (snd_hasDegree _ hfs))))
      (fst_hasDegree _ (snd_hasDegree _ (snd_hasDegree _ hfs))))

theorem writeCertificate_hasDegree (enc : M.Encoding)
    (c : NativeCertificate s ei (encoding enc))
    {a : α → M.Address} (address : NativeCertificate a ei enc.address)
    (value : NativeCertificate v ei enc.value) (hD : 3 ≤ D)
    (hc : c.HasDegree D) (ha : address.HasDegree D) (hv : value.HasDegree D) :
    (writeCertificate enc c address value).HasDegree D := by
  have hfs := fields_hasDegree enc c hc
  have hmem := comp_hasDegree _ _ (writeRaw_hasDegree enc hD)
    (prod_hasDegree _ _ (prod_hasDegree _ _ ha hv)
      (snd_hasDegree _ (snd_hasDegree _ (snd_hasDegree _ hfs))))
  exact post_hasDegree _ (pack enc).computes (prod_hasDegree _ _ (fst_hasDegree _ hfs)
    (prod_hasDegree _ _ (fst_hasDegree _ (snd_hasDegree _ hfs))
      (prod_hasDegree _ _ (fst_hasDegree _ (snd_hasDegree _ (snd_hasDegree _ hfs))) hmem)))

theorem evalOpCertificate_hasDegree (enc : M.Encoding)
    (N : M.NativePrimitives enc) (config : NativeCertificate k ei enc.config)
    (c : NativeCertificate s ei (encoding enc)) (o : Op M r) (hD : 3 ≤ D)
    (hN : N.HasDegree D) (hk : config.HasDegree D) (hc : c.HasDegree D) :
    (evalOpCertificate enc N config c o).HasDegree D := by
  have h1 : 1 ≤ D := by omega
  cases o with
  | const d literal =>
    refine (option_hasDegree _ _ _
      (comp_hasDegree _ _ (hN.constant literal) hk)
      (const_hasDegree none h1)
      (some_hasDegree _ (setCertificate_hasDegree enc _ d _
        (pull_hasDegree c hc h1) (payload_hasDegree ei enc.value h1))) h1).of_eq _ rfl rfl
      fun a => ?_
    simp only [Function.comp_apply, evalOp]
    cases M.checkedConstant literal (k a) <;> rfl
  | copy d src =>
    exact moveCertificate_hasDegree enc N config c d (register enc c src) h1 hN hk hc
      (register_hasDegree enc c src hc)
  | alu op d args =>
    refine (option_hasDegree _ _ _
      (comp_hasDegree _ _ (hN.operation op) (prod_hasDegree _ _ hk
        (operands_hasDegree enc c args hc)))
      (const_hasDegree none h1)
      (some_hasDegree _ (setCertificate_hasDegree enc _ d _
        (pull_hasDegree c hc h1) (payload_hasDegree ei enc.value h1))) h1).of_eq _ rfl rfl
      fun a => ?_
    simp only [Function.comp_apply, evalOp]
    cases M.checkedOp op (k a, (s a).regs ∘ args) <;> rfl
  | load d a =>
    have hpullC := pull_hasDegree (ed := enc.address) c hc h1
    have hpullK := pull_hasDegree (ed := enc.address) config hk h1
    have hpay := payload_hasDegree ei enc.address h1
    refine (option_hasDegree _ _ _
      (comp_hasDegree _ _ hN.address (prod_hasDegree _ _ hk (register_hasDegree enc c a hc)))
      (const_hasDegree none h1)
      (moveCertificate_hasDegree enc N _ _ d _ h1 hN hpullK hpullC
        (readCertificate_hasDegree enc _ _ hD hpullC hpay)) h1).of_eq _ rfl rfl fun x => ?_
    simp only [Function.comp_apply, evalOp]
    cases M.address (k x) ((s x).regs a) <;> rfl
  | store a src =>
    have hpullC := pull_hasDegree (ed := enc.address) c hc h1
    have hpullK := pull_hasDegree (ed := enc.address) config hk h1
    have hpay := payload_hasDegree ei enc.address h1
    refine (option_hasDegree _ _ _
      (comp_hasDegree _ _ hN.address (prod_hasDegree _ _ hk (register_hasDegree enc c a hc)))
      (const_hasDegree none h1)
      (branch_hasDegree _ _ _
        (comp_hasDegree _ _ hN.validMove (prod_hasDegree _ _ hpullK
          (register_hasDegree enc _ src hpullC)))
        (some_hasDegree _ (writeCertificate_hasDegree enc _ _ _ hD hpullC hpay
          (register_hasDegree enc _ src hpullC)))
        (const_hasDegree none h1)) h1).of_eq _ rfl rfl fun x => ?_
    simp only [Function.comp_apply, evalOp]
    cases M.address (k x) ((s x).regs a) <;> rfl

theorem resumeCertificate_hasDegree (enc : M.Encoding) (N : M.NativePrimitives enc)
    (config : NativeCertificate k ei enc.config) (c : NativeCertificate s ei (encoding enc))
    (pc : ℕ) (hD : 1 ≤ D) (hN : N.HasDegree D) (hk : config.HasDegree D)
    (hc : c.HasDegree D) :
    (resumeCertificate enc N config c pc).HasDegree D :=
  branch_hasDegree _ _ _
    (comp_hasDegree _ _ hN.validPC (prod_hasDegree _ _ hk (const_hasDegree pc hD)))
    (some_hasDegree _ (inl_hasDegree _ _ (post_hasDegree _ (pack enc).computes (prod_hasDegree _ _
      (const_hasDegree pc hD) (snd_hasDegree _ (fields_hasDegree enc c hc))))))
    (const_hasDegree none hD)

theorem evalInstrCertificate_hasDegree (enc : M.Encoding)
    (N : M.NativePrimitives enc) (config : NativeCertificate k ei enc.config)
    (c : NativeCertificate s ei (encoding enc)) (nextPC : ℕ) (i : Instr M r) (hD : 3 ≤ D)
    (hN : N.HasDegree D) (hk : config.HasDegree D) (hc : c.HasDegree D) :
    (evalInstrCertificate enc N config c nextPC i).HasDegree D := by
  have h1 : 1 ≤ D := by omega
  cases i with
  | op o =>
    refine (option_hasDegree _ _ _
      (evalOpCertificate_hasDegree enc N config c o hD hN hk hc)
      (const_hasDegree none h1)
      (resumeCertificate_hasDegree enc N _ _ nextPC h1 hN
        (pull_hasDegree config hk h1) (payload_hasDegree ei (encoding enc) h1)) h1).of_eq _
      rfl rfl fun a => ?_
    simp only [evalInstr]
    cases evalOp (k a) o (s a) <;> rfl
  | jump target =>
    exact resumeCertificate_hasDegree enc N config c target h1 hN hk hc
  | branch test target =>
    cases test with
    | test f args =>
      have hpullK := pull_hasDegree (ed := encBool) config hk h1
      have hpullC := pull_hasDegree (ed := encBool) c hc h1
      refine (option_hasDegree _ _ _
        (comp_hasDegree _ _ (hN.test f) (prod_hasDegree _ _ hk
          (operands_hasDegree enc c args hc)))
        (const_hasDegree none h1)
        (branch_hasDegree _ _ _
          (payload_hasDegree ei encBool h1)
          (resumeCertificate_hasDegree enc N _ _ target h1 hN hpullK hpullC)
          (resumeCertificate_hasDegree enc N _ _ nextPC h1 hN hpullK hpullC)) h1).of_eq _
        rfl rfl fun a => ?_
      simp only [Function.comp_apply, evalInstr]
      cases h : M.evalTest (k a) f ((s a).regs ∘ args) with
      | none => rfl
      | some b => cases b <;> rfl
  | halt idx =>
    exact branch_hasDegree _ _ _
      (comp_hasDegree _ _ hN.validMove (prod_hasDegree _ _ hk (register_hasDegree enc c idx hc)))
      (some_hasDegree _ (inr_hasDegree _ _ (register_hasDegree enc c idx hc)))
      (const_hasDegree none h1)

theorem pcEquals_hasDegree (enc : M.Encoding) (c : NativeCertificate s ei (encoding enc))
    (pc : ℕ) (hD : 2 ≤ D) (hc : c.HasDegree D) :
    (pcEquals enc c pc).HasDegree D := by
  have heq : (⟨fun p : ℕ × ℕ => ((encNat p.1).length + 1) *
      ((encNat p.1).length + (encNat p.2).length + 1),
    fun p : ℕ × ℕ => (encPair encNat encNat p).length,
    ComputableInO.eq encNat⟩ : NativeCertificate (fun p : ℕ × ℕ => decide (p.1 = p.2))
      (encPair encNat encNat) encBool).HasDegree D := by
    refine hasDegree_of_space_linear _ (DegreeBounded.mono_deg ⟨1, fun p => ?_⟩ hD)
      ⟨1, fun p => by simp⟩ (by omega)
    simp only [length_encPair]
    nlinarith
  exact comp_hasDegree _ _ heq (prod_hasDegree _ _ (fst_hasDegree _ (fields_hasDegree enc c hc))
    (const_hasDegree pc (by omega)))

theorem dispatchCertificate_hasDegree (enc : M.Encoding)
    (N : M.NativePrimitives enc) (config : NativeCertificate k ei enc.config)
    (c : NativeCertificate s ei (encoding enc)) (p : Program M r) (pc : ℕ) (hD : 3 ≤ D)
    (hN : N.HasDegree D) (hk : config.HasDegree D) (hc : c.HasDegree D) :
    (dispatchCertificate enc N config c p pc).HasDegree D := by
  induction p generalizing pc with
  | nil => exact const_hasDegree none (by omega)
  | cons i p ih =>
    refine congr_hasDegree _ _ ?_
    exact (branch_hasDegree _ _ _
      (pcEquals_hasDegree enc c pc (by omega) hc)
      (evalInstrCertificate_hasDegree enc N config c (pc + 1) i hD hN hk hc)
      (ih (pc + 1)))

end Native

/-- **One simulated step has degree `D`** when every primitive certificate has degree `D ≥ 3`. -/
theorem stepCertificate_hasDegree (enc : M.Encoding) (N : M.NativePrimitives enc)
    (p : Program M r) (hN : N.HasDegree D) (hD : 3 ≤ D) :
    (stepCertificate enc N p).HasDegree D := by
  have h1 : 1 ≤ D := by omega
  have hcfg := linear_hasDegree (ComputableInO.fst enc.config (encoding (M := M) (r := r) enc)) h1
  have hst := linear_hasDegree (ComputableInO.snd enc.config (encoding (M := M) (r := r) enc)) h1
  exact branch_hasDegree _ _ _
    (comp_hasDegree _ _ hN.validPC
      (prod_hasDegree _ _ hcfg (fst_hasDegree _ (Native.fields_hasDegree enc _ hst))))
    (Native.dispatchCertificate_hasDegree enc N _ _ p 0 hD hN hcfg hst)
    (const_hasDegree none h1)

/-- **One clocked round of the simulator has degree `D`** when every primitive certificate has
degree `D ≥ 3`. -/
theorem roundCertificate_hasDegree (enc : M.Encoding) (N : M.NativePrimitives enc)
    (p : Program M r) (hN : N.HasDegree D) (hD : 3 ≤ D) :
    (roundCertificate enc N p).HasDegree D := by
  have h1 : 1 ≤ D := by omega
  have hcont : (continuingCertificate (M := M) (r := r) enc).HasDegree D :=
    hasDegree_of_space_linear _ (DegreeBounded.self.mono_deg h1) DegreeBounded.self h1
  have hres : (stepResultCertificate enc N p).HasDegree D :=
    (option_hasDegree _ _ _
      (comp_hasDegree _ _ hcont (snd_hasDegree _ (linear_hasDegree
        (ComputableInO.of_eq (f := fun x : M.Config × Result M r => x) fun _ => rfl) h1)))
      (snd_hasDegree _ (linear_hasDegree _ h1))
      (comp_hasDegree _ _ (stepCertificate_hasDegree enc N p hN hD)
        (prod_hasDegree _ _ (fst_hasDegree _ (fst_hasDegree _ (linear_hasDegree
          (ComputableInO.of_eq (f := fun x : (M.Config × Result M r) × FiniteState M r => x)
            fun _ => rfl) h1)))
          (snd_hasDegree _ (linear_hasDegree _ h1)))) h1).of_eq _ rfl rfl
      fun q => (stepResult_eq q.1 p q.2).symm
  exact prod_hasDegree _ _ (fst_hasDegree _ (linear_hasDegree _ h1)) hres

/-! ## Clocked runs with explicit bounds -/

/-- The loop state after `j` rounds from a continuing state has the encoded length of the runtime
configuration and the `j`-step outcome. -/
theorem length_loopEncoding_iterate_round (enc : M.Encoding) (p : Program M r) (j : ℕ)
    (k : M.Config) (s : FiniteState M r) :
    (loopEncoding enc ((round p)^[j] (k, Option.some (.inl s)))).length =
      2 * (enc.config k).length + 1 + (resultEncoding enc (run k p j s)).length := by
  rw [iterate_round_inl, length_encPair]

/-- **Explicit clocked run time.** If every round costs at most `C (ℓ + 1) ^ D` on a loop state of
encoded length `ℓ`, and the outcomes of the first `n` steps have encoded length at most `B`, then
`n` clocked steps cost at most `3 |input| + (n + 1) (C X ^ D + X + (|n| + 1) ^ 2)`, where
`X = 2 |k| + B + 2` bounds the encoded loop states plus one. -/
theorem runTime_le (enc : M.Encoding) (N : M.NativePrimitives enc) (p : Program M r) {C : ℕ}
    (hround : ∀ x, (roundCertificate enc N p).time x ≤ C * ((loopEncoding enc x).length + 1) ^ D)
    (n : ℕ) (k : M.Config) (s : FiniteState M r) {B : ℕ}
    (hB : ∀ j ≤ n, (resultEncoding enc (run k p j s)).length ≤ B) :
    runTime enc N p (n, (k, s)) ≤ 3 * (runInputEncoding enc (n, (k, s))).length +
      (n + 1) * (C * (2 * (enc.config k).length + B + 2) ^ D +
        (2 * (enc.config k).length + B + 2) + ((encNat n).length + 1) ^ 2) := by
  have hT := maxRoundTime_le (roundCertificate enc N p) n (k, Option.some (.inl s))
    (R := C * (2 * (enc.config k).length + B + 2) ^ D) fun j hj => by
      refine (hround _).trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left ?_ D))
      have := hB j hj
      rw [length_loopEncoding_iterate_round]
      omega
  have hL := maxStateLength_le (encPair enc.config (resultEncoding enc)) (round p) n
    (k, Option.some (.inl s))
    (B := 2 * (enc.config k).length + B + 2) fun j hj => by
      have := hB j hj
      rw [length_loopEncoding_iterate_round]
      omega
  have hsum := Nat.mul_le_mul_left (n + 1) (Nat.add_le_add_right (Nat.add_le_add hT hL)
    (((encNat n).length + 1) ^ 2))
  simp only [runTime, runCertificate, congr_time, snd_time, iterate_time, initLoopCertificate,
    prod_time, fst_time, snd_time, some_time, inl_time, linear_time]
  omega

/-- **Explicit clocked run space.** The space analogue of `runTime_le`. -/
theorem runSpace_le (enc : M.Encoding) (N : M.NativePrimitives enc) (p : Program M r) {C : ℕ}
    (hround : ∀ x, (roundCertificate enc N p).space x ≤ C * ((loopEncoding enc x).length + 1) ^ D)
    (n : ℕ) (k : M.Config) (s : FiniteState M r) {B : ℕ}
    (hB : ∀ j ≤ n, (resultEncoding enc (run k p j s)).length ≤ B) :
    runSpace enc N p (n, (k, s)) ≤ 3 * (runInputEncoding enc (n, (k, s))).length +
      C * (2 * (enc.config k).length + B + 2) ^ D + (2 * (enc.config k).length + B + 2) +
        (encNat n).length := by
  have hS := maxRoundSpace_le (roundCertificate enc N p) n (k, Option.some (.inl s))
    (Q := C * (2 * (enc.config k).length + B + 2) ^ D) fun j hj => by
      refine (hround _).trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left ?_ D))
      have := hB j hj
      rw [length_loopEncoding_iterate_round]
      omega
  have hL := maxStateLength_le (encPair enc.config (resultEncoding enc)) (round p) n
    (k, Option.some (.inl s))
    (B := 2 * (enc.config k).length + B + 2) fun j hj => by
      have := hB j hj
      rw [length_loopEncoding_iterate_round]
      omega
  simp only [runSpace, runCertificate, congr_space, snd_space, iterate_space, initLoopCertificate,
    prod_space, fst_space, snd_space, some_space, inl_space, linear_space]
  omega

/-- **Whole-run transport with an explicit degree.** Suppose every primitive certificate of the
model has degree `D ≥ 3`, a halting run of `p` from `initState a` takes at most `steps a`
instructions, and the outcomes of its first `steps a` clocked steps have encoded length at most
`B a`. Then `f` is computable in time
`O(Tsteps + Tcfg + Tinit + |input| + (steps + 1) · (X ^ D + (|steps| + 1) ^ 2))`, where
`X = 2 |cfg| + B + 2` and `|input|` is the encoded length of `(steps, cfg, initState)`. Only the
constant factor is hidden. -/
theorem transport_inO_of_hasDegree (enc : M.Encoding) (N : M.NativePrimitives enc)
    (hN : N.HasDegree D) (hD : 3 ≤ D) (p : Program M r)
    {f : α → M.Value} {cfg : α → M.Config} {initState : α → FiniteState M r}
    {steps : α → ℕ}
    (cSteps : NativeCertificate steps ei encNat)
    (cCfg : NativeCertificate cfg ei enc.config)
    (cInit : NativeCertificate initState ei (encoding enc))
    (hExec : ∀ a, ∃ m ≤ steps a,
      GenericRAM.Executes (cfg a) p (initState a).denote (f a) m)
    {B : α → ℕ}
    (hOutLen : ∀ a, ∀ j ≤ steps a,
      (resultEncoding enc (run (cfg a) p j (initState a))).length ≤ B a) :
    ComputableInO f ei enc.value
      (fun a => cSteps.time a + cCfg.time a + cInit.time a +
        (runInputEncoding enc (steps a, (cfg a, initState a))).length +
        (steps a + 1) * ((2 * (enc.config (cfg a)).length + B a + 2) ^ D +
          ((encNat (steps a)).length + 1) ^ 2))
      (fun a => cSteps.space a + cCfg.space a + cInit.space a +
        (runInputEncoding enc (steps a, (cfg a, initState a))).length +
        (2 * (enc.config (cfg a)).length + B a + 2) ^ D + (encNat (steps a)).length) := by
  have hround := roundCertificate_hasDegree enc N p hN hD
  obtain ⟨Ct, hCt⟩ := hround.time
  obtain ⟨Cs, hCs⟩ := hround.space
  refine (transport_inO enc N p cSteps cCfg cInit hExec).mono (Ct + Cs + 4) (fun a => ?_)
    (fun a => ?_)
  · have hrun := runTime_le enc N p hCt (steps a) (cfg a) (initState a) (hOutLen a)
    set X := 2 * (enc.config (cfg a)).length + B a + 2
    have hX : X ≤ X ^ D := Nat.le_self_pow (by omega) X
    have hmul := Nat.mul_le_mul_left (steps a + 1)
      (show Ct * X ^ D + X + ((encNat (steps a)).length + 1) ^ 2 ≤
        (Ct + 1) * (X ^ D + ((encNat (steps a)).length + 1) ^ 2) by nlinarith)
    have hc : (steps a + 1) * ((Ct + 1) * (X ^ D + ((encNat (steps a)).length + 1) ^ 2)) ≤
        (Ct + Cs + 4) * ((steps a + 1) * (X ^ D + ((encNat (steps a)).length + 1) ^ 2)) := by
      rw [Nat.mul_left_comm]
      exact Nat.mul_le_mul_right _ (by omega)
    nlinarith
  · have hrun := runSpace_le enc N p hCs (steps a) (cfg a) (initState a) (hOutLen a)
    set X := 2 * (enc.config (cfg a)).length + B a + 2
    have hX : X ≤ X ^ D := Nat.le_self_pow (by omega) X
    nlinarith

end Cslib.GenericRAM.FiniteState
