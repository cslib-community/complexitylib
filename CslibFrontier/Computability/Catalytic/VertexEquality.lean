/-
Copyright (c) 2026 Jonathan Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Katz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Catalytic.Comparison
public import CslibFrontier.Foundations.Data.Nat.CeilDiv
public import CslibFrontier.Foundations.Data.Nat.Radix
public import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Constant-frame two-stage catalytic vertex equality

In `CslibFrontier.Computability.Catalytic.Comparison`, `eqTest` compares two `ℓ`-digit vectors over
`ZMod (2 ^ k)` in eight single-endpoint visits while restoring a borrowed register and accumulator,
provided the caller retains the initial `k`-bit accumulator across the forward call (or starts it at
zero). When `n`-bit identifiers (`n = O(B)`) are chunked into `q₁ ≈ log₂ B`-bit digits, that
accumulator has `k₁ = Θ(log B)` bits; keeping `k₁` clean local bits in every suspended recursive
frame is too large at constant slack `d = O(1)`.

In Lemma 9.9 and Lemma 11.9 of [OpenAI2026LogSpace], short `log₂ B`-bit keys are instead compared
with only constant local frame data across four single-endpoint excursions by toggling a shared
`B`-bit table (`Cslib.Catalytic.keyTest` over `ZMod 2`). Any excursion that returns to the caller
and restores the shared catalytic memory, with return value independent of the incoming catalytic
contents, composes across repeated and nested visits.

This module combines two deterministic sum-of-squares stages (`addSqDist`) with `keyTest` into an
**exact, deterministic, salt-free** 64-excursion equality procedure for `n`-bit natural identifiers:

1. **Stage 1 (`4` visits per signed call).** Split `x, y < 2 ^ n` into `ℓ₁ = ⌈n / q₁⌉` chunks of
   `q₁ = max 1 ⌊log₂ B⌋` bits (`natChunkVec`). `addSqDist (±1)` shifts a shared `k₁`-bit
   accumulator `z₁` over `ZMod (2 ^ k₁)` (`k₁ = 2 · q₁ + ⌊log₂ ℓ₁⌋ + 1`) by `± ∑ᵢ (xᵢ - yᵢ)²`
   while restoring its borrowed `ℓ₁`-word register. Because `ℓ₁ · (2 ^ q₁ - 1)² < 2 ^ k₁`, the
   shifted value `z₁'` equals `z₁` iff `x = y`.
2. **Stage 2 (`16` visits per signed call).** Alternate `Stage 1 (+1)` and `Stage 1 (-1)` four
   times so `z₁` alternates `z₁, z₁', z₁, z₁'` without storing `z₁` locally. Feed those four
   `k₁`-bit values, split into `ℓ₂ = ⌈k₁ / q₂⌉` chunks of `q₂ = max 1 ⌊q₁ / 2⌋` bits, into an
   inner `addSqDist (±1)` over `ZMod (2 ^ k₂)`. When `n ≤ C_N · B`,
   `ℓ₂ ≤ ⌊log₂ (C_N + 1)⌋ + 11` is bounded by a constant independent of `B`, so
   `k₂ ≤ 2 · q₂ + O(1) ≤ log₂ B + O(1)` and `2 ^ k₂ = O(B)`.
3. **Stage 3 (`64` visits total).** Alternate `Stage 2 (+1)` and `Stage 2 (-1)` four times so the
   inner accumulator alternates `z₂, z₂', z₂, z₂'`, and apply `keyTest 1` on a shared table
   `W : ZMod (2 ^ k₂) → ZMod 2`, adding `1` into a single local `ZMod 2` bit iff `x = y` and
   restoring all three catalytic components `(T₁, T₂, W)`.

Across all `64` excursions the caller retains only the phase in `Fin 64` and one result bit in
`ZMod 2` (`7` local bits total, `card_vertexLocalFrame`), while the shared restored catalytic state
`VertexCatState B n` occupies `vertexCatBits B n ≤ vertexCatLinearConst C_N * (B + 1)` bits
whenever `n ≤ C_N * B` (`card_vertexCatState`, `vertexCatBits_le`).

Like `Catalytic.Comparison`, this module formalizes the stepwise single-endpoint excursion contract,
nested-excursion restoration invariance, and exact state-cardinality bit budgets; it is not a native
Turing-machine space certificate.

## Main definitions

* `Cslib.Catalytic.ExcursionProc`: a deterministic `m`-visit single-endpoint comparison procedure,
  with `run`, `runExcursions`, and combinators `mapState`, `liftFst`, `precomp`, `append`,
  `liftAlternating`.
* `Cslib.Catalytic.sqDistProc`, `Cslib.Catalytic.keyTestProc`: `addSqDist` and `keyTest` packaged
  as `4`-visit `ExcursionProc`s.
* `Cslib.Catalytic.natChunkVec`: fixed-length base-`2 ^ q` chunk extraction via `Cslib.Radix.digit`.
* `Cslib.Catalytic.outerChunkBits`, `Cslib.Catalytic.outerDigits`, `Cslib.Catalytic.outerAccBits`,
  `Cslib.Catalytic.innerChunkBits`, `Cslib.Catalytic.innerDigits`, `Cslib.Catalytic.innerAccBits`:
  explicit bit-width parameters for the two-stage reduction.
* `Cslib.Catalytic.OuterRegState`, `Cslib.Catalytic.InnerRegState`, `Cslib.Catalytic.KeyTableState`:
  the Stage-1 and Stage-2 registers with their accumulators, and the Stage-3 `ZMod 2` key table.
* `Cslib.Catalytic.VertexCatState`, `Cslib.Catalytic.VertexLocalFrame`: the shared catalytic memory
  and the `7`-bit local frame `Fin 64 × ZMod 2`.
* `Cslib.Catalytic.stageOneSqDistProc`, `Cslib.Catalytic.twoStageSqDistProc`: the `4`-visit Stage-1
  and `16`-visit Stage-2 sum-of-squares procedures.
* `Cslib.Catalytic.vertexStateEquiv`: the reassociation separating the shared catalyst from the
  local result bit.
* `Cslib.Catalytic.vertexEqProc`, `Cslib.Catalytic.catalyticVertexEq`: the `64`-excursion restoring
  equality procedure and its Boolean wrapper.
* `Cslib.Catalytic.vertexCatBits`, `Cslib.Catalytic.vertexCatLinearConst`: exact catalytic bit count
  and explicit linear constant for `n ≤ C_N * B`.

## Main results

* `Cslib.Catalytic.ExcursionProc.runExcursions_eq_run`: excursion invariance for restoring,
  catalyst-independent endpoint callbacks (allowing nested restoring calls).
* `Cslib.Catalytic.ExcursionProc.run_liftAlternating`: four-block forward/inverse lifting executes
  an alternating `4`-visit outer procedure on the unshifted and shifted readouts while restoring
  the inner state.
* `Cslib.Catalytic.run_vertexEqProc_chunk`, `Cslib.Catalytic.run_vertexEqProc`,
  `Cslib.Catalytic.runExcursions_vertexEqProc`, `Cslib.Catalytic.catalyticVertexEq_eq`:
  unconditional restoration for all `x, y : ℕ` and exact equality detection for all `x, y < 2 ^ n`
  under arbitrary initial catalytic contents.
* `Cslib.Catalytic.card_vertexLocalFrame`: `Fintype.card VertexLocalFrame = 2 ^ 7`.
* `Cslib.Catalytic.card_vertexCatState`:
  `Fintype.card (VertexCatState B n) = 2 ^ vertexCatBits B n`.
* `Cslib.Catalytic.innerDigits_le`:
  `n ≤ C_N * B → innerDigits B n ≤ Nat.log 2 (C_N + 1) + 11`.
* `Cslib.Catalytic.vertexCatBits_le`:
  `n ≤ C_N * B → vertexCatBits B n ≤ vertexCatLinearConst C_N * (B + 1)`.

## References

* [H. Buhrman, R. Cleve, M. Koucký, B. Loff and F. Speelman, *Computing with a full memory:
  catalytic space*][BuhrmanCleveKouckyLoffSpeelman2014]
* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 9.6, Lemma 9.9 (`lem:fp-catalytic`) and Section 11.4, Lemma 11.9 (`lem:ctrl-equality`)
  for the excursion restoration principle and `ZMod 2` key test; the two-stage deterministic
  `addSqDist` + `keyTest` composition and bit-budget bounds here are original to `complexitylib`.
-/

public section

namespace Cslib.Catalytic

/-! ### Stepwise single-endpoint excursion procedures -/

/-- A deterministic `m`-visit single-endpoint comparison procedure on values of type `α` with state
`S`. At phase `p : Fin m`, `side p = false` visits the left endpoint `x` and `side p = true` visits
the right endpoint `y`; `step p v s` updates the state from the single visited value `v` alone. -/
structure ExcursionProc (m : ℕ) (α S : Type*) where
  /-- Endpoint selector at phase `p`: `false` visits `x`, `true` visits `y`. -/
  side : Fin m → Bool
  /-- State update at phase `p` given the visited endpoint value. -/
  step : Fin m → α → S → S

namespace ExcursionProc

/-- Direct execution on fixed endpoints `x` and `y` across phases `0, …, m - 1`. -/
@[expose] def run {m : ℕ} {α S : Type*} (P : ExcursionProc m α S) (x y : α) (s₀ : S) : S :=
  Fin.foldl m (fun s p ↦ P.step p (bif P.side p then y else x) s) s₀

/-- Execution through an endpoint-excursion callback `visit : Bool → Cat → α × Cat` sharing
catalytic state `Cat` while holding only `(p : Fin m, st.2 : Loc)` in the caller's local frame
across each excursion. -/
@[expose] def runExcursions {m : ℕ} {α Cat Loc : Type*} (P : ExcursionProc m α (Cat × Loc))
    (visit : Bool → Cat → α × Cat) (cat₀ : Cat) (loc₀ : Loc) : Cat × Loc :=
  Fin.foldl m
    (fun st p ↦
      let res := visit (P.side p) st.1
      P.step p res.1 (res.2, st.2))
    (cat₀, loc₀)

/-- **Excursion invariance** (Lemma 9.9 nested-excursion contract): if `visit false` returns `x`,
`visit true` returns `y`, and both restore any incoming catalytic state `cat` (even when `visit`
internally invokes nested restoring procedures on `cat`), then `runExcursions` equals `run x y`. -/
theorem runExcursions_eq_run {m : ℕ} {α Cat Loc : Type*} (P : ExcursionProc m α (Cat × Loc))
    {visit : Bool → Cat → α × Cat} {x y : α}
    (hvisit : ∀ b cat, visit b cat = (bif b then y else x, cat))
    (cat₀ : Cat) (loc₀ : Loc) :
    P.runExcursions visit cat₀ loc₀ = P.run x y (cat₀, loc₀) := by
  simp only [runExcursions, run, hvisit, Prod.mk.eta]

/-- Transport an excursion procedure along an equivalence of states `e : S₁ ≃ S₂`. -/
@[expose] def mapState {m : ℕ} {α S₁ S₂ : Type*} (e : S₁ ≃ S₂) (P : ExcursionProc m α S₁) :
    ExcursionProc m α S₂ where
  side := P.side
  step p v s := e (P.step p v (e.symm s))

private theorem foldl_mapState {m : ℕ} {S₁ S₂ : Type*} (e : S₁ ≃ S₂)
    (g : S₁ → Fin m → S₁) (s : S₁) :
    Fin.foldl m (fun acc p ↦ e (g (e.symm acc) p)) (e s) = e (Fin.foldl m g s) := by
  induction m generalizing s with
  | zero => rfl
  | succ m ih =>
    simp only [Fin.foldl_succ, Equiv.symm_apply_apply]
    exact ih (fun acc p ↦ g acc p.succ) (g s 0)

@[simp] theorem run_mapState {m : ℕ} {α S₁ S₂ : Type*} (e : S₁ ≃ S₂)
    (P : ExcursionProc m α S₁) (x y : α) (s : S₂) :
    (P.mapState e).run x y s = e (P.run x y (e.symm s)) := by
  simpa only [run, mapState, Equiv.apply_symm_apply] using
    foldl_mapState e (fun acc p ↦ P.step p (bif P.side p then y else x) acc) (e.symm s)

/-- Lift a procedure on `S` to `S × Θ`, acting on the first component and leaving `Θ` untouched. -/
@[expose] def liftFst {m : ℕ} {α S : Type*} (Θ : Type*) (P : ExcursionProc m α S) :
    ExcursionProc m α (S × Θ) where
  side := P.side
  step p v st := (P.step p v st.1, st.2)

@[simp] theorem run_liftFst {m : ℕ} {α S Θ : Type*} (P : ExcursionProc m α S) (x y : α)
    (s : S) (θ : Θ) : (P.liftFst Θ).run x y (s, θ) = (P.run x y s, θ) := by
  unfold run liftFst
  induction m generalizing s with
  | zero => rfl
  | succ m ih => exact ih ⟨fun p ↦ P.side p.succ, fun p ↦ P.step p.succ⟩ _

/-- Precompose a pure state transformation `f : S → S` onto phase `0` of a nonempty procedure,
adding no extra endpoint visits. -/
@[expose] def precomp {n : ℕ} {α S : Type*} (f : S → S) (P : ExcursionProc (n + 1) α S) :
    ExcursionProc (n + 1) α S where
  side := P.side
  step := Fin.cases (fun v s ↦ P.step 0 v (f s)) (fun i v s ↦ P.step i.succ v s)

@[simp] theorem run_precomp {n : ℕ} {α S : Type*} (f : S → S) (P : ExcursionProc (n + 1) α S)
    (x y : α) (s : S) : (P.precomp f).run x y s = P.run x y (f s) :=
  rfl

/-- Concatenate an `m₁`-visit procedure followed by an `m₂`-visit procedure. -/
@[expose] def append {m₁ m₂ : ℕ} {α S : Type*} (P : ExcursionProc m₁ α S)
    (Q : ExcursionProc m₂ α S) : ExcursionProc (m₁ + m₂) α S where
  side := Fin.addCases P.side Q.side
  step := Fin.addCases P.step Q.step

@[simp] theorem run_append {m₁ m₂ : ℕ} {α S : Type*} (P : ExcursionProc m₁ α S)
    (Q : ExcursionProc m₂ α S) (x y : α) (s : S) :
    (P.append Q).run x y s = Q.run x y (P.run x y s) := by
  have hcast (h : m₁ ≤ m₁ + m₂) (i : Fin m₁) : Fin.castLE h i = Fin.castAdd m₂ i := rfl
  simp only [run, append, Fin.foldl_add, hcast, Fin.addCases_left, Fin.addCases_right]

/-- Lift a `4`-visit alternating procedure `Q : ExcursionProc 4 β Θ` (visiting `a, b, a, b`) along
a forward procedure `P_fwd` and its inverse `P_inv` on `S`, reading `a = π s` in the unshifted
state and `b = π (P_fwd.run x y s)` in the shifted state across four blocks. -/
@[expose] def liftAlternating {n : ℕ} {α β S Θ : Type*}
    (P_fwd P_inv : ExcursionProc (n + 1) α S) (π : S → β) (Q : ExcursionProc 4 β Θ) :
    ExcursionProc (((n + 1) + (n + 1)) + ((n + 1) + (n + 1))) α (S × Θ) :=
  let block (P : ExcursionProc (n + 1) α S) (k : Fin 4) : ExcursionProc (n + 1) α (S × Θ) :=
    (P.liftFst Θ).precomp fun st ↦ (st.1, Q.step k (π st.1) st.2)
  ((block P_fwd 0).append (block P_inv 1)).append ((block P_fwd 2).append (block P_inv 3))

/-- **Four-block forward/inverse lifting**: when `P_inv` undoes `P_fwd` on `(x, y)` and `Q`
alternates `![false, true, false, true]`, `liftAlternating` restores `s` and executes `Q` on the
unshifted readout `π s` and shifted readout `π (P_fwd.run x y s)`. -/
theorem run_liftAlternating {n : ℕ} {α β S Θ : Type*}
    (P_fwd P_inv : ExcursionProc (n + 1) α S) (π : S → β) (Q : ExcursionProc 4 β Θ)
    (hside : Q.side = ![false, true, false, true]) {x y : α} {s : S}
    (hinv : P_inv.run x y (P_fwd.run x y s) = s) (θ : Θ) :
    (liftAlternating P_fwd P_inv π Q).run x y (s, θ) =
      (s, Q.run (π s) (π (P_fwd.run x y s)) θ) := by
  simp only [liftAlternating, run_append, run_precomp, run_liftFst, hinv]
  simp only [run, Fin.foldl_succ, Fin.foldl_zero, hside, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Bool.cond_false, Bool.cond_true]
  rfl

end ExcursionProc

/-! ### `addSqDist` and `keyTest` as 4-visit excursion procedures -/

/-- `Cslib.Catalytic.addSqDist` packaged as a `4`-visit single-endpoint `ExcursionProc`, encoding
each visited endpoint by `enc : α → Fin ℓ → R`. -/
@[expose] def sqDistProc {α R ι : Type*} [CommRing R] [DecidableEq ι] {ℓ : ℕ}
    (c : R) (r : ι) (enc : α → Fin ℓ → R) : ExcursionProc 4 α ((ι → Fin ℓ → R) × R) where
  side := ![false, true, false, true]
  step :=
    ![fun v T ↦ (Function.update T.1 r (T.1 r + enc v), T.2 + c * (enc v ⬝ᵥ enc v)),
      fun v T ↦ (T.1, T.2 + c * (enc v ⬝ᵥ enc v - 2 * (T.1 r ⬝ᵥ enc v))),
      fun v T ↦ (Function.update T.1 r (T.1 r - enc v), T.2),
      fun v T ↦ (T.1, T.2 + c * (2 * (T.1 r ⬝ᵥ enc v)))]

@[simp] theorem run_sqDistProc {α R ι : Type*} [CommRing R] [DecidableEq ι] {ℓ : ℕ}
    (c : R) (r : ι) (enc : α → Fin ℓ → R) (x y : α) (T : (ι → Fin ℓ → R) × R) :
    (sqDistProc c r enc).run x y T = addSqDist c r (enc x) (enc y) T :=
  rfl

/-- `Cslib.Catalytic.keyTest` packaged as a `4`-visit single-endpoint `ExcursionProc`. -/
@[expose] def keyTestProc {α κ M : Type*} [DecidableEq κ] [AddCommGroup M]
    (c : M) (enc : α → κ) : ExcursionProc 4 α ((κ → M) × M) where
  side := ![false, true, false, true]
  step :=
    ![fun v st ↦ (Function.update st.1 (enc v) (st.1 (enc v) + c), st.2),
      fun v st ↦ (st.1, st.2 + st.1 (enc v)),
      fun v st ↦ (Function.update st.1 (enc v) (st.1 (enc v) - c), st.2),
      fun v st ↦ (st.1, st.2 - st.1 (enc v))]

@[simp] theorem run_keyTestProc {α κ M : Type*} [DecidableEq κ] [AddCommGroup M]
    (c : M) (enc : α → κ) (x y : α) (V : κ → M) (s : M) :
    (keyTestProc c enc).run x y (V, s) = keyTest c (enc x) (enc y) V s :=
  rfl

/-! ### Fixed-length binary-chunk encoding of natural numbers -/

/-- Extract `ℓ` base-`2 ^ q` chunks of a natural number `x`, least-significant chunk first. -/
@[expose] def natChunkVec (q ℓ x : ℕ) (i : Fin ℓ) : ℕ :=
  Cslib.Radix.digit (2 ^ q) x i.val

theorem natChunkVec_lt (q ℓ x : ℕ) (i : Fin ℓ) : natChunkVec q ℓ x i < 2 ^ q := by
  rw [natChunkVec, Cslib.Radix.digit_eq_div_pow_mod]
  exact Nat.mod_lt _ (by positivity)

theorem natChunkVec_eq_iff {q ℓ x y : ℕ} (hx : x < 2 ^ (ℓ * q)) (hy : y < 2 ^ (ℓ * q)) :
    natChunkVec q ℓ x = natChunkVec q ℓ y ↔ x = y := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  have hpow : (2 ^ q) ^ ℓ = 2 ^ (ℓ * q) := by rw [← pow_mul, Nat.mul_comm]
  obtain ⟨dx, hdx, hvx⟩ := Nat.exists_ofDigits_ofFn (hpow.symm ▸ hx)
  obtain ⟨dy, hdy, hvy⟩ := Nat.exists_ofDigits_ofFn (hpow.symm ▸ hy)
  have hdx_eq : dx = natChunkVec q ℓ x := funext fun i ↦ by
    rw [natChunkVec, Cslib.Radix.digit_eq_div_pow_mod, ← hvx, Nat.ofDigits_ofFn_div_mod dx hdx i]
  have hdy_eq : dy = natChunkVec q ℓ y := funext fun i ↦ by
    rw [natChunkVec, Cslib.Radix.digit_eq_div_pow_mod, ← hvy, Nat.ofDigits_ofFn_div_mod dy hdy i]
  rw [← hvx, ← hvy, hdx_eq, hdy_eq, h]

private theorem mul_two_pow_sub_one_sq_lt (q ℓ : ℕ) :
    ℓ * (2 ^ q - 1) ^ 2 < 2 ^ (2 * q + Nat.log 2 ℓ + 1) := by
  have hℓ : ℓ < 2 ^ (Nat.log 2 ℓ + 1) := Nat.lt_pow_succ_log_self (by decide) ℓ
  have hsq : (2 ^ q - 1) ^ 2 ≤ 2 ^ (2 * q) := by
    calc (2 ^ q - 1) ^ 2 ≤ (2 ^ q) ^ 2 := Nat.pow_le_pow_left (Nat.sub_le _ _) 2
      _ = 2 ^ (2 * q) := by rw [← pow_mul, Nat.mul_comm]
  calc ℓ * (2 ^ q - 1) ^ 2
      ≤ ℓ * 2 ^ (2 * q) := Nat.mul_le_mul_left ℓ hsq
    _ < 2 ^ (Nat.log 2 ℓ + 1) * 2 ^ (2 * q) :=
        Nat.mul_lt_mul_of_pos_right hℓ (by positivity)
    _ = 2 ^ (2 * q + Nat.log 2 ℓ + 1) := by
        rw [← pow_add]
        congr 1
        omega

/-! ### Two-stage bit-width parameterization and 64-excursion vertex equality -/

/-- Outer chunk bit-width `q₁ = max 1 ⌊log₂ B⌋`. -/
@[expose] def outerChunkBits (B : ℕ) : ℕ := max 1 (Nat.log 2 B)

/-- Number of outer chunks `ℓ₁ = ⌈n / q₁⌉` covering an `n`-bit identifier. -/
@[expose] def outerDigits (B n : ℕ) : ℕ := n ⌈/⌉ outerChunkBits B

/-- Bit-width `k₁` of the Stage-1 sum-of-squares accumulator over `ZMod (2 ^ k₁)`. -/
@[expose] def outerAccBits (B n : ℕ) : ℕ :=
  2 * outerChunkBits B + Nat.log 2 (outerDigits B n) + 1

/-- Inner chunk bit-width `q₂ = max 1 ⌊q₁ / 2⌋`. -/
@[expose] def innerChunkBits (B : ℕ) : ℕ := max 1 (outerChunkBits B / 2)

/-- Number of inner chunks `ℓ₂ = ⌈k₁ / q₂⌉` covering the `k₁`-bit Stage-1 accumulator. -/
@[expose] def innerDigits (B n : ℕ) : ℕ := outerAccBits B n ⌈/⌉ innerChunkBits B

/-- Bit-width `k₂` of the Stage-2 sum-of-squares accumulator (and `log₂` of the Stage-3 table). -/
@[expose] def innerAccBits (B n : ℕ) : ℕ :=
  2 * innerChunkBits B + Nat.log 2 (innerDigits B n) + 1

/-- Stage-1 catalytic register and accumulator state (`(ℓ₁ + 1) · k₁` bits). -/
abbrev OuterRegState (B n : ℕ) : Type :=
  (Unit → Fin (outerDigits B n) → ZMod (2 ^ outerAccBits B n)) × ZMod (2 ^ outerAccBits B n)

/-- Stage-2 catalytic register and accumulator state (`(ℓ₂ + 1) · k₂` bits). -/
abbrev InnerRegState (B n : ℕ) : Type :=
  (Unit → Fin (innerDigits B n) → ZMod (2 ^ innerAccBits B n)) × ZMod (2 ^ innerAccBits B n)

/-- Stage-3 catalytic `ZMod 2` key table (`2 ^ k₂` bits). -/
abbrev KeyTableState (B n : ℕ) : Type :=
  ZMod (2 ^ innerAccBits B n) → ZMod 2

/-- Full shared catalytic memory `(T₁, T₂, W)` restored by `vertexEqProc` and
`catalyticVertexEq`. -/
abbrev VertexCatState (B n : ℕ) : Type :=
  OuterRegState B n × InnerRegState B n × KeyTableState B n

/-- Caller-local frame retained across each of the `64` excursions: a phase in `Fin 64` and one
accumulator bit in `ZMod 2` (`7` bits total, independent of `B` and `n`). -/
abbrev VertexLocalFrame : Type := Fin 64 × ZMod 2

/-- Stage-1 `4`-visit procedure adding `c₁` times the outer chunk squared distance to `T₁.2`. -/
@[expose] def stageOneSqDistProc (B n : ℕ) (c₁ : ZMod (2 ^ outerAccBits B n)) :
    ExcursionProc 4 ℕ (OuterRegState B n) :=
  sqDistProc c₁ () fun x ↦ (↑) ∘ natChunkVec (outerChunkBits B) (outerDigits B n) x

/-- Stage-2 `16`-visit procedure lifting the inner chunk squared distance along `stageOneSqDistProc`
and its inverse. -/
@[expose] def twoStageSqDistProc (B n : ℕ) (c₂ : ZMod (2 ^ innerAccBits B n)) :
    ExcursionProc 16 ℕ (OuterRegState B n × InnerRegState B n) :=
  ExcursionProc.liftAlternating (stageOneSqDistProc B n 1) (stageOneSqDistProc B n (-1)) Prod.snd
    (sqDistProc c₂ () fun z : ZMod (2 ^ outerAccBits B n) ↦
      (↑) ∘ natChunkVec (innerChunkBits B) (innerDigits B n) z.val)

/-- State reassociation separating the shared catalyst `VertexCatState B n` from the `1`-bit local
accumulator `ZMod 2`. -/
@[expose] def vertexStateEquiv (B n : ℕ) :
    ((OuterRegState B n × InnerRegState B n) × (KeyTableState B n × ZMod 2)) ≃
      (VertexCatState B n × ZMod 2) :=
  (Equiv.prodAssoc (OuterRegState B n × InnerRegState B n) (KeyTableState B n) (ZMod 2)).symm.trans
    ((Equiv.prodAssoc (OuterRegState B n) (InnerRegState B n) (KeyTableState B n)).prodCongr
      (Equiv.refl (ZMod 2)))

/-- **The `64`-excursion catalytic vertex-equality procedure.** On endpoints `x, y < 2 ^ n`, it
restores any incoming catalytic state `cat : VertexCatState B n` and adds `1 : ZMod 2` into the
local result bit iff `x = y`. -/
@[expose] def vertexEqProc (B n : ℕ) : ExcursionProc 64 ℕ (VertexCatState B n × ZMod 2) :=
  (ExcursionProc.liftAlternating (twoStageSqDistProc B n 1) (twoStageSqDistProc B n (-1))
    (Prod.snd ∘ Prod.snd) (keyTestProc (1 : ZMod 2) id)).mapState (vertexStateEquiv B n)

/-- **Boolean catalytic vertex equality via single-endpoint excursions.** Initializes the local
result bit to `0 : ZMod 2`, runs the `64` excursions through `visit`, and returns the equality
decision together with the restored catalytic state. -/
@[expose] def catalyticVertexEq (B n : ℕ)
    (visit : Bool → VertexCatState B n → ℕ × VertexCatState B n)
    (cat₀ : VertexCatState B n) : Bool × VertexCatState B n :=
  let res := (vertexEqProc B n).runExcursions visit cat₀ 0
  (decide (res.2 = 1), res.1)

/-! ### Exactness and exact restoration -/

private theorem stageOne_shift_eq_chunk_iff (B n x y : ℕ) (T₁ : OuterRegState B n) :
    T₁.2 = ((stageOneSqDistProc B n 1).run x y T₁).2 ↔
      natChunkVec (outerChunkBits B) (outerDigits B n) x =
        natChunkVec (outerChunkBits B) (outerDigits B n) y := by
  simp only [stageOneSqDistProc, run_sqDistProc, addSqDist_eq, one_mul, left_eq_add]
  exact natCast_sqDist_eq_zero_iff (natChunkVec_lt _ _ x) (natChunkVec_lt _ _ y)
    (mul_two_pow_sub_one_sq_lt (outerChunkBits B) (outerDigits B n))

private theorem run_twoStageSqDistProc (B n : ℕ) (c₂ : ZMod (2 ^ innerAccBits B n))
    (x y : ℕ) (T₁ : OuterRegState B n) (T₂ : InnerRegState B n) :
    (twoStageSqDistProc B n c₂).run x y (T₁, T₂) =
      (T₁, addSqDist c₂ ()
        ((↑) ∘ natChunkVec (innerChunkBits B) (innerDigits B n) T₁.2.val)
        ((↑) ∘ natChunkVec (innerChunkBits B) (innerDigits B n)
          ((stageOneSqDistProc B n 1).run x y T₁).2.val)
        T₂) := by
  have hinv : (stageOneSqDistProc B n (-1)).run x y ((stageOneSqDistProc B n 1).run x y T₁) =
      T₁ := addSqDist_neg_addSqDist 1 () _ _ T₁
  exact ExcursionProc.run_liftAlternating _ _ _ _ rfl hinv T₂

private theorem run_twoStageSqDistProc_neg (B n x y : ℕ)
    (T : OuterRegState B n × InnerRegState B n) :
    (twoStageSqDistProc B n (-1)).run x y ((twoStageSqDistProc B n 1).run x y T) = T := by
  obtain ⟨T₁, T₂⟩ := T
  rw [run_twoStageSqDistProc, run_twoStageSqDistProc, addSqDist_neg_addSqDist]

private theorem stageTwo_shift_eq_iff {B n : ℕ} (z₁ z₁' : ZMod (2 ^ outerAccBits B n))
    (T₂ : InnerRegState B n) :
    T₂.2 = (addSqDist 1 ()
      ((↑) ∘ natChunkVec (innerChunkBits B) (innerDigits B n) z₁.val)
      ((↑) ∘ natChunkVec (innerChunkBits B) (innerDigits B n) z₁'.val) T₂).2 ↔ z₁ = z₁' := by
  have hq₂ : 0 < innerChunkBits B := by simp [innerChunkBits]
  have hcov : outerAccBits B n ≤ innerDigits B n * innerChunkBits B := Nat.le_ceilDiv_mul hq₂
  have hz₁ : z₁.val < 2 ^ (innerDigits B n * innerChunkBits B) :=
    (ZMod.val_lt z₁).trans_le (Nat.pow_le_pow_right (by decide) hcov)
  have hz₁' : z₁'.val < 2 ^ (innerDigits B n * innerChunkBits B) :=
    (ZMod.val_lt z₁').trans_le (Nat.pow_le_pow_right (by decide) hcov)
  simp only [addSqDist_eq, one_mul, left_eq_add]
  exact (natCast_sqDist_eq_zero_iff (natChunkVec_lt _ _ z₁.val) (natChunkVec_lt _ _ z₁'.val)
      (mul_two_pow_sub_one_sq_lt (innerChunkBits B) (innerDigits B n))).trans
    ((natChunkVec_eq_iff hz₁ hz₁').trans (ZMod.val_injective (2 ^ outerAccBits B n)).eq_iff)

/-- **Unconditional restoration and chunk-equality characterization of `vertexEqProc`**: for all
`B n x y : ℕ` (without any range bound on `x` or `y`), `vertexEqProc` restores `cat` and adds `1`
to `s₀` iff `x` and `y` agree on their first `outerDigits B n` base-`2 ^ outerChunkBits B`
chunks. -/
theorem run_vertexEqProc_chunk (B n x y : ℕ) (cat : VertexCatState B n) (s₀ : ZMod 2) :
    (vertexEqProc B n).run x y (cat, s₀) =
      (cat, s₀ + if natChunkVec (outerChunkBits B) (outerDigits B n) x =
          natChunkVec (outerChunkBits B) (outerDigits B n) y then 1 else 0) := by
  obtain ⟨T₁, T₂, W⟩ := cat
  rw [vertexEqProc, ExcursionProc.run_mapState]
  change vertexStateEquiv B n
      ((ExcursionProc.liftAlternating (twoStageSqDistProc B n 1) (twoStageSqDistProc B n (-1))
        (Prod.snd ∘ Prod.snd) (keyTestProc (1 : ZMod 2) id)).run x y (((T₁, T₂), (W, s₀)))) = _
  rw [ExcursionProc.run_liftAlternating _ _ _ _ rfl (run_twoStageSqDistProc_neg B n x y (T₁, T₂)),
    run_keyTestProc]
  simp only [Function.comp_apply, id_eq, run_twoStageSqDistProc, keyTest_eq, vertexStateEquiv,
    Equiv.trans_apply, Equiv.prodAssoc_symm_apply, Equiv.prodCongr_apply, Equiv.prodAssoc_apply,
    Equiv.refl_apply, Prod.map_apply, stageTwo_shift_eq_iff, stageOne_shift_eq_chunk_iff]

/-- **Direct correctness and restoration of `vertexEqProc`**: for all `B n : ℕ`, all `x, y < 2 ^ n`,
and any initial catalytic contents `cat` and local bit `s₀ : ZMod 2`, `vertexEqProc` restores `cat`
and adds `if x = y then 1 else 0` to `s₀`. -/
theorem run_vertexEqProc {B n x y : ℕ} (hx : x < 2 ^ n) (hy : y < 2 ^ n)
    (cat : VertexCatState B n) (s₀ : ZMod 2) :
    (vertexEqProc B n).run x y (cat, s₀) = (cat, s₀ + if x = y then 1 else 0) := by
  have hq₁ : 0 < outerChunkBits B := by simp [outerChunkBits]
  have hcov : n ≤ outerDigits B n * outerChunkBits B := Nat.le_ceilDiv_mul hq₁
  have hx' : x < 2 ^ (outerDigits B n * outerChunkBits B) :=
    hx.trans_le (Nat.pow_le_pow_right (by decide) hcov)
  have hy' : y < 2 ^ (outerDigits B n * outerChunkBits B) :=
    hy.trans_le (Nat.pow_le_pow_right (by decide) hcov)
  rw [run_vertexEqProc_chunk]
  simp only [natChunkVec_eq_iff hx' hy']

/-- **Excursion correctness and restoration of `vertexEqProc`**: under any restoring,
catalyst-independent excursion callback `visit` for `x, y < 2 ^ n`, `runExcursions` restores `cat`
and adds `if x = y then 1 else 0` to `s₀`. -/
theorem runExcursions_vertexEqProc {B n x y : ℕ} (hx : x < 2 ^ n) (hy : y < 2 ^ n)
    {visit : Bool → VertexCatState B n → ℕ × VertexCatState B n}
    (hvisit : ∀ b cat, visit b cat = (bif b then y else x, cat))
    (cat : VertexCatState B n) (s₀ : ZMod 2) :
    (vertexEqProc B n).runExcursions visit cat s₀ = (cat, s₀ + if x = y then 1 else 0) := by
  rw [ExcursionProc.runExcursions_eq_run _ hvisit, run_vertexEqProc hx hy]

/-- **Exactness and restoration of `catalyticVertexEq`**: for all `B n : ℕ`, all `x, y < 2 ^ n`,
every restoring catalyst-independent callback `visit`, and arbitrary initial catalytic state `cat₀`,
`catalyticVertexEq` returns `(decide (x = y), cat₀)`. In particular, it satisfies the same
restoring catalyst-independent contract for outer callers. -/
theorem catalyticVertexEq_eq {B n x y : ℕ} (hx : x < 2 ^ n) (hy : y < 2 ^ n)
    {visit : Bool → VertexCatState B n → ℕ × VertexCatState B n}
    (hvisit : ∀ b cat, visit b cat = (bif b then y else x, cat))
    (cat₀ : VertexCatState B n) :
    catalyticVertexEq B n visit cat₀ = (decide (x = y), cat₀) := by
  simp only [catalyticVertexEq, runExcursions_vertexEqProc hx hy hvisit, zero_add]
  by_cases h : x = y <;> simp [h]

/-! ### Explicit local-frame and catalytic bit-budget accounting -/

/-- Total bit count of the shared catalytic state `VertexCatState B n`. -/
@[expose] def vertexCatBits (B n : ℕ) : ℕ :=
  (outerDigits B n + 1) * outerAccBits B n +
    (innerDigits B n + 1) * innerAccBits B n +
    2 ^ innerAccBits B n

/-- Explicit closed-form linear coefficient bounding `vertexCatBits B n` by
`vertexCatLinearConst C_N * (B + 1)` whenever `n ≤ C_N * B`. -/
@[expose] def vertexCatLinearConst (C_N : ℕ) : ℕ :=
  let c := Nat.log 2 (C_N + 1)
  let d := Nat.log 2 (c + 11) + 1
  (c + 5) * (C_N + 2) + (c + 12) * (d + 2) + 2 ^ (d + 2)

/-- **Constant local frame (`7` bits).** The caller's local frame across all `64` excursions has
cardinality `2 ^ 7`, independent of `B` and `n`. -/
theorem card_vertexLocalFrame : Fintype.card VertexLocalFrame = 2 ^ 7 := by
  rw [Fintype.card_prod, Fintype.card_fin, ZMod.card]
  rfl

/-- **Exact catalytic bit count.** The shared catalytic state `VertexCatState B n` has cardinality
`2 ^ vertexCatBits B n`. -/
theorem card_vertexCatState (B n : ℕ) :
    Fintype.card (VertexCatState B n) = 2 ^ vertexCatBits B n := by
  have card_reg (ℓ k : ℕ) :
      Fintype.card ((Unit → Fin ℓ → ZMod (2 ^ k)) × ZMod (2 ^ k)) = 2 ^ ((ℓ + 1) * k) := by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin,
      Fintype.card_unique, pow_one, ← pow_mul, ← pow_add]
    congr 1
    ring
  rw [Fintype.card_prod, card_reg, Fintype.card_prod, card_reg,
    Fintype.card_fun, ZMod.card, ZMod.card, vertexCatBits, pow_add, pow_add]
  ring

private theorem outerAccBits_le {B n C_N : ℕ} (hn : n ≤ C_N * B) :
    outerAccBits B n ≤ 3 * outerChunkBits B + Nat.log 2 (C_N + 1) + 2 := by
  have hq₁ : 0 < outerChunkBits B := by simp [outerChunkBits]
  have hℓ₁_le_n : outerDigits B n ≤ n :=
    (Nat.ceilDiv_le_iff hq₁).2 (Nat.le_mul_of_pos_right n hq₁)
  have hBlog : B < 2 ^ (Nat.log 2 B + 1) := Nat.lt_pow_succ_log_self (by decide) B
  have hBq₁ : B < 2 ^ (outerChunkBits B + 1) :=
    hBlog.trans_le (Nat.pow_le_pow_right (by decide) (by simp [outerChunkBits]))
  have hc : C_N + 1 < 2 ^ (Nat.log 2 (C_N + 1) + 1) :=
    Nat.lt_pow_succ_log_self (by decide) (C_N + 1)
  have hℓ₁_lt : outerDigits B n < 2 ^ (Nat.log 2 (C_N + 1) + outerChunkBits B + 2) := by
    calc outerDigits B n ≤ C_N * B := hℓ₁_le_n.trans hn
      _ ≤ C_N * 2 ^ (outerChunkBits B + 1) := Nat.mul_le_mul_left C_N hBq₁.le
      _ < (C_N + 1) * 2 ^ (outerChunkBits B + 1) :=
          Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self C_N) (by positivity)
      _ < 2 ^ (Nat.log 2 (C_N + 1) + 1) * 2 ^ (outerChunkBits B + 1) :=
          Nat.mul_lt_mul_of_pos_right hc (by positivity)
      _ = 2 ^ (Nat.log 2 (C_N + 1) + outerChunkBits B + 2) := by
          rw [← pow_add]
          congr 1
          omega
  have hlog_ℓ₁ : Nat.log 2 (outerDigits B n) < Nat.log 2 (C_N + 1) + outerChunkBits B + 2 :=
    Nat.log_lt_of_lt_pow' (by omega) hℓ₁_lt
  rw [outerAccBits]
  omega

/-- **Constant Stage-2 chunk count.** When `n ≤ C_N * B`, the number of inner chunks
`innerDigits B n` is bounded by `Nat.log 2 (C_N + 1) + 11`, independently of `B`. -/
theorem innerDigits_le {B n C_N : ℕ} (hn : n ≤ C_N * B) :
    innerDigits B n ≤ Nat.log 2 (C_N + 1) + 11 := by
  have hk₁ := outerAccBits_le hn
  have hq₂ : 0 < innerChunkBits B := by simp [innerChunkBits]
  have hq₁_le : outerChunkBits B ≤ 3 * innerChunkBits B := by grind [innerChunkBits]
  rw [innerDigits, Nat.ceilDiv_le_iff hq₂]
  nlinarith

/-- **`O(B)` catalytic bit budget.** Whenever `n ≤ C_N * B`, the total number of shared catalytic
bits satisfies `vertexCatBits B n ≤ vertexCatLinearConst C_N * (B + 1)`. -/
theorem vertexCatBits_le {B n C_N : ℕ} (hn : n ≤ C_N * B) :
    vertexCatBits B n ≤ vertexCatLinearConst C_N * (B + 1) := by
  set c := Nat.log 2 (C_N + 1)
  set d := Nat.log 2 (c + 11) + 1
  have hq₁_pos : 0 < outerChunkBits B := by simp [outerChunkBits]
  have hq₁_le_B : outerChunkBits B ≤ B + 1 := by
    have := Nat.log_le_self 2 B
    rw [outerChunkBits]
    omega
  have hq₂_le_B : innerChunkBits B ≤ B + 1 := by grind [innerChunkBits]
  -- Stage 1 bit bound: `(ℓ₁ + 1) * k₁ ≤ (c + 5) * (C_N + 2) * (B + 1)`.
  have hk₁_le : outerAccBits B n ≤ (c + 5) * outerChunkBits B := by
    have : outerAccBits B n ≤ 3 * outerChunkBits B + c + 2 := outerAccBits_le hn
    nlinarith
  have hℓ₁_mul : outerDigits B n * outerChunkBits B < n + outerChunkBits B :=
    Nat.ceilDiv_mul_lt hq₁_pos
  have hstage1 : (outerDigits B n + 1) * outerAccBits B n ≤ (c + 5) * (C_N + 2) * (B + 1) := by
    calc (outerDigits B n + 1) * outerAccBits B n
        ≤ (outerDigits B n + 1) * ((c + 5) * outerChunkBits B) := Nat.mul_le_mul_left _ hk₁_le
      _ = (c + 5) * (outerDigits B n * outerChunkBits B + outerChunkBits B) := by ring
      _ ≤ (c + 5) * ((C_N + 2) * (B + 1)) := by
          refine Nat.mul_le_mul_left _ ?_
          nlinarith
      _ = (c + 5) * (C_N + 2) * (B + 1) := by ring
  -- Stage 2 bit bound and Stage 3 table bound via `k₂ ≤ 2 * q₂ + d`.
  have hℓ₂ : innerDigits B n ≤ c + 11 := innerDigits_le hn
  have hlog_ℓ₂ : Nat.log 2 (innerDigits B n) ≤ Nat.log 2 (c + 11) := Nat.log_mono_right hℓ₂
  have hk₂ : innerAccBits B n ≤ 2 * innerChunkBits B + d := by grind [innerAccBits]
  have hk₂_lin : innerAccBits B n ≤ (d + 2) * (B + 1) := by
    nlinarith
  have hstage2 : (innerDigits B n + 1) * innerAccBits B n ≤ (c + 12) * (d + 2) * (B + 1) := by
    calc (innerDigits B n + 1) * innerAccBits B n
        ≤ (c + 12) * ((d + 2) * (B + 1)) := Nat.mul_le_mul (by omega) hk₂_lin
      _ = (c + 12) * (d + 2) * (B + 1) := by ring
  have hpow_q₂ : 2 ^ (2 * innerChunkBits B) ≤ 4 * (B + 1) := by
    by_cases hlog : Nat.log 2 B ≤ 1
    · have hq₂_eq : innerChunkBits B = 1 := by grind [innerChunkBits, outerChunkBits]
      rw [hq₂_eq]
      omega
    · have hB0 : B ≠ 0 := by intro h0; subst h0; simp at hlog
      have h2q₂ : 2 * innerChunkBits B ≤ Nat.log 2 B := by grind [innerChunkBits, outerChunkBits]
      calc 2 ^ (2 * innerChunkBits B)
          ≤ 2 ^ Nat.log 2 B := Nat.pow_le_pow_right (by decide) h2q₂
        _ ≤ B := Nat.pow_log_le_self 2 hB0
        _ ≤ 4 * (B + 1) := by omega
  have hstage3 : 2 ^ innerAccBits B n ≤ 2 ^ (d + 2) * (B + 1) := by
    calc 2 ^ innerAccBits B n
        ≤ 2 ^ (2 * innerChunkBits B + d) := Nat.pow_le_pow_right (by decide) hk₂
      _ = 2 ^ d * 2 ^ (2 * innerChunkBits B) := by rw [Nat.add_comm, pow_add]
      _ ≤ 2 ^ d * (4 * (B + 1)) := Nat.mul_le_mul_left _ hpow_q₂
      _ = 2 ^ (d + 2) * (B + 1) := by
          rw [show d + 2 = d + 1 + 1 by omega, pow_succ, pow_succ]
          ring
  calc vertexCatBits B n
      = (outerDigits B n + 1) * outerAccBits B n +
          (innerDigits B n + 1) * innerAccBits B n + 2 ^ innerAccBits B n := rfl
    _ ≤ (c + 5) * (C_N + 2) * (B + 1) +
          (c + 12) * (d + 2) * (B + 1) +
          2 ^ (d + 2) * (B + 1) :=
        Nat.add_le_add (Nat.add_le_add hstage1 hstage2) hstage3
    _ = vertexCatLinearConst C_N * (B + 1) := by
        dsimp only [vertexCatLinearConst, c, d]
        ring

end Cslib.Catalytic
