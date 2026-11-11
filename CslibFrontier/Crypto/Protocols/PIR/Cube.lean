/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.PIR.Basic
public import CslibFrontier.Foundations.Data.Code.Hadamard
public import Mathlib.Data.Nat.Sqrt

/-!
# Subcube schemes for private information retrieval

The schemes of
[Chor, Goldreich, Kushilevitz and Sudan, Section 3][ChorGoldreichKushilevitzSudan1998] ask each
server for the exclusive or of the database bits over a set of positions.

* **Two servers** (`PIR.twoServer`, Section 3.1). To read `x i`, the user draws a uniform set
  `T ⊆ ι`, sends `T` to one server and `T Δ {i}` to the other, and adds the two answers
  `⊕_{j ∈ T} x j` and `⊕_{j ∈ T Δ {i}} x j`. Sets are bit strings and the answer to `a` is the
  Hadamard codeword `x ⬝ᵥ a` (`BitString.hadamardCode`). Each server sees a uniform set, so the
  scheme is private, and it communicates `2 (n + 1)` bits.
* **`2 ^ d` servers** (`PIR.cube`, Section 3.2). The database is indexed by a cube `D → ι`, with
  `d = |D|` and `ℓ = |ι|`. The user draws uniform sets `T l ⊆ ι` for `l : D` and sends the server
  `σ : D → Bool` the sets `T l Δ {i l}` for the coordinates with `σ l = true` and `T l` for the
  others. The server answers with the exclusive or of the database over the subcube
  `∏ l, (its set for l)`, and the user adds the `2 ^ d` answers: every position other than `i`
  lies in an even number of the subcubes. The scheme communicates `2 ^ d (d ℓ + 1)` bits.
* **Balancing** (Section 3.4, Corollary 3). The rows transformation applied to the two-server
  scheme reads an `m × n` matrix with `2 (m + n)` bits (`PIR.communication_twoServer_rows`), so
  every `n ≤ m ^ 2` has a two-server scheme with `4 m` bits (`PIR.hasScheme_two_of_le_mul_self`),
  in particular `4 (⌊√n⌋ + 1)` bits (`PIR.hasScheme_two_sqrt`). Likewise every `n ≤ ℓ ^ d` has a
  `2 ^ d`-server scheme with `2 ^ d (d ℓ + 1)` bits (`PIR.hasScheme_two_pow_of_le_pow`). A
  database of `n` bits is placed in the grid or cube through an embedding, padding with `false`.

Flipping one coordinate of a server changes its query in a single set
(`PIR.query_update_cube`). The covering-code schemes of Section 3.3 (`PIR.CoveringCode`) use this
to let fewer servers emulate all `2 ^ d`.

## Main definitions

* `Cslib.Crypto.Protocols.PIR.twoServer`: the basic two-server scheme.
* `Cslib.Crypto.Protocols.PIR.cube`: the `2 ^ d`-server subcube scheme.

## Main results

* `Cslib.Crypto.Protocols.PIR.isCorrect_twoServer`,
  `Cslib.Crypto.Protocols.PIR.isPrivate_twoServer`,
  `Cslib.Crypto.Protocols.PIR.communication_twoServer`: the two-server scheme.
* `Cslib.Crypto.Protocols.PIR.isCorrect_cube`, `Cslib.Crypto.Protocols.PIR.isPrivate_cube`,
  `Cslib.Crypto.Protocols.PIR.communication_cube`: the subcube scheme.
* `Cslib.Crypto.Protocols.PIR.communication_twoServer_rows`: `2 (m + n)` bits for an `m × n`
  matrix.
* `Cslib.Crypto.Protocols.PIR.hasScheme_two_of_le_mul_self`,
  `Cslib.Crypto.Protocols.PIR.hasScheme_two_sqrt`,
  `Cslib.Crypto.Protocols.PIR.hasScheme_two_pow_of_le_pow`: schemes for `n`-bit databases.

## References

* [B. Chor, O. Goldreich, E. Kushilevitz, M. Sudan, *Private information
  retrieval*][ChorGoldreichKushilevitzSudan1998], Sections 3.1, 3.2 and 3.4
-/

public section

namespace Cslib.Crypto.Protocols.PIR

open Probability BitString

/-! ### Two servers -/

section TwoServer

variable (ι : Type) [Fintype ι] [DecidableEq ι]

/-- The basic two-server scheme [CGKS, Section 3.1][ChorGoldreichKushilevitzSudan1998]. The
servers are `false` and `true`. For the index `i`, the user draws a uniform `t : ι → Bool` and sends
`t` to the server `false` and `t + eᵢ` to the server `true`. Each server answers with the parity
`x ⬝ᵥ a` of the database on the set `a` it receives, and the user adds the two answers. -/
noncomputable def twoServer : Scheme ι Bool Unit (ι → Bool) Bool where
  query i := do
    let t ← ProbComp.uniform (ι → Bool)
    pure ((), fun σ => t + Pi.single i σ)
  answer _ x a := hadamardCode x a
  reconstruct _ _ a := a false + a true

variable {ι}

theorem answer_twoServer (σ : Bool) (x a : ι → Bool) :
    (twoServer ι).answer σ x a = hadamardCode x a := by
  rfl

theorem reconstruct_twoServer (i : ι) (r : Unit) (a : Bool → Bool) :
    (twoServer ι).reconstruct i r a = a false + a true := by
  rfl

/-- Each server of the two-server scheme receives a uniform set, whatever the index. -/
theorem eval_serverQuery_twoServer (σ : Bool) (i : ι) :
    ProbComp.eval ((twoServer ι).serverQuery σ i) = PMF.uniformOfFintype (ι → Bool) := by
  rw [Scheme.eval_serverQuery, twoServer]
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform, PMF.map_bind,
    PMF.pure_map]
  exact PMF.uniformOfFintype_map_equiv (Equiv.addRight (Pi.single i σ : ι → Bool))

/-- The two queries of the two-server scheme add up to `eᵢ`: together, the servers know `i`. -/
theorem query_add_query_twoServer {i : ι} {r : Unit} {q : Bool → ι → Bool}
    (hrq : (r, q) ∈ (ProbComp.eval ((twoServer ι).query i)).support) :
    q false + q true = Pi.single i true := by
  simp only [twoServer, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, Prod.mk.injEq] at hrq
  obtain ⟨t, -, -, rfl⟩ := hrq
  funext j
  change (t + (Pi.single i false : ι → Bool)) j + (t + (Pi.single i true : ι → Bool)) j =
    (Pi.single i true : ι → Bool) j
  rw [show (Pi.single i false : ι → Bool) = 0 from Pi.single_zero i, add_zero, Pi.add_apply,
    ← add_assoc, BooleanRing.add_self, zero_add]

/-- **The two-server scheme is private** [CGKS, Section 3.1][ChorGoldreichKushilevitzSudan1998]. -/
theorem isPrivate_twoServer : (twoServer ι).IsPrivate :=
  (twoServer ι).isPrivate_iff.mpr fun σ i i' => by
    rw [eval_serverQuery_twoServer, eval_serverQuery_twoServer]

/-- **The two-server scheme is correct** [CGKS, Section 3.1][ChorGoldreichKushilevitzSudan1998]:
the answers `x ⬝ᵥ t` and `x ⬝ᵥ (t + eᵢ)` add up to `x i`. -/
theorem isCorrect_twoServer : (twoServer ι).IsCorrect := by
  rw [Scheme.isCorrect_iff]
  intro x i r q hrq
  change hadamardCode x (q false) + hadamardCode x (q true) = x i
  rw [hadamardCode_apply, hadamardCode_apply, ← dotProduct_add, query_add_query_twoServer hrq]
  exact dotProduct_single_one x i

/-- The two-server scheme sends `n` bits to each server and receives one bit from each. -/
theorem communication_twoServer :
    communication Bool (ι → Bool) Bool = 2 * (Fintype.card ι + 1) := by
  rw [communication_eq, Fintype.card_bool, Fintype.card_fun, Fintype.card_bool,
    Nat.clog_pow 2 _ (by norm_num), Nat.clog_eq_one le_rfl le_rfl]

/-- The rows transformation of the two-server scheme reads an `m × n` matrix with `2 (m + n)` bits
[CGKS, Section 3.4][ChorGoldreichKushilevitzSudan1998]. -/
theorem communication_twoServer_rows (ρ : Type) [Fintype ρ] [DecidableEq ρ] :
    communication Bool (ι → Bool) (ρ → Bool) = 2 * (Fintype.card ι + Fintype.card ρ) := by
  rw [communication_rows, Fintype.card_bool, Fintype.card_fun, Fintype.card_bool,
    Nat.clog_pow 2 _ (by norm_num)]

end TwoServer

/-! ### `2 ^ d` servers -/

section Cube

variable (D ι : Type) [Fintype D] [DecidableEq D] [Fintype ι] [DecidableEq ι]

/-- The subcube scheme with `2 ^ |D|` servers [CGKS, Section 3.2][ChorGoldreichKushilevitzSudan1998]
for databases indexed by the cube `D → ι`. The servers are `σ : D → Bool`. For the index `i`, the
user draws uniform sets `t l : ι → Bool` and sends the server `σ` the sets `t l + σ l • e_{i l}`.
The server answers with the exclusive or `∑ j, x j * ∏ l, a l (j l)` of the database over the
subcube `∏ l, a l` it receives, and the user adds all the answers. -/
noncomputable def cube : Scheme (D → ι) (D → Bool) Unit (D → ι → Bool) Bool where
  query i := do
    let t ← ProbComp.uniform (D → ι → Bool)
    pure ((), fun σ l => t l + Pi.single (i l) (σ l))
  answer _ x a := ∑ j : D → ι, x j * ∏ l, a l (j l)
  reconstruct _ _ a := ∑ σ, a σ

variable {D ι}

/-- Each server of the subcube scheme receives `|D|` uniform independent sets, whatever the
index. -/
theorem eval_serverQuery_cube (σ : D → Bool) (i : D → ι) :
    ProbComp.eval ((cube D ι).serverQuery σ i) = PMF.uniformOfFintype (D → ι → Bool) := by
  rw [Scheme.eval_serverQuery, cube]
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform, PMF.map_bind,
    PMF.pure_map]
  exact PMF.uniformOfFintype_map_equiv
    (Equiv.addRight (fun l => Pi.single (i l) (σ l) : D → ι → Bool))

/-- **The subcube scheme is private** [CGKS, Section 3.2][ChorGoldreichKushilevitzSudan1998]. -/
theorem isPrivate_cube : (cube D ι).IsPrivate :=
  (cube D ι).isPrivate_iff.mpr fun σ i i' => by
    rw [eval_serverQuery_cube, eval_serverQuery_cube]

omit [Fintype D] [DecidableEq D] [Fintype ι] in
/-- Adding both choices of the flipped coordinate leaves the indicator of the flipped position. -/
private theorem sum_bool_add_single (t : ι → Bool) (k j : ι) :
    ∑ b : Bool, (t + (Pi.single k b : ι → Bool)) j = (Pi.single k true : ι → Bool) j := by
  rw [Fintype.sum_bool, show (Pi.single k false : ι → Bool) = 0 from Pi.single_zero k, add_zero,
    Pi.add_apply, add_comm, ← add_assoc, BooleanRing.add_self, zero_add]

omit [DecidableEq D] [Fintype ι] in
private theorem prod_single_eq (i j : D → ι) :
    ∏ l, (Pi.single (i l) true : ι → Bool) (j l) = if j = i then 1 else 0 := by
  split_ifs with h
  · subst h
    exact Finset.prod_eq_one fun l _ => Pi.single_eq_same _ _
  · obtain ⟨l, hl⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ l) (Pi.single_eq_of_ne hl _)

/-- **The subcube scheme is correct** [CGKS, Section 3.2][ChorGoldreichKushilevitzSudan1998]: the
position `i` lies in exactly one of the `2 ^ d` subcubes and every other position in an even
number of them. -/
theorem isCorrect_cube : (cube D ι).IsCorrect := by
  rw [Scheme.isCorrect_iff]
  intro x i r q hrq
  simp only [cube, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, Prod.mk.injEq] at hrq
  obtain ⟨t, -, -, rfl⟩ := hrq
  change ∑ σ : D → Bool, ∑ j : D → ι, x j * ∏ l, (t l + (Pi.single (i l) (σ l) : ι → Bool)) (j l) =
    x i
  rw [Finset.sum_comm]
  -- The number of subcubes containing `j`, modulo two, is the indicator of `j = i`.
  have hcount (j : D → ι) :
      ∑ σ : D → Bool, ∏ l, (t l + (Pi.single (i l) (σ l) : ι → Bool)) (j l) =
        if j = i then 1 else 0 := by
    rw [← prod_single_eq,
      ← Fintype.prod_sum (fun l (b : Bool) => (t l + (Pi.single (i l) b : ι → Bool)) (j l))]
    exact Finset.prod_congr rfl fun l _ => sum_bool_add_single (t l) (i l) (j l)
  simp only [← Finset.mul_sum, hcount, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- The subcube scheme sends `d` sets of `ℓ` bits to each of the `2 ^ d` servers and receives one
bit from each: `2 ^ d (d ℓ + 1)` bits [CGKS, Section 3.2][ChorGoldreichKushilevitzSudan1998]. -/
theorem communication_cube :
    communication (D → Bool) (D → ι → Bool) Bool =
      2 ^ Fintype.card D * (Fintype.card D * Fintype.card ι + 1) := by
  rw [communication_eq, Fintype.card_fun, Fintype.card_fun, Fintype.card_fun, Fintype.card_bool,
    ← pow_mul, Nat.clog_pow 2 _ (by norm_num), Nat.clog_eq_one le_rfl le_rfl,
    Nat.mul_comm (Fintype.card ι)]

/-- The server `σ` of the subcube scheme answers with the sum of the database over its subcube. -/
theorem answer_cube (σ : D → Bool) (x : (D → ι) → Bool) (a : D → ι → Bool) :
    (cube D ι).answer σ x a = ∑ j : D → ι, x j * ∏ l, a l (j l) := by
  rfl

/-- The user of the subcube scheme adds the answers of all `2 ^ d` servers. -/
theorem reconstruct_cube (i : D → ι) (r : Unit) (a : (D → Bool) → Bool) :
    (cube D ι).reconstruct i r a = ∑ σ, a σ := by
  rfl

/-- Flipping the coordinate `l` of a server of the subcube scheme flips the membership of `i l` in
its `l`-th set: the query of `update σ l (!σ l)` is that of `σ` with `e_{i l}` added at `l`. This is
what lets one server emulate its neighbours [CGKS, Section 3.3][ChorGoldreichKushilevitzSudan1998].
-/
theorem query_update_cube {i : D → ι} {r : Unit} {q : (D → Bool) → D → ι → Bool}
    (hrq : (r, q) ∈ (ProbComp.eval ((cube D ι).query i)).support) (σ : D → Bool) (l : D) :
    q (Function.update σ l (!σ l)) =
      Function.update (q σ) l (q σ l + Pi.single (i l) true) := by
  simp only [cube, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, Prod.mk.injEq] at hrq
  obtain ⟨t, -, -, rfl⟩ := hrq
  funext l'
  beta_reduce
  by_cases hl : l' = l
  · rw [hl]
    simp only [Function.update_self]
    rw [add_assoc, ← Pi.single_add]
    cases σ l <;> rfl
  · simp only [Function.update_of_ne hl]

end Cube

/-! ### Schemes for `n`-bit databases -/

/-- **Two servers with `4 m` bits** [CGKS, Corollary 3][ChorGoldreichKushilevitzSudan1998]: every
`n ≤ m ^ 2` has a perfectly correct and perfectly private two-server scheme for `n`-bit databases
communicating `4 m` bits. -/
theorem hasScheme_two_of_le_mul_self {n m : ℕ} (h : n ≤ m * m) : HasScheme (Fin n) 2 (4 * m) := by
  let e : Fin n ↪ Fin m × Fin m := (Fin.castLEEmb h).trans finProdFinEquiv.symm.toEmbedding
  have hP := (isCorrect_twoServer.rows (Fin m)).comap e
    |>.hasScheme ((isPrivate_twoServer.rows (Fin m)).comap e)
  rw [Fintype.card_bool, communication_twoServer_rows, Fintype.card_fin] at hP
  exact hP.mono (by omega)

/-- Two servers with `4 (⌊√n⌋ + 1)` bits. -/
theorem hasScheme_two_sqrt (n : ℕ) : HasScheme (Fin n) 2 (4 * (Nat.sqrt n + 1)) :=
  hasScheme_two_of_le_mul_self (Nat.lt_succ_sqrt n).le

/-- **`2 ^ d` servers with `2 ^ d (d ℓ + 1)` bits**
[CGKS, Section 3.2][ChorGoldreichKushilevitzSudan1998]: every `n ≤ ℓ ^ d` has a perfectly correct
and perfectly private `2 ^ d`-server scheme for `n`-bit databases communicating `2 ^ d (d ℓ + 1)`
bits. With `ℓ = ⌈n ^ (1/d)⌉` this is the source's `2 ^ d (d n ^ (1/d) + 1)`. -/
theorem hasScheme_two_pow_of_le_pow {n d ℓ : ℕ} (h : n ≤ ℓ ^ d) :
    HasScheme (Fin n) (2 ^ d) (2 ^ d * (d * ℓ + 1)) := by
  let e : Fin n ↪ (Fin d → Fin ℓ) :=
    (Fin.castLEEmb h).trans finFunctionFinEquiv.symm.toEmbedding
  have hP := isCorrect_cube.comap e |>.hasScheme (isPrivate_cube.comap e)
  rwa [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, communication_cube,
    Fintype.card_fin, Fintype.card_fin] at hP

end Cslib.Crypto.Protocols.PIR
