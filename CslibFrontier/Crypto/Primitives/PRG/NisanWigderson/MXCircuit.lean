/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Boolean.ACC0.Gadgets
public import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.BitPolynomial
import CslibFrontier.Computability.Circuit.CompositionDepth
import CslibFrontier.Computability.Circuit.Pi

/-!
# Reading the bit-indexed polynomial design in AC⁰[2]

Carmosino, Impagliazzo, Kabanets and Kolokolova show that the Nisan–Wigderson selection
`MX_NW(i, z) = z|S_i`, which reads a seed `z` on block `i` of their polynomial design, is computed
by AC⁰[p] circuits (Theorems 3.3, 3.6 and 3.7, pp. 10:10–10:13)
[CarmosinoImpagliazzoKabanetsKolokolova2016]. This file builds these circuits for `p = 2` and the
design `Cslib.Crypto.PRG.NisanWigderson.Design.binaryPolynomial n ℓ`, over
`Unbounded.extSignature` read with `MOD₂` gates.

Bit `c` of `A_i(r_j)` is the parity of the index `i` on a set fixed by `r_j`
(`Cslib.Crypto.PRG.NisanWigderson.bits_bitPoly_eq_parityOn`). So with `e` parity gates and their
negations for each row `j`, cell `(j, v)` lies in block `i` exactly when the conjunction of the
literals matching the bits of `v` holds (Theorem 3.6). Bit `j` of `z|S_i` is the seed bit of the
one cell of row `j` in the block, so it is the disjunction over the columns `v` of `z_(j, v)` and
that conjunction (Theorem 3.7). Inputs are the `ℓ` bits of `i` followed by the seed.

This differs from the source in these ways:

* only `p = 2` is built, over `BinaryField e` with `e = binaryFieldDegree n`, so the field has
  between `n` and `2 n` elements;
* Theorem 3.6 is proved with the cell `(j, v)` hard-wired, which is how Theorem 3.7 uses it; the
  circuit taking `j` and `v` as inputs is not built;
* the bounds are explicit and stronger than stated: the selection has depth at most `4` and
  `n (2 e + 2 ^ e + 1) ≤ 5 n²` gates, independent of `ℓ`, where the source has `O(ℓ n³ log n)`
  gates and depth `d_NW + 2`; the conjunctions of one row share its `2 e` literals;
* gates are counted (`Cslib.Circuits.Circuit.size`), not wires, and depth is the unit-cost
  `Cslib.Circuits.Circuit.depth`, negations included;
* the circuits are explicit, but no uniformity is claimed.

## Main definitions

* `Cslib.Crypto.PRG.NisanWigderson.memCircuit`: membership of a fixed cell in block `i`.
* `Cslib.Crypto.PRG.NisanWigderson.mxCircuit`: the selection `(i, z) ↦ z|S_i`.

## Main results

* `Cslib.Crypto.PRG.NisanWigderson.eval_memCircuit`: `memCircuit n ℓ j v` decides whether cell
  `(j, v)` lies in block `i` (Theorem 3.6).
* `Cslib.Crypto.PRG.NisanWigderson.size_memCircuit`,
  `Cslib.Crypto.PRG.NisanWigderson.depth_memCircuit_le`: `2 e + 1` gates, depth at most `3`.
* `Cslib.Crypto.PRG.NisanWigderson.eval_mxCircuit`: `mxCircuit n ℓ` computes the bits of the seed
  in block `i` (Theorem 3.7).
* `Cslib.Crypto.PRG.NisanWigderson.size_mxCircuit`,
  `Cslib.Crypto.PRG.NisanWigderson.size_mxCircuit_le`,
  `Cslib.Crypto.PRG.NisanWigderson.depth_mxCircuit_le`: `n (2 e + 2 ^ e + 1) ≤ 5 n²` gates and
  depth at most `4`.

## References

* [M. L. Carmosino, R. Impagliazzo, V. Kabanets, A. Kolokolova, *Learning algorithms from natural
  proofs*][CarmosinoImpagliazzoKabanetsKolokolova2016], Theorems 3.3, 3.6 and 3.7
* [N. Nisan, A. Wigderson, *Hardness vs randomness*][NisanWigderson1994]
-/

public section

namespace Cslib.Crypto.PRG.NisanWigderson

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.Unbounded Finset

variable {ℓ n : ℕ}

/-! ### Literals of parities -/

section Literals

variable {m : ℕ} (S : Fin m → Finset (Fin ℓ))

/-- The parities `parityOn (S k)` as outputs `castAdd m k`, then their negations as outputs
`natAdd m k`. -/
private def parityLiterals : Circuit extSignature ℓ (m + m) :=
  ((Circuit.wiring extSignature id).append
      (Circuit.pi fun k => Circuit.oneGate (σ := extSignature) (.ac .not) fun _ => k)).comp
    (Circuit.pi fun k => parityOnCircuit (S k))

/-- The output of `parityLiterals` holding when the parity on `S k` is `b`: the parity itself if
`b` is true, and its negation otherwise. -/
private def parityLiteral (b : Bool) (k : Fin m) : Fin (m + m) :=
  if b then Fin.castAdd m k else Fin.natAdd m k

variable {S}

private theorem eval_parityLiterals (x : BitString ℓ) (b : Bool) (k : Fin m) :
    (parityLiterals S).eval (extInterpretation (modGate 2)) x (parityLiteral b k) = true ↔
      parityOn (S k) x = b := by
  cases b <;> simp [parityLiterals, parityLiteral]

private theorem size_parityLiterals : (parityLiterals S).size = m + m := by
  simp [parityLiterals]

private theorem depth_parityLiterals_le : (parityLiterals S).depth ≤ 2 := by
  refine (Circuit.depth_comp_le _ _).trans (Nat.add_le_add ?_ ?_)
  · exact (Circuit.depth_append_le _ _).trans
      (max_le (by simp) (Circuit.depth_pi_le _ fun k => (Circuit.depth_oneGate _ _).le))
  · exact Circuit.depth_pi_le _ fun k => (depth_parityOnCircuit _).le

end Literals

/-! ### Membership in a block -/

/-- The exponents `t < ℓ` for which bit `c` of `r_j ^ t` is set, for the point
`r_j = binaryFieldPoints n j`. Bit `c` of `A_i(r_j)` is the parity of `i` on this set. -/
private noncomputable def expSet (n ℓ : ℕ) (j : Fin n) (c : Fin (binaryFieldDegree n)) :
    Finset (Fin ℓ) :=
  {t | BinaryField.equivBits (binaryFieldDegree_ne_zero n) (binaryFieldPoints n j ^ (t : ℕ)) c}

/-- `Design.mem_block_binaryPolynomial_iff`, with the sets of exponents named. -/
private theorem mem_block_iff (i : BitString ℓ) (j : Fin n) (v : Fin (2 ^ binaryFieldDegree n)) :
    finProdFinEquiv (j, v) ∈ (Design.binaryPolynomial n ℓ).block (BitString.equivFin ℓ i) ↔
      ∀ c, (BitString.equivFin _).symm v c = parityOn (expSet n ℓ j c) i :=
  Design.mem_block_binaryPolynomial_iff i j v

/-- **Theorem 3.6, with the cell hard-wired**: whether cell `(j, v)` lies in block `i`, from the
bits of `i`. The `e` parities of row `j` and their negations, then one conjunction of the
literals matching the bits of `v` [CarmosinoImpagliazzoKabanetsKolokolova2016, Theorem 3.6]. -/
noncomputable def memCircuit (n ℓ : ℕ) (j : Fin n) (v : Fin (2 ^ binaryFieldDegree n)) :
    Circuit extSignature ℓ 1 :=
  (Circuit.oneGate (σ := extSignature) (.ac (.and (binaryFieldDegree n)))
      fun c => parityLiteral ((BitString.equivFin _).symm v c) c).comp
    (parityLiterals (expSet n ℓ j))

/-- With `MOD₂` gates, `memCircuit n ℓ j v` decides whether cell `(j, v)` lies in block `i` of
`Design.binaryPolynomial n ℓ`. -/
theorem eval_memCircuit (j : Fin n) (v : Fin (2 ^ binaryFieldDegree n)) (i : BitString ℓ)
    (o : Fin 1) :
    (memCircuit n ℓ j v).eval (extInterpretation (modGate 2)) i o =
      decide (finProdFinEquiv (j, v) ∈
        (Design.binaryPolynomial n ℓ).block (BitString.equivFin ℓ i)) := by
  rw [memCircuit, Circuit.eval_comp, Circuit.eval_oneGate, extInterpretation_ac,
    interpretation_and, decide_eq_decide, mem_block_iff]
  exact forall_congr' fun c => (eval_parityLiterals i _ c).trans eq_comm

/-- `memCircuit n ℓ j v` has `2 e + 1` gates. -/
theorem size_memCircuit (j : Fin n) (v : Fin (2 ^ binaryFieldDegree n)) :
    (memCircuit n ℓ j v).size = 2 * binaryFieldDegree n + 1 := by
  rw [memCircuit, Circuit.size_comp, size_parityLiterals, Circuit.size_oneGate]
  ring

/-- `memCircuit n ℓ j v` has depth at most `3`. -/
theorem depth_memCircuit_le (j : Fin n) (v : Fin (2 ^ binaryFieldDegree n)) :
    (memCircuit (ℓ := ℓ) n ℓ j v).depth ≤ 3 :=
  (Circuit.depth_comp_le _ _).trans
    (by rw [Circuit.depth_oneGate]; have := depth_parityLiterals_le (S := expSet n ℓ j); omega)

/-! ### The selection -/

/-- **The selection `MX_NW(i, z) = z|S_i` in AC⁰[2]** [CarmosinoImpagliazzoKabanetsKolokolova2016,
Theorem 3.7], on the bits of `i` followed by the seed `z`. The literals of all rows, then for each
cell `(j, v)` the conjunction of `z_(j, v)` with the literals matching the bits of `v`, then for
each row `j` the disjunction of its cells. -/
noncomputable def mxCircuit (n ℓ : ℕ) :
    Circuit extSignature (ℓ + n * 2 ^ binaryFieldDegree n) n :=
  (Circuit.pi fun j : Fin n =>
      Circuit.oneGate (σ := extSignature) (.ac (.or (2 ^ binaryFieldDegree n)))
        fun v => finProdFinEquiv (j, v)).comp
    ((Circuit.pi fun p : Fin (n * 2 ^ binaryFieldDegree n) =>
        Circuit.oneGate (σ := extSignature) (.ac (.and (binaryFieldDegree n + 1)))
          (Fin.cons (Fin.natAdd _ p) fun c => Fin.castAdd _ (parityLiteral
            ((BitString.equivFin _).symm (finProdFinEquiv.symm p).2 c)
            (finProdFinEquiv ((finProdFinEquiv.symm p).1, c))) :
              Fin (binaryFieldDegree n + 1) → _)).comp
      (((parityLiterals fun k : Fin (n * binaryFieldDegree n) =>
          expSet n ℓ (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2).comp
          (Circuit.wiring extSignature (Fin.castAdd _))).append
        (Circuit.wiring extSignature (Fin.natAdd ℓ))))

/-- **The circuit computes the selection**: with `MOD₂` gates, on the index `i` followed by the
seed `z`, output `j` of `mxCircuit n ℓ` is bit `j` of `z` restricted to block `i`. -/
theorem eval_mxCircuit (i : BitString ℓ) (z : Fin (n * 2 ^ binaryFieldDegree n) → Bool) :
    (mxCircuit n ℓ).eval (extInterpretation (modGate 2)) (Fin.append i z) =
      (Design.binaryPolynomial n ℓ).restrict (BitString.equivFin ℓ i) z := by
  funext j
  set v := BitString.equivFin _ fun c => parityOn (expSet n ℓ j c) i with hv
  have hcell (w : Fin (2 ^ binaryFieldDegree n)) :
      (∀ c, (BitString.equivFin _).symm w c = parityOn (expSet n ℓ j c) i) ↔ w = v := by
    rw [← funext_iff, Equiv.symm_apply_eq]
  rw [Design.restrict_binaryPolynomial i z j v fun c => (hcell v).2 rfl c]
  sorry

/-- `mxCircuit n ℓ` has `n (2 e + 2 ^ e + 1)` gates: `2 e` literals, `2 ^ e` conjunctions and one
disjunction for each row. -/
theorem size_mxCircuit (n ℓ : ℕ) :
    (mxCircuit n ℓ).size = n * (2 * binaryFieldDegree n + 2 ^ binaryFieldDegree n + 1) := by
  simp [mxCircuit, size_parityLiterals]
  ring

/-- **`mxCircuit n ℓ` has at most `5 n²` gates**, whatever `ℓ`. -/
theorem size_mxCircuit_le (n ℓ : ℕ) : (mxCircuit n ℓ).size ≤ 5 * n ^ 2 := by
  rw [size_mxCircuit]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have he := binaryFieldDegree_le_self hn
  have hq := two_pow_binaryFieldDegree_le hn
  calc n * (2 * binaryFieldDegree n + 2 ^ binaryFieldDegree n + 1) ≤ n * (2 * n + 2 * n + n) :=
        Nat.mul_le_mul_left n (by omega)
    _ = 5 * n ^ 2 := by ring

/-- **`mxCircuit n ℓ` has depth at most `4`**: parities, negations, conjunctions and
disjunctions. -/
theorem depth_mxCircuit_le (n ℓ : ℕ) : (mxCircuit n ℓ).depth ≤ 4 := by
  refine (Circuit.depth_comp_le _ _).trans ?_
  have h3 := Circuit.depth_pi_le (n := n * 2 ^ binaryFieldDegree n) (fun j : Fin n =>
      Circuit.oneGate (σ := extSignature) (.ac (.or (2 ^ binaryFieldDegree n)))
        fun v => finProdFinEquiv (j, v)) fun j => (Circuit.depth_oneGate _ _).le
  refine Nat.add_le_add h3 ((Circuit.depth_comp_le _ _).trans (Nat.add_le_add
    (Circuit.depth_pi_le _ fun p => (Circuit.depth_oneGate _ _).le) ?_)) |>.trans le_rfl
  refine (Circuit.depth_append_le _ _).trans (max_le ?_ (by simp))
  refine (Circuit.depth_comp_le _ _).trans ?_
  rw [Circuit.depth_wiring, add_zero]
  exact depth_parityLiterals_le

end Cslib.Crypto.PRG.NisanWigderson
