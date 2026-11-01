/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Ary.Basic
public import Complexity.Foundations.BooleanAnalysis.MultilinearExtension
public import Complexity.Foundations.FieldTheory.Finite.UnitSum

/-!
# The Cook–Mertz procedure for Tree Evaluation with fan-in `d`

This generalizes the binary procedure `Cslib.TreeEval.proc` to fan-in `d`; at `d = 2` it is that
procedure step for step (`Cslib.TreeEval.Ary.proc_ofBinary`, proved beside the binary procedure,
which derives its correctness from this file). The procedure keeps `d + 1` registers, each
holding `ℓ` elements of a finite field `K`, as global storage shared by all levels of the
recursion. Called on a subtree, a coefficient `c` and a target register `t`, it adds `c` times the
value of the subtree (read as `0`/`1` field elements) to register `t` and leaves the other `d`
registers unchanged, whatever their contents.

The child `j` of a target `t` uses the register `reg t j = t + (j + 1)`, so the `d` children use
exactly the registers other than `t`; for `d = 2` these are the registers `t + 1` and `t + 2` of
the binary procedure. At an internal node with gate `f`, the procedure runs one round for every
unit `u` of `K`. A round scales the child registers by `u`, adds the children's values to them by
recursive calls, subtracts `c` times the multilinear extension of `f` at the masked values from
register `t`, and then undoes the recursive calls and the scaling. Summed over all units, the masks
cancel (`FiniteField.sum_units_eval_mul_add`), because the extension has degree at most
`d * ℓ < |K| - 1`, and register `t` has gained `c • f (v₀, …, v_{d-1})`.

`procWith` separates the Boolean value length from the register width and accepts a supplied
value representation and gate extension. Its correctness requires only a signed unmasking law;
this lets packed finite-alphabet extensions reuse the same masking proof. The original
multilinear procedure is its exact specialization (`procWith_embed`).

This file proves correctness only; space bounds are separate.

## Main definitions

* `Cslib.TreeEval.embed`: an `ℓ`-bit value read as `0`/`1` field elements, for any fan-in.
* `Cslib.TreeEval.Ary.reg`: the register of a child.
* `Cslib.TreeEval.Ary.gatePoly`: the multilinear extension of an output bit of a gate.
* `Cslib.TreeEval.Ary.proc`: the procedure, parametrized by an enumeration of the units of `K`.
* `Cslib.TreeEval.Ary.procWith`: the procedure with a supplied representation and gate extension.

## Main results

* `Cslib.TreeEval.Ary.procWith_eq`: correctness for any supplied extension satisfying unmasking.
* `Cslib.TreeEval.Ary.procWith_embed`: the multilinear procedure is a specialization, round for
  round.

* `Cslib.TreeEval.Ary.proc_eq`: the procedure adds `c` times the value of the tree to the target
  register and leaves the other registers unchanged.
* `Cslib.TreeEval.Ary.proc_zero`: started from zero registers, it leaves the value of the tree in
  the target register.
* `Cslib.TreeEval.Ary.embed_eval_eq_proc`: the same, for the canonical enumeration of the units.

## References

* [J. Cook and I. Mertz, *Tree Evaluation is in Space O(log n · log log n)*][CookMertz2024],
  Lemma 13 and Theorem 10, for fan-in `d`.
* [O. Goldreich, *On the Cook–Mertz Tree Evaluation procedure*][Goldreich2024TreeEval],
  Algorithm 1, whose signed recursive calls are followed here.
-/

@[expose] public section

open MvPolynomial Cslib.BitString

namespace Cslib.TreeEval

variable {K : Type*} [Field K] {d ℓ : ℕ}

/-- An `ℓ`-bit value read as `0`/`1` field elements. -/
def embed (v : Fin ℓ → Bool) : Fin ℓ → K := fun i => bitVal K (v i)

namespace Ary

/-- The global storage: `d + 1` registers of `ℓ` field elements. -/
abbrev State (K : Type*) (d ℓ : ℕ) := Fin (d + 1) → Fin ℓ → K

/-- The register of child `j` when the target register is `t`. -/
def reg (t : Fin (d + 1)) (j : Fin d) : Fin (d + 1) := t + j.succ

private theorem reg_ne (t : Fin (d + 1)) (j : Fin d) : reg t j ≠ t := by
  simp [reg, Fin.succ_ne_zero]

private theorem reg_injective (t : Fin (d + 1)) : Function.Injective (reg t) := by
  intro a b h
  simpa [reg] using h

/-- The children's registers are exactly the registers other than the target. -/
private theorem mem_map_reg_finRange {t r : Fin (d + 1)} :
    r ∈ (List.finRange d).map (reg t) ↔ r ≠ t := by
  refine ⟨?_, fun hr => ?_⟩
  · simp only [List.mem_map, List.mem_finRange, true_and]
    rintro ⟨j, rfl⟩
    exact reg_ne t j
  · have h0 : r - t ≠ 0 := sub_ne_zero.mpr hr
    refine List.mem_map.mpr ⟨(r - t).pred h0, List.mem_finRange _, ?_⟩
    simp [reg]

/-- The value of the child whose register is `r`, and `0` at the target register. -/
def childVal (t : Fin (d + 1)) (v : Fin d → Fin ℓ → K) (r : Fin (d + 1)) : Fin ℓ → K :=
  if h : r - t = 0 then 0 else v ((r - t).pred h)

@[simp] theorem childVal_reg (t : Fin (d + 1)) (v : Fin d → Fin ℓ → K) (j : Fin d) :
    childVal t v (reg t j) = v j := by
  simp [childVal, reg, Fin.succ_ne_zero]

/-- The multilinear extension of output bit `i` of a gate, in the bits of all its inputs. -/
noncomputable def gatePoly (f : Gate d ℓ) (i : Fin ℓ) : MvPolynomial (Fin d × Fin ℓ) K :=
  multilinearExtension fun z => bitVal K (f (fun j k => z (j, k)) i)

/-- Multiply register `r` by `a`. -/
def scale (r : Fin (d + 1)) (a : K) (S : State K d ℓ) : State K d ℓ :=
  Function.update S r (a • S r)

/-- The update of a round at a gate `f`: subtract `c` times the gate's extension at the child
registers from register `t`. -/
noncomputable def gateUpdate (f : Gate d ℓ) (c : K) (t : Fin (d + 1)) (S : State K d ℓ) :
    State K d ℓ :=
  Function.update S t fun i => S t i - c * eval (fun q => S (reg t q.1) q.2) (gatePoly f i)

/-- One round of the procedure at a gate `f`, for the unit `u`, given procedures `p j` for the
subtrees. The target is `t`, and the child registers `reg t j` hold the masks. -/
noncomputable def gateRound (p : Fin d → K → Fin (d + 1) → State K d ℓ → State K d ℓ)
    (f : Gate d ℓ) (c : K) (t : Fin (d + 1)) (u : Kˣ) (S : State K d ℓ) : State K d ℓ :=
  let S := (List.finRange d).foldl (fun S j => p j 1 (reg t j) (scale (reg t j) (u : K) S)) S
  let S := gateUpdate f c t S
  (List.finRange d).foldl
    (fun S j => scale (reg t j) ((u⁻¹ : Kˣ) : K) (p j (-1) (reg t j) S)) S

/-- The Cook–Mertz procedure: add `c` times the value of the tree to register `t`. At a gate it
runs one `gateRound` for every unit in the enumeration `us`. -/
noncomputable def proc (us : List Kˣ) :
    {h : ℕ} → Tree d ℓ h → K → Fin (d + 1) → State K d ℓ → State K d ℓ
  | _, .leaf v, c, t, S => Function.update S t (S t + c • embed v)
  | _, .node f ch, c, t, S =>
      us.foldl (fun S u => gateRound (fun j => proc us (ch j)) f c t u S) S

variable {r : ℕ}

/-- Subtract a coefficient times a supplied gate extension from the target register. The
extension may use a different number of field coordinates from the gate's bit length. -/
def gateUpdateWith (E : Gate d ℓ → (Fin d → Fin r → K) → Fin r → K)
    (f : Gate d ℓ) (c : K) (t : Fin (d + 1)) (S : State K d r) : State K d r :=
  Function.update S t fun i => S t i - c * E f (fun j => S (reg t j)) i

/-- A masking round with a supplied gate extension, sharing the same registers across recursive
calls. No polynomial representation or relation between bit length and register width is needed. -/
def gateRoundWith (E : Gate d ℓ → (Fin d → Fin r → K) → Fin r → K)
    (p : Fin d → K → Fin (d + 1) → State K d r → State K d r)
    (f : Gate d ℓ) (c : K) (t : Fin (d + 1)) (u : Kˣ) (S : State K d r) : State K d r :=
  let S := (List.finRange d).foldl (fun S j => p j 1 (reg t j) (scale (reg t j) (u : K) S)) S
  let S := gateUpdateWith E f c t S
  (List.finRange d).foldl
    (fun S j => scale (reg t j) ((u⁻¹ : Kˣ) : K) (p j (-1) (reg t j) S)) S

/-- The Cook–Mertz procedure with a supplied representation of bit values and gate extension.
The representation has `r` field coordinates, independently of the `ℓ` bits in a value. -/
def procWith (e : (Fin ℓ → Bool) → Fin r → K)
    (E : Gate d ℓ → (Fin d → Fin r → K) → Fin r → K) (us : List Kˣ) :
    {h : ℕ} → Tree d ℓ h → K → Fin (d + 1) → State K d r → State K d r
  | _, .leaf v, c, t, S => Function.update S t (S t + c • e v)
  | _, .node f ch, c, t, S =>
      us.foldl (fun S u => gateRoundWith E (fun j => procWith e E us (ch j)) f c t u S) S

/-- The multilinear procedure is the supplied-extension procedure with one field coordinate
per bit. This specialization preserves every recursive masking round. -/
theorem procWith_embed (us : List Kˣ) {h : ℕ} (T : Tree d ℓ h) :
    procWith embed (fun f x i => eval (fun q => x q.1 q.2) (gatePoly f i)) us T =
      proc us T := by
  induction T with
  | leaf v => rfl
  | node f ch ih =>
    funext c t S
    simp only [procWith, proc, ih]
    rfl

omit [Field K] in
/-- Updating each child register in turn, as a function of its previous content, updates all
registers other than the target. -/
private theorem foldl_update_reg (t : Fin (d + 1)) (g : Fin (d + 1) → (Fin ℓ → K) → Fin ℓ → K)
    (l : List (Fin d)) (hl : l.Nodup) (S : State K d ℓ) :
    l.foldl (fun S j => Function.update S (reg t j) (g (reg t j) (S (reg t j)))) S =
      fun r => if r ∈ l.map (reg t) then g r (S r) else S r := by
  induction l generalizing S with
  | nil => simp
  | cons j l ih =>
    obtain ⟨hj, hl⟩ := List.nodup_cons.mp hl
    rw [List.foldl_cons, ih hl]
    funext r
    by_cases hr : r = reg t j
    · subst hr
      have hn : reg t j ∉ l.map (reg t) := by
        rw [List.mem_map]
        rintro ⟨k, hk, hkj⟩
        exact hj (reg_injective t hkj ▸ hk)
      simp [hn]
    · simp [List.mem_cons, hr]

/-- A round, when all subtree procedures meet their specification, changes only the target
register, subtracting `c` times the gate's extension at the masked children's values. -/
private theorem gateRoundWith_eq
    (E : Gate d ℓ → (Fin d → Fin r → K) → Fin r → K)
    {p : Fin d → K → Fin (d + 1) → State K d r → State K d r}
    {v : Fin d → Fin r → K} (hp : ∀ j c t S, p j c t S = Function.update S t (S t + c • v j))
    (f : Gate d ℓ) (c : K) (t : Fin (d + 1)) (u : Kˣ) (S : State K d r) :
    gateRoundWith E p f c t u S = Function.update S t fun i =>
      S t i - c * E f (fun j k => (u : K) * S (reg t j) k + v j k) i := by
  have hnd := List.nodup_finRange d
  have e1 (S : State K d r) :
      (List.finRange d).foldl (fun S j => p j 1 (reg t j) (scale (reg t j) (u : K) S)) S =
        fun r => if r ≠ t then (u : K) • S r + childVal t v r else S r := by
    have h1 : (fun S j => p j 1 (reg t j) (scale (reg t j) (u : K) S)) =
        fun (S : State K d r) j => Function.update S (reg t j)
          ((fun r x => (u : K) • x + childVal t v r) (reg t j) (S (reg t j))) := by
      funext S j
      simp [hp, scale]
    rw [h1, foldl_update_reg t (fun r x => (u : K) • x + childVal t v r) _ hnd]
    simp only [mem_map_reg_finRange]
  have e3 (S : State K d r) :
      (List.finRange d).foldl
          (fun S j => scale (reg t j) ((u⁻¹ : Kˣ) : K) (p j (-1) (reg t j) S)) S =
        fun r => if r ≠ t then ((u⁻¹ : Kˣ) : K) • (S r - childVal t v r) else S r := by
    have h3 : (fun S j => scale (reg t j) ((u⁻¹ : Kˣ) : K) (p j (-1) (reg t j) S)) =
        fun (S : State K d r) j => Function.update S (reg t j)
          ((fun r x => ((u⁻¹ : Kˣ) : K) • (x - childVal t v r)) (reg t j) (S (reg t j))) := by
      funext S j
      simp [hp, scale, sub_eq_add_neg]
    rw [h3, foldl_update_reg t (fun r x => ((u⁻¹ : Kˣ) : K) • (x - childVal t v r)) _ hnd]
    simp only [mem_map_reg_finRange]
  have harg (t : Fin (d + 1)) :
      (fun j => (u : K) • S (reg t j) + v j) =
        (fun j k => (u : K) * S (reg t j) k + v j k) := rfl
  dsimp only [gateRoundWith]
  rw [e1, e3]
  funext r i
  by_cases hr : r = t
  · subst hr
    simp [gateUpdateWith, reg_ne, harg]
  · simp [gateUpdateWith, hr]

/-- The rounds for all units in `us` change only the target register, subtracting `c` times the
sum of the gate's extension at the masked children's values. -/
private theorem foldl_gateRoundWith_eq
    (E : Gate d ℓ → (Fin d → Fin r → K) → Fin r → K)
    {p : Fin d → K → Fin (d + 1) → State K d r → State K d r}
    {v : Fin d → Fin r → K} (hp : ∀ j c t S, p j c t S = Function.update S t (S t + c • v j))
    (f : Gate d ℓ) (c : K) (t : Fin (d + 1)) (us : List Kˣ) (S : State K d r) :
    us.foldl (fun S u => gateRoundWith E p f c t u S) S = Function.update S t fun i =>
      S t i - c * (us.map fun u : Kˣ =>
        E f (fun j k => (u : K) * S (reg t j) k + v j k) i).sum := by
  induction us generalizing S with
  | nil => simp
  | cons u us ih =>
    rw [List.foldl_cons, gateRoundWith_eq E hp, ih, Function.update_idem, Function.update_self]
    congr 1
    funext i
    have hreg (j : Fin d) : Function.update S t (fun i =>
        S t i - c * E f (fun j k => (u : K) * S (reg t j) k + v j k) i)
          (reg t j) = S (reg t j) := Function.update_of_ne (reg_ne t j) _ _
    simp only [hreg, List.map_cons, List.sum_cons]
    ring

variable [Fintype K]

/-- **Correctness with a supplied gate extension.** The unmasking identity is the only
property required of the representation and extension: the sum over all nonzero masks must be
minus the represented gate value. The conclusion holds from arbitrary initial register contents. -/
theorem procWith_eq [DecidableEq K]
    (e : (Fin ℓ → Bool) → Fin r → K)
    (E : Gate d ℓ → (Fin d → Fin r → K) → Fin r → K)
    (hE : ∀ (f : Gate d ℓ) (v : Fin d → Fin ℓ → Bool) (τ : Fin d → Fin r → K) (i : Fin r),
      ∑ u : Kˣ, E f (fun j k => (u : K) * τ j k + e (v j) k) i = -e (f v) i)
    {us : List Kˣ} (hnd : us.Nodup) (hmem : ∀ u, u ∈ us)
    {h : ℕ} (T : Tree d ℓ h) (c : K) (t : Fin (d + 1)) (S : State K d r) :
    procWith e E us T c t S = Function.update S t (S t + c • e T.eval) := by
  induction T generalizing c t S with
  | leaf v => rfl
  | node f ch ih =>
    rw [procWith, foldl_gateRoundWith_eq E (v := fun j => e (ch j).eval) fun j => ih j]
    congr 1
    funext i
    rw [← List.sum_toFinset _ hnd, show us.toFinset = Finset.univ by ext; simp [hmem]]
    rw [hE]
    simp [Tree.eval]

/-- **Correctness of the Cook–Mertz procedure for fan-in `d`.** If `us` enumerates the units of
`K` without repetition and `d * ℓ < |K| - 1`, then the procedure adds `c` times the value of the
tree to the target register and leaves the other registers unchanged, whatever their initial
contents. -/
theorem proc_eq {us : List Kˣ} (hnd : us.Nodup) (hmem : ∀ u, u ∈ us)
    (hK : d * ℓ < Fintype.card K - 1) {h : ℕ} (T : Tree d ℓ h) (c : K) (t : Fin (d + 1))
    (S : State K d ℓ) : proc us T c t S = Function.update S t (S t + c • embed T.eval) := by
  classical
  rw [← procWith_embed]
  apply procWith_eq embed (fun f x i => eval (fun q => x q.1 q.2) (gatePoly f i))
    (fun f v τ i => ?_) hnd hmem
  have hdeg : (gatePoly (K := K) f i).totalDegree < Fintype.card K - 1 :=
    (totalDegree_multilinearExtension_le _).trans_lt <| by simpa using hK
  have hsum := FiniteField.sum_units_eval_mul_add hdeg
    (fun q => τ q.1 q.2) (fun q => bitVal K (v q.1 q.2))
  simpa only [gatePoly, eval_multilinearExtension, embed] using hsum

/-- Started from zero registers, the procedure leaves the value of the tree in the target
register. -/
theorem proc_zero {us : List Kˣ} (hnd : us.Nodup) (hmem : ∀ u, u ∈ us)
    (hK : d * ℓ < Fintype.card K - 1) {h : ℕ} (T : Tree d ℓ h) (t : Fin (d + 1)) :
    proc us T 1 t 0 t = embed T.eval := by
  simp [proc_eq hnd hmem hK]

/-- **Tree Evaluation with fan-in `d` by the Cook–Mertz procedure.** Run over the units of `K` in
any order with `d * ℓ < |K| - 1`, from zero registers, the procedure computes the value of the
tree into the target register. -/
theorem embed_eval_eq_proc [DecidableEq K] (hK : d * ℓ < Fintype.card K - 1) {h : ℕ}
    (T : Tree d ℓ h) (t : Fin (d + 1)) :
    embed T.eval = proc (Finset.univ : Finset Kˣ).toList T 1 t 0 t :=
  (proc_zero (Finset.nodup_toList _) (fun _ => Finset.mem_toList.mpr (Finset.mem_univ _)) hK T
    t).symm

end Ary

end Cslib.TreeEval
