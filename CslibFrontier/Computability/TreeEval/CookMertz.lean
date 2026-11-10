/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.TreeEval.Ary.CookMertz

/-!
# The Cook–Mertz procedure for Tree Evaluation

The procedure keeps three registers, each holding `ℓ` elements of a finite field `K`, as global
storage shared by all levels of the recursion. Called on a subtree, a coefficient `c` and a target
register `t`, it adds `c` times the value of the subtree (read as `0`/`1` field elements) to
register `t` and leaves the other two registers unchanged, whatever their contents.

At an internal node with gate `f`, the procedure runs one round for every unit `u` of `K`. A
round scales the two other registers `a` and `b` by `u`, adds the children's values `v₀` and `v₁`
to them by recursive calls, subtracts `c` times the multilinear extension of `f` at the masked
values `u • a + v₀` and `u • b + v₁` from register `t`, and then undoes the recursive calls and the
scaling. Summed over all units, the masks cancel (`FiniteField.sum_units_eval_mul_add`), because
the extension has degree at most `2ℓ < |K| - 1`, and register `t` has gained `c • f v₀ v₁`.

Only the recursion depth, the round counter and the stage within a round are local to a level;
this is what makes the procedure space-efficient. It is the fan-in-`d` procedure
`Cslib.TreeEval.Ary.proc` at `d = 2`, step for step, on the embedded tree: child `0` uses register
`t + 1` and child `1` register `t + 2`, and the extensions of a binary gate and of its fan-in-`2`
reading differ only by the naming of their variables. Its correctness is therefore the case
`d = 2` of `Cslib.TreeEval.Ary.proc_eq`. This file proves correctness only; space bounds are
separate.

## Main definitions

* `Cslib.TreeEval.gatePoly`: the multilinear extension of an output bit of a gate.
* `Cslib.TreeEval.proc`: the procedure, parametrized by an enumeration of the units of `K`.

## Main results

* `Cslib.TreeEval.Ary.proc_ofBinary`: on an embedded binary tree, the fan-in-`d` procedure at
  `d = 2` is the binary procedure.
* `Cslib.TreeEval.proc_eq`: the procedure adds `c` times the value of the tree to the target
  register and leaves the other registers unchanged.
* `Cslib.TreeEval.proc_zero`: started from zero registers, it leaves the value of the tree in the
  target register.
* `Cslib.TreeEval.embed_eval_eq_proc`: the same, for the canonical enumeration of the units.

## References

* [J. Cook and I. Mertz, *Tree Evaluation is in Space O(log n · log log n)*][CookMertz2024],
  Lemma 13 and Theorem 10.
* [O. Goldreich, *On the Cook–Mertz Tree Evaluation procedure*][Goldreich2024TreeEval],
  Algorithm 1, whose signed recursive calls are followed here.
-/

@[expose] public section

open MvPolynomial Cslib.BitString

namespace Cslib.TreeEval

variable {K : Type*} [Field K] {ℓ : ℕ}

/-- The global storage: three registers of `ℓ` field elements. -/
abbrev State (K : Type*) (ℓ : ℕ) := Fin 3 → Fin ℓ → K

/-- The multilinear extension of output bit `i` of a gate, in the bits of both inputs. -/
noncomputable def gatePoly (f : Gate ℓ) (i : Fin ℓ) :
    MvPolynomial (Fin ℓ ⊕ Fin ℓ) K :=
  multilinearExtension fun z => bitVal K (f (z ∘ Sum.inl) (z ∘ Sum.inr) i)

/-- Multiply register `r` by `a`. -/
def scale (r : Fin 3) (a : K) (S : State K ℓ) : State K ℓ :=
  Function.update S r (a • S r)

/-- The update of a round at a gate `f`: subtract `c` times the gate's extension at registers
`t + 1` and `t + 2` from register `t`. -/
noncomputable def gateUpdate (f : Gate ℓ) (c : K)
    (t : Fin 3) (S : State K ℓ) : State K ℓ :=
  Function.update S t fun i => S t i - c * eval (Sum.elim (S (t + 1)) (S (t + 2))) (gatePoly f i)

/-- One round of the procedure at a gate `f`, for the unit `u`, given procedures `pl` and `pr`
for the two subtrees. The target is `t`, and the registers `t + 1` and `t + 2` hold the masks. -/
noncomputable def gateRound (pl pr : K → Fin 3 → State K ℓ → State K ℓ)
    (f : Gate ℓ) (c : K) (t : Fin 3) (u : Kˣ)
    (S : State K ℓ) : State K ℓ :=
  let S := pl 1 (t + 1) (scale (t + 1) (u : K) S)
  let S := pr 1 (t + 2) (scale (t + 2) (u : K) S)
  let S := gateUpdate f c t S
  let S := scale (t + 1) ((u⁻¹ : Kˣ) : K) (pl (-1) (t + 1) S)
  scale (t + 2) ((u⁻¹ : Kˣ) : K) (pr (-1) (t + 2) S)

/-- The Cook–Mertz procedure: add `c` times the value of the tree to register `t`. At a gate it
runs one `gateRound` for every unit in the enumeration `us`. -/
noncomputable def proc (us : List Kˣ) :
    {h : ℕ} → Tree ℓ h → K → Fin 3 → State K ℓ → State K ℓ
  | _, .leaf v, c, t, S => Function.update S t (S t + c • embed v)
  | _, .node f l r, c, t, S => us.foldl (fun S u => gateRound (proc us l) (proc us r) f c t u S) S

/-- The coordinates of the two inputs of a binary gate as the coordinates of the two children of
a gate of fan-in `2`. -/
private def sumEquivProd (ℓ : ℕ) : Fin ℓ ⊕ Fin ℓ ≃ Fin 2 × Fin ℓ :=
  (Equiv.boolProdEquivSum _).symm.trans (finTwoEquiv.symm.prodCongr (Equiv.refl _))

/-- The extension of a binary gate is that of its fan-in-`2` reading, up to naming the
variables. -/
private theorem rename_gatePoly (f : Gate ℓ) (i : Fin ℓ) :
    rename (sumEquivProd ℓ) (gatePoly (K := K) f i) = Ary.gatePoly (Ary.Gate.ofBinary f) i := by
  rw [gatePoly, rename_multilinearExtension]
  rfl

/-- The update of a round of fan-in `2` is the binary update. -/
private theorem gateUpdate_ofBinary (f : Gate ℓ) (c : K) (t : Fin 3) (S : State K ℓ) :
    Ary.gateUpdate (Ary.Gate.ofBinary f) c t S = gateUpdate f c t S := by
  have hS : (fun q => S (Ary.reg t q.1) q.2) ∘ sumEquivProd ℓ =
      Sum.elim (S (t + 1)) (S (t + 2)) := by
    funext x
    cases x <;> rfl
  simp only [Ary.gateUpdate, gateUpdate, ← rename_gatePoly, eval_rename, hS]

/-- A round of fan-in `2` performs the calls, the update and the scalings of a binary round, in
the same order. -/
private theorem gateRound_ofBinary (pl pr : K → Fin 3 → State K ℓ → State K ℓ) (f : Gate ℓ)
    (c : K) (t : Fin 3) (u : Kˣ) (S : State K ℓ) :
    Ary.gateRound ![pl, pr] (Ary.Gate.ofBinary f) c t u S = gateRound pl pr f c t u S := by
  simp only [Ary.gateRound, gateRound, gateUpdate_ofBinary]
  rfl

/-- **The binary procedure is the fan-in-`d` procedure at `d = 2`.** On a binary tree embedded
with fan-in `2`, the fan-in-`d` procedure is the binary procedure, step for step: it acts on the
same three registers (`Fin (2 + 1)` is `Fin 3`), calls the children in the same order with the
same coefficients and target registers, and performs the same updates and scalings. -/
theorem Ary.proc_ofBinary (us : List Kˣ) {h : ℕ} (T : TreeEval.Tree ℓ h) :
    Ary.proc us (Ary.Tree.ofBinary T) = TreeEval.proc us T := by
  induction T with
  | leaf v => rfl
  | node f l r ihl ihr =>
    funext c t S
    have hch : (fun j => Ary.proc us (![Ary.Tree.ofBinary l, Ary.Tree.ofBinary r] j)) =
        ![TreeEval.proc us l, TreeEval.proc us r] := by
      funext j
      fin_cases j <;> assumption
    simp only [Ary.Tree.ofBinary, Ary.proc, TreeEval.proc, hch, gateRound_ofBinary]

variable [Fintype K]

/-- **Correctness of the Cook–Mertz procedure.** If `us` enumerates the units of `K` without
repetition and `2ℓ < |K| - 1`, then the procedure adds `c` times the value of the tree to the
target register and leaves the other registers unchanged, whatever their initial contents. -/
theorem proc_eq {us : List Kˣ} (hnd : us.Nodup) (hmem : ∀ u, u ∈ us)
    (hK : 2 * ℓ < Fintype.card K - 1) {h : ℕ} (T : Tree ℓ h) (c : K) (t : Fin 3)
    (S : State K ℓ) : proc us T c t S = Function.update S t (S t + c • embed T.eval) := by
  rw [← Ary.proc_ofBinary, Ary.proc_eq hnd hmem hK, Ary.Tree.eval_ofBinary]

/-- Started from zero registers, the procedure leaves the value of the tree in the target
register. -/
theorem proc_zero {us : List Kˣ} (hnd : us.Nodup) (hmem : ∀ u, u ∈ us)
    (hK : 2 * ℓ < Fintype.card K - 1) {h : ℕ} (T : Tree ℓ h) (t : Fin 3) :
    proc us T 1 t 0 t = embed T.eval := by
  rw [← Ary.proc_ofBinary, Ary.proc_zero hnd hmem hK, Ary.Tree.eval_ofBinary]

/-- **Tree Evaluation by the Cook–Mertz procedure.** Run over the units of `K` in any order with
`2ℓ < |K| - 1`, from zero registers, the procedure computes the value of the tree into the
target register. -/
theorem embed_eval_eq_proc [DecidableEq K] (hK : 2 * ℓ < Fintype.card K - 1) {h : ℕ} (T : Tree ℓ h)
    (t : Fin 3) : embed T.eval = proc (Finset.univ : Finset Kˣ).toList T 1 t 0 t := by
  rw [← Ary.proc_ofBinary, ← Ary.embed_eval_eq_proc hK, Ary.Tree.eval_ofBinary]

end Cslib.TreeEval
