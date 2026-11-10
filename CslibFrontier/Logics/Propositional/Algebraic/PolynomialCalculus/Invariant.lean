/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.Algebraic.PolynomialCalculus.Proof
public import Mathlib.Algebra.Module.Submodule.Defs

/-!
# Monotonicity and invariants of polynomial calculus proofs

Two structural facts about polynomial calculus proofs (`Cslib.Logic.PL.PC.IsProof`).

* Proofs and refutations are monotone in the input list
  (`Cslib.Logic.PL.PC.IsProof.mono`, `Cslib.Logic.PL.PC.RefutableInDegree.mono`).
* **The invariant method for degree lower bounds**
  (`Cslib.Logic.PL.PC.IsProof.mem_of_degree_le`). Suppose an `R`-submodule `M` of polynomials
  contains every input and contains `X v * p` whenever `p ∈ M` and `X v * p` has degree at most
  `d`. Then every line of a proof of degree at most `d` lies in `M`. A degree lower bound follows
  when `1 ∉ M`. This is the shape of the argument of Theorem 5.1 of
  [ImpagliazzoPudlakSgall1999], used in `CslibFrontier.Logics.Propositional.Algebraic.SubsetSum`.

## Main results

* `Cslib.Logic.PL.PC.IsProof.mono`, `Cslib.Logic.PL.PC.RefutableInDegree.mono`: monotonicity in
  the inputs.
* `Cslib.Logic.PL.PC.IsProof.mem_of_degree_le`: the invariant method.

## References

* [R. Impagliazzo, P. Pudlák, J. Sgall, *Lower bounds for the polynomial calculus and the Gröbner
  basis algorithm*][ImpagliazzoPudlakSgall1999]
-/

public section

namespace Cslib.Logic.PL.PC

open MvPolynomial

variable {V R : Type*} [CommSemiring R]

/-- A proof from `F` is a proof from every list containing `F`. -/
theorem IsProof.mono {F G ls : List (MvPolynomial V R)} (h : IsProof F ls) (hFG : F ⊆ G) :
    IsProof G ls := by
  induction h with
  | nil => exact .nil
  | mem _ hp ih => exact ih.mem (hFG hp)
  | linear a b _ hp hq ih => exact ih.linear a b hp hq
  | mulVar v _ hp ih => exact ih.mulVar v hp

/-- Polynomial calculus refutability in degree `d` is monotone in the input list and in `d`. -/
theorem RefutableInDegree.mono {F G : List (MvPolynomial V R)} {d e : ℕ}
    (h : RefutableInDegree F d) (hFG : F ⊆ G) (hde : d ≤ e) : RefutableInDegree G e :=
  let ⟨ls, hls, h1, hd⟩ := h
  ⟨ls, hls.mono hFG, h1, hd.trans hde⟩

/-- **The invariant method.** Let `M` be a submodule containing every input and containing
`X v * p` whenever `p ∈ M` and `X v * p` has total degree at most `d`. Then every line of a
proof of degree at most `d` lies in `M`. -/
theorem IsProof.mem_of_degree_le {F ls : List (MvPolynomial V R)} (h : IsProof F ls) {d : ℕ}
    (hd : degree ls ≤ d) (M : Submodule R (MvPolynomial V R)) (hF : ∀ f ∈ F, f ∈ M)
    (hX : ∀ v, ∀ p ∈ M, (X v * p).totalDegree ≤ d → X v * p ∈ M) : ∀ p ∈ ls, p ∈ M := by
  induction h with
  | nil => simp
  | mem _ hp ih =>
    rw [degree_cons, max_le_iff] at hd
    exact List.forall_mem_cons.mpr ⟨hF _ hp, ih hd.2⟩
  | linear a b _ hp hq ih =>
    rw [degree_cons, max_le_iff] at hd
    have hM := ih hd.2
    refine List.forall_mem_cons.mpr ⟨?_, hM⟩
    rw [C_mul', C_mul']
    exact M.add_mem (M.smul_mem a (hM _ hp)) (M.smul_mem b (hM _ hq))
  | mulVar v _ hp ih =>
    rw [degree_cons, max_le_iff] at hd
    have hM := ih hd.2
    exact List.forall_mem_cons.mpr ⟨hX v _ (hM _ hp) hd.1, hM⟩

end Cslib.Logic.PL.PC
