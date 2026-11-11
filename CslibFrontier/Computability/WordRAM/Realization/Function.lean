/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Function
public import CslibFrontier.Computability.WordRAM.MapOp
public import CslibFrontier.Computability.WordRAM.Realization.Program
public import CslibFrontier.Computability.WordRAM.Realization.Witness

/-!
# Functions computed by realized memory clients

`Realizes.uniformComputableInPolyTime` turns one realization certificate into
`UniformComputableInPolyTime`. The flat program is the certificate's emitted body, preceded by
the charged argument-installation prefix `inputPrefix` and followed by a halt on one result
coordinate; it is chosen before every width and input. The client supplies the input layout and
an entry width and, at every admitted width, the program's domain, its admissible history, its
answer and a polynomial bound on its memory charge plus local work. A basis simulation carries
the exact-basis code to the target basis.

## Main results

* `Realizes.uniformComputableInPolyTime`: uniform polynomial time from a realization.
-/

public section

namespace Cslib.WordRAM.Realization.Realizes

open Cslib.DataStructure

variable {δ α : Type} {k l : ℕ} {p : δ → Memory.Prog α} {input : δ ↪ (Fin k → ℕ)}
  {output : α ↪ (Fin l → ℕ)} {safe : ℕ → δ → Memory.State → Prop}
  {work : δ → Memory.State → ℕ}

/-- **Uniform polynomial time from a realization.** If the first `k` input words encode the
argument, and at every width admitted by `logWidth c` the input fits, the program's domain and
admissible history hold, result coordinate `i` is the function's value, and the memory charge
plus local work is at most `T (size d)` for a polynomially bounded `T`, then one flat program
computes the function in polynomial time. Argument installation and the halt are charged. -/
theorem uniformComputableInPolyTime {B : Basis} (φ : Basis.exact.Simulates B)
    (h : Realizes .exact p input output safe work) (i : Fin l)
    {f : δ → ℕ} {encode : ℕ → δ → List ℕ} {size : δ → ℕ} {T : ℕ → ℕ}
    (hT : PolynomiallyBounded T) (c : ℕ) (hc : 0 < c)
    (hlayout : ∀ w d (j : Fin k), (encode w d).getD j.val 0 = input d j)
    (hspec : ∀ d w, logWidth c (size d) ≤ w → InputFits w (encode w d) →
      k ≤ (encode w d).length ∧ Fits w ((encode w d).length + 1) ∧
        safe w d (inputState (encode w d)) ∧
        (Memory.spec w).ValidHistory (inputState (encode w d))
          ((Memory.spec w).clientHistory (inputState (encode w d)) (p d)) ∧
        output ((Memory.spec w).clientResult (inputState (encode w d)) (p d)) i = f d ∧
        memoryCost (p d) (inputState (encode w d)) + work d (inputState (encode w d)) ≤
          T (size d)) :
    UniformComputableInPolyTime B f encode size := by
  let r := k + (l + h.scratchSize + 1) + 1
  let fr : Fin r := ⟨0, by omega⟩
  let src : Fin k → Fin r := fun j => ⟨j.val + 1, by omega⟩
  let tmp : Fin (l + h.scratchSize + 1) → Fin r := fun j => ⟨k + 1 + j.val, by omega⟩
  have hsrc : Function.Injective src := fun a b hab =>
    Fin.ext (by have := congrArg Fin.val hab; simp only [src] at this; omega)
  have htmp : Function.Injective tmp := fun a b hab =>
    Fin.ext (by have := congrArg Fin.val hab; simp only [tmp] at this; omega)
  have hd : ∀ a b, src a ≠ tmp b := fun a b hab => by
    have := congrArg Fin.val hab; simp only [src, tmp] at this; omega
  have hf : ∀ b, tmp b ≠ fr := fun b hb => by
    have := congrArg Fin.val hb; simp only [tmp, fr] at this; omega
  have hs : ∀ a, src a ≠ fr := fun a ha => by
    have := congrArg Fin.val ha; simp only [src, fr] at this; omega
  refine UniformComputableInPolyTime.of_code
    ((Code.seq (inputPrefix fr (tmp (Fin.last _)) src) (h.code fr src tmp)).mapSimulates φ)
    (tmp (Fin.castAdd (h.scratchSize + 1) i)) (T := fun n => 2 * k + 5 + h.factor * (T n + 1))
    (by fun_prop) c hc fun d w hw hin => ?_
  obtain ⟨hk, hfit, hsafe, hvalid, hout, hcost⟩ := hspec d w hw hin
  obtain ⟨x, ex, hx, hm, hwords, -⟩ := inputPrefix_exec fr (tmp (Fin.last _)) src (encode w d)
    hsrc (hf _) (fun j => hd j _) hs hk hfit hin
  obtain ⟨y, ey, -, hy, -⟩ := (h.code_spec fr src tmp htmp hd hf hs).2 w d x hx
    (funext fun j => (hwords j).trans (hlayout w d j)) (hm ▸ hsafe) (hm ▸ hvalid)
  rw [hm] at ey hy
  exact ⟨y, ((ex.seq ey).mapSimulates φ).mono
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _), (hy i).trans hout⟩

end Cslib.WordRAM.Realization.Realizes
