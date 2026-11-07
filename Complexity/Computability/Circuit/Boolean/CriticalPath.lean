/-
Copyright (c) 2026 Jonathan Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Katz
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.SemiCircuit.Gate
public import Complexity.Computability.Circuit.Complexity
public import Complexity.Computability.Circuit.CriticalPath
public import Cslib.Computability.Circuit.Full
import Complexity.Computability.Circuit.InnerSize

/-!
# Critical-path bottlenecks over the full binary Boolean basis `B₂`

Boolean specialization of `Complexity.Computability.Circuit.CriticalPath` to the complete binary
Boolean basis `B₂` (`Cslib.Circuits.fullInterpretation (k := 2) (Carrier := Bool)`), following
Sections 4.1.1 and 7.1 of Fan, Li, and Yang [FanLiYang2022].

Every binary Boolean operation is either affine (`SemiCircuit.IsAffineOp`) or non-affine
(`IsAndType`, `GF(2)` degree `2`). Composing a binary gate `opG` with unary Boolean functions on its
inputs and output preserves affineness and cannot turn a non-affine gate into a balanced affine XOR
gate (`IsXorType`). Consequently, if two distinct input coordinates `x ≠ y` of a single-output `B₂`
circuit with `NoDeadGates` have intersecting critical paths, either no `2`-bit restriction to
`(x, y)` is AND-type or no `2`-bit restriction to `(x, y)` is XOR-type
(`not_isAndType_or_not_isXorType_of_not_disjoint_criticalPath`). Combined with Lemma 7.4
(`Circuit.two_mul_sub_two_mul_le_size`), every `n`-bit Boolean function (`2 ≤ n`) of `B₂`
complexity strictly below `2 * n - 2` exhibits such a restricted-subfunction obstruction on some
coordinate pair `x < y` (`exists_lt_pair_not_isAndType_or_not_isXorType`).

## Main definitions

* `Cslib.Circuits.Boolean.IsAndType`, `Cslib.Circuits.Boolean.IsXorType`: non-affine (`GF(2)`
  degree `2`) and balanced two-variable affine operations in `B₂` ([FanLiYang2022], §4.1.1).

## Main results

* `Cslib.Circuits.Boolean.not_isAndType_comp_of_isAffineOp`,
  `Cslib.Circuits.Boolean.not_isXorType_comp_of_not_isAffineOp`: unary pre- and post-processing
  cannot turn an affine binary gate into an AND-type function or a non-affine gate into an XOR-type
  function.
* `Cslib.Circuits.Boolean.not_isAndType_or_not_isXorType_of_not_disjoint_criticalPath`: intersecting
  critical paths in a single-output `B₂` circuit with `NoDeadGates` exclude either all AND-type or
  all XOR-type `2`-bit restrictions ([FanLiYang2022], Lemma 7.2).
* `Cslib.Circuits.Boolean.exists_lt_pair_not_isAndType_or_not_isXorType`: every `n`-bit Boolean
  function (`2 ≤ n`) of `B₂`-complexity strictly below `2 * n - 2` has `x < y` in `Fin n` whose
  `2`-bit restrictions are either never AND-type or never XOR-type.

## References

* [Z. Fan, J. Li, and T. Yang, *The Exact Complexity of Pseudorandom Functions and the Black-Box
  Natural Proof Barrier for Bootstrapping Results in Computational Complexity*][FanLiYang2022],
  Sections 4.1.1 and 7.1.
-/

public section

namespace Cslib.Circuits.Boolean

open Cslib.Circuits

/-- A binary Boolean operation is *AND-type* when it is non-affine (`GF(2)` degree `2`), i.e., one
of the `8` operations `(a ⊕ α) ∧ (b ⊕ β) ⊕ γ` ([FanLiYang2022], §4.1.1). -/
@[expose] def IsAndType (h : Bool → Bool → Bool) : Prop :=
  ¬ SemiCircuit.IsAffineOp h

instance (h : Bool → Bool → Bool) : Decidable (IsAndType h) :=
  inferInstanceAs (Decidable (¬ _))

/-- A binary Boolean operation is *XOR-type* when it is affine and depends on both arguments, i.e.,
`a ⊕ b` or `¬(a ⊕ b)` ([FanLiYang2022], §4.1.1). -/
@[expose] def IsXorType (h : Bool → Bool → Bool) : Prop :=
  SemiCircuit.IsAffineOp h ∧ h false false ≠ h true false ∧ h false false ≠ h false true

instance (h : Bool → Bool → Bool) : Decidable (IsXorType h) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

private theorem not_isAndType_comp_aux :
    ∀ (u0 u1 v0 v1 w0 w1 g00 g10 g01 g11 : Bool),
      SemiCircuit.IsAffineOp
          (fun u v : Bool => if u then if v then g11 else g10 else if v then g01 else g00) →
        ¬ IsAndType fun a b =>
          if (if (if a then v1 else v0) then
                if (if b then w1 else w0) then g11 else g10
              else
                if (if b then w1 else w0) then g01 else g00) then u1 else u0 := by
  decide

private theorem not_isXorType_comp_aux :
    ∀ (u0 u1 v0 v1 w0 w1 g00 g10 g01 g11 : Bool),
      ¬ SemiCircuit.IsAffineOp
          (fun u v : Bool => if u then if v then g11 else g10 else if v then g01 else g00) →
        ¬ IsXorType fun a b =>
          if (if (if a then v1 else v0) then
                if (if b then w1 else w0) then g11 else g10
              else
                if (if b then w1 else w0) then g01 else g00) then u1 else u0 := by
  decide

/-- Composing an affine binary gate `G` with unary pre- and post-processing never yields an
AND-type binary function. -/
theorem not_isAndType_comp_of_isAffineOp {G : Bool → Bool → Bool}
    (hG : SemiCircuit.IsAffineOp G) (f₁ f₂ f₃ : Bool → Bool) :
    ¬ IsAndType fun a b => f₁ (G (f₂ a) (f₃ b)) := by
  have hG' : SemiCircuit.IsAffineOp
      (fun u v : Bool =>
        if u then if v then G true true else G true false
        else if v then G false true else G false false) := by
    convert hG using 1
    ext u v
    cases u <;> cases v <;> rfl
  convert not_isAndType_comp_aux (f₁ false) (f₁ true) (f₂ false) (f₂ true) (f₃ false) (f₃ true)
    (G false false) (G true false) (G false true) (G true true) hG' using 2
  ext a b
  cases a <;> cases b <;> cases h₂ : f₂ _ <;> cases h₃ : f₃ _ <;> cases hG₂ : G _ _ <;> simp_all

/-- Composing a non-affine (AND-type) binary gate `G` with unary pre- and post-processing never
yields an XOR-type binary function. -/
theorem not_isXorType_comp_of_not_isAffineOp {G : Bool → Bool → Bool}
    (hG : ¬ SemiCircuit.IsAffineOp G) (f₁ f₂ f₃ : Bool → Bool) :
    ¬ IsXorType fun a b => f₁ (G (f₂ a) (f₃ b)) := by
  have hGeq : (fun u v : Bool =>
      if u then if v then G true true else G true false
      else if v then G false true else G false false) = G := by
    ext u v
    cases u <;> cases v <;> rfl
  have hG' : ¬ SemiCircuit.IsAffineOp
      (fun u v : Bool =>
        if u then if v then G true true else G true false
        else if v then G false true else G false false) :=
    hGeq.symm ▸ hG
  convert not_isXorType_comp_aux (f₁ false) (f₁ true) (f₂ false) (f₂ true) (f₃ false) (f₃ true)
    (G false false) (G true false) (G false true) (G true true) hG' using 2
  ext a b
  cases a <;> cases b <;> cases h₂ : f₂ _ <;> cases h₃ : f₃ _ <;> cases hG₂ : G _ _ <;> simp_all

/-- In a single-output `B₂` circuit with `NoDeadGates` and intersecting critical paths at `x ≠ y`,
either no `2`-bit restriction to `(x, y)` is AND-type or no `2`-bit restriction to `(x, y)` is
XOR-type (the structural core of Fan–Li–Yang [FanLiYang2022], Lemma 7.2). -/
theorem not_isAndType_or_not_isXorType_of_not_disjoint_criticalPath {n : ℕ}
    (C : Circuit (fullSignature 2 Bool) n 1) (hnoDead : C.NoDeadGates)
    {x y : Fin n} (hxy : x ≠ y)
    (hinter : ¬ Disjoint (C.criticalPath x).toFinset (C.criticalPath y).toFinset) :
    (∀ ρ : Fin n → Bool,
      ¬ IsAndType fun bx by_ =>
        C.eval fullInterpretation (Function.update (Function.update ρ x bx) y by_) 0) ∨
    (∀ ρ : Fin n → Bool,
      ¬ IsXorType fun bx by_ =>
        C.eval fullInterpretation (Function.update (Function.update ρ x bx) y by_) 0) := by
  obtain ⟨opG, hbot⟩ := C.exists_bottleneck_of_not_disjoint_criticalPath
    fullInterpretation C.fanInAtMost_fullSignature hnoDead hxy hinter
  by_cases hAff : SemiCircuit.IsAffineOp opG
  · left
    intro ρ
    obtain ⟨f₁, f₂, f₃, hf⟩ := hbot ρ
    have hfun : (fun bx by_ =>
        C.eval fullInterpretation (Function.update (Function.update ρ x bx) y by_) 0) =
        fun bx by_ => f₁ (opG (f₂ bx) (f₃ by_)) :=
      funext fun bx => funext fun by_ => hf bx by_
    rw [hfun]
    exact not_isAndType_comp_of_isAffineOp hAff f₁ f₂ f₃
  · right
    intro ρ
    obtain ⟨f₁, f₂, f₃, hf⟩ := hbot ρ
    have hfun : (fun bx by_ =>
        C.eval fullInterpretation (Function.update (Function.update ρ x bx) y by_) 0) =
        fun bx by_ => f₁ (opG (f₂ bx) (f₃ by_)) :=
      funext fun bx => funext fun by_ => hf bx by_
    rw [hfun]
    exact not_isXorType_comp_of_not_isAffineOp hAff f₁ f₂ f₃

/-- Every `n`-bit Boolean function (`2 ≤ n`) of `B₂`-circuit complexity strictly less than
`2 * n - 2` either has an isolated coordinate or has two intersecting critical paths in an
equivalent `NoDeadGates` circuit, and in both cases admits `x < y` in `Fin n` whose `2`-bit
restrictions are either never AND-type or never XOR-type. -/
theorem exists_lt_pair_not_isAndType_or_not_isXorType {n : ℕ} (hn : 2 ≤ n)
    {f : (Fin n → Bool) → Bool}
    (hf : complexity (fullInterpretation (k := 2)) (single f) < 2 * n - 2) :
    ∃ x y : Fin n, x < y ∧
      ((∀ ρ : Fin n → Bool,
          ¬ IsAndType fun bx by_ => f (Function.update (Function.update ρ x bx) y by_)) ∨
       (∀ ρ : Fin n → Bool,
          ¬ IsXorType fun bx by_ => f (Function.update (Function.update ρ x bx) y by_))) := by
  obtain ⟨C₀, hC₀comp, hC₀size⟩ :=
    exists_computes_size_eq_complexity (I := fullInterpretation (k := 2)) (f := single f)
  obtain ⟨C, hCnoDead, hCsize, hCeval, -⟩ := C₀.exists_noDeadGates
  have hfeq : ∀ z : Fin n → Bool, f z = C.eval fullInterpretation z 0 := by
    intro z
    have h1 := Circuit.computes_single_iff.mp hC₀comp z
    have h2 := congrFun (hCeval fullInterpretation z) 0
    exact (h2.trans h1).symm
  have hlt : C.size < 2 * n - 2 := by omega
  by_cases hiso : C.HasIsolatedVar
  · obtain ⟨i, hout, hnotOut⟩ := hiso
    have hindep : ∀ (ρ : Fin n → Bool) (b : Bool), f (Function.update ρ i b) = f ρ := by
      intro ρ b
      rw [hfeq, hfeq, congrFun (C.eval_update_of_outDeg_input_eq_zero fullInterpretation
        hout hnotOut ρ b) 0]
    by_cases hi0 : i.val = 0
    · let y : Fin n := ⟨1, by omega⟩
      have hiy : i < y := by
        change i.val < 1
        omega
      refine ⟨i, y, hiy, Or.inr fun ρ hxor => ?_⟩
      have hxy : i ≠ y := ne_of_lt hiy
      have heq0 : f (Function.update (Function.update ρ i false) y false) =
          f (Function.update (Function.update ρ i true) y false) := by
        rw [Function.update_comm hxy, Function.update_comm hxy, hindep, hindep]
      exact hxor.2.1 heq0
    · let x : Fin n := ⟨0, by omega⟩
      have hxi : x < i := by
        change 0 < i.val
        omega
      refine ⟨x, i, hxi, Or.inr fun ρ hxor => ?_⟩
      have heq0 : f (Function.update (Function.update ρ x false) i false) =
          f (Function.update (Function.update ρ x false) i true) := by
        rw [hindep, hindep]
      exact hxor.2.2 heq0
  · have hnotDisj :
        ¬ Pairwise fun x y => Disjoint (C.criticalPath x).toFinset (C.criticalPath y).toFinset := by
      intro hdisj
      have hge := C.two_mul_sub_two_mul_le_size C.fanInAtMost_fullSignature hCnoDead hiso hdisj
      omega
    unfold Pairwise at hnotDisj
    push Not at hnotDisj
    obtain ⟨x, y, hxy, hinter⟩ := hnotDisj
    rcases lt_or_gt_of_ne hxy with hltXY | hgtXY
    · refine ⟨x, y, hltXY, ?_⟩
      simpa only [← hfeq] using
        not_isAndType_or_not_isXorType_of_not_disjoint_criticalPath C hCnoDead hxy hinter
    · have hinter' : ¬ Disjoint (C.criticalPath y).toFinset (C.criticalPath x).toFinset :=
        fun hd => hinter hd.symm
      refine ⟨y, x, hgtXY, ?_⟩
      simpa only [← hfeq] using
        not_isAndType_or_not_isXorType_of_not_disjoint_criticalPath C hCnoDead hxy.symm hinter'

end Cslib.Circuits.Boolean
