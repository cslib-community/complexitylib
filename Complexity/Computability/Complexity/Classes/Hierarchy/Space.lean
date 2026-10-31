/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Constructible
public import Complexity.Computability.Complexity.Classes.Hierarchy
public import Complexity.Computability.Complexity.Classes.Hierarchy.ShortDesc
public import Complexity.Computability.Complexity.Classes.LogSpace
public import Complexity.Computability.Complexity.Classes.Space.Time
public import Complexity.Computability.Machines.Turing.MultiTape.Run
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.SpaceBudget
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain

/-!
# The space hierarchy theorem

`Cslib.Complexity.DSPACE` is defined in `Classes.Space.Basic`, and
`Cslib.Complexity.SpaceConstructible` in `Classes.Constructible`. Their generic APIs and
the concrete `L` and `PSPACE` characterizations do not depend on this hierarchy theorem.

## The space hierarchy theorem

`Cslib.Complexity.spaceDiagonal G` runs the machine described at the start of its input `x`, when
the description is short (`Cslib.Complexity.Diagonal.shortDesc`), on `x` with the universal machine
within a space budget (`Turing.MultiTapeTM.Universal.budgetedUniversal`): for `2 ^ G n` steps, with
the configurations of the simulation encoded within `G n` bits. It negates the verdict, and answers
`false` on other inputs. The budgeted universal machine is the in-place universal run with a budget
test at the end of each pass, within space linear in the description, the budget and the lengths
of the clock and of `n` in binary (`Turing.MultiTapeTM.Universal.budgetSpace_le`). The diagonal
also holds its input, to test shortness and to convert it to symbols, so it takes space
`O(n + G n)` (`Cslib.Complexity.computableInO_spaceDiagonal`) and decides a problem in
`DSPACE G` when `n ≤ G n` (`Cslib.Complexity.setOf_spaceDiagonal_mem_DSPACE`).

Let a machine decide the same problem within space `c₁ * f n + c₂`, where every `c * f n + c` is
eventually below `G n`. It halts within its number of configurations, `(n + 2) * 2 ^ O(f n)`, which
is eventually below the clock. The configurations of its simulation take `O(f n + log n)` bits,
with a factor linear in its description: the overhead of the universal machine is a constant factor
for each simulated machine, eventually within the budget. So on its own description, padded, the
diagonal answers the negation of its answer (`Cslib.Complexity.setOf_spaceDiagonal_notMem_DSPACE`).
Hence the space hierarchy theorem [Stearns, Hartmanis and Lewis][StearnsHartmanisLewis1965],
[Sipser, Theorem 9.3][Sipser2013], [Arora and Barak, Theorem 4.8][AroraBarak09]:

* `DSPACE f ⊂ DSPACE g` for a space-constructible `g` with `n ≤ g n`, when every `c * f n + c` is
  eventually below `g n` (`Cslib.Complexity.DSPACE_ssubset_DSPACE`);
* `DSPACE (n ^ k) ⊂ DSPACE (n ^ (k + 1))` (`Cslib.Complexity.DSPACE_pow_ssubset_DSPACE_pow_succ`);
* `L ⊂ PSPACE` (`Cslib.Complexity.L_ssubset_PSPACE`).

The gap `f = o(g)` is the textbook one. The lower bound `n ≤ g n`, where the textbook asks
`log n ≤ g n`, is the space the diagonal takes to hold its input; hierarchies below linear space
are not claimed here.

## Main definitions

* `Cslib.Complexity.spaceDiagonal`: the diagonal within a space budget.

## Main results

* `Cslib.Complexity.spaceDiagonal_desc`: the diagonal negates the answer of a machine on its padded
  description, within the clock and the budget.
* `Cslib.Complexity.setOf_spaceDiagonal_mem_DSPACE`,
  `Cslib.Complexity.setOf_spaceDiagonal_notMem_DSPACE`: the diagonal within space `G` is decidable
  within space `O(G)`, and not within space `O(f)` for `f = o(G)`.
* `Cslib.Complexity.DSPACE_ssubset_DSPACE`: the space hierarchy theorem.
* `Cslib.Complexity.DSPACE_pow_ssubset_DSPACE_pow_succ`, `Cslib.Complexity.L_ssubset_PSPACE`: its
  corollaries.

## References

* [R. E. Stearns, J. Hartmanis, P. M. Lewis II, *Hierarchies of memory limited
  computations*][StearnsHartmanisLewis1965]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]

The padded diagonal argument follows the time hierarchy theorem
(`Complexity.Computability.Complexity.Classes.Hierarchy.Time`), here on Christian Reitwiessner's
in-place universal interpreter within a space budget.
-/

@[expose] public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal Filter

/-! ### The diagonal within a space budget -/

/-- **The diagonal within space `G`.** On a word `x` of length `n` whose framed description is
short (`Cslib.Complexity.Diagonal.shortDesc`), run the described machine on `x`, under the coding
`Turing.MultiTapeTM.Universal.eBit` of bits, for `2 ^ G n` steps within the budget of `G n` bits
for the encoded configurations of the simulation (`Turing.MultiTapeTM.Universal.budgetedUniversal`),
and return `false` exactly when it has halted with output `[true]`; answer `false` on other
words. -/
def spaceDiagonal (G : ℕ → ℕ) (x : List Bool) : Bool :=
  if Diagonal.shortDesc x then
    Diagonal.verdict (budgetedUniversal (decodeDesc (unframe x), x.map eBit, 2 ^ G x.length,
      G x.length))
  else false

private theorem exists_computableInO_of_space {β : Type} {encOut : β ↪ List Bool}
    {f : List Bool → β} {T S S' : List Bool → ℕ} (h : ComputableInO f encBits encOut T S)
    (k : ℕ) (hS : ∀ x, S x ≤ k * (S' x + 1)) :
    ∃ T', ComputableInO f encBits encOut T' S' :=
  ⟨T, h.mono (k + 1) (fun x => (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ (by omega)))
    fun x => (hS x).trans (Nat.mul_le_mul_right _ (Nat.le_succ _))⟩

open Diagonal in
/-- **The diagonal within space `G` is computable within space `O(n + G n)`**, for a
space-constructible `G`, charging the shortness test, decoding, the symbols of the input, the
budget `G n` in unary, the clock `2 ^ G n` in binary, the budgeted universal run and the test. The
description is short, so decoding it takes space `O(n)`, and the budgeted universal run takes
space linear in the description, the budget and the lengths of the clock and of `n` in binary
(`Turing.MultiTapeTM.Universal.budgetSpace_le`). -/
theorem computableInO_spaceDiagonal {G : ℕ → ℕ} (hG : SpaceConstructible G) :
    ∃ T, ComputableInO (spaceDiagonal G) encBits encBool T
      fun x => x.length + G x.length := by
  obtain ⟨dd, ed, hdec⟩ := exists_computableInDegree_decodeDesc
  have hu : ComputableInO unframe encBits encBits (fun x => x.length) fun x => x.length :=
    ComputableInO.of_linear (.of_unframe fun _ => rfl)
  have hdesc := hdec.inO.comp hu
  have hsym := Universal.computableTidilyInDegree_map_eBit.inO_one.computableInO
  obtain ⟨TG, hGb⟩ := hG.computableInO
  have hGu := ComputableInO.natToUnary.comp hGb
  have hclock := ((ComputableInDegree.two_pow_length encUnary).inO_one.comp_linear
    hGu).of_enc_eq (encC := encNat) (g := fun x : List Bool => 2 ^ G x.length) fun x => by
      simp only [Function.comp_apply, encUnary_apply, List.length_replicate]
  have hU := computableTidilyInO_budgetedUniversal.computableInO.comp
    (hdesc.prod (hsym.prod (hclock.prod hGu)))
  have h := computableInO_shortDesc.ite (computableInO_verdict.comp hU)
    (ComputableInO.const (encMid := encBool) false)
  obtain ⟨cD, -, hcD⟩ := hdesc
  obtain ⟨cA, hcA⟩ := PolynomiallyBounded.exists_le_mul_two_pow (p := fun u => (u + 1) ^ dd)
    (by fun_prop)
  refine exists_computableInO_of_space h (300 * (cD + 1) * (cA + 1) + 300)
    fun x => ?_
  dsimp only [Function.comp_apply, encBits_apply]
  have hK : ∀ m, 2 * m ≤ (300 * (cD + 1) * (cA + 1) + 300) * m := fun m =>
    Nat.mul_le_mul_right _ (by omega)
  split_ifs with hs
  · have hA : ((unframe x).length + 1) ^ dd ≤ cA * x.length :=
      (hcA _).trans (Nat.mul_le_mul_left _ (of_decide_eq_true hs))
    have hD := hcD x
    have hB := budgetSpace_le (decodeDesc (unframe x)) (x.map eBit) (G x.length) (2 ^ G x.length)
    have hO := length_eOut_budgetedUniversal_le (decodeDesc (unframe x)) (x.map eBit) (G x.length)
      (2 ^ G x.length)
    have hclk : (encNat (2 ^ G x.length)).length = G x.length + 1 := by
      rw [encNat_two_pow, List.length_append, List.length_replicate, List.length_singleton]
    have hlen : (encNat ((x.map eBit).length + 1)).length ≤ x.length + 1 := by
      rw [List.length_map]; exact Universal.length_encNat_le _
    have hmax : (x.map eBit).foldr max 0 ≤ 1 := listMax_le fun b _ => by cases b <;> decide
    simp only [descLen, Function.comp_apply, encBits_apply] at hB hD
    have e₁ : cD * (x.length + ((unframe x).length + 1) ^ dd + 1) ≤
        cD * (x.length + cA * x.length + 1) := Nat.mul_le_mul_left _ (by omega)
    have e₂ : cD * (x.length + cA * x.length + 1) + cA * x.length ≤
        (cD + 1) * (cA + 1) * (x.length + G x.length + 1) := by
      have : (cD + 1) * (cA + 1) * (x.length + G x.length + 1) =
          cD * (x.length + cA * x.length + 1) + cA * x.length + (cD * cA * G x.length + cD * cA +
            cD * G x.length + cA * G x.length + cA + x.length + G x.length + 1) := by ring
      omega
    have e₃ : (300 * (cD + 1) * (cA + 1) + 300) * (x.length + G x.length + 1) =
        300 * ((cD + 1) * (cA + 1) * (x.length + G x.length + 1)) +
          300 * (x.length + G x.length + 1) := by ring
    omega
  · have := hK (x.length + G x.length + 1)
    omega

/-- **The diagonal within space `G` decides a problem in `DSPACE G`**, for a space-constructible
`G` with `n ≤ G n`. -/
theorem setOf_spaceDiagonal_mem_DSPACE {G : ℕ → ℕ} (hG : SpaceConstructible G)
    (hn : ∀ n, n ≤ G n) : {x | spaceDiagonal G x = true} ∈ DSPACE encBits G := by
  obtain ⟨T, c, hc, -⟩ := computableInO_spaceDiagonal hG
  refine mem_DSPACE_iff.mpr ⟨2 * c, 2 * c, _, decidableInTimeAndSpace_iff.mpr
    ⟨spaceDiagonal G, hc.mono (fun _ => le_rfl) fun x => ?_,
      fun x => Iff.rfl⟩⟩
  have := hn x.length
  simp only [encBits_apply]
  nlinarith

open Diagonal in
/-- On a short padded description, the diagonal within space `G` negates the answer of a machine
that halts within the clock `2 ^ G n` and whose simulated configurations fit within the budget
`G n`. -/
theorem spaceDiagonal_desc {k : ℕ} {State : Type} [Fintype State] (eS : State ↪ ℕ)
    (tm : MultiTapeTM k Bool State) (pad : List Bool) (G : ℕ → ℕ) {b : Bool}
    (hshort : shortDesc (frame (eDesc (desc eS eBit tm)) ++ pad) = true)
    (hbudget : cfgSpace (desc eS eBit tm) ((frame (eDesc (desc eS eBit tm)) ++ pad).map eBit)
      (2 ^ G (frame (eDesc (desc eS eBit tm)) ++ pad).length) ≤
      G (frame (eDesc (desc eS eBit tm)) ++ pad).length)
    (hhalt : (tm.runFrom (tm.initCfg (frame (eDesc (desc eS eBit tm)) ++ pad))
      (2 ^ G (frame (eDesc (desc eS eBit tm)) ++ pad).length)).Halted)
    (hout : (tm.runFrom (tm.initCfg (frame (eDesc (desc eS eBit tm)) ++ pad))
      (2 ^ G (frame (eDesc (desc eS eBit tm)) ++ pad).length)).output = [b]) :
    spaceDiagonal G (frame (eDesc (desc eS eBit tm)) ++ pad) = !b := by
  simp only [spaceDiagonal, hshort, ↓reduceIte]
  rw [decodeDesc_unframe_frame_append, budgetedUniversal_desc eS eBit tm _ _ _ hbudget]
  simp only [Cfg.Halted] at hhalt
  rw [hhalt, hout]
  cases b <;> rfl

/-- Eventually, `n + 1` has at most `n / 4` binary digits. -/
private theorem eventually_four_mul_length_encNat_le :
    ∀ᶠ n in atTop, 4 * (encNat (n + 1)).length ≤ n := by
  obtain ⟨C, hC⟩ := exists_pow_length_encNat_le 2
  filter_upwards [eventually_ge_atTop (100 * (C + 1))] with n hn
  have h₁ := hC (n + 1)
  by_contra hlt
  have h₂ : (n + 1) ^ 2 ≤ 16 * ((encNat (n + 1)).length + 1) ^ 2 := by
    rw [show 16 * ((encNat (n + 1)).length + 1) ^ 2 = (4 * ((encNat (n + 1)).length + 1)) ^ 2 by
      ring]
    exact Nat.pow_le_pow_left (by omega) 2
  have h₃ : 100 * (C + 1) * (n + 1) ≤ (n + 1) ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul_right _ (by omega)
  nlinarith

open Diagonal in
/-- **The diagonal argument for space.** If every `c * f n + c` is eventually below `G n` and
`n ≤ G n`, the problem of the diagonal within space `G` is not in `DSPACE f`. A decider within
space `O(f)` halts within its number of configurations, `2 ^ O(f n)` times a polynomial, which is
eventually below the clock `2 ^ G n`, and the configurations of its simulation take
`O(f n + log n)` bits, eventually within the budget `G n`; so on its own description, padded to a
short one beyond these points, the diagonal answers the negation of its answer. -/
theorem setOf_spaceDiagonal_notMem_DSPACE {f G : ℕ → ℕ} (hn : ∀ n, n ≤ G n)
    (hfG : ∀ c, ∀ᶠ n in atTop, c * f n + c ≤ G n) :
    {x | spaceDiagonal G x = true} ∉ DSPACE encBits f := by
  rintro ⟨c₁, c₂, t, hA⟩
  obtain ⟨g, ⟨k, State, hfinite, tm, htm⟩, hg⟩ := decidableInTimeAndSpace_iff.mp hA
  have := Fintype.ofFinite State
  let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  set D := descLen (desc eS eBit tm) with hD
  set P := 6 * (2 * D + 5) * (c₁ + c₂) + 3 * D + 4 with hP
  set e := storageBoundExp Bool k
  set base := storageBoundBase Bool State k
  have hpoly : ∀ᶠ n in atTop, ((n + 2) * base) ^ 2 < 2 ^ n :=
    PolynomiallyBounded.eventually_lt_two_pow (f := fun n => ((n + 2) * base) ^ 2) (by fun_prop)
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((((hfG (2 * e * (c₁ + c₂))).and (hfG (2 * P))).and
    hpoly).and eventually_four_mul_length_encNat_le)
  -- the description, padded beyond `N` and to a length where it is short
  suffices ∀ pad : List Bool, N + 2 ^ (eDesc (desc eS eBit tm)).length ≤ pad.length → False from
    this (List.replicate _ false) (List.length_replicate ..).ge
  intro pad hpad
  have hpow := Nat.one_le_two_pow (n := (eDesc (desc eS eBit tm)).length)
  have hlen : (frame (eDesc (desc eS eBit tm)) ++ pad).length =
      2 * (eDesc (desc eS eBit tm)).length + 1 + pad.length := by
    rw [List.length_append, length_frame]
  have hshort : shortDesc (frame (eDesc (desc eS eBit tm)) ++ pad) = true := by
    rw [shortDesc, unframe_frame_append, hlen]
    exact decide_eq_true (by omega)
  generalize hx : frame (eDesc (desc eS eBit tm)) ++ pad = x at hlen hshort
  obtain ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩ := hN x.length (by omega)
  have hrun := htm x
  simp only [encBits_apply] at hrun
  set s := c₁ * f x.length + c₂ with hs
  have hsf : s ≤ (c₁ + c₂) * (f x.length + 1) := by rw [hs]; nlinarith
  -- the decider halts within the clock
  have hclock : (x.length + 2) * storageBound Bool State k s ≤ 2 ^ G x.length := by
    have he : 2 * (e * s) ≤ G x.length := by
      have := Nat.mul_le_mul_left (2 * e) hsf
      have e₁ : 2 * e * ((c₁ + c₂) * (f x.length + 1)) =
          2 * e * (c₁ + c₂) * f x.length + 2 * e * (c₁ + c₂) := by ring
      have e₂ : 2 * (e * s) = 2 * e * s := by ring
      omega
    have hsq : ((x.length + 2) * base * 2 ^ (e * s)) ^ 2 ≤ (2 ^ G x.length) ^ 2 := by
      calc ((x.length + 2) * base * 2 ^ (e * s)) ^ 2
          = ((x.length + 2) * base) ^ 2 * 2 ^ (2 * (e * s)) := by ring
        _ ≤ 2 ^ x.length * 2 ^ G x.length :=
          Nat.mul_le_mul h₃.le (Nat.pow_le_pow_right (by norm_num) he)
        _ ≤ 2 ^ G x.length * 2 ^ G x.length :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (hn _))
        _ = (2 ^ G x.length) ^ 2 := (sq _).symm
    refine le_trans ?_ ((Nat.pow_le_pow_iff_left two_ne_zero).mp hsq)
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (storageBound_le_base_mul_pow s)
  obtain ⟨hhalt, hout⟩ := hrun.of_card.runFrom_of_le hclock
  -- the configurations of the simulation fit within the budget
  have hbudget : cfgSpace (desc eS eBit tm) (x.map eBit) (2 ^ G x.length) ≤ G x.length := by
    have hsp : simSpace (desc eS eBit tm) (x.map eBit) (2 ^ G x.length) ≤ s := by
      rw [simSpace_desc]
      exact space_le_of_runsInSpace hrun.2.2 _
    have hk : (desc eS eBit tm).tapes ≤ D := by
      simp only [hD, descLen, eDesc_apply, length_encPair, encUnary_apply, List.length_replicate]
      omega
    have hP' : 6 * (2 * D + 5) * s + 3 * D + 4 ≤ P * (f x.length + 1) := by
      have := Nat.mul_le_mul_left (6 * (2 * D + 5)) hsf
      have e₁ : P * (f x.length + 1) = 6 * (2 * D + 5) * ((c₁ + c₂) * (f x.length + 1)) +
          (3 * D + 4) * (f x.length + 1) := by rw [hP]; ring
      have : 3 * D + 4 ≤ (3 * D + 4) * (f x.length + 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
    have e₂ : 2 * P * f x.length + 2 * P = 2 * (P * (f x.length + 1)) := by ring
    simp only [cfgSpace, List.length_map, ← hD]
    have e₃ : 3 * (2 * D + 5) * 2 * simSpace (desc eS eBit tm) (x.map eBit) (2 ^ G x.length) ≤
        6 * (2 * D + 5) * s := by
      rw [show 3 * (2 * D + 5) * 2 = 6 * (2 * D + 5) by ring]
      exact Nat.mul_le_mul_left _ hsp
    have := hn x.length
    omega
  -- so the diagonal negates the answer of the decider
  have hd : spaceDiagonal G x = !g x := by
    subst hx
    exact spaceDiagonal_desc eS tm pad G hshort hbudget hhalt hout
  have hgx := hg x
  simp only [Set.mem_ofPred_eq, hd] at hgx
  revert hgx
  cases g x <;> decide

/-! ### The space hierarchy theorem -/

/-- **The space hierarchy theorem.** If `g` is space-constructible, `n ≤ g n`, and every
`c * f n + c` is eventually below `g n`, then `DSPACE f` is strictly contained in `DSPACE g`
[Sipser, Theorem 9.3 and Corollary 9.4][Sipser2013], [Arora and Barak, Theorem 4.8][AroraBarak09].
The universal machine simulates within a budget with a constant overhead for each simulated
machine, so the gap is the textbook `f = o(g)`; the condition `n ≤ g n`, where the textbook asks
`log n ≤ g n`, is the space the diagonal takes to hold its input and decode its description. -/
theorem DSPACE_ssubset_DSPACE {f g : ℕ → ℕ} (hg : SpaceConstructible g) (hn : ∀ n, n ≤ g n)
    (hfg : ∀ c, ∀ᶠ n in atTop, c * f n + c ≤ g n) : DSPACE encBits f ⊂ DSPACE encBits g := by
  have hsub : DSPACE encBits f ⊆ DSPACE encBits g := DSPACE_mono_of_eventually_le <| by
    filter_upwards [hfg 1] with n h
    omega
  exact (Set.ssubset_iff_of_subset hsub).mpr ⟨_, setOf_spaceDiagonal_mem_DSPACE hg hn,
    setOf_spaceDiagonal_notMem_DSPACE hn hfg⟩

/-- **Logarithmic space is strictly within polynomial space**: `L ⊆ DSPACE n`, and the diagonal
within space `(n + 1) ^ 2` is in `PSPACE` but not in `DSPACE n`. This is the deterministic part of
[Sipser, Corollary 9.6][Sipser2013], which separates `NL` from `PSPACE`. -/
theorem L_ssubset_PSPACE : L encBits ⊂ PSPACE encBits := by
  have hL : L encBits ⊆ DSPACE encBits fun n => n := fun A hA =>
    DSPACE_mono (fun n => (Nat.log2_le_self n)) (mem_L_iff_mem_DSPACE.mp hA)
  refine (Set.ssubset_iff_of_subset L_subset_PSPACE).mpr ⟨_, DSPACE_subset_PSPACE (by fun_prop)
    (setOf_spaceDiagonal_mem_DSPACE (spaceConstructible_succ_pow 2)
      fun n => (Nat.le_succ n).trans (Nat.le_self_pow two_ne_zero _)), fun h =>
    setOf_spaceDiagonal_notMem_DSPACE (f := fun n => n)
      (fun n => (Nat.le_succ n).trans (Nat.le_self_pow two_ne_zero _)) (fun c => ?_) (hL h)⟩
  filter_upwards [eventually_ge_atTop c] with n hc
  nlinarith

/-- **Polynomial space has a strict hierarchy**: `DSPACE (n ^ k) ⊂ DSPACE (n ^ (k + 1))`
[Sipser, Corollary 9.5][Sipser2013]. The diagonal within space `(n + 1) ^ (k + 1)` separates
them. -/
theorem DSPACE_pow_ssubset_DSPACE_pow_succ (k : ℕ) :
    DSPACE encBits (· ^ k) ⊂ DSPACE encBits (· ^ (k + 1)) := by
  have hn (n : ℕ) : n ≤ (n + 1) ^ (k + 1) :=
    (Nat.le_succ n).trans (Nat.le_self_pow (by omega) _)
  have hsub : DSPACE encBits (· ^ k) ⊆ DSPACE encBits (· ^ (k + 1)) :=
    DSPACE_subset_of_le_mul_add 1 1 fun n => by
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · rcases Nat.eq_zero_or_pos k with rfl | hk <;> simp_all
      · have : n ^ k ≤ n ^ (k + 1) := Nat.pow_le_pow_right hpos (Nat.le_succ k)
        omega
  refine (Set.ssubset_iff_of_subset hsub).mpr ⟨_, DSPACE_subset_of_le_mul_add (2 ^ (k + 1)) 1
    (fun n => by simpa using Nat.mul_add_one_pow_le_two_pow 1 (k + 1) n)
    (setOf_spaceDiagonal_mem_DSPACE (spaceConstructible_succ_pow (k + 1)) hn),
    setOf_spaceDiagonal_notMem_DSPACE hn fun c => ?_⟩
  filter_upwards [eventually_ge_atTop (2 * c)] with n hc
  have h₁ : n ^ k ≤ (n + 1) ^ k := Nat.pow_le_pow_left (Nat.le_succ n) k
  have h₂ : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (by omega)
  have e : (n + 1) ^ (k + 1) = (n + 1) ^ k * (n + 1) := pow_succ ..
  nlinarith

end Cslib.Complexity
