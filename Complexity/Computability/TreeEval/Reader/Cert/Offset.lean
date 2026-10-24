/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Reader.Encode
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Plain

/-!
# Offsets of nodes within linear work space

The offset of the node at a path is a fold over the path from the root: a step adds the length of
a table and, to the right child, the length of the body of the left one. With the lengths computed
by iteration, and the path read off the stack, it is computable within work space linear in
the encoded stack, the height and the value length.

## Main results

* `Cslib.TreeEval.Reader.foldl_pathStep`: the offset as a fold over the path.
* `Cslib.TreeEval.Reader.pathOffset_inSpace`: the offset within linear work space.
-/

@[expose] public section

namespace Cslib.TreeEval

namespace Reader

open Turing MultiTapeTM ComputableTidilyInSpace Iter

private theorem bodyLength_add_tableLength_le (ℓ d : ℕ) :
    bodyLength ℓ d + tableLength ℓ ≤ 2 ^ d * (ℓ + tableLength ℓ) := by
  induction d with
  | zero => simp [bodyLength]
  | succ d ih => rw [bodyLength, pow_succ]; nlinarith

/-! ### Folding over the path -/

/-- A step of the offset along a path from the root, on the height left and the sum. -/
def pathStep (ℓ : ℕ) (s : ℕ × ℕ) (b : Bool) : ℕ × ℕ :=
  if s.1 = 0 then s else (s.1 - 1, s.2 + tableLength ℓ + if b then bodyLength ℓ (s.1 - 1) else 0)

/-- **The offset as a fold over the path**: folding `pathStep ℓ` over `P` from the height `d` and
the sum `acc` gives the height `d - P.length` and the sum `acc + pathOffset ℓ d P`. -/
theorem foldl_pathStep (ℓ : ℕ) (P : List Bool) :
    ∀ d acc, P.foldl (pathStep ℓ) (d, acc) = (d - P.length, acc + pathOffset ℓ d P) := by
  induction P with
  | nil => intro d acc; simp [pathOffset]
  | cons b P ih =>
    intro d acc
    rcases d with _ | d
    · rw [List.foldl_cons, pathStep]
      simp only [↓reduceIte, ih]
      cases P <;> simp [pathOffset]
    · rw [List.foldl_cons, pathStep]
      simp only [show d + 1 ≠ 0 by omega, ↓reduceIte, ih]
      simp only [Nat.add_sub_cancel, pathOffset, List.length_cons, Prod.mk.injEq]
      constructor <;> omega

theorem path_eq_reverse (st : List Frame) : path st = (st.map Frame.dir).reverse := by
  induction st with
  | nil => rfl
  | cons fr st ih => simp [path_cons, ih]

theorem foldl_cons_dir (st : List Frame) (acc : List Bool) :
    st.foldl (fun acc fr => fr.dir :: acc) acc = (st.map Frame.dir).reverse ++ acc := by
  induction st generalizing acc with
  | nil => rfl
  | cons fr st ih => simp [ih]

private theorem pathOffset_le_bodyLength (ℓ : ℕ) (P : List Bool) :
    ∀ d, pathOffset ℓ d P ≤ bodyLength ℓ d := by
  induction P with
  | nil => intro d; simp [pathOffset]
  | cons b P ih =>
    intro d
    rcases d with _ | d
    · simp [pathOffset]
    · simp only [pathOffset, bodyLength]
      have := ih d
      split_ifs <;> omega

/-! ### Certificates -/


private theorem length_encNat_pow_four (k : ℕ) : (encNat (4 ^ k)).length ≤ 2 * k + 1 := by
  have h : 4 ^ k = 2 ^ (2 * k) := by rw [pow_mul]; norm_num
  rw [length_encNat_eq_size]
  refine Nat.size_le.mpr ?_
  rw [h]
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem length_tableLength_le (ℓ : ℕ) : (encNat (tableLength ℓ)).length ≤ 3 * ℓ + 1 := by
  have h₁ := length_encNat_mul_le (4 ^ ℓ) ℓ
  have h₂ := length_encNat_pow_four ℓ
  have h₃ := length_encNat_le_self ℓ
  rw [tableLength]; omega

private theorem iterate_mul_four (k : ℕ) : (fun x => x * 4)^[k] 1 = 4 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, pow_succ]

/-- **The length of a table**, `4^ℓ * ℓ` from `ℓ`. -/
theorem tableLength_inSpace :
    ComputableInSpace tableLength encNat encNat fun ℓ => 4096 * (ℓ + 1) := by
  have this : ComputableTidilyInSpace tableLength encNat encNat fun ℓ => 4096 * (ℓ + 1) := by
    have hl : (fun ℓ => (encNat ℓ).length) ≼ fun ℓ => 1024 * (ℓ + 1) :=
      .of_le fun ℓ => by have := length_encNat_le_self ℓ; omega
    have hid : ComputableTidilyInSpace (fun ℓ : ℕ => ℓ) encNat encNat fun ℓ => 1024 * (ℓ + 1) :=
      (of_inO (.of_linear (.of_eq (f := id) fun _ => rfl))).weaken hl
    have hstep : ComputableTidilyInSpace (fun x : ℕ => x * 4) encNat encNat
        fun x => 64 * ((encNat x).length + 1) :=
      (budget_comp_lin natMul (linear_mul _) (budget_prod
        (of_inO (.of_linear (.of_eq (f := id) fun _ => rfl)))
        (budget_const (encB := encNat) 4 (.refl _)))).weaken (.of_le fun x => by omega)
    have h := iterate (n := fun ℓ : ℕ => ℓ) hid (budget_const (encB := encNat) 1 hl) hstep
      (Q := fun ℓ => 64 * (2 * ℓ + 2)) (B := fun ℓ => 2 * ℓ + 1)
      (fun ℓ k hk => by rw [iterate_mul_four]; have := length_encNat_pow_four k; omega)
      (fun ℓ k hk => by rw [iterate_mul_four]; have := length_encNat_pow_four k; omega)
    have hl' : (fun ℓ => 1024 * (ℓ + 1)) ≼ fun ℓ => 4096 * (ℓ + 1) := .of_le fun _ => by omega
    refine (budget_comp_lin natMul (linear_mul _) (budget_prod (h.mono_le fun ℓ => ?_)
      (hid.weaken hl'))).of_enc_eq fun ℓ => by rw [iterate_mul_four]; rfl
    have := length_encNat_le_self ℓ; omega
  simpa only [computableInSpace_iff_computableTidilyInSpace] using this

private theorem length_encNat_two_pow (k : ℕ) : (encNat (2 ^ k)).length ≤ k + 1 := by
  rw [length_encNat_eq_size]
  exact Nat.size_le.mpr (Nat.pow_lt_pow_right (by norm_num) (by omega))

private theorem length_bodyLength_le (ℓ k : ℕ) :
    (encNat (bodyLength ℓ k)).length ≤ k + 4 * ℓ + 4 := by
  have h₁ := ComputableTidilyInO.length_encNat_mono
    ((Nat.le_add_right _ _).trans (bodyLength_add_tableLength_le ℓ k))
  have h₂ := length_encNat_mul_le (2 ^ k) (ℓ + tableLength ℓ)
  have h₃ := length_encNat_two_pow k
  have h₄ := length_encNat_add_le_add ℓ (tableLength ℓ)
  have h₅ := length_tableLength_le ℓ
  have h₆ := length_encNat_le_self ℓ
  omega

/-- A step of the lengths of bodies, on `(G, b)`. -/
private def bodyStep (q : ℕ × ℕ) : ℕ × ℕ := (q.1, q.1 + 2 * q.2)

private theorem iterate_bodyStep (ℓ k : ℕ) :
    bodyStep^[k] (tableLength ℓ, ℓ) = (tableLength ℓ, bodyLength ℓ k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih]; rfl

/-- **The length of the body of a subtree**, `bodyLength ℓ e` from `(ℓ, e)`. -/
private theorem bodyLength_inSpace :
    ComputableTidilyInSpace (fun q : ℕ × ℕ => bodyLength q.1 q.2) (encPair encNat encNat) encNat
      fun q => 65536 * (q.1 + q.2 + 1) := by
  have hl : (fun q => (encPair encNat encNat q).length) ≼ fun q => 4096 * (q.1 + q.2 + 1) :=
    .of_le fun q => by
      have := length_encNat_le_self q.1
      have := length_encNat_le_self q.2
      simp only [length_encPair]; omega
  have hstep : ComputableTidilyInSpace bodyStep (encPair encNat encNat) (encPair encNat encNat)
      fun q => 64 * ((encPair encNat encNat q).length + 1) := by
    have hl₀ : (fun q => (encPair encNat encNat q).length) ≼
        fun q => 64 * ((encPair encNat encNat q).length + 1) := .of_le fun _ => by omega
    have hG := (fst encNat encNat).weaken hl₀
    have hb := (snd encNat encNat).weaken hl₀
    have h2b := budget_comp_lin natAdd linear_succ (budget_prod hb hb)
    have hsum := budget_comp_lin natAdd linear_succ (budget_prod hG h2b)
    exact (budget_prod hG hsum).of_enc_eq fun q => by simp [bodyStep, two_mul]
  have hG := budget_comp tableLength_inSpace.tidy ((fst encNat encNat).weaken hl)
    (.of_le_linear 1 0 fun q => by omega)
  have hinit := budget_prod hG ((fst encNat encNat).weaken hl)
  have hlen (q : ℕ × ℕ) (k : ℕ) (hk : k ≤ q.2) :
      (encPair encNat encNat (bodyStep^[k] (tableLength q.1, q.1))).length ≤
        16 * (q.1 + q.2 + 1) := by
    rw [iterate_bodyStep, length_encPair]
    have := length_tableLength_le q.1
    have := length_bodyLength_le q.1 k
    dsimp only
    omega
  have h := iterate (n := fun q : ℕ × ℕ => q.2) ((snd encNat encNat).weaken hl) hinit hstep
    (Q := fun q => 64 * (16 * (q.1 + q.2 + 1) + 1)) (B := fun q => 16 * (q.1 + q.2 + 1))
    (fun q k hk => by have := hlen q k hk; omega) hlen
  refine (snd' h).mono_le (fun q => ?_) |>.of_enc_eq fun q => by rw [iterate_bodyStep]
  have := length_encNat_le_self q.2
  omega

/-! ### Frames -/

/-- The encoding of tuples of frames. -/
abbrev encFrameTuple : ℕ × Fin 4 × Bool × Fin 3 ↪ List Bool :=
  encPair encNat (encFinEnum (Fin 4 × Bool × Fin 3))

theorem encFrame_apply (fr : Frame) : encFrame fr = encFrameTuple (Frame.equiv fr) := rfl

/-- **A function of the finite fields of a frame.** -/
theorem frameFinite_inSpace {β : Type} {encB : β ↪ List Bool} (g : Fin 4 × Bool × Fin 3 → β) :
    ComputableInSpace (fun fr : Frame => g (Frame.equiv fr).2) encFrame encB
      fun fr => (encFrame fr).length := by
  have this : ComputableTidilyInSpace (fun fr : Frame => g (Frame.equiv fr).2) encFrame encB
      fun fr => (encFrame fr).length := by
    have h := budget_finite (encC := encB) g (snd encNat (encFinEnum (Fin 4 × Bool × Fin 3)))
    exact h.of_encIn_eq Frame.equiv fun _ => rfl
  simpa only [computableInSpace_iff_computableTidilyInSpace] using this

/-- The round of a frame. -/
theorem round_inSpace :
    ComputableInSpace (fun fr : Frame => fr.round) encFrame encNat
      fun fr => (encFrame fr).length := by
  have this : ComputableTidilyInSpace (fun fr : Frame => fr.round) encFrame encNat fun fr =>
      (encFrame fr).length :=
    (fst encNat (encFinEnum (Fin 4 × Bool × Fin 3))).of_encIn_eq Frame.equiv fun _ => rfl
  simpa only [computableInSpace_iff_computableTidilyInSpace] using this

/-! ### The offset of the node at the path of a stack -/

private theorem three_mul_length_le (st : List Frame) : 3 * st.length ≤
    (encList encFrame st).length := by
  induction st with
  | nil => simp
  | cons fr st ih =>
    have : 1 ≤ (encFrame fr).length := by rw [encFrame_apply, length_encPair]; omega
    rw [length_encList] at ih ⊢
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

private theorem length_encList_bools (l : List Bool) :
    (encList encBool l).length = 3 * l.length := by
  induction l with
  | nil => rfl
  | cons b l ih => rw [length_encList] at ih ⊢; simp; ring

theorem dirs_inSpace :
    ComputableInSpace (fun st : List Frame => st.foldl (fun acc fr => fr.dir :: acc) [])
      (encList encFrame) (encList encBool) fun st => 64 * ((encList encFrame st).length + 1) := by
  have this : ComputableTidilyInSpace
      (fun st : List Frame => st.foldl (fun acc fr => fr.dir :: acc) []) (encList encFrame)
      (encList encBool) fun st => 64 * ((encList encFrame st).length + 1) := by
    have hl : (fun st => (encList encFrame st).length) ≼
        fun st => 8 * ((encList encFrame st).length + 1) := .of_le fun _ => by omega
    have hstep : ComputableTidilyInSpace (fun q : List Bool × Frame => q.2.dir :: q.1)
        (encPair (encList encBool) encFrame) (encList encBool)
        fun q => 2 * ((encPair (encList encBool) encFrame q).length + 1) := by
      have hl₀ : (fun q => (encPair (encList encBool) encFrame q).length) ≼
          fun q => 2 * ((encPair (encList encBool) encFrame q).length + 1) := .of_le fun _ => by
            omega
      have hd := budget_comp (frameFinite_inSpace (encB := encBool)
        fun y : Fin 4 × Bool × Fin 3 => y.1.val % 2 == 1).tidy
        ((snd (encList encBool) encFrame).weaken hl₀) (.of_le fun x => by
          simp only [length_encPair]; omega)
      have hc : ComputableTidilyInSpace (fun p : Bool × List Bool => p.1 :: p.2)
          (encPair encBool (encList encBool)) (encList encBool)
          fun p => (encPair encBool (encList encBool) p).length :=
        of_inO (ComputableTidilyInDegree.cons encBool).inO_one
      exact (budget_comp_linear hc (budget_prod hd ((fst (encList encBool) encFrame).weaken hl₀)))
        |>.of_enc_eq fun q => rfl
    have hlen (st : List Frame) (i : ℕ) :
        (encList encBool ((st.take i).foldl (fun acc fr => fr.dir :: acc) [])).length ≤
          (encList encFrame st).length := by
      rw [foldl_cons_dir, List.append_nil, length_encList_reverse, length_encList_bools,
        List.length_map]
      exact (Nat.mul_le_mul_left 3 (List.length_take_le' i st)).trans (three_mul_length_le st)
    have h := foldl (encL := encList encFrame) (list := fun st : List Frame => st)
      (init := fun _ => ([] : List Bool)) (step := fun acc fr => fr.dir :: acc)
      (of_inO (.of_linear (.of_eq (f := id) fun _ => rfl))) (budget_const [] (.refl _)) hstep
      (Q := fun st => 2 * (3 * (encList encFrame st).length + 2))
      (B := fun st => (encList encFrame st).length)
      (fun st i hi => by
        have h₁ := hlen st i
        have h₂ := length_le_encList_of_mem encFrame (List.getElem_mem hi)
        rw [length_encPair]; dsimp only; omega)
      (fun st i _ => hlen st i)
    exact h.mono_le fun st => by omega
  simpa only [computableInSpace_iff_computableTidilyInSpace] using this

/-- A step of the offset along a path, with the value length in the state. -/
private def pathStep' (q : ℕ × ℕ × ℕ) (b : Bool) : ℕ × ℕ × ℕ := (q.1, pathStep q.1 q.2 b)

private theorem foldl_pathStep' (ℓ : ℕ) (P : List Bool) (s : ℕ × ℕ) :
    P.foldl pathStep' (ℓ, s) = (ℓ, P.foldl (pathStep ℓ) s) := by
  induction P generalizing s with
  | nil => rfl
  | cons b P ih => rw [List.foldl_cons, List.foldl_cons, pathStep', ih]

private theorem pathStep'_inSpace :
    ComputableTidilyInSpace (fun q : (ℕ × ℕ × ℕ) × Bool => pathStep' q.1 q.2)
      (encPair encNat3 encBool) encNat3
      fun q => 2 ^ 20 * (q.1.1 + q.1.2.1 + (encPair encNat3 encBool q).length + 1) := by
  have hl : (fun q => (encPair encNat3 encBool q).length) ≼
      fun q => 2 ^ 20 * (q.1.1 + q.1.2.1 + (encPair encNat3 encBool q).length + 1) :=
    .of_le fun _ => by omega
  have hs := (fst encNat3 encBool).weaken hl
  have hb := (snd encNat3 encBool).weaken hl
  have hℓ := fst' hs
  have hd := fst' (snd' hs)
  have hacc := snd' (snd' hs)
  have hz := budget_comp_linear natIsZero hd
  have hd₁ := budget_comp_lin natPred linear_succ hd
  have hG := budget_comp tableLength_inSpace.tidy hℓ (.of_le_linear 1 0 fun q => by omega)
  have hB := budget_comp bodyLength_inSpace (budget_prod hℓ hd₁) (.of_le_linear 1 0 fun q => by
    dsimp only; omega)
  have hBif := budget_ite hb hB (budget_const (encB := encNat) 0 hl)
  have hsum₁ := budget_comp_lin natAdd linear_succ (budget_prod hacc hG)
  have hsum := budget_comp_lin natAdd linear_succ (budget_prod hsum₁ hBif)
  refine (budget_ite hz hs (budget_prod hℓ (budget_prod hd₁ hsum))).of_enc_eq fun q => ?_
  simp only [pathStep', pathStep]
  by_cases h : q.1.2.1 = 0 <;> simp [h]

private theorem length_pathOffset_le (ℓ d : ℕ) (P : List Bool) :
    (encNat (pathOffset ℓ d P)).length ≤ d + 4 * ℓ + 4 :=
  (ComputableTidilyInO.length_encNat_mono (pathOffset_le_bodyLength ℓ P d)).trans
    (length_bodyLength_le ℓ d)

/-- **The offset of the node at a path**, `pathOffset ℓ d P` from `((ℓ, d), P)`. -/
theorem pathOffset_inSpace :
    ComputableInSpace (fun q : (ℕ × ℕ) × List Bool => pathOffset q.1.1 q.1.2 q.2)
      (encPair (encPair encNat encNat) (encList encBool)) encNat
      fun q => 2 ^ 30 * (q.1.1 + q.1.2 +
        (encPair (encPair encNat encNat) (encList encBool) q).length + 1) := by
  have this : ComputableTidilyInSpace (fun q : (ℕ × ℕ) × List Bool => pathOffset q.1.1 q.1.2 q.2)
      (encPair (encPair encNat encNat) (encList encBool)) encNat fun q => 2 ^ 30 *
      (q.1.1 + q.1.2 + (encPair (encPair encNat encNat) (encList encBool) q).length + 1) := by
    have hl : (fun q => (encPair (encPair encNat encNat) (encList encBool) q).length) ≼
        fun q => 2 ^ 22 * (q.1.1 + q.1.2 +
          (encPair (encPair encNat encNat) (encList encBool) q).length + 1) :=
      .of_le fun _ => by omega
    have hld := (fst (encPair encNat encNat) (encList encBool)).weaken hl
    have hinit := budget_prod (fst' hld)
      (budget_prod (snd' hld) (budget_const (encB := encNat) 0 hl))
    have hstate (q : (ℕ × ℕ) × List Bool) (j : ℕ) :
        (encNat3 ((q.2.take j).foldl pathStep' (q.1.1, q.1.2, 0))).length ≤
          8 * (q.1.1 + q.1.2 + 1) := by
      rw [foldl_pathStep', foldl_pathStep]
      have h₁ := length_pathOffset_le q.1.1 q.1.2 (q.2.take j)
      have h₂ := length_encNat_le_self q.1.1
      have h₃ := length_encNat_le_self (q.1.2 - (q.2.take j).length)
      simp only [length_encPair, zero_add] at *
      omega
    have h := foldl (encL := encList encBool) (list := fun q : (ℕ × ℕ) × List Bool => q.2)
      (step := pathStep') ((snd (encPair encNat encNat) (encList encBool)).weaken hl) hinit
      pathStep'_inSpace
      (Q := fun q => 2 ^ 20 * (q.1.1 + q.1.2 + 2 * (8 * (q.1.1 + q.1.2 + 1)) + 4 + 1))
      (B := fun q => 8 * (q.1.1 + q.1.2 + 1))
      (fun q i hi => by
        have h₁ := hstate q i
        rw [foldl_pathStep', foldl_pathStep] at h₁ ⊢
        simp only [length_encPair, encBool_apply, List.length_singleton] at h₁ ⊢
        omega)
      (fun q i _ => hstate q i)
    refine (snd' (snd' h)).mono_le (fun q => ?_) |>.of_enc_eq fun q => by
      rw [foldl_pathStep', foldl_pathStep, zero_add]
    have := length_encNat_le_self q.1.1
    simp only [length_encPair] at *
    omega
  simpa only [computableInSpace_iff_computableTidilyInSpace] using this

end Reader

end Cslib.TreeEval
