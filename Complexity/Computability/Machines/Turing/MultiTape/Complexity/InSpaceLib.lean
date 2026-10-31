/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Plain
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Lists
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeOptionPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives

/-!
# Basic functions within linear work space

Arithmetic on binary naturals and operations on lists, computable within work space linear in the
lengths of their encoded arguments, for `Turing.MultiTapeTM.ComputableInSpace` (together with
compatibility wrappers in `Turing.MultiTapeTM.ComputableTidilyInSpace`). Combinators keep a
computation within a fixed space budget.

## Main results

* `Turing.MultiTapeTM.ComputableInSpace.natDivMod`: the quotient and the remainder.
* `Turing.MultiTapeTM.ComputableInSpace.natMul`: multiplication.
* `Turing.MultiTapeTM.ComputableInSpace.getD`: the element of a list at an index.
* `Turing.MultiTapeTM.ComputableInSpace.set`: replacing the element at an index.
* `Turing.MultiTapeTM.ComputableInSpace.budget_natAdd`,
  `Turing.MultiTapeTM.ComputableInSpace.budget_cons` and their siblings: arithmetic and list
  operations on values computed within a fixed budget stay within it.
* `Turing.MultiTapeTM.ComputableInSpace.dispatch`: a case distinction on the element of a
  fixed list at a computed index.
-/

@[expose] public section

namespace Turing.MultiTapeTM

namespace ComputableInSpace

variable {α β γ δ : Type} {encIn : α ↪ List Bool} {encB : β ↪ List Bool}
  {encC : γ ↪ List Bool} {Bs : α → ℕ}

/-! ### Computing within a space budget -/

theorem budget_comp {f : α → β} {g : β → γ} {Sg : β → ℕ}
    (hg : ComputableInSpace g encB encC Sg) (hf : ComputableInSpace f encIn encB Bs)
    (hS : (fun x => Sg (f x)) ≼ Bs) : ComputableInSpace (fun x => g (f x)) encIn encC Bs :=
  (hg.comp hf).weaken (.add (.refl _) hS)

theorem budget_comp_linear {f : α → β} {g : β → γ}
    (hg : ComputableInSpace g encB encC fun b => (encB b).length)
    (hf : ComputableInSpace f encIn encB Bs) :
    ComputableInSpace (fun x => g (f x)) encIn encC Bs :=
  budget_comp hg hf hf.length_le

/-- A multiple of the length of the argument, plus a constant, is linear in it. -/
theorem linear_mul (k : ℕ) : (fun b => k * ((encB b).length + 1)) ≼ fun b => (encB b).length :=
  ⟨k, fun _ => le_rfl⟩

theorem linear_succ : (fun b => (encB b).length + 1) ≼ fun b => (encB b).length :=
  ⟨1, fun _ => by dsimp only; omega⟩

/-- **Composition with a function computed in space linear in its argument**: no side condition,
as the argument is computed within the budget. -/
theorem budget_comp_lin {f : α → β} {g : β → γ} {Sg : β → ℕ}
    (hg : ComputableInSpace g encB encC Sg) (hSg : Sg ≼ fun b => (encB b).length)
    (hf : ComputableInSpace f encIn encB Bs) :
    ComputableInSpace (fun x => g (f x)) encIn encC Bs :=
  budget_comp_linear (hg.weaken hSg) hf

theorem budget_prod {f : α → β} {g : α → γ} (hf : ComputableInSpace f encIn encB Bs)
    (hg : ComputableInSpace g encIn encC Bs) :
    ComputableInSpace (fun x => (f x, g x)) encIn (encPair encB encC) Bs :=
  (hf.prod hg).weaken (.add (.refl _) (.refl _))

/-- A binary operation computed in space linear in its paired arguments, applied to two values
computed within the budget, stays within the budget. -/
private theorem budget_binop {f : α → β} {g : α → γ} {op : β × γ → δ} {encD : δ ↪ List Bool}
    {Sop : β × γ → ℕ} (hop : ComputableInSpace op (encPair encB encC) encD Sop)
    (hSop : Sop ≼ fun p => (encPair encB encC p).length)
    (hf : ComputableInSpace f encIn encB Bs)
    (hg : ComputableInSpace g encIn encC Bs) :
    ComputableInSpace (fun x => op (f x, g x)) encIn encD Bs :=
  budget_comp_lin hop hSop (budget_prod hf hg)

theorem budget_ite {c : α → Bool} {f g : α → β} (hc : ComputableInSpace c encIn encBool Bs)
    (hf : ComputableInSpace f encIn encB Bs) (hg : ComputableInSpace g encIn encB Bs) :
    ComputableInSpace (fun x => if c x then f x else g x) encIn encB Bs :=
  (hc.ite hf hg).weaken (.add (.refl _) (.ite _ (.refl _) (.refl _)))

theorem budget_const (b : β) (hl : (fun x => (encIn x).length) ≼ Bs) :
    ComputableInSpace (fun _ : α => b) encIn encB Bs :=
  (const b).weaken hl

theorem budget_finite {f : α → β} [Finite β] (g : β → γ)
    (hf : ComputableInSpace f encIn encB Bs) :
    ComputableInSpace (fun x => g (f x)) encIn encC Bs :=
  budget_comp_linear (of_finite g) hf

/-- **Iterating a step computed in linear space**, a computed number of times, within a budget
that covers the states. -/
theorem budget_iterate [Inhabited β] {n : α → ℕ} {init : α → β} {step : β → β} {B : α → ℕ}
    (hn : ComputableInSpace n encIn encNat Bs)
    (hinit : ComputableInSpace init encIn encB Bs)
    (hstep : ComputableInSpace step encB encB fun b => (encB b).length)
    (hstate : ∀ x, ∀ k ≤ n x, (encB (step^[k] (init x))).length ≤ B x) (hB : B ≼ Bs) :
    ComputableInSpace (fun x => step^[n x] (init x)) encIn encB Bs :=
  (iterate hn hinit hstep hstate hstate).weaken
    ((((BigOLe.refl _).add (.refl _)).add hB).add hB |>.add hn.length_le)

/-! ### Direct linear list and framing helpers -/

/-- Prepending an element to an encoded list in linear space. -/
theorem cons {ε : Type} (enc : ε ↪ List Bool) :
    ComputableInSpace (fun p : ε × List ε => p.1 :: p.2) (encPair enc (encList enc))
      (encList enc) fun p => (encPair enc (encList enc) p).length :=
  of_inO (ComputableInO.of_eq fun _ => rfl)

/-- Appending an element at the end of an encoded list in linear space. -/
theorem snoc {ε : Type} (enc : ε ↪ List Bool) :
    ComputableInSpace (fun p : List ε × ε => p.1 ++ [p.2]) (encPair (encList enc) enc)
      (encList enc) fun p => (encPair (encList enc) enc p).length :=
  of_inO (((ComputableInO.fst (encList enc) enc).append
    ((ComputableInO.of_linear (.of_frame fun _ => rfl)).comp_linear
      (ComputableInO.snd (encList enc) enc))
    (enc₂ := encFramed enc) fun _ => by simp).mono
    (T' := fun p => (encPair (encList enc) enc p).length) 2
    (fun _ => by omega) (fun _ => by omega))

/-- Framing an encoded value in linear space. -/
theorem frame {ε : Type} (enc : ε ↪ List Bool) :
    ComputableInSpace (fun a => Turing.MultiTapeTM.frame (enc a)) enc encBits
      fun a => (enc a).length :=
  of_inO (.of_linear (.of_frame fun _ => rfl))

/-! ### Arithmetic -/

theorem natSucc : ComputableInSpace (· + 1) encNat encNat fun n => (encNat n).length + 1 :=
  of_inO ComputableInO.natSucc

theorem natPred : ComputableInSpace (· - 1) encNat encNat fun n => (encNat n).length + 1 :=
  of_inO ComputableInO.natPred

theorem natIsZero :
    ComputableInSpace (fun n => decide (n = 0)) encNat encBool fun n => (encNat n).length :=
  of_inO ComputableInO.natIsZero

theorem natEq :
    ComputableInSpace (fun p : ℕ × ℕ => decide (p.1 = p.2)) (encPair encNat encNat) encBool
      fun p => (encPair encNat encNat p).length :=
  of_inO (.of_linear ComputableInLinearTimeAndSpace.natEq)

theorem natLt :
    ComputableInSpace (fun p : ℕ × ℕ => decide (p.1 < p.2)) (encPair encNat encNat) encBool
      fun p => (encPair encNat encNat p).length + 1 :=
  of_inO ComputableInO.natLt

theorem natSub :
    ComputableInSpace (fun p : ℕ × ℕ => p.2 - p.1) (encPair encNat encNat) encNat
      fun p => (encPair encNat encNat p).length + 1 :=
  of_inO ComputableInO.natSub

theorem natAdd :
    ComputableInSpace (fun p : ℕ × ℕ => p.1 + p.2) (encPair encNat encNat) encNat
      fun p => (encPair encNat encNat p).length + 1 :=
  of_inO ComputableInO.natAdd

/-- **Dispatching on the element of a fixed list at a computed index**: if `F x` is computed in
linear space for every `x`, and the index is computed in linear space, then so is
`F (l.getD (i a) d) a`. A finite case distinction, as on the instruction at the current label of
a program. -/
theorem dispatch {κ : Type*} (l : List κ) (d : κ) (F : κ → α → β)
    (hF : ∀ x, ComputableInSpace (F x) encIn encB fun a => (encIn a).length) {i : α → ℕ}
    (hi : ComputableInSpace i encIn encNat fun a => (encIn a).length) :
    ComputableInSpace (fun a => F (l.getD (i a) d) a) encIn encB
      fun a => (encIn a).length := by
  induction l generalizing i with
  | nil => simpa using hF d
  | cons x l ih =>
    have hz : ComputableInSpace (fun a => decide (i a = 0)) encIn encBool
        fun a => (encIn a).length := budget_comp_lin natIsZero (.refl _) hi
    have hpred : ComputableInSpace (fun a => i a - 1) encIn encNat
        fun a => (encIn a).length := budget_comp_lin natPred linear_succ hi
    refine (budget_ite hz (hF x) (ih hpred)).of_enc_eq fun a => ?_
    rcases i a with _ | c <;> simp

/-- A step of division: subtract the divisor from the remainder and count, while it fits. -/
def divStep (s : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  if 0 < s.1 ∧ s.1 ≤ s.2.2 then (s.1, s.2.1 + 1, s.2.2 - s.1) else s

theorem iterate_divStep (d r : ℕ) :
    ∀ k, divStep^[k] (d, 0, r) = (d, min k (r / d), r - d * min k (r / d)) := by
  intro k
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · induction k with
    | zero => simp
    | succ k ih => simp [Function.iterate_succ_apply', ih, divStep]
  · induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, divStep]
      by_cases hk : k < r / d
      · have h₁ : (k + 1) * d ≤ r := (Nat.le_div_iff_mul_le hd).mp hk
        have h₂ : d ≤ r - d * k := by rw [Nat.add_mul, one_mul] at h₁; rw [Nat.mul_comm]; omega
        rw [Nat.min_eq_left hk.le, Nat.min_eq_left (show k + 1 ≤ r / d by omega)]
        simp only [hd, h₂, and_self, ↓reduceIte, Prod.mk.injEq, true_and]
        rw [Nat.mul_succ]
        omega
      · have h₁ : r - d * (r / d) < d := by
          rw [← Nat.mod_eq_sub_mul_div]; exact Nat.mod_lt _ hd
        rw [Nat.min_eq_right (show r / d ≤ k by omega),
          Nat.min_eq_right (show r / d ≤ k + 1 by omega)]
        simp only [hd, true_and, show ¬d ≤ r - d * (r / d) by omega, ↓reduceIte]

theorem iterate_divStep_self (d r : ℕ) : divStep^[r] (d, 0, r) = (d, r / d, r % d) := by
  rw [iterate_divStep]
  have : r / d ≤ r := Nat.div_le_self r d
  rw [Nat.min_eq_right this, Nat.mod_eq_sub_mul_div]

theorem divStep_inSpace :
    ComputableInSpace divStep encNat3 encNat3 fun s => (encNat3 s).length + 1 := by
  have hl : (fun s => (encNat3 s).length) ≼ fun s => (encNat3 s).length + 1 := .of_le fun _ => by
    omega
  have h₁ : ComputableInSpace (fun s : ℕ × ℕ × ℕ => s.1) encNat3 encNat
      fun s => (encNat3 s).length + 1 := (fst _ _).weaken hl
  have h₂₂ : ComputableInSpace (fun s : ℕ × ℕ × ℕ => s.2) encNat3 (encPair encNat encNat)
      fun s => (encNat3 s).length + 1 := (snd _ _).weaken hl
  have h₂ := fst' h₂₂
  have h₃ := snd' h₂₂
  have hz := budget_comp_lin natIsZero (.refl _) h₁
  have hlt := budget_binop natLt linear_succ h₃ h₁
  have hc := budget_finite (encC := encBool) (fun q : Bool × Bool => !q.1 && !q.2)
    (budget_prod hz hlt)
  have hsucc := budget_comp_lin natSucc linear_succ h₂
  have hsub := budget_binop natSub linear_succ h₁ h₃
  have hnew := budget_prod h₁ (budget_prod hsucc hsub)
  have hall := budget_ite hc hnew ((ComputableInSpace.of_inO
    (ComputableInO.of_eq (f := id) fun _ => rfl)).weaken hl)
  refine hall.of_enc_eq fun s => ?_
  simp only [divStep]
  congr 1
  by_cases h : 0 < s.1 ∧ s.1 ≤ s.2.2
  · simp [h, h.1.ne', show ¬s.2.2 < s.1 by omega]
  · rcases Nat.eq_zero_or_pos s.1 with h0 | h0
    · simp [h0]
    · simp [h, h0.ne', show s.2.2 < s.1 by omega]

/-- **The quotient and the remainder**, `(r / d, r % d)` from `(r, d)`. -/
theorem natDivMod :
    ComputableInSpace (fun p : ℕ × ℕ => (p.1 / p.2, p.1 % p.2)) (encPair encNat encNat)
      (encPair encNat encNat) fun p => 16 * ((encPair encNat encNat p).length + 1) := by
  have hinit : ComputableInSpace (fun p : ℕ × ℕ => (p.2, 0, p.1)) (encPair encNat encNat)
      encNat3 fun p => 2 * ((encPair encNat encNat p).length + 1) :=
    (budget_prod (snd _ _) (budget_prod (budget_const 0 (.refl _)) (fst _ _))).weaken
      (.of_le fun p => by omega)
  have hlen (p : ℕ × ℕ) (k : ℕ) : (encNat3 (divStep^[k] (p.2, 0, p.1))).length ≤
      3 * ((encPair encNat encNat p).length + 1) := by
    rw [iterate_divStep]
    have h₁ := Turing.MultiTapeTM.length_encNat_mono (show min k (p.1 / p.2) ≤ p.1 from
      (Nat.min_le_right _ _).trans (Nat.div_le_self _ _))
    have h₂ := Turing.MultiTapeTM.length_encNat_mono
      (show p.1 - p.2 * min k (p.1 / p.2) ≤ p.1 from Nat.sub_le _ _)
    simp only [length_encPair] at h₁ h₂ ⊢
    omega
  have h := iterate (n := fun p : ℕ × ℕ => p.1) (fst _ _) hinit divStep_inSpace
    (Q := fun p => 3 * ((encPair encNat encNat p).length + 1) + 1)
    (B := fun p => 3 * ((encPair encNat encNat p).length + 1))
    (fun p k _ => by have := hlen p k; omega) (fun p k _ => hlen p k)
  refine (snd' h).mono_le (fun p => ?_) |>.of_enc_eq fun p => ?_
  · simp only [length_encPair]; omega
  · rw [iterate_divStep_self]

/-- The quotient. -/
theorem natDiv :
    ComputableInSpace (fun p : ℕ × ℕ => p.1 / p.2) (encPair encNat encNat) encNat
      fun p => 16 * ((encPair encNat encNat p).length + 1) :=
  fst' natDivMod

/-- The remainder. -/
theorem natMod :
    ComputableInSpace (fun p : ℕ × ℕ => p.1 % p.2) (encPair encNat encNat) encNat
      fun p => 16 * ((encPair encNat encNat p).length + 1) :=
  snd' natDivMod

/-- **Multiplication in binary.** -/
theorem natMul :
    ComputableInSpace (fun p : ℕ × ℕ => p.1 * p.2) (encPair encNat encNat) encNat
      fun p => 32 * ((encPair encNat encNat p).length + 1) :=
  (of_inO ComputableInO.natMul).weaken (.of_le fun _ => by omega)

/-! ### Lists of naturals -/

/-- **The element at an index**, `l.getD i 0` from `(l, i)`. -/
theorem getD :
    ComputableInSpace (fun p : List ℕ × ℕ => p.1.getD p.2 0)
      (encPair (encList encNat) encNat) encNat
      fun p => 8 * ((encPair (encList encNat) encNat p).length + 1) := by
  have htail : ComputableInSpace List.tail (encList encNat) (encList encNat)
      fun l => (encList encNat l).length :=
    of_inO (.of_linear (ListEncoding.tail encNat))
  have hlen (p : List ℕ × ℕ) (k : ℕ) :
      (encList encNat (List.tail^[k] p.1)).length ≤ (encList encNat p.1).length := by
    rw [List.tail_iterate, ← p.1.take_append_drop k, encList_append, List.length_append]; simp
  have h := iterate (n := fun p : List ℕ × ℕ => p.2) (snd _ _) (fst _ _) htail
    (Q := fun p => (encList encNat p.1).length) (B := fun p => (encList encNat p.1).length)
    (fun p k _ => hlen p k) (fun p k _ => hlen p k)
  have hhead : ComputableInSpace (fun l : List ℕ => l.headD 0) (encList encNat) encNat
      fun l => (encList encNat l).length :=
    of_inO (.of_linear (ListEncoding.headD 0))
  refine (budget_comp_linear hhead h).mono_le (fun p => ?_) |>.of_enc_eq fun p => ?_
  · simp only [length_encPair]; omega
  · rw [List.tail_iterate]
    simp [List.getD_eq_getElem?_getD, List.headD_eq_head?_getD, List.head?_drop]

/-- A step of rebuilding a list with the element at `i` replaced by `v`. -/
def setStep (s : (ℕ × ℕ) × ℕ × List ℕ) (a : ℕ) : (ℕ × ℕ) × ℕ × List ℕ :=
  (s.1, s.2.1 + 1, s.2.2 ++ [if s.2.1 = s.1.1 then s.1.2 else a])

theorem foldl_setStep (i v : ℕ) (l : List ℕ) (j : ℕ) (acc : List ℕ) :
    l.foldl setStep ((i, v), j, acc) =
      ((i, v), j + l.length, acc ++ l.mapIdx fun k a => if j + k = i then v else a) := by
  induction l generalizing j acc with
  | nil => simp
  | cons a l ih =>
    have hf : (fun k b => if j + 1 + k = i then v else b) =
        (fun k b => if j + (k + 1) = i then v else b) := by
      funext k b; rw [show j + 1 + k = j + (k + 1) by omega]
    rw [List.foldl_cons, setStep, ih, List.mapIdx_cons, hf]
    simp only [List.length_cons, List.append_assoc, List.singleton_append, add_zero,
      Prod.mk.injEq, true_and, and_true]
    omega

theorem set_eq_mapIdx (l : List ℕ) (i v : ℕ) :
    l.set i v = l.mapIdx fun k a => if k = i then v else a := by
  refine List.ext_getElem (by simp) fun k h₁ h₂ => ?_
  rw [List.getElem_set, List.getElem_mapIdx]
  split_ifs with h₃ h₄ h₄ <;> first | rfl | omega

theorem length_encList_set_le (l : List ℕ) (i v : ℕ) :
    (encList encNat (l.set i v)).length ≤
      (encList encNat l).length + 2 * (encNat v).length + 1 := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
    rcases i with _ | i
    · simp [length_encList]; omega
    · simp only [List.set_cons_succ, length_encList, List.map_cons, List.sum_cons] at ih ⊢
      have := ih i
      omega

/-- The encoding of the states of `setStep`. -/
abbrev encSetState : (ℕ × ℕ) × ℕ × List ℕ ↪ List Bool :=
  encPair (encPair encNat encNat) (encPair encNat (encList encNat))

theorem setStep_inSpace :
    ComputableInSpace (fun q : ((ℕ × ℕ) × ℕ × List ℕ) × ℕ => setStep q.1 q.2)
      (encPair encSetState encNat) encSetState
      fun q => 4 * ((encPair encSetState encNat q).length + 1) := by
  have hl : (fun q => (encPair encSetState encNat q).length) ≼
      fun q => 4 * ((encPair encSetState encNat q).length + 1) := .of_le fun _ => by omega
  have hs := (fst encSetState encNat).weaken hl
  have ha := (snd encSetState encNat).weaken hl
  have hiv := fst' hs
  have hi := fst' hiv
  have hv := snd' hiv
  have hj := fst' (snd' hs)
  have hacc := snd' (snd' hs)
  have he := budget_binop natEq (.refl _) hj hi
  have hel := budget_ite he hv ha
  have happ := budget_binop (snoc encNat) (.refl _) hacc hel
  have hsucc := budget_comp_lin natSucc linear_succ hj
  refine (budget_prod hiv (budget_prod hsucc happ)).of_enc_eq fun q => ?_
  simp only [setStep]
  congr 1
  by_cases h : q.1.2.1 = q.1.1.1 <;> simp [h]

/-- **Replacing the element at an index**, `l.set i v` from `(l, i, v)`. -/
theorem set :
    ComputableInSpace (fun p : List ℕ × ℕ × ℕ => p.1.set p.2.1 p.2.2)
      (encPair (encList encNat) (encPair encNat encNat)) (encList encNat)
      fun p => 128 * ((encPair (encList encNat) (encPair encNat encNat) p).length + 1) := by
  have hinit : ComputableInSpace (fun p : List ℕ × ℕ × ℕ => ((p.2.1, p.2.2), 0, []))
      (encPair (encList encNat) (encPair encNat encNat)) encSetState
      fun p => 4 * ((encPair (encList encNat) (encPair encNat encNat) p).length + 1) := by
    have hl : (fun p => (encPair (encList encNat) (encPair encNat encNat) p).length) ≼
        fun p => 4 * ((encPair (encList encNat) (encPair encNat encNat) p).length + 1) :=
      .of_le fun _ => by omega
    have h₂ := (snd (encList encNat) (encPair encNat encNat)).weaken hl
    exact budget_prod (budget_prod (fst' h₂) (snd' h₂))
      (budget_prod (budget_const 0 hl) (budget_const [] hl))
  have hstate (p : List ℕ × ℕ × ℕ) (k : ℕ) (hk : k ≤ p.1.length) :
      (encSetState ((p.1.take k).foldl setStep ((p.2.1, p.2.2), 0, []))).length ≤
        6 * ((encPair (encList encNat) (encPair encNat encNat) p).length + 1) := by
    rw [foldl_setStep]
    simp only [zero_add, List.nil_append, List.length_take, Nat.min_eq_left hk]
    have hset : (p.1.take k).mapIdx (fun k a => if k = p.2.1 then p.2.2 else a) =
        (p.1.take k).set p.2.1 p.2.2 := (set_eq_mapIdx _ _ _).symm
    have h₁ := length_encList_set_le (p.1.take k) p.2.1 p.2.2
    have h₂ := length_encList_take_le encNat p.1 k
    have h₃ : (encNat k).length ≤ (encList encNat p.1).length :=
      (length_encNat_le_self k).trans (hk.trans (length_le_length_encList _ _))
    simp only [length_encPair, hset] at h₁ ⊢
    omega
  have hmem (p : List ℕ × ℕ × ℕ) (i : ℕ) (hi : i < p.1.length) :
      (encNat p.1[i]).length ≤ (encList encNat p.1).length :=
    length_le_encList_of_mem encNat (List.getElem_mem hi)
  have h := foldl (list := fun p : List ℕ × ℕ × ℕ => p.1) (step := setStep)
    (fst (encList encNat) (encPair encNat encNat)) hinit setStep_inSpace
    (Q := fun p => 4 * (12 * ((encPair (encList encNat) (encPair encNat encNat) p).length + 1) +
      (encList encNat p.1).length + 4))
    (B := fun p => 6 * ((encPair (encList encNat) (encPair encNat encNat) p).length + 1))
    (fun p i hi => by
      have h₁ := hstate p i hi.le
      have h₂ := hmem p i hi
      rw [length_encPair]
      dsimp only
      omega)
    (fun p i hi => hstate p i hi)
  refine (snd' (snd' h)).mono_le (fun p => ?_) |>.of_enc_eq fun p => ?_
  · simp only [length_encPair]; omega
  · rw [foldl_setStep, set_eq_mapIdx]
    simp

/-! ### Building and measuring lists -/

section Generic

variable {ε : Type} {enc : ε ↪ List Bool}

theorem iterate_cons (a : ε) (l : List ε) (k : ℕ) :
    (fun q : ε × List ε => (q.1, q.1 :: q.2))^[k] (a, l) = (a, List.replicate k a ++ l) := by
  induction k generalizing l with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', ih, List.replicate_succ]; rfl

/-- **A list of copies**, `List.replicate n a` from `(n, a)`; its work space is that of the list. -/
theorem replicate [Inhabited ε] :
    ComputableInSpace (fun p : ℕ × ε => List.replicate p.1 p.2) (encPair encNat enc)
      (encList enc) fun p => 64 * ((p.1 + 1) * ((encPair encNat enc p).length + 1)) := by
  have hcons : ComputableInSpace (fun q : ε × List ε => (q.1, q.1 :: q.2))
      (encPair enc (encList enc)) (encPair enc (encList enc))
      fun q => 2 * ((encPair enc (encList enc) q).length + 1) := by
    have hl : (fun q => (encPair enc (encList enc) q).length) ≼
        fun q => 2 * ((encPair enc (encList enc) q).length + 1) := .of_le fun _ => by omega
    exact budget_prod ((fst _ _).weaken hl) ((cons enc).weaken hl)
  have hinit : ComputableInSpace (fun p : ℕ × ε => (p.2, ([] : List ε)))
      (encPair encNat enc) (encPair enc (encList enc))
      fun p => 2 * ((encPair encNat enc p).length + 1) :=
    (budget_prod (snd _ _) (budget_const [] (.refl _))).weaken (.of_le fun p => by omega)
  have hlen (p : ℕ × ε) (k : ℕ) (hk : k ≤ p.1) :
      (encPair enc (encList enc) ((fun q : ε × List ε => (q.1, q.1 :: q.2))^[k] (p.2, []))).length
        ≤ 3 * ((p.1 + 1) * ((encPair encNat enc p).length + 1)) := by
    rw [iterate_cons, List.append_nil, length_encPair, length_encList]
    simp only [List.map_replicate, List.sum_replicate, smul_eq_mul, length_encPair]
    have := Nat.mul_le_mul_right (2 * (enc p.2).length + 1) hk
    nlinarith
  have h := iterate (n := fun p : ℕ × ε => p.1) (fst _ _) hinit hcons
    (Q := fun p => 2 * (3 * ((p.1 + 1) * ((encPair encNat enc p).length + 1)) + 1))
    (B := fun p => 3 * ((p.1 + 1) * ((encPair encNat enc p).length + 1)))
    (fun p k hk => by have := hlen p k hk; omega) hlen
  refine (snd' h).mono_le (fun p => ?_) |>.of_enc_eq fun p => by
    rw [iterate_cons, List.append_nil]
  have h₁ : (encPair encNat enc p).length ≤ (p.1 + 1) * ((encPair encNat enc p).length + 1) := by
    nlinarith
  have h₂ : (encNat p.1).length ≤ (encPair encNat enc p).length := by
    simp only [length_encPair]; omega
  have h₃ : 1 ≤ (p.1 + 1) * ((encPair encNat enc p).length + 1) := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (by omega))
  omega

/-- **The length of a list.** -/
theorem length :
    ComputableInSpace (fun l : List ε => l.length) (encList enc) encNat
      fun l => 8 * ((encList enc l).length + 1) := by
  have hl := length_le_length_encList enc
  have hbits := length_encNat_le_self
  have hstep : ComputableInSpace (fun q : ℕ × ε => q.1 + 1) (encPair encNat enc) encNat
      fun q => (encPair encNat enc q).length + 1 :=
    budget_comp_lin natSucc linear_succ ((fst _ _).weaken (.of_le fun _ => by omega))
  have h := foldl (encL := encList enc) (list := fun l : List ε => l) (init := fun _ => 0)
    (step := fun n (_ : ε) => n + 1)
    (of_inO (ComputableInO.of_eq (f := id) fun _ => rfl)) (const 0) hstep
    (Q := fun l => 3 * (encList enc l).length + 3) (B := fun l => (encList enc l).length)
    (fun l i hi => by
      have h₁ := hbits i
      have h₂ := length_le_encList_of_mem enc (List.getElem_mem hi)
      rw [length_encPair, List.foldl_const, List.length_take, Nat.min_eq_left hi.le,
        ComputableInO.iterate_succ_eq, zero_add]
      have := hl l
      dsimp only
      omega)
    (fun l i hi => by
      rw [List.foldl_const, List.length_take, Nat.min_eq_left hi,
        ComputableInO.iterate_succ_eq, zero_add]
      exact (hbits _).trans (hi.trans (hl l)))
  refine h.mono_le (fun l => by omega) |>.of_enc_eq fun l => by
    rw [List.foldl_const, ComputableInO.iterate_succ_eq, zero_add]

/-- **Mapping with a parameter**, within the space of the parameter, of the list, of the mapped list
and of the largest application. -/
theorem mapWith {π κ : Type} {encP : π ↪ List Bool} {encK : κ ↪ List Bool} {f : π × ε → κ}
    {Sf : π × ε → ℕ} {par : α → π} {list : α → List ε} {Sp Sl : α → ℕ}
    (hf : ComputableInSpace f (encPair encP enc) encK Sf)
    (hpar : ComputableInSpace par encIn encP Sp)
    (hlist : ComputableInSpace list encIn (encList enc) Sl) :
    ComputableInSpace (fun x => (list x).map fun a => f (par x, a)) encIn (encList encK)
      fun x => (encIn x).length + Sp x + Sl x + (encP (par x)).length +
        (encList enc (list x)).length +
        (encList encK ((list x).map fun a => f (par x, a))).length +
        listMax (fun a => Sf (par x, a)) (list x) := by
  have hfold_eq (p : π) (l : List ε) (acc : List κ) :
      l.foldl (fun acc a => acc ++ [f (p, a)]) acc = acc ++ l.map (fun a => f (p, a)) := by
    induction l generalizing acc with
    | nil => simp
    | cons a l ih => simp [ih, List.append_assoc]
  have hq := fst (encPair encP (encList encK)) enc
  have hel := snd (encPair encP (encList encK)) enc
  obtain ⟨c, hc⟩ := hf.length_le
  have hstep : ComputableInSpace (fun q : (π × List κ) × ε => q.1.2 ++ [f (q.1.1, q.2)])
      (encPair (encPair encP (encList encK)) enc) (encList encK)
      fun q => (encPair (encPair encP (encList encK)) enc q).length + Sf (q.1.1, q.2) :=
    ((snoc encK).comp ((snd' hq).prod (hf.comp ((fst' hq).prod hel)))).weaken
      ⟨2 * c + 6, fun q => by
        have := hc (q.1.1, q.2)
        simp only [length_encPair] at this ⊢
        nlinarith⟩
  have hst (x : α) (i : ℕ) :
      (encList encK (((list x).take i).foldl (fun acc a => acc ++ [f (par x, a)]) [])).length ≤
        (encList encK ((list x).map fun a => f (par x, a))).length := by
    rw [hfold_eq, List.nil_append, List.map_take]
    exact length_encList_take_le encK _ _
  have hfold := foldlWith (encL := encList enc) (encB := encList encK)
    (step := fun p acc a => acc ++ [f (p, a)]) hpar hlist (const []) hstep
    (Q := fun x => 4 * (encP (par x)).length +
      3 * (encList enc (list x)).length +
      3 * (encList encK ((list x).map fun a => f (par x, a))).length + 5 +
      listMax (fun a => Sf (par x, a)) (list x))
    (B := fun x => (encList encK ((list x).map fun a => f (par x, a))).length)
    (fun x i hi => by
      have h₁ := length_le_encList_of_mem enc (List.getElem_mem hi)
      have h₂ := le_listMax (f := fun a => Sf (par x, a)) (List.getElem_mem hi)
      have h₃ := hst x i
      simp only [length_encPair] at h₂ ⊢
      omega)
    (fun x i _ => hst x i)
  refine (hfold.weaken ⟨6, fun x => by dsimp only; omega⟩).of_enc_eq fun x => ?_
  rw [hfold_eq, List.nil_append]

end Generic

/-! ### Operations within a fixed budget -/

section BudgetOps

variable {ε : Type} {enc : ε ↪ List Bool}

/-- Adding an element in front of a list, within the budget. -/
theorem budget_cons {a : α → ε} {l : α → List ε} (ha : ComputableInSpace a encIn enc Bs)
    (hl : ComputableInSpace l encIn (encList enc) Bs) :
    ComputableInSpace (fun x => a x :: l x) encIn (encList enc) Bs :=
  budget_binop (cons enc) (.refl _) ha hl

/-- Appending an element at the end of a list, within the budget. -/
theorem budget_snoc {l : α → List ε} {a : α → ε} (hl : ComputableInSpace l encIn (encList enc) Bs)
    (ha : ComputableInSpace a encIn enc Bs) :
    ComputableInSpace (fun x => l x ++ [a x]) encIn (encList enc) Bs :=
  budget_binop (snoc enc) (.refl _) hl ha

/-- The head of a list, within the budget. -/
theorem budget_headD (d : ε) {l : α → List ε}
    (hl : ComputableInSpace l encIn (encList enc) Bs) :
    ComputableInSpace (fun x => (l x).headD d) encIn enc Bs :=
  budget_comp_linear (of_inO (.of_linear (ListEncoding.headD (enc := encList enc) d))) hl

/-- The tail of a list, within the budget. -/
theorem budget_tail {l : α → List ε} (hl : ComputableInSpace l encIn (encList enc) Bs) :
    ComputableInSpace (fun x => (l x).tail) encIn (encList enc) Bs :=
  budget_comp_linear (of_inO (.of_linear (ListEncoding.tail (enc₁ := enc)))) hl

/-- Whether a list is empty, within the budget. -/
theorem budget_isEmpty {l : α → List ε} (hl : ComputableInSpace l encIn (encList enc) Bs) :
    ComputableInSpace (fun x => (l x).isEmpty) encIn encBool Bs :=
  budget_comp_linear (of_inO (.of_linear (ListEncoding.isEmpty (enc₁ := enc)))) hl

/-- The length of a list, within the budget. -/
theorem budget_length {l : α → List ε} (hl : ComputableInSpace l encIn (encList enc) Bs) :
    ComputableInSpace (fun x => (l x).length) encIn encNat Bs :=
  budget_comp_lin length (linear_mul 8) hl

end BudgetOps

/-- The successor, within the budget. -/
theorem budget_natSucc {a : α → ℕ} (ha : ComputableInSpace a encIn encNat Bs) :
    ComputableInSpace (fun x => a x + 1) encIn encNat Bs :=
  budget_comp_lin natSucc linear_succ ha

/-- The predecessor, within the budget. -/
theorem budget_natPred {a : α → ℕ} (ha : ComputableInSpace a encIn encNat Bs) :
    ComputableInSpace (fun x => a x - 1) encIn encNat Bs :=
  budget_comp_lin natPred linear_succ ha

/-- The zero test, within the budget. -/
theorem budget_natIsZero {a : α → ℕ} (ha : ComputableInSpace a encIn encNat Bs) :
    ComputableInSpace (fun x => decide (a x = 0)) encIn encBool Bs :=
  budget_comp_lin natIsZero (.refl _) ha

/-- Equality of numbers, within the budget. -/
theorem budget_natEq {a b : α → ℕ} (ha : ComputableInSpace a encIn encNat Bs)
    (hb : ComputableInSpace b encIn encNat Bs) :
    ComputableInSpace (fun x => decide (a x = b x)) encIn encBool Bs :=
  budget_binop natEq (.refl _) ha hb

/-- The sum, within the budget. -/
theorem budget_natAdd {a b : α → ℕ} (ha : ComputableInSpace a encIn encNat Bs)
    (hb : ComputableInSpace b encIn encNat Bs) :
    ComputableInSpace (fun x => a x + b x) encIn encNat Bs :=
  budget_binop natAdd linear_succ ha hb

/-- The product, within the budget. -/
theorem budget_natMul {a b : α → ℕ} (ha : ComputableInSpace a encIn encNat Bs)
    (hb : ComputableInSpace b encIn encNat Bs) :
    ComputableInSpace (fun x => a x * b x) encIn encNat Bs :=
  budget_binop natMul (linear_mul 32) ha hb

/-- The quotient, within the budget. -/
theorem budget_natDiv {a b : α → ℕ} (ha : ComputableInSpace a encIn encNat Bs)
    (hb : ComputableInSpace b encIn encNat Bs) :
    ComputableInSpace (fun x => a x / b x) encIn encNat Bs :=
  budget_binop natDiv (linear_mul 16) ha hb

/-- Truncated subtraction, within the budget. -/
theorem budget_natSub {a b : α → ℕ} (ha : ComputableInSpace a encIn encNat Bs)
    (hb : ComputableInSpace b encIn encNat Bs) :
    ComputableInSpace (fun x => a x - b x) encIn encNat Bs :=
  budget_binop natSub linear_succ hb ha

/-- The remainder, within the budget. -/
theorem budget_natMod {a b : α → ℕ} (ha : ComputableInSpace a encIn encNat Bs)
    (hb : ComputableInSpace b encIn encNat Bs) :
    ComputableInSpace (fun x => a x % b x) encIn encNat Bs :=
  budget_binop natMod (linear_mul 16) ha hb

/-- The strict comparison, within the budget. -/
theorem budget_natLt {a b : α → ℕ} (ha : ComputableInSpace a encIn encNat Bs)
    (hb : ComputableInSpace b encIn encNat Bs) :
    ComputableInSpace (fun x => decide (a x < b x)) encIn encBool Bs :=
  budget_binop natLt linear_succ ha hb

/-- A fixed natural power, within the budget. -/
theorem budget_natPow {a : α → ℕ} (ha : ComputableInSpace a encIn encNat Bs)
    (hin : (fun x => (encIn x).length) ≼ Bs) (d : ℕ) :
    ComputableInSpace (fun x => a x ^ d) encIn encNat Bs := by
  induction d with
  | zero => simpa using budget_const (encB := encNat) 1 hin
  | succ d ih => simpa [pow_succ] using budget_natMul ih ha

/-- The remainder modulo a positive constant, as an element of `Fin w`. -/
theorem budget_finMod {w : ℕ} (hw : 0 < w) {m : α → ℕ}
    (hm : ComputableInSpace m encIn encNat Bs) (hin : (fun x => (encIn x).length) ≼ Bs) :
    ComputableInSpace (fun x => (⟨m x % w, Nat.mod_lt _ hw⟩ : Fin w)) encIn
      (Fin.valEmbedding.trans encNat) Bs :=
  (budget_natMod hm (budget_const (encB := encNat) w hin)).of_enc_eq fun _ => rfl

/-- `some` of a number, within the budget. -/
theorem budget_optionSome {a : α → ℕ} (ha : ComputableInSpace a encIn encNat Bs) :
    ComputableInSpace (fun x => some (a x)) encIn (encOption encNat) Bs :=
  budget_comp_linear (of_inO (ComputableInDegree.optionSome (enc₁ := encNat)).inO_one) ha

end ComputableInSpace

/-! ### Tidy compatibility wrappers -/

namespace ComputableTidilyInSpace

variable {α β γ δ : Type} {encIn : α ↪ List Bool} {encB : β ↪ List Bool}
  {encC : γ ↪ List Bool} {Bs : α → ℕ}

theorem budget_comp {f : α → β} {g : β → γ} {Sg : β → ℕ}
    (hg : ComputableTidilyInSpace g encB encC Sg) (hf : ComputableTidilyInSpace f encIn encB Bs)
    (hS : (fun x => Sg (f x)) ≼ Bs) : ComputableTidilyInSpace (fun x => g (f x)) encIn encC Bs :=
  (hg.comp hf).weaken (.add (.refl _) hS)

theorem budget_comp_linear {f : α → β} {g : β → γ}
    (hg : ComputableTidilyInSpace g encB encC fun b => (encB b).length)
    (hf : ComputableTidilyInSpace f encIn encB Bs) :
    ComputableTidilyInSpace (fun x => g (f x)) encIn encC Bs :=
  budget_comp hg hf hf.length_le

theorem linear_mul (k : ℕ) : (fun b => k * ((encB b).length + 1)) ≼ fun b => (encB b).length :=
  ComputableInSpace.linear_mul k

theorem linear_succ : (fun b => (encB b).length + 1) ≼ fun b => (encB b).length :=
  ComputableInSpace.linear_succ

theorem budget_comp_lin {f : α → β} {g : β → γ} {Sg : β → ℕ}
    (hg : ComputableTidilyInSpace g encB encC Sg) (hSg : Sg ≼ fun b => (encB b).length)
    (hf : ComputableTidilyInSpace f encIn encB Bs) :
    ComputableTidilyInSpace (fun x => g (f x)) encIn encC Bs :=
  budget_comp_linear (hg.weaken hSg) hf

theorem budget_prod {f : α → β} {g : α → γ} (hf : ComputableTidilyInSpace f encIn encB Bs)
    (hg : ComputableTidilyInSpace g encIn encC Bs) :
    ComputableTidilyInSpace (fun x => (f x, g x)) encIn (encPair encB encC) Bs :=
  (hf.prod hg).weaken (.add (.refl _) (.refl _))

private theorem budget_binop {f : α → β} {g : α → γ} {op : β × γ → δ} {encD : δ ↪ List Bool}
    {Sop : β × γ → ℕ} (hop : ComputableTidilyInSpace op (encPair encB encC) encD Sop)
    (hSop : Sop ≼ fun p => (encPair encB encC p).length)
    (hf : ComputableTidilyInSpace f encIn encB Bs)
    (hg : ComputableTidilyInSpace g encIn encC Bs) :
    ComputableTidilyInSpace (fun x => op (f x, g x)) encIn encD Bs :=
  budget_comp_lin hop hSop (budget_prod hf hg)

theorem budget_ite {c : α → Bool} {f g : α → β} (hc : ComputableTidilyInSpace c encIn encBool Bs)
    (hf : ComputableTidilyInSpace f encIn encB Bs) (hg : ComputableTidilyInSpace g encIn encB Bs) :
    ComputableTidilyInSpace (fun x => if c x then f x else g x) encIn encB Bs :=
  (hc.ite hf hg).weaken (.add (.refl _) (.ite _ (.refl _) (.refl _)))

theorem budget_const (b : β) (hl : (fun x => (encIn x).length) ≼ Bs) :
    ComputableTidilyInSpace (fun _ : α => b) encIn encB Bs :=
  (const b).weaken hl

theorem budget_finite {f : α → β} [Finite β] (g : β → γ)
    (hf : ComputableTidilyInSpace f encIn encB Bs) :
    ComputableTidilyInSpace (fun x => g (f x)) encIn encC Bs :=
  budget_comp_linear (of_finite g) hf

theorem budget_iterate [Inhabited β] {n : α → ℕ} {init : α → β} {step : β → β} {B : α → ℕ}
    (hn : ComputableTidilyInSpace n encIn encNat Bs)
    (hinit : ComputableTidilyInSpace init encIn encB Bs)
    (hstep : ComputableTidilyInSpace step encB encB fun b => (encB b).length)
    (hstate : ∀ x, ∀ k ≤ n x, (encB (step^[k] (init x))).length ≤ B x) (hB : B ≼ Bs) :
    ComputableTidilyInSpace (fun x => step^[n x] (init x)) encIn encB Bs :=
  (iterate hn hinit hstep hstate hstate).weaken
    ((((BigOLe.refl _).add (.refl _)).add hB).add hB |>.add hn.length_le)

theorem natSucc : ComputableTidilyInSpace (· + 1) encNat encNat fun n => (encNat n).length + 1 :=
  ComputableInSpace.natSucc.tidy

theorem natPred : ComputableTidilyInSpace (· - 1) encNat encNat fun n => (encNat n).length + 1 :=
  ComputableInSpace.natPred.tidy

theorem natIsZero :
    ComputableTidilyInSpace (fun n => decide (n = 0)) encNat encBool fun n => (encNat n).length :=
  ComputableInSpace.natIsZero.tidy

theorem natEq :
    ComputableTidilyInSpace (fun p : ℕ × ℕ => decide (p.1 = p.2)) (encPair encNat encNat) encBool
      fun p => (encPair encNat encNat p).length :=
  ComputableInSpace.natEq.tidy

theorem natLt :
    ComputableTidilyInSpace (fun p : ℕ × ℕ => decide (p.1 < p.2)) (encPair encNat encNat) encBool
      fun p => (encPair encNat encNat p).length + 1 :=
  ComputableInSpace.natLt.tidy

theorem natSub :
    ComputableTidilyInSpace (fun p : ℕ × ℕ => p.2 - p.1) (encPair encNat encNat) encNat
      fun p => (encPair encNat encNat p).length + 1 :=
  ComputableInSpace.natSub.tidy

theorem natAdd :
    ComputableTidilyInSpace (fun p : ℕ × ℕ => p.1 + p.2) (encPair encNat encNat) encNat
      fun p => (encPair encNat encNat p).length + 1 :=
  of_inO ComputableInO.natAdd.tidy

theorem dispatch {κ : Type*} (l : List κ) (d : κ) (F : κ → α → β)
    (hF : ∀ x, ComputableTidilyInSpace (F x) encIn encB fun a => (encIn a).length) {i : α → ℕ}
    (hi : ComputableTidilyInSpace i encIn encNat fun a => (encIn a).length) :
    ComputableTidilyInSpace (fun a => F (l.getD (i a) d) a) encIn encB
      fun a => (encIn a).length := by
  induction l generalizing i with
  | nil => simpa using hF d
  | cons x l ih =>
    have hz : ComputableTidilyInSpace (fun a => decide (i a = 0)) encIn encBool
        fun a => (encIn a).length := budget_comp_lin natIsZero (.refl _) hi
    have hpred : ComputableTidilyInSpace (fun a => i a - 1) encIn encNat
        fun a => (encIn a).length := budget_comp_lin natPred linear_succ hi
    refine (budget_ite hz (hF x) (ih hpred)).of_enc_eq fun a => ?_
    rcases i a with _ | c <;> simp

/-- One subtraction step of binary division, retained in the tidy namespace. -/
abbrev divStep : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ := ComputableInSpace.divStep

theorem iterate_divStep (d r : ℕ) :
    ∀ k, divStep^[k] (d, 0, r) = (d, min k (r / d), r - d * min k (r / d)) :=
  ComputableInSpace.iterate_divStep d r

theorem iterate_divStep_self (d r : ℕ) : divStep^[r] (d, 0, r) = (d, r / d, r % d) :=
  ComputableInSpace.iterate_divStep_self d r

theorem divStep_inSpace :
    ComputableTidilyInSpace divStep encNat3 encNat3 fun s => (encNat3 s).length + 1 :=
  ComputableInSpace.divStep_inSpace.tidy

theorem natDivMod :
    ComputableTidilyInSpace (fun p : ℕ × ℕ => (p.1 / p.2, p.1 % p.2)) (encPair encNat encNat)
      (encPair encNat encNat) fun p => 16 * ((encPair encNat encNat p).length + 1) :=
  ComputableInSpace.natDivMod.tidy

theorem natDiv :
    ComputableTidilyInSpace (fun p : ℕ × ℕ => p.1 / p.2) (encPair encNat encNat) encNat
      fun p => 16 * ((encPair encNat encNat p).length + 1) :=
  fst' natDivMod

theorem natMod :
    ComputableTidilyInSpace (fun p : ℕ × ℕ => p.1 % p.2) (encPair encNat encNat) encNat
      fun p => 16 * ((encPair encNat encNat p).length + 1) :=
  snd' natDivMod

theorem natMul :
    ComputableTidilyInSpace (fun p : ℕ × ℕ => p.1 * p.2) (encPair encNat encNat) encNat
      fun p => 32 * ((encPair encNat encNat p).length + 1) :=
  ComputableInSpace.natMul.tidy

theorem getD :
    ComputableTidilyInSpace (fun p : List ℕ × ℕ => p.1.getD p.2 0)
      (encPair (encList encNat) encNat) encNat
      fun p => 8 * ((encPair (encList encNat) encNat p).length + 1) :=
  ComputableInSpace.getD.tidy

/-- Fold step for bounded-space list update, retained in the tidy namespace. -/
abbrev setStep : (ℕ × ℕ) × ℕ × List ℕ → ℕ → (ℕ × ℕ) × ℕ × List ℕ := ComputableInSpace.setStep

theorem foldl_setStep (i v : ℕ) (l : List ℕ) (j : ℕ) (acc : List ℕ) :
    l.foldl setStep ((i, v), j, acc) =
      ((i, v), j + l.length, acc ++ l.mapIdx fun k a => if j + k = i then v else a) :=
  ComputableInSpace.foldl_setStep i v l j acc

theorem set_eq_mapIdx (l : List ℕ) (i v : ℕ) :
    l.set i v = l.mapIdx fun k a => if k = i then v else a :=
  ComputableInSpace.set_eq_mapIdx l i v

theorem length_encList_set_le (l : List ℕ) (i v : ℕ) :
    (encList encNat (l.set i v)).length ≤
      (encList encNat l).length + 2 * (encNat v).length + 1 :=
  ComputableInSpace.length_encList_set_le l i v

/-- Encoding of `setStep` states, retained in the tidy namespace. -/
abbrev encSetState : (ℕ × ℕ) × ℕ × List ℕ ↪ List Bool := ComputableInSpace.encSetState

theorem setStep_inSpace :
    ComputableTidilyInSpace (fun q : ((ℕ × ℕ) × ℕ × List ℕ) × ℕ => setStep q.1 q.2)
      (encPair encSetState encNat) encSetState
      fun q => 4 * ((encPair encSetState encNat q).length + 1) :=
  ComputableInSpace.setStep_inSpace.tidy

theorem set :
    ComputableTidilyInSpace (fun p : List ℕ × ℕ × ℕ => p.1.set p.2.1 p.2.2)
      (encPair (encList encNat) (encPair encNat encNat)) (encList encNat)
      fun p => 128 * ((encPair (encList encNat) (encPair encNat encNat) p).length + 1) :=
  ComputableInSpace.set.tidy

section Generic

variable {ε : Type} {enc : ε ↪ List Bool}

theorem iterate_cons (a : ε) (l : List ε) (k : ℕ) :
    (fun q : ε × List ε => (q.1, q.1 :: q.2))^[k] (a, l) = (a, List.replicate k a ++ l) :=
  ComputableInSpace.iterate_cons a l k

theorem replicate [Inhabited ε] :
    ComputableTidilyInSpace (fun p : ℕ × ε => List.replicate p.1 p.2) (encPair encNat enc)
      (encList enc) fun p => 64 * ((p.1 + 1) * ((encPair encNat enc p).length + 1)) :=
  ComputableInSpace.replicate.tidy

theorem length :
    ComputableTidilyInSpace (fun l : List ε => l.length) (encList enc) encNat
      fun l => 8 * ((encList enc l).length + 1) :=
  ComputableInSpace.length.tidy

theorem mapWith {π κ : Type} {encP : π ↪ List Bool} {encK : κ ↪ List Bool} {f : π × ε → κ}
    {Sf : π × ε → ℕ} {par : α → π} {list : α → List ε} {Sp Sl : α → ℕ}
    (hf : ComputableTidilyInSpace f (encPair encP enc) encK Sf)
    (hpar : ComputableTidilyInSpace par encIn encP Sp)
    (hlist : ComputableTidilyInSpace list encIn (encList enc) Sl) :
    ComputableTidilyInSpace (fun x => (list x).map fun a => f (par x, a)) encIn (encList encK)
      fun x => (encIn x).length + Sp x + Sl x + (encP (par x)).length +
        (encList enc (list x)).length +
        (encList encK ((list x).map fun a => f (par x, a))).length +
        listMax (fun a => Sf (par x, a)) (list x) :=
  let ⟨_, hf⟩ := hf
  let ⟨_, hpar⟩ := hpar
  let ⟨_, hlist⟩ := hlist
  ⟨_, ComputableTidilyInO.mapWith hf hpar hlist⟩

end Generic

section BudgetOps

variable {ε : Type} {enc : ε ↪ List Bool}

theorem budget_cons {a : α → ε} {l : α → List ε} (ha : ComputableTidilyInSpace a encIn enc Bs)
    (hl : ComputableTidilyInSpace l encIn (encList enc) Bs) :
    ComputableTidilyInSpace (fun x => a x :: l x) encIn (encList enc) Bs :=
  budget_binop (of_inO (ComputableTidilyInDegree.cons enc).inO_one) (.refl _) ha hl

theorem budget_headD (d : ε) {l : α → List ε}
    (hl : ComputableTidilyInSpace l encIn (encList enc) Bs) :
    ComputableTidilyInSpace (fun x => (l x).headD d) encIn enc Bs :=
  budget_comp_linear (of_inO (.of_linear (Internal.NormalForm.linear
      (ListEncoding.headD (enc := encList enc) d)))) hl

theorem budget_tail {l : α → List ε} (hl : ComputableTidilyInSpace l encIn (encList enc) Bs) :
    ComputableTidilyInSpace (fun x => (l x).tail) encIn (encList enc) Bs :=
  budget_comp_linear (of_inO (.of_linear (Internal.NormalForm.linear
      (ListEncoding.tail (enc₁ := enc))))) hl

theorem budget_isEmpty {l : α → List ε} (hl : ComputableTidilyInSpace l encIn (encList enc) Bs) :
    ComputableTidilyInSpace (fun x => (l x).isEmpty) encIn encBool Bs :=
  budget_comp_linear (of_inO (.of_linear (Internal.NormalForm.linear
      (ListEncoding.isEmpty (enc₁ := enc))))) hl

theorem budget_length {l : α → List ε} (hl : ComputableTidilyInSpace l encIn (encList enc) Bs) :
    ComputableTidilyInSpace (fun x => (l x).length) encIn encNat Bs :=
  budget_comp_lin length (linear_mul 8) hl

end BudgetOps

theorem budget_natSucc {a : α → ℕ} (ha : ComputableTidilyInSpace a encIn encNat Bs) :
    ComputableTidilyInSpace (fun x => a x + 1) encIn encNat Bs :=
  budget_comp_lin natSucc linear_succ ha

theorem budget_natPred {a : α → ℕ} (ha : ComputableTidilyInSpace a encIn encNat Bs) :
    ComputableTidilyInSpace (fun x => a x - 1) encIn encNat Bs :=
  budget_comp_lin natPred linear_succ ha

theorem budget_natIsZero {a : α → ℕ} (ha : ComputableTidilyInSpace a encIn encNat Bs) :
    ComputableTidilyInSpace (fun x => decide (a x = 0)) encIn encBool Bs :=
  budget_comp_lin natIsZero (.refl _) ha

theorem budget_natEq {a b : α → ℕ} (ha : ComputableTidilyInSpace a encIn encNat Bs)
    (hb : ComputableTidilyInSpace b encIn encNat Bs) :
    ComputableTidilyInSpace (fun x => decide (a x = b x)) encIn encBool Bs :=
  budget_binop natEq (.refl _) ha hb

theorem budget_natAdd {a b : α → ℕ} (ha : ComputableTidilyInSpace a encIn encNat Bs)
    (hb : ComputableTidilyInSpace b encIn encNat Bs) :
    ComputableTidilyInSpace (fun x => a x + b x) encIn encNat Bs :=
  budget_binop natAdd linear_succ ha hb

theorem budget_natMul {a b : α → ℕ} (ha : ComputableTidilyInSpace a encIn encNat Bs)
    (hb : ComputableTidilyInSpace b encIn encNat Bs) :
    ComputableTidilyInSpace (fun x => a x * b x) encIn encNat Bs :=
  budget_binop natMul (linear_mul 32) ha hb

theorem budget_natDiv {a b : α → ℕ} (ha : ComputableTidilyInSpace a encIn encNat Bs)
    (hb : ComputableTidilyInSpace b encIn encNat Bs) :
    ComputableTidilyInSpace (fun x => a x / b x) encIn encNat Bs :=
  budget_binop natDiv (linear_mul 16) ha hb

theorem budget_natSub {a b : α → ℕ} (ha : ComputableTidilyInSpace a encIn encNat Bs)
    (hb : ComputableTidilyInSpace b encIn encNat Bs) :
    ComputableTidilyInSpace (fun x => a x - b x) encIn encNat Bs :=
  budget_binop natSub linear_succ hb ha

theorem budget_natMod {a b : α → ℕ} (ha : ComputableTidilyInSpace a encIn encNat Bs)
    (hb : ComputableTidilyInSpace b encIn encNat Bs) :
    ComputableTidilyInSpace (fun x => a x % b x) encIn encNat Bs :=
  budget_binop natMod (linear_mul 16) ha hb

theorem budget_natLt {a b : α → ℕ} (ha : ComputableTidilyInSpace a encIn encNat Bs)
    (hb : ComputableTidilyInSpace b encIn encNat Bs) :
    ComputableTidilyInSpace (fun x => decide (a x < b x)) encIn encBool Bs :=
  budget_binop natLt linear_succ ha hb

theorem budget_natPow {a : α → ℕ} (ha : ComputableTidilyInSpace a encIn encNat Bs)
    (hin : (fun x => (encIn x).length) ≼ Bs) (d : ℕ) :
    ComputableTidilyInSpace (fun x => a x ^ d) encIn encNat Bs := by
  induction d with
  | zero => simpa using budget_const (encB := encNat) 1 hin
  | succ d ih => simpa [pow_succ] using budget_natMul ih ha

theorem budget_finMod {w : ℕ} (hw : 0 < w) {m : α → ℕ}
    (hm : ComputableTidilyInSpace m encIn encNat Bs) (hin : (fun x => (encIn x).length) ≼ Bs) :
    ComputableTidilyInSpace (fun x => (⟨m x % w, Nat.mod_lt _ hw⟩ : Fin w)) encIn
      (Fin.valEmbedding.trans encNat) Bs :=
  (budget_natMod hm (budget_const (encB := encNat) w hin)).of_enc_eq fun _ => rfl

theorem budget_optionSome {a : α → ℕ} (ha : ComputableTidilyInSpace a encIn encNat Bs) :
    ComputableTidilyInSpace (fun x => some (a x)) encIn (encOption encNat) Bs :=
  budget_comp_linear (of_inO (ComputableTidilyInDegree.optionSome (enc₁ := encNat)).inO_one) ha

end ComputableTidilyInSpace

end Turing.MultiTapeTM
