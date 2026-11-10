/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Computability/RE.lean`)

public import CslibFrontier.Init
public import Mathlib.Computability.RE

/-!
# Closure properties of computable predicates

Mathlib's `ComputablePred p` states that `p` has a computable Boolean indicator. Mathlib proves
closure under negation (`ComputablePred.not`); this file adds closure under conjunction,
disjunction, implication, composition with computable functions, comparisons of computable
natural-number functions, and bounded quantification. The bounded quantifiers are the computable
analogues of Mathlib's `PrimrecPred.forall_lt` and `PrimrecPred.exists_lt`: a bound computed from
the parameter, over a predicate decidable in the parameter and the bound variable together.
Unbounded existential quantification of a computable predicate gives an r.e. predicate
(`ComputablePred.rePred_exists`), and r.e. predicates are closed under substitution of computable
functions (`REPred.comp`). A predicate is r.e. exactly when it is the domain of a code of
`Nat.Partrec.Code`, evaluated at the encoded argument (`rePred_iff_exists_code`).

The generic form of an incompleteness argument: if `p` is not r.e., then every r.e. predicate that
implies `p` misses a point of `p` (`REPred.exists_not_of_not_rePred`), and every decidable relation
`P a b` ("`b` is a proof of `a`") that is sound for `p` leaves a point of `p` without a proof
(`ComputablePred.exists_forall_not_of_not_rePred`). The variants
`REPred.exists_not_of_not_exists_rePred_iff` and
`ComputablePred.exists_forall_not_of_not_exists_rePred_iff` only assume that no r.e. predicate
agrees with `p` on a domain `D`, and find the point in `D`.

## Main results

* `ComputablePred.and`, `ComputablePred.or`, `ComputablePred.imp`: Boolean closure.
* `ComputablePred.comp`: substitution of a computable function.
* `ComputablePred.nat_le`, `ComputablePred.nat_lt`: comparisons of computable functions.
* `ComputablePred.forall_lt`, `ComputablePred.exists_lt`: bounded quantification.
* `ComputablePred.rePred_exists`: unbounded existential quantification gives an r.e. predicate.
* `REPred.comp`: substitution of a computable function into an r.e. predicate.
* `REPred.exists_not_of_not_rePred`, `REPred.exists_not_of_not_exists_rePred_iff`: an r.e.
  predicate that implies a non-r.e. predicate misses one of its points.
* `ComputablePred.exists_forall_not_of_not_rePred`,
  `ComputablePred.exists_forall_not_of_not_exists_rePred_iff`: a decidable proof relation that is
  sound for a non-r.e. predicate is incomplete.
* `rePred_iff_exists_code`: r.e. predicates are the domains of codes.
-/

public section

namespace ComputablePred

variable {α β : Type*} [Primcodable α] [Primcodable β]

/-- Computable predicates are closed under conjunction. -/
protected theorem and {p q : α → Prop} (hp : ComputablePred p) (hq : ComputablePred q) :
    ComputablePred fun a => p a ∧ q a := by
  obtain ⟨_, hp⟩ := hp
  obtain ⟨_, hq⟩ := hq
  exact Computable.computablePred <| (Primrec.and.to_comp.comp hp hq).of_eq fun a => by simp

/-- Computable predicates are closed under disjunction. -/
protected theorem or {p q : α → Prop} (hp : ComputablePred p) (hq : ComputablePred q) :
    ComputablePred fun a => p a ∨ q a := by
  obtain ⟨_, hp⟩ := hp
  obtain ⟨_, hq⟩ := hq
  exact Computable.computablePred <| (Primrec.or.to_comp.comp hp hq).of_eq fun a => by simp

/-- Computable predicates are closed under implication. -/
protected theorem imp {p q : α → Prop} (hp : ComputablePred p) (hq : ComputablePred q) :
    ComputablePred fun a => p a → q a :=
  (hp.not.or hq).of_eq fun _ => by
    classical
    exact imp_iff_not_or.symm

/-- Substituting a computable function into a computable predicate gives a computable
predicate. -/
protected theorem comp {p : β → Prop} {f : α → β} (hp : ComputablePred p) (hf : Computable f) :
    ComputablePred fun a => p (f a) := by
  obtain ⟨_, hp⟩ := hp
  exact Computable.computablePred (hp.comp hf)

/-- Comparing two computable natural-number functions with `≤` is computable. -/
theorem nat_le {f g : α → ℕ} (hf : Computable f) (hg : Computable g) :
    ComputablePred fun a => f a ≤ g a :=
  (Primrec.nat_le.decide.to_comp.comp hf hg).computablePred

/-- Comparing two computable natural-number functions with `<` is computable. -/
theorem nat_lt {f g : α → ℕ} (hf : Computable f) (hg : Computable g) :
    ComputablePred fun a => f a < g a :=
  (Primrec.nat_lt.decide.to_comp.comp hf hg).computablePred

/-- Bounded universal quantification preserves computability: if `p a i` is computable in
`(a, i)` and the bound `f a` is computable, then `∀ i < f a, p a i` is computable. -/
theorem forall_lt {p : α → ℕ → Prop} (hp : ComputablePred (Function.uncurry p)) {f : α → ℕ}
    (hf : Computable f) : ComputablePred fun a => ∀ i < f a, p a i := by
  obtain ⟨b, hb, hpb⟩ := computable_iff.1 hp
  -- `F (a, n)` folds the indicator `b (a, i)` over `i < n` with `&&`.
  let F : α × ℕ → Bool := fun x =>
    Nat.rec (motive := fun _ => Bool) true (fun i acc => acc && b (x.1, i)) x.2
  have hh : Computable₂ fun (x : α × ℕ) (iacc : ℕ × Bool) => iacc.2 && b (x.1, iacc.1) :=
    (Primrec.and.to_comp.comp (Computable.snd.comp Computable.snd)
      (hb.comp (Computable.pair (Computable.fst.comp Computable.fst)
        (Computable.fst.comp Computable.snd)))).to₂
  have hF : Computable F := Computable.nat_rec Computable.snd (Computable.const true) hh
  have key : ∀ a n, F (a, n) = true ↔ ∀ i < n, p a i := by
    intro a n
    induction n with
    | zero => simp [F]
    | succ n ih =>
      have hpi : p a n ↔ b (a, n) = true := by
        rw [show p a n = Function.uncurry p (a, n) from rfl, hpb]
      change (F (a, n) && b (a, n)) = true ↔ _
      rw [Bool.and_eq_true, ih, ← hpi]
      constructor
      · rintro ⟨h, h'⟩ i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        exacts [h i hi, h']
      · intro h
        exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h n (Nat.lt_succ_self n)⟩
  exact computable_iff.2 ⟨fun a => F (a, f a), hF.comp (Computable.pair Computable.id hf),
    funext fun a => propext (key a (f a)).symm⟩

/-- Bounded existential quantification preserves computability: if `p a i` is computable in
`(a, i)` and the bound `f a` is computable, then `∃ i < f a, p a i` is computable. -/
theorem exists_lt {p : α → ℕ → Prop} (hp : ComputablePred (Function.uncurry p)) {f : α → ℕ}
    (hf : Computable f) : ComputablePred fun a => ∃ i < f a, p a i :=
  ((forall_lt (p := fun a i => ¬p a i) hp.not hf).not).of_eq fun _ => by
    simp only [not_forall, not_not, exists_prop]

/-- Unbounded existential quantification of a computable predicate is r.e.: search for a witness
by `Nat.rfind` over the codes of `β`. -/
theorem rePred_exists {p : α → β → Prop} (hp : ComputablePred (Function.uncurry p)) :
    REPred fun a => ∃ b, p a b := by
  obtain ⟨hdec, hp⟩ := hp
  let _ : ∀ a b, Decidable (p a b) := fun a b => hdec (a, b)
  let f : α → ℕ → Bool := fun a n =>
    ((Encodable.decode (α := β) n).map fun b => decide (p a b)).getD false
  have hp' : Computable fun q : (α × ℕ) × β => decide (p q.1.1 q.2) :=
    hp.comp (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)
  have hf : Computable₂ f :=
    Computable.option_getD (Computable.option_map (Computable.decode.comp Computable.snd)
      hp'.to₂) (Computable.const false)
  let q : α → ℕ →. Bool := fun a n => Part.some (f a n)
  have hq : Partrec fun a => Nat.rfind (q a) := Partrec.rfind hf.partrec₂
  refine hq.dom_re.of_eq fun a => Nat.rfind_dom.trans ⟨fun ⟨n, hn, _⟩ => ?_,
    fun ⟨b, hb⟩ => ⟨Encodable.encode b, ?_, fun _ => trivial⟩⟩
  · have hn' : f a n = true := (Part.mem_some_iff.1 hn).symm
    simp only [f] at hn'
    cases hb : Encodable.decode (α := β) n with
    | none => simp [hb] at hn'
    | some b => exact ⟨b, by simpa [hb] using hn'⟩
  · exact Part.mem_some_iff.2 (by simp [f, Encodable.encodek, hb])

end ComputablePred

/-- Substituting a computable function into an r.e. predicate gives an r.e. predicate. -/
theorem REPred.comp {α β : Type*} [Primcodable α] [Primcodable β] {p : β → Prop}
    (hp : REPred p) {f : α → β} (hf : Computable f) : REPred fun a => p (f a) :=
  Partrec.comp hp hf

/-- **An r.e. predicate that implies a non-r.e. one misses a point, relative to a domain.** If no
r.e. predicate agrees with `p` on `D`, then every r.e. `S` that implies `p` misses some point of `D`
where `p` holds. -/
theorem REPred.exists_not_of_not_exists_rePred_iff {α : Type*} [Primcodable α] {D p S : α → Prop}
    (hp : ¬∃ T : α → Prop, REPred T ∧ ∀ a, D a → (T a ↔ p a)) (hS : REPred S)
    (hsound : ∀ a, S a → p a) : ∃ a, D a ∧ p a ∧ ¬S a := by
  by_contra hne
  exact hp ⟨S, hS, fun a ha => ⟨hsound a, fun h => by_contra fun hs => hne ⟨a, ha, h, hs⟩⟩⟩

/-- **An r.e. predicate that implies a non-r.e. one misses a point.** If `p` is not r.e., every
r.e. `S` that implies `p` misses some point where `p` holds. -/
theorem REPred.exists_not_of_not_rePred {α : Type*} [Primcodable α] {p S : α → Prop}
    (hp : ¬REPred p) (hS : REPred S) (hsound : ∀ a, S a → p a) : ∃ a, p a ∧ ¬S a := by
  obtain ⟨a, -, h⟩ := hS.exists_not_of_not_exists_rePred_iff (D := fun _ => True)
    (fun ⟨_, hT, hTp⟩ => hp (hT.of_eq fun a => hTp a trivial)) hsound
  exact ⟨a, h⟩

namespace ComputablePred

variable {α β : Type*} [Primcodable α] [Primcodable β]

/-- **A sound decidable proof relation for a non-r.e. predicate is incomplete, relative to a
domain.** If no r.e. predicate agrees with `p` on `D`, and `P a b` ("`b` is a proof of `a`") is
decidable and only points of `p` have proofs, then some point of `D` where `p` holds has no
proof. -/
theorem exists_forall_not_of_not_exists_rePred_iff {D p : α → Prop} {P : α → β → Prop}
    (hP : ComputablePred (Function.uncurry P))
    (hp : ¬∃ T : α → Prop, REPred T ∧ ∀ a, D a → (T a ↔ p a)) (hsound : ∀ a b, P a b → p a) :
    ∃ a, D a ∧ p a ∧ ∀ b, ¬P a b := by
  obtain ⟨a, ha, h, hS⟩ := (rePred_exists hP).exists_not_of_not_exists_rePred_iff hp
    fun a ⟨b, hb⟩ => hsound a b hb
  exact ⟨a, ha, h, fun b hb => hS ⟨b, hb⟩⟩

/-- **A sound decidable proof relation for a non-r.e. predicate is incomplete.** If `p` is not
r.e., and `P a b` ("`b` is a proof of `a`") is decidable and only points of `p` have proofs, then
some point where `p` holds has no proof. -/
theorem exists_forall_not_of_not_rePred {p : α → Prop} {P : α → β → Prop}
    (hP : ComputablePred (Function.uncurry P)) (hp : ¬REPred p) (hsound : ∀ a b, P a b → p a) :
    ∃ a, p a ∧ ∀ b, ¬P a b := by
  obtain ⟨a, h, hS⟩ := (rePred_exists hP).exists_not_of_not_rePred hp
    fun a ⟨b, hb⟩ => hsound a b hb
  exact ⟨a, h, fun b hb => hS ⟨b, hb⟩⟩

end ComputablePred

/-- A predicate is r.e. exactly when it is the domain of a code: `p a` holds iff the code `c`
halts on `encode a`. -/
theorem rePred_iff_exists_code {α : Type*} [Primcodable α] {p : α → Prop} :
    REPred p ↔ ∃ c : Nat.Partrec.Code, ∀ a, p a ↔ (c.eval (Encodable.encode a)).Dom := by
  refine ⟨fun hp => ?_, fun ⟨c, hc⟩ => ?_⟩
  · obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hp
    exact ⟨c, fun a => by simp [hc, Encodable.encodek, Part.assert]⟩
  · exact ((Nat.Partrec.Code.eval_part.comp (Computable.const c) Computable.encode).dom_re).of_eq
      fun a => (hc a).symm
