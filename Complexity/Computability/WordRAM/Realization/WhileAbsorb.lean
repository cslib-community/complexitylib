/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Realization.Absorb
public import Complexity.Computability.WordRAM.Realization.While

/-!
# While loops with semantic guards and absorbed work

`boundedWhile` accepts any decidable guard, so a source states its guard in its own terms:
`0 < r`, `a ≠ 0`, `i < n`. `Realizes.whileBounded` certifies the loop whose guard is a native
comparison of the encoded words. The congruence lemmas below move a loop, its domain and its
charge between pointwise equivalent guards and between environments at which the loop's
guard and body agree, so a certificate for the native guard transfers to the source's guard.
The `realize` tactic does this transfer itself.

`whileWork_le` bounds the local work of a loop whose body costs at most `K` by
`cutoff * (K + 1)`; with a logarithmic cutoff this gives a sift its logarithmic local work through
`Realizes.consequence`. When every body begins with a memory query, that query pays the
iteration's control unit (`whileWork_zero_le`), and `Realizes.while₀` is the while rule with local
work `0`, the shape `realize` composes.

## Main results

* `boundedWhile_congr`, `whileSafe_imp`, `whileSafe_congr`, `whileWork_congr`: congruence in
  the guard, the body and the environment.
* `whileWork_le`: the local work is at most `cutoff * (K + 1)`.
* `whileWork_zero_le`: a loop whose body begins with a query pays its control from memory.
* `Realizes.while₀`: the native while rule with absorbed local work.
-/

public section

namespace Cslib.WordRAM.Realization

open Cslib.DataStructure

variable {δ δ' σ : Type}

/-! ### Congruence -/

section Congr

variable (guard : δ → σ → Prop) [∀ d a, Decidable (guard d a)]
  (guard' : δ' → σ → Prop) [∀ d a, Decidable (guard' d a)]
  {body : δ × σ → Memory.Prog σ} {body' : δ' × σ → Memory.Prog σ} {d : δ} {d' : δ'}

/-- Loops whose guards and bodies agree at their environments are equal, whatever the guards'
decidability instances. -/
theorem boundedWhile_congr (hguard : ∀ a, guard d a ↔ guard' d' a)
    (hbody : ∀ a, body (d, a) = body' (d', a)) (n : ℕ) (a : σ) :
    boundedWhile guard body d n a = boundedWhile guard' body' d' n a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    by_cases hg : guard d a
    · simp only [boundedWhile, hg, (hguard a).mp hg, ↓reduceIte, hbody, ih]
    · simp only [boundedWhile, hg, mt (hguard a).mpr hg, ↓reduceIte]

/-- The reached-state domain transfers along agreeing guards and bodies and a weaker body
domain. The body domains are compared only where the guard holds, as only there is a body run. -/
theorem whileSafe_imp {safe : ℕ → δ × σ → Memory.State → Prop}
    {safe' : ℕ → δ' × σ → Memory.State → Prop} {w : ℕ}
    (hguard : ∀ a, guard d a ↔ guard' d' a) (hbody : ∀ a, body (d, a) = body' (d', a))
    (hsafe : ∀ a s, guard d a → safe w (d, a) s → safe' w (d', a) s) {n : ℕ} {a : σ}
    {s : Memory.State} (h : whileSafe guard body safe w d n a s) :
    whileSafe guard' body' safe' w d' n a s := by
  induction n generalizing a s with
  | zero => exact fun hg => h ((hguard a).mpr hg)
  | succ n ih =>
    by_cases hg : guard d a
    · simp only [whileSafe, hg, ↓reduceIte] at h
      simp only [whileSafe, (hguard a).mp hg, ↓reduceIte, ← hbody]
      exact ⟨hsafe a s hg h.1, ih h.2⟩
    · simp only [whileSafe, mt (hguard a).mpr hg, ↓reduceIte]

/-- The reached-state domain is invariant under agreeing guards, bodies and body domains. -/
theorem whileSafe_congr {safe : ℕ → δ × σ → Memory.State → Prop}
    {safe' : ℕ → δ' × σ → Memory.State → Prop} {w : ℕ}
    (hguard : ∀ a, guard d a ↔ guard' d' a) (hbody : ∀ a, body (d, a) = body' (d', a))
    (hsafe : ∀ a s, guard d a → (safe w (d, a) s ↔ safe' w (d', a) s)) (n : ℕ) (a : σ)
    (s : Memory.State) :
    whileSafe guard body safe w d n a s ↔ whileSafe guard' body' safe' w d' n a s :=
  ⟨whileSafe_imp guard guard' hguard hbody fun a s hg => (hsafe a s hg).mp,
    whileSafe_imp guard' guard (fun a => (hguard a).symm) (fun a => (hbody a).symm)
      fun a s hg => (hsafe a s ((hguard a).mpr hg)).mpr⟩

/-- The local work is invariant under agreeing guards, bodies and body charges. -/
theorem whileWork_congr {work : δ × σ → Memory.State → ℕ} {work' : δ' × σ → Memory.State → ℕ}
    (hguard : ∀ a, guard d a ↔ guard' d' a) (hbody : ∀ a, body (d, a) = body' (d', a))
    (hwork : ∀ a s, work (d, a) s = work' (d', a) s) (n : ℕ) (a : σ) (s : Memory.State) :
    whileWork guard body work d n a s = whileWork guard' body' work' d' n a s := by
  induction n generalizing a s with
  | zero => rfl
  | succ n ih =>
    by_cases hg : guard d a
    · simp only [whileWork, hg, (hguard a).mp hg, ↓reduceIte, hwork, ← hbody, ih]
    · simp only [whileWork, hg, mt (hguard a).mpr hg, ↓reduceIte]

end Congr

/-! ### Work envelopes -/

section Work

variable (guard : δ → σ → Prop) [∀ d a, Decidable (guard d a)] (body : δ × σ → Memory.Prog σ)

/-- With body work at most `K`, a loop with cutoff `n` has local work at most `n * (K + 1)`. -/
theorem whileWork_le {work : δ × σ → Memory.State → ℕ} {K : ℕ} (hK : ∀ x s, work x s ≤ K)
    (d : δ) (n : ℕ) (a : σ) (s : Memory.State) :
    whileWork guard body work d n a s ≤ n * (K + 1) := by
  induction n generalizing a s with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    by_cases hg : guard d a
    · have h₁ := hK (d, a) s
      have h₂ := ih ((Memory.spec 0).clientResult s (body (d, a)))
        ((Memory.spec 0).clientState s (body (d, a)))
      simp only [whileWork, hg, ↓reduceIte, Nat.succ_mul]
      omega
    · simp only [whileWork, hg, ↓reduceIte]
      exact Nat.zero_le _

/-- When every body issues a query, the loop's control work is at most its memory charge. -/
theorem whileWork_zero_le (hquery : ∀ x s, 1 ≤ memoryCost (body x) s) (d : δ) (n : ℕ) (a : σ)
    (s : Memory.State) :
    whileWork guard body (fun _ _ => 0) d n a s ≤ memoryCost (boundedWhile guard body d n a) s := by
  induction n generalizing a s with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    by_cases hg : guard d a
    · have h := while_charge_succ guard body (fun _ _ => 0) d n a s hg
      have h₁ := hquery (d, a) s
      have h₂ := ih ((Memory.spec 0).clientResult s (body (d, a)))
        ((Memory.spec 0).clientState s (body (d, a)))
      have h₃ : whileWork guard body (fun _ _ => 0) d (n + 1) a s =
          whileWork guard body (fun _ _ => 0) d n ((Memory.spec 0).clientResult s (body (d, a)))
            ((Memory.spec 0).clientState s (body (d, a))) + 1 := by
        simp only [whileWork, hg, ↓reduceIte, Nat.zero_add]
      omega
    · simp only [whileWork, hg, ↓reduceIte]
      exact Nat.zero_le _

end Work

/-! ### The absorbed rule -/

namespace Realizes

variable {B : Basis} {k l : ℕ}

/-- A while loop whose body begins with a query has local work `0`: each executed iteration's
control unit is paid by that query's memory charge. The guard is the native comparison `cond`
of the encoded environment and state; the cutoff is a ghost bound, never computed. -/
theorem while₀ (input : δ ↪ (Fin k → ℕ)) (output : σ ↪ (Fin l → ℕ)) (cond : Cond (k + l))
    (cutoff : δ × σ → ℕ) {body : δ × σ → Memory.Prog σ}
    {safe : ℕ → (δ × σ) → Memory.State → Prop}
    (h : Realizes B body (appendWords input output) output safe (fun _ _ => 0))
    (hquery : ∀ x s, 1 ≤ memoryCost (body x) s) :
    Realizes B (fun (d, a) => boundedWhile
      (fun d a => test cond ((appendWords input output) (d, a))) body d (cutoff (d, a)) a)
      (appendWords input output) output
      (fun w (d, a) s => whileSafe
        (fun d a => test cond ((appendWords input output) (d, a))) body safe w d
        (cutoff (d, a)) a s)
      (fun _ _ => 0) :=
  (whileBounded input output cond cutoff h).mono_mul 1 fun (d, a) s => by
    have := whileWork_zero_le (fun d a => test cond ((appendWords input output) (d, a))) body
      hquery d (cutoff (d, a)) a s
    dsimp only
    omega

end Realizes

end Cslib.WordRAM.Realization
