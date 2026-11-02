/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Ary.Iterative

/-!
# Correctness of the iterative fan-in-d Cook–Mertz controller

A call evaluates the existing recursive procedure while preserving its caller's continuation
stack. Node access is supplied by a path lookup agreeing with a subtree. In particular, using
an existing `Ary.Tree` as the lookup yields a terminating root call with exactly `Ary.procWith`'s
registers. No separate tree or evaluation semantics is introduced.

## Main results

* `Cslib.TreeEval.Ary.Iter.exists_runFrom_call`: a subtree call implements `Ary.procWith`.
* `Cslib.TreeEval.Ary.Iter.exists_runFrom_root`: the complete root call returns and halts.

## References

* [O. Goldreich, *On the Cook–Mertz Tree Evaluation procedure*][Goldreich2024TreeEval],
  Algorithm 1. The loop follows the signed calls of the existing fan-in-d algebra.

This proves pure control-loop correspondence, not a native implicit-input space theorem.
The gate extension is supplied; its implementation and same-input subroutine composition are
separate from the control-loop correspondence.
-/

public section

namespace Cslib.TreeEval.Ary.Iter

variable {K : Type*} [Field K] {d b r : ℕ}

private def Reaches {α : Type*} (next : α → α) (a z : α) : Prop := ∃ n, next^[n] a = z

private theorem Reaches.single {α : Type*} {next : α → α} {a z : α}
    (h : next a = z) : Reaches next a z := ⟨1, h⟩

private theorem Reaches.trans {α : Type*} {next : α → α} {a b z : α}
    (hab : Reaches next a b) (hbz : Reaches next b z) : Reaches next a z := by
  obtain ⟨m, hm⟩ := hab
  obtain ⟨n, hn⟩ := hbz
  refine ⟨m + n, ?_⟩
  rw [Nat.add_comm, Function.iterate_add_apply, hm, hn]

private theorem foldl_take_succ {α β : Type*} (l : List α) (f : β → α → β) (a : β)
    {j : ℕ} (hj : j < l.length) :
    (l.take (j + 1)).foldl f a = f ((l.take j).foldl f a) l[j] := by
  rw [List.take_succ_eq_append_getElem hj, List.foldl_append]
  rfl

variable {K : Type*} [Field K] {d b r : ℕ}

/-- A complete iterative masking round agrees with the supplied-extension algebraic round.
The child-call hypothesis permits arbitrary global registers and unchanged suspended frames.
Only control data, not register banks, are retained in the stack. -/
private theorem exists_runFrom_round (hd : 0 < d)
    (e : (Fin b → Bool) → Fin r → K)
    (E : Gate d b → (Fin d → Fin r → K) → Fin r → K)
    (us : List Kˣ) (read : List (Fin d) → Tree.Node d b)
    (p : Fin d → K → Fin (d + 1) → Ary.State K d r → Ary.State K d r)
    (f : Gate d b) (st : List (Frame K d)) (c : K) (t : Fin (d + 1)) (i : ℕ)
    (hgate : read (path st) = .gate f)
    (hp : ∀ (fr : Frame K d) (c' : K) (t' : Fin (d + 1)) (S : Ary.State K d r),
      ∃ n, runFrom hd e E us read ⟨S, fr :: st, .call c' t'⟩ n =
        ⟨p fr.child c' t' S, fr :: st, .ret⟩)
    (S : Ary.State K d r) :
    ∃ n, runFrom hd e E us read (beginRound hd us i c t S st) n =
      if i + 1 < us.length then
        beginRound hd us (i + 1) c t (gateRoundWith E p f c t (unitAt us i) S) st
      else ⟨gateRoundWith E p f c t (unitAt us i) S, st, .ret⟩ := by
  let next := step hd e E us read
  let u := unitAt us i
  let F (j : ℕ) := ((List.finRange d).take j).foldl
    (fun S j => p j 1 (reg t j) (scale (reg t j) (u : K) S)) S
  have hF0 : F 0 = S := rfl
  have hF (j : ℕ) (hj : j < d) :
      F (j + 1) = p ⟨j, hj⟩ 1 (reg t ⟨j, hj⟩)
        (scale (reg t ⟨j, hj⟩) (u : K) (F j)) := by
    dsimp only [F]
    rw [foldl_take_succ _ _ _ (by simpa using hj), List.getElem_finRange]
    simp only [Fin.cast_mk]
  have hforward : ∀ j (hj : j < d), Reaches next (beginRound hd us i c t S st)
      ⟨F (j + 1), ⟨i, ⟨j, hj⟩, false, c, t⟩ :: st, .ret⟩ := by
    intro j
    induction j with
    | zero =>
      intro hj
      rw [hF 0 hj, hF0]
      exact hp ⟨i, ⟨0, hj⟩, false, c, t⟩ 1 (reg t ⟨0, hj⟩)
        (scale (reg t ⟨0, hj⟩) (u : K) S)
    | succ j ih =>
      intro hj
      have hj' : j < d := by omega
      have hnext : next ⟨F (j + 1), ⟨i, ⟨j, hj'⟩, false, c, t⟩ :: st, .ret⟩ =
          ⟨scale (reg t ⟨j + 1, hj⟩) (u : K) (F (j + 1)),
            ⟨i, ⟨j + 1, hj⟩, false, c, t⟩ :: st, .call 1 (reg t ⟨j + 1, hj⟩)⟩ := by
        simp [next, step, hj, u]
      rw [show j.succ + 1 = (j + 1) + 1 by omega, hF (j + 1) hj]
      exact (ih hj').trans (Reaches.single hnext) |>.trans
        (hp ⟨i, ⟨j + 1, hj⟩, false, c, t⟩ 1 (reg t ⟨j + 1, hj⟩)
          (scale (reg t ⟨j + 1, hj⟩) (u : K) (F (j + 1))))
  let G := gateUpdateWith E f c t (F d)
  let B (j : ℕ) := ((List.finRange d).take j).foldl
    (fun S j => scale (reg t j) ((u⁻¹ : Kˣ) : K) (p j (-1) (reg t j) S)) G
  have hB0 : B 0 = G := rfl
  have hB (j : ℕ) (hj : j < d) :
      B (j + 1) = scale (reg t ⟨j, hj⟩) ((u⁻¹ : Kˣ) : K)
        (p ⟨j, hj⟩ (-1) (reg t ⟨j, hj⟩) (B j)) := by
    dsimp only [B]
    rw [foldl_take_succ _ _ _ (by simpa using hj), List.getElem_finRange]
    simp only [Fin.cast_mk]
  let undoStart : Cfg K d r :=
    ⟨G, ⟨i, ⟨0, hd⟩, true, c, t⟩ :: st, .call (-1) (reg t ⟨0, hd⟩)⟩
  have hlast : d - 1 < d := by omega
  have hlastEq : d - 1 + 1 = d := by omega
  have hupdate : Reaches next (beginRound hd us i c t S st) undoStart := by
    have hret := hforward (d - 1) hlast
    rw [hlastEq] at hret
    apply hret.trans
    apply Reaches.single
    simp [next, step, show ¬(d - 1 + 1 < d) by omega, updateAt, hgate, undoStart, G]
  have hbackward : ∀ j (hj : j < d), Reaches next undoStart
      ⟨p ⟨j, hj⟩ (-1) (reg t ⟨j, hj⟩) (B j),
        ⟨i, ⟨j, hj⟩, true, c, t⟩ :: st, .ret⟩ := by
    intro j
    induction j with
    | zero =>
      intro hj
      rw [hB0]
      exact hp ⟨i, ⟨0, hj⟩, true, c, t⟩ (-1) (reg t ⟨0, hj⟩) G
    | succ j ih =>
      intro hj
      have hj' : j < d := by omega
      have hnext : next
          ⟨p ⟨j, hj'⟩ (-1) (reg t ⟨j, hj'⟩) (B j),
            ⟨i, ⟨j, hj'⟩, true, c, t⟩ :: st, .ret⟩ =
          ⟨B (j + 1), ⟨i, ⟨j + 1, hj⟩, true, c, t⟩ :: st,
            .call (-1) (reg t ⟨j + 1, hj⟩)⟩ := by
        simp [next, step, hj, hB j hj', u]
      exact (ih hj').trans (Reaches.single hnext) |>.trans
        (hp ⟨i, ⟨j + 1, hj⟩, true, c, t⟩ (-1) (reg t ⟨j + 1, hj⟩) (B (j + 1)))
  have hBdone : B d = gateRoundWith E p f c t u S := by
    have htake : (List.finRange d).take d = List.finRange d :=
      List.take_of_length_le (by simp)
    simp only [B, G, F, gateRoundWith, htake]
  have hscaleLast :
      scale (reg t ⟨d - 1, hlast⟩) ((u⁻¹ : Kˣ) : K)
        (p ⟨d - 1, hlast⟩ (-1) (reg t ⟨d - 1, hlast⟩) (B (d - 1))) = B d := by
    rw [← hB (d - 1) hlast, hlastEq]
  have hexit : next
      ⟨p ⟨d - 1, hlast⟩ (-1) (reg t ⟨d - 1, hlast⟩) (B (d - 1)),
        ⟨i, ⟨d - 1, hlast⟩, true, c, t⟩ :: st, .ret⟩ =
      if i + 1 < us.length then beginRound hd us (i + 1) c t (B d) st
      else ⟨B d, st, .ret⟩ := by
    simp [next, step, show ¬(d - 1 + 1 < d) by omega, ← hscaleLast, u]
  have hrun := hupdate.trans (hbackward (d - 1) hlast) |>.trans (Reaches.single hexit)
  rw [hBdone] at hrun
  exact hrun


private theorem unitAt_getElem (us : List Kˣ) (i : ℕ) (hi : i < us.length) :
    unitAt us i = us[i] := by
  simp [unitAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

private theorem exists_runFrom_gate (hd : 0 < d)
    (e : (Fin b → Bool) → Fin r → K)
    (E : Gate d b → (Fin d → Fin r → K) → Fin r → K)
    (us : List Kˣ) (read : List (Fin d) → Tree.Node d b)
    (p : Fin d → K → Fin (d + 1) → Ary.State K d r → Ary.State K d r)
    (f : Gate d b) (st : List (Frame K d))
    (hgate : read (path st) = .gate f)
    (hp : ∀ (fr : Frame K d) (c : K) (t : Fin (d + 1)) (S : Ary.State K d r),
      ∃ N, runFrom hd e E us read ⟨S, fr :: st, .call c t⟩ N =
        ⟨p fr.child c t S, fr :: st, .ret⟩)
    (S : Ary.State K d r) (c : K) (t : Fin (d + 1)) :
    ∃ N, runFrom hd e E us read ⟨S, st, .call c t⟩ N =
      ⟨us.foldl (fun S u => gateRoundWith E p f c t u S) S, st, .ret⟩ := by
  cases hus : us with
  | nil =>
    refine ⟨1, ?_⟩
    simp only [runFrom_one, List.foldl_nil]
    exact step_call_gate_nil hd e E read S st c t f hgate
  | cons u tail =>
    let F := fun S u => gateRoundWith E p f c t u S
    have hprefix : ∀ j, j ≤ us.length → ∃ N,
        runFrom hd e E us read ⟨S, st, .call c t⟩ N =
          if j < us.length then beginRound hd us j c t ((us.take j).foldl F S) st
          else ⟨(us.take j).foldl F S, st, .ret⟩ := by
      intro j
      induction j with
      | zero =>
        intro _
        refine ⟨1, ?_⟩
        have hlen : 0 < us.length := by simp [hus]
        simp only [hlen, ↓reduceIte, List.take_zero, List.foldl_nil, runFrom_one]
        rw [hus]
        exact step_call_gate_cons hd e E u tail read S st c t f hgate
      | succ j ih =>
        intro hj
        have hjlt : j < us.length := by omega
        obtain ⟨N, hN⟩ := ih (by omega)
        rw [ite_eq_left hjlt] at hN
        obtain ⟨M, hM⟩ := exists_runFrom_round hd e E us read p f st c t j
          hgate hp ((us.take j).foldl F S)
        refine ⟨N + M, ?_⟩
        rw [runFrom_add, hN, hM]
        have hfold : (us.take (j + 1)).foldl F S =
            gateRoundWith E p f c t (unitAt us j) ((us.take j).foldl F S) := by
          rw [foldl_take_succ us F S hjlt, unitAt_getElem us j hjlt]
        rw [hfold]
    obtain ⟨N, hN⟩ := hprefix us.length le_rfl
    refine ⟨N, ?_⟩
    simpa only [Nat.lt_irrefl, ↓reduceIte, List.take_length, F, hus] using hN

/-- A call on any subtree implemented by the supplied lookup runs the existing recursive
procedure and returns to the same continuation stack, from arbitrary global register contents. -/
theorem exists_runFrom_call (hd : 0 < d)
    (e : (Fin b → Bool) → Fin r → K)
    (E : Gate d b → (Fin d → Fin r → K) → Fin r → K)
    (us : List Kˣ) (read : List (Fin d) → Tree.Node d b)
    {h : ℕ} (T : Tree d b h) (st : List (Frame K d))
    (hread : ∀ P, read (path st ++ P) = T.nodeAt P)
    (S : Ary.State K d r) (c : K) (t : Fin (d + 1)) :
    ∃ N, runFrom hd e E us read ⟨S, st, .call c t⟩ N =
      ⟨procWith e E us T c t S, st, .ret⟩ := by
  induction T generalizing st S c t with
  | leaf v =>
    refine ⟨1, ?_⟩
    have hv : read (path st) = .leaf v := by
      simpa only [List.append_nil, Tree.nodeAt_leaf_nil] using hread []
    rw [runFrom_one, step_call_leaf hd e E us read S st c t v hv]
    rfl
  | node f ch ih =>
    have hgate : read (path st) = .gate f := by
      simpa only [List.append_nil, Tree.nodeAt_node_nil] using hread []
    have hp (fr : Frame K d) (c' : K) (t' : Fin (d + 1)) (S' : Ary.State K d r) :
        ∃ N, runFrom hd e E us read ⟨S', fr :: st, .call c' t'⟩ N =
          ⟨procWith e E us (ch fr.child) c' t' S', fr :: st, .ret⟩ := by
      apply ih fr.child (fr :: st) _ S' c' t'
      intro P
      rw [path_cons, List.append_assoc, List.singleton_append]
      exact hread (fr.child :: P)
    exact exists_runFrom_gate hd e E us read (fun j => procWith e E us (ch j))
      f st hgate hp S c t

/-- The complete root call terminates with exactly the recursive procedure's registers. -/
theorem exists_runFrom_root (hd : 0 < d)
    (e : (Fin b → Bool) → Fin r → K)
    (E : Gate d b → (Fin d → Fin r → K) → Fin r → K)
    (us : List Kˣ) {h : ℕ} (T : Tree d b h)
    (S : Ary.State K d r) (c : K) (t : Fin (d + 1)) :
    ∃ N, runFrom hd e E us T.nodeAt (initialCfg S c t) N =
      ⟨procWith e E us T c t S, [], .ret⟩ := by
  exact exists_runFrom_call hd e E us T.nodeAt T [] (fun _ => rfl) S c t

end Cslib.TreeEval.Ary.Iter
