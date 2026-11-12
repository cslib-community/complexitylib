/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Construction.Gadget
import CslibFrontier.Foundations.Logic.Function.UpdateKernel

/-!
# Exact labels for attaching a two-port body

One selected external port shares the chosen old coordinate. The other is a fresh last
free coordinate. Old auxiliary blocks are concatenated in their original order. The
proved kernel identifies exactly the selected pair and retains every other label.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

/-- Retain old free indices by `castSucc`, share external port `t` with old `j`, and put
the other external port last. Left auxiliaries precede the right auxiliary block. -/
@[expose] def attachPortLabel (k a b : ℕ) (j : Fin k) (t : Fin 2) :
    (Fin k ⊕ Fin a) ⊕ (Fin 2 ⊕ Fin b) → Fin (k + 1) ⊕ Fin (a + b) :=
  Sum.elim (Sum.map Fin.castSucc (Fin.castAdd b))
    (Sum.map (fun i => if i = t then j.castSucc else Fin.last k) (Fin.natAdd a))

/-- The actual source-variable kernel is precisely the selected pair. All other free and
auxiliary labels remain distinct, independently of which labels occur in either body. -/
theorem attachPortLabel_kernel (k a b : ℕ) (j : Fin k) (t : Fin 2)
    (u v : (Fin k ⊕ Fin a) ⊕ (Fin 2 ⊕ Fin b)) :
    attachPortLabel k a b j t u = attachPortLabel k a b j t v ↔
      Function.update id (Sum.inl (Sum.inl j)) (Sum.inr (Sum.inl t)) u =
        Function.update id (Sum.inl (Sum.inl j)) (Sum.inr (Sum.inl t)) v := by
  rw [Function.update_id_apply_eq_iff]
  rcases u with (i | i) | (i | i) <;> rcases v with (q | q) | (q | q) <;>
    simp only [attachPortLabel, Sum.elim_inl, Sum.elim_inr, Sum.map_inl, Sum.map_inr,
      Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, false_and, and_false,
      false_or, or_false, Fin.ext_iff, Fin.val_castSucc, Fin.val_last, Fin.val_castAdd,
      Fin.val_natAdd, apply_ite, iff_false]
  all_goals first
    | omega
    | (split_ifs <;> simp_all only [Sum.inl.injEq,
        Fin.ext_iff, Fin.val_castSucc, Fin.val_last, not_false_eq_true, true_and, and_true,
        false_and, and_false, true_iff, iff_false] <;> omega)

end Cslib.Complexity.CSP.OrderedBoundary
