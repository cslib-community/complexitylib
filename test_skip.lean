import Mathlib

def skipX₀ {n m : ℕ} (i : Fin (n + m)) : Fin (n + 1 + m) :=
  if h : i.val < n then
    ⟨i.val, by omega⟩
  else
    ⟨i.val + 1, by omega⟩
