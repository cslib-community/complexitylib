import sys

with open("CslibFrontier/Foundations/LinearAlgebra/Matrix/KroneckerRank.lean", "r") as f:
    lines = f.readlines()

new_lines = []
skip = False
for i, line in enumerate(lines):
    if line.startswith("  have hS_rank : S.rank = Fintype.card (Fin A.rank) := hS_li.rank_matrix"):
        skip = True
        new_lines.append("  exact IsUnit.ne_zero (Matrix.isUnit_iff_isUnit_det.mp (Matrix.linearIndependent_row_iff_isUnit.mp hS_li))\n")
    elif skip and line.startswith("  exact zero_ne_one hdet1"):
        skip = False
    elif not skip:
        new_lines.append(line)

with open("CslibFrontier/Foundations/LinearAlgebra/Matrix/KroneckerRank.lean", "w") as f:
    f.writelines(new_lines)
