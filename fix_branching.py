import re

with open("CslibFrontier/Foundations/Data/BranchingVector.lean", "r") as f:
    content = f.read()

# Add imports
content = content.replace("public import Mathlib.Analysis.SpecialFunctions.Pow.Real", "public import Mathlib.Analysis.SpecialFunctions.Pow.Real\nimport CslibFrontier.Foundations.Data.List.Blocks\nimport Mathlib.Algebra.Order.Monoid.List")

# Fix sum_le_sum arguments
# Old: List.sum_le_sum (steps.filter (· ≤ n)) fun d hd =>
# New: List.sum_le_sum fun d hd =>
content = re.sub(r'List\.sum_le_sum\s+\([^\)]+\)\s+fun', 'List.sum_le_sum fun', content)
content = re.sub(r'List\.sum_le_sum\s+[a-zA-Z0-9_\.]+\s+fun', 'List.sum_le_sum fun', content)
content = re.sub(r'List\.sum_map_mul_left\s+([^\s]+)\s+([^\s]+)', r'List.sum_map_mul_left \1 \2', content)

with open("CslibFrontier/Foundations/Data/BranchingVector.lean", "w") as f:
    f.write(content)
