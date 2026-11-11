import re

with open("CslibFrontier/Foundations/Data/BranchingVector.lean", "r") as f:
    content = f.read()

# Fix List.sum_map_mul_left
content = content.replace("List.sum_map_mul_left (m : ℝ) (c₀ :: cs) (fun c => r ^ T.measure c)", "List.sum_map_mul_left (c₀ :: cs) (fun c => r ^ T.measure c) (m : ℝ)")

# Fix List.sum_map_flatMap usages.
# Previously it was used as `List.sum_map_flatMap xs f`. But wait, in the old file it was `list_sum_flatMap (T.children u) fun c => T.leaves c`
# It was used after `List.map_flatMap` at :439, 456? The review said:
# list_sum_flatMap (:159, used after List.map_flatMap at :439, 456) with List.sum_map_flatMap
# So I should change `rw [List.map_flatMap, List.sum_map_flatMap]` to `rw [List.sum_map_flatMap]`.
# Let's just find `rw [List.map_flatMap, List.sum_map_flatMap]`
content = content.replace("rw [List.map_flatMap, List.sum_map_flatMap]", "rw [List.sum_map_flatMap]")

with open("CslibFrontier/Foundations/Data/BranchingVector.lean", "w") as f:
    f.write(content)
