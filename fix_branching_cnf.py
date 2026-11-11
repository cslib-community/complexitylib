import re

with open("CslibFrontier/Logics/Propositional/CNF/Branching.lean", "r") as f:
    content = f.read()

# Delete private theorems countP_eq_sum_ite and finset_sum_list_sum
content = re.sub(r'private theorem countP_eq_sum_ite.*?(?=public section)', '', content, flags=re.DOTALL)

# Replace usages
# They said: countP_eq_sum_ite -> List.countP_eq_length_filter + List.length_filter_eq_sum
# Let's check where countP_eq_sum_ite was used
content = content.replace("countP_eq_sum_ite", "(by simp only [List.countP_eq_length_filter, List.length_filter_eq_sum])")
content = content.replace("finset_sum_list_sum", "Finset.sum_list_sum_comm")

with open("CslibFrontier/Logics/Propositional/CNF/Branching.lean", "w") as f:
    f.write(content)
