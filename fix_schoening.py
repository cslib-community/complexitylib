import re

with open("CslibFrontier/Computability/Complexity/FineGrained/SchoeningMachine.lean", "r") as f:
    content = f.read()

# Delete one_sub_mul_le_pow
content = re.sub(r'private theorem one_sub_mul_le_pow.*?(?=private theorem half_le_bernoulli_factor)', '', content, flags=re.DOTALL)

# Replace usage
content = content.replace("have hbern := one_sub_mul_le_pow hδ1 (3 * n)", "have hbern := one_add_mul_le_pow (a := -δ) (by linarith) (3 * n)")

with open("CslibFrontier/Computability/Complexity/FineGrained/SchoeningMachine.lean", "w") as f:
    f.write(content)
