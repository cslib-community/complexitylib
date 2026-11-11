import re

with open("CslibFrontier/Computability/Machines/Turing/MultiTape/Probabilistic/Sequential/CoinTape.lean", "r") as f:
    content = f.read()

content = content.replace(
    "/-- Running a sequential concatenation of coin sequences is equivalent to running them consecutively. -/",
    "/-- Running a sequential concatenation of coin sequences is equivalent to\nrunning them consecutively. -/"
)
content = content.replace(
    "/-- Replaying a sequence of coins on a sequentially composed machine either stays in the first phase or transitions to the second. -/",
    "/-- Replaying a sequence of coins on a sequentially composed machine either stays in the\nfirst phase or transitions to the second. -/"
)

with open("CslibFrontier/Computability/Machines/Turing/MultiTape/Probabilistic/Sequential/CoinTape.lean", "w") as f:
    f.write(content)
