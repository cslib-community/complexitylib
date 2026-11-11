import re

with open("CslibFrontier/Computability/Machines/Turing/MultiTape/Probabilistic/Sequential/CoinTape.lean", "r") as f:
    content = f.read()

# Fix Authors
content = re.sub(r'Authors: Christian Reitwiessner', 'Authors: Christian Reitwiessner, Samuel Schlesinger', content)

# Fix Main results
results = """## Main results

* `Turing.MultiTapePTM.step_withCoin_seq_left`: a running first phase follows its own step.
* `Turing.MultiTapePTM.step_withCoin_seq_right`: the second phase follows its own step.
* `Turing.MultiTapePTM.replay_append`: running a sequential concatenation of coin sequences is equivalent to running them consecutively.
* `Turing.MultiTapePTM.replay_seq_cases`: replaying a sequence of coins on a sequentially composed machine either stays in the first phase or transitions to the second.
* `Turing.MultiTapePTM.output_length_le_replay`: the output tape length is monotonically non-decreasing during a run.
* `Turing.MultiTapePTM.replay_halted`: a halted configuration does not change when further coins are replayed.
* `Turing.MultiTapePTM.completed_replay_mem_support`: a replay that halts belongs to the support of the closed run evaluation.
* `Turing.MultiTapePTM.replay_output_length_le`: bounds the output length of any replay given a bound on the support of the closed run."""
content = re.sub(r'## Main results.*?\*/\n', results + '\n-/\n', content, flags=re.DOTALL)

# Add docstrings
content = content.replace("theorem replay_append", "/-- Running a sequential concatenation of coin sequences is equivalent to running them consecutively. -/\ntheorem replay_append")
content = content.replace("theorem replay_seq_cases", "/-- Replaying a sequence of coins on a sequentially composed machine either stays in the first phase or transitions to the second. -/\ntheorem replay_seq_cases")
content = content.replace("theorem output_length_le_replay", "/-- The output tape length is monotonically non-decreasing during a run. -/\ntheorem output_length_le_replay")
content = content.replace("theorem replay_halted", "/-- A halted configuration does not change when further coins are replayed. -/\ntheorem replay_halted")
content = content.replace("theorem completed_replay_mem_support", "/-- A replay that halts belongs to the support of the closed run evaluation. -/\ntheorem completed_replay_mem_support")
content = content.replace("theorem replay_output_length_le", "/-- Bounds the output length of any replay given a bound on the support of the closed run. -/\ntheorem replay_output_length_le")

# Fix line 140
content = content.replace("rw [show (machine.withCoin bit).step cfg = cfg by simp [MultiTapeMachine.step, h], ih]", "rw [show (machine.withCoin bit).step cfg = cfg by simp only [MultiTapeMachine.step, h], ih]")

# Fix line 184 wrapping
content = content.replace(
    "  have hmono := output_length_le_replay machine extra (machine.runClosedConfigFromCoins coins (machine.initialConfig input))",
    "  have hmono := output_length_le_replay machine extra\n    (machine.runClosedConfigFromCoins coins (machine.initialConfig input))"
)

with open("CslibFrontier/Computability/Machines/Turing/MultiTape/Probabilistic/Sequential/CoinTape.lean", "w") as f:
    f.write(content)
