import re

with open("manual/programs-crypto-and-probability/programs-and-realization.md", "r") as f:
    content = f.read()

# Replace the sentence
old_sentence = r"when a tidy closed body preserves a state invariant and keeps every work-tape head inside `\[0, M\]` across one round, `seq prep \(repeatUntilBlank body\)` stays within `max M₀ M \+ 1` work-tape cells across arbitrarily many rounds, independent of the round count"
new_sentence = r"when a tidy closed `RunsWords` body preserves a state invariant and keeps every work-tape head inside `window B = [-B, B]`, where `B = max t₁ (max t t₂)`, `seq prep (seq (repeatUntilBlank body) lastM)` stays within workspace `k * (2 * max t₁ (max t t₂) + 1)` across arbitrarily many rounds, independent of the round count"
content = re.sub(old_sentence, new_sentence, content)

with open("manual/programs-crypto-and-probability/programs-and-realization.md", "w") as f:
    f.write(content)
