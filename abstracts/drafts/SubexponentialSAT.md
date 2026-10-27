# Pending catalogue proposal: subexponential SAT

This is staging material for [#1226](https://github.com/cslib-community/complexitylib/issues/1226),
not an entry in the selected catalogue. Samuel selected the title below in
[#587](https://github.com/cslib-community/complexitylib/issues/587#issuecomment-6445129935). The
[integration draft](../ComplexityAbstracts/SubexponentialSATAbstract.lean) now states the four
theorems through [its bridge](../ComplexityAbstracts/SubexponentialSATBridge.lean), consuming the
unconditional native endpoint. Its audit verifies the statement dependency boundary; Lean checks
the proofs. No PDF for these claims is published.

The proposed entry below is for use **after** the source dependencies and endpoint have landed,
the bridge has been validated on that source, and outside review and the required final checks
are complete. The theorem names now exist in this integration preparation, but the live
catalogue and the #1227 note remain unchanged.

```json
{
  "id": "subexponential-sat",
  "title": "OpenAI: the Exponential Time Hypothesis is false",
  "module": "ComplexityAbstracts.SubexponentialSATAbstract",
  "headline_theorems": [
    "ComplexityAbstracts.SubexponentialSATAbstract.exact_count",
    "ComplexityAbstracts.SubexponentialSATAbstract.not_eth",
    "ComplexityAbstracts.SubexponentialSATAbstract.not_seth",
    "ComplexityAbstracts.SubexponentialSATAbstract.satExponent_eq_zero"
  ],
  "summary": "For each fixed clause width, one deterministic native machine exactly counts satisfying assignments in subexponential time and polynomial space. Every fixed-width SAT exponent is zero, and ETH and SETH are false. Native formalization of OpenAI's manuscript, revised 25 October 2026, by the contributors to #1226.",
  "scope": "Explicit CNF semantics, declared-variable counts, unary declared size and binary formula/output encodings; the interpolation-scale exponent n (log log (n + 16))² / sqrt(log(n + 16)) from §§3–6 and Proposition 6.4, with polynomial time overhead and polynomial workspace charged to the original external input length. Includes all fixed widths and sizes, and rejects invalid declared inputs. This does not establish the sharper Theorem 1.1 / Appendix D bound.",
  "foundations": ["ComplexityAbstracts.Encoding"]
}
```

Proposed README selection row, pending integration and review:

| Result | Model and scope |
| --- | --- |
| [OpenAI: the Exponential Time Hypothesis is false](../ComplexityAbstracts/SubexponentialSATAbstract.lean) | One fixed native machine per width, exact declared-variable counts, and interpolation-scale time with polynomial overhead and polynomial space in the original external encoded input length; all SAT exponents zero and ETH/SETH false. §§3–6 and Proposition 6.4, not the sharper Theorem 1.1 / Appendix D bound. |

The endpoint checkpoint discharges the native branch certificate, feasible-branch exactness,
global polynomial branch space and branch polylogarithmic time obligations; the bridge imports
its public theorems, with no supplier assumptions. Before promotion, integrate the pending source
dependencies and endpoint, validate this bridge on the landed source, and obtain outside review
and the required final checks. Then add the entry to `catalogue.json`, move the row into the README
selection (adjusting its relative link), and build and inspect the generated PDFs. Delete this
staging file in that same promotion. Only then can the #1227 note change from
“claimed” to “proved in this library”, linking the new abstract; whether the conditional entry
remains is Samuel's decision.

Source: OpenAI, *The Exponential Time Hypothesis is False*, revised 25 October 2026,
[Proposition 6.4, pp. 43–44](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf).
The draft uses the accepted native join's original-input accounting and declared-range semantics,
including small sizes and width lifting. The bridge imports the public unconditional endpoint,
not the earlier private join, and introduces no conditional replacement headline.
