# Representative algorithm endpoints and their models

These results are clients of the RAM and specification models, not additional execution models. Several sections describe a result through its curated formal abstract, which restated the actual model, encoding, quantifiers and bounds with a checked bridge to the library. The abstracts were retired on 2026-11-08: their links are pinned to revisions that contain them, and the current statement is the library theorem that the bridge applied. This survey inspected the abstracts' source statements; it did not rerun their audits or render their PDFs [cslib-frontier][complexitylib].

The endpoints are grouped into topic pages, listed in the [reading map](index.md#reading-map). Put a new endpoint section on the matching topic page, in topic order.

## Other clients and classification

The source tree also contains native integer arithmetic, multiword circuit evaluation, matrix multiplication, primality/counting, predecessor structures, 3SUM/exact-triangle routines and randomized SAT algorithms. These broaden coverage of the machine library; they should be catalogued through the complete module census without counting each as a new model. In particular, a bounded frontend or a conditional transfer theorem should not be presented as completion of an unresolved fine-grained endpoint. The current `ROADMAP.md` and the theorem statements themselves are better evidence of endpoint disposition than a directory name.

## Tree Evaluation

The [Cook–Mertz endpoint](catalytic-and-tree-evaluation.md) computes the root of an explicitly table-encoded perfect binary tree in native independent workspace `O(log n · log log n)` for positive value length and height. The output is not charged to workspace, and the theorem leaves time existential. The same page distinguishes borrowed-register restoration and fan-in/packed procedure variants.

## Known Limitations

The numeric values on the topic pages are transcriptions of checked source statements, not results of new execution benchmarks. The source-reference audit checks locations and digests; it does not rerun Lean or prove asymptotic summaries. The full Haskell/Lean runtime behavior, allocator, operating system and hardware are outside these idealized RAM models.

[complexitylib]: ../sources.md#complexitylib
