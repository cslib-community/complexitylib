# Complexity-class inclusion tables

The daily **API documentation** workflow publishes these tables at
<https://www.cslib.io/cslib-frontier/class-inclusions/>, in the same Pages upload as the API docs,
the guide and the [source statistics](../stats/README.md). Only runs on `main` deploy.

The page is not committed. Each docs run builds it from that run's doc-gen4 declaration index, so
it always describes the published library and nothing can go stale. Every ✓ and ✗ mark links to
the theorem's API page by declaration name.

`build.py` combines two layers for every ordered pair of classes:

* **The library.** Theorems named `A_subset_B`, `A_ssubset_B`, `A_eq_B` or `A_not_subset_B`
  between classes of a grid (`UNIFORM`, `CIRCUIT`) appear automatically. `EXTRA` adds instances
  of parametric theorems such as `NC_subset_AC 1`. Proved inclusions are closed under chaining,
  and proved non-inclusions propagate outward.
* **The literature.** `LITERATURE` and `CO_CLOSED` record what is known unconditionally. A pair
  they neither prove nor refute is shown as open.

If the library proves something the literature layer calls open or false, the build fails, and so
does that docs run, rather than publishing a contradiction. Fix whichever layer is wrong.

To add a class, add it to a grid with the token used in theorem names, and add its known
relations to `LITERATURE` (and `CO_CLOSED` or `COMPLEMENT`, for uniform classes).

## Building locally

The build needs only Python 3.9+ and a doc-gen4 declaration index. The published one is enough
for a preview:

```sh
curl -fLo /tmp/declaration-data.bmp \
  https://www.cslib.io/cslib-frontier/declarations/declaration-data.bmp
python3 tools/class_inclusions/build.py --index /tmp/declaration-data.bmp
python3 -m unittest discover -s tools/class_inclusions -p 'test_*.py'
```

This writes `tools/class_inclusions/_site/index.html`. Its theorem links are relative to the
documentation root, so they resolve only once the page is published next to the API docs.
