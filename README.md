# Convert Lean 4 `.olean` files to s-expressions

This utility converts compiled Lean 4 modules to the [S-expression](https://en.wikipedia.org/wiki/S-expression) format: for every declaration an `(:entry (:name "...") <type> <body>)` with module-qualified constant names. These can be used for further processing, e.g. to build the dependency graph of a library or for machine-learning purposes.

## Building

```
lake build
```

The tool reads `.olean` files, which can only be loaded by the exact Lean toolchain that produced them, so `lean-toolchain` here must match the project you want to convert (currently `v4.37.0-rc1`).

## Usage

Build the project you want to convert first (or fetch its cache), then run the tool from that project through `lake env`, so that its `.olean` files are on the search path:

```
cd my-project
lake env path/to/lean2sexp/.lake/build/bin/lean2sexp [options] <dir-or-file>...
```

A directory `D` names the modules `D.*` found as `.lean` files below it, so pass the root directory of a library, e.g. `.lake/packages/mathlib/Mathlib` or `src/MyLib`; a file `M.lean` names the top-level module `M`. For Lean's own `Init`, pass (a symlink to) `<toolchain>/src/lean/Init` with that toolchain's `lean` on `PATH`.

```
  -o, --out DIR      output directory (default: sexp)
  -j, --jobs N       worker threads (default: number of cores)
  --refs-only        write (:references ...) lists instead of full expression trees
  --skip-internal    skip declarations with an `_` name component (private, aux);
                     by default they are kept so that no reference dangles
  --force            rewrite outputs that are up to date
```

### Output

One file per module, `<out>/<Module>/<Path>.sexp` (e.g. `sexp/Init/Data/List/Basic.sexp`), with one entry per declaration per line, in declaration order. Names are `<module>.<constant>` as in `(:name "Init.Prelude.Nat.add")`; a private declaration keeps its mangled name, e.g. `Init.Omega._private.Init.Omega.0.foo`.

Each file is written to `<file>.tmp` and renamed into place, and modules whose output is newer than their `.olean*` files are skipped. A killed run can therefore simply be restarted. The up-to-date check does not look at the options: use a different `--out` directory (or `--force`) when switching between `--refs-only` and full output.

The output does not depend on `--jobs` or on which modules are being converted: when the same declaration is present in several modules (Lean allows identical theorems, e.g. realized equation lemmas `foo.eq_1`; 0.2% of Init's names), it is attributed to the alphabetically first module, both for its own entry and for references to it.

### Memory and speed

The whole library is imported once (`importModules` mmaps the `.olean` files). Measured on Lean core `Init`, Mathlib, and riemann-hypothesis + Mathlib (71k modules): the import takes 0.6 s, 16 s and 15 s, and uses 0.4, 1.7 and 2.3 GB of anonymous memory. The rest of the resident memory reported by the OS is file-backed `.olean` pages that the kernel can evict, so the tool works on a small machine; it is CPU-bound and scales with `--jobs` (modules are converted independently).

## Checks

- `test/run.sh` builds a tiny `module`-system project and checks the entries, cross-module references, proof bodies and private declarations in its output.
- `scripts/compare-sexp.py OLD NEW` compares two output trees (in either the old one-file-per-declaration layout or the new one) as multisets of entries; `--modules FILE` strips module prefixes to ignore the attribution of multiply-declared names.

## Background

The utility is fashioned after a similar Agda backend, implemented in the
[`ast-dump` branch of this Agda fork](https://github.com/andrejbauer/agda/tree/ast-dump), see
[`src/full/Agda/Interaction/Highlighting/Sexp`](https://github.com/andrejbauer/agda/tree/ast-dump/src/full/Agda/Interaction/Highlighting/Sexp)
therein.
