# Convert Lean 4 `.olean` files to s-expressions

This utility converts compiled Lean 4 modules to the [S-expression](https://en.wikipedia.org/wiki/S-expression) format. These can be used for further processing, e.g., to build the dependency graph of a library or for machine-learning purposes.

## Building

```
lake build
```

`.olean` files can only be loaded by the exact toolchain that produced them, so the `lean-toolchain` of `lean2sexp` must match that of the project you want to convert (currently `v4.37.0-rc1`).

## Usage

Build the project you want to convert first (or run `lake exe cache get`). Then run the tool from that project through `lake env`, so that its `.olean` files are on the search path:

```
lake env path/to/lean2sexp/.lake/build/bin/lean2sexp [options] <dir-or-file>...
```

A directory `D` stands for the modules `D.*` below it, so pass the root of a library, e.g. `.lake/packages/mathlib/Mathlib`. The options are:

```
  -o, --out DIR      output directory (default: sexp)
  -j, --jobs N       worker threads (default: all cores; fewer use less memory)
  --refs-only        write (:references ...) lists instead of full expression trees
  --skip-internal    skip private and auxiliary declarations
  --json             write JSON Lines (.jsonl): (:tag a b) becomes ["tag", a, b]
  --force            rewrite outputs that are up to date
```

Each module goes to its own file, e.g. `sexp/Init/Data/List/Basic.sexp`, with one `(:entry ...)` per declaration per line. Every name comes with its module, as in `(:name "Nat.add" "Init.Prelude")`. A line of `--refs-only` output looks like this:

```
(:entry (:name "linter.nightlyRegressionSet" "Mathlib.Init") (:references (:name "Bool" "Init.Prelude") ...) (:abstract (:references ...)))
```

### Format

```
ENTRY ::= (:entry NAME E KIND RANGE?)           E = the declaration's type
NAME  ::= (:name "constant" "module")
KIND  ::= (:theorem E) | (:function E) | (:abstract E)       proof / body / opaque value
        | (:axiom) | (:recursor E) | (:data E NAME*)         recursor: its type; data: type, constructors
        | (:constructor NAME) | (:quot-info (:type|:ctor|:lift|:ind) NAME E)
E     ::= (:references NAME*)                                   with --refs-only: the constants used
        | (:const NAME LEVEL*) | (:apply E E+) | (:lambda E E) | (:pi E E)   binder type, body
        | (:let E E E) | (:var i) | (:literal n|"s") | (:sort LEVEL)       let: type, value, body; var: de Bruijn index
        | (:proj i NAME E) | (:fvar NAME) | (:meta NAME)
        | (:node k E E) | (:ref k)              (:node k S B): (:ref k) in B (and in later nodes) stands for S
RANGE ::= (:range line col end-line end-col)    position in the module's .lean file (lines from 1)
LEVEL ::= (:level (:lzero) | (:lsucc LEVEL) | (:max LEVEL LEVEL) | (:imax LEVEL LEVEL) | (:name "u"))
```

With `--json`, `(:tag a b)` is `["tag", a, b]`.

Use `--refs-only` for dependency graphs: full output contains whole proof terms and is huge (420 GB instead of 11 GB for the riemann-hypothesis formalization).
With `--json` every line is a JSON value, so the output loads with any JSON library.

Internal declarations are kept by default so that no reference dangles.
Modules whose output is up to date are skipped, so a killed run can simply be restarted. Use a fresh `-o` directory (or `--force`) when changing options.

`test/run.sh` and `scripts/compare-sexp.py` check the output.
