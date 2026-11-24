#!/usr/bin/env bash
# Builds the tiny module-system project in test/modtest, converts it with lean2sexp and checks
# cross-module references, definition bodies, proofs and private declarations in the output.
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT=$PWD
lake build 2>&1 | tail -1
cd test/modtest
lake build 2>&1 | tail -1
rm -rf out out-skip
lake env "$ROOT/.lake/build/bin/lean2sexp" -j 2 -o out ModTest.lean ModTest
lake env "$ROOT/.lake/build/bin/lean2sexp" -j 2 -o out-skip --skip-internal ModTest.lean ModTest

fail=0
check() { # description, file, regex
  if grep -q -E -- "$3" "$2"; then echo "ok   $1"; else echo "FAIL $1"; fail=1; fi
}
checkno() {
  if grep -q -E -- "$3" "$2"; then echo "FAIL $1"; fail=1; else echo "ok   $1"; fi
}
A=out/ModTest/A.sexp B=out/ModTest/B.sexp
[ -f out/ModTest.sexp ] && [ ! -s out/ModTest.sexp ] && echo "ok   module without declarations gives an empty file" || { echo "FAIL empty module"; fail=1; }
check "def body is present" $A '^\(:entry \(:name "ModTest.A.double"\) .* \(:function \(:'
check "private theorem is present, module-qualified" $A '^\(:entry \(:name "ModTest.A._private.ModTest.A.0.double_eq_aux"\) '
# a non-`public` declaration of a `module` is name-mangled like a `private` one
check "non-public theorem has its proof" $A '^\(:entry \(:name "ModTest.A._private.ModTest.A.0.double_eq_internal"\) .* \(:theorem \(:'
check "proof references the private theorem" $A '"ModTest.A._private.ModTest.A.0.double_eq_internal"\) .*"ModTest.A._private.ModTest.A.0.double_eq_aux"'
check "public theorem has its proof (not an axiom)" $A '^\(:entry \(:name "ModTest.A.double_eq"\) .* \(:theorem \(:'
check "public proof references the non-public theorem" $A '^\(:entry \(:name "ModTest.A.double_eq"\) .*"ModTest.A._private.ModTest.A.0.double_eq_internal"'
check "cross-module reference in a proof" $B '^\(:entry \(:name "ModTest.B.double_double"\) .*"ModTest.A.double_eq"'
check "cross-module reference in a def body" $B '^\(:entry \(:name "ModTest.B.quad"\) .* \(:function .*"ModTest.A.double"'
checkno "--skip-internal drops private declarations" out-skip/ModTest/A.sexp '^\(:entry \(:name "[^"]*_private'
check "--skip-internal keeps public ones" out-skip/ModTest/A.sexp '"ModTest.A.double_eq"'
# every ModTest.* name that is referenced is also declared (no dangling edges)
python3 - <<'EOF' || fail=1
import re, pathlib
decl, refs = set(), set()
for p in pathlib.Path("out").rglob("*.sexp"):
    for line in p.read_text().splitlines():
        names = re.findall(r'\(:name "((?:[^"\\]|\\.)*)"\)', line)
        decl.add(names[0])
        refs.update(n for n in names[1:] if n.startswith("ModTest."))
dangling = refs - decl
print(("ok   " if not dangling else "FAIL ") + f"no dangling ModTest references ({len(refs)} refs, {len(decl)} decls)", *sorted(dangling))
raise SystemExit(1 if dangling else 0)
EOF
[ $fail = 0 ] && echo "ALL PASSED" || { echo "SOME CHECKS FAILED"; exit 1; }
