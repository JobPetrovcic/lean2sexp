#!/usr/bin/env python3
"""Regression check: compare two lean2sexp output trees entry by entry.

Accepts both layouts: the original one file per declaration (<dir>/<id>.sexp) and
the per-module one (<dir>/<Module>/<Path>.sexp, one entry per line). Entries are
compared as multisets of (name, s-expression text), so neither file names nor
ordering matter.

usage: compare-sexp.py [--modules FILE] OLD_DIR NEW_DIR
exit status 0 iff the two trees contain exactly the same entries.

With --modules FILE (one module name per line), the module prefix is stripped from
every (:name "...") before comparing. A constant that is declared identically in
several modules (realized equation lemmas such as `foo.eq_1`) is attributed to the
first module in the import order of whatever was imported, which differs between a
per-module and a whole-library import; this option checks that everything else is
the same.
"""
import collections
import pathlib
import re
import sys

NAME = re.compile(r'^\(:entry \(:name "((?:[^"\\]|\\.)*)"\)')
ANY_NAME = re.compile(r'\(:name "((?:[^"\\]|\\.)*)"\)')


def strip_modules(modules):
    """Returns a function replacing every module-qualified name by the bare constant name."""
    mods = set(modules)

    def bare(m):
        n = m.group(1)
        parts = n.split(".")
        for k in range(len(parts) - 1, 0, -1):  # longest module prefix wins
            if ".".join(parts[:k]) in mods:
                return f'(:name "{".".join(parts[k:])}")'
        return m.group(0)

    return lambda line: ANY_NAME.sub(bare, line)


def entries(root, normalize):
    out = collections.Counter()
    for path in sorted(pathlib.Path(root).rglob("*.sexp")):
        with open(path, encoding="utf-8") as f:
            for line in f:
                line = line.rstrip("\n")
                if not line:
                    continue
                line = normalize(line)
                m = NAME.match(line)
                if not m:
                    sys.exit(f"{path}: line does not start with (:entry (:name ...)): {line[:80]}")
                out[(m.group(1), line)] += 1
    return out


def main():
    args = sys.argv[1:]
    normalize = lambda line: line
    if args[:1] == ["--modules"]:
        with open(args[1]) as f:
            normalize = strip_modules([l.strip() for l in f if l.strip()])
        args = args[2:]
    if len(args) != 2:
        sys.exit(__doc__)
    old, new = entries(args[0], normalize), entries(args[1], normalize)
    print(f"old: {sum(old.values())} entries, {len({n for n, _ in old})} distinct names")
    print(f"new: {sum(new.values())} entries, {len({n for n, _ in new})} distinct names")
    only_old, only_new = old - new, new - old
    if not only_old and not only_new:
        print("IDENTICAL")
        return 0
    names_old = collections.Counter(n for (n, _), k in only_old.items() for _ in range(k))
    names_new = collections.Counter(n for (n, _), k in only_new.items() for _ in range(k))
    changed = sorted(set(names_old) & set(names_new))
    print(f"{sum(only_old.values())} entries only in old, {sum(only_new.values())} only in new")
    print(f"  {len(changed)} names present in both with different s-expressions")
    print(f"  {len(set(names_old) - set(names_new))} names only in old, "
          f"{len(set(names_new) - set(names_old))} names only in new")
    for label, names in (("only in old", set(names_old) - set(names_new)),
                         ("only in new", set(names_new) - set(names_old)),
                         ("changed", changed)):
        for n in sorted(names)[:10]:
            print(f"    {label}: {n}")
    return 1


if __name__ == "__main__":
    sys.exit(main())
