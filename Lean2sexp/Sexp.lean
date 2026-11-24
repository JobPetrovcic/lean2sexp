import Lean

inductive Sexp : Type
| atom : String → Sexp
| string : String → Sexp
| integer : Int → Sexp
| double : Float → Sexp
| cons : List Sexp → Sexp
deriving Inhabited

partial def Sexp.toString : Sexp → String
  | .atom s => s
  | .string s => s.quote
  | .integer k => ToString.toString k
  | .double x => ToString.toString x
  | .cons lst => "(" ++ (" ".intercalate $ lst.map toString) ++ ")"

partial def Sexp.write (fh : IO.FS.Handle) : Sexp → IO Unit
  | .atom s => fh.putStr s
  | .string s => fh.putStr s.quote
  | .integer k => fh.putStr $ ToString.toString k
  | .double x => fh.putStr $ ToString.toString x
  | .cons lst =>
      do
        fh.putStr "("
        writeList lst
        fh.putStr ")"
  where
    writeList (lst : List Sexp) : IO Unit :=
    match lst with
    | [] => return
    | [s] => write fh s
    | s :: ss =>
      do
        write fh s
        fh.putStr " "
        writeList ss

/-- Writes the same tree as JSON: a list `(:tag a b ...)` becomes `["tag", a, b, ...]`
(the only atoms are such `:tag` keywords). -/
partial def Sexp.writeJson (fh : IO.FS.Handle) : Sexp → IO Unit
  | .atom s => fh.putStr ("\"" ++ Lean.Json.escape (s.dropWhile (· == ':')).toString ++ "\"")
  | .string s => fh.putStr ("\"" ++ Lean.Json.escape s ++ "\"")
  | .integer k => fh.putStr $ ToString.toString k
  | .double x => fh.putStr $ ToString.toString x
  | .cons lst => do
      fh.putStr "["
      let mut first := true
      for s in lst do
        unless first do fh.putStr ","
        first := false
        writeJson fh s
      fh.putStr "]"

instance: ToString Sexp where
  toString := Sexp.toString

def constr (head : String) (lst : List Sexp) : Sexp :=
  .cons ((.atom (":" ++ head)) :: lst)

class Sexpable (α : Type) : Type where
  toSexp : α → Sexp

def toSexp {α : Type} [s : Sexpable α] (x : α): Sexp := s.toSexp x

instance: Sexpable String where
  toSexp := .string

instance: Sexpable Int where
  toSexp := .integer

instance: Sexpable Nat where
  toSexp := fun n => .integer ↑n

instance: Sexpable UInt64 where
  toSexp := fun k => .integer ↑k.toNat

instance: Sexpable Float where
  toSexp := .double

/-- `(:name "<constant>" "<module>")`: the constant's name and the module that declares it. -/
def Sexp.fromName (moduleOf : Lean.Name → Lean.Name) (n : Lean.Name) : Sexp :=
  constr "name" [toSexp n.toString, toSexp (moduleOf n).toString]

def Sexp.fromNameBound (n : Lean.Name) : Sexp := constr "name" [toSexp (n).toString]

--instance: Sexpable Lean.Name where
--  toSexp := Sexp.fromName

def Sexp.fromLevel (moduleOf : Lean.Name → Lean.Name) (lvl : Lean.Level) : Sexp := constr "level" [fromLvl lvl]
  where
    fromLvl : Lean.Level → Sexp
    | .zero => constr "lzero" []
    | .succ lvl =>  constr "lsucc" [fromLevel moduleOf lvl]
    | .max lvl1 lvl2 => constr "max" [fromLevel moduleOf lvl1, fromLevel moduleOf lvl2]
    | .imax lvl1 lvl2 => constr "imax" [fromLevel moduleOf lvl1, fromLevel moduleOf lvl2]
    | .param nm => Sexp.fromNameBound nm
    | .mvar mv => Sexp.fromName moduleOf mv.name

--instance: Sexpable Lean.Level where
--  toSexp := Sexp.fromLevel

instance: Sexpable Lean.BinderInfo where
  toSexp := fun info =>
    match info with
    | .default => constr "default" []
    | .implicit => constr "implicit" []
    | .strictImplicit => constr "strict-implicit" []
    | .instImplicit => constr "inst-implicit" []

instance: Sexpable Lean.Literal where
  toSexp := fun lit =>
    match lit with
    | .natVal val => constr "literal" [toSexp val]
    | .strVal val => constr "literal" [toSexp val]

-- subexpressions that repeat
def repeated (e : Lean.Expr) : Std.HashSet Lean.Expr :=
  (collect {} e).fold (fun s e k => if k < 2 then s else s.insert e) {}
  where collect (seen : Std.HashMap Lean.Expr Nat) (e : Lean.Expr) : Std.HashMap Lean.Expr Nat :=
    match seen.get? e with
    | .some k =>
      -- seen before, no need to descend into subexpressions (this avoids exponential blowup)
      seen.insert e (k + 1)
    | .none =>
      match e with
      | .bvar _ => seen
      | .fvar _ => seen
      | .mvar _ => seen
      | .sort _ => seen
      | .const _ _ => seen
      | .lit _ => seen
      | .app e1 e2 =>
        let seen := seen.insert e 1
        collect (collect seen e1) e2
      | .lam _ binderType body _ =>
        let seen := seen.insert e 1
        collect (collect seen binderType) body
      | .forallE _ binderType body _ =>
        let seen := seen.insert e 1
        collect (collect seen binderType) body
      | .letE _ type value body _ =>
        let seen := seen.insert e 1
        collect (collect (collect seen type) value) body
      | .mdata _ expr => collect seen expr
      | .proj _ _ struct => collect seen struct

-- auxiliary function, the workhorse
structure St where
  repeated : Std.HashSet Lean.Expr -- the expressions that are repeated
  index : Std.HashMap Lean.Expr Nat := {} -- the index by which we refer to an expression
  nodes : List (Nat × Sexp) := [] -- the nodes

abbrev M := StateM St

def M.run {α : Type} (r : Std.HashSet Lean.Expr) (act : M α) : α :=
  StateT.run' (s := { repeated := r}) act

partial def M.convert (moduleOf : Lean.Name → Lean.Name) (e : Lean.Expr) : M Sexp := do
  let st ← get
  match st.index.get? e with
  | .some k => pure $ constr "ref" [toSexp k]
  | .none =>
    let s ←
      match e with
      | .bvar k => pure $ constr "var" [toSexp k]
      | .fvar fv => pure $ constr "fvar" [Sexp.fromName moduleOf fv.name]
      | .mvar mvarId => pure $ constr "meta" [Sexp.fromName moduleOf mvarId.name]
      | .sort u => pure $ constr "sort" [Sexp.fromLevel moduleOf u]
      | .const declName us => pure $ constr "const" $ (Sexp.fromName moduleOf declName) :: us.map (Sexp.fromLevel moduleOf)
      | .app _ _ =>
        let lst ← getSpine e
        pure $ constr "apply" lst.reverse
      | .lam _ binderType body _ =>
        let s1 ← convert moduleOf binderType
        let s2 ← convert moduleOf body
        pure $ constr "lambda" [s1, s2]
      | .forallE _ binderType body _ =>
        let s1 ← convert moduleOf binderType
        let s2 ← convert moduleOf body
        pure $ constr "pi" [s1, s2]
      | .letE _ type value body _ =>
        let s1 ← convert moduleOf type
        let s2 ← convert moduleOf value
        let s3 ← convert moduleOf body
        pure $ constr "let" [s1, s2, s3]
      | .lit l => pure $ toSexp l
      | .mdata _ expr => convert moduleOf expr
      | .proj typeName idx struct =>
        let s ← convert moduleOf struct
        pure $ constr "proj" [toSexp idx, Sexp.fromName moduleOf typeName, s]
    if (← get).repeated.contains e then
      let st ← get
      let r := st.nodes.length
      set ({st with index := st.index.insert e r, nodes := (r, s) :: st.nodes}) ;
    pure $ s
    where
      getSpine (e : Lean.Expr) : M (List Sexp) := do
        match e with
        | .app e1 e2 =>
          let ss1 ← getSpine e1
          let s2 ← convert moduleOf e2
          pure $ s2 :: ss1
        | e =>
          let s ← convert moduleOf e
          pure [s]

partial def Sexp.fromExpr (moduleOf : Lean.Name → Lean.Name) (e : Lean.Expr) : Sexp :=
  M.run (repeated e) do
    let s ← M.convert moduleOf e
    let st ← get
    pure $ st.nodes.foldl (fun t (k, n) => constr "node" [toSexp k, n, t]) s

-- collect all the names references by an expression
def collectRefs (moduleOf : Lean.Name → Lean.Name) (e : Lean.Expr) : List Lean.Name :=
  let (_, ns) := collect {} {} e
  ns
  where collect (seen : Std.HashSet Lean.Expr) (ns : List Lean.Name) (e : Lean.Expr)
    : Std.HashSet Lean.Expr × List Lean.Name :=
    if seen.contains e then
      (seen, ns)
    else
      let seen := seen.insert e
      match e with
      | .bvar _ => (seen, ns)
      | .fvar _ => (seen, ns) -- should never get here (exposed bound variable)
      | .mvar _ => (seen, ns)
      | .sort _ => (seen, ns)
      | .const declName _ => (seen, declName :: ns)
      | .lit _ => (seen, ns)
      | .app e1 e2 =>
        let (seen, ns) := collect seen ns e1
        collect seen ns e2
      | .lam _ binderType body _ =>
        let (seen, ns) := collect seen ns binderType
        collect seen ns body
      | .forallE _ binderType body _ =>
        let (seen, ns) := collect seen ns binderType
        collect seen ns body
      | .letE _ type value body _ =>
        let (seen, ns) := collect seen ns type
        let (seen, ns) := collect seen ns value
        collect seen ns body
      | .mdata _ expr => collect seen ns expr
      | .proj _ _ struct => collect seen ns struct

def Sexp.fromExprRefs (moduleOf : Lean.Name → Lean.Name) (e : Lean.Expr) : Sexp :=
  constr "references" $ (collectRefs moduleOf e).map (Sexp.fromName moduleOf)

-- instance: Sexpable Lean.Expr where
--   toSexp := Sexp.fromExpr

instance: Sexpable Lean.QuotKind where
  toSexp := fun k =>
    match k with
  | .type => constr "type" []
  | .ctor => constr "ctor" []
  | .lift => constr "lift" []
  | .ind  => constr "ind" []

def Sexp.constantInfo (moduleOf : Lean.Name → Lean.Name) (exprCollect : Lean.Expr → Sexp) (info : Lean.ConstantInfo) : Sexp :=
    constr "entry" [(Sexp.fromName moduleOf info.name), exprCollect info.type, theDef info]
    where theDef : Lean.ConstantInfo → Sexp := fun info =>
      match info with
      | .axiomInfo _ => constr "axiom" []
      | .defnInfo val => constr "function" [exprCollect val.value]
      | .thmInfo val => constr "theorem" [exprCollect val.value]
      | .opaqueInfo val => constr "abstract" [exprCollect val.value]
      | .quotInfo val => constr "quot-info" [toSexp val.kind, Sexp.fromName moduleOf val.name, exprCollect val.type]
      | .inductInfo val => constr "data" $ exprCollect val.type :: val.ctors.map (Sexp.fromName moduleOf)
      | .ctorInfo val => constr "constructor" [Sexp.fromName moduleOf val.induct]
      | .recInfo val => constr "recursor" [exprCollect val.type]

open Lean

/-- Maps every constant of the environment to the module that declares it, from the modules'
own constant lists. Lean allows the same theorem to be declared in several modules (realized
equation lemmas such as `foo.eq_1`, about 0.2% of names); `env.getModuleIdxFor?` then returns
the first in import order, which changes with the set of imported modules. We take the smallest
module name instead, so that the qualified names depend only on the library, not on which
modules are converted in a given run or in which order. -/
def constantModules (env : Environment) : Std.HashMap Name Name := Id.run do
  let mut m : Std.HashMap Name Name := {}
  for h : i in [0:env.header.moduleData.size] do
    let mod := env.header.moduleNames[i]!
    for c in env.header.moduleData[i].constNames do
      m := m.alter c fun
        | some mod' => some (if Name.lt mod mod' then mod else mod')
        | none => some mod
  return m

def getConstantModule (constantModules : Std.HashMap Name Name) (constantName : Name) : Name :=
  match constantModules[constantName]? with
  | some mod => mod
  | none => panic! s!"Module not found for constant: {constantName}"

def isAlnum (c : Char) : Bool :=
  c.isAlpha || c.isDigit || c == '_' || c == '-'

def cleanString (s : String) : String :=
  s.foldl (fun acc c => if isAlnum c then acc.push c else acc) ""

/-! ## Driver

One `importModules` of all requested modules (their `.olean*` files are mmapped, not copied)
gives both every module's complete constant list (`env.header.moduleData`) and the
constant → module map that gives every name its module (`constantModules`).
Modules are then converted independently on `--jobs` worker threads. Each module goes to
`<out>/<Module>/<Path>.sexp`, one `(:entry ...)` per line, written to a `.tmp` file and
renamed into place, so a killed run never leaves a complete-looking partial file and can
be resumed: modules whose output is newer than their `.olean*` files are skipped. -/

structure Config where
  srcs : Array System.FilePath := #[]
  outDir : System.FilePath := "sexp"
  /-- Worker threads; `0` means the number of hardware threads. -/
  jobs : Nat := 0
  refsOnly : Bool := false
  skipInternal : Bool := false
  json : Bool := false
  force : Bool := false

def usage : String := "usage: lean2sexp [options] <dir-or-file>...

Converts compiled Lean modules to s-expressions, one file per module:
module Init.Data.List.Basic goes to <out>/Init/Data/List/Basic.sexp,
one (:entry ...) per declaration per line.
A directory D names the modules D.* found as .lean files below it (so pass the
root of a library, e.g. `.lake/packages/mathlib/Mathlib`); a file M.lean names
the top-level module M. The .olean files must be on the search path, so run
the tool through `lake env` from the project that built them.

  -o, --out DIR      output directory (default: sexp)
  -j, --jobs N       worker threads (default: number of cores)
  --refs-only        write (:references ...) lists instead of full expression trees
  --skip-internal    skip declarations with an `_` name component (private, aux);
                     by default they are kept so that no reference dangles
  --json             write JSON Lines (.jsonl): (:tag a b) becomes [\"tag\",a,b]
  --force            rewrite outputs that are up to date
  -h, --help         show this help

Outputs that are newer than the module's .olean* files are skipped, so a run can
be interrupted and resumed. The up-to-date check does not look at the options,
so use a different output directory (or --force) when changing them."

def parseArgs : List String → Config → Except String Config
  | [], o => .ok o
  | "-o" :: d :: rest, o
  | "--out" :: d :: rest, o => parseArgs rest { o with outDir := d }
  | "-j" :: n :: rest, o
  | "--jobs" :: n :: rest, o =>
    match n.toNat? with
    | some k => if k == 0 then .error "--jobs must be positive" else parseArgs rest { o with jobs := k }
    | none => .error s!"--jobs: expected a number, got '{n}'"
  | "--refs-only" :: rest, o => parseArgs rest { o with refsOnly := true }
  | "--skip-internal" :: rest, o => parseArgs rest { o with skipInternal := true }
  | "--json" :: rest, o => parseArgs rest { o with json := true }
  | "--force" :: rest, o => parseArgs rest { o with force := true }
  | arg :: rest, o =>
    if arg.startsWith "-" then .error s!"unknown option '{arg}'"
    else parseArgs rest { o with srcs := o.srcs.push arg }

/-- Module names of the `.lean` files under `dir`, prefixed with `pre`. -/
partial def findModules (pre : Name) (dir : System.FilePath) : IO (Array Name) := do
  let mut mods := #[]
  for entry in (← dir.readDir) do
    if (← entry.path.isDir) then
      mods := mods ++ (← findModules (.str pre entry.fileName) entry.path)
    else if entry.path.extension == some "lean" then
      if let some stem := entry.path.fileStem then
        mods := mods.push (.str pre stem)
  return mods

/-- The modules named by a command-line argument: directory `D` holds the modules `D.*`
(as in the original tool), file `M.lean` is the top-level module `M`. -/
def modulesOf (src : System.FilePath) : IO (Array Name) := do
  let s := src.toString
  let src : System.FilePath := if s.length > 1 && s.endsWith "/" then ⟨(s.dropEnd 1).toString⟩ else src
  if ← src.isDir then
    let some root := src.fileName | throw <| IO.userError s!"{src}: cannot derive a module name"
    findModules (.str .anonymous root) src
  else if src.extension == some "lean" then
    let some stem := src.fileStem | throw <| IO.userError s!"{src}: cannot derive a module name"
    return #[.str .anonymous stem]
  else
    throw <| IO.userError s!"{src}: expected a directory or a .lean file"

/-- Whether `out` is newer than every existing part (`.olean`, `.olean.server`, `.olean.private`)
of the module's compiled data. -/
def upToDate (out olean : System.FilePath) : IO Bool := do
  let .ok outMd ← out.metadata.toBaseIO | return false
  for level in [OLeanLevel.exported, .server, .private] do
    if let .ok md ← (level.adjustFileName olean).metadata.toBaseIO then
      if md.modified > outMd.modified then return false
  return true

/-- The filter the tool applied before `--skip-internal` became optional: drop names with a
component starting with `_` (private, `_auxLemma`, ...) unless the name ends in a number. -/
def keepEntry (info : ConstantInfo) : Bool :=
  match info.name with
  | .anonymous => true
  | .str _ _ => ! info.name.isInternal
  | .num _ _ => true

/-- Converts the module with index `idx` in `env` and writes it to `out`. Returns the number
of entries written. -/
def writeModule (env : Environment) (modOf : Std.HashMap Name Name) (opts : Config) (idx : Nat)
    (out : System.FilePath) : IO Nat := do
  let data := env.header.moduleData[idx]!
  let fullName := getConstantModule modOf
  let exprConv := if opts.refsOnly then Sexp.fromExprRefs fullName else Sexp.fromExpr fullName
  if let some dir := out.parent then IO.FS.createDirAll dir
  let tmp := out.addExtension "tmp"
  let n ← IO.FS.withFile tmp .write fun fh => do
    let mut n := 0
    for info in data.constants do
      if opts.skipInternal && !keepEntry info then continue
      let e := Sexp.constantInfo fullName exprConv info
      if opts.json then e.writeJson fh else e.write fh
      fh.putStr "\n"
      n := n + 1
    return n
  IO.FS.rename tmp out
  return n

/-- Runs `work i` for every `i < n` on `jobs` dedicated threads, each taking the next index
from a shared counter. Results are returned in index order. -/
def parallelFor {α : Type} (jobs n : Nat) (work : Nat → IO α) : IO (Array (Except IO.Error α)) := do
  let next ← IO.mkRef 0
  let worker : IO (Array (Nat × Except IO.Error α)) := do
    let mut acc := #[]
    repeat
      let i ← next.modifyGet fun i => (i, i + 1)
      if i ≥ n then break
      acc := acc.push (i, ← (work i).toBaseIO)
    return acc
  let tasks ← (List.range jobs).mapM fun _ => IO.asTask worker .dedicated
  let mut results := Array.replicate n (.error <| IO.userError "not run")
  for t in tasks do
    for (i, r) in ← IO.ofExcept (← IO.wait t) do
      results := results.set! i r
  return results

unsafe def main (args : List String) : IO UInt32 := do
  if args.isEmpty || args.contains "-h" || args.contains "--help" then
    IO.println usage
    return (if args.isEmpty then 1 else 0)
  let opts ← match parseArgs args {} with
    | .ok o => pure o
    | .error e => IO.eprintln s!"lean2sexp: {e}\n\n{usage}"; return 1
  let jobs := if opts.jobs > 0 then opts.jobs else max 1 (System.Platform.Internal.getHardwareConcurrency ()).toNat
  -- find the core library and everything on LEAN_PATH (e.g. when run via `lake env`)
  initSearchPath (← findSysroot)
  let mut mods : Array Name := #[]
  for src in opts.srcs do
    mods := mods ++ (← modulesOf src)
  mods := mods.qsort (·.toString < ·.toString) |>.toList.eraseDups.toArray
  -- modules without compiled data (not built yet) are skipped, not fatal
  let mut built : Array Name := #[]
  let mut work : Array (Name × System.FilePath) := #[]
  for mod in mods do
    -- `findOLean` throws when no search path entry has the module's root at all
    let olean? ← try
        let olean ← findOLean mod
        pure (if (← olean.pathExists) then some olean else none)
      catch _ => pure none
    let some olean := olean? | IO.eprintln s!"warning: {mod}: no .olean, skipping"; continue
    built := built.push mod
    let out := modToFilePath opts.outDir mod (if opts.json then "jsonl" else "sexp")
    if opts.force || !(← upToDate out olean) then
      work := work.push (mod, out)
  IO.println s!"{built.size} modules, {built.size - work.size} up to date, {work.size} to convert on {jobs} threads"
  if work.isEmpty then return 0
  let t0 ← IO.monoMsNow
  -- All built modules are imported, not just the ones to convert, so that `constantModules`
  -- sees the same declarations in every run. `leakEnv`: the environment lives for the whole run
  -- and is shared read-only by all workers; marking it persistent avoids atomic reference
  -- counting on every lookup.
  let env ← importModules (built.map fun mod => { module := mod, importAll := true }) {} (leakEnv := true)
  IO.println s!"imported {env.header.moduleNames.size} modules in {(← IO.monoMsNow) - t0} ms"
  let t1 ← IO.monoMsNow
  let modOf ← Runtime.markPersistent (constantModules env)
  IO.println s!"indexed {modOf.size} constants in {(← IO.monoMsNow) - t1} ms"
  let done ← IO.mkRef 0
  let results ← parallelFor jobs work.size fun i => do
    let (mod, out) := work[i]!
    let some idx := env.getModuleIdx? mod | throw <| IO.userError s!"{mod}: not in the imported environment"
    let n ← writeModule env modOf opts idx.toNat out
    let k ← done.modifyGet fun k => (k + 1, k + 1)
    IO.println s!"[{k}/{work.size}] {mod}: {n} entries"
    return n
  let mut failures := 0
  let mut entries := 0
  for h : i in [0:results.size] do
    match results[i] with
    | .ok n => entries := entries + n
    | .error e =>
      failures := failures + 1
      IO.eprintln s!"error: {work[i]!.1}: {e}"
  IO.println s!"wrote {entries} entries for {work.size - failures} modules in {(← IO.monoMsNow) - t0} ms{if failures > 0 then s!", {failures} FAILED" else ""}"
  return (if failures > 0 then 1 else 0)
