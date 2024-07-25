import Mathlib
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
  toSexp := fun k => .integer ↑k.val

instance: Sexpable Float where
  toSexp := .double

def Sexp.fromName (n : Lean.Name) : Sexp := constr "name" [toSexp n.toString]

instance: Sexpable Lean.Name where
  toSexp := Sexp.fromName

def Sexp.fromLevel (lvl : Lean.Level) : Sexp := constr "level" [fromLvl lvl]
  where
    fromLvl : Lean.Level → Sexp
    | .zero => constr "lzero" []
    | .succ lvl =>  constr "lsucc" [fromLevel lvl]
    | .max lvl1 lvl2 => constr "max" [fromLevel lvl1, fromLevel lvl2]
    | .imax lvl1 lvl2 => constr "imax" [fromLevel lvl1, fromLevel lvl2]
    | .param nm => toSexp nm
    | .mvar mv => toSexp mv.name

instance: Sexpable Lean.Level where
  toSexp := Sexp.fromLevel

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
def repeated (e : Lean.Expr) : Lean.HashSet Lean.Expr :=
  (collect .empty e).fold (fun s e k => if k < 2 then s else s.insert e) .empty
  where collect (seen : Lean.HashMap Lean.Expr Nat) (e : Lean.Expr) : Lean.HashMap Lean.Expr Nat :=
    match seen.find? e with
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
  repeated : Lean.HashSet Lean.Expr -- the expressions that are repeated
  index : Lean.HashMap Lean.Expr Nat := {} -- the index by which we refer to an expression
  nodes : List (Nat × Sexp) := [] -- the nodes

abbrev M := StateM St

def M.run {α : Type} (r : Lean.HashSet Lean.Expr) (act : M α) : α :=
  StateT.run' (s := { repeated := r}) act

partial def M.convert (constantsToFullName : Lean.Name → Lean.Name) (e : Lean.Expr) : M Sexp := do
  let st ← get
  match st.index.find? e with
  | .some k => pure $ constr "ref" [toSexp k]
  | .none =>
    let s ←
      match e with
      | .bvar k => pure $ constr "var" [toSexp k]
      | .fvar fv => pure $ constr "fvar" [toSexp fv.name]
      | .mvar mvarId => pure $ constr "meta" [toSexp mvarId.name]
      | .sort u => pure $ constr "sort" [toSexp u]
      | .const declName us => pure $ constr "const" $ toSexp (constantsToFullName declName) :: us.map toSexp
      | .app _ _ =>
        let lst ← getSpine e
        pure $ constr "apply" lst.reverse
      | .lam _ binderType body _ =>
        let s1 ← convert constantsToFullName binderType
        let s2 ← convert constantsToFullName body
        pure $ constr "lambda" [s1, s2]
      | .forallE _ binderType body _ =>
        let s1 ← convert constantsToFullName binderType
        let s2 ← convert constantsToFullName body
        pure $ constr "pi" [s1, s2]
      | .letE _ type value body _ =>
        let s1 ← convert constantsToFullName type
        let s2 ← convert constantsToFullName value
        let s3 ← convert constantsToFullName body
        pure $ constr "let" [s1, s2, s3]
      | .lit l => pure $ toSexp l
      | .mdata _ expr => convert constantsToFullName expr
      | .proj typeName idx struct =>
        let s ← convert constantsToFullName struct
        pure $ constr "proj" [toSexp typeName, toSexp idx, s]
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
          let s2 ← convert constantsToFullName e2
          pure $ s2 :: ss1
        | e =>
          let s ← convert constantsToFullName e
          pure [s]

partial def Sexp.fromExpr (constantsToFullName : Lean.Name → Lean.Name) (e : Lean.Expr) : Sexp :=
  M.run (repeated e) do
    let s ← M.convert constantsToFullName e
    let st ← get
    pure $ st.nodes.foldl (fun t (k, n) => constr "node" [toSexp k, n, t]) s

-- collect all the names references by an expression
def collectRefs (e : Lean.Expr) : List Lean.Name :=
  let (_, ns) := collect {} {} e
  ns
  where collect (seen : Lean.HashSet Lean.Expr) (ns : List Lean.Name) (e : Lean.Expr)
    : Lean.HashSet Lean.Expr × List Lean.Name :=
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

def Sexp.fromExprRefs (e : Lean.Expr) : Sexp :=
  constr "references" $ (collectRefs e).map toSexp

-- instance: Sexpable Lean.Expr where
--   toSexp := Sexp.fromExpr

instance: Sexpable Lean.QuotKind where
  toSexp := fun k =>
    match k with
  | .type => constr "type" []
  | .ctor => constr "ctor" []
  | .lift => constr "lift" []
  | .ind  => constr "ind" []

def Sexp.constantInfo (constantsToFullName : Lean.Name → Lean.Name) (exprCollect : Lean.Expr → Sexp) (info : Lean.ConstantInfo) : Sexp :=
    constr "entry" [toSexp (constantsToFullName info.name), exprCollect info.type, theDef info]
    where theDef : Lean.ConstantInfo → Sexp := fun info =>
      match info with
      | .axiomInfo _ => constr "axiom" []
      | .defnInfo val => constr "function" [exprCollect val.value]
      | .thmInfo val => constr "theorem" [exprCollect val.value]
      | .opaqueInfo val => constr "abstract" [exprCollect val.value]
      | .quotInfo val => constr "quot-info" [toSexp val.kind, toSexp val.name, exprCollect val.type]
      | .inductInfo val => constr "data" $ exprCollect val.type :: val.ctors.map toSexp
      | .ctorInfo val => constr "constructor" [toSexp val.induct]
      | .recInfo val => constr "recursor" [exprCollect val.type]

def Sexp.fromModuleData (constantsToFullName : Lean.Name → Lean.Name) (refsOnly : Bool) (nm : Lean.Name) (data : Lean.ModuleData) : Sexp :=
  let lst := data.constants.toList.filter keepEntry -- list of constants
  let moduleBody := lst.map ((constantInfo constantsToFullName)$ if refsOnly then fromExprRefs else fromExpr constantsToFullName)
  constr "module" $ constr "module-name" [toSexp nm] :: moduleBody
  where keepEntry (info : Lean.ConstantInfo) : Bool :=
    match info.name with
    | .anonymous => true
    | .str _ _ => ! info.name.isInternal
    | .num _ _ => true


open Lean
open Lean.Elab
open Lean.Elab.Command

unsafe def getConstantsToFullName (nameToModuleId : Lean.Name → Option ModuleIdx) (importedModuleNames : Array Name) (constantName : Name) : Name :=
  match nameToModuleId constantName with
  | some a =>
    importedModuleNames[a.toNat]!.append constantName
  | none => panic! s!"Module ID not found for constant: {constantName}"

unsafe def processModule (moduleName : Name) : IO Sexp := do
  --IO.println s!"Processing module {moduleName}"
  let env ← importModules #[Import.mk moduleName false] {}
  let nameToModuleId := env.getModuleIdxFor?
  let importedModuleNames := env.header.moduleNames
  let constantsToFullName := getConstantsToFullName nameToModuleId importedModuleNames
  --IO.println s!"Modules {env.header.moduleNames}"
  --IO.println s!"Const2ModIdx {env.const2ModIdx.toList.map (fun (k, v) => toString k ++ ": " ++toString v)}"
  let modulesData := env.header.moduleData
  let mainModuleData := modulesData[modulesData.size - 1]!
  let sexpConstruct := (Sexp.fromModuleData constantsToFullName false moduleName mainModuleData)
  --Environment.freeRegions env
  pure sexpConstruct

unsafe def processRegularFile (overwrite :Bool := false) (moduleName : Lean.Name) (outFile : System.FilePath ) : IO Unit := do
  let outMetaData ← outFile.metadata.toBaseIO
  let proceed : Bool :=
    match outMetaData with
    | .error _ => true
    | .ok _ => overwrite

  if proceed then
    IO.println s!"Processing {moduleName}"

    let env ← importModules #[Import.mk moduleName false] {}
    let nameToModuleId := env.getModuleIdxFor?
    let importedModuleNames := env.header.moduleNames
    let constantsToFullName := getConstantsToFullName nameToModuleId importedModuleNames
    let modulesData := env.header.moduleData
    let mainModuleData := modulesData[modulesData.size - 1]!
    let sexpConstruct := (Sexp.fromModuleData constantsToFullName false moduleName mainModuleData)
    IO.FS.withFile outFile .write (fun fh => Sexp.write fh sexpConstruct)

    Environment.freeRegions env
  else
    IO.println s!"Skipping {moduleName}"

def nameToSexpFileName (n : Name) : String :=
  let rec aux : Name → List String
    | Name.anonymous => []
    | Name.str p s => aux p ++ [s]
    | Name.num p n => aux p ++ [toString n]
  let nameParts := aux n
  let joinedName := String.intercalate "_" nameParts
  joinedName ++ ".sexp"

unsafe def recursivelyProcessDirectory (curName : Name)(dir : System.FilePath): IO Unit := do
  IO.println s!"Searching files in source directory {dir}..."
  let mut entries ← dir.readDir
  for entry in entries do
    if (← entry.path.isDir) then
      -- is dir
      let newCurName := Name.str curName entry.fileName
      IO.println s!"Going into directory {newCurName}"
      recursivelyProcessDirectory newCurName entry.path
    else
      -- is regular file
      --IO.println s!"Processing {entry.path}"
      match entry.path.fileStem with
      | some baseName =>
        let moduleName := Name.str curName baseName
        let outFile := System.FilePath.mk ("sexp/" ++(nameToSexpFileName moduleName))
        processRegularFile false moduleName outFile
      | none => IO.println "This should be impossible."

unsafe def main (args : List String) : IO Unit := do
  match args with
  | dir :: [] => recursivelyProcessDirectory (Name.str Name.anonymous dir) dir
  | _ => panic! "Incorrect use of arguments. Input is only the directory."

--#eval main ["Mathlib"]
