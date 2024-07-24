import «Lean2sexp».Sexp
import Lean
open Nat

open Lean
open Lean.Elab
open Lean.Elab.Command

structure Config : Type where
  srcDir : System.FilePath := "Test"
  outDir : System.FilePath := "sexp" -- the output directory (created if needed)
  refsOnly : Bool := False -- only output references names
  force : Bool := False -- process file even if .sexp is newer than .olean

def parseArgs (conf : Config) (args : List String) : Option Config :=
  match args with
  | [] => .some conf
  | "--srcdir" :: dir :: args => parseArgs {conf with srcDir := dir} args
  | "--outdir" :: dir :: args => parseArgs {conf with outDir := dir} args
  | "--refsOnly" :: args => parseArgs {conf with refsOnly := True} args
  | "--force" :: args => parseArgs {conf with force := True} args
  | _ => .none

def usage : String :=
"Usage: lake exe lean2sexp <options>

  --srcdir ⟨DIR⟩    set the source directory where .olean files are (default: build/lib)
  --outdir ⟨DIR⟩    set the output directory (default: sexp)
  --refsOnly        output only referenced names instead of syntax trees, much faster (default: false)
  --force           process a file even if .sexp is newer than .olean (default: false)
"

unsafe def getConstantsToFullName (nameToModuleId : Lean.Name → Option ModuleIdx) (importedModuleNames : Array Name) (constantName : Name) : Name :=
  match nameToModuleId constantName with
  | some a =>
    importedModuleNames[a.toNat]!.append constantName
  | none => panic! s!"Module ID not found for constant: {constantName}"


unsafe def processModule (conf : Config) (moduleName : Name) : IO Unit := do
  let env ← importModules #[Import.mk moduleName false] {}
  let nameToModuleId := env.getModuleIdxFor?
  let importedModuleNames := env.header.moduleNames
  let constantsToFullName := getConstantsToFullName nameToModuleId importedModuleNames
  IO.println s!"{moduleName} should be same as {env.header.mainModule}"
  match nameToModuleId moduleName with
  | some a =>(
    do
    let mainModuleData := env.header.moduleData[a.toNat]!

    let outFile := System.FilePath.join conf.outDir $ (".".intercalate (moduleName.toString :: ["sexp"]))
    IO.FS.withFile outFile .write (fun fh => Sexp.write fh $ Sexp.fromModuleData constantsToFullName conf.refsOnly moduleName mainModuleData)
  )
  | none => throw (IO.userError s!"Module {moduleName} was not imported into the environment!")

unsafe def recursivelyProcessDirectory (conf : Config) (curName : Name)(dir : System.FilePath): IO Unit := do
  IO.println s!"Searching files in source directory {dir}..."
  let mut entries ← dir.readDir
  for entry in entries do
    if (← entry.path.isDir) then
      let newCurName := Name.str curName entry.fileName
      IO.println s!"Going into directory {newCurName}"
      -- is dir
      recursivelyProcessDirectory conf newCurName entry.path
    else
      -- is regular file
      --IO.println s!"Processing {entry.path}"
      let baseName := (entry.path.withExtension "").components.drop (conf.srcDir.components.length)
      let inFileString := (".".intercalate (baseName ++ ["sexp"]))
      IO.println s!"Processing {inFileString}"
      --match (System.FilePath.fileStem entry.path) with
      --| some fileRootName => (
      --  let newCurName := Name.str curName fileRootName
      --  IO.println s!"Processing {newCurName}"
      --  --(processModule conf newCurName)
      --)
      --| none => panic! s!"The file {entry.path} does not have the expected form."


unsafe def main (args : List String) : IO Unit := do
  match parseArgs ({} : Config) args with
  | .none =>
    IO.println s!"Error: could not parse command-line arguments\n\n{usage}"
  | .some conf => recursivelyProcessDirectory conf (Name.str Name.anonymous (conf.srcDir.toString)) conf.srcDir
