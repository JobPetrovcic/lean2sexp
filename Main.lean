import «Lean2sexp».Sexp
import Lean
import Lean.Environment
import Lean.Util

open Lean
unsafe def finalizeImportHacked (s : ImportState) (imports : Array Import) (opts : Options) (trustLevel : UInt32 := 0)
    (leakEnv := false) : IO (HashMap Name Name) := do
  let numConsts := s.moduleData.foldl (init := 0) fun numConsts mod =>
    numConsts + mod.constants.size + mod.extraConstNames.size
  let mut constantMapModule : HashMap Name Name := mkHashMap (capacity := numConsts)
  for h:modIdx in [0:s.moduleData.size] do
    let modName := s.moduleNames[modIdx]!
    let mod := s.moduleData[modIdx]'h.upper
    for cname in mod.constNames, cinfo in mod.constants do
      constantMapModule := constantMapModule.insertIfNew cname modName |>.1
  pure constantMapModule

unsafe def importModulesHacked (imports : Array Import) (opts : Options) (trustLevel : UInt32 := 0)
    (leakEnv := false) : IO (HashMap Name Name) := do
  for imp in imports do
    if imp.module matches .anonymous then
      throw <| IO.userError "import failed, trying to import module with anonymous name"
  withImporting do
    let (_, s) ← importModulesCore imports |>.run
    finalizeImportHacked (leakEnv := leakEnv) s imports opts trustLevel

structure Config : Type where
  srcDir : System.FilePath := ".lake/build/lib" -- the directory where .olean files are found
  outDir : System.FilePath := "sexp" -- the output directory (created if needed)
  refsOnly : Bool := False -- only output references names
  force : Bool := False -- process file even if .sexp is newer than .olean

def usage : String :=
"Usage: lake exe lean2sexp <options>

  --srcdir ⟨DIR⟩    set the source directory where .olean files are (default: build/lib)
  --outdir ⟨DIR⟩    set the output directory (default: sexp)
  --refsOnly        output only referenced names instead of syntax trees, much faster (default: false)
  --force           process a file even if .sexp is newer than .olean (default: false)
"
-- Poor man's parsing of command-line arguments
def parseArgs (conf : Config) (args : List String) : Option Config :=
  match args with
  | [] => .some conf
  | "--srcdir" :: dir :: args => parseArgs {conf with srcDir := dir} args
  | "--outdir" :: dir :: args => parseArgs {conf with outDir := dir} args
  | "--refsOnly" :: args => parseArgs {conf with refsOnly := True} args
  | "--force" :: args => parseArgs {conf with force := True} args
  | _ => .none

unsafe def main (args : List String) : IO Unit := do
  match parseArgs ({} : Config) args with
  | .none =>
    IO.println s!"Error: could not parse command-line arguments\n\n{usage}"
  | .some conf =>
    let what := if conf.refsOnly then "references" else "syntax trees"
    IO.println s!"Extracting {what} from {conf.srcDir} to {conf.outDir}"
    IO.FS.createDirAll conf.outDir
    let allFiles ← System.FilePath.walkDir conf.srcDir
    let files := allFiles.toList.filter (fun fp => fp.toString.endsWith ".olean")
    let totalFiles := files.length
    for (k, srcFile) in files.enumFrom 1 do
      if ! srcFile.toString.startsWith conf.srcDir.toString then
        IO.println s!"skipping {srcFile} because, mysteriously, is not in {conf.outDir}"
      else
        let baseName := (srcFile.withExtension "").components.drop (conf.srcDir.components.length)
        let outFile := System.FilePath.join conf.outDir $ (".".intercalate (baseName ++ ["sexp"]))
        let srcMetadata ← srcFile.metadata
        let outMetadata ← outFile.metadata.toBaseIO
        let srcNewer : Bool :=
          match outMetadata with
          | .error _ => true
          | .ok m => decide (srcMetadata.modified > m.modified)
        if ! conf.force && ! srcNewer then
          IO.println s!"[{k}/{totalFiles}] SKIPPING {srcFile}"
        else
          IO.println s!"[{k}/{totalFiles}] PROCESSING {srcFile} → {outFile}"
          let (data, region) ← Lean.readModuleData srcFile
          let constModMap ← importModulesHacked data.imports Lean.Options.empty
          let moduleName := baseName.foldl Lean.Name.str Lean.Name.anonymous
          IO.FS.withFile outFile .write (fun fh => Sexp.write fh $ Sexp.fromModuleData constModMap conf.refsOnly moduleName data)
          region.free
