import Lake
open Lake DSL

package «lean2sexp» where
  moreLeanArgs := #["-DautoImplicit=false"]

lean_lib «Lean2sexp» where
  -- add library configuration options here

@[default_target]
lean_exe «lean2sexp» where
  root := `Main
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true
