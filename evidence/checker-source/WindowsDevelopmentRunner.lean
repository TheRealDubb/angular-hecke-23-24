import Init.System.IO

/- Windows counterpart of upstream scripts/fake-landrun.sh DEVELOPMENT MODE.
   NO SANDBOX IS PROVIDED. Only the configured Lake and exporter may be launched.
   Arguments are passed directly, without a command shell. -/
def main (args : List String) : IO UInt32 := do
  let some lake ← IO.getEnv "FORMAL_WINDOWS_LAKE"
    | throw <| IO.userError "FORMAL_WINDOWS_LAKE is required"
  let some exporter ← IO.getEnv "COMPARATOR_LEAN4EXPORT"
    | throw <| IO.userError "COMPARATOR_LEAN4EXPORT is required"
  let some searchPathFile ← IO.getEnv "FORMAL_WINDOWS_LEAN_PATH_FILE"
    | throw <| IO.userError "The captured project LEAN_PATH file is required"
  let projectSearchPath ← IO.FS.readFile searchPathFile
  if projectSearchPath.isEmpty then
    throw <| IO.userError "The captured project LEAN_PATH must be nonempty"
  let afterSeparator := (args.dropWhile (· != "--")).drop 1
  let command :: childArgs := afterSeparator
    | throw <| IO.userError "Expected an explicit -- followed by the child command"
  let executable ← if command == "lake" then pure lake
    else if command == exporter then pure exporter
    else throw <| IO.userError "Development runner refuses an unconfigured executable"
  if command == "lake" && childArgs.head? != some "build" then
    throw <| IO.userError "Development runner permits only lake build"
  IO.eprintln "WINDOWS DEVELOPMENT MODE: running the configured child without a Landrun sandbox."
  IO.eprintln s!"Development launcher explicitly passes {projectSearchPath.length} LEAN_PATH characters."
  let child ← IO.Process.spawn {
    cmd := executable
    args := childArgs.toArray
    env := #[("LEAN_PATH", some projectSearchPath)]
  }
  child.wait
