import Init.System.IO

/- Minimal native executable discovery for the pinned comparator's `which git`.
   It reports the explicitly configured Git executable; it is not a general shell. -/
def main (args : List String) : IO UInt32 := do
  unless args == ["git"] do
    IO.eprintln "WindowsWhich only supports the comparator's `which git` request."
    return 2
  let some path ← IO.getEnv "FORMAL_WINDOWS_GIT"
    | throw <| IO.userError "FORMAL_WINDOWS_GIT is required"
  unless ← System.FilePath.pathExists path do
    throw <| IO.userError "The configured Git executable does not exist"
  IO.println path
  return 0
