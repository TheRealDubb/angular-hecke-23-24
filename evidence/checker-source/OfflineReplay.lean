import Comparator
import Export.Parse
import Lean

/- Windows offline replay. No sandbox assurance is claimed.
   compareAt and checkAxioms are the upstream comparator implementations.
   Kernel replay and quotient post-check reproduce upstream Main.lean. -/

private def primitiveTargets : Array Lean.Name := #[
  ``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.pow, ``Nat.gcd, ``Nat.div, ``Nat.mod,
  ``Nat.beq, ``Nat.ble, ``Nat.land, ``Nat.lor, ``Nat.xor, ``Nat.shiftLeft,
  ``Nat.shiftRight, ``String.ofList, ``Char.ofNat, ``List, ``eagerReduce,
  ``Nat, ``String, ``String.mk, ``Char, ``optParam, ``autoParam,
  ``semiOutParam, ``outParam]

private def parseExport (path : String) : IO Export.ExportedEnv := do
  let file ← IO.FS.Handle.mk path .read
  Export.parseStream (IO.FS.Stream.ofHandle file)

def main (args : List String) : IO Unit := do
  let [configFile, challengeFile, solutionFile] := args
    | throw <| IO.userError "Usage: offline-replay config.json challenge.ndjson solution.ndjson"
  let cfg ← IO.ofExcept <| Lean.Json.parse (← IO.FS.readFile configFile)
  let names := fun key => do
    let a ← cfg.getObjValAs? (Array String) key
    pure (a.map String.toName)
  let theorems ← IO.ofExcept (names "theorem_names")
  let axioms ← IO.ofExcept (names "permitted_axioms")
  let definitions := (names "definition_names").toOption.getD #[]
  let challenge ← parseExport challengeFile
  let solution ← parseExport solutionFile
  IO.ofExcept <| Comparator.compareAt challenge solution (theorems ++ axioms)
    definitions primitiveTargets
  IO.println "STATEMENT_COMPARISON_PASSED"
  IO.ofExcept <| Comparator.checkAxioms solution theorems definitions axioms
  IO.println "AXIOM_AUDIT_PASSED"
  let env ← Lean.mkEmptyEnvironment
  let mut kernelEnv := env.toKernelEnv
  let origConstMap := solution.constMap
  let quotTargets := [`Quot.mk, `Quot.lift, `Quot.ind]
  let kernelConstMap := quotTargets.foldl (init := origConstMap) (·.erase ·)
  kernelEnv ← kernelEnv.replay kernelConstMap
  for quotTarget in `Quot :: quotTargets do
    if let some info := origConstMap[quotTarget]? then
      let some info' := kernelEnv.find? quotTarget
        | throw <| IO.userError s!"Missing quotient constant: {quotTarget}"
      if info != info' then
        throw <| IO.userError s!"Quotient constant mismatch: {quotTarget}"
  IO.println "KERNEL_REPLAY_AND_QUOTIENT_POSTCHECK_PASSED"
  IO.println "OFFLINE_REPLAY_PASSED: native Windows; production sandbox not exercised"
