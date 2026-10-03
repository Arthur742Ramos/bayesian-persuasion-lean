module
public import BayesianPersuasion
import Lean.Util.CollectAxioms
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let allowed := #[`propext, `Quot.sound, `Classical.choice]
  let mut count : Nat := 0
  for (n, _) in env.constants.toList do
    let authored := match env.getModuleIdxFor? n with
      | some idx => (`BayesianPersuasion).isPrefixOf env.header.moduleNames[idx.toNat]!
      | none => false
    if authored then
      let axioms ← collectAxioms n
      for a in axioms do
        unless allowed.contains a do
          throwError "Forbidden axiom {a} in {n}"
      logInfo m!"AXIOMS {n}: {axioms}"
      count := count + 1
  logInfo m!"AUDIT PASSED: {count} authored constants; standard axioms only"
