import SupplementAdder

/-! Reject placeholders and additional axioms in all proof namespaces. -/
run_cmd do
  let env ← Lean.getEnv
  let count ← env.constants.foldM (init := (0 : Nat)) fun count name info => do
    let relevant := #["AdderTrace.", "AdderCones.", "ExplicitFilter.", "SupplementAdder."].any
      (fun nsPrefix => name.toString.startsWith nsPrefix)
    match info with
    | .thmInfo _ =>
      if relevant then
        let axioms ← Lean.collectAxioms name
        for ax in axioms do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "Unexpected axiom {ax} in {name}"
        return count + 1
      else return count
    | _ => return count
  Lean.logInfo m!"AXIOM AUDIT PASSED: {count} theorems; only propext, Classical.choice, Quot.sound."
