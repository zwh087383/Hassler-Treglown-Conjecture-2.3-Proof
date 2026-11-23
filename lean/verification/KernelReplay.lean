import Lean.Replay
import Lean.Util.Path
import Lean.Compiler.IR.CompilerM

open Lean

private def projectModule (n : Name) : Bool :=
  (`Audit).isPrefixOf n || (`Sumfree).isPrefixOf n

private def proofDependencies (all : Std.HashMap Name ConstantInfo) (targets : List Name) :
    IO (Std.HashMap Name ConstantInfo) := do
  let mut pending := targets
  let mut found : Std.HashMap Name ConstantInfo := {}
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail
    if found.contains n then continue
    let some ci := all[n]? | continue
    if ci.isUnsafe || ci.isPartial then
      throw <| IO.userError s!"Nonlogical project program in a proof dependency: {n}"
    found := found.insert n ci
    pending := ci.getUsedConstantsAsSet.toList ++ pending
    match ci with
    | .axiomInfo _ => throw <| IO.userError s!"Project axiom in a proof dependency: {n}"
    | .inductInfo i => pending := i.all ++ i.ctors ++ pending
    | .ctorInfo c => pending := c.induct :: pending
    | .recInfo r => pending := r.all ++ pending
    | _ => pure ()
  return found

/-- Recheck the project's compiled proof terms in an environment containing only its
    external dependencies. Extra command-line arguments identify theorem roots. -/
def main (args : List String) : IO Unit := do
  let target := (args[0]?.getD "Audit").toName
  let roots := if args.tail.isEmpty then [`Audit.Sharp.main_theorem] else args.tail.map String.toName
  initSearchPath (← findSysroot)
  let loaded ← importModules #[{ module := target }] {} 0
  let mut imports : Array Import := #[]
  let mut declarations : Std.HashMap Name ConstantInfo := {}
  let mut moduleCount := 0
  for moduleName in loaded.header.moduleNames, data in loaded.header.moduleData do
    if projectModule moduleName then
      moduleCount := moduleCount+1
      for declaration in data.constants do
        declarations := declarations.insert declaration.name declaration
    else
      imports := imports.push { module := moduleName }
  let base ← importModules imports {} 0
  for name in roots do
    if (base.toKernelEnv.find? name).isSome || !declarations.contains name then
      throw <| IO.userError s!"The expected theorem did not originate in the project: {name}"
  let needed ← proofDependencies declarations roots
  let theoremCount := needed.toList.countP (fun entry => entry.2 matches .thmInfo _)
  IO.println s!"Inspected {moduleCount} project modules. Replaying {needed.size} project declarations in the dependency closure, including {theoremCount} theorem declarations."
  let out ← IO.getStdout
  out.flush
  let mut checked := base
  let mut seen : NameSet := {}
  for i in [:loaded.header.moduleNames.size] do
    let moduleName := loaded.header.moduleNames[i]!
    if !projectModule moduleName then continue
    -- Native decision procedures need the interpreter's compiled code. These entries
    -- are not logical declarations and do not add anything to the kernel's constant map.
    for code in IR.declMapExt.getModuleEntries loaded i do
      checked := IR.declMapExt.addEntry checked code
    let mut inModule : Std.HashMap Name ConstantInfo := {}
    for ci in loaded.header.moduleData[i]!.constants do
      if needed.contains ci.name && !seen.contains ci.name then
        inModule := inModule.insert ci.name ci
        seen := seen.insert ci.name
    if inModule.isEmpty then continue
    -- Reset the elaborator's per-module private-name index between modules.
    checked ← Environment.replay inModule ((Environment.ofKernelEnv checked.toKernelEnv).setMainModule moduleName)
    IO.println s!"Checked {inModule.size} declarations from {moduleName}."
    out.flush
  -- The elaborator only indexes newly added declarations for the current module.
  -- The kernel map retains declarations from every preceding module as well.
  let kernel := checked.toKernelEnv
  for (name, _) in needed.toList do
    unless seen.contains name && (kernel.find? name).isSome do
      throw <| IO.userError s!"A dependency is absent after replay: {name}"
  for name in roots do
    unless (kernel.find? name).any (fun c => c matches .thmInfo _) do
      throw <| IO.userError s!"The expected theorem is absent after replay: {name}"
    IO.println s!"KERNEL REPLAY PASSED: {name}"
