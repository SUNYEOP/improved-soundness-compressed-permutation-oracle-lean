import QuantumOracle.Proof.ImprovedSoundness
import Lean

/-! A read-only environment inspection, not a proof-validation command.
The root theorem's VALUE is never traversed. This first, conservative slice
stops at Prop-valued declaration bodies but retains inline proof references
occurring inside computational definitions. All such references are labelled.
-/

open Lean Meta Elab Command

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace StatementReview

def rootName : Name := ``QuantumOracle.ImprovedSoundness.soundness

def constantKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def moduleName (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => env.mainModule

def boundaryModule (m : Name) : Bool :=
  ["Mathlib", "Lean", "Std", "Init"].any fun modulePrefix =>
    m.toString == modulePrefix || m.toString.startsWith (modulePrefix ++ ".")

def sourcePath (m : Name) : String :=
  let rel := m.toString.replace "." "/" ++ ".lean"
  if m.toString.startsWith "QuantumOracle" then rel
  else if m.toString.startsWith "RepresentationTheory" then
    "vendor/etingof-representation-theory/" ++ rel
  else rel

def sortedNames (names : Array Name) : Array Name :=
  (names.foldl (fun (s : NameHashSet) n => s.insert n) {}).toArray.qsort
    (fun a b => a.toString < b.toString)

/-- Include structure names carried by kernel projection expressions as well
as ordinary constants. Lean's `getUsedConstants` omits those projection tags. -/
def expressionDeps (e : Expr) : MetaM (Array Name) := do
  let names ← IO.mkRef (#[] : Array Name)
  e.forEach fun sub => do
    match sub with
    | .const n _ | .proj n _ _ => names.modify (·.push n)
    | _ => pure ()
  return sortedNames (← names.get)

def rangeJson (r : DeclarationRanges) : Json := Json.mkObj [
  ("startLine", toJson r.range.pos.line),
  ("startColumn", toJson r.range.pos.column),
  ("endLine", toJson r.range.endPos.line),
  ("endColumn", toJson r.range.endPos.column),
  ("selectionStartLine", toJson r.selectionRange.pos.line),
  ("selectionStartColumn", toJson r.selectionRange.pos.column),
  ("selectionEndLine", toJson r.selectionRange.endPos.line),
  ("selectionEndColumn", toJson r.selectionRange.endPos.column)]

partial def sourceRange (n : Name) : MetaM (Option (Name × DeclarationRanges)) := do
  if n.isAnonymous then return none
  if let some r ← findDeclarationRangesCore? n then return some (n, r)
  sourceRange n.getPrefix

def structuralDeps : ConstantInfo → MetaM (Array Name)
  | .inductInfo v => pure (v.all.toArray ++ v.ctors.toArray)
  | .ctorInfo v => pure #[v.induct]
  | .recInfo v => do
      let mut deps := v.all.toArray
      for rule in v.rules do
        deps := deps ++ #[rule.ctor] ++ (← expressionDeps rule.rhs)
      return deps
  | _ => pure #[]

def extract : MetaM Unit := do
  let env ← getEnv
  let mut pending := #[rootName]
  let mut cursor := 0
  let mut seen : NameHashSet := {}
  let mut nodes : Array Json := #[]
  let mut boundary : Array Json := #[]
  let mut missing : Array Name := #[]
  let mut proofCount := 0
  let mut valueCount := 0
  while cursor < pending.size do
    let n := pending[cursor]!
    cursor := cursor + 1
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | missing := missing.push n; continue
    let mod := moduleName env n
    let proof ← isProp ci.type
    if boundaryModule mod then
      boundary := boundary.push <| Json.mkObj [
        ("name", toJson n), ("module", toJson mod),
        ("kind", toJson (constantKind ci)), ("isProof", toJson proof)]
      continue
    let instanceDecl := isInstanceCore env n
    let typeDecl ← isTypeFormerType ci.type
    let category := if proof then "proof-obligation" else if instanceDecl then "instance"
      else if typeDecl then "type" else "definition"
    let typeDeps ← expressionDeps ci.type
    let value := if proof || n == rootName then none else ci.value? (allowOpaque := true)
    let valueDeps ← match value with
      | some v => expressionDeps v
      | none => pure #[]
    let structureDeps := sortedNames (← structuralDeps ci)
    let deps := sortedNames (typeDeps ++ valueDeps ++ structureDeps)
    pending := pending ++ deps
    if proof then proofCount := proofCount + 1
    if value.isSome then valueCount := valueCount + 1
    let source ← sourceRange n
    let prettyType ← ppExpr ci.type
    nodes := nodes.push <| Json.mkObj [
      ("name", toJson n), ("kind", toJson (constantKind ci)),
      ("classification", toJson category), ("isProof", toJson proof),
      ("isInstance", toJson instanceDecl), ("module", toJson mod),
      ("source", toJson (sourcePath mod)),
      ("sourceOwner", toJson (source.map (·.1))),
      ("sourceRange", (source.map (rangeJson ∘ Prod.snd)).getD Json.null),
      ("rangeInheritedFromParent", toJson (source.any (fun s => s.1 != n))),
      ("type", toJson prettyType.pretty),
      ("valueTraversed", toJson value.isSome),
      ("proofValueSkipped", toJson proof),
      ("typeDependencies", toJson typeDeps),
      ("valueDependencies", toJson valueDeps),
      ("structuralDependencies", toJson structureDeps),
      ("dependencies", toJson deps)]
  let report := Json.mkObj [
    ("schemaVersion", toJson (1 : Nat)),
    ("root", toJson rootName),
    ("rootTraversal", toJson "type only; theorem proof value excluded"),
    ("scope", toJson "Syntactic semantic slice, not a minimal mathematical closure or a standalone proof"),
    ("declarationPolicy", toJson "Follow types plus non-Prop values, inductive constructors and recursor rules; stop Prop-valued declaration bodies"),
    ("inlineProofPolicy", toJson "Conservative: retain inline proof references inside non-Prop values, then stop their named Prop declaration bodies"),
    ("boundaryModulePrefixes", toJson #["Mathlib", "Lean", "Std", "Init"]),
    ("sourceCoordinates", toJson "Lean declaration ranges: 1-based lines, 0-based Unicode-codepoint columns, exclusive end"),
    ("declarationCount", toJson nodes.size),
    ("proofObligationCount", toJson proofCount),
    ("traversedValueCount", toJson valueCount),
    ("externalBoundaryCount", toJson boundary.size),
    ("missingDeclarations", toJson (sortedNames missing)),
    ("declarations", toJson nodes),
    ("externalBoundary", toJson boundary)]
  let path := "review/semantic-dependencies.json"
  IO.FS.writeFile path (report.pretty ++ "\n")
  IO.println s!"Wrote {path}: {nodes.size} local declarations, {proofCount} proof obligations, {boundary.size} boundary declarations, {missing.size} missing."

end StatementReview

run_cmd liftTermElabM do StatementReview.extract
