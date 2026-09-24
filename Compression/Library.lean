import Lean.Data.Json

open Lean

abbrev DepGraph := Std.HashMap String (List String)

/-- Parse one package entry. -/
def parsePackage (j : Json) :
    Except String (String × List String) := do
  let obj <- j.getObj?
  match obj.get? "name" with
  | some (.str s) =>
      let deps :=
      match obj.get? "dependencies" with
      | some (.arr depArr) =>
        depArr.toList.filterMap (fun dep =>
          match dep with
          | Json.obj depObj =>
              match depObj.get? "name" with
              | some (.str s) => some s
              | _ => none
          | _ => none)
      | _ =>
          []
      pure (s, deps)
  | _ => throw "missing package name"

/-- Parse the package graph from a manifest JSON value. -/
def parseManifest (j : Json) :
    Except String DepGraph := do
  let obj <- j.getObj?
  match obj.get? "packages" with
  | some (.arr ps) =>
      let mut graph : DepGraph := {}
      for pkg in ps do
        let (name, deps) <- parsePackage pkg
        graph := graph.insert name deps
      pure graph
  | _ => throw "manifest does not contain field packages"

/-- Read and parse a lake-manifest.json file. -/
def loadDepGraph (manifestFile : System.FilePath) :
    IO DepGraph := do
  let txt ← IO.FS.readFile manifestFile
  let json ←
    match Json.parse txt with
    | .ok j => pure j
    | .error e => throw <| IO.userError s!"JSON parse error: {e}"
  match parseManifest json with
  | .ok graph => pure graph
  | .error e => throw <| IO.userError s!"Manifest parse error: {e}"

#eval do
  let graph ← loadDepGraph "lake-manifest.json"
  match graph.get? "mathlib" with
  | some deps => IO.println s!"mathlib depends on {deps}"
  | none => IO.println "mathlib not found"
