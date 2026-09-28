import Lean
import Std
import Mathlib

open Lean
open Std

/-- Extracts the name of the module containing an element of the environment. -/
def inModule (env : Environment) : Option Name → Option Name
| some N => match env.getModuleIdxFor? N with
            | some M => env.header.moduleNames[M.toNat]!
            | none => none
| none => none

/-- Produces an array of all the elements in the environment, with name,
    info on the constant and containing library, in dependency order.  -/
def declarationsInOrder (env : Environment) :
    Array ((Name × ConstantInfo) × Name) :=
  env.constants.toList.map
    (fun entry@(declName, _) =>
      (entry, Name.getPrefix (match inModule env (some declName) with
                              | some L => L
                              | none   => declName))) |>.toArray

/-- Tests -/
def declarationNamesInOrder (env : Environment) : Array Name :=
  env.constants.toList.map (·.1) |>.toArray

def inEnv (env : Environment) : Option Name -> Bool
| some N => Array.contains (declarationNamesInOrder env) N
| none => false

#eval do
  let env ← getEnv
  let l := declarationNamesInOrder env
  logInfo m!"number of declarations: {l.size}"
  --let N := `PointedCone.subset_dual_flip_iff_subset_dual
  logInfo s!"{inEnv env l[607902]?}"
  let N := some `PointedCone.subset_dual_flip_iff_subset_dual
  logInfo s!"{inModule env N}"
  logInfo s!"{inEnv env (some `PointedCone.subset_dual_flip_iff_subset_dual)}"
  -- then logInfo s!"{N} appears" else logInfo s!"No"

def libraries : Array Name :=
  #[`Mathlib]
/-- End of tests -/

/- From [ABFM26]: collect elements that appear in an
   expression, together with their number. -/
def collectElems (e : Expr) (acc : HashMap Name Nat := {}) :
    HashMap Name Nat :=
  match e with
  | .const declName _            =>
      acc.insert declName (acc.getD declName 0 + 1)
  | .app fn arg                  => collectElems arg (collectElems fn acc)
  | .lam _ binderType body _     =>
      collectElems body (collectElems binderType acc)
  | .forallE _ binderType body _ =>
      collectElems body (collectElems binderType acc)
  | .letE _ type value body _    =>
      collectElems body (collectElems value (collectElems type acc))
  | .mdata _ expr                => collectElems expr acc
  | .proj _ _ struct             => collectElems struct acc
  | .sort _                      =>
     acc.insert (Name.mkSimple "Sort")
                                   (acc.getD (Name.mkSimple "Sort") 0 + 1)
  | _                            => acc

/-- Find the elements depending of a given element, together with their
    weight. -/
def weightedDepNode : Name × ConstantInfo -> Array (Name × Nat) :=
   fun elem =>
     match elem with
     | (_,ci) =>
         match ci with
         | .defnInfo val   => (collectElems val.value).fold
                                (init := collectElems val.type)
                                (fun acc k v =>
                                   acc.insert k (v + acc.getD k 0))
                              |>.toArray
         | .thmInfo val    => (collectElems val.value).fold
                                (init := collectElems val.type)
                                (fun acc k v =>
                                   acc.insert k (v + acc.getD k 0))
                              |>.toArray
         | .opaqueInfo val => (collectElems val.value).fold
                                (init := collectElems val.type)
                                (fun acc k v =>
                                   acc.insert k (v + acc.getD k 0))
                              |>.toArray
         | .axiomInfo val  => collectElems val.type |>.toArray
         | .quotInfo val   => collectElems val.type |>.toArray
         | .inductInfo val => collectElems val.type |>.toArray
         | .ctorInfo val   => collectElems val.type |>.toArray
         | .recInfo val    => collectElems val.type |>.toArray

/-- For each element in an environment that is contained in a list of
    libraries, find all the dependent elements and their weights in type
    and value (if present) of the element. That corresponds to all the
    edges emanating from a given node in the formalisation graph, together
    with their weights. -/
def buildWeightedDepMap
    (entries : Array ((Name × ConstantInfo) × Name))
    (libs : Array Name) :
    Std.HashMap Name (Array (Name × Nat)) :=
  entries.foldl
    (fun acc entry@((declName, _), lib) =>
      if libs.contains lib then
        acc.insert declName (weightedDepNode entry.1)
      else
        acc)
    {}

namespace Tarjan

/-- Next, we make the weighted dependency graph acyclic: We identify all
    the strongly connected components using Tarjan's algorithm and then
    collapse all the nodes in the same component to one new node, adding
    up all the weights of the dependent nodes. The new nodes are arrays
    of the original nodes.

    State maintained by Tarjan's algorithm. -/
structure TarjanState where
  index   : Nat := 0
  indices : Array (Option Nat)
  lowlink : Array Nat
  onStack : Array Bool
  stack   : List Nat := []
  sccs    : List (List Nat) := []

abbrev M := StateM TarjanState

/-- Assign the next DFS index to v and push it on the stack. -/
def initNewNode (v : Nat) : M Unit := do
  let s ← get
  let i := s.index
  set { s with
          index := i + 1
          indices := s.indices.set! v (some i)
          lowlink := s.lowlink.set! v i
          stack := v :: s.stack
          onStack := s.onStack.set! v true }

/-- Main recursive Depth-First Search. -/
def strongConnect (g : Array (Array Nat)) (v : Nat) :
    M Unit := do
  initNewNode v
  for w in g[v]! do
    let s ← get
    match s.indices[w]! with
    | none      => sorry
    | some idxW => sorry
  sorry

/-- Run Tarjan's algorithm on a graph whose nodes are names. -/
def sccs (g : Array (Array Nat)) : List (List Nat) :=
  let n := g.size
  let init : TarjanState :=
    { indices := Array.map (fun _ : Array Nat => (none : Option Nat)) g
      lowlink := Array.map (fun _ : Array Nat => (0 : Nat)) g
      onStack := Array.map (fun _ : Array Nat => (false : Bool)) g }
  let rec visitAll (i : Nat) : M Unit := do
    if h : i < n then
      let s ← get
      match s.indices[i]! with
      | none   =>
          strongConnect g i
      | some _ =>
          pure ()
      visitAll (i+1)
    else
      pure ()
  let final := (visitAll 0).run init
  final.snd.sccs.reverse


end Tarjan
