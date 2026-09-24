import Lean
import Std
import Mathlib

open Lean
open Std

/-- Constants referenced by a declaration. -/
def constDeps (ci : ConstantInfo) : List Name :=
  ci.value?.map (·.getUsedConstants.toList) |>.getD []

def inModule (env : Environment) : Option Name → Option Name
| some N => match env.getModuleIdxFor? N with
            | some M => env.header.moduleNames[M.toNat]!
            | none => none
| none => none

def declarationsInOrder (env : Environment) :
    Array ((Name × ConstantInfo) × Name) :=
  env.constants.toList.map
    (fun entry@(declName, _) =>
      (entry, Name.getPrefix (match inModule env (some declName) with
                              | some L => L
                              | none   => declName))) |>.toArray

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
  -- then logInfo s!"{N} appears" else logInfo s!"No"

def libraries : Array Name :=
  #[`Mathlib]

/- From [ABFM26] -/
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
