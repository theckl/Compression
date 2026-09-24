import Std.Data.HashMap.Basic
import Compression.Library

/- Structure that stores the 25%-percentile, the median, and
   the 75%-percentile of a list of numbers -/
structure Percentiles where
  perc25 : Nat
  median : Nat
  perc75 : Nat

/- Structure that stores the unwrapped length and the depth of elements,
   and finally the dependency of unwrapped length by depth,
   in some set of elements -/
structure LibraryStats where
  unwrappedDepth : Std.HashMap String (Nat × Nat)
  compression  : Std.HashMap Nat Percentiles

/- produces the `LibraryStats` from a given set of libraries, already
   ordered by dependencies. Elements that are imported from libraries not
   in the list are treated as primitive nodes of depth 1. -/
def produceLibraryStats (depLib : DepLibrary) :
  LibraryStats :=
sorry
