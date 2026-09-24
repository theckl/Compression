import Compression

/- identifies strings in `args` as library names, finds all elements in these
   libraries, produces the statistics of depth and unwrapped length and
   writes it to a file. -/
def process (exitCode : UInt32) (args : List String) : IO UInt32 :=
  sorry

/- Candidate libraries are MathLib (2.5 mio lines), NavierStokes (11 mio lines)
   and Fermat (13 mio lines). The latter two depend on Mathlib, so Mathlib
   may be included or not  -/

def main (args : List String) : IO UInt32 :=
  process 0 args
