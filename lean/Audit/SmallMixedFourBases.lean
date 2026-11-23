import Audit.MixedStrip

namespace Audit.SmallMixed
open Finset Blocks Lower Generic

abbrev Plane := Field5 × Field5
abbrev Cube := Plane × Field5

def shape2 (j l : Fin 5) (a b : Field5) : Strip.Seed :=
  {(0,1,0),(1,0,0),(j,0,1),(l,a,b)}

def shape3 (j l : Fin 5) : Finset (Pt Cube) :=
  {(0,(1,0),0),(1,(0,0),0),(j,(0,1),0),(l,(0,0),1)}

def extra : Bool → Strip.Seed
  | false => {(0,1,0),(0,4,0),(1,0,0),(4,0,1)}
  | true => {(0,1,0),(0,0,1),(1,0,0),(4,4,0)}

end Audit.SmallMixed
