import Mathlib

/-!
# Pure seven-wheel order types

The eight conowheel types used by the universal hull-seven argument are a
small finite mathematical object.  They do not depend on a retained search
bank, a packed survivor path, or any production certificate.  This module
therefore owns the type, its exact 21-bit chord keys, and the three tiny list
helpers used to canonically compare dihedral presentations.
-/

namespace Heilbronn8

/-- A fixed-width big-endian Boolean expansion of a natural number. -/
def hullSevenFixedBitsAux : Nat → Nat → List Bool → List Bool
  | 0, _, answer => answer
  | length + 1, bits, answer =>
      hullSevenFixedBitsAux length (bits / 2) ((bits % 2 == 1) :: answer)

def hullSevenFixedBits (bits length : Nat) : List Bool :=
  hullSevenFixedBitsAux length bits []

/-- The eight self-dual seven-wheel chord types, in lexicographic key order. -/
inductive HullSevenType where
  | type0
  | type1
  | type2
  | type3
  | type4
  | type5
  | type6
  | type7
deriving Repr, DecidableEq

/-- Exact 21-bit key in nested pair order
`01,02,03,04,05,06,12,...,45,46,56`. -/
def HullSevenType.key : HullSevenType → List Bool
  | .type0 => hullSevenFixedBits 1065983 21 -- 100000100001111111111
  | .type1 => hullSevenFixedBits 1074175 21 -- 100000110001111111111
  | .type2 => hullSevenFixedBits 1078271 21 -- 100000111001111111111
  | .type3 => hullSevenFixedBits 1598271 21 -- 110000110001100111111
  | .type4 => hullSevenFixedBits 1598399 21 -- 110000110001110111111
  | .type5 => hullSevenFixedBits 1602367 21 -- 110000111001100111111
  | .type6 => hullSevenFixedBits 1602495 21 -- 110000111001110111111
  | .type7 => hullSevenFixedBits 1864639 21 -- 111000111001110111111

def hullSevenTypes : List HullSevenType :=
  [.type0, .type1, .type2, .type3, .type4, .type5, .type6, .type7]

def HullSevenType.ofKey (key : List Bool) : Option HullSevenType :=
  hullSevenTypes.find? fun orderType => orderType.key == key

/-- The 21 increasing pairs of seven indices. -/
def hullSevenPairIndices : List (Nat × Nat) :=
  (List.range 7).flatMap fun left =>
    ((List.range 7).drop (left + 1)).map fun right => (left, right)

/-- Lexicographic order on Boolean lists, with `false < true`. -/
def boolListLE : List Bool → List Bool → Bool
  | [], _ => true
  | _ :: _, [] => false
  | left :: lefts, right :: rights =>
      if left == right then boolListLE lefts rights else !left && right

def leastBoolList : List (List Bool) → List Bool
  | [] => []
  | first :: rest =>
      rest.foldl (fun best candidate =>
        if boolListLE candidate best then candidate else best) first

end Heilbronn8
