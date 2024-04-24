import LAMR
import Std

/-- The literal p_i_v says that the number at index `i` is `v`. -/
def mkLit (i v : Nat) : Lit :=
  Lit.pos s!"p_{i}_{v}"

-- We can represent a guess a list of literals together with the score
structure NumberMindGuess where
  lits : List Lit
  k : Nat

-- If the guess is given by a list of numbers, this turns it into the list of literals.
def guessRowToLits (ns : List Nat) :=
  List.range ns.length |>.zip ns |>.map fun (i, v) => mkLit i v

-- Make a row from a list of numbers and the number of correct guesses.
def NumberMindGuess.ofGuess (ns : List Nat) (k : Nat) : NumberMindGuess := {
  lits := guessRowToLits ns
  k }

-- If you use variables `x_i_v` to say that entry `i` has value `v`, you can use the
-- following to turn a satisfying assignment into a solution,.

def decodeSolution (puzzleLen : Nat) (τ : List Lit): Except String (List Nat) := do
  let mut soln : Array Nat := Array.mkArray puzzleLen 0
  for l in τ do
    if let Lit.pos x := l then
      let [_,i,v] := x.splitOn "_"
        | throw s!"unexpected variable {x}"
      let [some i, some v] := [i,v].map String.toNat?
        | throw s!"cannot decode numbers in {x}"
      soln := soln.set! i v
  return soln.toList

/-
This is what you need to write: given the length of the rows and a list of guesses,
print a solution.
-/
def solveNumberMind (puzzleLen : Nat) (guesses : List NumberMindGuess) : IO Unit := do
  sorry

-- This lets us write `ofGuess` instead of `NumberMindGuess.ofGuess`
open NumberMindGuess

-- You can test your solution on this easy game:
def easyGame : List NumberMindGuess := [
  ofGuess [9,0,3,4,2] 2,
  ofGuess [7,0,7,9,4] 0,
  ofGuess [3,9,4,5,8] 2,
  ofGuess [3,4,1,0,9] 1,
  ofGuess [5,1,5,4,5] 2,
  ofGuess [1,2,5,3,1] 1
]

/- ok: [3, 9, 5, 4, 2] -/
-- #eval solveNumberMind 5 easyGame

def toughGame : List NumberMindGuess := [
  ofGuess [5,6,1,6,1,8,5,6,5,0,5,1,8,2,9,3] 2,
  ofGuess [3,8,4,7,4,3,9,6,4,7,2,9,3,0,4,7] 1,
  ofGuess [5,8,5,5,4,6,2,9,4,0,8,1,0,5,8,7] 3,
  ofGuess [9,7,4,2,8,5,5,5,0,7,0,6,8,3,5,3] 3,
  ofGuess [4,2,9,6,8,4,9,6,4,3,6,0,7,5,4,3] 3,
  ofGuess [3,1,7,4,2,4,8,4,3,9,4,6,5,8,5,8] 1,
  ofGuess [4,5,1,3,5,5,9,0,9,4,1,4,6,1,1,7] 2,
  ofGuess [7,8,9,0,9,7,1,5,4,8,9,0,8,0,6,7] 3,
  ofGuess [8,1,5,7,3,5,6,3,4,4,1,1,8,4,8,3] 1,
  ofGuess [2,6,1,5,2,5,0,7,4,4,3,8,6,8,9,9] 2,
  ofGuess [8,6,9,0,0,9,5,8,5,1,5,2,6,2,5,4] 3,
  ofGuess [6,3,7,5,7,1,1,9,1,5,0,7,7,0,5,0] 1,
  ofGuess [6,9,1,3,8,5,9,1,7,3,1,2,1,3,6,0] 1,
  ofGuess [6,4,4,2,8,8,9,0,5,5,0,4,2,7,6,8] 2,
  ofGuess [2,3,2,1,3,8,6,1,0,4,3,0,3,8,4,5] 0,
  ofGuess [2,3,2,6,5,0,9,4,7,1,2,7,1,4,4,8] 2,
  ofGuess [5,2,5,1,5,8,3,3,7,9,6,4,4,3,2,2] 2,
  ofGuess [1,7,4,8,2,7,0,4,7,6,7,5,8,2,7,6] 3,
  ofGuess [4,8,9,5,7,2,2,6,5,2,1,9,0,3,0,6] 1,
  ofGuess [3,0,4,1,6,3,1,1,1,7,2,2,4,6,3,5] 3,
  ofGuess [1,8,4,1,2,3,6,4,5,4,3,2,4,5,8,9] 3,
  ofGuess [2,6,5,9,8,6,2,6,3,7,3,1,6,8,6,7] 2
]

/- This is the one you need to solve! -/
-- #eval solveNumberMind 16 toughGame
