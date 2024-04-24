import LAMR.Util.FirstOrder.Atp
open Std

-- The parts you need to fill in are labeled "TODO".

/-
These helper functions may be useful.
-/

namespace Std.AssocList

def find! [BEq α] [Inhabited β] (a : α) (m : AssocList α β) : β :=
  match m.find? a with
    | some b => b
    | none   => default

end Std.AssocList

def getVal (s : String) (m : AssocList String Sexp) : Nat :=
  match evalNumConst (m.find! s) with
    | some n => n
    | none   => 0

/-
These examples may be helpful. See also the examples in the folder
Examples/using_smt_solvers.
-/

def smt_example_input :=
let xmin := "5"
let ymin := "7"
sexps!{
    (set-logic QF_LIA)
    (set-option :produce-models true)
    (declare-const x Int)
    (declare-const y Int)
    (declare-const z Int)
    (assert (<= {xmin} x))
    (assert (<= {ymin} y))
    (assert (<= (+ x y) z))
    (check-sat)
    (get-model)
  }

def smt_example : IO Unit := do
  -- turn on verbose output to see what is going on.
  let out ← callZ3 smt_example_input (verbose := true)
  match out with
  | Sexp.atom "sat" :: m :: _ =>
    IO.println "Model as an Sexpr"
    IO.println m
    IO.println ""
    let assocList := decodeModelConsts m
    IO.println "Model as an association list:"
    IO.println assocList
    let x := getVal "x" assocList
    let y := getVal "y" assocList
    let z := getVal "z" assocList
    IO.println ""
    IO.println s!"x := {x}, y := {y}, z := {z}"
  | ss =>
    IO.println "Not SAT. Solver output:"
    IO.println ss

#eval smt_example

-- There is also notation for splicing in another list of sexprs.

def smt_example_input2 : List Sexp := Id.run do
  let mut decls : Array Sexp := #[]
  for var in ["x", "y", "z"] do
    decls := decls.push sexp!{(declare-const {var} Int)}
  let xmin := "5"
  let ymin := "7"
  sexps!{
      (set-logic QF_LIA)
      (set-option :produce-models true)
      ...{decls.toList}
      (assert (<= {xmin} x))
      (assert (<= {ymin} y))
      (assert (<= (+ x y) z))
      (check-sat)
      (get-model)
    }

def smt_example2 : IO Unit := do
  let out ← callZ3 smt_example_input (verbose := false)
  match out with
  | Sexp.atom "sat" :: m :: _ =>
    let assocList := decodeModelConsts m
    let x := getVal "x" assocList
    let y := getVal "y" assocList
    let z := getVal "z" assocList
    IO.println s!"x := {x}, y := {y}, z := {z}"
  | ss =>
    IO.println "Not SAT. Solver output:"
    IO.println ss

#eval smt_example2

/-
Problem 1.
-/

-- TODO: Add the relevant constraints

def problem1_input :=
sexps!{
    (set-logic QF_NIA)
    (set-option :produce-models true)
    (declare-const f Int)
    (declare-const o Int)
    (declare-const s Int)
    (declare-const c Int)
    (declare-const l Int)
    (declare-const a Int)
    (declare-const m Int)
    (declare-const r Int)
    (assert (and (>= f 0) (<= f 9)))
    (assert (and (>= o 0) (<= o 9)))
    (assert (and (>= s 0) (<= s 9)))
    (assert (and (>= c 0) (<= c 9)))
    (assert (and (>= l 0) (<= l 9)))
    (assert (and (>= a 0) (<= a 9)))
    (assert (and (>= m 0) (<= m 9)))
    (assert (and (>= r 0) (<= r 9)))
    (assert (distinct f o s c l a m r))
    (declare-const fof Int)
    (declare-const scs Int)
    (assert (= fof (+ (* f 101) (* o 10))))
    (assert (= scs (+ (* s 101) (* c 10))))
    (declare-const lamr Int)
    (assert (= lamr (+ (* l 1000) (* a 100) (* m 10) r)))
    (assert (= (* fof 9999) (* scs lamr)))
    (check-sat)
    (get-model)
  }

-- TODO: call the solver and print out the answer

def problem1 : IO Unit := do
  let out ← callZ3 problem1_input (verbose := false)
  match out with
  | Sexp.atom "sat" :: m :: _ =>
    let assocList := decodeModelConsts m
    IO.println "Solution:"
    IO.println assocList
  | ss =>
    IO.println "Not SAT. Solver output:"
    IO.println ss

#eval problem1

/-
Problem 2.
-/

-- Here are some helper functions

def distinctSexp (consts : List String) : Sexp :=
  Sexp.expr <| [Sexp.atom "distinct"] ++ consts.map Sexp.atom

def multiAritySexp (op : String) (args : List Sexp): Sexp :=
  Sexp.expr <| (Sexp.atom op) :: args

def natConst (i : Nat) := s!"{i}"
def node (i : Nat) := s!"v{i}"
def edge (i : Nat) := s!"e{i}"

#eval distinctSexp [node 0, node 1, node 2]
#eval multiAritySexp "or" [sexp!{({node 0} = 0)}, sexp!{({node 0} = 1)}, sexp!{({node 0} = 2)}]
#eval sexp!{(assert {multiAritySexp "or" [sexp!{({node 0} = 0)}, sexp!{({node 0} = 1)}, sexp!{({node 0} = 2)}]})}

-- TODO: The constraints from part A.

def gracefulLabelingA (n : Nat) : Array Sexp := Id.run do
  let mut body : Array Sexp := #[]
  -- Declare vertex and edge variables.
  for i in [0:n+1] do
    body := body.push (sexp!{(declare-const {node i} Int)})
  for i in [1:n+1] do
    body := body.push (sexp!{(declare-const {edge i} Int)})

  -- Distinct vertex labels.
  body := body.push (sexp!{(assert {distinctSexp (List.range (n+1) |>.map node)})})
  -- Distinct edge labels.
  body := body.push (sexp!{(assert {distinctSexp (List.range' 1 n |>.map edge)})})

  -- Vertex labels in range 0 to n.
  for i in [0:n+1] do
    body := body.push (sexp!{(assert (and (>= {node i} 0) (<= {node i} {natConst n})))})

  -- Edge labels in range 1 to n.
  for i in [1:n+1] do
    body := body.push (sexp!{(assert (and (>= {edge i} 1) (<= {edge i} {natConst n})))})

  -- Edge label is the absolute difference between its vertices.
  for i in [1:n+1] do
    body := body.push (sexp!{(assert (= {edge i} (abs (- {node i} {node (i-1)}))))})

  body

-- Do a reality check.

#eval gracefulLabelingA 9 |>.toList

-- TODO: the constraints from part B.

def gracefulLabelingB (n : Nat) : Array Sexp := Id.run do
  let mut body : Array Sexp := gracefulLabelingA n

  -- Additional constraints for part B.
  for i in [0:n+1] do
    let mut orClause : List Sexp := []
    for j in [0:n+1] do
      orClause := orClause.cons (sexp!{(= {node j} {natConst i})})
    body := body.push (sexp!{(assert {multiAritySexp "or" orClause})})

  for i in [1:n+1] do
    let mut orClause : List Sexp := []
    for j in [1:n+1] do
      orClause := orClause.cons (sexp!{(= {edge j} {natConst i})})
    body := body.push (sexp!{(assert {multiAritySexp "or" orClause})})

  body

def compareOptionNat (a b : Option Nat) : Bool :=
  match a, b with
  | none, none => false
  | none, _ => true
  | _, none => false
  | some n, some m => n <= m

def insertPair (p : Option Nat × Sexp) (l : List (Option Nat × Sexp)) : List (Option Nat × Sexp) :=
  match l with
  | [] => [p]
  | h::t => if compareOptionNat p.fst h.fst then p::l else h::(insertPair p t)

def sortPairs (l : List (Option Nat × Sexp)) : List (Option Nat × Sexp) :=
  match l with
  | [] => []
  | h::t => insertPair h (sortPairs t)
-- Another reality check.

def getLast : List α → Option α
| []       => none -- Empty list case
| [a]      => some a -- Single element list case
| _::xs => getLast xs -- Recursive call on the tail of the list

def constructString (node_list edge_list : List (Option Nat × Sexp)) : String :=
  let nodes := node_list.map (fun ⟨_, num⟩ => s!"({num})")
  let edges := edge_list.map (fun ⟨_, num⟩ => s!"-{num}-")
  let combined := List.zip nodes edges |> List.map (fun (n, e) => n ++ e)
  let combinedString := String.intercalate "" combined
  let finalNode := match getLast nodes with
                   | some a => a
                   | none => ""
  combinedString ++ finalNode



def removeFirstCharacter (str : String) : String :=
  match str with
  | "" => ""
  | _ => str.drop 1

def generateGraphString (input : AssocList String Sexp) : String
:=
  let input_list := input.toList
  let v_filtered := input_list.filter (fun ⟨fst, _⟩ => fst.startsWith "v")
  let v_num_list := v_filtered.map (fun (a,b) => (removeFirstCharacter (a), b))
  let v_list := v_num_list.map (fun (a,b) => (String.toNat? a, b))
  let v_list_final := sortPairs (v_list)
  let e_filtered := input_list.filter (fun ⟨fst, _⟩ => fst.startsWith "e")
  let e_num_list := e_filtered.map (fun (a,b) => (removeFirstCharacter (a), b))
  let e_list := e_num_list.map (fun (a,b) => (String.toNat? a, b))
  let e_list_final := sortPairs (e_list)
  let final_string := constructString v_list_final e_list_final
  final_string



def gracefulLabelingProblem (n : Nat) : List Sexp :=
sexps!{
    (set-logic QF_LIA)
    (set-option :produce-models true)
    ...{ gracefulLabelingB n |>.toList }
    (check-sat)
    (get-model)
  }

-- TODO: call the solver and print out the solution.


def gracefulLabeling (n : Nat) : IO Unit := do
  let out ← callZ3 (gracefulLabelingProblem n) (verbose := false)
  match out with
  | Sexp.atom "sat" :: m :: _ =>
    let assocList := decodeModelConsts m
    IO.println "Solution:"
    IO.println (generateGraphString (assocList))
  | ss =>
    IO.println "Not SAT. Solver output:"
    IO.println ss

#eval gracefulLabeling 9

/-
Problem 3.
-/

-- More helper functions.

def xmin (i : Nat) := s!"xmin_{i}"
def xmax (i : Nat) := s!"xmax_{i}"
def ymin (i : Nat) := s!"ymin_{i}"
def ymax (i : Nat) := s!"ymax_{i}"

-- TODO: Define the list of constant declarations and assertions that say that
-- the almost squares of orders 1 to m cover the almost square of order n.

def AlmostToSmt (n m : Nat) : List Sexp := Id.run do
  let mut decls : Array Sexp := #[]
  let mut asserts : Array Sexp := #[]

  -- Declare variables for the corners of the almost squares of orders 1 through n.
  for i in [1:n+1] do
    decls := decls.push (sexp!{(declare-const {xmin i} Int)})
    decls := decls.push (sexp!{(declare-const {xmax i} Int)})
    decls := decls.push (sexp!{(declare-const {ymin i} Int)})
    decls := decls.push (sexp!{(declare-const {ymax i} Int)})
  for i in [1:n+1] do
    -- Enforce the height to be n or n+1
    asserts := asserts.push (sexp!{(assert (or (= (- {xmax i} {xmin i} 1) {natConst i})
                                                (= (- {xmax i} {xmin i} 1) {natConst (i+1)})))})
    -- Enforce the width to be n or n+1
    asserts := asserts.push (sexp!{(assert (or (= (- {ymax i} {ymin i} 1) {natConst i})
                                                (= (- {ymax i} {ymin i} 1) {natConst (i+1)})))})
    -- Enforce the correct area, implicitly handled by the height and width constraints

  -- Return the concatenation of declarations and assertions.
  -- Assert no overlap among almost squares -- You might need additional constraints or logic here
  -- This is a simplified representation and may require more complex logic to fully implement overlap checks.

  decls.toList ++ asserts.toList






def String.ljust n s :=
  s ++ "".pushn ' ' (n - s.length)

-- TODO: Write a procedure to print it out

def printAlmostSquare (n m : Nat) (model : Sexp) : IO Unit := do
    IO.println ""

-- Call the SAT solver to construct the almost square.

#eval (do
  let cmds := AlmostToSmt 1 1
  -- Set `verbose := false` to hide SMT-LIB communications
  let out ← callZ3 cmds (verbose := true)
  match out with
  | Sexp.atom "sat" :: m :: _ =>
    IO.println <| decodeModelConsts m
    IO.println "SAT with assignment:"
    for (x, b) in decodeModelConsts m do
      IO.println s!"{x} ↦ {evalNumConst b |>.get!}"
    IO.println "\nResult:"
    printAlmostSquare 8 15 m
  | ss =>
    IO.println "Not SAT. Solver output:"
    IO.println ss

  : IO Unit)

-- TODO: Define the bitvector-based encoding.

def almostToSmtBv (n m : Nat) : List Sexp :=
sexps!{()}

-- Call the SAT solver to construct the result square.

#eval (do
  let cmds := almostToSmtBv 8 15
  -- Set `verbose := false` to hide SMT-LIB communications
  let out ← callZ3 cmds (verbose := true)
  match out with
  | Sexp.atom "sat" :: m :: _ =>
    IO.println "SAT with assignment:"
    for (x, b) in decodeModelConsts m do
      IO.println s!"{x} ↦ {evalNumConst b |>.get!}"
    IO.println "\nResult:"
    printAlmostSquare 8 15 m
  | ss =>
    IO.println "Not SAT. Solver output:"
    IO.println ss

  : IO Unit)
