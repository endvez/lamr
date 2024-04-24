import LAMR


def evalLit (τ : PropAssignment) : Lit → Option Bool
| Lit.tr => some true
| Lit.fls => some false
| Lit.pos s => τ.lookup s
| Lit.neg s => (τ.lookup s).map (not)


def clauseSatisfied (τ : PropAssignment) (clause : Clause) : Bool :=
  clause.any (λ lit => match evalLit τ lit with
                        | some true => true
                        | _ => false)

def isLitTouched (τ : PropAssignment) (lit : Lit) : Bool :=
  match lit with
  | Lit.pos s => τ.any (λ (v : String × Bool) => v.fst = s)
  | Lit.neg s => τ.any (λ (v : String × Bool) => v.fst = s)
  | _ => false


def isAutarky (τ : PropAssignment) (Γ : CnfForm) : Bool :=
  Γ.all (λ clause =>
           let touched := clause.any (λ lit => isLitTouched τ lit)
           let satisfied := clauseSatisfied τ clause
           not touched || satisfied)

#eval isAutarky [] cnf!{p q r, -p -q -r} == true
#eval isAutarky propassign!{p} cnf!{p q r, -p -q -r} == false
#eval isAutarky propassign!{p} cnf!{p q r, -q -r} == true
#eval isAutarky propassign!{p, -q} cnf!{p q r, -p -q -r} == true
#eval isAutarky propassign!{-q} cnf!{-p -q -r} == true
#eval isAutarky propassign!{-q} [] == true
#eval isAutarky (propassign!{p, q, -u, -r}) (cnf!{p q u -v, -u, -r, ⊥, ⊤}) == true
#eval isAutarky (propassign!{p, -q, v}) (cnf!{p q u -v, -u, u, -v}) == false
#eval isAutarky (propassign!{p, -q, v, w, a, b, c, d}) (cnf!{p q u -v, -u, u}) == true

def negOfLitInList : Lit → List Lit → Bool
| Lit.pos s, lits => lits.any (λ lit => match lit with | Lit.neg t => s = t | _ => false)
| Lit.neg s, lits => lits.any (λ lit => match lit with | Lit.pos t => s = t | _ => false)
| _, _ => false

def getAllLiterals (Γ : CnfForm) : List Lit :=
  Γ.foldl (λ acc clause => acc ++ clause) []


def getPure (Γ : CnfForm) : List Lit :=
  let allLits := getAllLiterals Γ
  allLits.filter (λ lit => not (negOfLitInList lit allLits))

def var (i j c : Nat) : String :=
  s!"x_{i}_{j}_{c}"

def rectangleConstraints (m n k : Nat) : CnfForm :=
  let indices := List.range m;
  let colors := List.range k;

  let colorAssignments : CnfForm := indices.bind (λ i =>
    indices.bind (λ j =>
      let posLits := colors.map (λ c => Lit.pos (var i j c));
      let negPairs := colors.bind (λ c1 =>
        colors.filterMap (λ c2 =>
          if c1 < c2 then some (Lit.neg (var i j c1), Lit.neg (var i j c2)) else none));
      [posLits] ++ negPairs.map (λ (l1, l2) => [l1, l2])
    )
  );


  let noMonochromaticRectangles : CnfForm := indices.bind (λ i1 =>
    indices.bind (λ i2 =>
      if i1 < i2 then
        indices.bind (λ j1 =>
          indices.bind (λ j2 =>
            if j1 < j2 then
              colors.map (λ c =>
                [Lit.neg (var i1 j1 c), Lit.neg (var i1 j2 c), Lit.neg (var i2 j1 c), Lit.neg (var i2 j2 c)])
            else []
          )
        )
      else []
    )
  );

  colorAssignments ++ noMonochromaticRectangles

#eval show IO Unit from do
  let (_, result) ← callCadical <| rectangleConstraints  10 10 3
  match result with
    | SatResult.Unsat _ => IO.println "unsat."
    | SatResult.Sat τ  => IO.println τ.toString

#eval show IO Unit from do
  let (_, result) ← callCadical <| rectangleConstraints  9 12 3
  match result with
    | SatResult.Unsat _ => IO.println "unsat."
    | SatResult.Sat τ  => IO.println τ.toString



def Lit.isPos : Lit → Bool
  | pos _ => true
  | _     => false


def decodeSolution (m n k: Nat) (τ : List Lit) : Except String (Array (Array Nat)) := do
  let mut grid : Array (Array Nat) := mkArray m (mkArray n 0)
  for lit in τ do
    match lit with
    | Lit.pos s =>
      let parts := s.splitOn "_"
      if parts.length = 4 then
        match (parts[1]!.toNat, parts[2]!.toNat, parts[3]!.toNat) with
        | (some i, some j, some c) =>
          if i < m && j < n && c < k then
            grid := grid.set! i (grid[i]!.set! j c)
          else
            Except.error s!"Index out of bounds"
        | _ => Except.error s!"Invalid literal format"
      else
        Except.error "Invalid number of args"
    | _ => continue
  Except.ok grid

def outputSolution (m n k : Nat) (τ : List Lit) : IO Unit :=
  let posLits := τ.filter Lit.isPos
  match decodeSolution m n k posLits with
    | Except.error s => IO.println s!"Error: {s}"
    | Except.ok grid =>
        for i in [:m] do
          for j in [:n] do
            IO.print s!"{grid[i]![j]!} "
          IO.println ""


#eval show IO Unit from do
  let (_, result) ← callCadical <| rectangleConstraints  10 10 3
  match result with
    | SatResult.Unsat _ => IO.println "unsat."
    | SatResult.Sat τ  => outputSolution 10 10 3 τ

#eval show IO Unit from do
  let (_, result) ← callCadical <| rectangleConstraints  9 12 3
  match result with
    | SatResult.Unsat _ => IO.println "unsat."
    | SatResult.Sat τ  => outputSolution 9 12 3 τ

namespace Resolution

/--
The resolution Step.
-/
def resolve (c₁ c₂ : Clause) (var : String) : Clause :=
  (c₁.erase (Lit.pos var)).union' (c₂.erase (Lit.neg var))

/--
A line of a resolution proof is either a hypothesis or the result of a
resolution step.
-/
inductive Step where
  | hyp (clause : Clause) : Step
  | res (var : String) (pos neg : Nat) : Step
deriving Inhabited

def Proof := Array Step deriving Inhabited

-- Ignore this: it is boilerplate to make `GetElem` work.
instance : GetElem Proof Nat Step (fun xs i => i < xs.size) :=
  inferInstanceAs (GetElem (Array Step) _ _ _)

-- determines whether a proof is well-formed
def Proof.wellFormed (p : Proof) : Bool := Id.run do
  for i in [:p.size] do
    match p[i]! with
      | Step.hyp _ => continue
      | Step.res _ pos neg =>
          if i ≤ pos ∨ i ≤ neg then
            return false
  true

-- prints out the proof
def Proof.show (p : Proof) : IO Unit := do
  if ¬ p.wellFormed then
    IO.println "Proof is not well-formed."
    return
  let mut clauses : Array Clause := #[]
  for i in [:p.size] do
    match p[i]! with
      | Step.hyp c =>
          clauses := clauses.push c
          IO.println s!"{i}: hypothesis: {c}"
      | Step.res var pos neg =>
          let resolvent := resolve clauses[pos]! clauses[neg]! var
          clauses := clauses.push resolvent
          IO.println s!"{i}: resolve {pos}, {neg} on {var}: {resolvent}"

end Resolution

section
open Resolution

def ex3 : Proof := #[
  .hyp clause!{p q -r},
  .hyp clause!{-p -q r},
  .hyp clause!{q r -s},
  .hyp clause!{-q -r s},
  .hyp clause!{p r s},
  .hyp clause!{-p -r -s},
  .hyp clause!{-p q s},
  .hyp clause!{p -q -s},
  .res "q" 0 7,
  .res "s" 4 8,
  .res "s" 5 6,
  .res "q" 3 10,
  .res "q" 1 2,
  .res "p" 9 12,
  .res "r" 11 13
]

#eval ex3.wellFormed
#eval ex3.show
