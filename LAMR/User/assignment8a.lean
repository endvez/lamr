import LAMR.Util.FirstOrder
open Std
open FOTerm

partial def collectVars : FOTerm → List String
  | var x => [x]
  | app _ args => args.foldl (fun acc term => acc.union (collectVars term)) []

def collectRhsVars (eqs : List (FOTerm × FOTerm)) : List String :=
  eqs.foldl (fun acc (_, rhs) => acc.union (collectVars rhs)) []

-- Implement this.
-- You can use `x ∈ forbidden` to check if a string `x` is in the list `forbidden`.
-- You can use `s == t` for the Boolean equality test between terms.
partial def match_aux? (forbidden : List String) (env : AssocList String FOTerm) :
      List (FOTerm × FOTerm) → Option (AssocList String FOTerm)
  | [] => some env
  | (var x, t) :: eqs =>
    if x ∈ forbidden then
      if t == var x then match_aux? forbidden env eqs
      else none
    else match env.find? x with
      | some t' => if t == t' then match_aux? forbidden env eqs else none
      | none => match_aux? forbidden (env.cons x t) eqs
    | (app f1 l1, app f2 l2) :: eqs =>
      if f1 == f2 && List.length l1 == List.length l2 then
        match_aux? forbidden env (List.zip l1 l2 ++ eqs)
      else none
    | _ => none

def match? (eqs : List (FOTerm × FOTerm)) :=
  match_aux? (collectRhsVars eqs) AssocList.nil eqs

partial def matchAndApply (eqs : List (FOTerm × FOTerm)) : Option (List (FOTerm × FOTerm)) :=
  match match? eqs with
    | some l => let σ : FOAssignment FOTerm := l
                eqs.map (fun (s, t) => (subst σ s, subst σ t))
    | none   => none

-- no match
def ex1 := [ (term!{ f(%x, g(%y))}, term!{ f(f(%z), %w) }) ]

#eval toString <| match? ex1
#eval toString <| matchAndApply ex1

-- has a match
def ex2 := [ (term!{ f(%x, %y)}, term!{ f(f(%z), g(%w)) }) ]

#eval toString <| match? ex2
#eval toString <| matchAndApply ex2

-- no match
def ex3 := [ (term!{ f(%x, %y) }, term!{ f(%y, %x) }) ]

#eval toString <| match? ex3
#eval toString <| matchAndApply ex3

-- has a match
def ex4 := [ (term!{ f(g(%x0), %x1) }, term!{ f(g(%x2), a) }) ]

#eval toString <| match? ex4
#eval toString <| matchAndApply ex4

-- has a match
def ex5 := [ (term!{ f(%x0) }, term!{ f(%x2) }),
             (term!{ f(%x1) }, term!{ f(%x2) }),
             (term!{ f(%x2) }, term!{ f(%x2) }),
             (term!{ f(%x3) }, term!{ f(%x2) })]

#eval toString <| match? ex5
#eval toString <| matchAndApply ex5
