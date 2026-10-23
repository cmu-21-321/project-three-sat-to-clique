import Mathlib

namespace SAT

-- Variables are identified by natural numbers.
abbrev Variable := Nat

-- A literal is a variable or its negation.
inductive Literal where
  | pos : Variable → Literal
  | neg : Variable → Literal
  deriving DecidableEq, Repr

-- An assignment gives each variable a truth value.
abbrev Assignment := Variable → Bool

-- A 3SAT clause contains exactly three literal occurrences.
-- Fin 3 is the type of natural numbers 0,1,2
abbrev Clause := Fin 3 → Literal

-- A formula is a conjunction of clauses.
abbrev Formula := List Clause

-- Function to check evaluation of a literal given an assignment
def Literal.eval (assignment : Assignment) (literal : Literal) : Bool :=
  match literal with
  | .pos v => assignment v
  | .neg v => !(assignment v)

-- Example how Literal.eval is used
def exampleAssignment : Assignment :=
  fun v => true

#eval Literal.eval exampleAssignment (Literal.pos 1) -- true
#eval Literal.eval exampleAssignment (Literal.neg 1) -- false
#eval Literal.eval exampleAssignment (Literal.pos 2) -- true
#eval Literal.eval exampleAssignment (Literal.neg 2) -- false

end SAT
