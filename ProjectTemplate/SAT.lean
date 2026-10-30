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

-- A clause is satisfied if at least one literal is true.
def Clause.Satisfied (clause : Clause) (assignment : Assignment) : Prop :=
  ∃ position : Fin 3, Literal.eval assignment (clause position) = true


-- A formula is satisfied if every clause is satisfied.
def Formula.Satisfied (formula : Formula) (assignment : Assignment) : Prop :=
  ∀ clause ∈ formula, clause.Satisfied assignment

-- A formula is satisfiable if some assignment satisfies it.
def Formula.Satisfiable (formula : Formula) : Prop :=
  ∃ assignment : Assignment, formula.Satisfied assignment

-- A variable and its negation cannot both be true under the same assignment.
lemma positive_and_negative_cannot_both_be_true
    (assignment : Assignment) (var : Variable) :
    ¬ (Literal.eval assignment (Literal.pos var) = true ∧
       Literal.eval assignment (Literal.neg var) = true) := by
  -- To prove the negation, assume both literals are true and derive False.
  intro bothTrue

  -- Extract the left side of the conjunction: the positive literal is true.
  have positiveTrue : Literal.eval assignment (Literal.pos var) = true :=
    And.left bothTrue

  -- Extract the right side: the negative literal is also true.
  have negativeTrue : Literal.eval assignment (Literal.neg var) = true :=
    And.right bothTrue

  -- Restate each assumption using the definition of literal evaluation.
  change assignment var = true at positiveTrue
  change (!(assignment var)) = true at negativeTrue

  -- Replace assignment var with true in negativeTrue.
  rw [positiveTrue] at negativeTrue

  -- The impossible equality false = true proves False and finishes the proof.
  contradiction

end SAT
