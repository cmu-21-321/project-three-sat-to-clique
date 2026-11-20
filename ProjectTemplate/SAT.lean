import Mathlib
import ImportGraph.Tools.MinImports
--lake exe cache get

namespace SAT

-- Variables are identified by natural numbers.
abbrev Variable := Nat

-- A literal is a variable or its negation.
inductive Literal where
  | pos : Variable → Literal
  | neg : Variable → Literal
  deriving DecidableEq

-- An assignment gives each variable a truth value.
abbrev Assignment := Variable → Bool

-- A 3SAT clause contains three literals.
abbrev Clause := Fin 3 → Literal

-- A formula is a conjunction of clauses.
abbrev Formula := List Clause

-- This function checks evaluation of a literal given an assignment
def Literal.eval (assignment : Assignment) (literal : Literal) : Bool :=
  match literal with
  | .pos v => assignment v
  | .neg v => !(assignment v)

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
lemma positive_and_negative_cannot_both_be_true (assignment : Assignment) (var : Variable) :
    ¬ (Literal.eval assignment (Literal.pos var) = true ∧
       Literal.eval assignment (Literal.neg var) = true) := by
  intro bothTrue
  -- Left and right side of the conjunction
  have positiveTrue : Literal.eval assignment (Literal.pos var) = true := And.left bothTrue
  have negativeTrue : Literal.eval assignment (Literal.neg var) = true := And.right bothTrue
  -- Change positiveTrue and negativeTrue by evaluating Literal.eval
  change assignment var = true at positiveTrue
  change (!(assignment var)) = true at negativeTrue
  -- Replace assignment var with true in negativeTrue.
  rw [positiveTrue] at negativeTrue
  contradiction

end SAT

#min_imports
