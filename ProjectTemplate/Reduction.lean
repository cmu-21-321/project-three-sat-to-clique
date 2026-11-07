import ProjectTemplate.SAT
import ProjectTemplate.Clique

namespace Reduction

-- Each vertex represents one literal occurrence in the formula.
-- Its clause index identifies a clause, and its literal position
-- identifies one of the three slots within that clause.
structure Vertex (formula : SAT.Formula) where
  -- A valid clause index, starting at 0.
  clauseIndex : Fin (List.length formula)
  -- A position within the clause: 0, 1, or 2.
  literalPosition : Fin 3
  -- Automatically provides a way to decide whether two vertices are equal.
  deriving DecidableEq

-- Retrieve the literal represented by a vertex.
def literalAt (formula : SAT.Formula) (vertex : Vertex formula) : SAT.Literal :=
  -- First, retrieve the clause identified by the vertex.
  let clause : SAT.Clause := List.get formula (vertex.clauseIndex)
  -- Then, retrieve the literal at the vertex's position in that clause.
  clause (vertex.literalPosition)

-- Two literals contradict each other when they refer to the same
-- variable but have opposite signs.
def Contradictory (first : SAT.Literal) (second : SAT.Literal) : Prop :=
  match first, second with
  | SAT.Literal.pos firstVar, SAT.Literal.neg secondVar =>
      firstVar = secondVar
  | SAT.Literal.neg firstVar, SAT.Literal.pos secondVar =>
      firstVar = secondVar
  | SAT.Literal.pos _, SAT.Literal.pos _ =>
      False
  | SAT.Literal.neg _, SAT.Literal.neg _ =>
      False

lemma contradictory_symm {first second : SAT.Literal} (h : Contradictory first second) :
    Contradictory second first := by
  cases first <;> cases second <;> simp_all [Contradictory]

-- Two literals that are true under one assignment cannot contradict each other.
lemma not_contradictory_of_eval_eq_true (assignment : SAT.Assignment)
    {first second : SAT.Literal} (hfirst : SAT.Literal.eval assignment first = true)
    (hsecond : SAT.Literal.eval assignment second = true) : ¬ Contradictory first second := by
  intro hcontr
  cases first <;> cases second <;> simp_all [Contradictory, SAT.Literal.eval]

-- Literal occurrences are adjacent when they lie in different clauses and do not contradict.
def reductionGraph (formula : SAT.Formula) : SimpleGraph (Vertex formula) where
  Adj first second := first.clauseIndex ≠ second.clauseIndex ∧
    ¬ Contradictory (literalAt formula first) (literalAt formula second)
  symm := by
    constructor
    intro first second h
    exact ⟨h.1.symm, fun hcontr ↦ h.2 (contradictory_symm hcontr)⟩
  loopless := by
    constructor
    intro vertex h
    exact h.1 rfl

lemma clauseIndex_ne_of_adj {formula : SAT.Formula} {first second : Vertex formula}
    (h : (reductionGraph formula).Adj first second) : first.clauseIndex ≠ second.clauseIndex :=
  h.1

-- A satisfying assignment lets us choose a true literal position in every clause.
lemma exists_true_literal_positions (formula : SAT.Formula) (assignment : SAT.Assignment)
    (h : formula.Satisfied assignment) :
    ∃ positions : Fin formula.length → Fin 3,
      ∀ i, SAT.Literal.eval assignment (formula.get i (positions i)) = true := by
  have hclause (i : Fin formula.length) :
      ∃ position : Fin 3, SAT.Literal.eval assignment (formula.get i position) = true :=
    h (formula.get i) (List.get_mem formula i)
  exact Classical.axiomOfChoice hclause

-- Choosing a true literal in each clause gives a clique of literal occurrences.
lemma isClique_range_of_eval_eq_true (formula : SAT.Formula) (assignment : SAT.Assignment)
    (positions : Fin formula.length → Fin 3)
    (h : ∀ i, SAT.Literal.eval assignment (formula.get i (positions i)) = true) :
    (reductionGraph formula).IsClique
      (Set.range fun i ↦ (⟨i, positions i⟩ : Vertex formula)) := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
  constructor
  · intro hij
    exact hne (by cases hij; rfl)
  · exact not_contradictory_of_eval_eq_true assignment (h i) (h j)

end Reduction
