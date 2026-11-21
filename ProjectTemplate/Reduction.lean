import ProjectTemplate.SAT
import ProjectTemplate.Clique

namespace Reduction

-- Each vertex represents one literal occurrence in the formula by storing the
-- clause index and the literal index in the clause
structure Vertex (formula : SAT.Formula) where
  clauseIndex : Fin (List.length formula)
  literalPosition : Fin 3
  deriving DecidableEq

-- Retrieve the literal represented by a vertex.
def literalAt (formula : SAT.Formula) (vertex : Vertex formula) : SAT.Literal :=
  let clause : SAT.Clause := List.get formula (vertex.clauseIndex)
  clause (vertex.literalPosition)

-- Two literals contradict each other when they are the negation of the other
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

-- Two if first contradicts second, second contradicts first
lemma contradictory_symm {first second : SAT.Literal}
    (h : Contradictory first second) :
    Contradictory second first := by
  cases first with
  | pos a =>
      cases second with
      | pos b =>
          change False at h
          exact False.elim h
      | neg b =>
          change a = b at h
          change b = a
          exact Eq.symm h
  | neg a =>
      cases second with
      | pos b =>
          change a = b at h
          change b = a
          exact Eq.symm h
      | neg b =>
          change False at h
          exact False.elim h

-- Two literals do not contradict each other and can be connected in the graph.
lemma not_contradictory_of_eval_eq_true (assignment : SAT.Assignment)
    {first second : SAT.Literal}
    (hfirst : SAT.Literal.eval assignment first = true)
    (hsecond : SAT.Literal.eval assignment second = true) :
    ¬ Contradictory first second := by
  intro hcontr
  cases first with
  | pos a =>
      cases second with
      | pos b =>
          change False at hcontr
          exact False.elim hcontr
      | neg b =>
          change a = b at hcontr
          subst b
          change assignment a = true at hfirst
          change (!assignment a) = true at hsecond
          rw [hfirst] at hsecond
          -- hsecond now says false = true.
          cases hsecond
  | neg a =>
      cases second with
      | pos b =>
          change a = b at hcontr
          subst b
          change (!assignment a) = true at hfirst
          change assignment a = true at hsecond
          rw [hsecond] at hfirst
          -- hfirst now says false = true.
          cases hfirst
      | neg b =>
          change False at hcontr
          exact False.elim hcontr

-- Literal occurrences are adjacent when they are from different clauses and don't contradict.
def reductionGraph (formula : SAT.Formula) : SimpleGraph (Vertex formula) where
  -- Define rule for adjacency.
  Adj first second := first.clauseIndex ≠ second.clauseIndex ∧
    ¬ Contradictory (literalAt formula first) (literalAt formula second)
  -- Proof that adjacency is symmetric.
  symm := by
    constructor
    intro first second h
    exact ⟨h.1.symm, fun hcontr ↦ h.2 (contradictory_symm hcontr)⟩
  -- Proof that no vertex is adjacent to itself.
  loopless := by
    constructor
    intro vertex h
    exact h.1 rfl

lemma clauseIndex_ne_of_adj {formula : SAT.Formula} {first second : Vertex formula}
    (h : (reductionGraph formula).Adj first second) : first.clauseIndex ≠ second.clauseIndex :=
  h.1

end Reduction
