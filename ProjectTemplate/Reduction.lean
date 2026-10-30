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


end Reduction
