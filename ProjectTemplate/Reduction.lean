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

-- A satisfying assignment produces a clique with one vertex per clause.
theorem exists_clique_of_satisfied (formula : SAT.Formula) (assignment : SAT.Assignment)
    (h : formula.Satisfied assignment) :
    ∃ vertices, (reductionGraph formula).IsNClique formula.length vertices := by
  classical
  obtain ⟨positions, hpositions⟩ := exists_true_literal_positions formula assignment h
  let choose : Fin formula.length → Vertex formula := fun i ↦ ⟨i, positions i⟩
  have hinj : Function.Injective choose := fun _ _ heq ↦ congrArg Vertex.clauseIndex heq
  refine ⟨Finset.univ.image choose, ?_, ?_⟩
  · simpa [choose] using isClique_range_of_eval_eq_true formula assignment positions hpositions
  · rw [Finset.card_image_of_injective _ hinj]
    simp

-- A clique contains at most one vertex from each clause.
lemma clauseIndex_injOn_of_isClique {formula : SAT.Formula} {vertices : Finset (Vertex formula)}
    (h : (reductionGraph formula).IsClique vertices) :
    Set.InjOn Vertex.clauseIndex (vertices : Set (Vertex formula)) := by
  intro first hfirst second hsecond heq
  by_contra hne
  exact (clauseIndex_ne_of_adj (h hfirst hsecond hne)) heq

-- A clique with as many vertices as clauses must meet every clause.
lemma exists_vertex_of_isNClique {formula : SAT.Formula} {vertices : Finset (Vertex formula)}
    (h : (reductionGraph formula).IsNClique formula.length vertices)
    (i : Fin formula.length) : ∃ vertex ∈ vertices, vertex.clauseIndex = i := by
  have hsurj := Finset.surjOn_of_injOn_of_card_le Vertex.clauseIndex
    (s := vertices) (t := Finset.univ) (fun _ _ ↦ Finset.mem_univ _)
    (clauseIndex_injOn_of_isClique h.isClique) (by simp [h.card_eq])
  exact hsurj (Finset.mem_univ i)

-- Set a variable to true exactly when a positive occurrence is selected.
def assignmentFromClique (formula : SAT.Formula)
    (vertices : Finset (Vertex formula)) : SAT.Assignment :=
  fun var ↦ decide (∃ vertex ∈ vertices, literalAt formula vertex = .pos var)

-- Every literal selected by a clique is true under the induced assignment.
lemma eval_assignmentFromClique_eq_true {formula : SAT.Formula}
    {vertices : Finset (Vertex formula)} (h : (reductionGraph formula).IsClique vertices)
    {vertex : Vertex formula} (hvertex : vertex ∈ vertices) :
    SAT.Literal.eval (assignmentFromClique formula vertices) (literalAt formula vertex) = true := by
  classical
  cases hlit : literalAt formula vertex with
  | pos var =>
    have hpos : ∃ v ∈ vertices, literalAt formula v = .pos var := ⟨vertex, hvertex, hlit⟩
    simp [SAT.Literal.eval, assignmentFromClique, hpos]
  | neg var =>
    -- A selected negative literal rules out every positive occurrence of its variable.
    have hnone : ¬ ∃ v ∈ vertices, literalAt formula v = .pos var := by
      rintro ⟨other, hother, hpos⟩
      have hne : other ≠ vertex := by
        intro heq
        subst other
        rw [hlit] at hpos
        cases hpos
      exact (h hother hvertex hne).2 (by simp [Contradictory, hpos, hlit])
    simp [SAT.Literal.eval, assignmentFromClique, hnone]

-- A clique of the target size gives an assignment satisfying every clause.
theorem satisfiable_of_exists_clique (formula : SAT.Formula)
    (h : ∃ vertices, (reductionGraph formula).IsNClique formula.length vertices) :
    formula.Satisfiable := by
  obtain ⟨vertices, hvertices⟩ := h
  refine ⟨assignmentFromClique formula vertices, ?_⟩
  intro clause hclause
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hclause
  obtain ⟨vertex, hvertex, hindex⟩ := exists_vertex_of_isNClique hvertices i
  refine ⟨vertex.literalPosition, ?_⟩
  have htrue := eval_assignmentFromClique_eq_true hvertices.isClique hvertex
  simpa [literalAt, hindex] using htrue

-- The reduction preserves satisfiability in both directions, including the empty formula.
theorem satisfiable_iff_exists_clique (formula : SAT.Formula) :
    formula.Satisfiable ↔
      ∃ vertices, (reductionGraph formula).IsNClique formula.length vertices := by
  constructor
  · rintro ⟨assignment, h⟩
    exact exists_clique_of_satisfied formula assignment h
  · exact satisfiable_of_exists_clique formula

-- The same correctness statement using the project's CLIQUE decision predicate.
theorem satisfiable_iff_hasClique (formula : SAT.Formula) :
    formula.Satisfiable ↔
      Clique.HasClique (Vertex formula) (reductionGraph formula) formula.length := by
  rw [satisfiable_iff_exists_clique]
  constructor
  · rintro ⟨vertices, h⟩
    exact ⟨vertices, fun first second hfirst hsecond hne ↦ h.isClique hfirst hsecond hne,
      h.card_eq⟩
  · rintro ⟨vertices, hclique, hcard⟩
    exact ⟨vertices, ⟨fun first hfirst second hsecond hne ↦
      hclique first second hfirst hsecond hne, hcard⟩⟩

end Reduction
