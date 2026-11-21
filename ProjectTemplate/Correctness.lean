import ProjectTemplate.Reduction

/-!
# Correctness of the 3SAT-to-CLIQUE reduction

A formula is satisfiable exactly when its reduction graph has a clique
whose size is the number of clauses.
-/

namespace Reduction

-- A satisfying assignment lets us choose a true literal in every clause.
lemma exists_true_literal_positions
    (formula : SAT.Formula) (assignment : SAT.Assignment)
    (h : formula.Satisfied assignment) :
    ∃ positions : Fin formula.length → Fin 3,
    ∀ i, SAT.Literal.eval assignment
      (formula.get i (positions i)) = true := by
  have hclause : ∀ i : Fin formula.length,
      ∃ position : Fin 3,
        SAT.Literal.eval assignment
          (formula.get i position) = true := by
    intro i
    exact h (formula.get i) (List.get_mem formula i)
  -- Choice combines existence per clause into a function.
  exact Classical.axiomOfChoice hclause

-- The chosen true literal occurrences form a clique.
lemma isClique_range_of_eval_eq_true
    (formula : SAT.Formula) (assignment : SAT.Assignment)
    (positions : Fin formula.length → Fin 3)
    (h : ∀ i, SAT.Literal.eval assignment
      (formula.get i (positions i)) = true) :
    (reductionGraph formula).IsClique
      (Set.range fun i ↦ (⟨i, positions i⟩ : Vertex formula)) := by
  intro first hfirst second hsecond hne
  rcases hfirst with ⟨i, hi⟩
  rcases hsecond with ⟨j, hj⟩
  subst first
  subst second
  constructor
  · -- Equal clause indices would give the same chosen vertex.
    intro hij
    apply hne
    cases hij
    rfl
  · exact not_contradictory_of_eval_eq_true assignment (h i) (h j)

-- There is exactly one chosen vertex per clause.
theorem exists_clique_of_satisfied
    (formula : SAT.Formula) (assignment : SAT.Assignment)
    (h : formula.Satisfied assignment) :
    ∃ vertices,
      (reductionGraph formula).IsNClique formula.length vertices := by
  classical
  rcases exists_true_literal_positions formula assignment h with
    ⟨positions, hpositions⟩
  let choose : Fin formula.length → Vertex formula :=
    fun i ↦ ⟨i, positions i⟩

  have hinj : Function.Injective choose := by
    intro i j heq
    have hindices :
        (choose i).clauseIndex = (choose j).clauseIndex := by
      exact congrArg Vertex.clauseIndex heq
    exact hindices

  apply Exists.intro (Finset.univ.image choose)
  constructor
  · simpa [choose] using
      isClique_range_of_eval_eq_true
        formula assignment positions hpositions
  · rw [Finset.card_image_of_injective _ hinj]
    simp

-- A clique contains at most one vertex from each clause.
lemma clauseIndex_injOn_of_isClique
    {formula : SAT.Formula} {vertices : Finset (Vertex formula)}
    (h : (reductionGraph formula).IsClique vertices) :
    Set.InjOn Vertex.clauseIndex (vertices : Set (Vertex formula)) := by
  intro first hfirst second hsecond heq
  by_contra hne
  have hadj : (reductionGraph formula).Adj first second := by
    exact h hfirst hsecond hne
  have hindices : first.clauseIndex ≠ second.clauseIndex := by
    exact clauseIndex_ne_of_adj hadj
  exact hindices heq

-- A clique with as many vertices as clauses meets every clause.
lemma exists_vertex_of_isNClique
    {formula : SAT.Formula} {vertices : Finset (Vertex formula)}
    (h : (reductionGraph formula).IsNClique formula.length vertices)
    (i : Fin formula.length) :
    ∃ vertex ∈ vertices, vertex.clauseIndex = i := by
  -- Every vertex's clause index belongs to the set of all clause indices.
  have hmaps : Set.MapsTo Vertex.clauseIndex
      (vertices : Set (Vertex formula))
      (Finset.univ : Finset (Fin formula.length)) := by
    intro vertex hvertex
    exact Finset.mem_univ vertex.clauseIndex
  have hinj : Set.InjOn Vertex.clauseIndex
      (vertices : Set (Vertex formula)) := by
    exact clauseIndex_injOn_of_isClique h.isClique
  have hsize :
      (Finset.univ : Finset (Fin formula.length)).card ≤ vertices.card := by
    rw [h.card_eq]
    simp
  -- An injection between these equally sized finite sets is surjective.
  have hsurj : Set.SurjOn Vertex.clauseIndex
      (vertices : Set (Vertex formula))
      (Finset.univ : Finset (Fin formula.length)) := by
    exact Finset.surjOn_of_injOn_of_card_le
      Vertex.clauseIndex hmaps hinj hsize
  exact hsurj (Finset.mem_univ i)

-- A variable is true exactly when a positive occurrence is selected.
def assignmentFromClique (formula : SAT.Formula)
    (vertices : Finset (Vertex formula)) : SAT.Assignment :=
  fun var ↦ decide (∃ vertex ∈ vertices, literalAt formula vertex = .pos var)

-- Every selected literal is true under this assignment.
lemma eval_assignmentFromClique_eq_true
    {formula : SAT.Formula} {vertices : Finset (Vertex formula)}
    (h : (reductionGraph formula).IsClique vertices)
    {vertex : Vertex formula} (hvertex : vertex ∈ vertices) :
    SAT.Literal.eval (assignmentFromClique formula vertices)
      (literalAt formula vertex) = true := by
  classical
  cases hlit : literalAt formula vertex with
  | pos var =>
      -- This vertex witnesses the existence of a selected positive occurrence.
      have hpos : ∃ v ∈ vertices, literalAt formula v = .pos var := by
        apply Exists.intro vertex
        constructor
        · exact hvertex
        · exact hlit
      simp [SAT.Literal.eval, assignmentFromClique, hpos]
  | neg var =>
      -- A selected negative occurrence rules out a positive one.
      have hnone : ¬ ∃ v ∈ vertices, literalAt formula v = .pos var := by
        intro hexists
        rcases hexists with ⟨other, hother, hpos⟩
        have hne : other ≠ vertex := by
          intro heq
          subst other
          rw [hlit] at hpos
          cases hpos
        have hadj : (reductionGraph formula).Adj other vertex := by
          exact h hother hvertex hne
        have hcompatible :
            ¬ Contradictory (literalAt formula other)
              (literalAt formula vertex) := by
          exact hadj.2
        have hcontr :
            Contradictory (literalAt formula other)
              (literalAt formula vertex) := by
          rw [hpos, hlit]
          change var = var
          rfl
        exact hcompatible hcontr
      simp [SAT.Literal.eval, assignmentFromClique, hnone]

-- Every clause contains a selected literal, and that literal is true.
theorem satisfiable_of_exists_clique (formula : SAT.Formula)
    (h : ∃ vertices,
      (reductionGraph formula).IsNClique formula.length vertices) :
    formula.Satisfiable := by
  rcases h with ⟨vertices, hvertices⟩
  use assignmentFromClique formula vertices
  intro clause hclause
  -- Find this clause's index in the formula.
  rcases List.mem_iff_get.mp hclause with ⟨i, hi⟩
  subst clause
  -- Find the clique's vertex in that clause.
  rcases exists_vertex_of_isNClique hvertices i with
    ⟨vertex, hvertex, hindex⟩
  use vertex.literalPosition
  have htrue :
      SAT.Literal.eval (assignmentFromClique formula vertices)
        (literalAt formula vertex) = true := by
    exact eval_assignmentFromClique_eq_true hvertices.isClique hvertex
  simpa [literalAt, hindex] using htrue

-- Combine the forward and reverse directions.
theorem satisfiable_iff_exists_clique (formula : SAT.Formula) :
    formula.Satisfiable ↔
      ∃ vertices,
        (reductionGraph formula).IsNClique formula.length vertices := by
  constructor
  · intro hsatisfied
    rcases hsatisfied with ⟨assignment, hassignment⟩
    exact exists_clique_of_satisfied formula assignment hassignment
  · intro hclique
    exact satisfiable_of_exists_clique formula hclique

-- Express the same result using the project's HasClique definition.
theorem satisfiable_iff_hasClique (formula : SAT.Formula) :
    formula.Satisfiable ↔
      Clique.HasClique (Vertex formula)
        (reductionGraph formula) formula.length := by
  rw [satisfiable_iff_exists_clique]
  constructor
  · intro hexists
    rcases hexists with ⟨vertices, h⟩
    use vertices
    constructor
    · intro first second hfirst hsecond hne
      exact h.isClique hfirst hsecond hne
    · exact h.card_eq
  · intro hexists
    rcases hexists with ⟨vertices, hclique, hcard⟩
    apply Exists.intro vertices
    constructor
    · intro first hfirst second hsecond hne
      exact hclique first second hfirst hsecond hne
    · exact hcard

end Reduction
