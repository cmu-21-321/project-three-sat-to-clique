import ProjectTemplate.Reduction

/-!
# Correctness of the 3SAT-to-CLIQUE reduction

A formula is satisfiable exactly when its reduction graph has a clique
whose size is the number of clauses. The proof handles the empty formula too.
-/

namespace Reduction

/-! ## Forward direction: a satisfying assignment gives a clique -/

-- A satisfying assignment lets us choose a true literal position in every clause.
lemma exists_true_literal_positions (formula : SAT.Formula) (assignment : SAT.Assignment)
    (h : formula.Satisfied assignment) :
    ∃ positions : Fin formula.length → Fin 3,
      ∀ i, SAT.Literal.eval assignment (formula.get i (positions i)) = true := by
  have hclause (i : Fin formula.length) :
      ∃ position : Fin 3, SAT.Literal.eval assignment (formula.get i position) = true :=
    h (formula.get i) (List.get_mem formula i)
  -- Turn a separate existence proof for each clause into one function of choices.
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
  -- Choices from different clauses are different vertices, even if their literals agree.
  have hinj : Function.Injective choose := fun _ _ heq ↦ congrArg Vertex.clauseIndex heq
  refine ⟨Finset.univ.image choose, ?_, ?_⟩
  -- First prove pairwise adjacency, then prove that there are exactly formula.length vertices.
  · simpa [choose] using isClique_range_of_eval_eq_true formula assignment positions hpositions
  · rw [Finset.card_image_of_injective _ hinj]
    simp

/-! ## Reverse direction: a clique of the target size gives a satisfying assignment -/

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
  -- The clause-index map is injective on the clique. Since there are as many
  -- selected vertices as clause indices, the map must also be surjective.
  have hsurj := Finset.surjOn_of_injOn_of_card_le Vertex.clauseIndex
    (s := vertices) (t := Finset.univ) (fun _ _ ↦ Finset.mem_univ _)
    (clauseIndex_injOn_of_isClique h.isClique) (by simp [h.card_eq])
  exact hsurj (Finset.mem_univ i)

-- Set a variable to true exactly when a positive occurrence is selected.
-- Variables without a selected positive occurrence are assigned false.
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
    -- This vertex itself witnesses that the variable should be assigned true.
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
      -- These distinct selected vertices would have to be adjacent, but their
      -- opposite literals contradict the graph's adjacency condition.
      exact (h hother hvertex hne).2 (by simp [Contradictory, hpos, hlit])
    simp [SAT.Literal.eval, assignmentFromClique, hnone]

-- A clique of the target size gives an assignment satisfying every clause.
theorem satisfiable_of_exists_clique (formula : SAT.Formula)
    (h : ∃ vertices, (reductionGraph formula).IsNClique formula.length vertices) :
    formula.Satisfiable := by
  obtain ⟨vertices, hvertices⟩ := h
  refine ⟨assignmentFromClique formula vertices, ?_⟩
  intro clause hclause
  -- Convert list membership into a clause index, then find the selected vertex there.
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hclause
  obtain ⟨vertex, hvertex, hindex⟩ := exists_vertex_of_isNClique hvertices i
  refine ⟨vertex.literalPosition, ?_⟩
  have htrue := eval_assignmentFromClique_eq_true hvertices.isClique hvertex
  simpa [literalAt, hindex] using htrue

/-! ## Combine both directions and connect to the project's clique definition -/

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
  -- The intermediate proofs use Mathlib's IsNClique. Here we translate its
  -- pairwise-adjacency and cardinality fields into the project's HasClique predicate.
  rw [satisfiable_iff_exists_clique]
  constructor
  · rintro ⟨vertices, h⟩
    exact ⟨vertices, fun first second hfirst hsecond hne ↦ h.isClique hfirst hsecond hne,
      h.card_eq⟩
  · rintro ⟨vertices, hclique, hcard⟩
    exact ⟨vertices, ⟨fun first hfirst second hsecond hne ↦
      hclique first second hfirst hsecond hne, hcard⟩⟩

end Reduction
