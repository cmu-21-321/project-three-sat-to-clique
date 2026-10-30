import Mathlib

namespace Clique

-- SimpleGraph Vertex is Mathlib's type for an undirected graph
-- with vertices of type Vertex and no edges from a vertex to itself.
-- graph.Adj first second states that two vertices are connected.

-- A finite set of vertices is a clique if every two distinct vertices in that set are connected.
def IsClique (Vertex : Type) (graph : SimpleGraph Vertex) (vertices : Finset Vertex) : Prop :=
  ∀ first : Vertex, ∀ second : Vertex,
    first ∈ vertices →
    second ∈ vertices →
    first ≠ second →
    graph.Adj first second

-- A graph has a clique of size k if some clique contains exactly k vertices.
def HasClique (Vertex : Type) (graph : SimpleGraph Vertex) (k : Nat) : Prop :=
  ∃ vertices : Finset Vertex, IsClique Vertex graph vertices ∧ Finset.card vertices = k

-- Any subset of a clique is also a clique.
lemma subset_of_clique_is_clique
    (Vertex : Type) (graph : SimpleGraph Vertex)
    (smaller : Finset Vertex) (larger : Finset Vertex)
    (subsetProof : smaller ⊆ larger)
    (cliqueProof : IsClique Vertex graph larger) :
    IsClique Vertex graph smaller := by
    unfold IsClique
    intro first second firstInSmaller secondInSmaller different
    have firstInLarger : first ∈ larger := subsetProof firstInSmaller
    have secondInLarger : second ∈ larger := subsetProof secondInSmaller
    unfold IsClique at cliqueProof
    exact cliqueProof first second firstInLarger secondInLarger different

end Clique
