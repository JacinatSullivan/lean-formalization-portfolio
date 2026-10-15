import Mathlib

/-!
# Lean Formalization Portfolio: Graph Connectivity and Hamiltonian Cycles

This file is a portfolio-style exercise in expressing graph-theoretic concepts
with Lean 4 and Mathlib. It introduces definitions for spanning subgraphs,
2-regularity, and a uniquely specified witness.

Important: these are illustrative definitions, not a claim that a major
open graph-theory result has been proved here. Compile this file in the same
Lean/Mathlib version used by your project before publishing it.
-/

namespace GraphFormalizationPortfolio

/--
`SpanningSubgraph H G` means that `H` is a subgraph of `G` with the same
vertex type. Since both graphs are defined on `V`, the subgraph is spanning
when every edge of `H` is also an edge of `G`; the vertex set is shared.
-/
def SpanningSubgraph {V : Type*} (H G : SimpleGraph V) : Prop :=
  H ≤ G

/--
A graph is 2-regular if every vertex has degree two.
The finite-type assumption lets Mathlib interpret vertex degrees as finite
natural numbers.
-/
def Is2Regular {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ v : V, G.degree v = 2

/--
A graph `G` has a unique 2-regular spanning subgraph if there is exactly one
subgraph `H` of `G` that is 2-regular.

This is a useful formalization pattern: existence plus uniqueness (`∃!`)
makes the intended witness explicit.
-/
def HasUniqueTwoRegularSpanningSubgraph
    {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃! H : SimpleGraph V,
    SpanningSubgraph H G ∧ Is2Regular H

/--
Any witness supplied by the unique-subgraph property is a subgraph of `G`
and satisfies the 2-regularity condition.
-/
theorem unique_subgraph_has_required_properties
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (h : HasUniqueTwoRegularSpanningSubgraph G) :
    ∃ H : SimpleGraph V,
      SpanningSubgraph H G ∧ Is2Regular H := by
  rcases h with ⟨H, hH, _hUnique⟩
  exact ⟨H, hH⟩

/--
The uniqueness part of `∃!` states that any other qualifying subgraph equals
the chosen witness. This theorem extracts that property from the definition.
-/
theorem qualifying_subgraph_is_unique
    {V : Type*} [Fintype V] (G H K : SimpleGraph V)
    (h : HasUniqueTwoRegularSpanningSubgraph G)
    (hH : SpanningSubgraph H G ∧ Is2Regular H)
    (hK : SpanningSubgraph K G ∧ Is2Regular K) :
    H = K := by
  rcases h with ⟨W, hW, hUnique⟩
  have hHW : H = W := hUnique H hH
  have hKW : K = W := hUnique K hK
  exact hHW.trans hKW.symm

end GraphFormalizationPortfolio
