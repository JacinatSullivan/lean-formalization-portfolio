import Mathlib

/-!
# Lean Formalization Portfolio: Finite Graphs

-/

namespace LeanPortfolio

/--
A finite simple graph is 4-regular when every vertex has degree four.

`[Fintype V]` supplies finiteness of the vertex type, which Mathlib uses
for finite graph computations and degree-related results.
-/
def Is4Regular {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ v : V, G.degree v = 4

/--
Unpack the definition of 4-regularity at a particular vertex.

This small theorem illustrates how a definition can be used to derive a
specific, formally checked fact.
-/
theorem degree_eq_four
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : Is4Regular G) (v : V) :
    G.degree v = 4 := by
  exact hG v

/--
Two graphs on the same vertex type are equal in their degree at every vertex
if both satisfy the same constant-degree condition.
-/
theorem both_four_regular
    {V : Type*} [Fintype V]
    (G H : SimpleGraph V)
    (hG : Is4Regular G)
    (hH : Is4Regular H)
    (v : V) :
    G.degree v = 4 ∧ H.degree v = 4 := by
  constructor
  · exact hG v
  · exact hH v

end LeanPortfolio

 
