# Proof outline

The main declaration is `FSCofinality.theorem1_2`. It constructs one fixed
countable relational language and an isomorphism-invariant Borel class in that
language. Every countable stage of the fixed Friedman–Stanley tower reduces to
isomorphism on this class, while graph isomorphism does not. The original
bounded rooted-tree relations also reduce to it.

## Tower stages as cosets

Fix a countable ordinal. The semantic construction assigns each source point
countable pools of names at the relevant ordinal levels. Dedicated columns
encode the chosen fundamental sequences at limit levels. Generic Boolean
tables turn these names and their membership and profile relations into
countable relational structures with a distinguished coordinate sort.

There are three separate conclusions about these structures. Equivalent source
points have an isomorphism fixing every distinguished coordinate. Conversely,
an isomorphism fixing those coordinates recovers the semantic names, by
induction through ordinary and limit levels, and therefore recovers source
equivalence. Finally, an automorphism fixing every distinguished coordinate is
the identity. These are actual isomorphisms and automorphisms of the constructed
structures, rather than assumptions about an abstract coding scheme.

Every two output structures are isomorphic if the distinguished coordinates
may move. Finite extension arguments establish this common isomorphism type.
Measurable back-and-forth chooses isomorphisms from each output to one base
structure. The countable presentations and the chosen isomorphisms are Borel.

The automorphism group of the base structure is a closed subgroup of the
permutation group. Restriction to the distinguished coordinates is a continuous
homomorphism. The rigidity conclusion makes it injective. Its image is Borel,
by the proved continuous-homomorphism image theorem for Polish groups.
Restricting the chosen isomorphisms and taking their inverses gives the required
coset reduction. The inverses match the fixed convention that two permutations
are related when the inverse of the second times the first lies in the image.

This proves `FSCofinality.coset_cofinality` for each countable ordinal.

## One Borel invariant class

`FSCofinality.MarkedCoding.classSet` is a single Borel invariant class in a
single fixed language. It uses named Cantor parameters and canonical orbit
structures for closed permutation groups. A closed-graph construction encodes
the graph of a continuous homomorphism using two sorts. This proves that every
homomorphic-image coset relation supplied above reduces to this same class.

The construction has Borel isomorphism in each fixed real-parameter fiber.
The invariant-real principle for graph isomorphism says that every Borel
isomorphism-invariant real parameter is constant on the image of some Borel
self-reduction of graph isomorphism. If graph isomorphism reduced to the
constructed class, composing its parameter with this principle would reduce
graph isomorphism to one Borel fiber. That would make graph isomorphism Borel,
contradicting the independently proved graph non-Borelness theorem. Analytic
tree boundedness and fat-padding back-and-forth provide the non-Borelness and
invariant-real results used here.

## Original bounded rooted trees

The final comparison uses actual node isomorphisms of the mission's bounded
rooted trees. Recursive child classification, occurrence-tag multiset coding,
and tower sum and product absorption give a Borel reduction of each countably
bounded tree relation to some countable tower stage. Empty trees and finite
child sets are included. The comparison is cofinal; it does not identify the
same ordinal indices across different hierarchy conventions.

Composing this reduction with tower cofinality proves the final clause of the
main theorem. The three conclusions use the same language and Borel class.

## Kernel verification

`lake env lean AuditAll.lean` reports only `propext`, `Classical.choice`, and
`Quot.sound` for the main theorem and all four supporting mission statements.
The main audit covers its full transitive proof dependency closure.
