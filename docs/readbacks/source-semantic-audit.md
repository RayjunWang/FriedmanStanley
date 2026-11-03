# Source and declaration audit

This is a semantic comparison, not a proof of any open target. It was
performed with access to both the manuscript and the Lean declarations;
it is separate from the blind read-backs.

## Main target

`FSCofinality.theorem1_2` matches the three assertions of the manuscript's
Theorem 1.2 (`thm:main`, lines 130–143): one fixed countable language and
one isomorphism-invariant Borel class receive all countable levels, graph
isomorphism does not reduce to that class, and the bounded-tree family is
also dominated.

- The language is existentially chosen once, before all ordinal
  quantifiers. Its symbol set is genuinely countable. Relational symbols
  include arity zero. Using a relational language is compatible with the
  manuscript's permitted graph coding of functions and constants.
- Structures have domain `ℕ` and the actual truth-table product topology.
  `MeasurableSet K` therefore means that the class of structures is Borel.
  It does not impose Borelness on the isomorphism graph.
- `Isomorphic` uses one permutation of the entire domain, preserving every
  relation coordinate. `IsInvariant` expresses closure under these
  isomorphisms.
- `classRelation L K` has carrier the subtype `K` and its inherited
  measurable structure. Reductions land in the class, rather than merely
  in the ambient structure space.
- The graph benchmark consists of actual symmetric, irreflexive Boolean
  adjacency tables on `ℕ`. Its isomorphisms are actual domain
  permutations. Nonreducibility is the negation of an everywhere
  preserving-and-reflecting measurable reduction.
- `a < Ordinal.omega 1` expresses the countable ordinal range, including
  zero for the Friedman–Stanley tower. The tree clause additionally
  requires `0 < a`.
- Quantifier order is `∀ a, ∃ reduction`, inside one chosen target class.
  No Borel selection of reductions across ordinal codes is imposed.

## Concrete hierarchy

`fsTower` is an actual ordinal recursion into code spaces. Its zero stage
is equality on Cantor space. A successor code is an option containing an
infinite enumeration, with a distinct empty code; equivalence compares
the enumerated sets of preceding equivalence classes and ignores
repetitions. The option measurable structure is explicitly transported
from the canonical singleton/sequence disjoint sum.

Every countable nonzero limit uses a fixed strictly increasing cofinal
natural sequence and a coordinatewise countable product. Existence and
cofinality of these sequences are proved from Mathlib's ordinal
fundamental-sequence results. Default values at uncountable limits are
outside every main-target ordinal quantifier and outside the recursion
below any such countable ordinal.

This is the manuscript's product-limit presentation `J`, not a claim that
all sum-limit, product-limit, set-jump, and multiset-jump presentations
have identical ordinal indices. The manuscript's Proposition 4.13 and
Lemma 4.14 explain the cofinal comparisons needed for the usual notation.

## Tree codes and the global height convention

Tree codes are prefix-closed subsets of finite natural sequences. Finite
trees, arbitrary countable branching, and the empty tree are permitted.
An isomorphism is a bijection of actual present nodes preserving and
reflecting immediate-child edges. Repeated isomorphic branches remain
different nodes, so branch multiplicities are retained.

`BoundedTree T a` means there is a node labeling by ordinals strictly
below `a` which strictly decreases from parent to immediate child. This
is a global reverse-tree well-founded height bound. Mathematically it is
equivalent to bounding the supremum of `rank(node) + 1` over all nodes:
any such labeling bounds the canonical well-founded node ranks, and
those canonical ranks themselves supply a labeling when that supremum
is at most `a`.

Consequently the empty tree has height zero, the one-node tree has height
one, and a root with finite branches of unbounded finite lengths has
global height `ω + 1`. The existential rank witness does not certify an
ill-founded tree: a branch would yield an infinite descending sequence
of ordinals.

The original Friedman–Stanley PDF describes reverse-order well-founded
rank and explicitly gives rank one to a one-point tree (printed page
899, PDF page 7). Printed page 901 (PDF page 9) explicitly allows finite
trees and fixes `C₀ = {0}` and `C₁ = {0,1}`. A narrow search of the full
PDF's extracted text found no additional explicit rank-recursion formula.
Its child-code discussion states that immediate subtrees of a member at
bound `a` lie at lower bounds; it does not give a separate iff formula at
limit ordinals.

The global-height presentation is consistent with the stated
reverse-order rank convention. Nevertheless, this audit does not certify
same-index identities with every published rank presentation. The
mission should continue to describe a concrete cofinal bounded-height
presentation and refrain from identifying ordinal indices. Domination
of every countable bound is unchanged by the countable reindexings used
to compare the standard bounded-rank presentations.

## Status and source identity

All target theorem bodies remain the explicit open-problem placeholder.
Compilation checks their declarations and the concrete definitions; it
does not verify the manuscript's proposed new proof.

The audited manuscript is `FriedmanStanleyQuestion.tex`, dated
2 November 2026, SHA-256
`10d9e37ebf19c1d873fbc7ccf45ac57e42b7c023f275e9ec8ff3209f9a577624`.
Its stated assurance is internal checking only, with no independent
mathematical verification. The older `FriedmanStanleyCofinality.tex` was
not substituted for the requested revision.
