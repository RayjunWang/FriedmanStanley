# Blind read-back: tree declarations

Read-back model: the exact underlying model identifier is not exposed to this auditor. This read-back was made from the tree declarations and their imported structures declarations, without consulting an informal statement or source material.

**`Node`.** A node code is a finite list of natural numbers, including the empty list $[]$.

**`PrefixClosed`.** For a function $t$ from finite lists of natural numbers to Boolean values, prefix closure means that, for every finite list $s$ and every natural number $n$, if $t(s\mathbin{+\!+}[n])$ is true, then $t(s)$ is true; here $s\mathbin{+\!+}[n]$ is the list obtained by appending the single entry $n$ to $s$. No code is required to have value true, so the everywhere-false function satisfies this condition.

**`TreeSpace`.** A tree is a Boolean-valued function on finite lists of natural numbers together with a proof of the preceding prefix-closure condition. Thus its actual nodes are exactly its true entries. Empty trees, finite trees, and infinite trees are permitted; there is no requirement of finite branching, no requirement of infinitely many nodes, and no well-foundedness requirement in this definition. Every nonempty such tree contains the empty list, and its node set is countable because all node codes are finite lists of natural numbers.

**Topology on `TreeSpace`.** The topology on these trees is the subspace topology inherited from the product of copies of the discrete Boolean space indexed by all finite lists of natural numbers.

**Function coercion for `TreeSpace`.** Evaluating a tree $T$ at a node code $s$ means evaluating its underlying Boolean function at $s$; its stored prefix-closure proof contributes no additional Boolean values.

**`isClosed_prefixClosed`.** Within the product space of all Boolean-valued functions on finite lists of natural numbers, the subset of functions satisfying the stated prefix-closure condition is closed.

**Polish-space instance for `TreeSpace`.** The tree space with the preceding topology is second countable and admits a compatible complete metric.

**Measurable-space instance for `TreeSpace`.** The measurable sets of the tree space are its Borel sets for the preceding topology.

**Borel-space instance for `TreeSpace`.** The specified measurable structure on the tree space equals the Borel measurable structure of its specified topology.

**`Nodes`.** For every tree $T$, the type of actual nodes of $T$ consists of finite lists $s$ together with a proof that $T(s)$ is true. If $T$ is empty this type is empty; no false entry is included as an actual node.

**`Child`.** For every tree $T$ and every pair $s,t$ of actual nodes of that same tree, $s$ is a child of $t$ precisely when there exists a natural number $n$ such that the list underlying $s$ is the list underlying $t$ with $n$ appended. The first argument is the child and the second argument is its immediate parent; this relation does not mean an arbitrary proper descendant.

**`Isomorphic`.** For every two trees $T,U$, they are isomorphic precisely when there exists one bijection $e$ from the entire actual node set of $T$ onto the entire actual node set of $U$ such that, for every ordered pair $s,t$ of actual nodes of $T$, $s$ is a child of $t$ if and only if $e(s)$ is a child of $e(t)$. The bijection is not required to preserve the natural-number entries of the node lists. This is a full bijection preserving and reflecting the immediate-child relation, rather than an embedding or a family of pairwise choices. It includes empty, finite, and infinite node sets: the empty tree is isomorphic to itself, and cannot be isomorphic to a nonempty tree.

**`BoundedTree`.** For every tree $T$ and every ordinal $a$ in the specified small ordinal universe, $T$ is bounded by $a$ precisely when there exists a function $\rho$ assigning an ordinal in that same universe to every actual node of $T$ such that both (i) for every actual node $s$, $\rho(s)<a$, and (ii) for every pair of actual nodes $s,t$, if $s$ is an immediate child of $t$, then $\rho(s)<\rho(t)$. The quantifier over $\rho$ is existential for the given $T,a$; the bounds and strict decrease are universal over all actual nodes and all immediate-child pairs. No countability restriction is imposed on the ordinal $a$ or on the assigned ordinals. The function need not be unique, minimal, or a recursively defined node rank. In particular, leaves are not required to receive zero. This is a strict bound on all node labels, with child labels smaller than parent labels. The empty tree satisfies the condition for every $a$, including zero, since its labeling function has empty domain; a nonempty tree cannot satisfy it for $a=0$. The one-node tree satisfies it exactly when $0<a$, by assigning its sole node zero. Infinite trees are included whenever such a labeling exists, including the tree with a root and infinitely many immediate leaves at bound $2$; a tree with an infinite branch cannot have such a strictly decreasing ordinal labeling. Thus the least possible bound is zero for the empty tree and one for the one-node tree. No separate height function, least-bound function, or equation between a root label and a tree height is defined.

**`treeRelation`.** For every ordinal $a$ in the specified small ordinal universe, the resulting coded relation has as its carrier all trees $T$ together with a proof that there exists an ordinal labeling satisfying the preceding strict global bound $a$ and strict decrease from parent to child. The carrier is a subtype of the actual tree space, and its measurable structure is the native inherited subtype measurable structure: it is generated by intersections with Borel sets of the ambient tree space. This does not assert that the bounded-tree subset is itself Borel or Polish. Two members of this carrier are related precisely when there is one bijection between all their actual nodes preserving and reflecting the immediate-child relation, as defined above; the relation ignores the stored proofs of boundedness. A coded relation here means only a carrier type, a specified measurable structure on it, and a binary proposition-valued relation on it. Its imported definition imposes no additional requirement that the relation have a Borel graph. The ordinal-labeling witness is asserted to exist by carrier membership; it is not a further selected component of a carrier element.

**`emptyTree`.** The specified empty tree assigns false to every finite list of natural numbers and satisfies prefix closure vacuously; it has no actual nodes.

**`oneNodeTree`.** The specified one-node tree assigns true exactly to the empty list and false to every other finite list of natural numbers. Its only actual node is the empty list, and it has no immediate-child pairs.

**`bounded_emptyTree`.** For every ordinal $a$ in the specified small ordinal universe, the everywhere-false tree admits a function from its empty actual node set to ordinals for which every label is strictly below $a$ and every immediate child has a strictly smaller label than its parent; both requirements are vacuous, including when $a=0$.

**`bounded_oneNodeTree`.** The tree whose only actual node is the empty list admits an ordinal labeling with every label strictly below $1$ and with every immediate child strictly below its parent: its sole node is assigned $0$, and there are no immediate-child pairs.
