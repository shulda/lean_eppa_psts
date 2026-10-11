# Exact finite universal-stage criterion (all ranks): the real missing invariant

2026-10-11. HUMAN MATHEMATICAL LEMMA; **not yet a Lean theorem**.
This records the clean equivalence underlying the k=1 universal
permutation-stage shortcut, while isolating why it does NOT give
a free shortcut to higher ranks.

## Statement

Let E be a finite alphabet, H a finite E-generated group
(with distinguished generators \(\eta(e)\)), k≥0, and let
\(\mathscr T\) be ANY finite family of finite **complete**
E-labelled deterministic action graphs. The graphs may be
disconnected, provided the covering requirement is applied
to every connected component. Let \(\tau_T:E\to\mathrm{Sym}(V_T)\)
denote the genuine positive transition permutations.

The following are **equivalent**:

**(Kernel condition K_k)**: for each \(T\in\mathscr T\), every
subset \(C\subseteq E\) with \(|C|\le k\), and every signed
word w supported in C,
\[
  [w]_H=1 \quad\Longrightarrow\quad \tau_T(w)=1.
\]

**(Finite stable common covering)**: there exists a finite
E-generated group G, a surjective generator-preserving
\(k\)-stable homomorphism \(G\twoheadrightarrow H\), and a
label-preserving canonical graph cover from Cayley(G)
onto **each connected component** of every \(T\in\mathscr T\).

This is a statement about **completed stage transition
permutations**, NOT merely about their old incomplete skeletons.

### Necessity

Suppose G exists. Let w have support ≤k and value 1 in H.
By k-stability, w also has value 1 in G. A labelled canonical
Cayley-G cover of any component of T sends the word action
of w to identity at every point of that component. Doing so
for all components forces \(\tau_T(w)=1\). Thus K_k holds.

No source-specific geometry is needed for this direction.

### Sufficiency (explicit synchronous product)

Set
\[
  G=\langle (\eta(e),(\tau_T(e))_{T\in\mathscr T}) :
        e\in E\rangle
  \le H\times\prod_{T\in\mathscr T}\mathrm{Sym}(V_T).
\]
The first projection is generator-preserving and surjective.
For k-stability, take two signed words u,v both supported
in C with |C|≤k and with [u]_H=[v]_H.
Then the supported relation \(uv^{-1}\) has value 1 in H,
so K_k forces \(\tau_T(u)=\tau_T(v)\) in EACH stage.
The H-coordinate and every T-coordinate agree, hence
[u]_G=[v]_G. Each stage action is a quotient of the actual
generated group G, and every connected orbit is covered
by the right Cayley graph of G. G is finite by construction.

### A choice-free UNIVERSAL finite action family

Suppose additionally all desired stages have ≤M vertices.
Define
\[
  \mathcal P_{k,M}(H)=
   \{\rho:E\to \mathrm{Sym}(M):
       \forall C\subseteq E,\ |C|\le k,\;
       \forall w\in\widetilde C^*,\
       [w]_H=1\Rightarrow \rho(w)=1\}.
\]
This family is finite (although its defining predicate quantifies
over words; membership can equivalently be expressed by requiring
that each restriction to C factor through the finite group H[C]).
Synchronizing H with ALL \(\rho\in\mathcal P_{k,M}(H)\)
always yields a finite k-stable quotient onto H.

If the required stages satisfy K_k, then each stage can be
padded by fixed points to an M-point action in
\(\mathcal P_{k,M}(H)\). So this one finite group covers
every component of every required stage. This avoids
**constructing the actual required stage-index family as
a datum of the resulting group**.

**But it does NOT avoid proving K_k.** In the source ABO
induction, K_k for the whole Definition-5.3 stage family is
precisely the difficult Proposition-5.4 historical-action
argument. Universal enumeration cannot make that argument
go away; it only changes where the finite indexing lives.

## Source-specific rank one, why this really IS simpler

In source H1, every generator e has exact order \(m_e\in\{1,2\}\):
m_e=1 for an original loop and m_e=2 otherwise
(source §5.1 and first line of §5.2).
At k=1, K_1 means ONLY that each stage transition
\(\tau_T(e)\) has order dividing m_e. This was proved
directly for all Definition-5.3 rank-one completed stages
in [the rank-one replacement note]
(ABO_UNIVERSAL_RANK_ONE_STAGE_REPLACEMENT_2026-10-11.md).

For arbitrary finite source H1, a **classification-free**
stage bound \(M=3|H_1|+1\) suffices: the actual old
H1-cover has ≤|H1| vertices, each of its two unary
subalphabets contributes at most |H1| new coset points,
and one augmentation contributes at most 1. Rank-one
type-(1) clusters are even smaller.

Our separate paper classification reduces M to 6,
but that optimization is not needed for this theorem.
The new independent finite checker
\`research/abo_rank_one_sanity.py\` enumerates all 256
four-vertex two-positive-edge endpoint patterns, including
loops, parallel edges and disjoint cases. It independently
confirms maxima (old cover, plain CE, augmented CE)
=(4,5,6), and the source-faithful nonredundancy witness
ord(ef)=4 for a plain 4-vertex CE versus 5 after one
true B≠∅ augmentation.

## Higher-rank warning

For k≥2, unary period preservation alone is NOT K_k.
For H=(C2)^E and the three-vertex completed two-letter
cluster with generators the two transpositions (1 a)
and (1 b), the commutator w=[a,b] has value 1 in H
but not in that stage. It fails K_k for every k≥2.

Therefore no k-stable finite group can cover that stage
over this H. This is an obstruction to arbitrary-H
**stage sufficiency**, not to corrected ABO: the
true source H_k has already deleted the offending
low-rank relation in G_2.

At higher ranks one can still use the universal construction
conditionally, but proving K_k requires the historical
cluster/CE component classification, and the source
Theorem-4.7 admissibility, embeddedness and bridge-free
induction still have to be established independently.
This is a conceptual factoring of the problem,
not an all-rank shortcut to PSTS EPPA.

## Conservative Lean strategy

1. Prove the GENERAL abstract necessity/sufficiency
   lemma for finite groups and finite complete action
   graphs without introducing source CE/cluster types.
2. For k=1, prove the two SOURCE-specific elementary
   lemmas (size bound and unary period preservation).
   Construct the universal bounded finite permutation
   catalogue, preserving automorphism naturality
   (all actions, no arbitrary representatives).
3. Use corrected source Proposition 4.4 + Theorem 4.7
   to discharge Cond2 for this new G2.
4. Do NOT generalize the rank-one shortcut to arbitrary
   k without first proving source K_k for EACH required
   completed Definition-5.3 stage. At that point the
   universal indexing is optional organizational cleanup,
   not a substitute for the mathematical hard part.

**No claim of an existing Lean proof or unconditional
finite reflecting-group/PSTS-EPPA theorem.**
