# A bounded universal permutation-stage substitute for source \`Z₁\`

2026-10-11 · human mathematical construction / **NOT a Lean theorem**.

**Scope:** the first geometric expansion \`H₁→G₂\` in the corrected
Auinger–Bitterlich–Otto proof for an arbitrary **finite original
oriented E-labelled graph**, including loops and parallel edges.
This is a *new first-rank shortcut candidate*, distinct from the
FAILURE of the detector-only/all-Cayley-pullback shortcut.
The argument below is elementary at k=1, but requires the source's
corrected geometric Theorem 4.7 for the subsequent Cond₂ conclusion;
it **does not** solve general k or PSTS EPPA.

## A. Input and an explicit common size bound

Use the exact source \`X₁,Y₁,H₁=T(Y₁)\`. Each label e is an ORIGINAL
edge of the source input. Thus in \`X₁\` the transition of e is either
a transposition (nonloop input edge) or identity (loop). Its singleton
detector \`G₁[{e}]\` has the SAME period. Hence, in \`H₁\`,
\[
m_e:=\operatorname{ord}_{H_1}(e)=
\begin{cases}
2,& e\text{ is nonloop};\\
1,& e\text{ is a loop}.
\end{cases}
\]

For source Definition 5.3, take any A={e,f}, |A|=2,
and any source H₁-cover \`C_H\` of any connected component
of the two-original-edge graph \`E[A]\`. It is an actual subgraph
of the finite Cayley H₁ and therefore has at most N=|H₁|
vertices. (In fact the exhaustive local human analysis in
\`ABO_STAGE_FAMILY_HUMAN_AUDIT_2026-10-11.md\` proves
|C_H|≤4, but this **stronger** fact is not necessary.)

For the **plain full proper-alphabet coset extension**
\`CE(H₁,C_H;P_A)\`, the only nontrivial attached subgroup
alphabets are \`{e}\` and \`{f}\`. Each attached coset has
at most 2 vertices and is anchored along an existing old
\`{e}\`- or \`{f}\`-component. Each component contributes
at most one NEW vertex and there are at most |C_H|
components of each label. Thus
\[
|CE(H₁,C_H;P_A)|\le 3\,|C_H|\le 3N.
\]
Further \`B\`-augmentation for B⊊A attaches at most one
new point (B=∅ adds none), so all **type-(2) stages**
have at most \`3N+1\` vertices.

A source **type-(1)** cluster of proper B⊊A is a union
of H₁[∅]={1}, H₁[{e}] (≤2 points), H₁[{f}] (≤2 points),
so at most 3 vertices. Its B-augmentation adds at most
one point, hence at most 4.

Set \`M:=3N+1\`. Since N≥1, **EVERY** exact source \`Z₁\`
completed stage has no more than M vertices.

### A1. Uniform bound M=13 is possible, independent of |H₁|

The M=3|H₁|+1 bound above is deliberately conservative
and requires no classification. The independent complete
rank-one cover classification in the accompanying audit
§4e gives a stronger fact: **every source H₁-cover
over a connected component of E[{e,f}] has at most
four vertices**, including the parallel-edge and loop cases.
Inserting |C_H|≤4 into the same full-CE counting
argument yields the entirely INPUT-INDEPENDENT
\[
M=3\cdot4+1=13.
\]
Type-(1) augmented clusters have ≤4≤13 vertices.
Thus one can in principle define the universal
rank-one stage catalogue using \`Sym(Fin 13)\`
uniformly for every finite original input graph.
The only source-dependent information needed to
INDEX the catalogue is the finite label set E
and whether each original edge is a loop (m_e=1)
or a nonloop (m_e=2).

This uniform 13-point variant saves the bound
\`|H₁|\` entirely but relies on the separately
checked complete two-label source-cover
classification. For the shortest formalization,
use M=3|H₁|+1 first and improve later.

### A2. Optional sharper universal bound M=6

The complete source-specific classification in the accompanying
audit §4e gives these MAXIMUM sizes over one genuine connected
H₁-cover of a component of E[{e,f}]:

| Original two-label configuration | Plain full CE | Any B-augmentation |
|---|---:|---:|
| Two disjoint nonloop edges | 4 | 5 |
| Two incident, nonparallel nonloop edges | 5 | 6 |
| Two parallel nonloop edges | 4 | 4 |
| One loop and one nonloop edge | 2 | 2 |
| Two loops | 1 | 1 |

All type-(1) augmented clusters have ≤4 vertices. Consequently
\`M=6\` is sufficient for EVERY actual rank-one Z₁ completed
stage, provided each source positive generator labels one
original edge, as in the source initial graph construction.
A separate exhaustive 83-pattern/177-cover finite census
independently checked this maximum, including loops and
parallel edges. The proof is by the finite two-transposition
source classification, NOT just by relying on the census.

For the cheapest **robust Lean path**, retain the simpler
classification-free \`M=3|H₁|+1\` bound and prove the whole
universal stage cover from that. The uniform 6-point
optimization can be formalized later, if beneficial.
It is an optional performance/size simplification, not
a premise of the universal rank-one replacement theorem.

## B. The other key fact: unary PERIOD PRESERVATION

Every source stage T in Definition 5.3 has its missing edges
trivially completed. For any e∈E, the e-positive transition
on T has order dividing m_e.

Why this is genuine geometry, not an assumption:
- In a type-(1) augmented cluster on A={e,f}, every
  e-labelled original edge belongs to one complete
  \`H₁[{e}]\` coset; its positive e-cycles have
  length m_e. The augmentation by a proper B-coset
  adds at most one further complete unary coset.
- In a type-(2) full CE, all old e-labelled edges are
  extended into full \`H₁[{e}]\` constituent cosets
  because \`{e}∈P_A\`. A B-augmentation also
  inserts a complete B-coset. The completed stage
  therefore has only cycles of length m_e and
  newly added loops. No unfinished e-path remains.
- Labels e∉A are absent until trivial completion,
  hence act as identity. A loop label has m_e=1,
  so even where it appears, its complete unary
  coset is a one-vertex loop.

**Be careful:** the original oriented input e-edge alone
is not weakly complete; it has a positive e-edge in only
one direction. The full CE adds the missing positive
reverse edge as part of the complete e-coset BEFORE
trivial completion. The proof does *not* add e-loops
in place of that reverse edge.

Thus \`(T.e)^{m_e}=\mathrm{id}\` on every type-(1)
and type-(2) completed stage, including B=∅.

**Why component tags cannot create longer e-cycles.**
This is the potential loophole in the informal argument and must
be addressed explicitly when formalizing the source lemma.

For A={e,f} and the plain type-(2) full CE, each intrinsic
old {e}-component is either a full two-vertex e-orbit
(or the one-vertex orbit if m_e=1), or a singleton. The
e-coset attachment completes exactly that ONE old component
to a full H1[{e}]-orbit, without joining it to another
old {e}-component. The source gluing relation (3.10)
identifies constituent points across different labels
only through a shared point over their INTERSECTION alphabet.
At rank two, {e}∩{f}=∅, whose only component representatives
are anchored in the OLD skeleton. Thus an attached NEW
{e}-point is never identified with a distinct attached
{f}-point merely because their ambient H1 coordinate agrees.
The resulting true e-orbits remain of size at most m_e,
even if ambient coordinates collide.

In a B-augmentation, Proposition 4.4 and the rank-two
component classification imply that the chosen B-component
is either already a full unary B-coset (augmentation
redundant) or a singleton. With B={e}, the latter is
completed to one new full e-orbit, while all other e-orbits
are unaffected. With B={f}, any new vertex has no old
e-edge and trivial completion gives an e-loop. For B=∅,
no new point is introduced. The type-(1) augmented
clusters have an even simpler identical orbit argument:
their constituent e-components are already full unary
cosets and any B= {e} augmentation completes at most
one singleton.

This checks the period statement on the ACTUAL tagged
quotient graph, not on the possibly noninjective map
to ambient Cayley H1. Positive e-action on all T is
therefore a disjoint union of 1-cycles and m_e-cycles
(m_e∈{1,2}). The missing-edge trivial completion
does not change any nonloop orbit, only adds 1-cycles.


## C. Explicit universal finite complete E-graph

Let \`[M]={0,\ldots,M-1}\`. Define
\[
\mathcal U_1
=\left\{
  \rho:E\to\operatorname{Sym}([M]):
  \ \rho(e)^{m_e}=1\text{ for every }e
 \right\}.
\]
This is a **FINITE**, explicitly defined family.
For every \(\rho\) take the complete labelled action
\([M]_\rho\), with positive e-edges
\(x\xrightarrow{e}\rho(e)(x)\) and formal negative
edges determined by inverse permutations.

Set
\[
X_2^{\rm univ}=Y_1\sqcup\bigsqcup_{\rho\in\mathcal U_1}[M]_\rho,
\qquad G_2^{\rm univ}=T(X_2^{\rm univ}).
\]
Equivalently, \`G_2^{univ}\` is the actual E-generated
synchronous subgroup of
\[
H_1\times\prod_{\rho\in\mathcal U_1}
\langle \rho(E)\rangle.
\]

### C1. The projection G₂^{univ}→H₁ is 1-STABLE

It is generated-surjective by definition. Every signed
word supported on \`{e}\` is a power e^t. If its value
in H₁ is identity, m_e divides t. By construction
every universal coordinate \(\rho(e)\) has order dividing
m_e, so e^t acts trivially on EVERY added component.
Thus no extra one-letter relation is lost, and the
quotient \`G₂^{univ}↠H₁\` is 1-stable.
The corrected rank descent then gives 2-retractability
of \`G₂^{univ}\`, since \`H₁\` is 2-retractable.

### C2. G₂^{univ} covers EVERY source Z₁ completed stage

Fix any source Definition-5.3 stage T. By A and B,
its carrier has n≤M points and generator permutations
t_e of order dividing m_e.

Choose ANY bijection of its carrier with a subset
of [M] of size n; transport all t_e to that subset
and fix every point of its complement. The resulting
assignment \(\rho_T:E\to\operatorname{Sym}([M])\) belongs
to \(\mathcal U_1\), and its complete action has
T as a literal invariant complete subgraph/summand.
The \(\rho_T\)-coordinate of the synchronous group
therefore has a canonical generator-preserving
surjection onto the transition group T(T), so the
Cayley graph of \`G₂^{univ}\` covers EVERY connected
component of T in the source sense.

No source-H₁-cover \`C_H\`, componentwise CE quotient
isomorphism or explicit Z₁ stage-index enumeration is
needed to CONSTRUCT \`G₂^{univ}\`; the bound and unary
period checks suffice to guarantee source-Z₁ coverage.

### C3. Manifest naturality / source symmetries

An automorphism τ of the ORIGINAL input graph induces
a label permutation σ of E, preserves loop-vs-nonloop
status and hence \(m_{\sigma(e)}=m_e\).
It induces the usual \(\tau_H\in\operatorname{Aut}(H_1)\)
with \(\tau_H(e)=\sigma(e)\).
Relabel \(\rho\) by \((\sigma\cdot\rho)(e)
=\rho(\sigma^{-1}(e))\). This permutes ALL coordinates
of \(\mathcal U_1\) canonically, preserves the
bounds \(m_e\), and respects group multiplication
and composition of input automorphisms.
On each universal [M] vertex carrier the automorphism
acts as the identity, moving only the complete
action-component index \(\rho\mapsto\sigma\cdot\rho\).
Together with the canonical action on Y₁, this
implements exactly the first-step symmetry analogue
of source Proposition 5.5, with no arbitrary
choice of graph component/transporter.

## C4. Exact human theorem and a conservative Lean interface

The rank-one replacement can be stated as a standalone abstract
finite-group theorem, separating its trivial universal-action
argument from ALL source-specific graph geometry.

Let \((E,m)\) be a finite alphabet with \(m_e≥1\).
Let \((H,\eta)\) be a finite **E-generated** group such that
each distinguished generator \(\eta(e)\) has **exact order**
\(m_e\). Choose a positive integer M. Form the finite action
family
\[
\mathcal P(E,m,M)
 =\{\rho:E\to\mathrm{Sym}(M):
       \rho(e)^{m_e}=\mathrm{id}\ \forall e\},
\]
and its generated synchronized group
\[
U(H,m,M)
 := \big\langle
   \big(\eta(e),(\rho(e))_{\rho\in\mathcal P(E,m,M)}\big):
   e\in E\big\rangle
 \le H\times\prod_{\rho\in\mathcal P(E,m,M)}
      \mathrm{Sym}(M).
\]

**Abstract assertions, admitting elementary proofs:**

1. The first projection \(U↠H\) is a surjective labelled
   group homomorphism, provided \(\eta(E)\) generates H.
2. It is **1-stable**, because the only one-letter relations
   in H are exponent-\(m_e\) relations, satisfied in every
   \(\rho\).
3. Every complete E-graph T with \(|V(T)|≤M\) and each
   generator permutation of order dividing \(m_e\) is
   a labelled invariant subgraph of the \(\rho_T\)-action
   for SOME \(\rho_T\in\mathcal P(E,m,M)\), by padding the
   underlying finite permutation action with fixed points.
   In particular, every connected component T₀ of T
   is **canonically covered** by Cayley U (for each selected
   root \(v\in T_0\)).
4. Every permutation \(\sigma:E\to E\) preserving \(m\)
   permutes the finite family \(\mathcal P(E,m,M)\)
   functorially. If \(\sigma\) extends to an automorphism
   of H, it also extends to an automorphism of U.
   Signed relabelings are harmless when \(m_e≤2\):
   inversion and the positive generator have the same
   effect on the added permutations.

No coset-extension, cluster, source X₁ or source E occurs
in these four abstract assertions.

**Source specialization:** take \(H=H_1\),
\(m_e\in\{1,2\}\) and \(M=3|H_1|+1\).
To connect this abstract theorem to source Definition 5.3
one needs only TWO genuine source-specific lemmas:

(A) Every completed Z₁ stage has at most M vertices.
(B) In EVERY Z₁ stage T, positive e acts with period
    dividing \(m_e\).

These are checked on paper in §§A–B above and are
simple enough to prove directly over the existing
source weakly-complete/full-coset model; unlike the
previous proposed matching theorem, they need NO
classification of individual H₁-cover components.

**Suggested Lean dependency order (not yet executed):**
- Build finite \(\mathcal P(E,m,M)\) and its complete E-graph
  as a dependent tagged disjoint union, reusing
  \`FiniteActionStages\` and \`DependentDisjointStages\`.
- Use the existing \`SynchronizedProduct\` and
  \`SynchronizedProductStability\` infrastructures
  to construct U, prove its generatedness, finite
  carrier and rank-one stability.
- Prove abstract padding/covering theorem for arbitrary
  finite complete E-graphs T with period constraints.
- Separately prove source Z₁ bounds and unary period
  from full coset geometry; link the abstract covering
  theorem to the corrected Theorem 4.7 base only then.

The abstract algebraic theorem can be formalized FIRST
and audited independently. It cannot by itself certify
source Cond₂ or the higher-rank reflecting group.

## D. What follows and what DOES NOT

**Conditional human implication:** corrected source
Proposition 4.4 supplies the rank-two admissibility/
cluster-property base, and the corrected source
Theorem 4.7 requires a 1-stable, 2-retractable
group above H₁ whose Cayley graph covers each
type-(1)/(2) Definition-5.3 completed stage.
C1–C2 supply those hypotheses, so the source
Cond₂ base should carry through with
\`G₂^{univ}\` in place of its specifically indexed
transition group. This is a legitimate much
**larger but simpler** construction for k=1.

**It does NOT solve the general induction.**
For k≥2, allowing ALL bounded finite permutation
actions that satisfy merely the unary m_e periods
will violate k-stability; the 3-vertex
C₂^E commutator obstruction in the accompanying
human audit is a rigorous example. A corresponding
universal action family with exact k-letter
kernel constraints would already require the
hard source Proposition 5.4 / historical-stage
invariant to show it contains the required Z_k.
The method merely makes the first nontrivial
geometric step finite and formalization-friendly.

**Formalization cost:** constructing all finite
permutations/labels over [M] is elementary Mathlib
\`Fintype (Equiv.Perm (Fin M))\` bookkeeping,
but the source-facing period lemma for every
kind of Z₁ stage and applying the corrected
Theorem 4.7 remain real obligations. No Lean
proof of C1–C3/Cond₂ is asserted by this note.

**Practical recommendation:** seriously consider
this UNIVERSAL stage family for the first
\`H₁→G₂\` transition instead of spending many
Lean steps faithfully indexing φ-pullback
H₁-covers, their componentwise full-CE quotient
isomorphisms, and every B-augmentation. Do not
force the same shortcut at higher rank.
