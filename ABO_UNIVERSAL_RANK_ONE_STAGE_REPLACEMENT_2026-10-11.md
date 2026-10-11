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
