# Human mathematical audit of the exact ABO Section 5.3 stage families
2026-10-11 · scope: the corrected ABO-I path to finite reflecting groups and PSTS EPPA

**Status: HUMAN CHECK, NOT A NEW LEAN THEOREM.**
Authoritative Lean baseline: main #334, the all-rank group detector lift; geometric
normalization #331. Primary source: Auinger–Bitterlich–Otto,
*Finite approximation of free groups I: the F-inverse cover problem*
(arXiv:2208.03273v6; final PDF at
https://www2.mathematik.tu-darmstadt.de/~otto/papers/hrfinal25.pdf),
especially Theorem 3.8 (PDF p.19), Theorem 4.7 (p.39–43),
Definition 5.3 (p.46–47), Proposition 5.4 (p.47–48), Condition 5.2 (p.45)
and Proposition 3.24 (p.33–34).
The independent corrected source review is
§§6–8 of `sources/PROJECT2_ABO_AUDIT.md` in the October-7 advisory bundle.
The specific earlier two-letter counterexamples are in
`ABO_HUMAN_GEOMETRY_SHORTCUT_AUDIT_2026-10-11.md`.

## EXECUTIVE VERDICT

**No blanket equivalence between our arbitrary-Cayley-skeleton stage
superfamilies and the source's Y_k/Z_k stage families has been shown.**
The failure is mathematical, not simply a missing Lean proof: an abstract
k-retractable group with the detector rank lift need NOT admit a k-stable
finite group whose Cayley graph covers every source-shaped rank-(k+1)
stage. An explicit THREE-VERTEX stage falsifies that shortcut for every
k≥2 (proof below).

On the other hand:

* For *k-retractable* input and 1≤k<|E|, our detector group using all
  subalphabets of size ≤k is **isomorphic as a labelled group** to the
  SOURCE Theorem-3.8 group that uses only subalphabets of size exactly k.
  This is an elementary human proof below, not yet a Lean equivalence theorem.
* For rank two, the existing three genuine Lean stage families are
  **shape-complete for Definition-5.3's types (1) and (2) over a FIXED
  admissible connected Cayley skeleton K in a retractable group Γ**.
  The rank-two cluster property makes every type-(2) B-augmentation
  either already present in the plain completed full extension or a
  singleton off-B augmentation. THIS DOES NOT identify K with every
  genuine H₁-cover of a source component.
* The later §§4b–4c give a **paper proof outline and a precise
  componentwise coset-quotient decomposition argument** showing how
  every source H₁-cover C_H and every completed Z₁ action is simulated
  by rank-two stages of a SINGLE canonical inverse-image Cayley
  skeleton K_E. The full source index matching is **not yet a
  Lean theorem** and depends on building that specific φ:H₁→X₁,
  source E-preimage and quotient isomorphisms, but there is no
  remaining unexplained combinatorial case in the rank-one
  decomposition argument.
* The genuinely hard high-rank obligations remain the **COMPLETE
  k-STABILITY of X_{k+1}=Y_k ⊔ overline(Z_k)** via the previous
  stage-action history and the Theorem-4.7 geometric induction.
  They do not follow from k-retractability alone.

## 1. What the source *literally* asks us to index

Source Eq. (5.3): let G_k=T(X_k) and take

  Y_k = X_k ⊔ (disjoint union of G_k[A], all A⊆E with |A|=k),
  H_k = T(Y_k).

All components are complete E-labelled action graphs: every generator
outside A acts as the identity on the new G_k[A] component.

Definition 5.3 prescribes for *every* A⊆E, |A|=k+1, the following
TWO families of WEAKLY complete graphs, each then trivially completed:

**(1) Arbitrary-cluster type.**
For every set P of proper subsets of A, every actual vertex v of the
cluster CL(H_k[A],P), and every B⊊A, include the augmentation
CL(H_k[A],P)@_v H_k[B].

**(2) Actual-input-cover type.**
Let E[A] be the subgraph spanned by the original letters in A.
For every connected component C of E[A], for EVERY H_k-cover
C_H of C (connected component of the true preimage of C under
the canonical covering H_k→X₁), every actual vertex
v ∈ CE(H_k,C_H;P_A) and every B⊊A, include
CE(H_k,C_H;P_A)@_v H_k[B].
Here P_A is ALL proper subalphabets of A.

B=∅ is NOT dispensable. As H_k[∅]={1}, this case is the
plain/unaugmented cluster or full CE. Source Theorem 4.7(ii)
uses the plain full CE for EMBEDDEDNESS; Theorem 4.7(iii)
uses the augmented copies for BRIDGE-FREENESS.

To build the transition group G_{k+1}, the source sets
X_{k+1}=Y_k⊔(trivial completions of all these Z_k stages),
then G_{k+1}=T(X_{k+1}).

## 2. Exact algebraic relationship of #334 to the source Theorem 3.8

Take an E-labelled group Γ which is k-retractable; assume 1≤k<|E|.
Define D_≤k=∏_{|B|≤k}Γ[B], with all labels outside B trivial in
each coordinate, and D_=k=∏_{|A|=k}Γ[A].
Let H_≤k and H_=k be the ACTUALLY GENERATED subgroups of
Γ×D_≤k and Γ×D_=k respectively, synchronizing all labelled generators.

The source H_k (for Γ=G_k=T(X_k)) is literally H_=k up to
canonical faithful transition representations of its disjoint
action components.

There is an obvious labelled surjective projection
π:H_≤k→H_=k, forgetting all smaller components.
It is INJECTIVE:

For any B⊆E with |B|≤k choose A⊇B with |A|=k. Because Γ is
k-retractable, the GROUP Γ[A] admits the canonical subgroup
retraction ρ_{A,B}:Γ[A]→Γ[B] that erases all A\B letters.
The B-coordinate of any generator word w is ρ_{A,B} of its
A-coordinate. If two generated tuples agree on all rank-exactly-k
coordinates, they therefore agree on every lower B-coordinate.
The Γ-coordinate is also kept; hence π is injective.

So H_≤k≅H_=k AS LABELLED GROUPS. No choice of A(B) survives
in the final statement, because the full synchronized tuple
contains all A's and the word-evaluation identity fixes every B.

For k=1 this gives a particularly concrete source match:
H₁=T(X₁⊔∐_i Γ[{i}]) is the synchronization with one cyclic
detector per letter, precisely the labelled algebraic content of
`UnaryDetectorSynchronizedCover.lean` in #328.

**Critical limitation:** this algebraic match does NOT construct the
canonical covering H_k→X₁ and its actual source C_H; nor does it
supply ANY Z_k stage action or Cond_{k+1}.

## 3. A NO-GO example for adding all rank-(k+1) stages to arbitrary Γ

Fix k≥2 and a finite alphabet E with |E|≥k+1; choose distinct a,b,
and A⊆E of size k+1 containing both a,b.
Let Γ=(C₂)^E, with labelled generators the independent coordinate
involutions. Γ is globally retractable.

Source Definition 5.3(1) permits P={{a},{b}}, B=∅, v=1. The
cluster CL(Γ[A],P) is the actual THREE-vertex labelled graph:
vertices {1,a,b}, an a-edge 1--a, a b-edge 1--b, and their formal
inverse oriented edge tokens. Missing signed edges are completed
by loops. On its complete transition action,
t_a=(1 a), t_b=(1 b) and every other generator fixes all vertices.
In particular,
  t_a t_b != t_b t_a
and the commutator w=aba^{-1}b^{-1} acts nontrivially (it is a 3-cycle).
But [w]_Γ=1 and w uses only 2≤k letters.

Suppose a labelled group quotient Q:G↠Γ were k-STABLE and
Cayley G covered that complete stage. Since w uses only two
letters and [w]_Γ=1, k-stability forces [w]_G=1.
A Cayley covering action necessarily sends [w]_G=1 to a trivial
transition word in EVERY covered complete stage. Contradiction.

Therefore **k-retractability of arbitrary Γ, even full
retractability, does not suffice to add all Definition-5.3(1)
stages while retaining k-stability**.

Why this does NOT refute corrected ABO: its actual Γ=H_k is
not arbitrary! The previous groups G_k already detected
low-rank cluster relations via Z_{k-1}. In the example,
the three-vertex rank-two cluster must have appeared at the
previous rank; the source stage history forbids the naive
commuting relation in the later H_k.

Why this ALSO invalidates naive "include all possible extra stages"
simplifications: adding new full transition ACTIONS shrinks the
group word kernel. A superfamily helps the desired covering
property but can violate k-stability unless EACH extra component
has the correct rank-k identity-word kernel.

**Coatom caution:** a full CE can be recoded using coatoms, as our
Lean coatom/full CE isomorphism proves; this does NOT license
enlarging arbitrary type-(1) clusters P to coatom sets. Replacing
{{a},{b}} by {{a,b}} in the example changes a three-vertex
noncommuting action to the four-vertex regular Cayley square with
commuting a,b, changing its transition word kernel.

## 3a. A genuine source example where Z₁ *removes* the obstruction

The previous no-go used an arbitrary abelian Γ. The necessity
of retaining the stage history is also visible in a completely
source-faithful input.

Take the connected ORIGINAL oriented graph E to be the
four-vertex path
  0 --a--> 1 --c--> 2 --b--> 3
with all three positive edge labels distinct.

The genuine source X₁ has transition group G₁=S₄ generated
by adjacent transpositions a=(0 1), c=(1 2), b=(2 3).
The disjoint ones a,b COMMUTE in G₁.
They also commute in source H₁=T(Y₁): the added singleton
detector coordinates are independent, and the first
projection G₁ already has a,b commuting. Their actual
H₁-generated subgroup is C₂×C₂.

But Z₁ type (1) for A={a,b}, P={{a},{b}}, B=∅ is exactly
the three-vertex path-shaped cluster discussed in §3:
its completed a,b actions are (1 a), (1 b), so they
DO NOT commute. The true generated transition group
G₂=T(Y₁⊔overline(Z₁)) therefore also has
[a,b]_{G₂} != 1. This is perfectly consistent with
G₂↠H₁ being only **1-STABLE**, not 2-stable!

At the next source step, H₂↠G₂ is **2-stable**, hence
[a,b]_{H₂} != 1. Consequently Z₂'s reuse of the analogous
type-(1) cluster with A={a,b,c} does NOT force a
NEW violation of 2-stability: the relation it detects
was already removed by the previous stage.

This three-letter source example is an exact, hand-checkable
explanation of the paper's induction invariant:
**Z_{k-1}'s action supplies the stage history which makes
adding Z_k consistent with k-stability.**
No abstract k-retractability statement can replace it.

## 4. POSITIVE rank-two (k=1) comparison over a FIXED input K

Fix A of cardinality 2, a generated retractable labelled ambient Γ,
and a (source admissible) connected A-Cayley skeleton K.
The checked Lean base
`RankTwoClusterPropertyBase.rank_two_B_component_full_or_singleton_with_core_support`
says that each B-component of CE(Γ,K;P_A), B⊊A, is either
a tagged full B-coset or a singleton, with the source's required
least-support property in the latter case.

Therefore:

* If B=∅, the augmentation is EXACTLY the plain full CE.
  This is the complete stage whose kernel is certified in
  `RankTwoPlainFullCEKernel.lean`.
* If B={a} or {b} and the B-component of the chosen basepoint
  is already a full B-coset, gluing another full B-coset adds
  no actual vertex/edge: the augmented graph is canonically
  isomorphic to the plain full CE.
* Otherwise, the B-component of that basepoint is a singleton
  off the old skeleton and the augmentation is exactly the
  singleton-off-B object constructed in
  `RankTwoOffComponentCompletedStage.lean` and indexed in
  `RankTwoType2IndexedFamily.lean`.
* Definition-5.3(1) type-(1) objects are covered over Γ[A] by the
  full finite index over all P, augmentation labels and actual
  basepoints in `AugmentedClusterIndexedFamily.lean`.
* The three families occur together in the genuine complete
  action `RankTwoThreeFamilyStableCover.lean`. Their complete
  rank-ONE kernels were certified for EVERY singleton label,
  including labels outside A; their synchronized quotient is
  1-stable.

So over ANY FIXED valid rank-two K, this is a convincing
human *isomorphism-type coverage* of the source's rank-one
Definition-5.3 stages. The key classification facts are already
in Lean.

**NON-CLAIM:** no Lean theorem yet constructs the required actual
H₁-cover C_H of the original input graph and identifies it
with the K in that stage family. Different H₁-covers of the
various E[A] components must ALL be covered. The current
`RankTwoGlobalSkeletonCover.lean` instead begins with ONE externally
supplied ambient Cayley subgraph and slices it over all A and cosets.
We still need to supply the specific true preimage of the source
oriented E in the H₁-Cayley graph, split into ACTUAL A-components,
and prove it ranges over each C_H (or provide a directly checked
stage-action kernel simulation). The available connected-coset
subgraph and path-reflection lemmas should help, but this is
a substantive *index matching* obligation.

## 4a. A TRUE source-H₁ rank-two example (not an arbitrary Γ)

Take original oriented E to be the three-vertex path
0 --a--> 1 --b--> 2, with two positive edge labels.

The source starts with X₁ on vertices {0,1,2}:
a=(0 1) and b=(1 2), so G₁≅S₃. Its Y₁ also contains the
complete singleton Cayley graphs G₁[{a}] and G₁[{b}].
Consequently the true source H₁ is the generated subgroup of
S₃×C₂×C₂ under ((0 1),1,0), ((1 2),0,1).
It has order 12 (dihedral of order 12); this is exactly the
unary synchronised H₁ detector group discussed above.

Now use the TRUE canonical H₁→X₁ vertex-action covering map.
The inverse image of the original E (only its real signed
a/b-edge tokens, NOT X₁'s artificial added reverse-positive
edges) has 12 vertices, four fibres over each of 0,1,2.
As a labelled graph it is exactly the disjoint union of
FOUR actual three-vertex path components: a cover of a tree
has a path component for each of the four starting-fibre points.

For each such rooted path x--a--xa--b--xab, its rank-two
full proper-alphabet CE has FIVE vertices. Its two new tagged
points are represented in the ambient H₁ by xb and xaba.
These are distinct from each other and from the old triple,
since (ab) has order 6 in the source H₁. All four CE components
therefore happen to embed individually in the source H₁
for this particular elementary example. Their disjoint
union has TWENTY tagged vertices, so cannot globally inject
into the 12-element H₁ Cayley graph; component tags matter.

This was checked by an explicit 12-state generator enumeration
(with the S₃ permutation factor and two detector bits).
It is a **finite sanity check**, not a general proof. It supports
the intended specific choice of K for our rank-two family:
K should be the preimage of the ACTUAL original edge graph E
in the H₁ Cayley graph, and its actual connected two-letter
components, not an arbitrarily guessed rank-two skeleton.

In particular, our earlier counterexample using Γ=C₂²
is an obstruction to the universal *shortcut* but it is NOT
an instance of this true source-H₁ example: here H₁ separates
the words b and aba as it should.

## 4bb. Equivariance warning: ONE chosen φ-basepoint is not canonical

There is a genuine distinction between **kernel-stage sufficiency**
and **source Proposition 5.5 automorphism-equivariance**.

The single fixed-basepoint skeleton K_E from §4b covers all based
choices **UP TO A LEFT TRANSLATION**, so it is enough for a
non-equivariant source-Z₁ word-kernel/cover simulation after
enumerating all local coset representatives. But it is NOT
on its face fixed by an automorphism of the original graph
that moves the chosen basepoint v₀∈X₁.
Thus blindly replacing the source's full Y₁/Z₁ indexing by
one anchored K_E risks losing the symmetric construction
needed for source Proposition 5.5 / the eventual EPPA bridge.

**Simple finite, manifestly equivariant repair:**
index the canonical inverse-image skeletons by ALL v∈V(X₁),
\[
 K_E^v := \varphi_v^{-1}(E)\ \subseteq\ \mathrm{Cayley}(H_1),
 \qquad \varphi_v(h)=v\cdot q(h).
\]
For each v take all |A|=2 label subsets and all g∈H₁
left coset slices of the genuine incomplete K_E^v;
include their three certified families of completed stages.
The total indexed family remains FINITE. At k=1 its
word-kernel hypothesis is unchanged because every extra
stage individually has the already certified full rank-one
kernel. The resulting generated group is still
1-stable above H₁ and 2-retractable after rank descent.

This indexing is **naturally equivariant**. For each automorphism
τ of the oriented input graph, let τ_X be its action on X₁,
τ_H the induced generator-permuting automorphism of H₁,
and σ_τ the induced permutation of edge labels.
The source first group action satisfies
\[
 \tau_X(\varphi_v(h))=
 \varphi_{\tau_X(v)}(\tau_H(h)),
\]
where the labels transform by σ_τ.
Consequently τ_H sends K_E^v (with relabeling) to
K_E^{τ_X(v)}, and the stage index
\[
 (v,A,g)\longmapsto(\tau_X(v),\sigma_\tau(A),\tau_H(g))
\]
is canonical. It respects compositions of input automorphisms
without choosing any transporter of τ_X(v₀) back to v₀.

**Recommendation:** the first source-faithful rank-one
implementation should use the all-basepoint indexed family,
NOT silently choose one v₀ and promise that left-translation
symmetries will later be coherent. The one-basepoint proof
in §4b is useful to reason about isomorphism types and
component quotient decompositions, but the actual
automorphism-equivariant construction should retain v
in its finite index type. This restores precisely the
source's intended symmetry-by-uniform-enumeration mechanism.

## 4c. Componentwise CE decomposition: complete paper proof at the quotient level

The non-formal lemma needed in step 4b(3) is in fact quite clean,
provided **connected components mean realised A-paths in the
INCOMPLETE old skeleton**, never ambient A-coset equality.

Let K be any finite A-labelled Cayley skeleton admissible for full
A-coset extension and let K=⨆_{i∈I}K_i be its decomposition
into connected A-components, where every old edge belongs to exactly
one K_i. For every B⊊A:

* Each intrinsic B-component of K is wholly contained in a unique
  K_i. Hence the actual type \`ComponentIndex K B\` is the disjoint
  union of \`ComponentIndex K_i B\` over i. This is a genuine
  equivalence of tagged quotient *types*, not an assertion that
  two equal ambient group cosets determine the same index.
* Each component-indexed attached B-coset point (q,h) inherits
  the unique parent i of q. Under an inclusion from alphabet
  D⊆B, the larger component index still has that same parent.
* In the raw tagged vertex family
  Σ_{B∈P} AttachedCosetVertex(K,B), assign to every tagged
  vertex its parent i. If two raw vertices are related by the
  source equation (3.10), they have a common intersection-alphabet
  point r over B∩C. By the preceding observation both endpoints
  have the same parent as r. Therefore the *actual* source
  gluing equivalence relation never identifies points of
  DIFFERENT old A-components. Its restriction to parent i
  is precisely the relation used by CE(K_i;P).
* Every raw directed edge belongs to a single-alphabet
  coset extension, whose old edges and newly completed
  B-coset edges have source and target with the SAME parent i.
  The raw edge-token equivalence in Lean is **equal quotient
  source plus equal signed label**. Equal quotient source
  forces the same parent; thus no cross-component edge
  identification occurs either. Its restriction to parent i
  is the actual edge-token equivalence of CE(K_i;P).
* The quotient source/target/inverse/label functions therefore
  respect the partition, giving a canonical E-labelled graph
  isomorphism
  \[
    \mathrm{CE}(\Gamma,K;P)
      \cong \bigsqcup_{i\in I}\mathrm{CE}(\Gamma,K_i;P).
  \]
  Missing signed labels are completed **by loops at individual
  vertices** so the same isomorphism holds after trivial
  completion to complete E-graphs.
* If z is a vertex of the i-th summand and B⊊A, its intrinsic
  B-component lies entirely in this summand. The B-augmentation
  therefore modifies ONLY summand i, and the other summands
  remain unchanged:
  \[
   \overline{\mathrm{CE}(\Gamma,K;P)@_z\Gamma[B]}
   \cong
   \overline{\mathrm{CE}(\Gamma,K_i;P)@_z\Gamma[B]}
   \;\sqcup\!
   \bigsqcup_{j\ne i}
   \overline{\mathrm{CE}(\Gamma,K_j;P)}.
  \]
  This is also true for B=∅, where the augmentation is plain.

Consequently the complete transition action of each connected
source-indexed augmented CE(K_i) is a genuine *invariant
component action* of the augmented CE of the larger K.
For every signed word w, identity of its action on the large
completed stage implies identity on the specific source stage:
\[
 \ker(\mathrm{wordValue}_{\mathrm{augCE}(K)})
 \subseteq
 \ker(\mathrm{wordValue}_{\mathrm{augCE}(K_i)}).
\]
This is the **correct kernel inclusion direction** for having
the synchronized larger stage group cover each prescribed
source object.

This completes the **human proof of componentwise gluing** by
unpacking the actual checked Lean quotient definitions
\`ComponentIndexedCosets\`,
\`MultiCosetVertexQuotient.MultiCosetRawRelated\`,
\`MultiCosetRawEdges\` and \`MultiCosetEdgeQuotient\`.
A future *formal* equivalence/isomorphism proof still has
dependent subtype/quotient transport bookkeeping. The proof
assumes source admissibility and retractability where the
multi-coset setoid is needed; at rank two admissibility
is automatic and the generated local subgroup H₁[A] is
globally retractable.

**Important:** this is an equivalence of the **component-tagged
full coset extension**, not of the potentially noninjective
projection into the ambient Cayley graph. Two distinct
components can have new vertices at equal ambient Γ-values,
yet are NOT glued (the 5-vertex counterexample above).

## 4b. Promising human reduction: all genuine Z₁ covers from ONE canonical source skeleton

The previous fixed-K result becomes much more powerful when K is
chosen **canonically from the true initial graph**, rather than arbitrarily.

Let G₁=T(X₁) be the source first transition group and
H₁=T(Y₁) its actual rank-one unary-detector synchronization
(algebraically as in §§2 and 4a). Choose the source canonical
covering morphism φ:H₁→X₁, induced from H₁↠G₁ and the
G₁-action on the vertices of X₁. Let **K_E** be the literal
INCOMPLETE H₁-Cayley skeleton obtained as the complete inverse
image of the ORIGINAL oriented graph E⊆X₁ under φ.
This retains the original signed edge tokens but excludes the
artificial nonoriginal edges added in the initial completion X₁.

There is a plausible direct five-step **human proof outline**:

1. **All source H₁-covers are literal connected components.**
   For each two-letter alphabet A and every connected component
   C of the ORIGINAL E[A], the true source H₁-cover C_H is
   exactly an A-component of K_E whose φ-image lies in C.
   Conversely each non-isolated A-component of K_E over C
   is one of these covers. This follows directly from the
   definition as a connected component of φ⁻¹(C), provided
   K_E is defined using the original graph's true edge tokens.
2. **They all occur in the local slices.**
   Any A-component in an H₁-Cayley skeleton lies inside a
   left coset g·H₁[A], because every actual path uses only
   A-labelled generators. Our checked `leftCosetSlice` and
   exact subalphabet path-restriction theorems implement this.
   Therefore all source C_H are components of at least one
   rank-two local slice used by `rankTwoGlobalSkeletonStage(K_E)`.
**All choices of canonical source basepoint are covered, not just one.**
The initial complete E-graph X₁ is connected (the original E is
connected), so the transition G₁-action is transitive. Fix one
basepoint v₀∈X₁ and the canonical surjection q:H₁↠G₁.
For any other v∈X₁ there exists t∈H₁ such that
v=v₀·q(t). On Cayley vertices h∈H₁ the source canonical
morphism with basepoint v is
φ_v(h)=v·q(h)=v₀·q(th)=φ_{v₀}(th).
Thus the complete preimage graph of E under φ_v is obtained
from the single preimage K_E under φ_{v₀} by LEFT
translation h↦th; it preserves both signed directed edge
tokens and all A-path components. The overfamily enumerating
ALL coset representatives g therefore captures every possible
source choice of based covering morphism. This discharges
the **human basepoint-indexing issue** in §4b(1) without
selecting canonical representatives invariantly.

3. **Full CE respects input-component disjoint unions.**
   This is a concrete NOT-YET-LEANED gluing lemma. In the
   literal quotient definition, every attached B-coset is
   tagged by a B-component of the old skeleton. Such a
   component lies in one A-component. The only identifications
   of different coset tags come from a shared intersection
   subcomponent OVER AN ACTUAL OLD VERTEX. Hence points originating in
   different A-components can never be glued together.
   The completed full CE of a possibly disconnected A-skeleton
   thus decomposes, as an E-labelled action graph, into
   disjoint completed CEs of its actual A-components.
   **This lemma must be stated and checked explicitly:**
   equality of ambient group coordinates does NOT cause gluing.
4. **Augmentations respect the selected component.**
   B=∅ means the plain CE. For singleton B at rank two,
   full B-components give the same plain CE; off-B singleton
   components are exactly our indexed off-component stages.
   Augmenting the disconnected slice at one root only changes
   its corresponding A-component; the other components remain
   untouched (and retain their own trivial completions).
   Thus every source type-(2) *completed* stage occurs, up to
   faithful labelled graph isomorphism, as a complete connected
   summand of one stage already in the global three-family
   action. Type-(1) is indexed independently for all P,B,v.
5. **Transition word-kernel simulation.**
   If a source complete action S is a complete invariant
   summand of one of our existing complete stages T, then
   ker(wordValue_T) ⊆ ker(wordValue_S) immediately.
   Synchronizing all our stages with H₁ yields a group
   whose Cayley graph can cover S, via the action quotient.
   The already-certified full singleton stage word kernels
   guarantee 1-stability, and corrected rank descent gives
   2-retractability. In combination with the source
   Proposition 4.4 and corrected Theorem 4.7, this *would*
   establish the exact rank-one-to-rank-two geometric base.

**Assessment:** On paper this is a coherent plan and looks viable.
The genuine bottleneck is **(3)+(4)**, faithful component-level
decomposition of the real tagged coset quotient, followed by the
actual constructed φ and E-preimage in (1). They are more concrete
than a generic higher-rank geometric invariant and should be
independently verified before expensive formalization. No general
counterexample has been found to these steps.

**Scope caution:** this is NOT the full higher-rank induction.
At k≥2, off-skeleton B-components need not be singletons and the
rank-two type-(2) family ceases to be exhaustive. Also replacing
X_k and its historical Z_{k-1} action by an arbitrary detector
group would violate k-stability, as proved in §3.

## 4d. Explicit first higher-rank geometric obstruction: off-skeleton B-component can be THREE vertices

The earlier rank-two classification relies on the fact that
a proper B⊊A has at most one letter. At the first genuinely
higher rank |A|=3, its analogue is FALSE, even in a completely
elementary globally retractable ambient group.

Let Γ=C₂³ with independent involutory generators a,b,c,
A={a,b,c}, and let the old incomplete A-skeleton K
consist only of its identity vertex 1, without any old edges.
K is trivially admissible (for all proper alphabets).

The true full proper-alphabet coset extension CE(Γ,K;P_A)
coincides with the **literal cluster**
\[
\mathrm{CL}(\Gamma[A],P_A)
 = \Gamma[\{a,b\}]\;\cup\;
   \Gamma[\{a,c\}]\;\cup\;
   \Gamma[\{b,c\}],
\]
where P_A consists of ALL proper subsets of A.
Its seven vertices are
\[
   1,\ a,\ b,\ c,\ ab,\ ac,\ bc;
\]
only abc is missing from Γ[A].

Now choose B={a,b} and z=c. Inside the ACTUAL (uncompleted)
full coset extension, the B-component of z is
\[
  z\,\mathrm{CE}[B]=\{c,ac,bc\},
\]
with exactly the two geometric B-edges c--a--ac and
c--b--bc. The fourth point abc of the full B-coset
c Γ[B]={c,ac,bc,abc} is MISSING. This component
does not meet the old skeleton {1} and is **NOT a singleton**;
rather, it is the proper rank-two B-cluster
CL(Γ[B], {{a},{b}}) translated by c.

The source-type (2) augmentation at z, B adds the
missing abc vertex and the two missing B-edges,
producing the full cΓ[B]. It cannot be represented by
either (i) the plain CE (B=∅), or (ii) the special
rank-two *off-B singleton* augmentation from
§RankTwoType2IndexedFamily.lean§.

This is an explicit small mathematical disproof of trying
to ITERATE our rank-two singleton classification as a
higher-rank Z_k catalogue. It demonstrates exactly why
Proposition 3.24/cluster property must be invoked for
general off-skeleton B-component shapes.

**Quantifier caution:** this example is a valid admissible
Cayley-skeleton/coset-extension/augmentation instance,
but K={1} has not been shown to be a canonical H₂-cover
of a component of a particular source initial E[A].
Thus it invalidates an arbitrary-input geometric
generalization, NOT source Proposition 5.4 or the
source-specific higher-rank Z₂ construction.

A hand and machine check on the eight C₂³ elements
gives seven CE vertices and the B-component {c,ac,bc};
the missing vertex is abc.

## 4e. NEW: exact H₁-cover shapes on every two-letter input (including loops and parallel edges)

This strengthens §4a/§4b from "we should understand the H₁-covers"
to an **explicit complete rank-one classification**. It is a paper
calculation plus an independent finite enumeration, NOT a Lean theorem.

In the source first action \`X₁\`, every positive input edge \`e\` induces
the **single transposition** of its endpoints, or identity if it is a
loop. Its singleton \`G₁[{e}]\` detector is therefore \`C₂\` (nonloop)
or trivial (loop). For distinct labels \`e,f\`, the *actual subgroup*
\`H₁[{e,f}]\` consists of words in
\[
\widehat e=(t_e,\epsilon_e,0),\qquad
\widehat f=(t_f,0,\epsilon_f),
\]
where a detector bit is absent/trivial if its edge is a loop.
**Other input labels cannot introduce extra local relations among
these two generators**, since the word value is coordinatewise in
the full source group \`H₁\`.

Consequently there are only these source two-edge configurations.
Here "plain CE" and "augmented CE" refer to the *genuine source
Definition-5.3 type-(2) stages over ONE actual connected H₁-cover*
of a component of \`E[{e,f}]\`, not to an arbitrary skeleton.

| Source pair of labelled edges | \`H₁[{e,f}]\` | Each connected H₁-cover \`C_H\` | Plain full CE size | Augmented CE sizes |
|---|---|---|---:|---|
| two disjoint nonloop edges | \`C₂²\` | one 2-vertex edge | 4 | 4 or 5 |
| two nonloop edges meeting in exactly one vertex | dihedral of order 12 | one 3-vertex path | 5 | 5 or 6 |
| two parallel nonloop edges, even if oppositely oriented | \`C₂²\` | a 4-vertex cycle covering the parallel-edge pair twice | 4 | 4 |
| one nonloop edge and one loop (attached or disjoint) | \`C₂\` | a 2-vertex edge with optional attached loop, or an isolated loop vertex | 2 | 2 |
| two loops (same or distinct vertices) | trivial | isolated vertex with its selected original loops | 1 | 1 |

**Derivation, not just a computer census:**
- Disjoint nonloop transpositions commute and have independent detector
  bits, so local \`H₁[{e,f}]=C₂²\`. Over either original isolated
  one-edge component the other edge is *absent*, yielding
  disjoint copies of that 2-vertex edge in the old preimage graph.
- At a common endpoint, the original transpositions generate \`S₃\`,
  and \`\widehat e\widehat f\` has order
  \`\mathrm{lcm}(3,2)=6\`; the two involutions generate dihedral
  order 12. A covering of the 3-vertex original **tree**
  consists of four separate copies of that path.
- For parallel original edges, \`t_e=t_f\`; independent detector bits
  yield \`C₂²\`. The true inverse image of the two parallel
  oriented edges is one 4-cycle (a two-sheeted cover).
- A loop label acts as identity in \`X₁\` and its singleton
  detector is trivial. The remaining nonloop edge, if any,
  generates \`C₂\`. Two loop labels generate the trivial group.

Each \`H₁\` component is contained in a left
\`H₁[{e,f}]\` coset; coset translations and arbitrary source
basepoints do not change any of these component isomorphism types.
There are **no rank-one source \`C_H\` components larger than 4 vertices**.

An independent exhaustive enumerator checked all **83** ordered
two-labelled-edge endpoint patterns on at most four vertices
(where endpoint order within an edge is immaterial, labels are
distinct, and loops, parallel edges and disconnected configurations
are included). It enumerated the actual synchronized two-letter
group, the inverse image of the ORIGINAL true edge tokens and
its intrinsic connected components. The largest component had
four vertices. The independent tagged full-CE/augmentation
calculation also reproduced all stage vertex counts in the table.
This is finite **sanity checking**, not the proof of the general
conclusion (which is the preceding subgroup-action argument).

**Impact on formalization:** an exact source-\`Z₁\` index matching
can in principle be reduced to these finitely many elementary
rank-two templates, plus the existing source-\`H₁\` action,
coset translations and component-quotient isomorphisms.
The theorem "all \`Z₁\` cases are simulated by our actual
rank-two stage family" is still not in Lean, but there is no
large uncontrolled class of source \`H₁\`-covers to classify at
rank one. The loop and parallel-edge cases are essential:
silently treating all \`E[A]\` components as trees is false.

## 4f. NEW: a genuine source-Z₁ type-(2) augmentation changes the word kernel

The general C₂² counterexample in the earlier audit is now
realised in an **actual source input**. Let the original connected
graph \`E\` be the four-vertex path
\[
0\xrightarrow{e}1\xrightarrow{g}2\xrightarrow{f}3,
\]
with distinct edge labels. The two labels \`e,f\` are disjoint.
Thus the actual \`H₁[{e,f}]\cong C₂²\`; this is **not** an
arbitrary surrogate group.

Fix the source \`E[{e,f}]\`-component containing the original
\`e\`-edge. A genuine \`H₁\`-cover of it is a **single e-edge**
\[
u\xleftrightarrow{e}ue.
\]
Its **plain** full proper-alphabet coset extension attaches
distinct \`f\`-cosets at \`u\` and \`ue\`; the literal graph is
the four-vertex alternating path
\[
uf\xleftrightarrow{f}u
\xleftrightarrow{e}ue
\xleftrightarrow{f}uef.
\]
After trivial completion its positive transition permutations are
\[
t_e=(u\ ue),\qquad
t_f=(u\ uf)(ue\ uef).
\]
Therefore \`t_et_f\` is a **4-cycle**.

Definition 5.3(2) also REQUIRES augmentation at the genuine new
vertex \`uf\` with \`B=\{e\}\`. Its true \`e\`-component is a
singleton. The augmentation attaches a fresh vertex \`z\` of
ambient coordinate \`uef\`, different from the already present
tagged point \`uef\`. The resulting five-vertex graph is
\[
z\xleftrightarrow{e}uf
\xleftrightarrow{f}u
\xleftrightarrow{e}ue
\xleftrightarrow{f}uef.
\]
After trivial completion,
\[
t_e=(z\ uf)(u\ ue),\qquad
t_f=(uf\ u)(ue\ uef),
\]
and \`t_et_f\` is a **5-cycle**.

Take the signed positive word \`w=(ef)^{12}\`.
It acts trivially on
- source \`Y₁\`: the e- and f-transpositions are disjoint,
  and the corresponding rank-one detectors are independent,
  so \`ef\` has order 2;
- **every source type-(1) cluster or augmentation**:
  if its parent alphabet omits e or f, the absent generator
  acts as identity, and the remaining generator is an involution;
  if its parent alphabet is \`\{e,f\}\`, its entire actual
  augmented cluster sits inside the four-element \`C₂²\`,
  so the permutation \`ef\` has order 1, 2, 3 or 4;
- **every PLAIN source type-(2) CE**: for parent
  \`\{e,f\}\`, its components are the two disjoint old edge
  covers, each giving an alternating four-vertex path and
  an \`ef\` 4-cycle. For parents \`\{e,g\}\` or \`\{g,f\}\`,
  the missing \`f\` or \`e\` acts trivially after completion,
  so \`ef\` has order dividing 2.

But \`w\` does **not** act trivially on the displayed genuine
type-(2) B≠∅-augmented CE, because \`5\nmid12\`.

This proves a sharp, **source-faithful kernel nonredundancy**:
dropping all type-(2) B≠∅ augmentations from this source's
\`Z₁\` strictly enlarges the common transition word kernel,
even while retaining *all* its type-(1) stages and *all*
plain type-(2) CEs. It is NOT a proof that a different
reduced construction cannot still achieve the ultimate EPPA;
it does rule out the proposal that these augmentation actions
are redundant or that a detector-only rank lift reproduces the
source \`G₂\`.

It also explains how stage history can create much larger
orders from very small Cayley groups: plain CE detects order 4,
augmentation detects order 5, although the ambient \`H₁\`
has \`ef\` of order 2. All are compatible with required
**1-stability**, which constrains only one-letter words.

## 5. Required interfaces: where current Lean stops

| Source obligation | Current Lean ingredient | Human audit verdict |
|---|---|---|
| G_k→H_k, k-stable and (k+1)-retractable | #334 detector lift, #328 unary H₁ | Algebraically equivalent to source under k-retractability; missing explicit equivalence theorem |
| Z_k(1) ALL arbitrary P,v,B | `AugmentedClusterIndexedFamily` for k=1 | Good k=1; no generic higher-rank family/kernel |
| Z_k(2) plain CE, B=∅ | `RankTwoPlainFullCEKernel` | Good k=1 for supplied K; missing all source C_H indices |
| Z_k(2) B≠∅ full-component augmentation | `RankTwoClusterPropertyBase` | Canonically redundant/plain at k=1; higher-rank can be nontrivial |
| Z_k(2) B≠∅ off-skeleton augmentation | `RankTwoType2IndexedFamily` | Singleton exhaustive at k=1; higher-rank can be a non-singleton B-cluster |
| Full Z_k group transition-action kernel over all stages | `RankTwoThreeFamilyStableCover` and #314/#325 | Proved for rank1, supplied K, not whole source Y₁/Z₁ catalogue |
| Complete rank-k stage kernel, Proposition 5.4 | `SynchronizedStageStableCover` provides abstract kernel→stability | CRITICAL OPEN for k≥2; depends on previous stage action |
| Theorem 4.7(ii) embedding | #331 factorization of ALREADY Cayley-embedded skeletons | CRITICAL OPEN; can't use as a substitute for proving embeddedness |
| Theorem 4.7(iii) bridge freeness | `BridgeFreenessInterface` and coatom transfer | CRITICAL OPEN as genuine construction/proof |
| Condition 5.2 across ranks and final Lemma 2.5 | Conditional PSTS transfer modules | CRITICAL OPEN |

## 6. Concrete cheaper human tests before more Lean

**Rank-one source-geometry test (first priority):**
Start from the actual initial graph E and its G₁ transition action X₁.
Construct algebraic H₁ by the unary synchronized group already
certified. Let φ:H₁→X₁ be the canonical covering action induced
by its projection to G₁.
Construct ONE *source-specific* incomplete H₁-Cayley subgraph
L_E with exactly the vertices and real signed edges projecting
to the original E, but NOT to the artificially added nonoriginal
edges of X₁.
For each two-letter A and each connected component C of E[A],
verify: every component of φ^{-1}(C) occurs as an intrinsic
A-component of L_E (potentially intersected with an H₁[A] coset).
At that point compare the completed CE of EACH component with
our fixed-K three-family stage. Beware that using a disconnected
slice instead of its actual connected component must not merge
distinct component tags or silently add paths. **This is testable
humanly and on small finite models before any new Lean.**

**Rank-two-history test (second priority):**
Explicitly audit Proposition 5.4's nontrivial
rank-2 cluster/augmented-cluster witness for each possible
C-component of every Z₂ stage, using Cor. 3.12, 3.15 and
Prop. 3.24. Check its transport to a *specific* Z₁ action
from the preceding step. This is the precise human invariant
missing from the detector-only construction and prevents the
three-vertex commuting counterexample.

**Geometry/bridge test (third priority):**
Only after the rank-k stage kernel succeeds, verify the SOURCE
Theorem 4.7 hypotheses for exact C_H covers; then prove
embeddedness using the plain B=∅ completed extension and
bridge-freeness using ALL B-augmentations and the corrected
full-B-coset exception. The existing #331 factorization is
available only AFTER the relevant Cayley embedding is known,
not as an inductive replacement.

**Fallback:** use the exact source X_k/Y_k/Z_k transition action
families and already audited local repairs R1–R8. Don't force
a minimal-pullback or detector-only shortcut. For formalization,
stop adding stage indices until the corresponding rank-k
kernel statement has been checked on paper.

## 6a. The SOURCE authors explicitly considered a simpler Z_k, and rejected it as unproved

An exceptionally relevant remark appears **after Lemma 5.6**, PDF
p.51 (arXiv:2208.03273v6). For establishing the *final path
content-reduction lemma alone*, it would suffice to add basic
one-alphabet coset extensions CE(H_k,A_k;B) rather than the
whole Definition-5.3 full/augmented graph machinery.
The authors say they tried this and **could not prove k-stability
of H_k→G_{k+1}** for that simplified Z_k, and did not know
whether such a procedure could achieve k-stability.

They therefore built ALL of the augmented clusters and
full CE stages, with Section 4 geometry, PRECISELY to guarantee
the stability needed to safely iterate. The source explicitly
states this motivation, rather than presenting the cumbersome
stage family as merely a convenient overcomplete implementation.

This directly supports our audit verdict: while many smaller
families might witness the FINAL endpoint assertion in isolation,
the hard problem is retaining rank-k identity-word kernels at
each intermediate stage. Our detector theorem #334 settles the
algebraic H-step but does not supply that historical-kernel
invariant for a thinner Z_k.

**Caution:** inability to prove the reduced method is NOT a
counterexample to its correctness. It is a sharply scoped
RESEARCH LEAD, not an accepted shorter proof.

## 7. Risk-calibrated conclusion

The algebraic rank lift is strong and humanly equivalent to the
source H-step; that part is NOT the core remaining risk. The
rank-one *shapes* of Z₁ look exhaustively represented by our
three genuine completed stage families for any single input
skeleton K. The outstanding work there is identifying ALL
canonical H₁-covers and their rooted subgraphs. At ranks ≥2,
the source's previous transition-group stage history is
mathematically ESSENTIAL even to the mere existence of a
k-stable cover of the required Z_k family. The no-go example
rules out all-rank group detector lifts as a stand-alone
geometric replacement.

**No new claim of unconditional PSTS EPPA, source
Y_k/Z_k completeness or general bridge freeness is made.**
