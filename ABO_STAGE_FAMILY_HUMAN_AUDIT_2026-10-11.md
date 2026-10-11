# Human mathematical audit of the exact ABO Section 5.3 stage families
2026-10-11 · scope: the corrected ABO-I path to finite reflecting groups and PSTS EPPA

**Status: HUMAN CHECK, NOT A NEW LEAN THEOREM.**
Authoritative Lean baseline: main #334, `5 group detector lift; geometric
normalization #331. Primary source: Auinger–Bitterlich–Otto,
*Finite approximation of free groups I: the F-inverse cover problem*
(arXiv:2208.03273v6; final PDF at
https://www2.mathematik.tu-darmstadt.de/~otto/papers/hrfinal25.pdf),
especially Theorem 3.8 (PDF p.19), Theorem 4.7 (p.39–43),
Definition 5.3 (p.46–47), Proposition 5.4 (p.47–48), Condition 5.2 (p.45)
and Proposition 3.24 (p.33–34).
The independent corrected source review is
``6–8 of `sources/PROJECT2_ABO_AUDIT.md` in the October-7 advisory bundle.
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
* The hardest genuinely missing proposition is source-faithful
  construction of ALL C_H from the canonical H_k→X₁ action, followed by
  the **COMPLETE k-STABILITY of X_{k+1}=Y_k ⊔ overline(Z_k)** and
  Theorem-4.7 geometric induction. These use the PREVIOUS stage history;
  they do not follow from k-retractability alone.

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
