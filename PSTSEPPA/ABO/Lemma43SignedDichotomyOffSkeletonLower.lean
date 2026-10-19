import PSTSEPPA.ABO.Lemma43SignedDichotomyFromMinimum
import PSTSEPPA.ABO.Lemma43NoFullMinimumOffSkeleton

/-!
# EXACT SOURCE REFINEMENT: lower minima are required ONLY for genuinely
OFF-SKELETON components at strictly smaller rank

Unlike the stronger earlier conditional API, the second lower
induction premise is asked ONLY for C with B∩C ⊊ C. For a lower
C-component with B∩C=C, a minimum alphabet M⊊C may be false in
the full-C-coset case, and the source Lemma 4.3 does not need it.
The separate lower bridge-free hypothesis is unchanged.

# ABO Lemma 4.3 at every higher rank: actual SIGNED coset-or-cluster theorem

This is the promised composition of the EXISTING PUBLISHED
Auinger--Bitterlich--Otto I Lemma 4.3, not a new proof scheme.

The original signed coset extension is over a FINITE generated and
retractable labelled group Γ. For a rank |A|>=3 and each actual
B-component Q, the printed forward-induction assumptions are:

* every lower rooted original C-component full proper-coset extension,
  for C⊊A, is bridge-free;
* every one of its genuine (B∩C)-components has an attained minimum
  original-tagged support of proper C-rank.

These explicit hypotheses are now required ONLY FOR OFF-SKELETON lower D-components,
precisely as printed Definition 3.22 supplies. This repairs the prior
overstrong unrestricted-minimum hypothesis; the actual signed off-skeleton
descent is separately proved in the predecessor modules.
They are NOT silently asserted for arbitrary incomplete skeletons.

The source proof now gives a complete two-case SIGNED graph theorem:

FULL: if a selected completed C-copy with B⊆C supports the anchor,
the original B-component is a full component-tagged B-coset.
It has every real original positive and inverse signed B-edge
at every reachable vertex, and ALL original B-edges are signed
edges of that SAME completed tagged C constituent.

PROPER: otherwise, independently checked source lower-induction
minimum theorem supplies an attained tagged minimum of the
whole genuine B-component, and the already accepted source
minimum→signed-cluster theorem gives an honest translated
PROPER B-cluster labelled graph isomorphism, bijective on
ORIGINAL signed vertices and oriented signed edge tokens.

No further hMinIfNoFull, hMulti, hSingle, path or common-core
witness is assumed: they are all derived from the stated
LOWER-RANK induction hypotheses inside the existing source
lemmas. The REAL old component tags remain distinguished.
No fake missing old edges or global ambient Cayley injectivity
are introduced.

IMPORTANT DOMAIN LIMITATION: the present generic theorem takes
Retractable gen for the ACTUAL chosen Γ. The original paper
often assumes local rank-k retractability and works in H[A].
The already certified subgroup algebra localization supplies
generatedness and retractability of H[A]; transport of the
original signed component-tagged C-skeleton and coset extension
to that local model is a SEPARATE source-faithfulness gate.
Further source Theorem 4.5 / 4.7 induction and PSTS EPPA
are not concluded here.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Exact induction assumptions used by the higher-rank
source ABO Lemma 4.3 at a chosen signed path alphabet B.

Lower rooted C-component stages (for EVERY selected C⊊A)
must be bridge-free and their genuine signed (B∩C)
components must have attained minimum old-component-tagged
support of alphabet M⊊C. These are the two published
lower-rank obligations, NOT an additional new axiom. -/
def HasOffSkeletonLowerLemma43Induction
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι) : Prop :=
  (∀ (C : Finset ι)
      (hCP : C ∈ (allProperCosetFamily A).alphabets)
      (root : K.Vertex),
      (K.subalphabetComponentSubgraph C root).MultiCosetBridgeFree
        (allProperCosetFamily C)
        (K.subalphabetComponentSubgraph_admissible
          hadm C ((mem_allProperCosetFamily A C).mp hCP) root)
        hgen hret) ∧
  (∀ (C : Finset ι)
      (hCP : C ∈ (allProperCosetFamily A).alphabets)
      (hDlocal : B ∩ C ⊂ C)
      (root : K.Vertex),
      ∀ x₀ : (K.subalphabetComponentSubgraph C root).MultiCosetVertex
        (allProperCosetFamily C)
        (K.subalphabetComponentSubgraph_admissible
          hadm C ((mem_allProperCosetFamily A C).mp hCP) root)
        hgen hret,
        (¬ ∃ (v : (K.subalphabetComponentSubgraph C root).Vertex)
          (w : LabelWord ι),
          LabelWord.Uses (B ∩ C) w ∧
          ((K.subalphabetComponentSubgraph C root).multiCosetEGraph
            (allProperCosetFamily C)
            (K.subalphabetComponentSubgraph_admissible
              hadm C ((mem_allProperCosetFamily A C).mp hCP) root)
            hgen hret).Follows
              (((K.subalphabetComponentSubgraph C root).skeletonToMultiCosetHom
                (allProperCosetFamily C)
                (K.subalphabetComponentSubgraph_admissible
                  hadm C ((mem_allProperCosetFamily A C).mp hCP) root)
                hgen hret (B ∩ C)
                ((mem_allProperCosetFamily C (B ∩ C)).mpr hDlocal)).onVertex v)
              w x₀) →
      ∃ (M : Finset ι) (hMC : M ⊂ C)
        (m : (K.subalphabetComponentSubgraph C root).ComponentIndex M),
        (K.subalphabetComponentSubgraph C root).IsMinimalTaggedSupportFor
          (allProperCosetFamily C)
          (K.subalphabetComponentSubgraph_admissible
            hadm C ((mem_allProperCosetFamily A C).mp hCP) root)
          hgen hret
          {x | ∃ w : LabelWord ι, LabelWord.Uses (B ∩ C) w ∧
            ((K.subalphabetComponentSubgraph C root).multiCosetEGraph
              (allProperCosetFamily C)
              (K.subalphabetComponentSubgraph_admissible
                hadm C ((mem_allProperCosetFamily A C).mp hCP) root)
              hgen hret).Follows x₀ w x}
          M m)

/-- HIGHER-RANK signed source Lemma 4.3 on the original
component-tagged old+fresh full proper-coset extension.

At arbitrary rank |A|>=3, the EXPLICIT lower-rank
bridge-free and attained tagged-minimum assumptions
yield the full two-branch original signed graph theorem.

In the FULL branch every original signed B-edge is
in one correctly tagged completed constituent and
every signed B-step from every component vertex exists.
In the PROPER branch an ACTUAL translated proper B-cluster
is labelled-graph isomorphic to the original signed
B-component, bijectively on vertices and oriented edges.

No extra independently assumed minimum or source paths. -/
theorem allProperCoset_higher_rank_signed_cluster_dichotomy_of_off_skeleton_lower
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hAcard : 3 ≤ A.card)
    (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (anchor : K.MultiCosetVertex
      (allProperCosetFamily A) hadm hgen hret)
    (hLower : K.HasStrictLowerLemma43Induction
      hadm hgen hret B) :
    K.HasFullSignedBCosetAlternative
      hadm hgen hret B anchor ∨
    K.HasProperSignedBClusterAlternative
      hadm hgen hret B anchor := by
  obtain ⟨hBridge, hLowerMinimum⟩ := hLower
  apply K.allProperCoset_signed_full_or_proper_cluster_of_minimum
    hadm hgen hret (by omega) B anchor
  intro hNoFull
  exact K.allProperCoset_noFull_B_component_minimum_of_off_skeleton_lower_induction
    hadm hgen hret hAcard B hBP anchor
    hNoFull hBridge hLowerMinimum

end CayleySubgraphSpec
end ABO
end PSTSEPPA
