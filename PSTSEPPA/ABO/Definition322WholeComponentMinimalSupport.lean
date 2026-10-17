import PSTSEPPA.ABO.MultiCosetMinimalSupport
import PSTSEPPA.ABO.ComponentIndexMonotonicity

/-!
# ABO Definition 3.22: minimum support of an ENTIRE subgraph

This is the literal component-tagged SUPPORT part of ABO I §3.3.3
and Definition 3.22 (PDF pp.30–31). It is deliberately separate
from the CLUSTER-SHAPE part, which requires the published
Lemma-4.3 induction and is not assumed here.

A vertex z of a genuine tagged coset extension has support (D,c)
when it belongs to a completed D-copy with ORIGINAL intrinsic
skeleton D-component index c. For a vertex set S, the same pair
is a MINIMUM support in the sense of ABO precisely when

  (1) it genuinely supports SOME z in S, i.e. the minimum is
      ATTAINED inside S; and
  (2) every supporting pair (C,q) of EVERY vertex of S has
      D ⊆ C and c maps to q's genuine original C-component
      under the canonical component-index enlargement.

Note that (2) is about inclusion of original old component
TAGS and not equality of ambient group values of DISTINCT
vertices. The latter is generally false.

We certify:
  * the exact source Definition-3.22 data as a predicate on S,
  * source uniqueness of its alphabet and of the indexed
    original D-component tag,
  * the source singleton-support base by the existing
    true intersection-support quotient result, and
  * preservation when unions of patches already carry the
    SAME minimum support.

The difficult part of published Lemma 4.3 is still to PROVE
that minimum supports of genuinely intersecting lower-rank
patches synchronize under the inductive bridge-free /
embeddedness hypotheses. We do not assert that as an axiom,
nor extrapolate singleton support to entire B-components.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Original component-tagged support (D,c) of a TRUE
quotient vertex z of an actual multi-coset extension.
It explicitly remembers the intrinsic old skeleton
component index and is stronger than ambient membership
in a G[D] coset. -/
def HasTaggedSupportAt
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (D : Finset ι) (c : K.ComponentIndex D)
    (z : K.MultiCosetVertex P hadm hgen hret) : Prop :=
  ∃ (hDP : D ∈ P.alphabets)
    (p : K.AttachedCosetVertex D),
      p.1 = c ∧
        K.multiCosetInclude P hadm hgen hret D hDP p = z

/-- The precise MINIMUM support of a whole vertex set,
as in source §3.3.3 / Definition 3.22, with attainment.

No background cluster-property hypothesis is needed
to DEFINE the condition. The source later proves it
for actual off-skeleton B-components by induction.

The 'minimum' is a pair of an alphabet D and the
original K.D-component tag c; neither just its
alphabet nor an ambient Cayley value is enough. -/
def IsMinimalTaggedSupportFor
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (S : Set (K.MultiCosetVertex P hadm hgen hret))
    (D : Finset ι) (c : K.ComponentIndex D) : Prop :=
  (∃ z, z ∈ S ∧ K.HasTaggedSupportAt P hadm hgen hret D c z) ∧
  ∀ (C : Finset ι) (hCP : C ∈ P.alphabets)
    (q : K.AttachedCosetVertex C)
    (z : K.MultiCosetVertex P hadm hgen hret),
    z ∈ S →
      K.multiCosetInclude P hadm hgen hret C hCP q = z →
        ∃ hDC : D ⊆ C,
          K.componentIndexMap D C hDC c = q.1

/-- A minimum support alphabet for a nonempty subset is
unique, regardless of where in the subset each minimum
is attained. This is a direct consequence of the
quantifiers in the source definition, not an inferred
global ambient embedding. -/
theorem minimalTaggedSupport_alphabet_unique
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (S : Set (K.MultiCosetVertex P hadm hgen hret))
    (D C : Finset ι)
    (c : K.ComponentIndex D) (d : K.ComponentIndex C)
    (hD : K.IsMinimalTaggedSupportFor P hadm hgen hret S D c)
    (hC : K.IsMinimalTaggedSupportFor P hadm hgen hret S C d) :
    D = C := by
  obtain ⟨⟨x, hx, hDx⟩, hMinD⟩ := hD
  obtain ⟨⟨y, hy, hCy⟩, hMinC⟩ := hC
  obtain ⟨hDP, p, hpc, hp⟩ := hDx
  obtain ⟨hCP, q, hqd, hq⟩ := hCy
  obtain ⟨hDC, _⟩ := hMinD C hCP q y hy hq
  obtain ⟨hCD, _⟩ := hMinC D hDP p x hx hp
  exact Finset.Subset.antisymm hDC hCD

/-- Once the minimal alphabet D is fixed, the original
intrinsic D-component tag c is also unique. Distinct
old component tags are never identified merely because
they share ambient group coordinates. -/
theorem minimalTaggedSupport_tag_unique
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (S : Set (K.MultiCosetVertex P hadm hgen hret))
    (D : Finset ι) (c d : K.ComponentIndex D)
    (hc : K.IsMinimalTaggedSupportFor P hadm hgen hret S D c)
    (hd : K.IsMinimalTaggedSupportFor P hadm hgen hret S D d) :
    c = d := by
  obtain ⟨⟨x, hx, hCx⟩, hMinC⟩ := hc
  obtain ⟨hDP, p, hpc, hp⟩ := hCx
  obtain ⟨hDD, hDtag⟩ := hd.2 D hDP p x hx hp
  have hSame : K.componentIndexMap D D hDD d = d := by
    simpa only [K.componentIndexMap_self] using
      K.componentIndexMap_self D d
  calc
    c = p.1 := hpc.symm
    _ = K.componentIndexMap D D hDD d := hDtag.symm
    _ = d := hSame

/-- Every singleton vertex has a minimum component-tagged
support, as required before Definition 3.22.

This uses the previously certified ORIGINAL
intersection-support quotient (3.11), including its
component-index refinement, not any assumption that
all connected B-components have singleton supports. -/
theorem allProperCoset_singleton_minimalTaggedSupport
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (z : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret) :
    ∃ (D : Finset ι) (c : K.ComponentIndex D),
      K.IsMinimalTaggedSupportFor
        (allProperCosetFamily A) hadm hgen hret
        ({z} : Set (K.MultiCosetVertex
          (allProperCosetFamily A) hadm hgen hret))
        D c := by
  let P := allProperCosetFamily A
  obtain ⟨D, hDP, p, hp, hMin⟩ :=
    K.allProperCosetVertex_exists_minimal_tagged_support
      hadm hgen hret z
  refine ⟨D, p.1, ?_⟩
  constructor
  · exact ⟨z, Set.mem_singleton z, hDP, p, rfl, hp⟩
  · intro C hCP q y hy hqy
    have hyz : y = z := (Set.mem_singleton_iff).mp hy
    subst y
    obtain ⟨hDC, hPoints⟩ := hMin C hCP q hqy
    refine ⟨hDC, ?_⟩
    have hIdx :
        K.attachedIndex C
            (K.attachedSubalphabetMap D C hDC p) = q.1 :=
      congrArg (K.attachedIndex C) hPoints
    exact hIdx

/-- If two genuine patches have the SAME minimum
old-component-tagged support, their union retains
that support, attained in the first patch.

This is the *elementary set-theoretic* union step in
the source's finite constituent induction; it does
NOT supply the mathematically difficult preceding
synchronization of supports across intersecting patches. -/
theorem minimalTaggedSupport_union
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (S T : Set (K.MultiCosetVertex P hadm hgen hret))
    (D : Finset ι) (c : K.ComponentIndex D)
    (hS : K.IsMinimalTaggedSupportFor P hadm hgen hret S D c)
    (hT : K.IsMinimalTaggedSupportFor P hadm hgen hret T D c) :
    K.IsMinimalTaggedSupportFor P hadm hgen hret (S ∪ T) D c := by
  obtain ⟨⟨z, hz, hSupport⟩, hMinS⟩ := hS
  obtain ⟨_hAttT, hMinT⟩ := hT
  constructor
  · exact ⟨z, Or.inl hz, hSupport⟩
  · intro C hCP q y hy hqy
    rcases hy with hys | hyt
    · exact hMinS C hCP q y hys hqy
    · exact hMinT C hCP q y hyt hqy

end CayleySubgraphSpec
end ABO
end PSTSEPPA
