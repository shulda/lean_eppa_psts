import PSTSEPPA.ABO.SourceSignedWholeClusterProperty

/-!
# ABO Lemma 4.3: source lower CLUSTER hypotheses imply forward cluster property

The printed hypothesis of Lemma 4.3 is the ACTUAL cluster property
of every embedded lower C-component extension, not an auxiliary
assertion that arbitrary lower D-components have a minimum.

Definition 3.22 supplies the exact source missing ingredient:
for each off-skeleton lower D-component, whether FULL D-coset
or proper D-cluster, the whole D-component has an ATTAINED
original-component-tagged minimum support. Its supporting
alphabet is necessarily proper in the lower parent C, by
the literal selected proper-coset family.

This module extracts that minimum directly from our source-accurate
whole signed cluster-property predicate and combines it with the
lower bridgefreeness hypotheses to instantiate the certified
uniform forward Lemma-4.3 result. No extra minimum assumption,
no fake old signed edge, and no global ambient-coordinate
identification of distinct original component tags.

This is source-faithful Lemma 4.3 under explicit LOWER cluster
and bridge-free hypotheses. Theorem 4.5 then removes the lower
cluster premise by induction on |A| using Proposition 4.4;
that next induction is not silently claimed here.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Uniform source lower-rooted bridge-freeness with respect to the
ACTUAL original component-tagged signed lower C extensions. -/
def HasAllLowerRootedBridgeFree
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen) : Prop :=
  ∀ (C : Finset ι)
    (hCP : C ∈ (allProperCosetFamily A).alphabets)
    (root : K.Vertex),
      (K.subalphabetComponentSubgraph C root).MultiCosetBridgeFree
        (allProperCosetFamily C)
        (K.subalphabetComponentSubgraph_admissible
          hadm C ((mem_allProperCosetFamily A C).mp hCP) root)
        hgen hret

/-- Uniform actual source lower-cluster hypothesis, where the
cluster property quantifies over precisely the lower D-components
DISJOINT from their own old C-skeleton and includes attained
minimum support even for full D-cosets. -/
def HasAllLowerRootedSignedClusterProperty
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen) : Prop :=
  ∀ (C : Finset ι)
    (hCP : C ∈ (allProperCosetFamily A).alphabets)
    (root : K.Vertex),
      (K.subalphabetComponentSubgraph C root).HasExactSignedWholeComponentClusterProperty
        (K.subalphabetComponentSubgraph_admissible
          hadm C ((mem_allProperCosetFamily A C).mp hCP) root)
        hgen hret

/-- The actual Definition-3.22 lower cluster property, together
with lower bridge-freeness, provides the exact uniform input
of the signed forward Lemma 4.3. Crucially, a lower minimum is
requested ONLY if that particular D-component is off its old
C-skeleton, and the minimal support alphabet M is PROVED proper
from its actual supporting constituent. -/
theorem hasUniformOffSkeletonLowerInput_of_lowerClusters
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hBridge : K.HasAllLowerRootedBridgeFree hadm hgen hret)
    (hCluster : K.HasAllLowerRootedSignedClusterProperty hadm hgen hret) :
    K.HasUniformOffSkeletonLowerComponentInput hadm hgen hret := by
  refine ⟨hBridge, ?_⟩
  intro C hCP D hDC root x₀ hOff
  obtain ⟨M, m, hMin, _hShape, _hCore⟩ :=
    hCluster C hCP root D
      ((mem_allProperCosetFamily C D).mpr hDC) x₀ hOff
  obtain ⟨z, _hz, hSupport⟩ := hMin.1
  obtain ⟨hMP, _p, _hTag, _hInclude⟩ := hSupport
  exact ⟨M, (mem_allProperCosetFamily C M).mp hMP, m, hMin⟩

/-- Published ABO Lemma 4.3 in its actual complete signed
whole-component form. Every lower rooted extension is assumed
embedded/bridge-free and has the source exact signed cluster
property, rather than the stronger auxiliary all-D minimum
assumption. It follows that the actual full proper A-extension
has the same signed cluster property.

This is still a conditional step; the cardinality induction of
Theorem 4.5 must produce the lower cluster assumptions from
lower bridgefreeness, and Theorem 4.7 remains separate. -/
theorem hasExactSignedWholeComponentClusterProperty_of_lowerClusters
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hAcard : 3 ≤ A.card)
    (hBridge : K.HasAllLowerRootedBridgeFree hadm hgen hret)
    (hCluster : K.HasAllLowerRootedSignedClusterProperty hadm hgen hret) :
    K.HasExactSignedWholeComponentClusterProperty hadm hgen hret :=
  K.hasExactSignedWholeComponentClusterProperty_of_offSkeletonLower
    hadm hgen hret hAcard
    (K.hasUniformOffSkeletonLowerInput_of_lowerClusters
      hadm hgen hret hBridge hCluster)

end CayleySubgraphSpec
end ABO
end PSTSEPPA
