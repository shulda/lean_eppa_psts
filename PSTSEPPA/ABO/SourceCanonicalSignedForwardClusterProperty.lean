import PSTSEPPA.ABO.CanonicalSignedTranslatedProperCluster
import PSTSEPPA.ABO.ForwardInductionTheorem45

/-!
# ABO Theorem 4.5: canonical concrete signed whole-component CLUSTER PROPERTY

The accepted source global forward theorem produces the complete
Definition-3.22 tagged minimum support for every OFF-SKELETON
signed B-component, and its real FULL-vs-PROPER cluster shape.
However its proper-branch EGraph target was existential and
was not itself declared the CANONICAL g-translated Cayley
cluster graph. The genuine source original signed Lemma 4.3
and the preceding independently tested component image
equalities let us strengthen this without adding assumptions.

Here the proper alternative gives a labelled graph ISOMORPHISM
onto the ACTUAL translated Γ proper B-cluster signed Cayley
skeleton, including the true signed source/incidence, full
positive/negative labels and formal inverse edge tokens.
The attained support (M,m) of the WHOLE B-component is
retained, and its old-component-tagged common-core point
still lies in every active tagged coatom.

The sole inductive premise is the ORIGINAL proper-rooted
bridge freeness, not an additionally assumed cluster property.
This is the precise canonical graph-shape form needed for
root/local k-retractable source transfer via the recently
certified signed translated-cluster equivalence.
No global embedding or additional axioms/sorry.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Genuine PROPER source B-cluster alternative with the
CANONICAL translated signed Cayley skeleton target, not
a freely chosen deterministic graph over equal carriers. -/
def HasCanonicalProperSignedBCosetAlternative
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (anchor : K.MultiCosetVertex
      (allProperCosetFamily A) hadm hgen hret) : Prop :=
  ∃ (core : K.MultiCosetVertex
        (allProperCosetFamily A) hadm hgen hret)
    (hProper :
      ∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
        B ∩ K.properCosetTagAlphabet t ⊂ B),
    (∃ w : LabelWord ι, LabelWord.Uses B w ∧
      (K.multiCosetEGraph
        (allProperCosetFamily A) hadm hgen hret).Follows anchor w core) ∧
    (∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
      core ∈ K.properCosetTagSlice hadm hgen hret B anchor t) ∧
    ∃ f : LabelledGraphHom
      ((K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).BComponentEGraph B anchor).toLabelledGraph
      (((K.activeTaggedLowerClusterSpec
        hadm hgen hret B anchor hProper).rootTranslatedCayleySubgraph
          gen (K.multiCosetAmbientValue
            (allProperCosetFamily A) hadm hgen hret core)).toEGraph.toLabelledGraph),
      Function.Bijective f.onVertex ∧ Function.Bijective f.onEdge

/-- The ORIGINAL proper B-cluster signed graph-shape theorem
admits the CANONICAL translated Cayley cluster, including
actual signed edge tokens, as its isomorphism target. -/
theorem properSignedBCosetAlternative_canonical
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcard : 2 ≤ A.card)
    (B : Finset ι)
    (anchor : K.MultiCosetVertex
      (allProperCosetFamily A) hadm hgen hret)
    (hAlt : K.HasProperSignedBClusterAlternative
      hadm hgen hret B anchor) :
    K.HasCanonicalProperSignedBCosetAlternative
      hadm hgen hret B anchor := by
  obtain ⟨core, hProper, hReach, hAll, _T, _f, _hv, _he⟩ := hAlt
  refine ⟨core, hProper, hReach, hAll, ?_⟩
  exact K.allProperCoset_B_component_canonicalTranslatedCluster_signedIso
    hadm hgen hret hcard B anchor core hAll hProper

/-- Strong complete signed cluster property: OFF-SKELETON
entire-B-component minimum attained in one original
tagged old-component support (M,m), concrete full-B
alternative OR canonical translated-proper-cluster signed
graph isomorphism, plus the genuine support-attaining
old-tagged coatom COMMON CORE. -/
def HasCanonicalExactSignedWholeClusterProperty
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen) : Prop :=
  ∀ (B : Finset ι)
    (hBP : B ∈ (allProperCosetFamily A).alphabets)
    (anchor : K.MultiCosetVertex
      (allProperCosetFamily A) hadm hgen hret),
    (¬ ∃ (x : K.Vertex) (w : LabelWord ι),
      LabelWord.Uses B w ∧
      (K.multiCosetEGraph
        (allProperCosetFamily A) hadm hgen hret).Follows
          ((K.skeletonToMultiCosetHom
            (allProperCosetFamily A) hadm hgen hret
            B hBP).onVertex x)
          w anchor) →
    ∃ (M : Finset ι) (m : K.ComponentIndex M),
      K.IsMinimalTaggedSupportFor
        (allProperCosetFamily A) hadm hgen hret
        {y | ∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph
            (allProperCosetFamily A) hadm hgen hret).Follows anchor w y}
        M m ∧
      (K.HasFullSignedBCosetAlternative hadm hgen hret B anchor ∨
       K.HasCanonicalProperSignedBCosetAlternative hadm hgen hret B anchor) ∧
      ∃ core : K.MultiCosetVertex
        (allProperCosetFamily A) hadm hgen hret,
        (∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph
            (allProperCosetFamily A) hadm hgen hret).Follows anchor w core) ∧
        K.HasTaggedSupportAt
          (allProperCosetFamily A) hadm hgen hret M m core ∧
        ∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
          core ∈ K.properCosetTagSlice hadm hgen hret B anchor t

/-- Canonical source Theorem 4.5 forward signed cluster
property follows solely from the printed ORIGINAL lower
rooted bridge-freeness hypotheses (global retractable Γ
instance). Does not assume the upper cluster property. -/
theorem canonicalExactSignedWholeClusterProperty_of_lowerBridgeFree
    [Finite Γ]
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcard : 2 ≤ A.card)
    (hBridge : K.HasAllLowerRootedBridgeFree hadm hgen hret) :
    K.HasCanonicalExactSignedWholeClusterProperty
      hadm hgen hret := by
  have hBase :=
    K.exactSignedClusterProperty_of_allLowerRootedBridgeFree
      hadm hgen hret hBridge
  intro B hBP anchor hOff
  obtain ⟨M, m, hMin, hShape, core, hReach, hTag, hAll⟩ :=
    hBase B hBP anchor hOff
  refine ⟨M, m, hMin, ?_, core, hReach, hTag, hAll⟩
  rcases hShape with hFull | hProper
  · exact Or.inl hFull
  · exact Or.inr
      (K.properSignedBCosetAlternative_canonical
        hadm hgen hret hcard B anchor hProper)

end CayleySubgraphSpec
end ABO
end PSTSEPPA
