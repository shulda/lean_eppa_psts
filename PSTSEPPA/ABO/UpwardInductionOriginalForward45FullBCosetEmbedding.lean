import PSTSEPPA.ABO.UpwardInductionOriginalBComponentSignedFullCosetEmbedding
import PSTSEPPA.ABO.CanonicalSignedTranslatedProperCluster

/-!
# ORIGINAL source forward Theorem4.5 produces the TRUE full-H[B] signed component embedding

The corrected ABO upward Theorem 4.7(iii) nonisolated proper
B-cluster case requires an ACTUAL signed labelled graph
morphism from the ORIGINAL old-component-tagged B-component
of CE(H,L_H;P_A) to its canonical full H[B] left coset,
INJECTIVE on original quotient vertices.

The accepted forward Theorem4.5 already produces a
VERTEX- AND ORIENTED SIGNED EDGE-bijective genuine
labelled graph morphism from the ENTIRE original
B-component to the canonical g-left-translated proper
B-cluster, under exactly its genuine common-core and
strict lower-constituent hypotheses. The independently
green #931 source module embeds that TRUE canonical
translated B-cluster in the actual complete H[B] coset.

We compose these TWO ACTUAL signed graph morphisms.
No free arbitrary B-component coordinate injection
remains. The resulting original signed B-component→full
H[B] coset morphism preserves BOTH positive and inverse
old edge tokens, original source/target incidence,
and is injective on true component-tagged old vertices.

The remaining forward/upward interface is to extract
these genuine hAll/hProper hypotheses from the source
whole-component cluster-property alternative at the
precise ORIGINAL historical H-stage. This theorem does
not assume global H coset extension ambient injectivity,
invent missing old B-edges, or identify unrelated
components by equal H group coordinates.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ] [Finite Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- ACTUAL ORIGINAL selected proper signed B-component→full
H[B]-coset labelled morphism, automatically produced by
the previously accepted ORIGINAL forward canonical signed
B-cluster isomorphism. The signed coset map is injective
on every ORIGINAL component-tagged old B-vertex.

This is the concrete coordinate injection for the
NONISOLATED whole-B-component augmented stage. -/
theorem allProperCoset_originalBComponent_signedFullBCosetEmbedding
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcard : 2 ≤ A.card)
    (B : Finset ι)
    (anchor core : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (hAll :
      ∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
        core ∈ K.properCosetTagSlice hadm hgen hret B anchor t)
    (hProper :
      ∀ t ∈ K.activeTaggedCoatoms hadm hgen hret B anchor,
        B ∩ K.properCosetTagAlphabet t ⊂ B) :
    ∃ cHom : LabelledGraphHom
        (((K.multiCosetEGraph (allProperCosetFamily A)
          hadm hgen hret).BComponentEGraph B anchor).toLabelledGraph)
        (((IsolatedCosetGluing.fullCosetSubgraph gen B
          (K.multiCosetAmbientValue
            (allProperCosetFamily A) hadm hgen hret core)).toEGraph).toLabelledGraph),
      Function.Injective cHom.onVertex := by
  let G := K.multiCosetEGraph (allProperCosetFamily A)
    hadm hgen hret
  let P := K.activeTaggedLowerClusterSpec
    hadm hgen hret B anchor hProper
  let g := K.multiCosetAmbientValue
    (allProperCosetFamily A) hadm hgen hret core
  obtain ⟨f, hfV, _hfE⟩ :=
    K.allProperCoset_B_component_canonicalTranslatedCluster_signedIso
      hadm hgen hret hcard B anchor core hAll hProper
  let cHom := G.originalBComponentToFullBCosetHom
    B anchor gen P g f
  refine ⟨cHom, ?_⟩
  exact G.originalBComponentToFullBCosetHom_vertex_injective
    B anchor gen P g f hfV.1

end CayleySubgraphSpec
end ABO
end PSTSEPPA
