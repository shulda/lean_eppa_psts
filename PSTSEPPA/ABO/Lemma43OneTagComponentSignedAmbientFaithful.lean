import PSTSEPPA.ABO.Lemma43WholeComponentAmbientFaithful
import PSTSEPPA.ABO.Lemma43WholeComponentSignedEdgeFaithful
import PSTSEPPA.ABO.TrueSignedBComponentImageGraphIso

/-!
# ABO Lemma 4.3: genuine signed B-component inside ONE tagged coatom embeds faithfully

The accepted multi-constituent branch first synchronizes all
active original coatom tags over one skeleton anchor, then
establishes vertex and oriented signed-edge faithfulness of
the ambient group-coordinate map on that ONE B-component.

The ONE-constituent case is simpler. If ALL vertices of
a true intrinsic signed B-component Q lie in ONE selected
full C-constituent with ONE ORIGINAL old skeleton
C-component tag c, then the entire ambient Cayley map
is already injective on the vertices and REAL oriented
signed B-edge tokens of Q.

The statement does NOT assume the source of every edge is
a C-completed edge. Edge injectivity only requires
source vertex injectivity and deterministic oriented
signed labels, which hold for the ORIGINAL incomplete
multi-coset EGraph, including inverse tokens and loops.

Proof chooses a REAL original old skeleton vertex x
representing c and applies accepted common-old-anchor
gluing injectivity; it then applies signed graph
determinism to equality of mapped source and signed
label for the TRUE B-component edge set.

This is a source-faithfulness theorem without finite-group
or no-smaller-support assumptions. The separate
one-constituent / no-lower-support actual C-edge
rigidity theorem ensures that the EDGE IMAGE is
the expected B∩C-coset edge set in that branch.
Together these are prerequisites for the remaining
one-constituent labelled graph isomorphism.

No global coset-extension Cayley injection,
fictional old edge completion or new axiom/sorry.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Actual one-original-C-tag ambient vertex faithfulness of
ONE signed B-component of the original full proper CE.

All vertices must have true presentations inside the SAME
old skeleton C-component, but different vertices may be
represented by different attached points p of that copy.
No global ambient Cayley embedding is assumed. -/
theorem allProperCoset_one_tagged_C_B_component_ambient_vertex_injOn
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C : Finset ι)
    (hCP : C ∈ (allProperCosetFamily A).alphabets)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (c : K.ComponentIndex C)
    (hContained :
      ∀ y : K.MultiCosetVertex (allProperCosetFamily A)
          hadm hgen hret,
        (∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).Follows anchor w y) →
        ∃ pC : K.AttachedCosetVertex C,
          pC.1 = c ∧
          y = K.multiCosetInclude (allProperCosetFamily A)
            hadm hgen hret C hCP pC) :
    Set.InjOn
      (K.multiCosetAmbientValue (allProperCosetFamily A)
        hadm hgen hret)
      ((K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).BComponentVertexSet B anchor) := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  obtain ⟨x, hx⟩ := K.componentClass_surjective C c
  apply K.multiCosetAmbientValue_injOn_of_common_old_anchor
    P hadm hgen hret x (G.BComponentVertexSet B anchor)
  intro y hy
  obtain ⟨pC, hpCtag, hpCy⟩ := hContained y hy
  refine ⟨C, hCP, pC, ?_, hpCy.symm⟩
  exact hpCtag.trans hx.symm

/-- Under the SAME exact single old-C-tag hypothesis,
the original oriented signed B-edge quotient embeds
faithfully into ambient Cayley signed edge tokens.
This does NOT require that every true B-edge lie
inside a completed C-constituent, only that its
genuine SOURCE belongs to the chosen B-component. -/
theorem allProperCoset_one_tagged_C_B_component_ambient_signed_edge_injOn
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B C : Finset ι)
    (hCP : C ∈ (allProperCosetFamily A).alphabets)
    (anchor : K.MultiCosetVertex (allProperCosetFamily A)
      hadm hgen hret)
    (c : K.ComponentIndex C)
    (hContained :
      ∀ y : K.MultiCosetVertex (allProperCosetFamily A)
          hadm hgen hret,
        (∃ w : LabelWord ι, LabelWord.Uses B w ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).Follows anchor w y) →
        ∃ pC : K.AttachedCosetVertex C,
          pC.1 = c ∧
          y = K.multiCosetInclude (allProperCosetFamily A)
            hadm hgen hret C hCP pC) :
    Set.InjOn
      (K.multiCosetEdgeQuotientAmbient
        (allProperCosetFamily A) hadm hgen hret)
      ((K.multiCosetEGraph (allProperCosetFamily A)
        hadm hgen hret).BComponentEdgeSet B anchor) := by
  let P := allProperCosetFamily A
  let G := K.multiCosetEGraph P hadm hgen hret
  let H := K.multiCosetAmbientHom P hadm hgen hret
  have hV : Set.InjOn
      (K.multiCosetAmbientValue P hadm hgen hret)
      (G.BComponentVertexSet B anchor) :=
    K.allProperCoset_one_tagged_C_B_component_ambient_vertex_injOn
      hadm hgen hret B C hCP anchor c hContained
  intro e he f hf hef
  have heReach : G.source e ∈ G.BComponentVertexSet B anchor := he.2
  have hfReach : G.source f ∈ G.BComponentVertexSet B anchor := hf.2
  have hAmbientSource :
      K.multiCosetAmbientValue P hadm hgen hret (G.source e) =
        K.multiCosetAmbientValue P hadm hgen hret (G.source f) := by
    change H.onVertex (G.source e) = H.onVertex (G.source f)
    calc
      H.onVertex (G.source e) =
          (cayleyGraph gen).source (H.onEdge e) :=
        (H.map_source e).symm
      _ = (cayleyGraph gen).source (H.onEdge f) := by
        change H.onEdge e = H.onEdge f at hef
        rw [hef]
      _ = H.onVertex (G.source f) := H.map_source f
  have hSource : G.source e = G.source f :=
    hV heReach hfReach hAmbientSource
  have hLabel : G.label e = G.label f := by
    calc
      G.label e = (cayleyGraph gen).label (H.onEdge e) :=
        (H.map_label e).symm
      _ = (cayleyGraph gen).label (H.onEdge f) := by
        change H.onEdge e = H.onEdge f at hef
        rw [hef]
      _ = G.label f := H.map_label f
  exact G.deterministic hSource hLabel

end CayleySubgraphSpec
end ABO
end PSTSEPPA
