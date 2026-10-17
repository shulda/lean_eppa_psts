import PSTSEPPA.ABO.SourceLiteralY1TaggedFirstRankComponentAssembly
import PSTSEPPA.ABO.GraphHomInjectivity

/-!
# Fully signed component-tagged Cayley edge embeddings at the first rank

The accepted tagged-vertex assembly embeds the original old+fresh
multi-coset extension into the product of its intrinsic old A-component
index with its genuine local Cayley coordinate. Here we strengthen it
to ALL ACTUAL ORIENTED SIGNED EDGE TOKENS.

The signed coordinate of an actual edge is its real image under the
original component-tagged multiCE-to-Cayley labelled graph morphism.
We retain its source's original A-component tag as the first coordinate.
The resulting map is globally injective on signed edge tokens once
the component-tagged vertex map is injective: any two source edges
with equal source and signed label coincide by EGraph determinism.

This includes both formal inverse tokens, genuine signed loops,
and the original source's incomplete old-edge relation. It does not
replace missing old edges with stationary completion loops and does
not conflate distinct old A-components merely sharing a G[A] value.

The first-rank specialization invokes the independently certified
genuine finite source embedding (PR #670), rather than assuming the
entire disconnected old pullback embeds into a single untagged Cayley
graph. These are faithful *tagged* vertex and edge maps; the higher
ABO cluster induction, Condition 5.2, reflecting group and PSTS EPPA
are not consequences of this lemma.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The actual signed directed edge token is sent to its genuine
Cayley signed edge, but with its intrinsically inherited parent
A-component index retained as a first coordinate. -/
def multiCosetComponentTaggedAmbientEdge
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient P hadm hgen hret) :
    K.ComponentIndex A × ActionEdge Γ ι :=
  ((K.multiCosetVertexToParent P hadm hgen hret A
      (fun C hCP => (P.proper C hCP).subset)
      ((K.multiCosetEGraph P hadm hgen hret).source e)).1,
   (K.multiCosetAmbientHom P hadm hgen hret).onEdge e)

/-- Injectivity for ALL original oriented signed edge tokens,
from globally injective component-tagged VERTEX coordinates.

The proof uses the exact original signed graph morphism
rather than falsely inferring target/edge existence from
ambient Cayley coordinates. -/
theorem multiCosetComponentTaggedAmbientEdge_injective_of_vertices
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hVertices : Function.Injective
      (K.multiCosetComponentTaggedAmbientValue P hadm hgen hret)) :
    Function.Injective
      (K.multiCosetComponentTaggedAmbientEdge P hadm hgen hret) := by
  intro e f hef
  let G := K.multiCosetEGraph P hadm hgen hret
  let H := K.multiCosetAmbientHom P hadm hgen hret
  have hTag :
      (K.multiCosetVertexToParent P hadm hgen hret A
        (fun C hCP => (P.proper C hCP).subset) (G.source e)).1 =
      (K.multiCosetVertexToParent P hadm hgen hret A
        (fun C hCP => (P.proper C hCP).subset) (G.source f)).1 :=
    congrArg Prod.fst hef
  have hAmbientEdge : H.onEdge e = H.onEdge f :=
    congrArg Prod.snd hef
  have hAmbientSource :
      K.multiCosetAmbientValue P hadm hgen hret (G.source e) =
      K.multiCosetAmbientValue P hadm hgen hret (G.source f) := by
    change H.onVertex (G.source e) = H.onVertex (G.source f)
    calc
      H.onVertex (G.source e) =
          (cayleyGraph gen).source (H.onEdge e) :=
        (H.map_source e).symm
      _ = (cayleyGraph gen).source (H.onEdge f) :=
        congrArg (cayleyGraph gen).source hAmbientEdge
      _ = H.onVertex (G.source f) := H.map_source f
  have hTaggedSource :
      K.multiCosetComponentTaggedAmbientValue P hadm hgen hret
          (G.source e) =
      K.multiCosetComponentTaggedAmbientValue P hadm hgen hret
          (G.source f) :=
    Prod.ext hTag hAmbientSource
  have hSource : G.source e = G.source f :=
    hVertices hTaggedSource
  have hLabel : G.label e = G.label f := by
    calc
      G.label e = (cayleyGraph gen).label (H.onEdge e) :=
        (H.map_label e).symm
      _ = (cayleyGraph gen).label (H.onEdge f) :=
        congrArg (cayleyGraph gen).label hAmbientEdge
      _ = G.label f := H.map_label f
  exact G.deterministic hSource hLabel

/-- The EVERY-old-root componentwise source embedding theorem
supplies both globally injective TAGGED vertex and signed edge
coordinates without assuming that the old pullback is A-connected. -/
theorem multiCosetComponentTaggedAmbientEdge_injective_of_all_roots
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hRoots : ∀ r : K.Vertex,
      Set.InjOn (K.multiCosetAmbientValue P hadm hgen hret)
        (K.rootedMultiCosetImage P hadm hgen hret r)) :
    Function.Injective
      (K.multiCosetComponentTaggedAmbientEdge P hadm hgen hret) :=
  K.multiCosetComponentTaggedAmbientEdge_injective_of_vertices
    P hadm hgen hret
    (K.multiCosetComponentTaggedAmbientValue_injective_of_all_roots
      P hadm hgen hret hRoots)

end CayleySubgraphSpec

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- TRUE original finite corrected ABO first-rank graph:
all oriented signed old/fresh P_A edges have globally
injective Cayley edge tokens once the original intrinsic
old A-component tag is remembered. -/
theorem sourceLiteralY1SelectedLocal_componentTaggedSignedEdge_injective
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    Function.Injective
      ((sourceLiteralY1SelectedLocalGOldPullback
        src dst base A root).multiCosetComponentTaggedAmbientEdge
          (allProperCosetFamily A)
          (sourceLiteralY1SelectedLocalGOld_admissible
            src dst base A hcard root)
          (sourceLiteralY1X2AllLocal_isGenerated src dst A)
          (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le)) := by
  let K := sourceLiteralY1SelectedLocalGOldPullback
    src dst base A root
  exact K.multiCosetComponentTaggedAmbientEdge_injective_of_all_roots
    (allProperCosetFamily A)
    (sourceLiteralY1SelectedLocalGOld_admissible
      src dst base A hcard root)
    (sourceLiteralY1X2AllLocal_isGenerated src dst A)
    (sourceLiteralY1X2AllLocal_retractable src dst A hcard.le)
    (fun r => sourceLiteralY1SelectedLocal_everyOldRoot_rootedMultiCoset_injOn
      src dst base A hcard root r)

end ABO
end PSTSEPPA
