import PSTSEPPA.ABO.SourceLiteralY1SelectedLocalRootedAmbientEmbedding
import PSTSEPPA.ABO.MultiCosetSignedParentSupport
import PSTSEPPA.ABO.LocalCosetCayleySlice
import PSTSEPPA.ABO.MultiCosetMorphisms

/-!
# Global source Cayley embedding of the TRUE local signed first-rank component

The original signed full P_A multi-coset extension of the
actual local G[A] old pullback is over the genuine generated
subgroup G[A], with generators outside A completed by 1.
The ORIGINAL finite corrected ABO type-(2) transition group
is instead the whole G=T(X₂^all).

There is NO labelled graph hom from the WHOLE complete
Cayley(G[A]) to Cayley(G) by subgroup inclusion when
labels i outside A act trivially in G[A] but not in G.

The crucial source-correct interface is the ORIGINAL
INCOMPLETE multiCE signed EGraph: EVERY real signed edge
has underlying label in A. On precisely these genuinely
present old/fresh signed edge tokens, subgroup inclusion
G[A]↪G DOES preserve signed sources, formal inverse tokens
and all full signed labels. No artificial outside-A edge
is inserted, and no completion edge is passed upstairs.

We prove the generic support-restricted signed Cayley
composition, specialize it to the ACTUAL first-rank G[A]
original multiCE, and transfer the independently certified
rooted Set.InjOn ambient embedding to its ORIGINAL finite
global G Cayley coordinate map.

This produces the first of the two genuine old signed
morphisms S and M required for the certified based type-(2)
off-B-orbit detector (#657):
  S : genuine original G[A] multiCE -> Cayley(G).
The other one M goes to the true original H[A] old
multiCE, then via rooted source normalization to the
literal printed H old signed stage.

The scope is ONE true selected rooted old A-component.
No global whole-pullback connectedness, subgroup
hom on complete Cayley outside-A labels, 4.7(iii),
R8, higher stages or finite PSTS EPPA is asserted.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ X E : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

namespace EGraph

/-- A genuine signed L→Cayley(G[A]) hom whose original
edges are supported in A can be composed with the
underlying subgroup inclusion to give an EXACT signed
L→Cayley(G) hom.

The support premise is indispensable: outside-A signed
edges of the COMPLETED local Cayley(G[A]) would not map
correctly to the true global Cayley(G). We use only
originally present signed L-edges. -/
noncomputable def aSupportedLocalCayleyToGlobal
    (L : EGraph X E ι)
    (gen : ι → Γ) (A : Finset ι)
    (F : LabelledGraphHom
      L.toLabelledGraph
      (cayleyGraph (trivialCompletionGenerator gen A)).toEGraph.toLabelledGraph)
    (hSupport : ∀ e : E, signedBase (L.label e) ∈ A) :
    LabelledGraphHom
      L.toLabelledGraph
      (cayleyGraph gen).toEGraph.toLabelledGraph where
  onVertex x := ((F.onVertex x : generatedSubgroup gen A) : Γ)
  onEdge e := (((F.onEdge e).1 : Γ), (F.onEdge e).2)
  map_source := by
    intro e
    change ((F.onEdge e).1 : Γ) =
      ((F.onVertex (L.source e) : generatedSubgroup gen A) : Γ)
    exact congrArg (fun x : generatedSubgroup gen A => (x : Γ))
      (F.map_source e)
  map_inv := by
    intro e
    have hs : signedBase (F.onEdge e).2 ∈ A := by
      have hl : (F.onEdge e).2 = L.label e := F.map_label e
      rw [hl]
      exact hSupport e
    have hi := localCayley_inv_leftTranslate
      gen A (1 : Γ) (F.onEdge e) hs
    change
      (((F.onEdge (L.inv e)).1 : Γ),
        (F.onEdge (L.inv e)).2) =
      (cayleyGraph gen).inv
        (((F.onEdge e).1 : Γ), (F.onEdge e).2)
    rw [F.map_inv e]
    simpa using hi
  map_label := by
    intro e
    exact F.map_label e

@[simp] theorem aSupportedLocalCayleyToGlobal_vertex
    (L : EGraph X E ι)
    (gen : ι → Γ) (A : Finset ι)
    (F : LabelledGraphHom
      L.toLabelledGraph
      (cayleyGraph (trivialCompletionGenerator gen A)).toEGraph.toLabelledGraph)
    (hSupport : ∀ e : E, signedBase (L.label e) ∈ A)
    (x : X) :
    (L.aSupportedLocalCayleyToGlobal gen A F hSupport).onVertex x =
      ((F.onVertex x : generatedSubgroup gen A) : Γ) :=
  rfl

@[simp] theorem aSupportedLocalCayleyToGlobal_edge
    (L : EGraph X E ι)
    (gen : ι → Γ) (A : Finset ι)
    (F : LabelledGraphHom
      L.toLabelledGraph
      (cayleyGraph (trivialCompletionGenerator gen A)).toEGraph.toLabelledGraph)
    (hSupport : ∀ e : E, signedBase (L.label e) ∈ A)
    (e : E) :
    (L.aSupportedLocalCayleyToGlobal gen A F hSupport).onEdge e =
      (((F.onEdge e).1 : Γ), (F.onEdge e).2) :=
  rfl

end EGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The ACTUAL original old/fresh full P_A signed multiCE
over the genuine first-rank G[A] pullback maps into the
FULL GLOBAL finite Cayley(T(X₂^all)) through the true
subgroup G[A] inclusion.

This is a labelled graph morphism on EVERY genuine
oriented signed edge token, including old loops and new
completed B-constituents, but NOT on fictitious
outside-A completion loops. -/
noncomputable def sourceLiteralY1SelectedLocalGOldGlobalAmbientSignedHom
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    LabelledGraphHom
      ((sourceLiteralY1SelectedLocalGOldPullback
        src dst base A root).multiCosetEGraph
          (allProperCosetFamily A)
          (sourceLiteralY1SelectedLocalGOld_admissible
            src dst base A hcard root)
          (sourceLiteralY1X2AllLocal_isGenerated src dst A)
          (sourceLiteralY1X2AllLocal_retractable
            src dst A hcard.le)).toLabelledGraph
      (cayleyGraph (sourceLiteralY1X2AllGenerator src dst)).toEGraph.toLabelledGraph := by
  let K := sourceLiteralY1SelectedLocalGOldPullback
    src dst base A root
  let P := allProperCosetFamily A
  let hAdm := sourceLiteralY1SelectedLocalGOld_admissible
    src dst base A hcard root
  let hGen := sourceLiteralY1X2AllLocal_isGenerated src dst A
  let hRet := sourceLiteralY1X2AllLocal_retractable
    src dst A hcard.le
  exact (K.multiCosetEGraph P hAdm hGen hRet).aSupportedLocalCayleyToGlobal
    (sourceLiteralY1X2AllGenerator src dst) A
    (K.multiCosetAmbientHom P hAdm hGen hRet)
    (K.multiCosetEGraph_label_mem_parent P hAdm hGen hRet)

/-- The original signed global Cayley map's coordinate of
any TRUE locally attached G[A] quotient vertex is
EXACTLY its ambient local G[A] coordinate, coerced to
the global finite first-rank G transition group. -/
@[simp] theorem sourceLiteralY1SelectedLocalGOldGlobalAmbientSignedHom_vertex
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup)
    (z : (sourceLiteralY1SelectedLocalGOldPullback
      src dst base A root).MultiCosetVertex
        (allProperCosetFamily A)
        (sourceLiteralY1SelectedLocalGOld_admissible
          src dst base A hcard root)
        (sourceLiteralY1X2AllLocal_isGenerated src dst A)
        (sourceLiteralY1X2AllLocal_retractable
          src dst A hcard.le)) :
    (sourceLiteralY1SelectedLocalGOldGlobalAmbientSignedHom
      src dst base A hcard root).onVertex z =
      (((sourceLiteralY1SelectedLocalGOldPullback
        src dst base A root).multiCosetAmbientValue
          (allProperCosetFamily A)
          (sourceLiteralY1SelectedLocalGOld_admissible
            src dst base A hcard root)
          (sourceLiteralY1X2AllLocal_isGenerated src dst A)
          (sourceLiteralY1X2AllLocal_retractable
            src dst A hcard.le) z :
          generatedSubgroup (sourceLiteralY1X2AllGenerator src dst) A) :
        (sourceLiteralY1X2AllStage src dst).transitionGroup) :=
  rfl

/-- The ALREADY CERTIFIED source-rooted ambient embedding
also holds for the honest global G=T(X₂^all) Cayley
coordinate map on that ONE entire original A-component,
including all old/fresh tagged multiCE vertices.

The generally disconnected global pullback is NOT
assumed embedded, and there are no outside-A old edges. -/
theorem sourceLiteralY1SelectedLocalGOldGlobalAmbientSignedHom_rooted_injOn
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    Set.InjOn
      (sourceLiteralY1SelectedLocalGOldGlobalAmbientSignedHom
        src dst base A hcard root).onVertex
      ((sourceLiteralY1SelectedLocalGOldPullback
        src dst base A root).rootedMultiCosetImage
          (allProperCosetFamily A)
          (sourceLiteralY1SelectedLocalGOld_admissible
            src dst base A hcard root)
          (sourceLiteralY1X2AllLocal_isGenerated src dst A)
          (sourceLiteralY1X2AllLocal_retractable
            src dst A hcard.le)
          (sourceLiteralY1SelectedLocalGOld_identity
            src dst base A root)) := by
  intro x hx y hy hxy
  have hLocal :
      (sourceLiteralY1SelectedLocalGOldPullback
        src dst base A root).multiCosetAmbientValue
          (allProperCosetFamily A)
          (sourceLiteralY1SelectedLocalGOld_admissible
            src dst base A hcard root)
          (sourceLiteralY1X2AllLocal_isGenerated src dst A)
          (sourceLiteralY1X2AllLocal_retractable
            src dst A hcard.le) x =
      (sourceLiteralY1SelectedLocalGOldPullback
        src dst base A root).multiCosetAmbientValue
          (allProperCosetFamily A)
          (sourceLiteralY1SelectedLocalGOld_admissible
            src dst base A hcard root)
          (sourceLiteralY1X2AllLocal_isGenerated src dst A)
          (sourceLiteralY1X2AllLocal_retractable
            src dst A hcard.le) y := by
    apply Subtype.ext
    exact hxy
  exact (sourceLiteralY1SelectedLocal_rootedMultiCoset_injOn
    src dst base A hcard root) hx hy hLocal

end ABO
end PSTSEPPA
