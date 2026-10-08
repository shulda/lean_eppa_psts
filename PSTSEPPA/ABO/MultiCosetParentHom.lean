import PSTSEPPA.ABO.MultiCosetParentFold
import PSTSEPPA.ABO.SingleCosetEnlargement
import PSTSEPPA.ABO.GraphHomInjectivity

/-!
# Functorial embedding of a family of lower coset extensions into a B-extension

Let P be a selected family of subalphabets C ⊆ B, with B ⊂ A.
The already-checked folding map on the vertex quotient
  CE(G,K;P) → CE(G,K;B)
extends to a labelled E-graph morphism.

On each C-constituent the map agrees literally with the canonical
enlargement CE(G,K;C) → CE(G,K;B). The edge map is well-defined on the
source/signed-label quotient by deterministic B-edges: the vertex
folding map respects identified sources and enlargement preserves labels.
Formal edge reversal and all incidences then descend correctly.

Admissibility gives an injective map on vertices; deterministic
E-graph structure gives injectivity on signed oriented edge tokens.
No global injectivity of the CE → ambient Cayley projection is assumed.

If B itself is selected, the folding maps are surjective on both
vertices and edges. Thus the resulting labelled graph is isomorphic
to the single-B extension, on its literal vertex and edge universes.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- The raw edge map of a lower coset-extension family to the
single-B extension is defined by the checked C→B graph morphism
on each selected C-constituent. -/
noncomputable def multiCosetRawEdgeToParent
    (P : CosetFamilySpec A)
    (B : Finset ι)
    (hPsub : ∀ C ∈ P.alphabets, C ⊆ B)
    (e : K.MultiCosetRawEdge P) : K.SingleCosetEdge B :=
  (K.singleCosetEnlargeHom e.1.1 B
    (hPsub e.1.1 e.1.2)).onEdge e.2

/-- Equal glued sources and equal signed labels give equal parent
B-edges: the crucial quotient congruence. -/
theorem multiCosetRawEdgeToParent_congr
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hPsub : ∀ C ∈ P.alphabets, C ⊆ B)
    (e f : K.MultiCosetRawEdge P)
    (hef : K.MultiCosetRawEdgeRelated P hadm hgen hret e f) :
    K.multiCosetRawEdgeToParent P B hPsub e =
      K.multiCosetRawEdgeToParent P B hPsub f := by
  rcases e with ⟨C, e⟩
  rcases f with ⟨D, f⟩
  rcases hef with ⟨hsource, hlabel⟩
  have hfold := congrArg
    (K.multiCosetVertexToParent P hadm hgen hret B hPsub) hsource
  have hparent :
      K.attachedSubalphabetMap C.1 B (hPsub C.1 C.2)
          ((K.singleCosetEGraph C.1).source e) =
      K.attachedSubalphabetMap D.1 B (hPsub D.1 D.2)
          ((K.singleCosetEGraph D.1).source f) := by
    change
      K.attachedSubalphabetMap C.1 B (hPsub C.1 C.2)
          ((K.singleCosetEGraph C.1).source e) =
        K.attachedSubalphabetMap D.1 B (hPsub D.1 D.2)
          ((K.singleCosetEGraph D.1).source f) at hfold
    exact hfold
  apply (K.singleCosetEGraph B).deterministic
  · calc
      (K.singleCosetEGraph B).source
          ((K.singleCosetEnlargeHom C.1 B (hPsub C.1 C.2)).onEdge e) =
        K.attachedSubalphabetMap C.1 B (hPsub C.1 C.2)
          ((K.singleCosetEGraph C.1).source e) :=
        (K.singleCosetEnlargeHom C.1 B (hPsub C.1 C.2)).map_source e
      _ = K.attachedSubalphabetMap D.1 B (hPsub D.1 D.2)
          ((K.singleCosetEGraph D.1).source f) := hparent
      _ = (K.singleCosetEGraph B).source
          ((K.singleCosetEnlargeHom D.1 B (hPsub D.1 D.2)).onEdge f) :=
        ((K.singleCosetEnlargeHom D.1 B (hPsub D.1 D.2)).map_source f).symm
  · exact
      ((K.singleCosetEnlargeHom C.1 B (hPsub C.1 C.2)).map_label e).trans
        (hlabel.trans
          ((K.singleCosetEnlargeHom D.1 B (hPsub D.1 D.2)).map_label f).symm)

/-- The parent B-edge map descends to the quotient by the actual
source-and-signed-label gluing relation. -/
noncomputable def multiCosetEdgeToParent
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hPsub : ∀ C ∈ P.alphabets, C ⊆ B)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient P hadm hgen hret) :
    K.SingleCosetEdge B :=
  Quotient.liftOn e
    (K.multiCosetRawEdgeToParent P B hPsub)
    (K.multiCosetRawEdgeToParent_congr P hadm hgen hret B hPsub)

/-- The source of the descended edge map is the parent of the
already-glued source vertex. -/
theorem multiCosetEdgeToParent_source
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hPsub : ∀ C ∈ P.alphabets, C ⊆ B)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient P hadm hgen hret) :
    (K.singleCosetEGraph B).source
        (K.multiCosetEdgeToParent P hadm hgen hret B hPsub e) =
      K.multiCosetVertexToParent P hadm hgen hret B hPsub
        ((K.multiCosetEGraph P hadm hgen hret).source e) := by
  induction e using Quotient.inductionOn with
  | h e =>
      rcases e with ⟨C, e⟩
      exact (K.singleCosetEnlargeHom C.1 B
        (hPsub C.1 C.2)).map_source e

/-- Formal reversal of oriented edges is preserved under the
parent B-coset fold. -/
theorem multiCosetEdgeToParent_inv
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hPsub : ∀ C ∈ P.alphabets, C ⊆ B)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient P hadm hgen hret) :
    K.multiCosetEdgeToParent P hadm hgen hret B hPsub
        ((K.multiCosetEGraph P hadm hgen hret).inv e) =
      (K.singleCosetEGraph B).inv
        (K.multiCosetEdgeToParent P hadm hgen hret B hPsub e) := by
  induction e using Quotient.inductionOn with
  | h e =>
      rcases e with ⟨C, e⟩
      exact (K.singleCosetEnlargeHom C.1 B
        (hPsub C.1 C.2)).map_inv e

/-- Signed labels are preserved under the parent B-coset fold. -/
theorem multiCosetEdgeToParent_label
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hPsub : ∀ C ∈ P.alphabets, C ⊆ B)
    (e : K.MultiCosetEdgeVertexIncidenceQuotient P hadm hgen hret) :
    (K.singleCosetEGraph B).label
        (K.multiCosetEdgeToParent P hadm hgen hret B hPsub e) =
      (K.multiCosetEGraph P hadm hgen hret).label e := by
  induction e using Quotient.inductionOn with
  | h e =>
      rcases e with ⟨C, e⟩
      exact (K.singleCosetEnlargeHom C.1 B
        (hPsub C.1 C.2)).map_label e

/-- The canonical family-to-parent fold is an actual labelled
graph morphism, not merely a map on quotient vertices. -/
noncomputable def multiCosetToParentHom
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hPsub : ∀ C ∈ P.alphabets, C ⊆ B) :
    LabelledGraphHom
      (K.multiCosetEGraph P hadm hgen hret).toLabelledGraph
      (K.singleCosetEGraph B).toLabelledGraph where
  onVertex := K.multiCosetVertexToParent P hadm hgen hret B hPsub
  onEdge := K.multiCosetEdgeToParent P hadm hgen hret B hPsub
  map_source := K.multiCosetEdgeToParent_source P hadm hgen hret B hPsub
  map_inv := K.multiCosetEdgeToParent_inv P hadm hgen hret B hPsub
  map_label := K.multiCosetEdgeToParent_label P hadm hgen hret B hPsub

/-- Admissibility ensures this full labelled graph morphism is
injective on vertices for a containing proper B ⊂ A. -/
theorem multiCosetToParentHom_vertex_injective
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι) (hBA : B ⊂ A)
    (hPsub : ∀ C ∈ P.alphabets, C ⊆ B) :
    Function.Injective
      (K.multiCosetToParentHom P hadm hgen hret B hPsub).onVertex :=
  K.multiCosetVertexToParent_injective
    P hadm hgen hret B hBA hPsub

/-- Injectivity on all signed directed edge tokens is forced by
determinism of the multi-coset E-graph. -/
theorem multiCosetToParentHom_edge_injective
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι) (hBA : B ⊂ A)
    (hPsub : ∀ C ∈ P.alphabets, C ⊆ B) :
    Function.Injective
      (K.multiCosetToParentHom P hadm hgen hret B hPsub).onEdge :=
  LabelledGraphHom.edge_injective_of_vertex_injective
    (K.multiCosetToParentHom P hadm hgen hret B hPsub)
    (K.multiCosetToParentHom_vertex_injective
      P hadm hgen hret B hBA hPsub)

/-- The constituent C→B morphism factors through the multi-CE
inclusion and family-to-parent folding, on vertices. -/
theorem multiCosetToParentHom_on_constituent_vertex
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hPsub : ∀ C ∈ P.alphabets, C ⊆ B)
    (C : Finset ι) (hCP : C ∈ P.alphabets)
    (p : K.AttachedCosetVertex C) :
    (K.multiCosetToParentHom P hadm hgen hret B hPsub).onVertex
      ((K.singleCosetToMultiHom P hadm hgen hret C hCP).onVertex p) =
    (K.singleCosetEnlargeHom C B (hPsub C hCP)).onVertex p :=
  rfl

/-- The same constituent factorization holds on signed directed
edge tokens, including their formal inverse tokens. -/
theorem multiCosetToParentHom_on_constituent_edge
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hPsub : ∀ C ∈ P.alphabets, C ⊆ B)
    (C : Finset ι) (hCP : C ∈ P.alphabets)
    (e : K.SingleCosetEdge C) :
    (K.multiCosetToParentHom P hadm hgen hret B hPsub).onEdge
      ((K.singleCosetToMultiHom P hadm hgen hret C hCP).onEdge e) =
    (K.singleCosetEnlargeHom C B (hPsub C hCP)).onEdge e :=
  rfl

/-- If B occurs in the selected alphabet family, the B-parent
fold is surjective on all vertices. -/
theorem multiCosetToParentHom_vertex_surjective
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hPsub : ∀ C ∈ P.alphabets, C ⊆ B)
    (hBP : B ∈ P.alphabets) :
    Function.Surjective
      (K.multiCosetToParentHom P hadm hgen hret B hPsub).onVertex :=
  K.multiCosetVertexToParent_surjective
    P hadm hgen hret B hPsub hBP

/-- If B itself is selected, every B-edge has an original
constituent B-edge preimage in the family graph. -/
theorem multiCosetToParentHom_edge_surjective
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (hPsub : ∀ C ∈ P.alphabets, C ⊆ B)
    (hBP : B ∈ P.alphabets) :
    Function.Surjective
      (K.multiCosetToParentHom P hadm hgen hret B hPsub).onEdge := by
  intro e
  refine ⟨K.multiCosetEdgeInclude P hadm hgen hret B hBP e, ?_⟩
  change (K.singleCosetEnlargeHom B B (hPsub B hBP)).onEdge e = e
  apply (K.singleCosetEGraph B).deterministic
  · calc
      (K.singleCosetEGraph B).source
          ((K.singleCosetEnlargeHom B B (hPsub B hBP)).onEdge e) =
        K.attachedSubalphabetMap B B (hPsub B hBP)
          ((K.singleCosetEGraph B).source e) :=
        (K.singleCosetEnlargeHom B B (hPsub B hBP)).map_source e
      _ = (K.singleCosetEGraph B).source e :=
        K.attachedSubalphabetMap_self B _
  · exact (K.singleCosetEnlargeHom B B (hPsub B hBP)).map_label e

end CayleySubgraphSpec
end ABO
end PSTSEPPA
