import PSTSEPPA.ABO.MultiCosetEGraph
import PSTSEPPA.ABO.MultiCosetMorphisms

/-!
# Canonical embeddings of coset extensions under enlargement of the family

For an admissible Cayley skeleton K, an inclusion P.alphabets⊆Q.alphabets
induces a canonical labelled E-graph morphism
  CE(G,K;P) → CE(G,K;Q).
The underlying gluing of tagged coset points is by the SAME exact
intersection-support relation, irrespective of which additional
alphabets are present in the family Q.

Consequently this graph morphism is injective both on quotient vertices
and signed directed edge tokens. On edges, source-label determinism
in the target Q extension supplies the quotient-level map.
The construction preserves formal reversal and labels exactly.

This is a useful functoriality interface for reducing the full family
of all proper alphabets to the maximal proper subfamily in the forward
induction; no globally injective ambient Cayley projection, bridge
freeness or cluster property is assumed.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Inclusion of selected families preserves the EXACT tagged vertex
gluing relation. This defines the canonical quotient vertex map. -/
def multiCosetFamilyVertexMap
    (P Q : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hPQ : P.alphabets ⊆ Q.alphabets) :
    K.MultiCosetVertex P hadm hgen hret →
      K.MultiCosetVertex Q hadm hgen hret :=
  fun z =>
    Quotient.liftOn z
      (fun raw : K.MultiCosetRawVertex P =>
        K.multiCosetInclude Q hadm hgen hret
          raw.1.1 (hPQ raw.1.2) raw.2)
      (by
        intro x y hxy
        apply Quotient.sound
        change K.ShareIntersectionSupport
          x.1.1 y.1.1 x.2 y.2
        exact hxy)

/-- The inclusion maps constituent tagged vertices literally to
their corresponding Q-constituent presentations. -/
@[simp]
theorem multiCosetFamilyVertexMap_include
    (P Q : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hPQ : P.alphabets ⊆ Q.alphabets)
    (B : Finset ι) (hBP : B ∈ P.alphabets)
    (p : K.AttachedCosetVertex B) :
    K.multiCosetFamilyVertexMap P Q hadm hgen hret hPQ
      (K.multiCosetInclude P hadm hgen hret B hBP p) =
      K.multiCosetInclude Q hadm hgen hret B (hPQ hBP) p :=
  rfl

/-- The Q-gluing never identifies two vertices that were distinct
in the P-gluing. Different component tags are respected. -/
theorem multiCosetFamilyVertexMap_injective
    (P Q : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hPQ : P.alphabets ⊆ Q.alphabets) :
    Function.Injective
      (K.multiCosetFamilyVertexMap P Q hadm hgen hret hPQ) := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | h x =>
      induction y using Quotient.inductionOn with
      | h y =>
          apply Quotient.sound
          have hrelQ :
              K.ShareIntersectionSupport
                x.1.1 y.1.1 x.2 y.2 := by
            have h := Quotient.exact hxy
            change K.ShareIntersectionSupport
              x.1.1 y.1.1 x.2 y.2 at h
            exact h
          exact hrelQ

/-- Map signed directed edge tokens between the glued extensions.
Equal source-and-label classes in P remain equal in Q since the
vertex map preserves sources and Q is deterministic. -/
noncomputable def multiCosetFamilyEdgeMap
    (P Q : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hPQ : P.alphabets ⊆ Q.alphabets) :
    K.MultiCosetEdgeVertexIncidenceQuotient P hadm hgen hret →
      K.MultiCosetEdgeVertexIncidenceQuotient Q hadm hgen hret :=
  fun z =>
    Quotient.liftOn z
      (fun raw : K.MultiCosetRawEdge P =>
        K.multiCosetEdgeInclude Q hadm hgen hret
          raw.1.1 (hPQ raw.1.2) raw.2)
      (by
        intro e f hef
        have hs :
            K.multiCosetRawEdgeSource P hadm hgen hret e =
              K.multiCosetRawEdgeSource P hadm hgen hret f :=
          hef.1
        have hLift := congrArg
          (K.multiCosetFamilyVertexMap P Q hadm hgen hret hPQ) hs
        apply (K.multiCosetEGraph Q hadm hgen hret).deterministic
        · change
            K.multiCosetInclude Q hadm hgen hret
              e.1.1 (hPQ e.1.2)
              ((K.singleCosetEGraph e.1.1).source e.2) =
            K.multiCosetInclude Q hadm hgen hret
              f.1.1 (hPQ f.1.2)
              ((K.singleCosetEGraph f.1.1).source f.2)
          exact hLift
        · exact hef.2)

/-- The edge inclusion agrees literally with its constituent edge. -/
@[simp]
theorem multiCosetFamilyEdgeMap_include
    (P Q : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hPQ : P.alphabets ⊆ Q.alphabets)
    (B : Finset ι) (hBP : B ∈ P.alphabets)
    (e : K.SingleCosetEdge B) :
    K.multiCosetFamilyEdgeMap P Q hadm hgen hret hPQ
      (K.multiCosetEdgeInclude P hadm hgen hret B hBP e) =
      K.multiCosetEdgeInclude Q hadm hgen hret B (hPQ hBP) e :=
  rfl

/-- The vertex- and edge-level inclusion maps form a genuine
labelled graph morphism, compatible with actual signed paths. -/
noncomputable def multiCosetFamilyHom
    (P Q : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hPQ : P.alphabets ⊆ Q.alphabets) :
    LabelledGraphHom
      (K.multiCosetEGraph P hadm hgen hret).toLabelledGraph
      (K.multiCosetEGraph Q hadm hgen hret).toLabelledGraph where
  onVertex := K.multiCosetFamilyVertexMap P Q hadm hgen hret hPQ
  onEdge := K.multiCosetFamilyEdgeMap P Q hadm hgen hret hPQ
  map_source := by
    intro e
    induction e using Quotient.inductionOn with
    | h raw => rfl
  map_inv := by
    intro e
    induction e using Quotient.inductionOn with
    | h raw => rfl
  map_label := by
    intro e
    induction e using Quotient.inductionOn with
    | h raw => rfl

/-- The induced graph embedding is also injective on signed
directed edge tokens; no new edge identification appears by
adding more coset alphabets. -/
theorem multiCosetFamilyEdgeMap_injective
    (P Q : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hPQ : P.alphabets ⊆ Q.alphabets) :
    Function.Injective
      (K.multiCosetFamilyEdgeMap P Q hadm hgen hret hPQ) := by
  intro e f hef
  let F := K.multiCosetFamilyHom P Q hadm hgen hret hPQ
  apply (K.multiCosetEGraph P hadm hgen hret).deterministic
  · apply K.multiCosetFamilyVertexMap_injective
      P Q hadm hgen hret hPQ
    calc
      F.onVertex ((K.multiCosetEGraph P hadm hgen hret).source e) =
        (K.multiCosetEGraph Q hadm hgen hret).source (F.onEdge e) :=
        (F.map_source e).symm
      _ = (K.multiCosetEGraph Q hadm hgen hret).source (F.onEdge f) :=
        congrArg _ hef
      _ = F.onVertex ((K.multiCosetEGraph P hadm hgen hret).source f) :=
        F.map_source f
  · calc
      (K.multiCosetEGraph P hadm hgen hret).label e =
        (K.multiCosetEGraph Q hadm hgen hret).label (F.onEdge e) :=
        (F.map_label e).symm
      _ = (K.multiCosetEGraph Q hadm hgen hret).label (F.onEdge f) :=
        congrArg _ hef
      _ = (K.multiCosetEGraph P hadm hgen hret).label f :=
        F.map_label f

end CayleySubgraphSpec
end ABO
end PSTSEPPA
