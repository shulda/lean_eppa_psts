import PSTSEPPA.ABO.ProperClusterRootTranslatedSignedIso
import PSTSEPPA.ABO.SignedBComponentShapeTransport
import PSTSEPPA.ABO.CayleyLeftTranslations

/-!
# Source ABO 4.5: the actual TWO root translations in the proper cluster

The standard global proper-B-cluster graph theorem identifies a real
signed B-component with the canonical t-translated cluster in H[C].
The original Γ-stage is rooted at an old vertex with ambient coordinate
g∈Γ; hence the correct target is the (g * (t:Γ))-translated proper
B-cluster in Γ, NOT the unshifted Γ cluster or an unrooted subgroup
inclusion.

We prove the missing graph-theoretic composite, preserving ALL genuine
positive/inverse signed edge tokens of incomplete Cayley skeletons.
First translate a cluster by any group element IN ITS OWN GROUP;
this is a real signed labelled-graph isomorphism, not merely equality
of group-coordinate sets. Then invert that isomorphism in local H[C]
and compose with the previously certified H[C]→Γ
`localSignedTranslatedClusterHomOfParent` at the EXACT combined
root `g * (t:Γ)`.

No generatedness or retractability of Γ is assumed. No fake old signed
edge, ambient tag collapse, new axiom or sorry.
-/

namespace PSTSEPPA
namespace ABO
namespace ClusterSpec

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {B : Finset ι}

/-- Left translation by g is an ACTUAL signed graph isomorphism
from an (untranslated) proper B-cluster to its literal g-translated
Cayley skeleton. The maps are on vertices and REAL oriented edge
tokens, with full labels and formal edge inversion. -/
noncomputable def rootTranslatedClusterHom
    (gen : ι → Γ) (P : ClusterSpec B) (g : Γ) :
    LabelledGraphHom
      (P.toLabelledGraph gen)
      ((P.rootTranslatedCayleySubgraph gen g).toEGraph).toLabelledGraph where
  onVertex x :=
    ⟨g * x.1, by
      change g⁻¹ * (g * x.1) ∈ P.VertexSet gen
      simpa using x.2⟩
  onEdge e :=
    ⟨(g * e.1.1, e.1.2), by
      change (g⁻¹ * (g * e.1.1), e.1.2) ∈ P.EdgeSet gen
      simpa using e.2⟩
  map_source e := by
    apply Subtype.ext
    rfl
  map_inv e := by
    apply Subtype.ext
    exact (cayleyLeftTranslateHom gen g).map_inv e.1
  map_label e := rfl

/-- The translated graph map is BIJECTIVE on ALL vertices and on
BOTH oriented signed edge-token classes, with no assumption of
global group generation or ambient graph completeness. -/
theorem rootTranslatedClusterHom_bijective
    (gen : ι → Γ) (P : ClusterSpec B) (g : Γ) :
    Function.Bijective (P.rootTranslatedClusterHom gen g).onVertex ∧
    Function.Bijective (P.rootTranslatedClusterHom gen g).onEdge := by
  constructor
  · constructor
    · intro x y hxy
      apply Subtype.ext
      exact mul_left_cancel (congrArg Subtype.val hxy)
    · intro y
      refine ⟨⟨g⁻¹ * y.1, ?_⟩, ?_⟩
      · change g⁻¹ * y.1 ∈ P.VertexSet gen
        exact y.2
      · apply Subtype.ext
        change g * (g⁻¹ * y.1) = y.1
        group
  · constructor
    · intro e f hef
      apply Subtype.ext
      apply Prod.ext
      · exact mul_left_cancel (congrArg (fun z => z.1.1) hef)
      · exact congrArg (fun z => z.1.2) hef
    · intro y
      refine ⟨⟨(g⁻¹ * y.1.1, y.1.2), ?_⟩, ?_⟩
      · change (g⁻¹ * y.1.1, y.1.2) ∈ P.EdgeSet gen
        exact y.2
      · apply Subtype.ext
        apply Prod.ext
        · change g * (g⁻¹ * y.1.1) = y.1.1
          group
        · rfl

/-- TWO-ROOT TRUE SIGNED GRAPH ISO, with the exact source root.

Local input: genuine t-translated B-cluster in H[C].
Original target: genuine (g*(t:Γ))-translated B-cluster in Γ.
Every signed edge orientation and old/fresh incidence is retained.

The root t is NOT dropped: the first factor inverts translation
by t inside H[C]; the second factor translates its unrooted
B-cluster by the correct ORIGINAL Γ root g*t. -/
noncomputable def localRootTranslatedClusterHomOfParent
    (gen : ι → Γ) (P : ClusterSpec B)
    (C : Finset ι) (hBC : B ⊆ C)
    (g : Γ) (t : generatedSubgroup gen C) :
    LabelledGraphHom
      (((P.rootTranslatedCayleySubgraph
        (trivialCompletionGenerator gen C) t).toEGraph).toLabelledGraph)
      (((P.rootTranslatedCayleySubgraph
        gen (g * (t : Γ))).toEGraph).toLabelledGraph) :=
  (P.localSignedTranslatedClusterHomOfParent gen C hBC
    (g * (t : Γ))).comp
      ((P.rootTranslatedClusterHom
        (trivialCompletionGenerator gen C) t).inverseOfBijective
          (P.rootTranslatedClusterHom_bijective
            (trivialCompletionGenerator gen C) t).1
          (P.rootTranslatedClusterHom_bijective
            (trivialCompletionGenerator gen C) t).2)

/-- The TWO-root Γ transport is bijective on entire vertex and
both oriented actual signed edge token sorts. No ambient Γ
generation/retractability is needed, only B⊆C. -/
theorem localRootTranslatedClusterHomOfParent_bijective
    (gen : ι → Γ) (P : ClusterSpec B)
    (C : Finset ι) (hBC : B ⊆ C)
    (g : Γ) (t : generatedSubgroup gen C) :
    Function.Bijective
      (P.localRootTranslatedClusterHomOfParent gen C hBC g t).onVertex ∧
    Function.Bijective
      (P.localRootTranslatedClusterHomOfParent gen C hBC g t).onEdge := by
  let fL := P.rootTranslatedClusterHom (trivialCompletionGenerator gen C) t
  have hL := P.rootTranslatedClusterHom_bijective
    (trivialCompletionGenerator gen C) t
  let fI := fL.inverseOfBijective hL.1 hL.2
  have hI := fL.inverseOfBijective_bijective hL.1 hL.2
  let fT := P.localSignedTranslatedClusterHomOfParent gen C hBC
    (g * (t : Γ))
  have hT := P.localSignedTranslatedClusterHomOfParent_bijective
    gen C hBC (g * (t : Γ))
  change Function.Bijective (fT.onVertex ∘ fI.onVertex) ∧
    Function.Bijective (fT.onEdge ∘ fI.onEdge)
  exact
    ⟨⟨hT.1.1.comp hI.1.1, hT.1.2.comp hI.1.2⟩,
     ⟨hT.2.1.comp hI.2.1, hT.2.2.comp hI.2.2⟩⟩

end ClusterSpec
end ABO
end PSTSEPPA
