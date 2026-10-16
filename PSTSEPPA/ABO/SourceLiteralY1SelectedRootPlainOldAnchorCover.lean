import PSTSEPPA.ABO.SourceLiteralY1X2AllPrintedPlainTransitionQuotient
import PSTSEPPA.ABO.SourceLiteralY1X2AllOriginalSelectedRootCoverage
import PSTSEPPA.ABO.SourceLiteralY1SelectedRootAmbientValue
import PSTSEPPA.ABO.StandardCosetFamily

/-!
# ACTUAL literal T(Y₁)-rooted plain P_A anchor and its based T(X₂-all) cover

The corrected ABO Theorem 4.7(ii) starts with an ORIGINAL
incomplete H-Cayley A-component, its true old H root, and
the completed full P_A coset extension of exactly that
component. The root in the completed stage is not an
ambient group-coordinate surrogate: it must be the literal
component-tagged OLD coset-extension vertex, glued by
common intersection-supported (B∩C)-components.

The all-choice finite first-rank action already supplies
a genuine generator-preserving T(X₂^all) Cayley morphism
into EVERY selected literal plain completed P_A stage,
based at ANY chosen stage vertex. The newly certified
first-rank original-cover theorem also lifts EVERY old
H root to some genuine old G root and covers its WHOLE
original signed A-component on vertices and edge tokens.

Here we now CONNECT those data:
* choose the literal old H A-component root as an actual
  vertex of its original incomplete rooted skeleton;
* embed it into the EXACT component-tagged full P_A
  multi-coset quotient by the selected empty-alphabet
  constituent (which exists because |A|=2);
* prove its ambient H-group coordinate is the chosen
  actual group root, WITHOUT asserting ambient injectivity;
* obtain the real based Cayley(T(X₂^all))→completed-P_A
  signed graph cover with identity at precisely this
  old tagged H stage vertex;
* simultaneously choose a genuine G old root above the
  given H root whose A-component surjectively covers all
  old H signed vertices and oriented edges.

This is the exact first-rank rooted input to the source's
Cayley-cover normalization and mixed-support gluing proof.
The F–old-skeleton agreement on the entire selected G
component (and its localization to G[A]) remains a further
explicit source compatibility gate. We do NOT infer that
the H multiCE is globally ambient embedded, that the
G original old A-component map is injective, or that
Condition 5.2, R8 bridge freeness, higher ranks or
unconditional PSTS EPPA have been proved.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Exactly the chosen true original incomplete H=T(Y₁)
A-root, as a point of its ORIGINAL old signed A-component,
not an ambient subgroup A-coset or an X₁-completed graph. -/
noncomputable def sourceLiteralY1SelectedRootOldPoint
    (src dst : ι → V) (base : V)
    (A : Finset ι)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    (sourceLiteralY1DirectRootComponent src dst base A root).Vertex := by
  let K := (sourceLiteralY1DirectOriginalSkeleton src dst base).restrictAlphabet A
  let r : K.Vertex := ⟨root, by trivial⟩
  exact ⟨root, ⟨r, rfl, K.subalphabetReachable_refl A r⟩⟩

/-- The real old root in the selected paper P_A completed
stage has a LITERAL component-index tag (even for B=∅):
it is the exact glued quotient point associated to the
original old A-root in the selected empty constituent.
This definition is valid for any two-letter parent. -/
noncomputable def sourceLiteralY1SelectedRootPlainOldAnchor
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    Quotient (sourceLiteralY1DirectRootMultiCosetSetoid
      src dst base A hcard root (allProperCosetFamily A)) := by
  let L := sourceLiteralY1DirectRootComponent src dst base A root
  have hn : A.Nonempty := Finset.card_pos.mp (by rw [hcard]; decide)
  let hEmpty : (∅ : Finset ι) ∈ (allProperCosetFamily A).alphabets :=
    empty_mem_allProperCosetFamily A hn
  exact Quotient.mk (sourceLiteralY1DirectRootMultiCosetSetoid
    src dst base A hcard root (allProperCosetFamily A))
      (⟨⟨∅, hEmpty⟩,
        L.attachedOfSkeletonVertex ∅
          (sourceLiteralY1SelectedRootOldPoint src dst base A root)⟩ :
        L.MultiCosetRawVertex (allProperCosetFamily A))

/-- The true tagged old root retains EXACTLY its original
ambient T(Y₁) group coordinate; this is a PROJECTION
statement, not injectivity of the full multiCE coordinate
map (which can fail for different component tags). -/
theorem sourceLiteralY1SelectedRootPlainOldAnchor_value
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    sourceLiteralY1SelectedRootAmbientValue
      src dst base A hcard root (allProperCosetFamily A)
        (sourceLiteralY1SelectedRootPlainOldAnchor
          src dst base A hcard root) = root := by
  rfl

/-- The TRUE first-rank finite group's labelled Cayley
cover of the selected literal original rooted P_A
completed signed action, based at its ACTUAL old
component-tagged H root, not just at an arbitrary
ambient coordinate-equal point. -/
noncomputable def sourceLiteralY1X2AllSelectedRootPlainCayleyHom
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    LabelledGraphHom
      (cayleyGraph (sourceLiteralY1X2AllGenerator src dst)).toEGraph.toLabelledGraph
      (sourceLiteralY1SelectedRootPlainCompleteStage
        src dst base A hcard root).toEGraph.toLabelledGraph :=
  sourceLiteralY1X2AllPrintedPlainCayleyHom src dst base
    A hcard root
    (sourceLiteralY1SelectedRootPlainOldAnchor
      src dst base A hcard root)

/-- The based Cayley cover takes the group identity to
PRECISELY the selected OLD tagged H stage anchor. -/
@[simp] theorem sourceLiteralY1X2AllSelectedRootPlainCayleyHom_one
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    (sourceLiteralY1X2AllSelectedRootPlainCayleyHom
      src dst base A hcard root).onVertex 1 =
    sourceLiteralY1SelectedRootPlainOldAnchor
      src dst base A hcard root :=
  sourceLiteralY1X2AllPrintedPlainCayleyHom_one
    src dst base A hcard root
    (sourceLiteralY1SelectedRootPlainOldAnchor
      src dst base A hcard root)

/-- Every original H-root has BOTH:
  (1) a genuine original G-root above it whose actual
      old A-component covers the true H A-component
      surjectively on all signed vertices and edges; and
  (2) ONE real Cayley(G)→the chosen exact completed H
      rooted plain P_A stage whose identity maps to the
      literal OLD component-tagged H root.

Only SURJECTIVE A-component coverage is claimed:
the first-rank G→H quotient is 1-stable, not 2-stable. -/
theorem sourceLiteralY1X2AllSelectedRootPlain_cover_and_oldRoot
    (src dst : ι → V) (base : V)
    (A : Finset ι) (hcard : A.card = 2)
    (root : (sourceLiteralY1 src dst).transitionGroup) :
    ∃ gRoot : (sourceLiteralY1X2AllOriginalSkeleton src dst base).Vertex,
      (sourceLiteralY1X2AllOriginalToY1Hom src dst base).onVertex gRoot =
        (⟨root, by trivial⟩ :
          (sourceLiteralY1DirectOriginalSkeleton src dst base).Vertex) ∧
      Function.Surjective
        ((sourceLiteralY1DirectOriginalSkeleton src dst base).pullbackQuotient_intrinsicBComponentVertexMap
          (sourceLiteralY1X2AllToY1 src dst) A gRoot) ∧
      Function.Surjective
        ((sourceLiteralY1DirectOriginalSkeleton src dst base).pullbackQuotient_intrinsicBComponentEdgeMap
          (sourceLiteralY1X2AllToY1 src dst) A gRoot) ∧
      (sourceLiteralY1X2AllSelectedRootPlainCayleyHom
        src dst base A hcard root).onVertex 1 =
        sourceLiteralY1SelectedRootPlainOldAnchor
          src dst base A hcard root := by
  obtain ⟨gRoot, hImage, hVertex, hEdge⟩ :=
    sourceLiteralY1X2AllOriginal_eachHRoot_AComponent_cover
      src dst base A
      (⟨root, by trivial⟩ :
        (sourceLiteralY1DirectOriginalSkeleton src dst base).Vertex)
  exact ⟨gRoot, hImage, hVertex, hEdge,
    sourceLiteralY1X2AllSelectedRootPlainCayleyHom_one
      src dst base A hcard root⟩

end ABO
end PSTSEPPA
