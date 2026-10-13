import PSTSEPPA.ABO.Type1ClusterCatalogueAnchor
import PSTSEPPA.ABO.SourceG2LocalCayleyCovers

/-!
# The actual finite source G₂ Cayley graph covers all local type-(1) clusters

Corrected ABO Definition 5.3 contains genuine augmented
type-(1) CLUSTER actions as well as the type-(2) full coset
extensions. The input-dependent finite G₂ includes the complete
all-local three-family action over EVERY pair (A,K). At each A,
the type-(1) augmented-cluster family does not depend on K,
so a canonical edgeless full-vertex Γ[A] skeleton indexes
its literal occurrence in the actual catalogue.

The preceding exact catalogue embedding preserves ALL signed
action words, retaining all chosen cluster and fresh point tags.
The separately certified actual source G₂ Cayley cover maps each
group word to its genuine endpoint on this labelled disjoint
action, with no injectivity assumption on ambient H₁ coordinates.

Here we compose them, obtaining for EVERY type-(1) augmented
cluster choice and EVERY vertex of its LEGAL completed action
a concrete G₂ Cayley covering map rooted at the corresponding
exact tagged source-catalogue point. All signed paths, negative
letters and fixed-point loops are represented literally.

This is a local type-(1) occurrence and action-cover theorem.
The source Z₁ type-(1) family must still be matched to the
corresponding Γ[A] cluster models; corrected Condition 5.2 and
higher-rank reflecting-group induction remain open.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The actual type-(1) cluster completed-stage point inside the
genuine finite source G₂ catalogue, indexed by the explicit
edgeless local (A,K₀) skeleton. All original cluster/fresh
vertex tags remain distinct. -/
noncomputable def sourceG2Type1CatalogueBasepoint
    (src dst : ι → V)
    (A : Finset ι) (hcard : A.card = 2)
    (x : Σ j : ClusterSpec.augmentedType1Index
      (trivialCompletionGenerator (sourceH1Generator src dst) A) A,
        ClusterSpec.augmentedType1Vertex j) :
    sourceG2LocalStageVertex src dst :=
  type1StageVertexIntoAllLocalG2
    (sourceH1Generator src dst)
    (sourceH1_twoRetractable src dst)
    A hcard x

/-- The identity element of the ACTUAL generated source G₂
maps to this literal type-(1) augmented-cluster vertex. -/
@[simp] theorem sourceG2Type1CatalogueCover_one
    (src dst : ι → V)
    (A : Finset ι) (hcard : A.card = 2)
    (x : Σ j : ClusterSpec.augmentedType1Index
      (trivialCompletionGenerator (sourceH1Generator src dst) A) A,
        ClusterSpec.augmentedType1Vertex j) :
    (sourceG2LocalCayleyHom src dst
      (sourceG2Type1CatalogueBasepoint src dst A hcard x)).onVertex 1 =
    sourceG2Type1CatalogueBasepoint src dst A hcard x :=
  sourceG2LocalCayleyHom_one src dst
    (sourceG2Type1CatalogueBasepoint src dst A hcard x)

/-- Every actual signed word w in the concrete finite source G₂,
evaluated in its genuine Cayley graph, reaches EXACTLY the same
old/fresh tagged cluster vertex as following w in the literal
completed type-(1) cluster stage. No abstract coordinate-only
or merely group-kernel assertion is substituted. -/
theorem sourceG2Type1CatalogueCover_word
    (src dst : ι → V)
    (A : Finset ι) (hcard : A.card = 2)
    (x : Σ j : ClusterSpec.augmentedType1Index
      (trivialCompletionGenerator (sourceH1Generator src dst) A) A,
        ClusterSpec.augmentedType1Vertex j)
    (w : LabelWord ι) :
    (sourceG2LocalCayleyHom src dst
      (sourceG2Type1CatalogueBasepoint src dst A hcard x)).onVertex
      (PSTS.SignedWord.evalGroup
        (sourceAllLocalG2Generator src dst) w) =
    sourceG2Type1CatalogueBasepoint src dst A hcard
      ((ClusterSpec.augmentedType1FamilyStage
        (trivialCompletionGenerator (sourceH1Generator src dst) A) A
       ).followWord x w) := by
  calc
    (sourceG2LocalCayleyHom src dst
      (sourceG2Type1CatalogueBasepoint src dst A hcard x)).onVertex
        (PSTS.SignedWord.evalGroup
          (sourceAllLocalG2Generator src dst) w) =
      (sourceG2LocalCompleteStage src dst).followWord
        (sourceG2Type1CatalogueBasepoint src dst A hcard x) w :=
        sourceG2LocalCayleyHom_word src dst
          (sourceG2Type1CatalogueBasepoint src dst A hcard x) w
    _ = sourceG2Type1CatalogueBasepoint src dst A hcard
          ((ClusterSpec.augmentedType1FamilyStage
            (trivialCompletionGenerator (sourceH1Generator src dst) A) A
          ).followWord x w) :=
        type1StageVertexIntoAllLocalG2_followWord
          (sourceH1Generator src dst)
          (sourceH1_twoRetractable src dst)
          A hcard x w

end ABO
end PSTSEPPA
