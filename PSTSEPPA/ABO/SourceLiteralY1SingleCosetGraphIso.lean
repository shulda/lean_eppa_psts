import PSTSEPPA.ABO.LabelledGroupSingleCosetGraphIso
import PSTSEPPA.ABO.SourceLiteralY1TaggedCosetAttachments

/-!
# Literal paper T(Y₁) versus source H₁: actual signed single-B coset graphs

The printed original OLD input-edge T(Y₁)-Cayley preimage and
the synchronized SourceH₁ old preimage are separately certified
isomorphic as incomplete signed oriented labelled EGraphs over the
ORIGINAL input. Their actual generators agree under the independently
certified same-labelled group equivalence.

We instantiate the generic component-tagged single-coset EGraph
naturality theorem with those concrete source models: for EVERY
subalphabet B, including the empty one, all genuinely present
old outside-B edge tokens and freshly added inside-B full-coset
signed edge tokens match bijectively. We preserve sources,
targets, labels, formal inversion and arbitrary realised signed
paths, including loops and repeated labels.

No selected root A-component, proper-family multi-coset gluing,
B-augmentation or Definition-5.3 Z₁ catalogue identity is claimed.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- The actual paper-to-source comparison of every complete tagged
single-B attachment is a genuine labelled morphism between signed
EGraphs. It uses only old input signed edges plus actual B-coset
completed signed edges, not the artificial complete X₁ action. -/
noncomputable def sourceLiteralY1DirectSingleCosetGraphHom
    (src dst : ι → V) (base : V) (B : Finset ι) :
    LabelledGraphHom
      ((sourceLiteralY1DirectOriginalSkeleton src dst base).singleCosetEGraph B).toLabelledGraph
      ((sourceH1OriginalSkeleton src dst base).singleCosetEGraph B).toLabelledGraph :=
  (sourceLiteralY1DirectOriginalSkeleton src dst base).labelledGroupIsoSingleCosetGraphHom
    (sourceH1OriginalSkeleton src dst base)
    (sourceLiteralY1DirectToSourceH1OriginalHom src dst base)
    (sourceLiteralY1DirectToSourceH1OriginalHom_bijective src dst base).1
    (sourceLiteralY1DirectToSourceH1OriginalHom_bijective src dst base).2
    (sourceH1EquivLiteralY1Transition src dst).symm
    (sourceLiteralY1Generator_to_sourceH1 src dst)
    (sourceLiteralY1DirectToSourceH1_coordinate src dst base) B

/-- This map is bijective on actual attached vertices AND all formal
directed signed edge tokens, retaining separate component tags. -/
theorem sourceLiteralY1DirectSingleCosetGraphHom_bijective
    (src dst : ι → V) (base : V) (B : Finset ι) :
    Function.Bijective
      (sourceLiteralY1DirectSingleCosetGraphHom src dst base B).onVertex ∧
    Function.Bijective
      (sourceLiteralY1DirectSingleCosetGraphHom src dst base B).onEdge := by
  exact (sourceLiteralY1DirectOriginalSkeleton src dst base).labelledGroupIsoSingleCosetGraphHom_bijective
    (sourceH1OriginalSkeleton src dst base)
    (sourceLiteralY1DirectToSourceH1OriginalHom src dst base)
    (sourceLiteralY1DirectToSourceH1OriginalHom_bijective src dst base).1
    (sourceLiteralY1DirectToSourceH1OriginalHom_bijective src dst base).2
    (sourceH1EquivLiteralY1Transition src dst).symm
    (sourceLiteralY1Generator_to_sourceH1 src dst)
    (sourceLiteralY1DirectToSourceH1_coordinate src dst base) B

/-- An original paper T(Y₁) completed single-B graph realises a
chronological signed word between attached points iff the corresponding
actual source-H₁ completed single-B graph realises that same word. -/
theorem sourceLiteralY1DirectSingleCosetGraphHom_follows_iff
    (src dst : ι → V) (base : V) (B : Finset ι)
    (u v : (sourceLiteralY1DirectOriginalSkeleton src dst base).AttachedCosetVertex B)
    (w : LabelWord ι) :
    ((sourceLiteralY1DirectOriginalSkeleton src dst base).singleCosetEGraph B).Follows u w v ↔
      ((sourceH1OriginalSkeleton src dst base).singleCosetEGraph B).Follows
        ((sourceLiteralY1DirectSingleCosetGraphHom src dst base B).onVertex u) w
        ((sourceLiteralY1DirectSingleCosetGraphHom src dst base B).onVertex v) := by
  exact (sourceLiteralY1DirectOriginalSkeleton src dst base).labelledGroupIsoSingleCosetGraphHom_follows_iff
    (sourceH1OriginalSkeleton src dst base)
    (sourceLiteralY1DirectToSourceH1OriginalHom src dst base)
    (sourceLiteralY1DirectToSourceH1OriginalHom_bijective src dst base).1
    (sourceLiteralY1DirectToSourceH1OriginalHom_bijective src dst base).2
    (sourceH1EquivLiteralY1Transition src dst).symm
    (sourceLiteralY1Generator_to_sourceH1 src dst)
    (sourceLiteralY1DirectToSourceH1_coordinate src dst base) B u v w

end ABO
end PSTSEPPA
