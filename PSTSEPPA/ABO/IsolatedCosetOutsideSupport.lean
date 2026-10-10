import PSTSEPPA.ABO.AllProperCosetEdgeSupport
import PSTSEPPA.ABO.IsolatedCosetCompletion

/-!
# No new outside-A labels under genuine full B-coset gluing

For corrected ABO Proposition 5.4 rank-one stability, stages
built from an A-labelled skeleton must also have trivial
transition action for all generator labels OUTSIDE A.

The previous source-facing theorem shows this for the actual
all-proper multi-coset extension. The singleton type-(2)
augmentation is obtained by adjoining a complete B-coset
with B⊆A. Its new edges thus remain A-labelled, whereas
all old edges retain their original A-labels.

We prove this directly for the real glued EGraph, then use
the LEGAL loop-only completion to show arbitrary words on
C disjoint from A fix every old and fresh vertex. This
requires no ambient group evaluation identity and no
global coset coordinate injectivity.

The source-specific rank-two specialization is a direct
consequence once hSupportOld is supplied by the checked
all-proper quotient edge-label theorem.
-/

namespace PSTSEPPA
namespace ABO
namespace IsolatedCosetGluing

variable {V OldEdge ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

/-- The literal coset-attachment cannot introduce a label
outside its parent A if all old edges were A-labelled
and the attached B is contained in A. -/
theorem glued_edge_label_mem_parent
    (G : EGraph V OldEdge ι)
    (gen : ι → Γ) (A B : Finset ι)
    (hBA : B ⊆ A)
    (g : Γ) (root : V)
    (hMissing : ∀ e : OldEdge,
      G.source e = root → signedBase (G.label e) ∉ B)
    (hOldSupport : ∀ e : OldEdge,
      signedBase (G.label e) ∈ A)
    (e : Edge OldEdge gen B g) :
    signedBase ((gluedEGraph G gen B g root hMissing).label e) ∈ A := by
  cases e with
  | inl e =>
      exact hOldSupport e
  | inr e =>
      exact hBA e.2.2

/-- Every signed C-word for C disjoint from the parent
alphabet A acts trivially at EVERY vertex of the completed
singleton augmentation, regardless of ambient group value. -/
theorem completedStage_outside_parent_word_fixes
    (G : EGraph V OldEdge ι)
    (gen : ι → Γ) (A B : Finset ι)
    (hBA : B ⊆ A)
    (g : Γ) (root : V)
    (hMissing : ∀ e : OldEdge,
      G.source e = root → signedBase (G.label e) ∉ B)
    (hOldSupport : ∀ e : OldEdge,
      signedBase (G.label e) ∈ A)
    (hpaired : G.LocallyPairedLabels)
    (C : Finset ι) (hdis : Disjoint C A)
    (w : LabelWord ι) (hw : LabelWord.Uses C w)
    (v : Vertex V gen B g) :
    (completedStage G gen B g root hMissing hpaired).followWord v w = v := by
  let H := gluedEGraph G gen B g root hMissing
  let hpNew : H.LocallyPairedLabels :=
    glued_locallyPairedLabels G gen B g root hMissing hpaired
  have hSupport : ∀ e : Edge OldEdge gen B g,
      signedBase (H.label e) ∈ A :=
    glued_edge_label_mem_parent
      G gen A B hBA g root hMissing hOldSupport
  exact H.trivialLoopCompletion_disjoint_word_fixes
    A C hSupport hpNew hdis w hw v

end IsolatedCosetGluing
end ABO
end PSTSEPPA
