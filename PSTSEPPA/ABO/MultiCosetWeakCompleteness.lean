import PSTSEPPA.ABO.MultiCosetEGraph
import PSTSEPPA.ABO.MultiCosetMorphisms

/-!
# Weak completeness of multi-alphabet coset extensions

ABO, immediately after equation (3.12), observes that if every
generator label occurring in the original skeleton K is covered by
some alphabet selected for coset extension, then *every directed edge*
in the resulting multi-coset E-graph lies in a completed constituent
coset graph.

This is a weak-completeness property, NOT E-graph completeness at
every vertex. In particular, the original skeleton may have missing
edges outside the selected alphabets.

The proof uses the exact source-and-signed-label quotient:
an old skeleton edge with covered label coincides, by deterministic
gluing, with the completed edge carrying that label at the same
original skeleton source in the appropriate selected coset.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Every directed edge in the multi-coset extension has a
representative which is a full-coset edge (rather than an old
outside-alphabet skeleton edge). -/
def MultiCosetWeaklyComplete
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen) : Prop :=
  ∀ e : K.MultiCosetEdgeVertexIncidenceQuotient P hadm hgen hret,
    ∃ (B : Finset ι) (hBP : B ∈ P.alphabets)
      (p : K.AttachedCosetVertex B)
      (s : {s : SignedLabel ι // signedBase s ∈ B}),
      K.multiCosetEdgeInclude P hadm hgen hret B hBP
        (Sum.inr (p, s)) = e

/-- Covering every signed generator occurring in the original
skeleton by some member of P ensures weak completeness of the
entire multi-coset extension. -/
theorem multiCosetWeaklyComplete_of_label_coverage
    (P : CosetFamilySpec A)
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (hcover : ∀ e : K.Edge,
      ∃ B ∈ P.alphabets, signedBase e.1.2 ∈ B) :
    K.MultiCosetWeaklyComplete P hadm hgen hret := by
  intro e
  induction e using Quotient.inductionOn with
  | h raw =>
    rcases raw with ⟨B, edge⟩
    cases edge with
    | inr edge =>
        exact ⟨B.1, B.2, edge.1, edge.2, rfl⟩
    | inl edge =>
        obtain ⟨C, hCP, hlabelC⟩ := hcover edge.1
        let x : K.Vertex := (K.toEGraph).source edge.1
        let p : K.AttachedCosetVertex C :=
          K.attachedOfSkeletonVertex C x
        let s : {s : SignedLabel ι // signedBase s ∈ C} :=
          ⟨edge.1.1.2, hlabelC⟩
        refine ⟨C, hCP, p, s, ?_⟩
        apply (K.multiCosetEGraph P hadm hgen hret).deterministic
        · change
            K.multiCosetInclude P hadm hgen hret C hCP
              (K.attachedOfSkeletonVertex C x) =
            K.multiCosetInclude P hadm hgen hret B.1 B.2
              (K.attachedOfSkeletonVertex B.1 x)
          exact K.multiCosetInclude_skeleton_independent
            P hadm hgen hret C B.1 hCP B.2 x
        · rfl

end CayleySubgraphSpec
end ABO
end PSTSEPPA
