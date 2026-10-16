import PSTSEPPA.ABO.CayleyStageProjection
import PSTSEPPA.ABO.CosetConnectivity
import PSTSEPPA.ABO.Morphisms

/-!
# One actual G-Cayley cover forces common completed H-stage terminals

The precise mechanism in corrected ABO Theorem 4.7(ii)
starts with a TRUE labelled Cayley(G) morphism onto the
LEGAL completion of a component-tagged H-coset stage.
It does NOT require the H multiCE ambient H-coordinate
map to be globally injective (which can be false).

Here we isolate the part that is forced by the cover
itself, without pretending the stage is ambient embedded:

* any chronological signed word is followed by the
  same word in the stage, for an arbitrary group root;
* whenever two G-word paths have the SAME original
  terminal G-group element, their two completed
  stage paths have the SAME actual STAGE VERTEX;
* if g lies simultaneously in distinct translated
  group cosets xG[B] and yG[C], there exist actual
  signed words w_B,w_C supported respectively in B
  and C and landing at g; their stage images agree.

This applies to the TWO different B/C supports needed
for exact intersection-support gluing. It handles the
empty alphabet, formal inverses, repeated/trivial
generators and real group loops. No equality of ambient
H-coordinates is used to identify different tagged
stage vertices.

Next work must connect these common stage vertices
to the EXACT tagged H CE representatives via
root-compatible OLD skeleton maps and the source's
completed H-stage embedding; only then can the
mixed B/C support-reflection lemma (#608) yield
G-level multiCE ambient embeddedness. This module
DOES NOT silently discharge that compatibility,
Theorem 4.7(iii), R8 or final PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ V Edge : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]

namespace CompleteEGraph

variable (T : CompleteEGraph V Edge ι)

/-- A genuine signed labelled Cayley(G) cover sends
each ORIGINAL chronological group-word path to
the corresponding complete H-stage signed-word
path, from ANY chosen group point. -/
theorem cayleyStageHom_followWord
    (gen : ι → Γ)
    (F : LabelledGraphHom
      (cayleyGraph gen).toEGraph.toLabelledGraph
      T.toEGraph.toLabelledGraph)
    (g : Γ) (w : LabelWord ι) :
    T.followWord (F.onVertex g) w =
      F.onVertex (g * PSTS.SignedWord.evalGroup gen w) := by
  rw [T.hom_followWord (cayleyGraph gen) F g w]
  exact congrArg F.onVertex
    (cayleyGraph.followWord_eq_mul_evalGroup gen g w)

/-- Two ACTUAL Cayley paths with the same G terminal
have literally the SAME completed stage endpoint.
Nothing like H-multiCE ambient embeddedness is
assumed or used. -/
theorem cayleyStageHom_terminal_eq_of_equal_group_endpoint
    (gen : ι → Γ)
    (F : LabelledGraphHom
      (cayleyGraph gen).toEGraph.toLabelledGraph
      T.toEGraph.toLabelledGraph)
    (x y g : Γ)
    (w₁ w₂ : LabelWord ι)
    (h₁ : (cayleyGraph gen).followWord x w₁ = g)
    (h₂ : (cayleyGraph gen).followWord y w₂ = g) :
    T.followWord (F.onVertex x) w₁ =
      T.followWord (F.onVertex y) w₂ := by
  calc
    T.followWord (F.onVertex x) w₁ =
        F.onVertex ((cayleyGraph gen).followWord x w₁) :=
      T.hom_followWord (cayleyGraph gen) F x w₁
    _ = F.onVertex g := congrArg F.onVertex h₁
    _ = F.onVertex ((cayleyGraph gen).followWord y w₂) :=
      (congrArg F.onVertex h₂).symm
    _ = T.followWord (F.onVertex y) w₂ :=
      (T.hom_followWord (cayleyGraph gen) F y w₂).symm

/-- A group point inside a chosen B-left coset admits
a TRUE signed B-word whose completed H-stage path
ends at the image of exactly THAT group element.
The resulting stage vertex is not identified with
an H-group coordinate or with a different tag. -/
theorem cayleyStageHom_coset_word_image
    (gen : ι → Γ)
    (F : LabelledGraphHom
      (cayleyGraph gen).toEGraph.toLabelledGraph
      T.toEGraph.toLabelledGraph)
    (B : Finset ι) (x g : Γ)
    (hx : g ∈ generatedLeftCoset gen B x) :
    ∃ w : LabelWord ι,
      LabelWord.Uses B w ∧
        T.followWord (F.onVertex x) w =
          F.onVertex g := by
  obtain ⟨w, hw, hEnd⟩ :=
    (mem_generatedLeftCoset_iff_subalphabetReachable gen B x g).mp hx
  refine ⟨w, hw, ?_⟩
  rw [T.hom_followWord (cayleyGraph gen) F x w, hEnd]

/-- The genuine source-Cayley collision at the
intersection of B and C FULL group cosets: two
signed paths supported on DIFFERENT alphabets
end in precisely the SAME tagged completed H-stage
vertex because their ORIGINAL G terminal is equal.
This is the source-relevant part of Thm 4.7(ii). -/
theorem cayleyStageHom_twoCoset_common_terminal
    (gen : ι → Γ)
    (F : LabelledGraphHom
      (cayleyGraph gen).toEGraph.toLabelledGraph
      T.toEGraph.toLabelledGraph)
    (B C : Finset ι)
    (x y g : Γ)
    (hB : g ∈ generatedLeftCoset gen B x)
    (hC : g ∈ generatedLeftCoset gen C y) :
    ∃ (wB wC : LabelWord ι),
      LabelWord.Uses B wB ∧
      LabelWord.Uses C wC ∧
      T.followWord (F.onVertex x) wB =
        T.followWord (F.onVertex y) wC := by
  obtain ⟨wB, hwB, hEndB⟩ :=
    T.cayleyStageHom_coset_word_image gen F B x g hB
  obtain ⟨wC, hwC, hEndC⟩ :=
    T.cayleyStageHom_coset_word_image gen F C y g hC
  exact ⟨wB, wC, hwB, hwC, hEndB.trans hEndC.symm⟩

end CompleteEGraph
end ABO
end PSTSEPPA
