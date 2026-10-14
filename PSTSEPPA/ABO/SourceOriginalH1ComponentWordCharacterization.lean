import PSTSEPPA.ABO.SourceOriginalH1PathValueNormalization

/-!
# Exact rooted components of the genuine original-edge H₁ Cayley preimage

The input source is the ACTUAL incomplete signed EGraph, not the
artificially completed X₁ action. The canonical H₁ Cayley preimage
retains only original signed edge tokens. We prove an exact
characterization of which first-rank H₁ group elements occur in the
intrinsic A-component of the identity above any original input
vertex u:

  g is in that component  ↔
    g is the value in the actual H₁ of an A-word realized by
    an ORIGINAL signed input path starting at u.

In particular the full original signed path has a lift to the
PRECISE group-word endpoint, not just some unspecified lift;
and conversely the presence of such a canonical lift certifies
a genuinely realized old input path. This identifies the true
rooted component by historical paths, preserving all original
signed edges and every ambient-coset component tag.

This is a source-cover classification gate, NOT an equivalence to
all selected Definition-5.3 Z₁ stages. Corrected Condition 5.2,
Theorem 4.7 and higher-rank induction are separate.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Realization of an ORIGINAL signed path u --w--> v is
equivalent to existence of its exact H₁ Cayley lift rooted
at identity, with *specified* endpoint evalGroup(w), and
the corresponding actual target projection to v.
No path in the completed X₁ graph counts. -/
theorem sourceH1_original_path_iff_exact_H1_lift
    (src dst : ι → V) (u v : V) (w : LabelWord ι) :
    (sourceInputEGraph src dst).Follows u w v ↔
      (sourceH1OriginalSkeleton src dst u).toEGraph.Follows
        (⟨1, by trivial⟩ : (sourceH1OriginalSkeleton src dst u).Vertex)
        w
        (⟨PSTS.SignedWord.evalGroup
            (sourceH1Generator src dst) w, by trivial⟩ :
          (sourceH1OriginalSkeleton src dst u).Vertex) ∧
      sourceH1Orbit src dst u
        (PSTS.SignedWord.evalGroup
          (sourceH1Generator src dst) w) = v := by
  constructor
  · intro hp
    obtain ⟨y, hy, hval, hproj⟩ :=
      sourceH1OriginalSkeleton_original_path_lift_value src dst hp
    have hvertex :
        y =
          (⟨PSTS.SignedWord.evalGroup
              (sourceH1Generator src dst) w, by trivial⟩ :
            (sourceH1OriginalSkeleton src dst u).Vertex) :=
      Subtype.ext hval
    constructor
    · simpa only [hvertex] using hy
    · change sourceH1Orbit src dst u y.1 = v at hproj
      simpa only [hval] using hproj
  · rintro ⟨hlift, horbit⟩
    have hproj :=
      hlift.map (sourceH1OriginalSkeletonHom src dst u)
    change
      (sourceInputEGraph src dst).Follows
        (sourceH1Orbit src dst u 1) w
        (sourceH1Orbit src dst u
          (PSTS.SignedWord.evalGroup (sourceH1Generator src dst) w))
        at hproj
    simpa only [sourceH1Orbit_one, horbit] using hproj

/-- EXACT path-language characterization of the vertices
of the identity's TRUE intrinsic signed A-component in
the original-edge H₁ preimage skeleton. The right-hand
side mentions only REAL original input paths and their
chronological values in the actually constructed H₁. -/
theorem sourceH1_original_root_component_iff_original_word_value
    (src dst : ι → V) (u : V)
    (A : Finset ι) (g : SourceH1 src dst) :
    (∃ y : (sourceH1OriginalSkeleton src dst u).Vertex,
      (sourceH1OriginalSkeleton src dst u).SubalphabetReachable A
        (⟨1, by trivial⟩ :
          (sourceH1OriginalSkeleton src dst u).Vertex) y ∧
      y.1 = g) ↔
    ∃ w : LabelWord ι,
      LabelWord.Uses A w ∧
      ∃ v : V,
        (sourceInputEGraph src dst).Follows u w v ∧
        PSTS.SignedWord.evalGroup
          (sourceH1Generator src dst) w = g := by
  constructor
  · rintro ⟨y, ⟨w, hw, hpath⟩, hval⟩
    have heval :
        PSTS.SignedWord.evalGroup
          (sourceH1Generator src dst) w = y.1 := by
      simpa only [one_mul] using
        (sourceH1OriginalSkeleton_follows_group_value
          src dst u hpath)
    have hproj := hpath.map (sourceH1OriginalSkeletonHom src dst u)
    change
      (sourceInputEGraph src dst).Follows
        (sourceH1Orbit src dst u 1) w
        (sourceH1Orbit src dst u y.1) at hproj
    rw [sourceH1Orbit_one] at hproj
    exact ⟨w, hw, _, hproj, heval.trans hval⟩
  · rintro ⟨w, hw, v, hpath, heval⟩
    obtain ⟨y, hlift, hval, _hproj⟩ :=
      sourceH1OriginalSkeleton_original_path_lift_value
        src dst hpath
    exact ⟨y, ⟨w, hw, hlift⟩, hval.trans heval⟩

end ABO
end PSTSEPPA
