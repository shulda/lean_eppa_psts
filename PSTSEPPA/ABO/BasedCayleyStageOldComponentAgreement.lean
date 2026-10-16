import PSTSEPPA.ABO.CayleyLeftTranslations
import PSTSEPPA.ABO.CayleySubgraphComponents
import PSTSEPPA.ABO.Morphisms

/-!
# Based Cayley-to-stage covers agree with ORIGINAL incomplete old skeleton maps

The corrected ABO Theorem 4.7(ii) obtains G-level
multiCE embeddedness from a based G-Cayley map into
the legal completion of the selected H-level multiCE
stage. One must NOT assume that the H multiCE
ambient Cayley-coordinate map is already injective:
explicit small admissible retractable counterexamples
show it can fail.

The essential compatibility statement is more basic.
Let L be a TRUE incomplete A-labelled G-Cayley
skeleton and T an arbitrary COMPLETE signed EGraph.
Suppose f:L→T is the canonical labelled morphism
of the actual ORIGINAL OLD signed edges into the
completed H-level stage, while F:Cayley(G)→T is
the based labelled cover used to distinguish words.

If f and F agree at one old root r, then on the whole
genuine intrinsic A-connected old component they
agree at EVERY old vertex. Both are labelled graph
morphisms, so the same real signed path from r to x
has one unique endpoint in the deterministic stage T.

In the SOURCE NORMALIZATION F(1)=f(r), the correct
global map is obtained by left translation r⁻¹,
so the exact equality is

    F(r⁻¹ x) = f(x)

for all old x reachable from r. This is not
F(x)=f(x) without translating, which would be false
at arbitrary nonidentity component roots.

Formal inverses, fixed input loops, repeated labels
and nonfaithful complete-stage transitions all work.
This proves the precise rooted-old compatibility
needed for the later H-stage collision argument;
it does not by itself establish multiCE embeddedness,
source Definition 5.3 equivariance, bridge freeness,
higher k induction or PSTS EPPA.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ V E : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

/-- Any two true labelled maps from an ORIGINAL incomplete
Cayley subgraph to the same COMPLETE EGraph, one via the
ambient group Cayley graph and one from the original
signed skeleton, agree at all OLD vertices in the root's
intrinsic A-component once their root images coincide. -/
theorem CayleySubgraphSpec.cayleyStage_agrees_on_old_component
    (L : CayleySubgraphSpec gen A)
    (T : CompleteEGraph V E ι)
    (f : LabelledGraphHom
      L.toEGraph.toLabelledGraph T.toEGraph.toLabelledGraph)
    (F : LabelledGraphHom
      (cayleyGraph gen).toEGraph.toLabelledGraph
      T.toEGraph.toLabelledGraph)
    (root : L.Vertex)
    (hRoot : F.onVertex root.1 = f.onVertex root)
    (x : L.Vertex)
    (hx : L.SubalphabetReachable A root x) :
    F.onVertex x.1 = f.onVertex x := by
  obtain ⟨w, _hw, hPath⟩ := hx
  have hOld :
      T.toEGraph.Follows
        (f.onVertex root) w (f.onVertex x) :=
    hPath.map f
  have hCayley :
      T.toEGraph.Follows
        (F.onVertex root.1) w (F.onVertex x.1) :=
    (hPath.map L.inclusion).map F
  rw [hRoot] at hCayley
  exact T.toEGraph.follows_right_unique hCayley hOld

/-- In the CORRECTED SOURCE normalization F(1)=f(root),
the based original stage cover is first translated by
the inverse of the ACTUAL OLD ROOT's G-coordinate.
The resulting map agrees on the entire connected
original OLD skeleton component, with its exact
component tag and all signed edge paths. -/
theorem CayleySubgraphSpec.basedCayleyStage_agrees_on_old_component
    (L : CayleySubgraphSpec gen A)
    (T : CompleteEGraph V E ι)
    (f : LabelledGraphHom
      L.toEGraph.toLabelledGraph T.toEGraph.toLabelledGraph)
    (F : LabelledGraphHom
      (cayleyGraph gen).toEGraph.toLabelledGraph
      T.toEGraph.toLabelledGraph)
    (root : L.Vertex)
    (hOne : F.onVertex (1 : Γ) = f.onVertex root)
    (x : L.Vertex)
    (hx : L.SubalphabetReachable A root x) :
    F.onVertex (root.1⁻¹ * x.1) = f.onVertex x := by
  let Froot : LabelledGraphHom
      (cayleyGraph gen).toEGraph.toLabelledGraph
      T.toEGraph.toLabelledGraph :=
    F.comp (cayleyLeftTranslateHom gen root.1⁻¹)
  have hRoot : Froot.onVertex root.1 = f.onVertex root := by
    change F.onVertex (root.1⁻¹ * root.1) = f.onVertex root
    simpa using hOne
  have hAgree :=
    L.cayleyStage_agrees_on_old_component
      T f Froot root hRoot x hx
  change F.onVertex (root.1⁻¹ * x.1) = f.onVertex x at hAgree
  exact hAgree

end ABO
end PSTSEPPA
