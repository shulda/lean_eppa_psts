import PSTSEPPA.ABO.Lemma43TaggedSliceOverlapByDeletion
import PSTSEPPA.ABO.CoatomEdgeCover

/-!
# ABO Lemma 4.3: connectivity of the actual maximal constituent overlap graph

The PUBLISHED Lemma 4.3 chooses a finite family of maximal
constituent cosets which together cover an actual intrinsic
B-component Q of the old+fresh signed full coset extension.
The finite connected-family common-core induction then needs
the graph on these selected constituent slices, with edges
for NONEMPTY ACTUAL vertex intersections, to be connected.

This file isolates the missing graph-theoretic implication
behind that source paragraph:

If a family of actual vertex slices contains the entire
component Q, all slices are B-reachable from one root,
and EVERY REAL oriented signed B-edge is contained in
at least one of the selected slices, then the graph on
selected slices is connected by REAL intersection vertices.

Crucially a mere VERTEX cover is NOT enough; the source's
certified CoatomEdgeCover supplies the necessary EDGE
coverage for a sufficiently rich maximal-constituent family.
We therefore keep the edge-cover hypothesis explicit, and
do not silently identify an arbitrary minimal vertex-cover
with an edge-cover.

The generic lemma follows an ACTUAL signed B-word path.
Each edge lies inside some selected slice k, so the source's
current slice and k overlap at the actual source, while k
and the next slice overlap at the actual target. This
constructs a finite walk through the intersection graph.
All inverse signed tokens are handled by the original
EGraph.Follows and path inversion, not by fake completion.

The source specialization uses the precise original
component-tagged slice B_i=Q∩v_iH[C_i]; its membership
automatically provides a genuine B-word from the chosen
root of Q.

This still assumes that the selected finite family covers
each true B-edge. Building an ACTUAL finite maximal
coatom family with this property from the published
vertex/edge coset construction and original finite group
is the next separate source Lemma-4.3 obligation.
-/

namespace PSTSEPPA
namespace ABO

namespace EGraph

variable {V Edge ι κ : Type*}
variable [Fintype ι] [DecidableEq ι] [DecidableEq κ]

/-- If a TRUE signed B-path starts in one slice and ends
in another, and EVERY oriented signed B-edge is present
in some selected slice with BOTH actual endpoints, then
the two slice indices are connected in the graph of
literal nonempty overlaps of those selected slices.

No completeness, finiteness of the vertex universe,
or ambient group quotient is assumed. -/
theorem path_endpoint_slices_overlap_connected
    (G : EGraph V Edge ι)
    (B : Finset ι)
    (slices : κ → Set V) (I : Finset κ)
    (hEdgeCover :
      ∀ e : Edge, signedBase (G.label e) ∈ B →
        ∃ k ∈ I,
          G.source e ∈ slices k ∧ G.target e ∈ slices k)
    {u v : V} {w : LabelWord ι}
    (hp : G.Follows u w v)
    (hw : LabelWord.Uses B w)
    (i j : κ) (hi : i ∈ I) (hj : j ∈ I)
    (hu : u ∈ slices i) (hv : v ∈ slices j) :
    Relation.ReflTransGen
      (fun a b : κ =>
        a ∈ I ∧ b ∈ I ∧ (slices a ∩ slices b).Nonempty)
      i j := by
  let R : κ → κ → Prop :=
    fun a b => a ∈ I ∧ b ∈ I ∧ (slices a ∩ slices b).Nonempty
  have hPath :
      ∀ {x y : V} {p : LabelWord ι},
        G.Follows x p y → LabelWord.Uses B p →
          ∀ (a b : κ),
            a ∈ I → b ∈ I →
            x ∈ slices a → y ∈ slices b →
            Relation.ReflTransGen R a b := by
    intro x y p hReal
    induction hReal with
    | nil x =>
        intro _hw a b ha hb hxa hxb
        have hab : R a b :=
          ⟨ha, hb, ⟨x, hxa, hxb⟩⟩
        exact Relation.ReflTransGen.tail
          Relation.ReflTransGen.refl hab
    | @cons x y s p e hsource hlabel hrest ih =>
        intro hpB a b ha hb hxa hyb
        have hLetterB : signedBase (G.label e) ∈ B := by
          rw [hlabel]
          exact hpB.1
        obtain ⟨k, hk, hSourceK, hTargetK⟩ :=
          hEdgeCover e hLetterB
        have hXK : x ∈ slices k := by
          simpa only [hsource] using hSourceK
        have hak : R a k :=
          ⟨ha, hk, ⟨x, hxa, hXK⟩⟩
        have hStep :
            Relation.ReflTransGen R a k :=
          Relation.ReflTransGen.tail Relation.ReflTransGen.refl hak
        have hRest :
            Relation.ReflTransGen R k b :=
          ih hpB.2 k b hk hb hTargetK hyb
        exact hStep.trans hRest
  exact hPath hp hw i j hi hj hu hv

/-- A selected family of true B-connected graph slices with
a nonempty root slice and REAL edge coverage is connected
in its ACTUAL vertex-intersection graph.

It is important that selected slices are subsets of
one B-path component based at anchor, not merely that
their ambient group coordinates lie in one B-coset. -/
theorem selected_B_component_slices_overlap_connected
    (G : EGraph V Edge ι)
    (B : Finset ι) (anchor : V)
    (slices : κ → Set V) (I : Finset κ)
    (root : κ) (hroot : root ∈ I)
    (hNonempty : ∀ i ∈ I, (slices i).Nonempty)
    (hBComponent :
      ∀ i ∈ I, ∀ z ∈ slices i,
        ∃ w : LabelWord ι,
          LabelWord.Uses B w ∧ G.Follows anchor w z)
    (hEdgeCover :
      ∀ e : Edge, signedBase (G.label e) ∈ B →
        ∃ k ∈ I,
          G.source e ∈ slices k ∧ G.target e ∈ slices k) :
    ∀ i ∈ I, Relation.ReflTransGen
      (fun j k : κ =>
        j ∈ I ∧ k ∈ I ∧ (slices j ∩ slices k).Nonempty)
      root i := by
  obtain ⟨u, huRoot⟩ := hNonempty root hroot
  obtain ⟨wu, hwU, hAnchorU⟩ :=
    hBComponent root hroot u huRoot
  intro i hi
  obtain ⟨v, hvI⟩ := hNonempty i hi
  obtain ⟨wv, hwV, hAnchorV⟩ :=
    hBComponent i hi v hvI
  have hUV :
      G.Follows u (PSTS.SignedWord.inv wu ++ wv) v :=
    G.follows_append (G.follows_inverse hAnchorU) hAnchorV
  have hwUV :
      LabelWord.Uses B (PSTS.SignedWord.inv wu ++ wv) :=
    (LabelWord.uses_append B _ _).mpr ⟨hwU.inv, hwV⟩
  exact G.path_endpoint_slices_overlap_connected
    B slices I hEdgeCover hUV hwUV
    root i hroot hi huRoot hvI

end EGraph

variable {ι Γ κ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable [DecidableEq κ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- Exact source Lemma-4.3 connectivity gate for a
finite indexed cover by GENUINE original component-tagged
C_i-coset slices of one TRUE B-component.

The hypothesis that every actual signed B-edge is
contained in some one of the selected slices is made
explicit. CoatomEdgeCover.lean establishes existence
of a coatom *presentation* for each old/fresh edge;
selecting a finite family with ALL such presentations
and then restricting to those meeting this B-component
is a separate constructive step. -/
theorem allProperCoset_tagged_slice_overlap_connected_of_edge_cover
    (hadm : K.AdmissibleForCosetExtension)
    (hgen : IsGenerated gen) (hret : Retractable gen)
    (B : Finset ι)
    (anchor : K.MultiCosetVertex
      (allProperCosetFamily A) hadm hgen hret)
    (C : κ → Finset ι)
    (hCP : ∀ i : κ,
      C i ∈ (allProperCosetFamily A).alphabets)
    (c : ∀ i : κ, K.ComponentIndex (C i))
    (I : Finset κ)
    (root : κ) (hroot : root ∈ I)
    (hNonempty : ∀ i ∈ I,
      (K.allProperCoset_taggedConstituentSlice
        hadm hgen hret B anchor (C i) (hCP i) (c i)).Nonempty)
    (hEdgeCover :
      ∀ e : K.MultiCosetEdgeVertexIncidenceQuotient
          (allProperCosetFamily A) hadm hgen hret,
        signedBase
          ((K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).label e) ∈ B →
        ∃ i ∈ I,
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).source e ∈
            K.allProperCoset_taggedConstituentSlice
              hadm hgen hret B anchor (C i) (hCP i) (c i) ∧
          (K.multiCosetEGraph (allProperCosetFamily A)
            hadm hgen hret).target e ∈
            K.allProperCoset_taggedConstituentSlice
              hadm hgen hret B anchor (C i) (hCP i) (c i)) :
    ∀ i ∈ I, Relation.ReflTransGen
      (fun j k : κ =>
        j ∈ I ∧ k ∈ I ∧
          ((K.allProperCoset_taggedConstituentSlice
            hadm hgen hret B anchor (C j) (hCP j) (c j)) ∩
           (K.allProperCoset_taggedConstituentSlice
            hadm hgen hret B anchor (C k) (hCP k) (c k))).Nonempty)
      root i := by
  let G := K.multiCosetEGraph (allProperCosetFamily A)
    hadm hgen hret
  let slices : κ → Set
      (K.MultiCosetVertex (allProperCosetFamily A)
        hadm hgen hret) :=
    fun i => K.allProperCoset_taggedConstituentSlice
      hadm hgen hret B anchor (C i) (hCP i) (c i)
  have hInside :
      ∀ i ∈ I, ∀ z ∈ slices i,
        ∃ w : LabelWord ι,
          LabelWord.Uses B w ∧ G.Follows anchor w z := by
    intro i _hi z hz
    exact hz.1
  exact G.selected_B_component_slices_overlap_connected
    B anchor slices I root hroot
    hNonempty hInside hEdgeCover

end CayleySubgraphSpec
end ABO
end PSTSEPPA
