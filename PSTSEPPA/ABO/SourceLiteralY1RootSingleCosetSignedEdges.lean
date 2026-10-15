import PSTSEPPA.ABO.SourceLiteralY1RootMultiCosetSetoid
import PSTSEPPA.ABO.LabelledGroupSingleCosetGraphIso
import PSTSEPPA.ABO.MultiCosetRawEdges

/-!
# Selected original rank-two paper/source rooted A-components:
# full single-B signed graph and all raw oriented multi-coset edge transport

The certified oriented signed graph isomorphism of TRUE original
root A-components of literal paper T(Y₁) and source H₁ preserves
the real group generators. We apply the general labelled-group
single-B coset EGraph functor to every B, including the empty
alphabet. Both OLD outside-B oriented edges and NEW inside-B
component-tagged full-coset oriented edges are transported.

We then obtain a bijection of the entire P-indexed disjoint
union of raw signed oriented edges; this bijection commutes with
formal reversal, full signed labels and the true RAW incidence
on the actual tagged attached coset vertices.

The previous rank-two source-to-paper setoid theorem guarantees
that source and paper glued vertex quotients are defined, but
we do not yet assert that the final edge source-and-label
quotient EGraphs coincide: raw source naturality over the
selected quotient and target congruence are next.
-/

namespace PSTSEPPA
namespace ABO

variable {ι V : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype V] [DecidableEq V]

/-- Actual selected original-root single-B signed graph isomorphism,
including OLD outside-B and freshly attached complete inside-B
oriented tokens, and keeping intrinsic B-path component tags. -/
noncomputable def sourceLiteralY1DirectRootSingleCosetGraphHom
    (src dst : ι → V) (base : V)
    (A : Finset ι) (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι) :
    LabelledGraphHom
      ((sourceLiteralY1DirectRootComponent src dst base A root).singleCosetEGraph B).toLabelledGraph
      ((sourceH1OriginalRootComponent src dst base A
        ((sourceH1EquivLiteralY1Transition src dst).symm root)).singleCosetEGraph B).toLabelledGraph := by
  let L := sourceLiteralY1DirectRootComponent src dst base A root
  let K := sourceH1OriginalRootComponent src dst base A
    ((sourceH1EquivLiteralY1Transition src dst).symm root)
  let f := sourceLiteralY1DirectRootComponentGraphHom src dst base A root
  let hb := sourceLiteralY1DirectRootComponentGraphHom_bijective src dst base A root
  let E := (sourceH1EquivLiteralY1Transition src dst).symm
  have hc : ∀ x : L.Vertex, E x.1 = (f.onVertex x).1 := by
    intro x
    rfl
  exact L.labelledGroupIsoSingleCosetGraphHom
    K f hb.1 hb.2 E (sourceLiteralY1Generator_to_sourceH1 src dst) hc B

/-- True bijection of all completed single-B coset extension
vertices AND formal signed directed edge tokens. -/
theorem sourceLiteralY1DirectRootSingleCosetGraphHom_bijective
    (src dst : ι → V) (base : V)
    (A : Finset ι) (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι) :
    Function.Bijective
      (sourceLiteralY1DirectRootSingleCosetGraphHom src dst base A root B).onVertex ∧
    Function.Bijective
      (sourceLiteralY1DirectRootSingleCosetGraphHom src dst base A root B).onEdge := by
  let L := sourceLiteralY1DirectRootComponent src dst base A root
  let K := sourceH1OriginalRootComponent src dst base A
    ((sourceH1EquivLiteralY1Transition src dst).symm root)
  let f := sourceLiteralY1DirectRootComponentGraphHom src dst base A root
  let hb := sourceLiteralY1DirectRootComponentGraphHom_bijective src dst base A root
  let E := (sourceH1EquivLiteralY1Transition src dst).symm
  have hc : ∀ x : L.Vertex, E x.1 = (f.onVertex x).1 := by
    intro x
    rfl
  exact L.labelledGroupIsoSingleCosetGraphHom_bijective
    K f hb.1 hb.2 E (sourceLiteralY1Generator_to_sourceH1 src dst) hc B

/-- Real selected root attached single-B signed edge equivalence,
including both original incomplete skeleton and newly attached edges. -/
noncomputable def sourceLiteralY1DirectRootSingleCosetEdgeEquiv
    (src dst : ι → V) (base : V)
    (A : Finset ι) (root : (sourceLiteralY1 src dst).transitionGroup)
    (B : Finset ι) :
    (sourceLiteralY1DirectRootComponent src dst base A root).SingleCosetEdge B ≃
      (sourceH1OriginalRootComponent src dst base A
        ((sourceH1EquivLiteralY1Transition src dst).symm root)).SingleCosetEdge B :=
  Equiv.ofBijective
    (sourceLiteralY1DirectRootSingleCosetGraphHom src dst base A root B).onEdge
    (sourceLiteralY1DirectRootSingleCosetGraphHom_bijective src dst base A root B).2

/-- Exact bijection on P-indexed disjoint unions of signed
ORIENTED raw edge tokens, retaining the full outer alphabet
index and separate old/new components. -/
noncomputable def sourceLiteralY1DirectRootMultiCosetRawEdgeEquiv
    (src dst : ι → V) (base : V)
    (A : Finset ι) (root : (sourceLiteralY1 src dst).transitionGroup)
    (P : CosetFamilySpec A) :
    (sourceLiteralY1DirectRootComponent src dst base A root).MultiCosetRawEdge P ≃
      (sourceH1OriginalRootComponent src dst base A
        ((sourceH1EquivLiteralY1Transition src dst).symm root)).MultiCosetRawEdge P where
  toFun := fun e =>
    ⟨e.1, sourceLiteralY1DirectRootSingleCosetEdgeEquiv
      src dst base A root e.1.1 e.2⟩
  invFun := fun e =>
    ⟨e.1, (sourceLiteralY1DirectRootSingleCosetEdgeEquiv
      src dst base A root e.1.1).symm e.2⟩
  left_inv := by
    rintro ⟨b, e⟩
    change
      (⟨b, (sourceLiteralY1DirectRootSingleCosetEdgeEquiv src dst base A root b.1).symm
          (sourceLiteralY1DirectRootSingleCosetEdgeEquiv src dst base A root b.1 e)⟩ :
        (sourceLiteralY1DirectRootComponent src dst base A root).MultiCosetRawEdge P) =
      ⟨b, e⟩
    simp
  right_inv := by
    rintro ⟨b, e⟩
    change
      (⟨b, sourceLiteralY1DirectRootSingleCosetEdgeEquiv src dst base A root b.1
          ((sourceLiteralY1DirectRootSingleCosetEdgeEquiv src dst base A root b.1).symm e)⟩ :
        (sourceH1OriginalRootComponent src dst base A
          ((sourceH1EquivLiteralY1Transition src dst).symm root)).MultiCosetRawEdge P) =
      ⟨b, e⟩
    simp

/-- The exact selected-root RAW edge correspondence commutes with
FORMAL signed reversal, including old inverse loops and fresh B-edges. -/
theorem sourceLiteralY1DirectRootMultiCosetRawEdgeEquiv_inv
    (src dst : ι → V) (base : V)
    (A : Finset ι) (root : (sourceLiteralY1 src dst).transitionGroup)
    (P : CosetFamilySpec A)
    (e : (sourceLiteralY1DirectRootComponent src dst base A root).MultiCosetRawEdge P) :
    sourceLiteralY1DirectRootMultiCosetRawEdgeEquiv src dst base A root P
      ((sourceLiteralY1DirectRootComponent src dst base A root).multiCosetRawEdgeInv P e) =
    (sourceH1OriginalRootComponent src dst base A
      ((sourceH1EquivLiteralY1Transition src dst).symm root)).multiCosetRawEdgeInv P
      (sourceLiteralY1DirectRootMultiCosetRawEdgeEquiv src dst base A root P e) := by
  rcases e with ⟨b, e⟩
  apply congrArg (fun q => (⟨b, q⟩ :
    (sourceH1OriginalRootComponent src dst base A
      ((sourceH1EquivLiteralY1Transition src dst).symm root)).MultiCosetRawEdge P))
  exact (sourceLiteralY1DirectRootSingleCosetGraphHom src dst base A root b.1).map_inv e

/-- Transport preserves the EXACT full signed label of each raw
oriented edge, including negative letters and identity generators. -/
theorem sourceLiteralY1DirectRootMultiCosetRawEdgeEquiv_label
    (src dst : ι → V) (base : V)
    (A : Finset ι) (root : (sourceLiteralY1 src dst).transitionGroup)
    (P : CosetFamilySpec A)
    (e : (sourceLiteralY1DirectRootComponent src dst base A root).MultiCosetRawEdge P) :
    (sourceH1OriginalRootComponent src dst base A
      ((sourceH1EquivLiteralY1Transition src dst).symm root)).multiCosetRawEdgeLabel P
      (sourceLiteralY1DirectRootMultiCosetRawEdgeEquiv src dst base A root P e) =
    (sourceLiteralY1DirectRootComponent src dst base A root).multiCosetRawEdgeLabel P e := by
  rcases e with ⟨b, e⟩
  exact (sourceLiteralY1DirectRootSingleCosetGraphHom src dst base A root b.1).map_label e

/-- Raw source INCIDENCE matches the natural family of full B-coset
equivalences on the ACTUAL old signed root A-component, not ambient
left-coset coordinates. -/
theorem sourceLiteralY1DirectRootMultiCosetRawEdgeEquiv_source
    (src dst : ι → V) (base : V)
    (A : Finset ι) (root : (sourceLiteralY1 src dst).transitionGroup)
    (P : CosetFamilySpec A)
    (e : (sourceLiteralY1DirectRootComponent src dst base A root).MultiCosetRawEdge P) :
    sourceLiteralY1DirectRootMultiCosetRawVertexEquiv src dst base A root P
      (⟨e.1,
        ((sourceLiteralY1DirectRootComponent src dst base A root).singleCosetEGraph e.1.1).source e.2⟩ :
        (sourceLiteralY1DirectRootComponent src dst base A root).MultiCosetRawVertex P) =
    (⟨(sourceLiteralY1DirectRootMultiCosetRawEdgeEquiv src dst base A root P e).1,
      ((sourceH1OriginalRootComponent src dst base A
        ((sourceH1EquivLiteralY1Transition src dst).symm root)).singleCosetEGraph e.1.1).source
        (sourceLiteralY1DirectRootMultiCosetRawEdgeEquiv src dst base A root P e).2⟩ :
      (sourceH1OriginalRootComponent src dst base A
        ((sourceH1EquivLiteralY1Transition src dst).symm root)).MultiCosetRawVertex P) := by
  rcases e with ⟨b, e⟩
  apply congrArg (fun q => (⟨b, q⟩ :
    (sourceH1OriginalRootComponent src dst base A
      ((sourceH1EquivLiteralY1Transition src dst).symm root)).MultiCosetRawVertex P))
  exact ((sourceLiteralY1DirectRootSingleCosetGraphHom src dst base A root b.1).map_source e).symm

end ABO
end PSTSEPPA
