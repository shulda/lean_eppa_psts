import PSTSEPPA.ABO.ForwardInductionRootedTagPairTransport
import PSTSEPPA.ABO.Definition322WholeComponentMinimalSupport

/-!
# ABO Definition 3.22: entire-component MINIMUM TAGGED SUPPORT under localization

The exact local/rooted-original labelled EGraph isomorphism preserves
and REFLECTS all actually realized signed paths, as well as every
original supporting tagged attached D-coset pair (D,c). The missing
source step for the cluster property is that a SINGLE MINIMUM
tagged support of an ENTIRE connected B-component is also invariant,
including its attainment at a real vertex and domination of ALL
supporting pairs of EVERY vertex of the whole component.

We define the literal original rooted quotient analogue of
IsMinimalTaggedSupportFor for any vertex subset S, WITHOUT
requiring globally retractable Γ, and prove exact equivalence
for every local vertex subset under the local/original
component-tagged quotient equivalence.

The proof crucially uses NATURALITY of the ORIGINAL old D-component
index equivalences under inclusion D⊆E, not just preservation of
the supporting alphabet or ambient Γ-coordinate. The reverse
direction uses the true inverse tagged attached-coset map.

Together with the accepted genuine signed B-path iff, this is
the main formal support-theoretic gateway for reflecting the
published whole signed cluster property from the globally
retractable H[C] stage back to original k-retractable Γ.

No new axioms/sorry, invented original signed edges, or
equality-by-ambient-group-coordinate gluing is assumed.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ : Type*}
variable [Fintype ι] [DecidableEq ι] [Group Γ]
variable {gen : ι → Γ} {A : Finset ι}

namespace CayleySubgraphSpec

variable (K : CayleySubgraphSpec gen A)

/-- True old rooted component-index maps commute with alphabet
enlargement D⊆E. This records the ORIGINAL component tags
explicitly; it is not an untagged coset-coordinate assertion. -/
theorem rootedLocalComponentIndexEquiv_natural
    (C D E : Finset ι) (hDE : D ⊆ E)
    (root : K.Vertex)
    (d : (K.intrinsicComponentLocalSlice C root).ComponentIndex D) :
    (K.subalphabetComponentSubgraph C root).componentIndexMap
      D E hDE
      (K.rootedLocalComponentIndexEquiv C root D d) =
    K.rootedLocalComponentIndexEquiv C root E
      ((K.intrinsicComponentLocalSlice C root).componentIndexMap
        D E hDE d) :=
  (K.intrinsicComponentLocalSlice C root).componentIndexEquiv_of_graphIso_natural
    (K.subalphabetComponentSubgraph C root)
    (K.intrinsicComponentLocalHom C root)
    (K.intrinsicComponentLocalHom_bijective C root).1
    (K.intrinsicComponentLocalHom_bijective C root).2
    D E hDE d

/-- Source Definition 3.22 minimum for an ENTIRE subset of
the ACTUAL ORIGINAL rooted C-component tagged multiCE quotient.
The tagged pair (D,d) genuinely supports some point of S,
and is below every tagged attached E-coset presentation of
every point in S. The original Γ need not be globally retractable. -/
def ArbitraryRankRootedOriginalMinimalTaggedSupportFor
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (S : Set (Quotient (K.arbitraryRankRootedOriginalMultiCosetSetoid
      C root P hadm hgen hret)))
    (D : Finset ι)
    (d : (K.subalphabetComponentSubgraph C root).ComponentIndex D) : Prop :=
  (∃ z, z ∈ S ∧ K.ArbitraryRankRootedOriginalTaggedSupportAt
    C root P hadm hgen hret D d z) ∧
  ∀ (E : Finset ι) (hEP : E ∈ P.alphabets)
    (p : (K.subalphabetComponentSubgraph C root).AttachedCosetVertex E)
    (z : Quotient (K.arbitraryRankRootedOriginalMultiCosetSetoid
      C root P hadm hgen hret)),
    z ∈ S →
    Quotient.mk
      (K.arbitraryRankRootedOriginalMultiCosetSetoid
        C root P hadm hgen hret)
      (⟨⟨E,hEP⟩,p⟩ :
        (K.subalphabetComponentSubgraph C root).MultiCosetRawVertex P) = z →
    ∃ hDE : D ⊆ E,
      (K.subalphabetComponentSubgraph C root).componentIndexMap
        D E hDE d = p.1

/-- Full source/local naturality of the unique ATTAINED
minimum tagged support (D,c) of ANY WHOLE vertex subset,
under the genuine arbitrary-rank signed-glued quotient
equivalence, not only singleton supports.

The minimum's alphabet is the SAME, and its original
component tag is exactly the real index transport of c.
All other supporting tagged E-coset presentations are
compared by the naturality of component index enlargement.

No globally retractable original Γ hypothesis. -/
theorem arbitraryRankRootedLocalMinimalTaggedSupport_iff_original
    (C : Finset ι) (root : K.Vertex) (P : CosetFamilySpec C)
    (hadm : (K.intrinsicComponentLocalSlice C root).AdmissibleForCosetExtension)
    (hgen : IsGenerated (trivialCompletionGenerator gen C))
    (hret : Retractable (trivialCompletionGenerator gen C))
    (S : Set ((K.intrinsicComponentLocalSlice C root).MultiCosetVertex
      P hadm hgen hret))
    (D : Finset ι)
    (d : (K.intrinsicComponentLocalSlice C root).ComponentIndex D) :
    (K.intrinsicComponentLocalSlice C root).IsMinimalTaggedSupportFor
      P hadm hgen hret S D d ↔
    K.ArbitraryRankRootedOriginalMinimalTaggedSupportFor
      C root P hadm hgen hret
      ((K.arbitraryRankRootedLocalMultiCosetVertexEquiv
        C root P hadm hgen hret) '' S)
      D (K.rootedLocalComponentIndexEquiv C root D d) := by
  let L := K.intrinsicComponentLocalSlice C root
  let M := K.subalphabetComponentSubgraph C root
  let e := K.arbitraryRankRootedLocalMultiCosetVertexEquiv
    C root P hadm hgen hret
  constructor
  · rintro ⟨⟨z, hz, hSupport⟩, hMin⟩
    refine ⟨⟨e z, ⟨z,hz,rfl⟩, ?_⟩, ?_⟩
    · exact (K.arbitraryRankRootedLocalTaggedSupport_iff_original
        C root P hadm hgen hret D d z).mp hSupport
    · intro E hEP p y hy hpy
      obtain ⟨x,hx,rfl⟩ := hy
      let F := K.rootedLocalAttachedCosetEquiv C E
        (P.proper E hEP).subset root
      let q : L.AttachedCosetVertex E := F.symm p
      have hMap :
          K.rootedLocalAttachedCosetMap C E
            (P.proper E hEP).subset root q = p :=
        F.apply_symm_apply p
      have hLocal : L.multiCosetInclude P hadm hgen hret E hEP q = x := by
        apply e.injective
        calc
          e (L.multiCosetInclude P hadm hgen hret E hEP q) =
            Quotient.mk
              (K.arbitraryRankRootedOriginalMultiCosetSetoid
                C root P hadm hgen hret)
              (⟨⟨E,hEP⟩,
                K.rootedLocalAttachedCosetMap C E
                  (P.proper E hEP).subset root q⟩ :
                M.MultiCosetRawVertex P) :=
              K.arbitraryRankRootedLocalMultiCosetVertexEquiv_include
                C root P hadm hgen hret E hEP q
          _ = Quotient.mk
              (K.arbitraryRankRootedOriginalMultiCosetSetoid
                C root P hadm hgen hret)
              (⟨⟨E,hEP⟩,p⟩ : M.MultiCosetRawVertex P) := by rw [hMap]
          _ = e x := hpy
      obtain ⟨hDE,hTag⟩ := hMin E hEP q x hx hLocal
      refine ⟨hDE, ?_⟩
      calc
        M.componentIndexMap D E hDE
            (K.rootedLocalComponentIndexEquiv C root D d) =
          K.rootedLocalComponentIndexEquiv C root E
            (L.componentIndexMap D E hDE d) :=
          K.rootedLocalComponentIndexEquiv_natural C D E hDE root d
        _ = K.rootedLocalComponentIndexEquiv C root E q.1 :=
          congrArg (K.rootedLocalComponentIndexEquiv C root E) hTag
        _ = p.1 := by
          change (K.rootedLocalAttachedCosetMap C E
            (P.proper E hEP).subset root q).1 = p.1
          exact congrArg (fun t : M.AttachedCosetVertex E => t.1) hMap
  · rintro ⟨⟨y, hy, hSupport⟩, hMin⟩
    obtain ⟨z,hz,rfl⟩ := hy
    refine ⟨⟨z,hz,?_⟩, ?_⟩
    · exact (K.arbitraryRankRootedLocalTaggedSupport_iff_original
        C root P hadm hgen hret D d z).mpr hSupport
    · intro E hEP q z hz hqz
      let p : M.AttachedCosetVertex E :=
        K.rootedLocalAttachedCosetMap C E
          (P.proper E hEP).subset root q
      have hp :
          Quotient.mk
            (K.arbitraryRankRootedOriginalMultiCosetSetoid
              C root P hadm hgen hret)
            (⟨⟨E,hEP⟩,p⟩ : M.MultiCosetRawVertex P) =
          e z := by
        calc
          Quotient.mk
              (K.arbitraryRankRootedOriginalMultiCosetSetoid
                C root P hadm hgen hret)
              (⟨⟨E,hEP⟩,p⟩ : M.MultiCosetRawVertex P) =
            e (L.multiCosetInclude P hadm hgen hret E hEP q) :=
            (K.arbitraryRankRootedLocalMultiCosetVertexEquiv_include
              C root P hadm hgen hret E hEP q).symm
          _ = e z := congrArg e hqz
      obtain ⟨hDE,hOrigTag⟩ :=
        hMin E hEP p (e z) ⟨z,hz,rfl⟩ hp
      refine ⟨hDE, ?_⟩
      apply (K.rootedLocalComponentIndexEquiv C root E).injective
      calc
        K.rootedLocalComponentIndexEquiv C root E
            (L.componentIndexMap D E hDE d) =
          M.componentIndexMap D E hDE
            (K.rootedLocalComponentIndexEquiv C root D d) :=
          (K.rootedLocalComponentIndexEquiv_natural
            C D E hDE root d).symm
        _ = p.1 := hOrigTag
        _ = K.rootedLocalComponentIndexEquiv C root E q.1 := rfl

end CayleySubgraphSpec
end ABO
end PSTSEPPA
