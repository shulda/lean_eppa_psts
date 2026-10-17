import PSTSEPPA.ABO.PullbackSingleCosetSignedNaturality
import PSTSEPPA.ABO.PullbackMultiCosetTaggedVertexNaturality
import PSTSEPPA.ABO.MultiCosetEGraph
import PSTSEPPA.ABO.KStablePullbackAdmissibility

/-!
# The genuine ORIGINAL signed G-pullback multiCE → original H multiCE morphism

One real ORIGINAL incomplete H-Cayley skeleton K, a labelled
quotient Q:G↠H, its exact signed old-edge pullback L=Q^-1(K),
and the true component-tagged full multi-coset extensions
CE(G,L;P) and CE(H,K;P).

Previously checked (and required as mathematical dependencies):
* a well-defined TRUE component-tagged full multiCE vertex
  quotient map from G to H, respecting intersection-support
  gluing and original old-skeleton inclusions;
* full signed single-B coset-extension graph morphisms for
  every B∈P, preserving REAL old signed outside-B edges
  separately from freshly completed B-coset signed edges,
  sources, formal inverses and entire signed labels.

Here we descend the entire family of oriented edge maps through
the REAL source-and-FULL-SIGNED-LABEL edge quotient of the
multiCE, not through equality of ambient Cayley group edges.

Well-definedness of the quotient edge map uses precisely:
  (i) equality of the SOURCE *component-tagged glued*
      quotient vertices, transported by the true vertex map;
  (ii) equality of the FULL signed labels.
The target H EGraph is deterministic; hence the images of raw
edge tokens agree. The same naturality shows compatibility
with formal edge inversion of BOTH signs (including geometric
loops), edge source and signed label.

The result is a G-original→H-original TRUE labelled graph
morphism on ALL old+fresh tagged multiCE points AND EVERY
actual oriented signed edge. Its vertex map is EXACTLY
the independently constructed component-tag-preserving map.

NO claim of H ambient injection, G pullback connectedness,
full A-stability or invented original old edges is made.
This signed map is the essential missing OLD H geometry
input to the based source type-(2) augmentation detector
and corrected ABO Theorem 4.7(iii).
The other essential source input — aligning the correct
printed augmented Cayley map at one chosen off-B root —
remains separate.
-/

namespace PSTSEPPA
namespace ABO

variable {ι Γ Δ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Group Γ] [Group Δ]
variable {genΓ : ι → Γ} {genΔ : ι → Δ}
variable {A : Finset ι}

namespace CayleySubgraphSpec

/-- The exact SOURCE naturality of one raw original/fresh
oriented signed edge under the genuine G/H multiCE map.
We compare actual GLUED source vertices, never just
equal coordinates in H. -/
theorem pullbackQuotient_multiCosetRawEdge_source_natural
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (P : CosetFamilySpec A)
    (hAdmG : (K.pullbackQuotient Q).AdmissibleForCosetExtension)
    (hGenG : IsGenerated genΓ) (hRetG : Retractable genΓ)
    (hAdmH : K.AdmissibleForCosetExtension)
    (hGenH : IsGenerated genΔ) (hRetH : Retractable genΔ)
    (e : (K.pullbackQuotient Q).MultiCosetRawEdge P) :
    K.multiCosetRawEdgeSource P hAdmH hGenH hRetH
        ⟨e.1,
          (K.pullbackQuotient_singleCosetHom Q e.1.1).onEdge e.2⟩ =
      K.pullbackQuotient_multiCosetVertexToBase
        Q P hAdmG hGenG hRetG hAdmH hGenH hRetH
        ((K.pullbackQuotient Q).multiCosetRawEdgeSource
          P hAdmG hGenG hRetG e) := by
  rcases e with ⟨⟨B, hBP⟩, e⟩
  let F := K.pullbackQuotient_singleCosetHom Q B
  change K.multiCosetInclude P hAdmH hGenH hRetH B hBP
        ((K.singleCosetEGraph B).source (F.onEdge e)) =
      K.multiCosetInclude P hAdmH hGenH hRetH B hBP
        (F.onVertex ((K.pullbackQuotient Q).singleCosetEGraph B |>.source e))
  exact congrArg
    (K.multiCosetInclude P hAdmH hGenH hRetH B hBP)
    (F.map_source e)

/-- The FULL signed label of an old or newly completed raw
B-constituent edge is preserved literally by Q. -/
theorem pullbackQuotient_multiCosetRawEdge_label_natural
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (P : CosetFamilySpec A)
    (e : (K.pullbackQuotient Q).MultiCosetRawEdge P) :
    K.multiCosetRawEdgeLabel P
        ⟨e.1,
          (K.pullbackQuotient_singleCosetHom Q e.1.1).onEdge e.2⟩ =
      (K.pullbackQuotient Q).multiCosetRawEdgeLabel P e := by
  rcases e with ⟨⟨B, hBP⟩, e⟩
  exact (K.pullbackQuotient_singleCosetHom Q B).map_label e

/-- TRUE raw oriented signed edge mapping, OLD→OLD for
genuinely present old edges and FRESH→FRESH for full B edges.
It is NOT a map on mere ambient Cayley group edge tokens. -/
noncomputable def pullbackQuotient_multiCosetRawEdgeToBase
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (P : CosetFamilySpec A)
    (e : (K.pullbackQuotient Q).MultiCosetRawEdge P) :
    K.MultiCosetRawEdge P :=
  ⟨e.1, (K.pullbackQuotient_singleCosetHom Q e.1.1).onEdge e.2⟩

/-- The exact raw signed edge image respects the SOURCE+FULL
SIGNED LABEL quotient relation, since the H target EGraph
already identifies exactly equal glued source and signed label.
No group-coordinate gluing is used. -/
theorem pullbackQuotient_multiCosetRawEdgeToBase_related
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (P : CosetFamilySpec A)
    (hAdmG : (K.pullbackQuotient Q).AdmissibleForCosetExtension)
    (hGenG : IsGenerated genΓ) (hRetG : Retractable genΓ)
    (hAdmH : K.AdmissibleForCosetExtension)
    (hGenH : IsGenerated genΔ) (hRetH : Retractable genΔ)
    (e f : (K.pullbackQuotient Q).MultiCosetRawEdge P)
    (hef : (K.pullbackQuotient Q).MultiCosetRawEdgeRelated
      P hAdmG hGenG hRetG e f) :
    K.MultiCosetRawEdgeRelated P hAdmH hGenH hRetH
      (K.pullbackQuotient_multiCosetRawEdgeToBase Q P e)
      (K.pullbackQuotient_multiCosetRawEdgeToBase Q P f) := by
  constructor
  · calc
      K.multiCosetRawEdgeSource P hAdmH hGenH hRetH
          (K.pullbackQuotient_multiCosetRawEdgeToBase Q P e) =
        K.pullbackQuotient_multiCosetVertexToBase
          Q P hAdmG hGenG hRetG hAdmH hGenH hRetH
          ((K.pullbackQuotient Q).multiCosetRawEdgeSource
            P hAdmG hGenG hRetG e) :=
        K.pullbackQuotient_multiCosetRawEdge_source_natural
          Q P hAdmG hGenG hRetG hAdmH hGenH hRetH e
      _ = K.pullbackQuotient_multiCosetVertexToBase
          Q P hAdmG hGenG hRetG hAdmH hGenH hRetH
          ((K.pullbackQuotient Q).multiCosetRawEdgeSource
            P hAdmG hGenG hRetG f) :=
        congrArg (K.pullbackQuotient_multiCosetVertexToBase
          Q P hAdmG hGenG hRetG hAdmH hGenH hRetH) hef.1
      _ = K.multiCosetRawEdgeSource P hAdmH hGenH hRetH
          (K.pullbackQuotient_multiCosetRawEdgeToBase Q P f) :=
        (K.pullbackQuotient_multiCosetRawEdge_source_natural
          Q P hAdmG hGenG hRetG hAdmH hGenH hRetH f).symm
  · calc
      K.multiCosetRawEdgeLabel P
          (K.pullbackQuotient_multiCosetRawEdgeToBase Q P e) =
        (K.pullbackQuotient Q).multiCosetRawEdgeLabel P e :=
          K.pullbackQuotient_multiCosetRawEdge_label_natural Q P e
      _ = (K.pullbackQuotient Q).multiCosetRawEdgeLabel P f := hef.2
      _ = K.multiCosetRawEdgeLabel P
          (K.pullbackQuotient_multiCosetRawEdgeToBase Q P f) :=
        (K.pullbackQuotient_multiCosetRawEdge_label_natural Q P f).symm

/-- Genuine full multiCE signed EDGE QUOTIENT map, induced by the
true old/fresh constituent signed maps. It cannot collapse
distinct H component-index tags by definition. -/
noncomputable def pullbackQuotient_multiCosetEdgeToBase
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (P : CosetFamilySpec A)
    (hAdmG : (K.pullbackQuotient Q).AdmissibleForCosetExtension)
    (hGenG : IsGenerated genΓ) (hRetG : Retractable genΓ)
    (hAdmH : K.AdmissibleForCosetExtension)
    (hGenH : IsGenerated genΔ) (hRetH : Retractable genΔ)
    (e : (K.pullbackQuotient Q).MultiCosetEdgeVertexIncidenceQuotient
      P hAdmG hGenG hRetG) :
    K.MultiCosetEdgeVertexIncidenceQuotient P hAdmH hGenH hRetH :=
  Quotient.liftOn e
    (fun raw =>
      Quotient.mk (K.multiCosetRawEdgeSetoid P hAdmH hGenH hRetH)
        (K.pullbackQuotient_multiCosetRawEdgeToBase Q P raw))
    (by
      intro e f hef
      apply Quotient.sound
      exact K.pullbackQuotient_multiCosetRawEdgeToBase_related
        Q P hAdmG hGenG hRetG hAdmH hGenH hRetH e f hef)

/-- The true EXACT signed multiCE EGraph morphism G→H,
with vertex map independently certified by intrinsic
common-intersection component-tag support and edge
map induced by SOURCE+FULL SIGNED LABEL quotient.

This maps every actual original-old signed edge to its real
H-original old image, and each newly completed full B-coset
signed edge to the genuine corresponding tagged H coset edge.
It preserves BOTH formal inverse edge tokens, sources and
signed labels, with no global ambient-coordinate assumption. -/
noncomputable def pullbackQuotient_multiCosetSignedHom
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (P : CosetFamilySpec A)
    (hAdmG : (K.pullbackQuotient Q).AdmissibleForCosetExtension)
    (hGenG : IsGenerated genΓ) (hRetG : Retractable genΓ)
    (hAdmH : K.AdmissibleForCosetExtension)
    (hGenH : IsGenerated genΔ) (hRetH : Retractable genΔ) :
    LabelledGraphHom
      ((K.pullbackQuotient Q).multiCosetEGraph P
        hAdmG hGenG hRetG).toLabelledGraph
      (K.multiCosetEGraph P hAdmH hGenH hRetH).toLabelledGraph where
  onVertex :=
    K.pullbackQuotient_multiCosetVertexToBase Q P
      hAdmG hGenG hRetG hAdmH hGenH hRetH
  onEdge :=
    K.pullbackQuotient_multiCosetEdgeToBase Q P
      hAdmG hGenG hRetG hAdmH hGenH hRetH
  map_source := by
    intro e
    induction e using Quotient.inductionOn with
    | h raw =>
      exact K.pullbackQuotient_multiCosetRawEdge_source_natural
        Q P hAdmG hGenG hRetG hAdmH hGenH hRetH raw
  map_inv := by
    intro e
    induction e using Quotient.inductionOn with
    | h raw =>
      rcases raw with ⟨⟨B, hBP⟩, e⟩
      let F := K.pullbackQuotient_singleCosetHom Q B
      change K.multiCosetEdgeInclude P hAdmH hGenH hRetH
          B hBP (F.onEdge ((K.pullbackQuotient Q).singleCosetEGraph B |>.inv e)) =
        K.multiCosetEdgeInclude P hAdmH hGenH hRetH
          B hBP ((K.singleCosetEGraph B).inv (F.onEdge e))
      exact congrArg
        (K.multiCosetEdgeInclude P hAdmH hGenH hRetH B hBP)
        (F.map_inv e)
  map_label := by
    intro e
    induction e using Quotient.inductionOn with
    | h raw =>
      exact K.pullbackQuotient_multiCosetRawEdge_label_natural
        Q P raw

/-- The resulting signed graph hom maps every selected old
actual original G-skeleton vertex into the canonically
included TRUE old H-skeleton vertex. This is an equality
of component-tagged quotient vertices, not of H values. -/
theorem pullbackQuotient_multiCosetSignedHom_oldVertex
    (K : CayleySubgraphSpec genΔ A)
    (Q : LabelledGroupQuotient genΓ genΔ)
    (P : CosetFamilySpec A)
    (hAdmG : (K.pullbackQuotient Q).AdmissibleForCosetExtension)
    (hGenG : IsGenerated genΓ) (hRetG : Retractable genΓ)
    (hAdmH : K.AdmissibleForCosetExtension)
    (hGenH : IsGenerated genΔ) (hRetH : Retractable genΔ)
    (B : Finset ι) (hBP : B ∈ P.alphabets)
    (x : (K.pullbackQuotient Q).Vertex) :
    (K.pullbackQuotient_multiCosetSignedHom
      Q P hAdmG hGenG hRetG hAdmH hGenH hRetH).onVertex
      (((K.pullbackQuotient Q).skeletonToMultiCosetHom
        P hAdmG hGenG hRetG B hBP).onVertex x) =
      (K.skeletonToMultiCosetHom
        P hAdmH hGenH hRetH B hBP).onVertex
        ((K.pullbackQuotientHom Q).onVertex x) :=
  K.pullbackQuotient_multiCosetVertexToBase_old_skeleton
    Q P hAdmG hGenG hRetG hAdmH hGenH hRetH B hBP x

end CayleySubgraphSpec
end ABO
end PSTSEPPA
