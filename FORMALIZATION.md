# Formalization status

This file is the live map from the mathematical proof plan to Lean.
A statement is called **Formalized** only after the corresponding declaration
is on `main` and GitHub Actions is green.

**Status meanings**

- **API formalized** — definitions compile and are used by later files.
- **Formalized** — theorem and proof are checked by Lean on green `main`.
- **Current target** — active work frontier.
- **Planned** — intentionally not opened yet.

| Mathematical item / gate | Lean declaration / file | Status | Notes |
| --- | --- | --- | --- |
| Repository / CI bootstrap | `PSTSEPPA.lean`, `.github/workflows/lean.yml` | Current target | Mirror the pinned toolchain, build and axiom-audit policy of `lean_all_those_eppa_classes`. |
| T0: PSTS basic API | `PSTSEPPA/PSTS/Basic.lean` | Planned | Partial binary operation; repeated arguments and Steiner identities must be explicit. |
| T0: closed subsets / induced systems | `PSTSEPPA/PSTS/Closed.lean` | Planned | Closedness is essential for the EPPA category. |
| T0/T1: partial automorphisms | `PSTSEPPA/PSTS/PartialAut.lean` | Planned | Prefer concrete partial equivalences if mathlib's API is robust enough. |
| T1: signed words and partial evaluation | `PSTSEPPA/PSTS/WordEval.lean` | Planned | Audit composition/action orientation carefully. |
| T2: abstract MAX interface | `PSTSEPPA/PSTS/MaxTransporter.lean` | Planned | State only what the quotient development needs. |
| T2: quotient development | `PSTSEPPA/PSTS/Development.lean` | Planned | Equality criterion, injective base copy, functionality, closedness, group action. |
| T2: conditional EPPA transfer | `PSTSEPPA/PSTS/EPPAFromMax.lean` | Planned | **Hard gate before ABO Sections 3–5.** |
| A1: oriented labelled graphs / transition groups | `PSTSEPPA/ABO/...` | Planned | Custom graph API likely preferable to `SimpleGraph`. |
| A2: clusters / coset extensions | `PSTSEPPA/ABO/...` | Planned | Include degenerate/equal-parameter cases explicitly. |
| A3: corrected ABO Theorem 4.7 | `PSTSEPPA/ABO/UpwardInduction.lean` | Planned | Incorporate repairs R1, R7, R8. Highest-risk gate. |
| A4: corrected Section 5 induction | `PSTSEPPA/ABO/FiniteConstruction.lean` | Planned | Separate repaired `k = 1` base case R2. |
| A5: corrected ABO Lemma 2.5 | `PSTSEPPA/ABO/MainLemma.lean` | Planned | Include final-group equality and equivariance. |
| C1: Cayley / semidirect-product bridge | `PSTSEPPA/ABO/CayleyApplication.lean`, `PSTSEPPA/ABO/MaxTransporter.lean` | Planned | Derive the concrete fibre-MAX property. |
| FINAL: unconditional PSTS-EPPA | `PSTSEPPA/PSTS/EPPA.lean` | Planned | Instantiate T2 with C1. |

## Gate discipline

Do not begin the long ABO construction merely because its definitions are
available. The first major milestone is a compiled conditional theorem of the
form

```text
finite PSTS A + finite selected partial automorphisms + MAX extension
    => finite PSTS witness extending the selected maps.
```

If that transfer layer does not compile cleanly, repair it or use the documented
fallback ladder before investing in ABO Sections 3–5.
