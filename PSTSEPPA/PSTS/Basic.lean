/-!
# Partial Steiner triple systems

This file is the entry point for Gate T0.  The mathematical API will encode a
partial Steiner triple system as a partial binary operation, with repeated
arguments and the Steiner companion identities made explicit.

No mathematical PSTS declaration is added in the bootstrap commit: the first
API choice should be checked immediately by CI rather than mixed into repository
initialization.
-/

namespace PSTSEPPA

/-- Technical declaration ensuring that the CI axiom audit exercises this
project even before Gate T0 introduces mathematical declarations. -/
theorem bootstrapAuditMarker : True := by
  trivial

end PSTSEPPA
