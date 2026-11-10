/-!
# Principia Machina (PMA)

The Lean sources of the library `Principia` are the specification of the framework
machinery; the `pcalc` executable and the vector tests are its implementation.
-/

namespace Principia

/-- The version of the Calculator. Changed only with a release, never in place. -/
def version : String := "0.1.0"

theorem version_nonempty : version ≠ "" := by decide

end Principia
