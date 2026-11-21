import Phi2NB.PhiR.Statement
import Phi2NB.Phi2HInf.PremiseCorrespondence
import Phi2NB.Phi2HInf.Classical
import Phi2NB.Phi2HInf.PoleTwoBsup

/-!
# Phi2NB v1.2: natural boundaries under H∞, with the RH results retained

This entry point imports the complete release: the v1.1 RH theorems for Φ₂ and Φ_r,
the H∞ theorems for both series, their classical-form corollaries, and the real pole at 2B
and the RH criterion for Φ₂ under H∞.
Plain `lake build` builds the single default library target `Phi2NB`.

The H∞ development shares the v1.1 definitions and proofs. Extracted source helpers
whose types take the stronger counting premise `Paper2.Z2` have the suffix
`_fullZ2`; the original v1.1 declarations keep their names and statements.
The four public H∞ theorem statements keep their original premise names and types.

Do not import the unextracted `GoldbachBoundaries` source tree alongside this
release: it independently defines names that this library already supplies.
-/
