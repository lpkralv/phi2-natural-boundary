import Phi2NB.BoundaryLemma
import Phi2NB.TIdentity.Assembly

/-!
# Half-planes are preconnected
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries

/-- The half-plane `{Re s > a}` is preconnected (it is convex). -/
lemma isPreconnected_halfPlane (a : ℝ) : IsPreconnected (halfPlane a) :=
  (convex_halfSpace_re_gt a).isPreconnected

end GoldbachBoundaries
