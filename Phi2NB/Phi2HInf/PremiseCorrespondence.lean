import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.PhiR.PremiseCorrespondence

/-! Definitional bridges between the unchanged H∞ premises and the v1.1 premises.
`Z2` retains its asymptotic conjunct; only the local-count conjunct is projected below. -/

namespace GoldbachBoundaries.Phi2HInf

open Paper2

theorem Z1_iff_zeroSymmetry : Z1 ↔ ZeroSymmetry := Iff.rfl

theorem Z3_iff_logDerivZetaLocal : Z3 ↔ LogDerivZetaLocal := Iff.rfl

theorem ZLittlewood_iff_littlewoodGap : ZLittlewood ↔ LittlewoodGap := Iff.rfl

theorem Z2_iff_sourceZ2 : Z2 ↔ PhiRSource.Z2 := Iff.rfl

theorem riemannVonMangoldt_of_Z2 (h : Z2) : RiemannVonMangoldt := h.2

end GoldbachBoundaries.Phi2HInf
