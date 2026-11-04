import SMT.Core
import SMT.BitVec.Shift
import Lean.Meta.Tactic.BVDecide.Attr

/-! Optional tactic registration. Mathematical modules do not import the SAT engine. -/
attribute [bv_normalize] SMT.Core.differentFrom_nil SMT.Core.differentFrom_cons
  SMT.Core.distinct_nil SMT.Core.distinct_cons SMT.BitVec.bvshl_normalize
