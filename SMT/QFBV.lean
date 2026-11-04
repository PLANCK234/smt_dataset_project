import SMT.Core
import SMT.BitVec
import SMT.Normalize
import Std.Tactic.BVDecide

/-!
Public SMT-LIB 2.7 QF_BV compatibility boundary. Generated files import this module.
The frontend validates positive widths, indexed-operation domains, and source profiles.
All SMT terms are values; `SMT.Core.holds` explicitly bridges Bool into Prop.
-/
