(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
 Patrice Godefroid, SAGE (systematic dynamic test generation)
 For more information: http://research.microsoft.com/en-us/um/people/pg/public_psfiles/ndss2008.pdf
|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun T1_118 () (_ BitVec 8))
(assert (and true (= (bvsub ((_ zero_extend 24) (_ bv0 8)) (bvsub (_ bv0 32) ((_ zero_extend 24) (ite (bvult (_ bv0 8) (bvand T1_118 (_ bv128 8))) (_ bv1 8) (_ bv0 8))))) (_ bv1 32)) (not (= (bvand T1_118 (_ bv64 8)) (_ bv0 8)))))
(check-sat)
(exit)
