(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
 Patrice Godefroid, SAGE (systematic dynamic test generation)
 For more information: http://research.microsoft.com/en-us/um/people/pg/public_psfiles/ndss2008.pdf
|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun T1_31268 () (_ BitVec 8))
(declare-fun T2_31268 () (_ BitVec 16))
(declare-fun T1_31269 () (_ BitVec 8))
(assert (and true (= T2_31268 (bvor (bvshl ((_ zero_extend 8) T1_31269) (_ bv8 16)) ((_ zero_extend 8) T1_31268))) (not (= (bvand ((_ extract 7 0) (bvashr (bvashr ((_ extract 15 0) (bvashr ((_ zero_extend 16) T2_31268) (_ bv1 32))) ((_ zero_extend 8) (_ bv2 8))) ((_ zero_extend 8) (_ bv3 8)))) (_ bv1 8)) (_ bv0 8))) (= (bvand T1_31268 (_ bv1 8)) (_ bv0 8))))
(check-sat)
(exit)
