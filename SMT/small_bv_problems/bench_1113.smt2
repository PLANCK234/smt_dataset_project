(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
 Patrice Godefroid, SAGE (systematic dynamic test generation)
 For more information: http://research.microsoft.com/en-us/um/people/pg/public_psfiles/ndss2008.pdf
|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun T2_31327 () (_ BitVec 16))
(declare-fun T1_31327 () (_ BitVec 8))
(declare-fun T1_31328 () (_ BitVec 8))
(assert (let ((?v_0 ((_ zero_extend 16) T2_31327))) (and true (= T2_31327 (bvor (bvshl ((_ zero_extend 8) T1_31328) (_ bv8 16)) ((_ zero_extend 8) T1_31327))) (bvslt (_ bv14 32) ?v_0) (bvslt (_ bv13 32) ?v_0) (bvult (_ bv0 16) T2_31327) (bvule ?v_0 (_ bv16 32)) (bvule (_ bv0 32) ?v_0))))
(check-sat)
(exit)
