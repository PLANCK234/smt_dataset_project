(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
Ivan Jager <aij+nospam@andrew.cmu.edu>

|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun R_ESP_1_58 () (_ BitVec 32))
(assert (let ((?v_0 (bvsub R_ESP_1_58 (_ bv4 32)))) (= (_ bv1 1) (bvand (_ bv1 1) (bvand (bvnot (ite (= (_ bv1 32) (bvand (_ bv1 32) (bvlshr (bvand (bvxor ?v_0 (_ bv8 32)) (bvxor ?v_0 (bvsub ?v_0 (_ bv8 32)))) (_ bv31 32)))) (_ bv1 1) (_ bv0 1))) (_ bv1 1))))))
(check-sat)
(exit)
