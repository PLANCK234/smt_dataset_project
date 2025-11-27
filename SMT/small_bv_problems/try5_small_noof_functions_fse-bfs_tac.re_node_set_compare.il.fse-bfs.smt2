(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
Ivan Jager <aij+nospam@andrew.cmu.edu>

|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun R_EDX_8_82 () (_ BitVec 32))
(declare-fun R_ESP_1_59 () (_ BitVec 32))
(declare-fun R_EAX_5_56 () (_ BitVec 32))
(assert (let ((?v_1 ((_ extract 0 0) (concat (_ bv0 31) (ite (= R_EAX_5_56 (_ bv0 32)) (_ bv1 1) (_ bv0 1))))) (?v_0 (bvsub R_ESP_1_59 (_ bv4 32)))) (let ((?v_2 (bvand (bvnot (ite (= (_ bv1 32) (bvand (_ bv1 32) (bvlshr (bvand (bvxor ?v_0 (_ bv16 32)) (bvxor ?v_0 (bvsub ?v_0 (_ bv16 32)))) (_ bv31 32)))) (_ bv1 1) (_ bv0 1))) (_ bv1 1)))) (= (_ bv1 1) (bvor (bvand (_ bv1 1) (bvand ((_ extract 0 0) (concat (_ bv0 31) (ite (= R_EDX_8_82 (_ bv0 32)) (_ bv1 1) (_ bv0 1)))) (bvand (bvnot ?v_1) ?v_2))) (bvand (_ bv1 1) (bvand ?v_1 ?v_2)))))))
(check-sat)
(exit)
