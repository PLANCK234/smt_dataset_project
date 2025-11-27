(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
Ivan Jager <aij+nospam@andrew.cmu.edu>

|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun R_EAX_5_60 () (_ BitVec 32))
(assert (= (_ bv1 1) (bvand (_ bv1 1) (bvand (bvnot (ite (= (_ bv1 32) (bvand (_ bv1 32) (bvlshr (bvand (bvxor R_EAX_5_60 (_ bv4294967294 32)) (bvxor R_EAX_5_60 (bvadd R_EAX_5_60 (_ bv1 32)))) (_ bv31 32)))) (_ bv1 1) (_ bv0 1))) (_ bv1 1)))))
(check-sat)
(exit)
