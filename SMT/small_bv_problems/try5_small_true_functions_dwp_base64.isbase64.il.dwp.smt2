(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
Ivan Jager <aij+nospam@andrew.cmu.edu>

|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun t_164 () (_ BitVec 1))
(declare-fun t_163 () (_ BitVec 1))
(declare-fun t_162 () (_ BitVec 1))
(assert (let ((?v_0 (bvnot (_ bv0 1)))) (= (_ bv1 1) (bvand (bvand (bvand (ite (= t_164 (bvor t_162 t_163)) (_ bv1 1) (_ bv0 1)) (ite (= t_163 ?v_0) (_ bv1 1) (_ bv0 1))) (ite (= t_162 (_ bv0 1)) (_ bv1 1) (_ bv0 1))) (bvand ?v_0 (bvand t_164 (_ bv1 1)))))))
(check-sat)
(exit)
