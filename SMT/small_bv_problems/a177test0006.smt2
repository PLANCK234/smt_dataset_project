(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
Bit-vector benchmarks from Dawson Engler's tool contributed by Vijay Ganesh
(vganesh@stanford.edu).  Translated into SMT-LIB format by Clark Barrett using
CVC3.

|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun n () (_ BitVec 32))
(declare-fun c () (_ BitVec 8))
(assert (bvult n (_ bv16 32)))
(assert (not (= (concat (_ bv0 24) c) (_ bv254 32))))
(assert (not (bvult n (_ bv12 32))))
(assert (not (not (= (concat (_ bv0 24) ((_ extract 7 0) (concat (_ bv0 24) c))) (_ bv0 32)))))
(assert (not (not (= (bvand n (_ bv3 32)) (_ bv0 32)))))
(check-sat)
(exit)
