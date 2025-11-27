(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
Bit-vector benchmarks from Dawson Engler's tool contributed by Vijay Ganesh
(vganesh@stanford.edu).  Translated into SMT-LIB format by Clark Barrett using
CVC3.

|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun x () (_ BitVec 31))
(assert (bvslt (_ bv0 32) ((_ extract 31 0) (concat x (_ bv0 1)))))
(check-sat)
(exit)
