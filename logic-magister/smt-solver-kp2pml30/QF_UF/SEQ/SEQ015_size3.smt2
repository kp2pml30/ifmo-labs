(set-info :smt-lib-version 2.6)
(set-logic QF_UF)
(set-info :source |
CADE ATP System competition. See http://www.cs.miami.edu/~tptp/CASC
 for more information. 

This benchmark was obtained by trying to find a finite model of a first-order 
formula (Albert Oliveras).
|)
(set-info :category "crafted")
(set-info :status unsat)
(declare-sort U 0)
(declare-fun c3 () U)
(declare-fun f1 (U U) U)
(declare-fun f4 (U) U)
(declare-fun c2 () U)
(declare-fun c_0 () U)
(declare-fun c_1 () U)
(declare-fun c_2 () U)
(assert (let ((?v_1 (f1 c3 c_0))) (let ((?v_0 (f1 ?v_1 c_0)) (?v_2 (f1 c_0 c_0)) (?v_4 (f1 c_0 c_1)) (?v_5 (f1 c_0 c_2)) (?v_3 (f1 ?v_1 c_1)) (?v_6 (f1 ?v_1 c_2)) (?v_8 (f1 c3 c_1))) (let ((?v_7 (f1 ?v_8 c_0)) (?v_9 (f1 c_1 c_0)) (?v_11 (f1 c_1 c_1)) (?v_12 (f1 c_1 c_2)) (?v_10 (f1 ?v_8 c_1)) (?v_13 (f1 ?v_8 c_2)) (?v_15 (f1 c3 c_2))) (let ((?v_14 (f1 ?v_15 c_0)) (?v_16 (f1 c_2 c_0)) (?v_18 (f1 c_2 c_1)) (?v_19 (f1 c_2 c_2)) (?v_17 (f1 ?v_15 c_1)) (?v_20 (f1 ?v_15 c_2)) (?v_21 (f4 c_0))) (let ((?v_22 (f1 c_0 ?v_21)) (?v_23 (f4 c_1))) (let ((?v_24 (f1 c_1 ?v_23)) (?v_25 (f4 c_2))) (let ((?v_26 (f1 c_2 ?v_25)) (?v_28 (f1 c2 c_0))) (let ((?v_27 (f1 ?v_28 c_0)) (?v_29 (f1 ?v_28 c_1)) (?v_30 (f1 ?v_28 c_2)) (?v_32 (f1 c2 c_1))) (let ((?v_31 (f1 ?v_32 c_0)) (?v_33 (f1 ?v_32 c_1)) (?v_34 (f1 ?v_32 c_2)) (?v_36 (f1 c2 c_2))) (let ((?v_35 (f1 ?v_36 c_0)) (?v_37 (f1 ?v_36 c_1)) (?v_38 (f1 ?v_36 c_2))) (and (distinct c_0 c_1 c_2) (= (f1 ?v_0 c_0) (f1 c_0 ?v_2)) (= (f1 ?v_0 c_1) (f1 c_0 ?v_4)) (= (f1 ?v_0 c_2) (f1 c_0 ?v_5)) (= (f1 ?v_3 c_0) (f1 c_1 ?v_2)) (= (f1 ?v_3 c_1) (f1 c_1 ?v_4)) (= (f1 ?v_3 c_2) (f1 c_1 ?v_5)) (= (f1 ?v_6 c_0) (f1 c_2 ?v_2)) (= (f1 ?v_6 c_1) (f1 c_2 ?v_4)) (= (f1 ?v_6 c_2) (f1 c_2 ?v_5)) (= (f1 ?v_7 c_0) (f1 c_0 ?v_9)) (= (f1 ?v_7 c_1) (f1 c_0 ?v_11)) (= (f1 ?v_7 c_2) (f1 c_0 ?v_12)) (= (f1 ?v_10 c_0) (f1 c_1 ?v_9)) (= (f1 ?v_10 c_1) (f1 c_1 ?v_11)) (= (f1 ?v_10 c_2) (f1 c_1 ?v_12)) (= (f1 ?v_13 c_0) (f1 c_2 ?v_9)) (= (f1 ?v_13 c_1) (f1 c_2 ?v_11)) (= (f1 ?v_13 c_2) (f1 c_2 ?v_12)) (= (f1 ?v_14 c_0) (f1 c_0 ?v_16)) (= (f1 ?v_14 c_1) (f1 c_0 ?v_18)) (= (f1 ?v_14 c_2) (f1 c_0 ?v_19)) (= (f1 ?v_17 c_0) (f1 c_1 ?v_16)) (= (f1 ?v_17 c_1) (f1 c_1 ?v_18)) (= (f1 ?v_17 c_2) (f1 c_1 ?v_19)) (= (f1 ?v_20 c_0) (f1 c_2 ?v_16)) (= (f1 ?v_20 c_1) (f1 c_2 ?v_18)) (= (f1 ?v_20 c_2) (f1 c_2 ?v_19)) (not (= ?v_22 (f1 ?v_21 ?v_22))) (not (= ?v_24 (f1 ?v_23 ?v_24))) (not (= ?v_26 (f1 ?v_25 ?v_26))) (= (f1 ?v_27 c_0) (f1 (f1 ?v_2 c_0) c_0)) (= (f1 ?v_27 c_1) (f1 (f1 ?v_4 c_0) c_1)) (= (f1 ?v_27 c_2) (f1 (f1 ?v_5 c_0) c_2)) (= (f1 ?v_29 c_0) (f1 (f1 ?v_2 c_1) c_0)) (= (f1 ?v_29 c_1) (f1 (f1 ?v_4 c_1) c_1)) (= (f1 ?v_29 c_2) (f1 (f1 ?v_5 c_1) c_2)) (= (f1 ?v_30 c_0) (f1 (f1 ?v_2 c_2) c_0)) (= (f1 ?v_30 c_1) (f1 (f1 ?v_4 c_2) c_1)) (= (f1 ?v_30 c_2) (f1 (f1 ?v_5 c_2) c_2)) (= (f1 ?v_31 c_0) (f1 (f1 ?v_9 c_0) c_0)) (= (f1 ?v_31 c_1) (f1 (f1 ?v_11 c_0) c_1)) (= (f1 ?v_31 c_2) (f1 (f1 ?v_12 c_0) c_2)) (= (f1 ?v_33 c_0) (f1 (f1 ?v_9 c_1) c_0)) (= (f1 ?v_33 c_1) (f1 (f1 ?v_11 c_1) c_1)) (= (f1 ?v_33 c_2) (f1 (f1 ?v_12 c_1) c_2)) (= (f1 ?v_34 c_0) (f1 (f1 ?v_9 c_2) c_0)) (= (f1 ?v_34 c_1) (f1 (f1 ?v_11 c_2) c_1)) (= (f1 ?v_34 c_2) (f1 (f1 ?v_12 c_2) c_2)) (= (f1 ?v_35 c_0) (f1 (f1 ?v_16 c_0) c_0)) (= (f1 ?v_35 c_1) (f1 (f1 ?v_18 c_0) c_1)) (= (f1 ?v_35 c_2) (f1 (f1 ?v_19 c_0) c_2)) (= (f1 ?v_37 c_0) (f1 (f1 ?v_16 c_1) c_0)) (= (f1 ?v_37 c_1) (f1 (f1 ?v_18 c_1) c_1)) (= (f1 ?v_37 c_2) (f1 (f1 ?v_19 c_1) c_2)) (= (f1 ?v_38 c_0) (f1 (f1 ?v_16 c_2) c_0)) (= (f1 ?v_38 c_1) (f1 (f1 ?v_18 c_2) c_1)) (= (f1 ?v_38 c_2) (f1 (f1 ?v_19 c_2) c_2)) (or (= ?v_2 c_0) (= ?v_2 c_1) (= ?v_2 c_2)) (or (= ?v_4 c_0) (= ?v_4 c_1) (= ?v_4 c_2)) (or (= ?v_5 c_0) (= ?v_5 c_1) (= ?v_5 c_2)) (or (= ?v_9 c_0) (= ?v_9 c_1) (= ?v_9 c_2)) (or (= ?v_11 c_0) (= ?v_11 c_1) (= ?v_11 c_2)) (or (= ?v_12 c_0) (= ?v_12 c_1) (= ?v_12 c_2)) (or (= ?v_16 c_0) (= ?v_16 c_1) (= ?v_16 c_2)) (or (= ?v_18 c_0) (= ?v_18 c_1) (= ?v_18 c_2)) (or (= ?v_19 c_0) (= ?v_19 c_1) (= ?v_19 c_2)) (or (= ?v_21 c_0) (= ?v_21 c_1) (= ?v_21 c_2)) (or (= ?v_23 c_0) (= ?v_23 c_1) (= ?v_23 c_2)) (or (= ?v_25 c_0) (= ?v_25 c_1) (= ?v_25 c_2)) (or (= c3 c_0) (= c3 c_1) (= c3 c_2)) (or (= c2 c_0) (= c2 c_1) (= c2 c_2))))))))))))))
(check-sat)
(exit)
