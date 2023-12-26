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
(declare-fun f1 (U U) U)
(declare-fun f2 (U) U)
(declare-fun c10 () U)
(declare-fun c11 () U)
(declare-fun c3 () U)
(declare-fun c4 () U)
(declare-fun c5 () U)
(declare-fun c6 () U)
(declare-fun c7 () U)
(declare-fun c8 () U)
(declare-fun c9 () U)
(declare-fun c_0 () U)
(declare-fun c_1 () U)
(declare-fun c_2 () U)
(declare-fun c_3 () U)
(assert (let ((?v_0 (f1 c_0 c_0))) (let ((?v_4 (f2 ?v_0)) (?v_1 (f1 c_0 c_1))) (let ((?v_5 (f2 ?v_1)) (?v_2 (f1 c_0 c_2))) (let ((?v_6 (f2 ?v_2)) (?v_3 (f1 c_0 c_3))) (let ((?v_7 (f2 ?v_3)) (?v_8 (f1 c_1 c_0)) (?v_9 (f1 c_1 c_1)) (?v_10 (f1 c_1 c_2)) (?v_11 (f1 c_1 c_3)) (?v_16 (f1 c_2 c_0)) (?v_17 (f1 c_2 c_1)) (?v_18 (f1 c_2 c_2)) (?v_19 (f1 c_2 c_3)) (?v_20 (f1 c_3 c_0)) (?v_21 (f1 c_3 c_1)) (?v_22 (f1 c_3 c_2)) (?v_23 (f1 c_3 c_3))) (let ((?v_12 (f2 ?v_8)) (?v_13 (f2 ?v_9)) (?v_14 (f2 ?v_10)) (?v_15 (f2 ?v_11)) (?v_24 (f2 ?v_16)) (?v_25 (f2 ?v_17)) (?v_26 (f2 ?v_18)) (?v_27 (f2 ?v_19)) (?v_28 (f2 ?v_20)) (?v_29 (f2 ?v_21)) (?v_30 (f2 ?v_22)) (?v_31 (f2 ?v_23)) (?v_32 (f2 c_0)) (?v_33 (f2 c_1)) (?v_34 (f2 c_2)) (?v_35 (f2 c_3))) (and (distinct c_0 c_1 c_2 c_3) (= (f1 c_0 (f1 ?v_0 ?v_4)) c_0) (= (f1 c_0 (f1 ?v_1 ?v_5)) c_0) (= (f1 c_0 (f1 ?v_2 ?v_6)) c_0) (= (f1 c_0 (f1 ?v_3 ?v_7)) c_0) (= (f1 c_0 (f1 ?v_8 ?v_4)) c_1) (= (f1 c_0 (f1 ?v_9 ?v_5)) c_1) (= (f1 c_0 (f1 ?v_10 ?v_6)) c_1) (= (f1 c_0 (f1 ?v_11 ?v_7)) c_1) (= (f1 c_0 (f1 ?v_16 ?v_4)) c_2) (= (f1 c_0 (f1 ?v_17 ?v_5)) c_2) (= (f1 c_0 (f1 ?v_18 ?v_6)) c_2) (= (f1 c_0 (f1 ?v_19 ?v_7)) c_2) (= (f1 c_0 (f1 ?v_20 ?v_4)) c_3) (= (f1 c_0 (f1 ?v_21 ?v_5)) c_3) (= (f1 c_0 (f1 ?v_22 ?v_6)) c_3) (= (f1 c_0 (f1 ?v_23 ?v_7)) c_3) (= (f1 c_1 (f1 ?v_0 ?v_12)) c_0) (= (f1 c_1 (f1 ?v_1 ?v_13)) c_0) (= (f1 c_1 (f1 ?v_2 ?v_14)) c_0) (= (f1 c_1 (f1 ?v_3 ?v_15)) c_0) (= (f1 c_1 (f1 ?v_8 ?v_12)) c_1) (= (f1 c_1 (f1 ?v_9 ?v_13)) c_1) (= (f1 c_1 (f1 ?v_10 ?v_14)) c_1) (= (f1 c_1 (f1 ?v_11 ?v_15)) c_1) (= (f1 c_1 (f1 ?v_16 ?v_12)) c_2) (= (f1 c_1 (f1 ?v_17 ?v_13)) c_2) (= (f1 c_1 (f1 ?v_18 ?v_14)) c_2) (= (f1 c_1 (f1 ?v_19 ?v_15)) c_2) (= (f1 c_1 (f1 ?v_20 ?v_12)) c_3) (= (f1 c_1 (f1 ?v_21 ?v_13)) c_3) (= (f1 c_1 (f1 ?v_22 ?v_14)) c_3) (= (f1 c_1 (f1 ?v_23 ?v_15)) c_3) (= (f1 c_2 (f1 ?v_0 ?v_24)) c_0) (= (f1 c_2 (f1 ?v_1 ?v_25)) c_0) (= (f1 c_2 (f1 ?v_2 ?v_26)) c_0) (= (f1 c_2 (f1 ?v_3 ?v_27)) c_0) (= (f1 c_2 (f1 ?v_8 ?v_24)) c_1) (= (f1 c_2 (f1 ?v_9 ?v_25)) c_1) (= (f1 c_2 (f1 ?v_10 ?v_26)) c_1) (= (f1 c_2 (f1 ?v_11 ?v_27)) c_1) (= (f1 c_2 (f1 ?v_16 ?v_24)) c_2) (= (f1 c_2 (f1 ?v_17 ?v_25)) c_2) (= (f1 c_2 (f1 ?v_18 ?v_26)) c_2) (= (f1 c_2 (f1 ?v_19 ?v_27)) c_2) (= (f1 c_2 (f1 ?v_20 ?v_24)) c_3) (= (f1 c_2 (f1 ?v_21 ?v_25)) c_3) (= (f1 c_2 (f1 ?v_22 ?v_26)) c_3) (= (f1 c_2 (f1 ?v_23 ?v_27)) c_3) (= (f1 c_3 (f1 ?v_0 ?v_28)) c_0) (= (f1 c_3 (f1 ?v_1 ?v_29)) c_0) (= (f1 c_3 (f1 ?v_2 ?v_30)) c_0) (= (f1 c_3 (f1 ?v_3 ?v_31)) c_0) (= (f1 c_3 (f1 ?v_8 ?v_28)) c_1) (= (f1 c_3 (f1 ?v_9 ?v_29)) c_1) (= (f1 c_3 (f1 ?v_10 ?v_30)) c_1) (= (f1 c_3 (f1 ?v_11 ?v_31)) c_1) (= (f1 c_3 (f1 ?v_16 ?v_28)) c_2) (= (f1 c_3 (f1 ?v_17 ?v_29)) c_2) (= (f1 c_3 (f1 ?v_18 ?v_30)) c_2) (= (f1 c_3 (f1 ?v_19 ?v_31)) c_2) (= (f1 c_3 (f1 ?v_20 ?v_28)) c_3) (= (f1 c_3 (f1 ?v_21 ?v_29)) c_3) (= (f1 c_3 (f1 ?v_22 ?v_30)) c_3) (= (f1 c_3 (f1 ?v_23 ?v_31)) c_3) (or (not (= (f1 c10 c11) (f1 c11 c10))) (not (= (f1 (f2 c3) c3) (f1 (f2 c4) c4))) (not (= (f1 (f1 (f2 c5) c5) c6) c6)) (not (= (f1 (f1 c7 c8) c9) (f1 c7 (f1 c8 c9))))) (or (= ?v_0 c_0) (= ?v_0 c_1) (= ?v_0 c_2) (= ?v_0 c_3)) (or (= ?v_1 c_0) (= ?v_1 c_1) (= ?v_1 c_2) (= ?v_1 c_3)) (or (= ?v_2 c_0) (= ?v_2 c_1) (= ?v_2 c_2) (= ?v_2 c_3)) (or (= ?v_3 c_0) (= ?v_3 c_1) (= ?v_3 c_2) (= ?v_3 c_3)) (or (= ?v_8 c_0) (= ?v_8 c_1) (= ?v_8 c_2) (= ?v_8 c_3)) (or (= ?v_9 c_0) (= ?v_9 c_1) (= ?v_9 c_2) (= ?v_9 c_3)) (or (= ?v_10 c_0) (= ?v_10 c_1) (= ?v_10 c_2) (= ?v_10 c_3)) (or (= ?v_11 c_0) (= ?v_11 c_1) (= ?v_11 c_2) (= ?v_11 c_3)) (or (= ?v_16 c_0) (= ?v_16 c_1) (= ?v_16 c_2) (= ?v_16 c_3)) (or (= ?v_17 c_0) (= ?v_17 c_1) (= ?v_17 c_2) (= ?v_17 c_3)) (or (= ?v_18 c_0) (= ?v_18 c_1) (= ?v_18 c_2) (= ?v_18 c_3)) (or (= ?v_19 c_0) (= ?v_19 c_1) (= ?v_19 c_2) (= ?v_19 c_3)) (or (= ?v_20 c_0) (= ?v_20 c_1) (= ?v_20 c_2) (= ?v_20 c_3)) (or (= ?v_21 c_0) (= ?v_21 c_1) (= ?v_21 c_2) (= ?v_21 c_3)) (or (= ?v_22 c_0) (= ?v_22 c_1) (= ?v_22 c_2) (= ?v_22 c_3)) (or (= ?v_23 c_0) (= ?v_23 c_1) (= ?v_23 c_2) (= ?v_23 c_3)) (or (= ?v_32 c_0) (= ?v_32 c_1) (= ?v_32 c_2) (= ?v_32 c_3)) (or (= ?v_33 c_0) (= ?v_33 c_1) (= ?v_33 c_2) (= ?v_33 c_3)) (or (= ?v_34 c_0) (= ?v_34 c_1) (= ?v_34 c_2) (= ?v_34 c_3)) (or (= ?v_35 c_0) (= ?v_35 c_1) (= ?v_35 c_2) (= ?v_35 c_3)) (or (= c10 c_0) (= c10 c_1) (= c10 c_2) (= c10 c_3)) (or (= c11 c_0) (= c11 c_1) (= c11 c_2) (= c11 c_3)) (or (= c3 c_0) (= c3 c_1) (= c3 c_2) (= c3 c_3)) (or (= c4 c_0) (= c4 c_1) (= c4 c_2) (= c4 c_3)) (or (= c5 c_0) (= c5 c_1) (= c5 c_2) (= c5 c_3)) (or (= c6 c_0) (= c6 c_1) (= c6 c_2) (= c6 c_3)) (or (= c7 c_0) (= c7 c_1) (= c7 c_2) (= c7 c_3)) (or (= c8 c_0) (= c8 c_1) (= c8 c_2) (= c8 c_3)) (or (= c9 c_0) (= c9 c_1) (= c9 c_2) (= c9 c_3))))))))))
(check-sat)
(exit)
