(set-info :smt-lib-version 2.6)
(set-logic QF_AX)
(set-info :source |
Benchmarks used in the followin paper:
Big proof engines as little proof engines: new results on rewrite-based satisfiability procedure
Alessandro Armando, Maria Paola Bonacina, Silvio Ranise, Stephan Schulz. 
PDPAR'05
http://www.ai.dist.unige.it/pdpar05/


|)
(set-info :category "crafted")
(set-info :status sat)
(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun a1 () (Array Index Element))
(declare-fun i1 () Index)
(declare-fun i2 () Index)
(declare-fun i3 () Index)
(declare-fun i4 () Index)
(assert (let ((?v_0 (select a1 i3))) (let ((?v_1 (store (store a1 i3 ?v_0) i3 ?v_0))) (let ((?v_2 (select ?v_1 i1))) (let ((?v_3 (store (store ?v_1 i1 ?v_2) i1 ?v_2))) (let ((?v_7 (select ?v_3 i4)) (?v_8 (select ?v_3 i2))) (let ((?v_4 (store (store ?v_3 i4 ?v_8) i2 ?v_7))) (let ((?v_5 (select ?v_4 i3))) (let ((?v_6 (store (store ?v_4 i3 ?v_5) i3 ?v_5)) (?v_9 (store (store ?v_3 i2 ?v_7) i4 ?v_8))) (let ((?v_10 (select ?v_9 i3))) (let ((?v_11 (store (store ?v_9 i3 ?v_10) i3 ?v_10))) (not (= (store (store ?v_6 i1 (select ?v_6 i3)) i3 (select ?v_6 i1)) (store (store ?v_11 i3 (select ?v_11 i2)) i2 (select ?v_11 i3)))))))))))))))
(check-sat)
(exit)
