(set-info :smt-lib-version 2.6)
(set-logic QF_AUFLIA)
(set-info :source |
Benchmarks used in the followin paper:
Big proof engines as little proof engines: new results on rewrite-based satisfiability procedure
Alessandro Armando, Maria Paola Bonacina, Silvio Ranise, Stephan Schulz. 
PDPAR'05
http://www.ai.dist.unige.it/pdpar05/


|)
(set-info :category "crafted")
(set-info :status sat)
(declare-fun a1 () (Array Int Int))
(declare-fun i0 () Int)
(declare-fun i1 () Int)
(declare-fun i2 () Int)
(declare-fun sk ((Array Int Int) (Array Int Int)) Int)
(assert (let ((?v_0 (select a1 i0))) (let ((?v_1 (store (store a1 i0 ?v_0) i0 ?v_0))) (let ((?v_2 (store (store ?v_1 i1 (select ?v_1 i2)) i2 (select ?v_1 i1)))) (let ((?v_4 (select ?v_2 i2))) (let ((?v_3 (store (store ?v_2 i1 ?v_4) i2 (select ?v_2 i1))) (?v_5 (store (store ?v_2 i2 ?v_4) i2 ?v_4))) (let ((?v_6 (sk ?v_3 ?v_5))) (not (= (select ?v_3 ?v_6) (select ?v_5 ?v_6))))))))))
(check-sat)
(exit)
