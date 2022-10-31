Require Import List.
Import ListNotations.

Require Import BinInt ZArith_dec.
Require Export Id State Expr.

From hahn Require Import HahnBase.

(* AST for statements *)
Inductive stmt : Type :=
| SKIP  : stmt
| Assn  : id -> expr -> stmt
| READ  : id -> stmt
| WRITE : expr -> stmt
| Seq   : stmt -> stmt -> stmt
| If    : expr -> stmt -> stmt -> stmt
| While : expr -> stmt -> stmt.

(* Supplementary notation *)
Notation "x  '::=' e"                         := (Assn  x e    ) (at level 37, no associativity).
Notation "s1 ';;'  s2"                        := (Seq   s1 s2  ) (at level 35, right associativity).
Notation "'COND' e 'THEN' s1 'ELSE' s2 'END'" := (If    e s1 s2) (at level 36, no associativity).
Notation "'WHILE' e 'DO' s 'END'"             := (While e s    ) (at level 36, no associativity).

(* Configuration *)
Definition conf :=  (state Z * list Z * list Z)%type.

(* Big-step evaluation relation *)
Reserved Notation "c1 '==' s '==>' c2" (at level 0).

Notation "st [ x '<-' y ]" := (update st x y) (at level 0).

Inductive bs_int : stmt -> conf -> conf -> Prop := 
| bs_Skip        : forall (c : conf),
    c == SKIP ==> c 
| bs_Assign      : forall (s : state Z) (i o : list Z) (x : id) (e : expr) (z : Z)
                          (VAL : [| e |] s => z),
    (s, i, o) == x ::= e ==> (s [x <- z], i, o)
| bs_Read        : forall (s : state Z) (i o : list Z) (x : id) (z : Z),
    (s, z::i, o) == READ x ==> (s [x <- z], i, o)
| bs_Write       : forall (s : state Z) (i o : list Z) (e : expr) (z : Z)
                          (VAL : [| e |] s => z),
    (s, i, o) == WRITE e ==> (s, i, z::o)
| bs_Seq         : forall (c c' c'' : conf) (s1 s2 : stmt)
                          (STEP1 : c == s1 ==> c') (STEP2 : c' == s2 ==> c''),
    c ==  s1 ;; s2 ==> c''
| bs_If_True     : forall (s : state Z) (i o : list Z) (c' : conf) (e : expr) (s1 s2 : stmt)
                     (CVAL : [| e |] s => Z.one)
                     (STEP : (s, i, o) == s1 ==> c'),
    (s, i, o) == COND e THEN s1 ELSE s2 END ==> c'
| bs_If_False    : forall (s : state Z) (i o : list Z) (c' : conf) (e : expr) (s1 s2 : stmt)
                     (CVAL : [| e |] s => Z.zero)
                     (STEP : (s, i, o) == s2 ==> c'),
    (s, i, o) == COND e THEN s1 ELSE s2 END ==> c'
| bs_While_True  : forall (st : state Z) (i o : list Z) (c' c'' : conf) (e : expr) (s : stmt)
                          (CVAL  : [| e |] st => Z.one)
                          (STEP  : (st, i, o) == s ==> c')
                          (WSTEP : c' == WHILE e DO s END ==> c''),
    (st, i, o) == WHILE e DO s END ==> c''
| bs_While_False : forall (st : state Z) (i o : list Z) (e : expr) (s : stmt)
                          (CVAL : [| e |] st => Z.zero),
    (st, i, o) == WHILE e DO s END ==> (st, i, o)
where "c1 == s ==> c2" := (bs_int s c1 c2).

(* Big step equivalence *)
Definition bs_equivalent (s1 s2 : stmt) :=
  forall (c c' : conf),
    c == s1 ==> c' <-> c == s2 ==> c'.

Notation "s1 '~~~' s2" := (bs_equivalent s1 s2) (at level 0).

Lemma bs_equivalent_refl (s : stmt) : s ~~~ s.
Proof.
  split; ins; auto.
Qed.

Ltac seq_inversion :=
  match goal with
    H: _ == _ ;; _ ==> _ |- _ => inversion_clear H
  end.

Ltac seq_apply :=
  match goal with
  | H: _   == ?s1 ==> ?c' |- _ == (?s1 ;; _) ==> _ => 
    apply bs_Seq with c'; solve [seq_apply | assumption]
  | H: ?c' == ?s2 ==>  _  |- _ == (_ ;; ?s2) ==> _ => 
    apply bs_Seq with c'; solve [seq_apply | assumption]
  end.

Module SmokeTest.

  (* Associativity of sequential composition *)
  Lemma seq_assoc (s1 s2 s3 : stmt) :
    ((s1 ;; s2) ;; s3) ~~~ (s1 ;; (s2 ;; s3)).
  Proof.
    split;
      ins;
      repeat seq_inversion;
      seq_apply.
  Qed.
  
  (* One-step unfolding *)
  Lemma while_unfolds (e : expr) (s : stmt) :
    (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof.
    split; ins.
    { inv H.
      { eapply bs_If_True; eauto.
        seq_apply. }
      eapply bs_If_False; eauto.
      constructor. }
    inv H.
    { inv STEP.
      eapply bs_While_True; eauto. }
    inv STEP.
    eapply bs_While_False; eauto.
  Qed.
  
  (* Terminating loop invariant *)
  Lemma while_false (e : expr) (s : stmt) (st : state Z)
        (i o : list Z) (c : conf)
        (EXE : c == WHILE e DO s END ==> (st, i, o)) :
    [| e |] st => Z.zero.
  Proof.
    remember (WHILE e DO s END) as EXE1.
    remember ((st, i, o)).
    induction EXE; auto.
    all: now inv HeqEXE1.
  Qed.
  
  (* Big-step semantics does not distinguish non-termination from stuckness *)
  Lemma loop_eq_undefined :
    (WHILE (Nat 1) DO SKIP END) ~~~
    (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof.
    split; ins.
    { remember (WHILE (Nat 1) DO SKIP END) as HAHA.
      induction H.
      all: try now inv HeqHAHA.
      inv HeqHAHA.
      inv H.
      eapply IHbs_int2; eauto.
    }
    inv H; inv CVAL.
  Qed.
  
  (* Loops with equivalent bodies are equivalent *)
  Lemma while_eq (e : expr) (s1 s2 : stmt)
        (EQ : s1 ~~~ s2) :
    WHILE e DO s1 END ~~~ WHILE e DO s2 END.
  Proof.
    unfold "~~~" in EQ.
    split;
      ins;
      remember (WHILE e DO s1 END) as HAHA1;
      remember (WHILE e DO s2 END) as HAHA2;
      induction H.
    all: try (inv HeqHAHA1); (try inv HeqHAHA2).
    all: try now
      eapply bs_While_True; eauto;
      apply EQ;
      auto.
    all: try now
      eapply bs_While_False; eauto.
  Qed.
  
  (* Loops with the constant true condition don't terminate *)
  (* Exercise 4.8 from Winskel's *)
  Lemma while_true_undefined c s c' :
    ~ c == WHILE (Nat 1) DO s END ==> c'.
  Proof.
    intros A.
    remember (WHILE Nat 1 DO s END) as HAHA.
    induction A.
    all: inv HeqHAHA.
    inv CVAL.
  Qed.
  
End SmokeTest.

(* Semantic equivalence is a congruence *)
Lemma eq_congruence_seq_r (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s  ;; s1) ~~~ (s  ;; s2).
Proof.
  remember (s ;; s1) as HAHA1.
  remember (s ;; s2) as HAHA2.
  split; ins;
    induction H.
  all: try (inv HeqHAHA1); try (inv HeqHAHA2).
  all:
    apply EQ in H0;
    econstructor; eauto.
Qed.

Lemma eq_congruence_seq_l (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s1 ;; s) ~~~ (s2 ;; s).
Proof.
  remember (s1 ;; s) as HAHA1.
  remember (s2 ;; s) as HAHA2.
  split; ins; induction H.
  all: try (inv HeqHAHA1); try (inv HeqHAHA1).
  all: apply EQ in H; econstructor; eauto.
Qed.

Lemma eq_congruence_cond_else
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END.
Proof.
  remember (COND e THEN s ELSE s1 END) as HAHA1.
  remember (COND e THEN s ELSE s2 END) as HAHA2.
  split; ins; induction H.
  all: try (inv HeqHAHA1); try (inv HeqHAHA1).
  all: try now eapply bs_If_True; try (apply EQ in H); eauto.
  all: now eapply bs_If_False; try (apply EQ in H); eauto.
Qed.

Lemma eq_congruence_cond_then
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s1 ELSE s END ~~~ COND e THEN s2 ELSE s END.
Proof.
  remember (COND e THEN s1 ELSE s END) as HAHA1.
  remember (COND e THEN s2 ELSE s END) as HAHA2.
  split; ins; induction H.
  all: try (inv HeqHAHA1); try (inv HeqHAHA1).
  all: try now eapply bs_If_True; try (apply EQ in H); eauto.
  all: now eapply bs_If_False; try (apply EQ in H); eauto.
Qed.

Lemma eq_congruence_while
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  WHILE e DO s1 END ~~~ WHILE e DO s2 END.
Proof.
  remember (WHILE e DO s1 END) as HAHA1.
  remember (WHILE e DO s2 END) as HAHA2.
  split; ins; induction H.
  all: try (inv HeqHAHA1); try (inv HeqHAHA1).
  all: try now eapply bs_While_True; try (apply EQ in H); eauto.
  all: now eapply bs_While_False; try (apply EQ in H); eauto.
Qed.

Lemma eq_congruence (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  ((s  ;; s1) ~~~ (s  ;; s2)) /\
  ((s1 ;; s ) ~~~ (s2 ;; s )) /\
  (COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END) /\
  (COND e THEN s1 ELSE s  END ~~~ COND e THEN s2 ELSE s  END) /\
  (WHILE e DO s1 END ~~~ WHILE e DO s2 END).
Proof.
  splits; intros n.
  { apply eq_congruence_seq_r; auto. }
  { apply eq_congruence_seq_l; auto. }
  { apply eq_congruence_cond_else; auto. }
  { apply eq_congruence_cond_then; auto. }
  { apply eq_congruence_while; auto. }
Qed.

(* Big-step semantics is deterministic *)
Ltac by_eval_deterministic :=
  match goal with
    H1: [|?e|]?s => ?z1, H2: [|?e|]?s => ?z2 |- _ => 
     apply (eval_deterministic e s z1 z2) in H1; [subst z2; reflexivity | assumption]
  end.

Ltac eval_zero_not_one :=
  match goal with
    H : [|?e|] ?st => (Z.one), H' : [|?e|] ?st => (Z.zero) |- _ =>
    assert (Z.zero = Z.one) as JJ; [ | inversion JJ];
    eapply eval_deterministic; eauto
  end.

Lemma bs_int_deterministic (c c1 c2 : conf) (s : stmt)
      (EXEC1 : c == s ==> c1) (EXEC2 : c == s ==> c2) :
  c1 = c2.
Proof.
  generalize dependent c1.
  generalize dependent c2.
  generalize dependent c.
  induction s; ins.
  all: try now
    inv EXEC1; inv EXEC2;
    try remember (eval_deterministic _ _ _ _ VAL0 VAL); subst;
    auto.
  { inv EXEC1.
    inv EXEC2.
    remember (eq_congruence_seq_r s1 s2 s2 (bs_equivalent_refl _)).
    specialize (IHs1 c _ STEP1 _ STEP0); subst.
    specialize (IHs2 c' _ STEP3 _ STEP2); subst.
    reflexivity. }
  { inv EXEC1;
    inv EXEC2.
    { eapply bs_If_True in EXEC1; eauto. }
    { eval_zero_not_one. }
    { eval_zero_not_one. }
    eapply bs_If_False in EXEC1; eauto. }
  remember (WHILE e DO s END) as HAHA.
  induction EXEC1.
  all: inv HeqHAHA.
  { specialize (IHEXEC1_2 HeqHAHA).
    remember ((st, i, o)) as c0.
    (*
      c0 ==> s ==> c'
      c' == WHILE ==> c''
      c0 ==> WHILE ==> c2
    *)
    apply SmokeTest.while_unfolds in EXEC2.
    remember (COND e THEN s;; (WHILE e DO s END) ELSE SKIP END) as IFF.
    inv EXEC2.
    { inv STEP.
      remember (IHs (st, i, o) c'0 STEP1 c' EXEC1_1) as c'0_eq_c'.
      subst.
      intuition. }
    eval_zero_not_one. }
  apply SmokeTest.while_unfolds in EXEC2.
  remember (COND e THEN s;; (WHILE e DO s END) ELSE SKIP END) as IFF.
  inv EXEC2.
  { eval_zero_not_one. }
  { inversion STEP. reflexivity. }
  Unshelve.
  all: auto.
Qed.

(* Contextual equivalence *)
Inductive Context : Type :=
| Hole 
| SeqL   : Context -> stmt -> Context
| SeqR   : stmt -> Context -> Context
| IfThen : expr -> Context -> stmt -> Context
| IfElse : expr -> stmt -> Context -> Context
| WhileC : expr -> Context -> Context.

(* Plugging a statement into a context *)
Fixpoint plug (C : Context) (s : stmt) : stmt := 
  match C with
  | Hole => s
  | SeqL     C  s1 => Seq (plug C s) s1
  | SeqR     s1 C  => Seq s1 (plug C s) 
  | IfThen e C  s1 => If e (plug C s) s1
  | IfElse e s1 C  => If e s1 (plug C s)
  | WhileC   e  C  => While e (plug C s)
  end.  

Notation "C '<~' e" := (plug C e) (at level 43, no associativity).

(* Contextual equivalence *)
Definition contextual_equivalent (s1 s2 : stmt) :=
  forall (C : Context), (C <~ s1) ~~~ (C <~ s2).
Notation "s1 '~c~' s2" := (contextual_equivalent s1 s2)
                            (at level 42, no associativity).

Lemma eq_eq_ceq_there C c c' s1 s2 (H : forall c c' : conf, (c) == s1 ==> (c') <-> (c) == s2 ==> (c')) (PRE : (c) == C <~ s1 ==> (c')) :
  (c) == C <~ s2 ==> (c').
Proof.
  unfold "~c~", "~~~".
  ins.
  generalize dependent c.
  generalize dependent c'.
  induction C.
  { ins.
    eapply H; eauto. }
  all:
    intros c c' IH;
    simpl in *.
  1-4:
    inv IH.
  { specialize (IHC _ _ STEP1).
    seq_apply. }
  { specialize (IHC _ _ STEP2).
    seq_apply. }
  1, 3: now apply bs_If_True; eauto.
  1, 2: now apply bs_If_False; eauto.
  remember (WHILE e DO C <~ s1 END) as HAHA.
  induction IH.
  all: inv HeqHAHA.
  { eapply bs_While_True; eauto. }
  eapply bs_While_False; eauto.
Qed.

(* Contextual equivalence is equivalent to the semantic one *)
Lemma eq_eq_ceq s1 s2: s1 ~~~ s2 <-> s1 ~c~ s2.
Proof.
  unfold "~c~", "~~~".
  split; ins; split; ins.
  1, 2: now eapply eq_eq_ceq_there; eauto.
  1, 2: specialize (H Hole c c'); simpl in H; intuition.
Qed.