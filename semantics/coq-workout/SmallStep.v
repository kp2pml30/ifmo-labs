Require Import List.
Import ListNotations.

Require Import BinInt ZArith_dec.
Require Export Id State Expr Stmt.

From hahn Require Import HahnBase.

Module SmallStep.

  Reserved Notation "c1 '--' s '-->' c2" (at level 0).

  Inductive ss_int_step : stmt -> conf -> option stmt * conf -> Prop :=
  | ss_Skip        : forall (c : conf), c -- SKIP --> (None, c)
  | ss_Assign      : forall (s : state Z) (i o : list Z) (x : id) (e : expr) (z : Z)
                            (SVAL : [| e |] s => z),
      (s, i, o) -- x ::= e --> (None, (s [x <- z], i, o))
  | ss_Read        : forall (s : state Z) (i o : list Z) (x : id) (z : Z),
      (s, z::i, o) -- READ x --> (None, (s [x <- z], i, o))
  | ss_Write       : forall (s : state Z) (i o : list Z) (e : expr) (z : Z)
                            (SVAL : [| e |] s => z),
      (s, i, o) -- WRITE e --> (None, (s, i, z::o))
  | ss_Seq_Compl   : forall (c c' : conf) (s1 s2 : stmt)
                            (SSTEP : c -- s1 --> (None, c')),
      c -- s1 ;; s2 --> (Some s2, c')
  | ss_Seq_InCompl : forall (c c' : conf) (s1 s2 s1' : stmt)
                            (SSTEP : c -- s1 --> (Some s1', c')),
      c -- s1 ;; s2 --> (Some (s1' ;; s2), c')
  | ss_If_True     : forall (s : state Z) (i o : list Z) (s1 s2 : stmt) (e : expr)
                            (SCVAL : [| e |] s => Z.one),
      (s, i, o) -- COND e THEN s1 ELSE s2 END --> (Some s1, (s, i, o))
  | ss_If_False    : forall (s : state Z) (i o : list Z) (s1 s2 : stmt) (e : expr)
                            (SCVAL : [| e |] s => Z.zero),
      (s, i, o) -- COND e THEN s1 ELSE s2 END --> (Some s2, (s, i, o))
  | ss_While       : forall (c : conf) (s : stmt) (e : expr),
      c -- WHILE e DO s END --> (Some (COND e THEN s ;; WHILE e DO s END ELSE SKIP END), c)
  where "c1 -- s --> c2" := (ss_int_step s c1 c2).

  Reserved Notation "c1 '--' s '-->>' c2" (at level 0).

  Inductive ss_int : stmt -> conf -> conf -> Prop :=
    ss_int_Base : forall (s : stmt) (c c' : conf)
                         (STEP : c -- s --> (None, c')),
      c -- s -->> c'
  | ss_int_Step : forall (s s' : stmt) (c c' c'' : conf)
                    (STEP  : c -- s --> (Some s', c'))
                    (STEPS : c' -- s' -->> c''),
      c -- s -->> c''
  where "c1 -- s -->> c2" := (ss_int s c1 c2).

  Lemma ss_int_step_deterministic (s : stmt)
        (c : conf) (c' c'' : option stmt * conf)
        (EXEC1 : c -- s --> c')
        (EXEC2 : c -- s --> c'') :
    c' = c''.
  Proof.
    generalize dependent c'.
    generalize dependent c''.
    induction s; ins.
    all: try now inv EXEC1; inv EXEC2.
    all: try now
      inv EXEC1; inv EXEC2;
      remember (eval_deterministic _ _ _ _ SVAL SVAL0);
      subst;
      auto.
    { inv EXEC1;
      inv EXEC2;
        specialize (IHs1 _ SSTEP _ SSTEP0);
        inv IHs1.
    }
    inv EXEC1;
    inv EXEC2;
    eval_zero_not_one.
  Qed.

  Lemma ss_int_deterministic (c c' c'' : conf) (s : stmt)
        (STEP1 : c -- s -->> c') (STEP2 : c -- s -->> c'') :
    c' = c''.
  Proof.
    induction STEP1; inv STEP2.
    all: try now
      remember (ss_int_step_deterministic _ _ _ _ STEP STEP0) as HAHA;
      inv HAHA;
      intuition.
  Qed.

  Lemma ss_bs_base (s : stmt) (c c' : conf) (STEP : c -- s --> (None, c')) :
    c == s ==> c'.
  Proof.
    generalize dependent c'.
    induction s; ins.
    all: now
      inv STEP;
      constructor.
  Qed.

  Lemma ss_ss_composition (c c' c'' : conf) (s1 s2 : stmt)
        (STEP1 : c -- s1 -->> c'') (STEP2 : c'' -- s2 -->> c') :
    c -- s1 ;; s2 -->> c'.
  Proof.
    induction STEP1; ins.
    { inv STEP2.
      all:
        remember (ss_Seq_Compl _ _ _ s2 STEP) as TUTU;
        eapply ss_int_Step; eauto. }
    remember (ss_int_Step _ _ _ _ _ STEP STEP1) as OH.
    inv STEP2.
    all:
      remember (ss_Seq_InCompl);
      remember (ss_Seq_InCompl _ _ _ s2 _ STEP) as HAHA;
      enough (c'0 -- s' ;; s2 -->> c');
      (try now eapply ss_int_Step; eauto);
      specialize (IHSTEP1 STEP2);
      auto.
  Qed.

  Lemma ss_bs_step (c c' c'' : conf) (s s' : stmt)
        (STEP : c -- s --> (Some s', c'))
        (EXEC : c' == s' ==> c'') :
    c == s ==> c''.
  Proof.
    generalize dependent s'.
    generalize dependent c''.
    induction s; ins.
    1-4: now inv STEP.
    { inv STEP.
      { eapply ss_bs_base in SSTEP.
        seq_apply. }
      inv EXEC.
      specialize (IHs1 c'0 s1' SSTEP STEP1).
      seq_apply. }
    1: inv STEP.
    1-2: now econstructor; eauto.
    inv STEP.
    inv EXEC.
    { seq_inversion.
      econstructor; eauto. }
    inv STEP0.
    constructor.
    auto.
  Qed.

  Theorem bs_ss_eq (s : stmt) (c c' : conf) :
    c == s ==> c' <-> c -- s -->> c'.
  Proof.
    split; ins.
    { generalize dependent c.
      generalize dependent c'.
      induction s; ins.
      all: try now inv H; repeat constructor.
      2: {
        inv H.
        1:
          specialize (IHs1 _ _ STEP);
          remember (ss_If_True s i o s1 s2 e CVAL).
        2:
          specialize (IHs2 _ _ STEP);
          remember (ss_If_False s i o s1 s2 e CVAL).
        all: now eapply ss_int_Step; eauto. }
      2: {
        remember (WHILE e DO s END) as WHL.
        induction H; ins.
        all: try now inversion HeqWHL.
        { inv HeqWHL.
          intuition.
          assert ((st, i, o) -- s;; (WHILE e DO s END) -->> c'') as WHL.
          { now eapply ss_ss_composition; eauto. }
          assert ((st, i, o) -- (COND e THEN s;; WHILE e DO s END ELSE SKIP END) --> (Some (s;; WHILE e DO s END), (st, i, o))) as HAHA.
          { constructor; auto. }
          eapply ss_int_Step.
          { apply ss_While. }
          now eapply ss_int_Step; eauto. }
        inv HeqWHL.
        assert ((st, i, o) -- (COND e THEN s;; WHILE e DO s END ELSE SKIP END) --> (Some SKIP, (st, i, o))) as HAHA.
        { constructor. auto. }
        eapply ss_int_Step.
        { eapply ss_While. }
        eapply ss_int_Step.
        { exact HAHA. }
        now repeat constructor.
      }
      seq_inversion.
      rename c' into c''.
      rename c'0 into c'.
      specialize (IHs2 c'' c' STEP2) as R2.
      specialize (IHs1 c' c STEP1) as R1.
      now eapply ss_ss_composition; eauto. }
    induction H.
    { apply ss_bs_base. auto. }
    now eapply ss_bs_step; eauto.
  Qed.
End SmallStep.
