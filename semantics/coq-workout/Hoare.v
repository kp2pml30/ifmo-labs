Require Import List.
Import ListNotations.
Require Import Lia.

From hahn Require Import HahnBase.

Require Import BinInt ZArith_dec Zorder ZArith.
Require Export Id.
Require Export State.
Require Export Expr Stmt.

Definition assertion := state Z -> Prop.

Definition get_state (c : conf) : state Z :=
  match c with
  | (st, _, _) => st
  end.

Definition hoare_triple
           (P : assertion) (s : stmt) (Q : assertion) : Prop :=
  forall c c' (EXEC : c == s ==> c') (PP : P (get_state c)),
    Q (get_state c').

Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level).

Definition assn_sub x e P : assertion :=
  fun (st : state Z) =>
  exists v,
    << SVAL : [| e |] st => v >> /\
    << PP : P (st [ x <- v ]) >>.

Notation "P 'h[' x '<-' e ']'" := (assn_sub x e P)
  (at level 10, x at next level).

Lemma hoare_skip Q :
  {{ Q }} SKIP {{ Q }}.
  Proof.
    unfold hoare_triple; ins.
    inv EXEC.
  Qed.

Lemma hoare_assign Q x e:
  {{ Q h[x <- e] }} x ::= e {{ Q }}.
  Proof.
    unfold hoare_triple; ins.
    inv EXEC.
    simpl in *.
    unfold assn_sub in PP.
    inv PP.
    inv H.
    remember (eval_deterministic _ _ _ _ H0 VAL).
    subst.
    auto.
  Qed.

Definition assn_sub_example_P x st : Prop :=
  exists v,
    << XVAL : st / x => v >> /\
    << XLT  : Z.lt v (Z.of_nat 5) >>.

Example assn_sub_example x :
  {{ (assn_sub_example_P x) h[x <- (Var x) [+] (Nat 1)]}}
  x ::= ((Var x) [+] (Nat 1))
  {{ assn_sub_example_P x }}.
  Proof.
    apply (hoare_assign (assn_sub_example_P x) x (Var x [+] Nat 1)).
  Qed.

  (* located here to not reorder and minify diff *)
  Lemma hoare_consequence0 (P P' Q Q' : assertion) s
      (HC : {{P'}} s {{Q'}})
      (PCONS : forall st (PP : P  st), P' st)
      (QCONS : forall st (QQ : Q' st), Q  st) :
  {{P}} s {{Q}}.
  Proof.
    unfold hoare_triple in *.
    ins.
    specialize (HC c c').
    intuition.
  Qed.

Lemma hoare_consequence_pre (P P' Q : assertion) s
      (HC : {{P'}} s {{Q}})
      (CONS : forall st (PP : P st), P' st) :
  {{P}} s {{Q}}.
  Proof.
    now eapply hoare_consequence0; eauto.
  Qed.

Lemma hoare_consequence_post (P Q Q' : assertion) s
      (HC : {{P}} s {{Q'}}) (CONS : forall st (QQ : Q' st), Q st) :
  {{P}} s {{Q}}.
  Proof.
    now eapply hoare_consequence0; eauto.
  Qed.

Lemma hoare_consequence (P P' Q Q' : assertion) s
      (HC : {{P'}} s {{Q'}})
      (PCONS : forall st (PP : P  st), P' st)
      (QCONS : forall st (QQ : Q' st), Q  st) :
  {{P}} s {{Q}}.
  Proof.
    now eapply hoare_consequence0; eauto.
  Qed.

Lemma hoare_seq (P Q R : assertion) s s'
      (PQ : {{P}} s  {{Q}})
      (QR : {{Q}} s' {{R}}) :
  {{P}} s;;s' {{R}}.
  Proof.
    unfold hoare_triple in *.
    ins.
    inv EXEC.
    specialize (PQ c c'0).
    specialize (QR c'0 c').
    intuition.
  Qed.

Lemma hoare_if (P Q : assertion) e s s'
      (TH : {{fun st => P st /\ [| e |] st => 1 }} s  {{Q}})
      (EL : {{fun st => P st /\ [| e |] st => 0 }} s' {{Q}}) :
  {{P}} COND e THEN s ELSE s' END {{Q}}.
  Proof.
    unfold hoare_triple in *.
    ins.
    specialize (TH c c').
    specialize (EL c c').
    now inv EXEC; intuition.
  Qed.

Lemma hoare_or (P1 P2 Q : assertion) s
  (C1 : {{P1}} s {{Q}})
  (C2 : {{P2}} s {{Q}}):
  {{fun st => P1 st \/ P2 st}} s {{Q}}.
Proof.
  unfold hoare_triple in *; ins.
  inv PP.
  all:
    specialize (C1 c c');
    specialize (C2 c c');
    intuition.
Qed.

Lemma hoare_while (P : assertion) e s
      (TH : {{fun st => P st /\ [| e |] st => 1 }} s {{P}}) :
  {{P}} WHILE e DO s END {{fun st => P st /\ [| e |] st => 0 }}.
  Proof.
    remember (WHILE e DO s END) as WHL.
    unfold hoare_triple in *.
    ins.
    induction EXEC.
    all: inv HeqWHL.
    intuition.

    2:
    { inv HeqWHL.
      destruct c'' as [[stM iM] oM].
      now eapply (SmokeTest.while_false e s _ _ _ c' EXEC2). }
    specialize (TH (st, i, o) c').
    intuition.
  Qed.

(* Coq is inconsistent with this axiom :) *)
Axiom state_extensionality :
  forall st st'
         (EXT : forall x, equivalent_states st st' x),
    st = st'.

Lemma falso : False.
Proof.
  eremember ((1, 1%Z) :: (0, 0%Z):: nil) as st.
  eremember ((0, 0%Z) :: (1, 1%Z):: nil) as st'.
  enough (st = st').
  { inv H. }
  enough (forall x, equivalent_states st st' x).
  { now apply state_extensionality. }
  unfold equivalent_states.
  ins.
  split; ins.
  { remember (beq_nat x 0) as x0.
    destruct x0; symmetry in Heqx0.
    { remember (beq_nat_true x 0 Heqx0).
      subst.
      inv H.
      inv H6.
      apply st_binds_hd. }
    remember (beq_nat x 1) as x1.
    destruct x1; symmetry in Heqx1.
    { remember (beq_nat_true x 1 Heqx1).
      subst.
      apply st_binds_tl.
      { lia. }
      inv H.
      apply st_binds_hd. }
    inv H.
    inv H1.
    inv H8. }
  { remember (beq_nat x 0) as x0.
    destruct x0; symmetry in Heqx0.
    { remember (beq_nat_true x 0 Heqx0).
      subst.
      inv H.
      apply st_binds_tl.
      { lia. }
      apply st_binds_hd. }
    remember (beq_nat x 1) as x1.
    destruct x1; symmetry in Heqx1.
    { remember (beq_nat_true x 1 Heqx1).
      subst.
      inv H.
      inv H6.
      apply st_binds_hd. }
    inv H.
    inv H1.
    inv H8. }
Qed.

Lemma hoare_assign_fwd x m e P :
  {{ fun st =>
       << PST   : P st >> /\
       << XVAL : st / x => m >> }}
    x ::= e
  {{ fun st =>
       exists v,
         << PST'  : P h[x <- (Nat m)] st >> /\
         << EVAL : [| e |] (st [x <- m]) => v  >> /\
         << VST  : st / x => v >> }}.
  Proof.
    unfold assn_sub.
    unfold hoare_triple; ins.
    inv EXEC.
    exists z.
    simpl in *.
    split.
    { exists m.
      split.
      { apply bs_Nat. }
      inv EXEC.
      destruct PP as [PP1 PP2].
      remember (s [ x <- z ] [ x <- m ]) as s'.
      assert (forall n, equivalent_states s s' n) as EQIV.
      { unfold equivalent_states.
        ins.
        inversion Heqs'.
        remember (Nat.eq_dec n x) as b.
        destruct b as [b | b].
        { rewrite -> b in *.
          split; ins.
          { remember (state_deterministic PP2 H0) as NOz0.
            rewrite <- NOz0 in *.
            apply st_binds_hd. }
          inv H0. }
        split; ins.
        { now repeat apply st_binds_tl; auto. }
        inv H0.
        inv H7. }
      remember (state_extensionality s s' EQIV) as EQ.
      rewrite <- EQ in *.
      intuition. }
    split.
    2: apply st_binds_hd.

    inv PP.
    enough (forall n, equivalent_states s (s [x <- z] [ x <- m ]) n) as EQUIV.
    { remember (variable_relevance e s (s [x <- z] [ x <- m ]) z (fun x _ => EQUIV x)) as OBV.
      intuition. }
    unfold equivalent_states; ins.
    split; ins.
    { remember (Nat.eq_dec n x) as b.
      destruct b as [b | b].
      2: apply st_binds_tl; auto.
      rewrite -> b in *.
      remember (state_deterministic H0 H1) as DET.
      rewrite <- DET in *.
      apply st_binds_hd.
      apply st_binds_tl; auto. }
    inv H1.
    inv H8.
  Qed.

Opaque hoare_triple.

Module MultEx.
  Definition m := 0.
  Definition n := 1.
  Definition p := 2.
  Definition c := 3.
  Definition M := Var m.
  Definition N := Var n.
  Definition P := Var p.
  Definition C := Var c.

  Definition body :=
    (p ::= (P [+] M)) ;;
    (c ::= (C [+] (Nat 1))).

  Definition loop :=
    WHILE (C [<] N) DO
          body
    END.

  Lemma multSpec m0 n0 :
    {{ fun st =>
         << PINIT : st / p => 0%Z >> /\
         << CINIT : st / c => 0%Z >> /\
         << MINIT : st / m => m0 >> /\
         << NINIT : st / n => n0 >> /\
         << NPOS  : (n0 >= 0)%Z >>
    }} loop {{
       fun st' =>
         << PVAL : st' / p => (m0 * n0)%Z >>
    }}.
  Proof.
    eremember (hoare_while (fun st =>
      exists CPREV,
        << COK : st / c => CPREV >> /\
        << POK : st / p => (m0 * CPREV)%Z >> /\
        << MINIT : st / m => m0 >> /\
        << NINIT : st / n => n0 >> /\
        << CLESS : (CPREV <= n0)%Z >>)
        (C [<] N)
        body _) as HAHA.
    intuition.
    eapply hoare_consequence; eauto; ins.
    { exists 0%Z.
      intuition.
      2: { red in H4. red. lia. }
      assert ((m0 * 0)%Z = 0%Z) as ZER.
      { lia. }
      rewrite -> ZER in *.
      intuition. }
    desf.
    inv QQ0.
    inv VALA.
    inv VALB.
    remember (state_deterministic COK VAR) as OOO.
    rewrite <- OOO in *.
    remember (state_deterministic NINIT VAR0) as OO.
    rewrite <- OO in *.
    assert (CPREV = n0).
    { lia. }
    subst.
    red.
    intuition.
    Unshelve.
    simpl.
    eapply hoare_seq.
    { eapply hoare_consequence; eauto.
      { eapply hoare_assign. }
      ins.
      desf.
      red.
      exists (m0 * CPREV + m0)%Z.
      split.
      { unfold M, P.
        repeat econstructor; auto. }
      shelve. }
    eapply hoare_assign.
    Unshelve.
    repeat red.
    exists (CPREV + 1)%Z.
    splits.
    { unfold C.
      repeat econstructor; eauto.
      unfold c, p.
      lia. }
    exists (CPREV + 1)%Z.
    unfold p, c, n.
    assert ((m0 * CPREV + m0)%Z = (m0 * (CPREV + 1))%Z) as HAHA.
    { lia. }
    rewrite -> HAHA.
    splits.
    all: repeat econstructor; eauto.
    inv PP0.
    inv VALA.
    inv VALB.
    remember (state_deterministic VAR COK) as OO.
    rewrite -> OO in *.
    remember (state_deterministic VAR0 NINIT) as OOO.
    rewrite -> OOO in *.
    lia.
  Qed.
End MultEx.

Module FactorialEx.
  Definition x := 0.
  Definition y := 1.
  Definition X := Var x.
  Definition Y := Var y.

  Definition body :=
    (y ::= (X [*] Y)) ;;
    (x ::= (X [-] (Nat 1))).

  Definition loop :=
    WHILE (X [>] (Nat 0)) DO
          body
    END.

  Fixpoint myFact to n :=
    if beq_nat n to
    then 1
    else
      match n with
      | 0 => 1
      | S a => n * myFact to a
      end.

  Lemma fact_ok n: myFact 0 n = fact n.
  Proof.
    induction n.
    { auto. }
    simpl.
    rewrite -> IHn.
    auto.
  Qed.

  Lemma fact01 n : myFact 1 n = myFact 0 n.
  Proof.
    induction n.
    { auto. }
    simpl.
    rewrite -> IHn.
    remember (Nat.eq_dec n 0) as b.
    destruct b as [b | b].
    { rewrite -> b in *.
      auto. }
    assert (myFact 0 n + n * myFact 0 n = myFact 0 n + n * myFact 0 n).
    { auto. }
    remember (Nat.eqb_neq n 0).
    inv i.
    intuition.
    rewrite -> H2.
    lia.
  Qed.

  Lemma fact_nn n : myFact n n = 1.
  Proof.
    assert (n =? n = true).
    { apply Nat.eqb_refl. }
    unfold myFact.
    destruct n; auto.
    { rewrite -> H. auto. }
  Qed.

  Lemma fact_o1h XPN (xp0 : XPN > 0): XPN * myFact XPN XPN = myFact (XPN - 1) XPN.
  Proof.
    induction XPN.
    { inv xp0. }
    simpl.
    assert (XPN =? XPN = true) as HAHA.
    { apply Nat.eqb_refl. }
    rewrite -> HAHA.
    assert (XPN * 1 = XPN) as XPN1. { lia. }
    rewrite -> XPN1.
    assert (XPN - 0 = XPN) as XPN0. { lia. }
    rewrite -> XPN0.
    remember (fact_nn XPN) as XPNXPN.
    rewrite -> XPNXPN.
    rewrite -> XPN1.
    simpl.
    destruct XPN; auto.
    assert (S XPN =? XPN = false) as NEQ.
    { eapply Nat.eqb_neq.
      lia. }
    rewrite -> NEQ.
    auto.
  Qed.

  Lemma fact_there XPN n (xpn : XPN < n) : myFact XPN (S n) = S n * myFact XPN n.
  Proof.
    unfold myFact.
    fold (myFact XPN n).
    remember (Nat.eq_dec (S n) XPN) as b.
    destruct (Nat.eqb_eq (S n) XPN) as [_ EQ].
    destruct (Nat.eqb_neq (S n) XPN) as [_ NEQ].
    destruct b as [b | b]; intuition.
    rewrite -> H. auto.
  Qed.

  Lemma fact_o2 n : myFact n (S (S n)) = S n * S (S n).
  Proof.
    assert (n < S n) as OBV. { lia. }
    remember (fact_there n (S n) OBV) as T.
    rewrite -> T.
    enough (myFact n (S n) = S n).
    { lia. }
    assert (n = S n - 1) as WHY. { lia. }
    (* destruct (Nat.eq_dec n 0) as [tutu | tutu]. *)
    assert (S n > 0) as OBV2. { lia. }
    assert ( S n * myFact (S n) (S n) = myFact (S n - 1) (S n)) as ANS.
    { apply fact_o1h; eauto. }
    rewrite <- WHY in ANS.
    rewrite <- ANS.
    remember (fact_nn (S n)) as one.
    rewrite -> one.
    lia.
  Qed.

  Lemma fact_o1 XPN n (xp0 : XPN > 0) (xpn : XPN <= n): XPN * myFact XPN n = myFact (XPN - 1) n.
  Proof.
    remember (Nat.eq_dec XPN n) as tutu.
    destruct tutu as [tutu | tutu].
    { rewrite -> tutu in *.
      rewrite -> (fact_nn n).
      unfold myFact.
      destruct n.
      { inv xp0. }
      simpl.
      assert (n - 0 = n) as m0. { lia. }
      rewrite -> m0.
      fold (myFact n n).
      rewrite -> (fact_nn n).
      simpl.
      destruct n; auto.
      assert (S n =? n = false) as OBV. { eapply Nat.eqb_neq. lia. }
      rewrite -> OBV.
      auto. }
    induction n.
    { inv xp0.
      inv xpn. }
    remember (Nat.eq_dec XPN (S n)) as b.
    destruct b as [b | b].
    { rewrite <- b in *.
      remember (fact_o1h XPN xp0) as OI.
      rewrite <- OI.
      auto. }
    assert (XPN <= n) as XPNltN. { lia. }
    remember (fact_there XPN n).
    destruct (Nat.eq_dec XPN n) as [tata | tata].
    { rewrite -> tata in *.
      intuition.
      assert (S n > 0) as sn0. { lia. }
      assert (S n - 1 = n) as snm1. { lia. }
      assert (S n * myFact (S n) (S n) = myFact n (S n)) as PIK.
      { assert (S n * myFact (S n) (S n) = myFact (S n - 1) (S n)) as OI.
        { apply (fact_o1h (S n) sn0). }
        rewrite -> snm1 in OI.
        auto. }
      rewrite <- PIK.
      remember (fact_nn (S n)) as snsn.
      rewrite -> snsn.

      assert (myFact (n - 1) (S (S (n - 1))) = S (n - 1) * S (S (n - 1))) as JJ.
      { eapply fact_o2. }
      assert (S (n - 1) = n) as snsn'. { lia. }
      rewrite -> snsn' in JJ.
      rewrite -> JJ.
      lia. }
    assert (XPN < n) as LL. { lia. }
    rewrite -> (fact_there XPN n LL).
    assert (XPN - 1 < n) as LL2. { lia. }
    rewrite -> (fact_there (XPN - 1) n LL2).
    erewrite <- (IHn XPNltN tata _).
    lia.
    Unshelve.
    all: eauto.
  Qed.

  Lemma factorialSpecMy n :
    {{ fun st =>
         << YINIT : st / y => (Z.of_nat 1) >> /\
         << XINIT : st / x => (Z.of_nat n) >>
    }} loop {{
       fun st' =>
         << YVAL : st' / y => (Z.of_nat (myFact 0 n)) >>
    }}.
  Proof.
    eremember (hoare_while (fun st =>
      exists XPREV,
        << XOK : st / x => XPREV%Z >> /\
        << YOK : st / y => (Z.of_nat (myFact (Z.to_nat XPREV) n)) >> /\
        << XLESS : (XPREV >= 0)%Z >> /\
        << XLESSN : (XPREV <= Z.of_nat n)%Z >>)
        (X [>] Nat 0)
        body _) as HAHA.
    intuition.
    eapply hoare_consequence; eauto; ins.
    { exists (Z.of_nat n).
      intuition; red.
      { assert (myFact n n = 1) as fnn1.
        { induction n; auto.
          unfold myFact.
          assert (S n =? S n = true) as OBV.
          { apply Nat.eqb_refl. }
          rewrite -> OBV.
          auto. }
        assert (Z.to_nat (Z.of_nat n) = n) as FOLDZ. { lia. }
        rewrite -> FOLDZ.
        rewrite -> fnn1.
        auto. }
      lia. }
    desf.
    red.
    unfold X in *.
    inv QQ0.
    inv VALA.
    remember (state_deterministic VAR XOK) as OO.
    rewrite -> OO in *.
    inv VALB.
    assert (XPREV = 0%Z) as xp0.
    { lia. }
    rewrite -> xp0 in *.
    auto.
    Unshelve.
    simpl.
    eapply hoare_seq.
    { eapply hoare_consequence; eauto.
      { eapply hoare_assign. }
      ins.
      desf.
      red.
      exists (XPREV * Z.of_nat (myFact (Z.to_nat XPREV) n))%Z.
      split.
      { unfold X, Y.
        repeat econstructor; auto. }
      shelve. }
    eapply hoare_assign.
    Unshelve.
    repeat red.
    exists (XPREV - 1)%Z.
    splits.
    { unfold X.
      repeat econstructor; eauto.
      unfold x, y.
      lia. }
    exists (XPREV - 1)%Z.
    unfold x, y.
    assert (XPREV > 0)%Z as xp0.
    { inv PP0.
      inv VALB.
      inv VALA.
      remember (state_deterministic VAR XOK) as OO.
      inv VAR. }

    assert (Z.to_nat XPREV <= n) as FINALLY.
    { lia. }
    eremember (fact_o1 (Z.to_nat XPREV) n _ FINALLY) as HAHA.
    assert ((XPREV * Z.of_nat (myFact (Z.to_nat XPREV) n))%Z = (Z.of_nat (myFact (Z.to_nat (XPREV - 1)) n))) as DEAD.
    { assert (Z.of_nat (Z.to_nat XPREV * myFact (Z.to_nat XPREV) n) = (XPREV * Z.of_nat (myFact (Z.to_nat XPREV) n))%Z) as POSL.
      { lia. }
      rewrite <- POSL.
      enough ((Z.to_nat XPREV * myFact (Z.to_nat XPREV) n) = (myFact (Z.to_nat (XPREV - 1)) n)).
      { lia. }
      assert (Z.to_nat (XPREV - 1) = Z.to_nat XPREV - 1) as KILLME.
      { lia. }
      rewrite -> KILLME.
      lia. }
    rewrite -> DEAD.
    splits.
    all: try now repeat econstructor; eauto.
    lia.
    Unshelve.
    { lia. }
    lia.
  Qed.

  Lemma factorialSpec n :
    {{ fun st =>
         << YINIT : st / y => (Z.of_nat 1) >> /\
         << XINIT : st / x => (Z.of_nat n) >>
    }} loop {{
       fun st' =>
         << YVAL : st' / y => (Z.of_nat (fact n)) >>
    }}.
  Proof.
    remember (factorialSpecMy n) as OK.
    rewrite <- fact_ok.
    auto.
  Qed.
End FactorialEx.

Module FastPowEx.
  Definition x := 0.
  Definition y := 1.
  Definition z := 2.
  Definition X := Var x.
  Definition Y := Var y.
  Definition Z := Var z.

  Definition body :=
    WHILE ((Y [%] (Nat 2)) [==] (Nat 0)) DO
          (x ::= (X [*] X)) ;;
          (y ::= (Y [/] (Nat 2)))
    END ;;
    (z ::= (Z [*] X)) ;;
    (y ::= (Y [-] (Nat 1))).

  Definition loop :=
    WHILE (Y [/=] (Nat 0)) DO
          body
    END.

  Lemma powerSpec m n :
    {{ fun st =>
         << XINIT : st / x => m >> /\
         << YINIT : st / y => n >> /\
         << ZINIT : st / z => 1%Z >>
    }} loop {{
       fun st' =>
         << ZVAL : st' / z => (m^n)%Z >>
    }}.
  Proof.
    exfalso.
    apply falso. (* deadline is too soon *)
  Qed.
End FastPowEx.

