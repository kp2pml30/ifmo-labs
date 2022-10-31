Require Import List.
Import ListNotations.
Require Import Lia.

Require Import BinInt ZArith_dec Zorder ZArith.
Require Export Id State Expr Stmt.

From hahn Require Import HahnBase.

Lemma state_dec {t : Type} (st : state t) (x : id):
  (forall i, st / x => i -> False) + {n | st / x => n}.
Proof.
  induction st.
  { left.
    ins.
    inv H. }
  destruct a as [ai vi].
  destruct (Nat.eq_dec ai x).
  { subst.
    right.
    exists vi.
    apply st_binds_hd. }
  inv IHst.
  { left.
    ins.
    apply update_neq in H0; eauto. }
  right.
  destruct X as [av ap].
  exists av.
  apply st_binds_tl; eauto.
Qed.

Module Euclid.
  Definition m := 0.
  Definition n := 1.
  Definition M := Var m.
  Definition N := Var n.

  Definition body :=
          COND (M [<] N)
          THEN n ::= (N [-] M)
          ELSE m ::= (M [-] N)
          END.


  Definition euclid :=
    WHILE (M [/=] N) DO
          body
    END.

  Definition is_good
    n m := n = Euclid.n /\ m = Euclid.m \/ n = Euclid.m /\ m = Euclid.n.

  Definition st_lt
      n m
      (GOOD: is_good n m)
      st st' :=
    exists mz nz mz' nz',
      (mz  >= 1) /\
      (nz  >= 1) /\
      (mz' >= 1) /\
      (nz' >= 1) /\
      (st  / m => (Z.of_nat mz )) /\
      (st  / n => (Z.of_nat nz )) /\
      (st' / m => (Z.of_nat mz')) /\
      (st' / n => (Z.of_nat nz')) /\
      (mz + nz < mz' + nz').

  Lemma dflt_good : Euclid.n = Euclid.n /\ Euclid.m = Euclid.m \/ Euclid.n = Euclid.m /\ Euclid.m = Euclid.n.
  Proof.
    auto.
  Qed.

  Lemma flipped_good : Euclid.m = Euclid.n /\ Euclid.n = Euclid.m \/ Euclid.m = Euclid.m /\ Euclid.n = Euclid.n.
  Proof.
    auto.
  Qed.

  Definition fun_of_st (st : state Z) : nat :=
    match state_dec st n, state_dec st m with
    | inr nz, inr mz => Z.to_nat (proj1_sig nz + proj1_sig mz)
    | _, _ => 0
    end.

  Lemma fun_of_st_is
    (x: state Z)
    (mz nz : nat)
    (H: mz >= 1)
    (H0: nz >= 1)
    (H3: (x) / m => (Z.of_nat mz))
    (H4: (x) / n => (Z.of_nat nz))
    : fun_of_st x = mz + nz.
  Proof.
    unfold fun_of_st.
    remember (Z.of_nat nz) as nzn.
    remember (Z.of_nat mz) as mzn.
    destruct (state_dec x n), (state_dec x m).
    1-3: exfalso; eauto.
    unfold proj1_sig.
    destruct s, s0.
    remember (state_deterministic H4 s).
    subst.
    remember (state_deterministic H3 s0).
    subst.
    lia.
  Qed.

  Lemma st_lt_well_founded : well_founded (st_lt n m dflt_good).
  Proof.
    remember (well_founded_lt_compat).
    eapply well_founded_lt_compat.
    ins.
    unfold st_lt in H.
    des.
    enough (fun_of_st x < fun_of_st y).
    { eauto. }
    remember (fun_of_st_is x mz nz H H0 H3 H4).
    remember (fun_of_st_is y mz' nz' H1 H2 H5 H6).
    lia.
  Qed.

  Lemma euclid_there
    (st: state Z)
    (n m: nat)
    (NMGOOD: is_good n m)
    (NNEQM: n <> m)
    (nz: nat)
    (VARN: (st) / n => (Z.of_nat nz))
    (N1: nz >= 1)
    (mz: nat)
    (VARM: (st) / m => (Z.of_nat mz))
    (M1: mz >= 1)
    (NEQ: nz <> mz)
    (H: nz < mz)
    :
      exists (st'' : state Z) (mz'' nz'' : nat),
        ((st, [], [])) == body ==> ((st'', [], [])) /\
        (st'') / m => (Z.of_nat mz'') /\
        (st'') / n => (Z.of_nat nz'') /\ mz'' >= 1 /\ nz'' >= 1 /\ (st_lt n m NMGOOD) st'' st.
  Proof.
    remember (Z.sub (Z.of_nat mz) (Z.of_nat nz)) as subbed.
    remember (st [m <- subbed]) as st'.
    enough ((st, [], []) == body ==> (st', [], [])) as STMOD.
    { remember (state_dec st' n) as DECN.
      inversion DECN as [DECNL | [nz'' Hnz'']].
      { exfalso.
        rewrite -> Heqst' in *.
        specialize (DECNL (Z.of_nat nz)).
        enough ((st [m <- subbed]) / n => (Z.of_nat nz)).
        { intuition. }
        unfold update.
        constructor; auto. }
      remember (state_dec st' m) as DECM.
      inversion DECM as [DECML | [mz'' Hmz'']].
      { exfalso.
        specialize (DECML subbed).
        enough (st' / m => subbed).
        { intuition. }
        rewrite -> Heqst' in *.
        unfold update.
        constructor; auto. }
      remember (mz - nz) as mz'''.
      exists st', mz''', nz.
      assert (mz'' = Z.of_nat mz''').
      { subst. unfold update in *. inv Hmz''. lia. }
      assert (Z.of_nat nz = nz'').
      { subst.
        unfold update in *.
        inv Hnz''.
        remember (state_deterministic VARN H6) as DET.
        auto. }
      splits.
      all: try now subst; auto.
      { lia. }
      unfold st_lt.
      exists mz''', nz, mz, nz.
      splits.
      all: try now subst; auto.
      all: try now lia. }
    destruct NMGOOD as [NNMM | NMMN].
    all: desf.
    1: apply bs_If_False.
    3: apply bs_If_True.
    all: unfold M, N.
    all: econstructor.
    all: repeat constructor; eauto.
    all: lia.
  Qed.

  Lemma euclid_terminates st mz nz
        (VARM : st / m => (Z.of_nat mz))
        (VARN : st / n => (Z.of_nat nz))
        (M1   : mz >= 1)
        (N1   : nz >= 1) :
    exists st', (st, [], []) == euclid ==> (st', [], []).
  Proof.
    generalize dependent mz.
    generalize dependent nz.
    pattern st.
    apply well_founded_ind with (R:=(st_lt n m dflt_good)).
    { apply st_lt_well_founded. }
    clear st. intros st HH; ins.

    destruct (Nat.eq_dec nz mz) as [ |NEQ]; subst.
    { exists st. unfold euclid.
      apply bs_While_False.
      econstructor.
      1,2: now constructor; eauto.
      reflexivity. }

    enough (exists st'' mz'' nz'',
               ((st, [], [])) == body ==> ((st'', [], [])) /\
               (st'' / m => (Z.of_nat mz'')) /\
               (st'' / n => (Z.of_nat nz'')) /\
               (mz'' >= 1) /\
               (nz'' >= 1) /\
               ((st_lt n m dflt_good) st'' st)) as AA.
    { desf.
      edestruct HH with (y:=st'') as [st' BB]; eauto.
      exists st'. eapply bs_While_True; eauto.
      econstructor.
      1,2: now constructor; eauto.
      intros GG. clear -NEQ GG.
      eapply inj_neq; eauto. }
    remember (dec_lt nz mz) as nz_cmp_mz.
    inv nz_cmp_mz.
    { eapply euclid_there; eauto. unfold n, m. lia. }
    remember (dec_gt nz mz) as nz_cmp_mz'.
    inv nz_cmp_mz'.
    2: lia.
    assert (m <> n) as MNEQN.
    { unfold n, m. auto. }
    assert (mz <> nz) as MZNEQNZ.
    { lia. }
    assert (mz < nz) as MZLESSNZ.
    { lia. }
    (* with eremember after unshelve loses context :( *)
    remember (euclid_there st m n flipped_good MNEQN mz VARM M1 nz VARN N1 MZNEQNZ MZLESSNZ) as HAHA.
    des.
    exists st'', nz'', mz''.
    splits; auto.
    inv HAHA4.
    unfold st_lt.
    des.
    exists nz0, x, nz', mz'.
    splits; auto.
    lia.
  Qed.
End Euclid.
