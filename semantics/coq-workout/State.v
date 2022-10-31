(** Based on Benjamin Pierce's "Software Foundations" *)

Require Import List.
Import ListNotations.
Require Export Arith Arith.EqNat.
Require Export Id.

From hahn Require Import HahnBase.

Lemma x_not_x {t: Type} {x: t} (eq: x <> x): False.
Proof.
  tauto.
Qed.

Section S.

  Set Implicit Arguments.

  Variable A : Type.

  Definition state := list (id * A). 

  Reserved Notation "st / x => y" (at level 0).

  Inductive st_binds : state -> id -> A -> Prop := 
    st_binds_hd : forall st id x, ((id, x) :: st) / id => x
  | st_binds_tl : forall st id x id' x', id <> id' -> st / id => x -> ((id', x')::st) / id => x
  where "st / x => y" := (st_binds st x y).

  Definition update (st : state) (id : id) (a : A) : state := (id, a) :: st.

  Notation "st [ x '<-' y ]" := (update st x y) (at level 0).

  Lemma state_deterministic (st : state) (x : id) (n m : A)
        (SN : st / x => n)
        (SM : st / x => m) :
    n = m.
  Proof.
    induction st.
    { inv SN. }
    inversion SN; subst.
    { inversion SM; subst.
     { reflexivity. }
     exfalso.
     apply (x_not_x H4). }
    inversion SM; subst.
    { exfalso. apply (x_not_x H1). }
    apply (IHst H4 H7).
  Qed.
 
  Lemma update_eq (st : state) (x : id) (n : A) :
    st [x <- n] / x => n.
  Proof.
    unfold update.
    apply st_binds_hd.
  Qed.

  Lemma update_neq (st : state) (x2 x1 : id) (n m : A)
        (NEQ : x2 <> x1) : st / x1 => m <-> st [x2 <- n] / x1 => m.
  Proof.
    unfold iff, update.
    split.
    { intros a.
      apply st_binds_tl.
      { apply ne_symm. apply NEQ. }
      apply a. }
    intros aa.
    inv aa.
  Qed.

  Lemma update_shadow (st : state) (x1 x2 : id) (n1 n2 m : A) :
    st[x2 <- n1][x2 <- n2] / x1 => m <-> st[x2 <- n2] / x1 => m.
  Proof.
    unfold iff.
    split; intros a.
    { unfold update in a.
      fold (update st x2 n1) in a.
      remember (beq_nat x1 x2) as bl.
      destruct bl; symmetry in Heqbl.
      { apply beq_nat_true in Heqbl; subst.
        unfold update in *.
        remember (state_deterministic ((st_binds_hd ((x2, n1) :: st) x2 n2)) a); subst.
        apply (st_binds_hd st x2 m). }
      apply beq_nat_false in Heqbl.
      apply ne_symm in Heqbl.
      apply update_neq; auto.
      apply update_neq in a; auto.
      apply update_neq in a; auto. }
    unfold update in *.
    remember (beq_nat x1 x2) as bl.
    destruct bl; symmetry in Heqbl.
    { apply beq_nat_true in Heqbl; subst.
      rewrite <- (state_deterministic a (st_binds_hd st x2 n2)) in *.
      apply st_binds_hd. }
    apply beq_nat_false in Heqbl.
    apply update_neq in a; auto.
    apply st_binds_tl; auto.
    apply st_binds_tl; auto.
  Qed.
  
  Lemma update_same (st : state) (x1 x2 : id) (n1 m : A)
        (SN : st / x1 => n1)
        (SM : st / x2 => m) :
    st [x1 <- n1] / x2 => m.
  Proof.
    unfold update.
    remember (beq_nat x1 x2) as bl.
    destruct bl; symmetry in Heqbl.
    { apply beq_nat_true in Heqbl; subst.
      rewrite -> (state_deterministic SN SM).
      apply st_binds_hd. }
    apply beq_nat_false in Heqbl.
    remember (st_binds_tl) as why.
    apply (why st x2 m x1 n1 (ne_symm _ _ Heqbl) SM).
  Qed.
  
  Lemma update_permute (st : state) (x1 x2 x3 : id) (n1 n2 m : A)
        (NEQ : x2 <> x1)
        (SM : st [x2 <- n1][x1 <- n2] / x3 => m) :
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof.
    remember (beq_nat x1 x3) as x1_eq_x2.
    destruct x1_eq_x2; symmetry in Heqx1_eq_x2.
    { apply beq_nat_true in Heqx1_eq_x2; subst.
      apply update_neq; auto.
      rewrite -> (state_deterministic (st_binds_hd (st [x2 <- n1]) x3 n2) SM) in *.
      unfold update.
      apply st_binds_hd. }
    apply beq_nat_false in Heqx1_eq_x2.
    
    remember (beq_nat x2 x3) as x2_eq_x3.
    destruct x2_eq_x3; symmetry in Heqx2_eq_x3.
    { apply beq_nat_true in Heqx2_eq_x3; subst.
      unfold update in *.
      remember (st_binds_tl n2 NEQ (st_binds_hd st x3 n1)) as bbb.
      rewrite -> (state_deterministic bbb SM).
      apply st_binds_hd. }
    apply beq_nat_false in Heqx2_eq_x3.
    apply update_neq; auto.
    apply update_neq; auto.
    apply update_neq in SM; auto.
    apply update_neq in SM; auto.
  Qed.
End S.
