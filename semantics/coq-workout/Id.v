Require Import Arith Arith.EqNat.
Require Import Lia.

Definition id := nat.

Lemma lt_eq_lt_id_dec (id1 id2 : id) :
  {id1 < id2} + {id1 = id2} + {id2 < id1}.
Proof.
  induction id1.
  { left. destruct id2.
    { tauto. }
    left.
    lia. }
  destruct IHid1 as [[g|g]|g].
  { left.
    remember (beq_nat (S id1) id2) as eq.
    destruct eq; symmetry in Heqeq.
    { apply (beq_nat_true (S id1) id2) in Heqeq; subst.
      tauto. }
    apply (beq_nat_false (S id1) id2) in Heqeq; subst.
    left.
    lia.
  }
  { right. lia. }
  right.
  lia.
Qed.

Lemma gt_eq_gt_id_dec (id1 id2 : id):
  {id1 > id2} + {id1 = id2} + {id2 > id1}.
Proof.
  unfold gt.
  destruct (lt_eq_lt_id_dec id2 id1) as [[t|s]|t]; auto.
Qed.

Lemma le_is_or {id1 id2: id} (l: id1 <= id2):
  {id1 < id2} + {id1 = id2}.
Proof.
  remember (beq_nat id1 id2) as eq.
  destruct eq; symmetry in Heqeq.
  { apply (beq_nat_true _ _) in Heqeq; subst.
    tauto. }
  apply (beq_nat_false _ _) in Heqeq; subst.
  left.
  lia.
Qed.

Lemma le_gt_id_dec (id1 id2 : id): {id1 <= id2} + {id1 > id2}.
Proof.
  destruct (lt_eq_lt_id_dec id2 id1) as [[t|s]|t]; auto.
  1,2 : left; lia.
Qed.

Lemma id_eq_dec (id1 id2 : id): {id1 = id2} + {id1 <> id2}.
Proof.
  remember (beq_nat id1 id2) as eq.
  destruct eq; symmetry in Heqeq.
  { apply (beq_nat_true _ _) in Heqeq; subst.  tauto. }
  apply (beq_nat_false _ _) in Heqeq; subst.
  tauto.
Qed.

Lemma eq_id {T} x (p q:T):
  (if id_eq_dec x x then p else q) = p.
Proof.
  remember (id_eq_dec x x) as eq.
  destruct eq; congruence.
Qed.

Lemma neq_id {T} x y (p q:T) (NEQ: x <> y):
  (if id_eq_dec x y then p else q) = q.
Proof.
  remember (id_eq_dec x y) as eq.
  destruct eq.
  { tauto. }
  reflexivity.
Qed.

Lemma lt_gt_id_false (id1 id2 : id)
      (GT : id1 > id2) (GT': id2 > id1):
  False.
Proof.
  lia.
Qed.

Lemma le_gt_id_false (id1 id2 : id)
      (LE : id2 <= id1) (GT : id2 > id1) :
  False.
Proof.
  lia.
Qed.

Lemma le_lt_eq_id_dec (id1 id2 : id) (LE : id1 <= id2):
  {id1 = id2} + {id2 > id1}.
Proof.
  remember (le_is_or LE) as aa.
  auto.
Qed.

Lemma neq_lt_gt_id_dec (id1 id2 : id) (NEQ : id1 <> id2):
    {id1 > id2} + {id2 > id1}.
Proof.
  induction id1.
  { right. lia. }
  remember (id_eq_dec id1 id2) as eq.
  destruct eq.
  { subst. auto. }
  remember (IHid1 n) as aaa.
  destruct aaa.
  { left. auto. }
  right.
  lia.
Qed.
    
Lemma eq_gt_id_false (id1 id2 : id)
      (EQ : id1 = id2) (GT : id1 > id2) :
  False.
Proof.
  lia.
Qed.

Lemma ne_symm (id1 id2 : id) (NEQ : id1 <> id2) : id2 <> id1.
Proof.
  unfold not in *.
  intros a.
  symmetry in a.
  apply (NEQ a).
Qed.
