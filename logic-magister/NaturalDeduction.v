(* Natural Deduction *)
Lemma Le : forall A B C: Prop, (A \/ B -> C) <-> (A -> C) /\ (B -> C).
Proof.
  intros A B C. unfold "<->". split. (* split позволяет разделить цель на подцели *)
  - (* при помощи буллетов - + * и т.п. можно фокусироваться на подцелях *)
    intro Habc. split.
    + intro a. apply Habc. (* тактика apply позволяет применить известную теорему или гипотезу из контекста: если в цели следствие теоремы, она трансформирует цель так, что нужно доказать посылку теоремы *)
      left. (* left и right позволяют выбирать конкретный член дизъюнкции, который мы можем доказать *)
      apply a.
    + intro b. apply Habc. right. exact b.
  - intros H1 H2.
    elim H1. intros Hac Hbc. elim H2.
    + intros a. apply Hac. exact a.
    + intros b. apply Hbc. now exact b.
Qed.

Print True. (* True - тип с одним конструктором без аргументов: I *)
Print False. (* False - тип без конструкторов *)

Theorem True_can_be_proven : True.
  exact I.
Qed.

Theorem Ex_Falso : forall A, False -> A.
Proof. intros A H. elim H. Qed.

(* Отрицание в Coq реализовано как импликация в ложь. Подробнее об этом, когда на лекциях будем говорить про интуиционисткую логику. *)
Print "~".

(* Ложь - то, что никогда не может быть доказано. *)
Theorem False_cannot_be_proven__again : ~False.
Proof.
  unfold "~". (* тактика unfold позволяет раскрывать определения и синтаксический сахар *)
  intros proof_of_False.
  (* если ложь оказалась в контексте, из неё следует что угодно: с точки зрения типов у нас есть терм типа, у которого нет конструкторов! это невозможно, поэтому можно доказать что угодно. *)
  elim proof_of_False. (* тактика elim позволяет разобрать возможные случаи, какими конструкторами был построен терм. поскольку у типа False нет конструкторов, elim рассматривает 0 случаев, а поэтому доказательство завершается! *)
Qed.

Theorem double_neg : forall P : Prop, P -> ~~P.
Proof.
  intros P H G. (* синтаксический сахар для отрицания автоматически раскрывается в импликацию, когда используем intros *)
  apply G. apply H.
Qed.

(* Exercise *)
Theorem backward_huge : (forall A B C : Prop, A -> (A -> B) -> (A -> B -> C) -> C).
Proof.
    intros A B C f1 f2 f3.
    exact (f3 f1 (f2 f1)).
Qed.

(* Exercise *)
Lemma distributivity_of_disjunction_over_conjunction:
  forall A B C : Prop,
    A \/ (B /\ C) <-> (A \/ B) /\ (A \/ C).
Proof.
  intros A B C.
  split; intros H.
  { split.
    { destruct H.
      { left. exact H. }
      destruct H as [ BT CT ].
      right. exact BT. }
    destruct H.
    { left; exact H. }
    destruct H as [ BT CT ].
    right. apply CT. }
  destruct H as [ AB AC ].
  destruct AB as [A1 | B1].
  { left. assumption. }
  destruct AC.
  { left. assumption. }
  right.
  split; now assumption.
Qed.

(* Exercise *)
Lemma Curry_and_unCurry : forall P Q R : Prop, (P /\ Q -> R) <-> (P -> Q -> R).
  intros P Q R.
  split; intros H.
  { intros p q.
    remember (conj p q) as PQ.
    exact (H PQ).  }
  intros [p q].
  specialize (H p q).
  assumption.
Qed.

(* Exercise *)
Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  unfold not in *.
  intros P Q pq nq p.
  exact (nq (pq p)).
Qed.

(* Exercise *)
Theorem de_morgan_not_or : forall (P Q : Prop), ~ (P \/ Q) <-> ~P /\ ~Q.
Proof.
  intros P Q.
  unfold not in *.
  split; intros H.
  { split;
      intros PQ.
    all: assert (P \/ Q) as pq.
    1: { left. exact PQ. }
    2: { right. exact PQ. }
    all: exact (H pq). }
  intros P_or_Q.
  destruct H as [Pf Qf].
  destruct P_or_Q as [ p | q ].
  { exact (Pf p). }
  exact (Qf q).
Qed.

Ltac tauto := idtac.
Ltac tauto1 :=
  match goal with
  | [ H : ?X |- ?X ] => exact H
  | [ H : _ /\ _ |- _ ] => elim H; clear H
  | [ H : _ \/ _ |- _ ] => elim H; clear H
  | [ H : False |- _ ] => elim H; clear H
  | [ H1 : ?X -> False, H2 : ?X |- _ ] => elim (H1 H2)
  | [ |- _ <-> _ ] => split
  | [ |- _ /\ _ ] => split
  | [ |- ?X -> ?Y ] => intro
  | [ |- True ] => exact I
  | [ |- _ \/ _ ] => (left; solve [tauto]) || (right; solve [tauto])
  | [ H : _ -> ?X |- ?X ] => apply H
  end.
Ltac tauto ::= unfold not in *; repeat tauto1.

Lemma Le_again : forall A B C: Prop, (A \/ B -> C) <-> (A -> C) /\ (B -> C).
Proof. intros A B C. tauto. Qed.

(* logical laws exercises *)
Definition LEM := forall P, P \/ ~P.
Definition DNE := forall P, ~~P -> P.
Definition PEIRCE := forall P Q: Prop, ((P -> Q) -> P) -> P.
Definition IMPNOTOR := forall P Q: Prop, (P -> Q) -> ~P \/ Q.
Definition DMGNAND := forall P Q, ~(~P /\ ~Q) -> P \/ Q.

(*           LEM    DNE    PEIRCE  IMPNOTOR  DMGNAND
  LEM         -      o       o        o         o
  DNE         o      -       o        o         o
  PEIRCE      o      o       -        o         o
  IMPNOTOR    o      *       *        -         *
  DMGNAND     o      o       o        o         -
*)

Theorem IMPNOTOR_implies_LEM : IMPNOTOR -> LEM.
Proof.
    unfold IMPNOTOR, LEM. intros H P.
    assert (H0: P -> P). (* assert позволяет добавить новую гипотезу P -> P с именем H0, доказав её отдельной целью *)
    - (* здесь нужно доказать гипотезу P -> P*) tauto.
    - (* здесь P -> P уже можно использовать *) specialize (H P P H0). tauto.
Qed.

(* Exercise *)
Theorem LEM_implies_DNE : LEM -> DNE.
Proof.
  unfold LEM, DNE.
  intros lem.
  intros P nnp.
  specialize (lem P).
  unfold not in *.
  destruct lem; tauto.
Qed.

(* Exercise *)
Theorem LEM_implies_PEIRCE : LEM -> PEIRCE.
Proof.
  intros lem.
  unfold LEM, PEIRCE, DNE in *.
  intros P Q pqp.
  specialize (lem P).
  destruct lem.
  { assumption. }
  unfold not in *.
  apply pqp.
  intros p.
  exfalso.
  tauto.
Qed.

(* Exercise *)
Theorem LEM_implies_IMPNOTOR : LEM -> IMPNOTOR.
Proof.
  intros lem.
  unfold LEM, IMPNOTOR in *.
  intros P Q p_impl_q.
  specialize (lem P).
  destruct lem.
  { right. exact (p_impl_q H). }
  left. assumption.
Qed.

(* Exercise *)
Theorem LEM_implies_DMGNAND : LEM -> DMGNAND.
Proof.
  intros lem.
  unfold LEM, DMGNAND in *.
  intros P Q H.
  remember (lem P) as lemP.
  remember (lem Q) as lemQ.
  destruct lemP; tauto.
  destruct lemQ; tauto.
  assert ((P -> False) /\ (Q -> False)) as H1.
  { split; assumption. }
  specialize (H H1).
  elim H.
Qed.

(* Exercise *)
Theorem DNE_implies_LEM : DNE -> LEM.
Proof.
  intros dne.
  unfold DNE, LEM in *.
  intros P.
  assert (~~ (P \/ ~P)) as OK.
  { intros X.
    destruct (de_morgan_not_or P (~P)) as [ dem _ ].
    specialize (dem X).
    destruct dem; tauto. }
  exact (dne _ OK).
Qed.

(* Exercise *)
Theorem DNE_implies_PEIRCE : DNE -> PEIRCE.
Proof.
  intros dne.
  apply (LEM_implies_PEIRCE (DNE_implies_LEM dne)).
Qed.

(* Exercise *)
Theorem DNE_implies_IMPNOTOR : DNE -> IMPNOTOR.
Proof.
  intros dne.
  apply (LEM_implies_IMPNOTOR (DNE_implies_LEM dne)).
Qed.

(* Exercise *)
Theorem DNE_implies_DMGNAND : DNE -> DMGNAND.
Proof.
  intros dne.
  apply (LEM_implies_DMGNAND (DNE_implies_LEM dne)).
Qed.

(* Exercise *)
Theorem PEIRCE_implies_LEM : PEIRCE -> LEM.
Proof.
  intros peirce.
  unfold PEIRCE, LEM in *.
  intros P.
  assert (~(P \/ ~P) -> P \/ ~P) as OK.
  { intros n.
    right.
    unfold not in *.
    intros p.
    assert (P \/ (P -> False)) as n0.
    { left. exact p. }
    exact (n n0). }
  apply (peirce _ _) in OK.
  exact OK.
Qed.
(* Exercise *)
Theorem PEIRCE_implies_DNE : PEIRCE -> DNE.
Proof.
  intros peirce.
  apply (LEM_implies_DNE (PEIRCE_implies_LEM peirce)).
Qed.

(* Exercise *)
Theorem PEIRCE_implies_IMPNOTOR : PEIRCE -> IMPNOTOR.
Proof.
  intros peirce.
  apply (LEM_implies_IMPNOTOR (PEIRCE_implies_LEM peirce)).
Qed.

(* Exercise *)
Theorem PEIRCE_implies_DMGNAND : PEIRCE -> DMGNAND.
Proof.
  intros peirce.
  apply (LEM_implies_DMGNAND (PEIRCE_implies_LEM peirce)).
Qed.

Definition id {P : Prop} (x: P): P := x.

(* Exercise *)
Theorem IMPNOTOR_implies_DNE : IMPNOTOR -> DNE.
Proof.
  intros impnotor.
  unfold IMPNOTOR, DNE in *.
  assert LEM as lem.
  { unfold LEM.
    intros P0.
    remember (impnotor P0 P0 id) as lem.
    destruct lem; tauto. }
  apply (LEM_implies_DNE lem).
Qed.

(* Exercise *)
Theorem IMPNOTOR_implies_PEIRCE : IMPNOTOR -> PEIRCE.
Proof.
  intros imptor.
  apply (DNE_implies_PEIRCE (IMPNOTOR_implies_DNE imptor)).
Qed.

(* Exercise *)
Theorem IMPNOTOR_implies_DMGNAND : IMPNOTOR -> DMGNAND.
Proof.
  intros imptor.
  apply (DNE_implies_DMGNAND (IMPNOTOR_implies_DNE imptor)).
Qed.

(* Exercise *)
Theorem DMGNAND_implies_LEM : DMGNAND -> LEM.
Proof.
  intros dmgnand.
  unfold DMGNAND, LEM in *.
  intros P.
  apply (dmgnand P (~P)).
  unfold not.
  intros FNS.
  destruct FNS.
  tauto.
Qed.

(* Exercise *)
Theorem DMGNAND_implies_DNE : DMGNAND -> DNE.
Proof.
  intros dmgnand.
  apply (LEM_implies_DNE (DMGNAND_implies_LEM dmgnand)).
Qed.

(* Exercise *)
Theorem DMGNAND_implies_PEIRCE : DMGNAND -> PEIRCE.
Proof.
  intros dmgnand.
  apply (LEM_implies_PEIRCE (DMGNAND_implies_LEM dmgnand)).
Qed.

(* Exercise *)
Theorem DMGNAND_implies_IMPNOTOR : DMGNAND -> IMPNOTOR.
Proof.
  intros dmgnand.
  apply (LEM_implies_IMPNOTOR (DMGNAND_implies_LEM dmgnand)).
Qed.
