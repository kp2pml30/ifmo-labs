Inductive bool : Type :=
  | true
  | false.

(* Check позволяет проверить тип *)
Check false.

(* Definition позволяет давать имена выражениям, например, определять функции *)
Definition negb (b:bool) : bool :=
  match b with (* сопоставление с образцом *)
  | true => false
  | false => true
  end.

(* Compute позволяет вычислять *)
Compute (negb (negb (negb false))).
Check negb.
(* Print выведет определение *)
Print negb.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

(* Notation позволяет определять свои нотации *)
Notation "x && y" := (andb x y).
Compute (false && true && true).

(* Inductive позволяет определять индуктивные типы (обобщение АТД из Хаскеля) *)
Inductive nat : Type :=
  | O
  | S (x : nat).

Definition one := S O.
Definition two := S one.

(* Для лямбда функций есть свой синтаксис *)
Definition plus2 : nat -> nat := fun x => S (S x).
Check plus2.
Compute (plus2 two).

(* Definition не допускает рекурсии. Fixpoint позволяет определять завершающиеся рекурсивные функции. *)
Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Compute (even (plus2 one)).
Compute (even (plus2 two)).

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.
Notation "x + y" := (plus x y).

Compute (two + two).

(* Exercise: напишите функцию умножения двух чисел *)
Fixpoint mult (n : nat) (m : nat) : nat :=
  match n with
  | O => O
  | S x => m + mult (x) m
  end.
Notation "x * y" := (mult x y).

Definition six := two + two + two.

Theorem check_mul : mult two six = six + six.
Proof.
  reflexivity.
Qed.

(* Exercise: напишите функцию факториала *)
Fixpoint factor (n : nat) : nat :=
  match n with
  | O => S O
  | S x => n * factor x
  end.

Theorem check_factor : factor (two + S O) = six.
Proof.
  reflexivity.
Qed.

(* Exercise: напишите функцию возведения в степень *)
Fixpoint power (n : nat) (p : nat) : nat :=
  match p with
  | O => S O (* pow 0 0 is what? *)
  | S p' => n * power n p'
  end.
Notation "x ^ y" := (power x y).

Theorem check_power : two ^ six = (six * two * two + six + two) * two.
Proof.
  reflexivity.
Qed.

(* Можно сопоставлять с образцом сразу несколько переменных *)
Fixpoint eqb (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | S n', S m' => eqb n' m'
  | _, _ => false
  end.
Notation "x == y" := (eqb x y) (at level 55).

Compute (two + two == plus2 two).

(* Первая теорема. Объявляются командами Theorem, Lemma, Example и т.д. (всё синонимы). *)
Theorem plus_O_n : forall n : nat, n = O + n.
Proof.
  intros n. (* "пусть есть число n" *)
  simpl. (* O + n можно частично вычислить, раскрыв определение "+" *)
  reflexivity.
Qed.

(* Exercise: замените Admitted на доказательство *)
Example mult_0_l : forall n:nat, O = O * n.
Proof.
  intros n.
  unfold mult. (* optional actually *)
  reflexivity.
Qed.

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.
Proof.
  intros n m.
  intros H. (* допустим, n = m (назовём гипотезу H) *)
  rewrite -> H. (* раз знаем, что n = m, можно всюду n заменить на m *)
  reflexivity.
Qed.

(* Exercise: замените Admitted на доказательство *)
Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o n_eq_m m_eq_o.
  rewrite -> n_eq_m.
  rewrite -> m_eq_o.
  reflexivity.
Qed.

Theorem plus_n_0_m_0 : forall p q : nat,
  (O + p) + (O + q) = p + q.
Proof.
  intros p q. (* что-то похожее уже доказывали, как переиспользовать? *)
  Check plus_O_n.
  rewrite <- plus_O_n. (* переписываем при помощи известной теоремы *)
  rewrite <- plus_O_n.
  reflexivity.
Qed.

Theorem plus_1_neq_0 : forall n : nat, (n + one == O) = false.
Proof.
  intros n. simpl. (* 1 справа, ничего не упрощается *)
  destruct n as [| n'] eqn:E. (* тактика для разбора случаев *)
  - unfold "+". (* unfold раскрывает и упрощает *)
    reflexivity.
  - unfold "+". fold plus. (* fold сворачивает определение *)
    unfold "==". reflexivity.
Qed.

(* Exercise: замените Admitted на доказательство *)
Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b.
  unfold negb.
  destruct b.
  all: now reflexivity.
Qed.

(* Exercise: замените Admitted на доказательство *)
Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct b.
  { unfold andb in H.
    apply H. }
  inversion H. (* contradiction *)
Qed.

Theorem add_0_r : forall n:nat,
  n + O = n.
Proof.
  induction n.
  { unfold plus. reflexivity. }
  assert (S n + O = S (n + O)) as H.
  { unfold plus.
    fold plus.
    reflexivity. }
  rewrite -> H.
  rewrite -> IHn.
  reflexivity.
Qed.

Theorem add_0_l (n : nat):
  O + n = n.
Proof.
  unfold plus.
  reflexivity.
Qed.

(* Exercise *)
Theorem mul_0_r : forall n:nat,
  n * O = O.
Proof.
  induction n.
  { unfold mult.
    reflexivity. }
  unfold mult.
  rewrite -> (add_0_l _).
  fold mult.
  assumption.
Qed.

Theorem SDistr (x: nat) (y: nat): S (x + y) = S x + y.
Proof.
  unfold plus.
  fold plus.
  reflexivity.
Qed.

(* Exercise *)
Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.

  induction n.
  { assert (forall x, O + x = x) as add_0_l.
    { unfold plus. reflexivity. }
    rewrite -> (add_0_l m).
    rewrite -> (add_0_l (S m)).
    reflexivity. }
  rewrite <- (SDistr n m).
  rewrite -> IHn.
  rewrite <- (SDistr n (S m)).
  reflexivity.
Qed.

(* Exercise *)
Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n.
  { rewrite -> add_0_r.
    unfold plus.
    reflexivity. }
  rewrite <- (plus_n_Sm m n).
  unfold plus.
  fold plus.
  rewrite -> IHn.
  reflexivity.
Qed.

(* Exercise *)
Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n.
  { assert (forall y, O + y = y) as add_0_l.
    { now auto. } (* already proofed somewhere *)
    repeat rewrite -> (add_0_l _).
    reflexivity. }
  repeat rewrite <- (SDistr _).
  rewrite -> IHn.
  reflexivity.
Qed.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Notation "x :: l" := (cons x l)
                      (at level 60, right associativity).
Notation "[ ]" := nil.

Fixpoint length (l : natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

(* Exercise: напишите функцию, которая возвращает список из count элементов, каждый из которых n *)
Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => []
  | S x => n :: (repeat n x)
  end.

Theorem check_repeat: repeat one two = one :: one :: [].
Proof.
  reflexivity.
Qed.

(* Exercise *)
Theorem length_of_repeat : forall (n count : nat), length (repeat n count) = count.
Proof.
  intros n count.
  induction count.
  { unfold repeat. unfold length. reflexivity. }
  unfold repeat. fold repeat.
  unfold length. fold length.
  rewrite -> IHcount.
  reflexivity.
Qed.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y).

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| x l1 IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil    => nil
  | h :: t => rev t ++ h :: []
  end.

(* Используется дальше *)
Lemma app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons *)
    simpl. rewrite -> IHl1'. reflexivity.
Qed.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - simpl. rewrite <- IHl'.
    (* stuck *)
    rewrite -> app_length.
    simpl.
    rewrite add_comm. reflexivity.
Qed.

Fixpoint map (f : nat -> nat) (xs : natlist) : natlist :=
  match xs with
  | [] => []
  | x :: xs' => f x :: map f xs'
  end.

Theorem map_compose : forall f g xs, map f (map g xs) = map (fun x => f (g x)) xs.
Proof.
  intros f g xs. induction xs as [| x xs IH].
  - reflexivity.
  - simpl. rewrite <- IH. reflexivity.
Qed.

(* Exercise: напишите функцию фильтрации по предикату *)
Fixpoint filter (p : nat -> bool) (xs : natlist) : natlist :=
  match xs with
  | [ ] => []
  | x :: xs' =>
    let rest := filter p xs' in
    if p x
    then x :: rest
    else rest
  end.

(* Exercise *)
Theorem filter_map : forall f p xs,
  filter p (map f xs) = map f (filter (fun x => p (f x)) xs).
Proof.
  intros f p xs.
  induction xs.
  { unfold map.
    unfold filter.
    reflexivity. }
  assert (map f (n :: xs) = f n :: map f xs) as MapSmth.
  { shelve. }
  rewrite -> MapSmth.
  unfold filter.
  fold filter.
  rewrite -> IHxs.
  remember (p (f n)) as pfn.
  destruct pfn.
  { unfold map. fold map.
    reflexivity. }
  reflexivity.
Unshelve.
  unfold map.
  fold map.
  reflexivity.
Qed.
