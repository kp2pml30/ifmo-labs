Require Import BinNums BinPos Setoid.
Definition V := positive.

Inductive Formula : Set :=
  | Top
  | Bottom
  | Var : V -> Formula
  | Not : Formula -> Formula
  | And : Formula -> Formula -> Formula
  | Or : Formula -> Formula -> Formula.

Notation "⊤" := Top.
Notation "⊥" := Bottom.
Notation "¬" := Not (at level 35).
Infix "∧" := And (at level 40).
Infix "∨" := Or (at level 41).

Definition Implication (φ ψ : Formula) : Formula := ¬φ ∨ ψ.
Infix "→" := Implication (at level 50).

Definition Equivalence (φ ψ : Formula) : Formula := (φ → ψ) ∧ (ψ → φ).
Infix "↔" := Equivalence (at level 51).

Definition Max (φ ψ : bool) : bool :=
  match φ, ψ with
  | false, false => false
  | _, _ => true
  end.

Definition Min (φ ψ : bool) : bool :=
  match φ, ψ with
  | true, true => true
  | _, _ => false
  end.

Definition flip (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition Model := V -> bool.

Fixpoint Eval (M: Model) (φ : Formula) : bool :=
  match φ with
  | ⊤ => true
  | ⊥ => false
  | Var p => M p
  | ¬ψ => flip (Eval M ψ)
  |ψ ∨ γ => Max (Eval M ψ) (Eval M γ)
  |ψ ∧ γ => Min (Eval M ψ) (Eval M γ)
  end.

Definition Models M φ := (Eval M φ) = true.
Definition Entails φ ψ := forall M, (Models M φ) -> (Models M ψ).
Definition Tautology φ := forall M, Models M φ.
Infix "⊨" := Entails (at level 53, left associativity).
Notation "ε⊨" := Tautology.
Definition LogicEquivalence φ ψ := (φ ⊨ ψ) /\ (ψ ⊨ φ).
Infix "~" := LogicEquivalence (at level 52).

(* Используется дальше *)
Lemma MinIsTrue : forall a b : bool, Min a b = true <-> a = true /\ b = true.
Proof.
  intros a b. split.
  + intros HMin.
    destruct a, b; simpl in HMin.
    - split; intuition. (* intuition разбирает логические связки, затем применяет тактику (по умолчанию auto) *)
    - discriminate. (* эта тактика работает, когда в гипотезах равенство между синтаксически неравными термами *)
    - discriminate.
    - discriminate.
  + intros [Ha Hb]. rewrite Ha, Hb. reflexivity.
Qed.

(* Используется дальше *)
Lemma MaxIsTrue : forall a b : bool, Max a b = true <-> a = true \/ b = true.
Proof. intros a b. destruct a, b; simpl; tauto. Qed.

Theorem KickTheTires : forall a b c : Formula, ((a ∧ (b ∧ c)) ~ ((a ∧ c) ∧ (b ↔ a))).
Proof.
  intros a b c.
  unfold LogicEquivalence, Entails, Models, Equivalence, Implication. simpl.
  split.
  - intros M HMabc.
    apply MinIsTrue in HMabc as [Ha HMbc].
    apply MinIsTrue in HMbc as [Hb Hc].
    rewrite Ha, Hb, Hc. reflexivity.
  - intros M HMacba.
    apply MinIsTrue in HMacba as [Hac Hba].
    apply MinIsTrue in Hac as [Ha Hc].
    apply MinIsTrue in Hba as [_ Hb].
    apply MaxIsTrue in Hb as [Hna | Hb].
    + rewrite Ha in Hna. discriminate.
    + apply MinIsTrue. split. assumption. apply MinIsTrue. tauto.
Qed.




(* Exercise *)
Theorem Task_1a: forall φ ψ, ε⊨(φ → ψ) <-> φ ⊨ ψ.
Proof.
  intros.
  split; intros H.
  { unfold Entails.
    unfold Tautology in H.
    intuition.
    specialize (H M).
    unfold Models in H, H0.
    unfold Implication in H.
    unfold Eval in H, H0.
    rewrite -> H0 in H.
    fold Eval in H, H0.
    unfold Max in H.
    simpl in H.
    remember ((Eval M ψ)) as X.
    unfold Models.
    destruct X; intuition auto with *. }
  unfold Tautology.
  unfold Entails in H.
  intros M.
  unfold Models.
  simpl.
  specialize (H M).
  apply MaxIsTrue.
  unfold flip.
  remember ((Eval M φ)) as Emp.
  unfold Models in H.
  destruct Emp; intuition.
Qed.

(* Exercise *)
Theorem Task_3a: forall φ ψ, ε⊨ ((φ → ψ) ↔ ((¬ψ) → (¬φ))).
Proof.
  unfold Tautology, Models.
  intros.
  simpl.
  destruct ((Eval M φ));
      destruct ((Eval M ψ));
      intuition.
Qed.

Definition p := Var 1%positive.
Definition q := Var 2%positive.
Definition r := Var 3%positive.

Definition Task_3b_model : Model := fun x =>
  match x with
  | 1%positive => true
  | 2%positive => true
  | 3%positive => false
  | _ => false
  end.
(* Exercise *)
(* Скорее всего вам понадобятся какие-нибудь функции из этих двух мест:
  https://coq.inria.fr/stdlib/Coq.PArith.BinPosDef.html#Pos.eqb
  https://coq.inria.fr/stdlib/Coq.Init.Datatypes.html#lab1271
  *)
Theorem Task_3b: ~ ε⊨ ((p → (q → r)) ↔ (¬r → (¬q → ¬p))).
Proof.
  unfold not.
  intros.
  simpl in H.
  unfold Tautology in *.
  specialize (H Task_3b_model).
  unfold Models, Task_3b_model in H.
  unfold Eval in H.
  unfold p, q, r in H.
  unfold Equivalence, Implication in H.
  simpl in H.
  discriminate H.
Qed.

#[local] Hint Rewrite MinIsTrue.
#[local] Hint Rewrite MaxIsTrue.

Lemma MinIsFalse : forall a b : bool, Min a b = false <-> a = false \/ b = false.
Proof. intros a b. destruct a, b; simpl; tauto. Qed.
#[local] Hint Rewrite MinIsFalse.

Lemma MaxIsFalse : forall a b : bool, Max a b = false <-> a = false /\ b = false.
Proof. intros a b. destruct a, b; simpl; tauto. Qed.
#[local] Hint Rewrite MaxIsFalse.

Lemma MaxOfFalse : forall a : bool, Max a false = a.
Proof. intros []; reflexivity. Qed.
#[local] Hint Rewrite MaxOfFalse.

Lemma flip_flip : forall b1 b2 : bool, flip b1 = b2 <-> b1 = flip b2.
Proof. intros [] []; intuition. Qed.
#[local] Hint Rewrite flip_flip.

Ltac sintuition := simpl in *; repeat (intros; intuition; try subst; autorewrite with core in *); try congruence; eauto 1.
Ltac crush1 := fail.
Ltac crush := unfold Tautology, LogicEquivalence, Entails, Models, Equivalence, Implication in *; repeat crush1.
Ltac crush2 := idtac.
Ltac crush1 ::=
  let H' := fresh "H" in
  sintuition; match goal with
  | [ H : context [Min _ _ = true] |- _ ] => rewrite MinIsTrue in H
  | [ |- context[Min _ _ = true] ] => rewrite MinIsTrue
  | [ H : context [Min _ _ = false] |- _ ] => rewrite MinIsFalse in H
  | [ |- context[Min _ _ = false] ] => rewrite MinIsFalse
  | [ H : context [Max _ _ = true] |- _ ] => rewrite MaxIsTrue in H
  | [ |- context[Max _ _ = true] ] => rewrite MaxIsTrue
  | [ H : context [Max _ _ = false] |- _ ] => rewrite MaxIsFalse in H
  | [ |- context[Max _ _ = false] ] => rewrite MaxIsFalse
  | [ |- context[Max _ false = _] ] => rewrite MaxOfFalse
  | [ H : context[flip _ = _] |- _ ] => rewrite flip_flip in H; simpl in H
  | [ |- context[flip _ = _] ] => rewrite flip_flip; simpl
  | [ H : forall _ : ?T, _, H1 : ?T |- _ ] => specialize (H H1)
  | [ |- _] => crush2
  | [ |- _ \/ _ ] => (left; solve [crush]) || (right; solve [crush])
  end.

Section Task_4.
(* Привести следующую формулу в равносильные ННФ (формула находится в ННФ, если
в нее входят только конъюнкции, дизъюнкции и литералы), КНФ и ДНФ:
  ¬(¬(p ∧ q) → ¬r)
*)
Inductive Literal : Formula -> Prop :=
| LiteralTop : Literal ⊤
| LiteralBottom : Literal ⊥
| LiteralVar : forall v : V, Literal (Var v)
| LiteralNot : forall v : V, Literal (Not (Var v)).

(* Exercise *)
Inductive NNF : Formula -> Prop :=
  | NNF_var : forall v : V, NNF (Var v)
  | NNF_N_var : forall v : V, NNF (Not (Var v))
  | NNF_and : forall l r : Formula, forall LNNF : NNF l, forall RNNF : NNF r, NNF (And l r)
  | NNF_or : forall l r : Formula, forall LNNF : NNF l, forall RNNF : NNF r, NNF (Or l r).
Hint Constructors NNF.

Inductive Disjunct : Formula -> Prop :=
  | Disjunct_var : forall v : V, Disjunct (Var v)
  | Disjunct_not_var : forall v : V, Disjunct (Not (Var v))
  | Disjunct_or : forall l r : Formula, forall DL : Disjunct l, forall DR : Disjunct r, Disjunct (Or l r).
Hint Constructors Disjunct.

Inductive Conjunct : Formula -> Prop :=
  | Conjunct_var : forall v : V, Conjunct (Var v)
  | Conjunct_not_var : forall v : V, Conjunct (Not (Var v))
  | Conjunct_or : forall l r : Formula, forall DL : Conjunct l, forall DR : Conjunct r, Conjunct (And l r).
Hint Constructors Conjunct.

(* Exercise *)
Inductive CNF : Formula -> Prop :=
  | CNF_1 : forall f : Formula, forall OK : Disjunct f, CNF f
  | CNF_2 : forall l r : Formula, forall OKL : CNF l, forall OKR : CNF r, CNF (And l r).
Hint Constructors CNF.

(* Exercise *)
Inductive DNF : Formula -> Prop :=
  | DNF_1 : forall f : Formula, forall OK : Conjunct f, DNF f
  | DNF_2 : forall l r : Formula, forall OKL : DNF l, forall OKR : DNF r, DNF (Or l r).
Hint Constructors DNF.

(* Exercise *)
Theorem Task_4a: exists φ, NNF φ /\ ¬(¬(p ∧ q) → ¬r) ~ φ.
Proof.
  intros.
  unfold Implication.
  (*
  (¬) ((¬) ((¬) (p ∧ q)) ∨ (¬) r)
  (¬) ((¬) (¬p ∨ ¬q) ∨ ¬r)
  (¬) ((p ∧ q) ∨ ¬r)
  ¬(p ∧ q) ∧ r
  (¬p ∨ ¬q) ∧ r
  *)
  exists ((¬p ∨ ¬q) ∧ r).
  split.
  { repeat constructor. }
  unfold LogicEquivalence.
  split; unfold Entails; intros; now crush.
Qed.

(* Exercise *)
Theorem Task_4b: exists φ, CNF φ /\ ¬(¬(p ∧ q) → ¬r) ~ φ.
Proof.
  exists ((¬p ∨ ¬q) ∧ r).
  split.
  { apply CNF_2.
    { apply CNF_1.
      repeat constructor. }
    repeat constructor. }
  unfold LogicEquivalence.
  split; crush.
Qed.

(* Exercise *)
Theorem Task_4c: exists φ, DNF φ /\ ¬(¬(p ∧ q) → ¬r) ~ φ.
Proof.
  (*
  (¬p ∨ ¬q) ∧ r
  ¬p ∧ r ∨ ¬q ∧ r
  *)
  exists ((¬p ∧ r ∨ ¬q ∧ r)).
  split.
  { apply DNF_2; apply DNF_1.
    all: repeat constructor. }
  unfold LogicEquivalence.
  split; crush.
Qed.
End Task_4.



Require Import MSets.
Module LitSet := Make Z_as_OT.
Section Task_5.
Definition Lit := Z.
Definition varToLit := Zpos.
Definition notVarToLit := Zneg.

(* set functions: https://coq.inria.fr/library/Coq.MSets.MSetInterface.html *)
Fixpoint literals (φ : Formula) : LitSet.t :=
  match φ with
  | ⊤ => LitSet.empty
  | ⊥ => LitSet.empty
  | Var p => LitSet.singleton (varToLit p)
  | ¬(Var p) => LitSet.singleton (notVarToLit p)
  | ¬ _ => LitSet.empty
  |ψ ∨ γ => LitSet.union (literals ψ) (literals γ)
  |ψ ∧ γ => LitSet.union (literals ψ) (literals γ)
  end.

Definition EvalLit (M: Model) (x : Lit) : bool :=
  match x with
  | Zpos y => M y
  | Zneg y => negb (M y)
  | Z0 => false
  end.

Definition positive (I : Model) (φ : Formula) : LitSet.t :=
  LitSet.filter (EvalLit I) (literals φ).

Ltac crush3 := idtac.
Ltac crush2 ::=
  match goal with
  | [ H : context[LitSet.In _ (LitSet.singleton _)] |- _ ] => setoid_rewrite LitSet.singleton_spec in H
  | [ |- context[LitSet.In _ (LitSet.singleton _)] ] => setoid_rewrite LitSet.singleton_spec
  | [ H : forall a : LitSet.elt, _, x : LitSet.elt |- _ ] => specialize (H x)
  | [ |- context[LitSet.In _ (LitSet.filter _ _)] ] => setoid_rewrite LitSet.filter_spec
  | [ H : context[LitSet.In _ (LitSet.filter _ _)] |- _ ] => setoid_rewrite LitSet.filter_spec in H
  | [ |- LitSet.In _ (LitSet.inter _ _) ] => apply LitSet.inter_spec
  | [ H : LitSet.In _ (LitSet.inter _ _) |- _ ] => apply LitSet.inter_spec in H
  | [ |- LitSet.In _ (LitSet.union _ _) ] => apply LitSet.union_spec
  | [ H : context[LitSet.In _ LitSet.empty] |- _ ] => apply LitSet.empty_spec in H as []
  | [ H : context[LitSet.In _ (LitSet.union _ _)] |- _ ] => apply LitSet.union_spec in H as []
  | [ H : LitSet.In _ (if ?X then _ else _) |- _ ] => destruct X eqn:H'
  | [ |- LitSet.In _ (if ?X then _ else _) ] => destruct X eqn:H'
  | [ H : forall a, a = ?X /\ _ -> _ |- _ ] => specialize (H X)
  | _ => crush3
  end.

Theorem Task_5_lemma
  xx l r I I'
  (H0 : LitSet.Subset (LitSet.filter (EvalLit I) (LitSet.union (literals l) (literals r))) (LitSet.filter (EvalLit I') (LitSet.union (literals l) (literals r))))
  (H1 : Eval I l = true \/ Eval I r = true)
  (xx_ok : xx = l \/ xx = r) :
    LitSet.Subset (LitSet.filter (EvalLit I) (literals xx)) (LitSet.filter (EvalLit I') (literals xx)).
Proof.
  unfold LitSet.Subset in *.
  intros elt elt_in.
  setoid_rewrite LitSet.filter_spec.
  2: { intuition auto with *. }
  setoid_rewrite LitSet.filter_spec in elt_in.
  2: { intuition auto with *. }
  specialize (H0 elt).
  assert (LitSet.In elt (LitSet.filter (EvalLit I) (LitSet.union (literals l) (literals r)))) as HOHO.
  { setoid_rewrite LitSet.filter_spec.
    2: { intuition auto with *. }
    split.
    2: { intuition auto with *. }
    apply LitSet.union_spec.
    destruct xx_ok as [ xx_ok | xx_ok ];
      rewrite -> xx_ok in *;
      now intuition. }
  specialize (H0 HOHO).
  setoid_rewrite LitSet.filter_spec in H0.
  2: { intuition auto with *. }
  now intuition.
Qed.

(* Exercise *)
(* Пусть φ — пропозициональная формула в ННФ и пусть I — интерпретация φ. Пусть positive(I, φ) — множество литералов в φ, интерпретируемых в I истинно. Например, для формулы (¬x ∧ y) ∨ z и интерпретации I = [x → 0, y → 1, z → 0], positive(I, φ) = {¬x, y}. Доказать следующую теорему о монотонности ННФ. *)
Theorem Task_5 : forall φ I I', NNF φ -> LitSet.Subset (positive I φ) (positive I' φ) -> Models I φ -> Models I' φ.
Proof. (* Указание: использовать индукцию по утверждению, что φ в ННФ. *)
  intros.
  induction H.
  { crush.
    unfold LitSet.Subset in H0.
    specialize (H0 (varToLit v)).
    unfold positive, literals in H0.
    setoid_rewrite LitSet.filter_spec in H0; try now intuition auto with *.
    setoid_rewrite LitSet.singleton_spec in H0.
    simpl in H0.
    intuition. }
  { crush.
    unfold LitSet.Subset in H0.
    specialize (H0 (notVarToLit v)).
    unfold positive, literals in H0.
    setoid_rewrite LitSet.filter_spec in H0; try now intuition auto with *.
    crush. }
  all:
    rename r0 into r;
    unfold Models, Eval.
  { apply MinIsTrue.
    simpl.
    fold Eval.
    unfold Models, Eval in H1.
    simpl in H1.
    fold Eval in H1.
    apply MinIsTrue in H1.
    unfold positive, literals in *.
    fold literals in *.
    unfold Models in *.
    remember (Task_5_lemma l l r I I' H0).
    remember (Task_5_lemma r l r I I' H0).
    intuition. }
  apply MaxIsTrue.
  fold Eval.
  unfold Models, Eval in H1.
  simpl in H1.
  fold Eval in H1.
  apply MaxIsTrue in H1.
  unfold positive, literals in *.
  fold literals in *.
  unfold Models in *.
  remember (Task_5_lemma l l r I I' H0).
  remember (Task_5_lemma r l r I I' H0).
  intuition.
Qed.
End Task_5.


Section Task_6.
Require Import Vector.
Definition Vars n := t V n.
Definition Bools n := t bool n.
Definition BooleanFunction n := Bools n -> bool.

Definition Specialize {n} (f : BooleanFunction (S n)) (b : bool) : BooleanFunction n :=
  fun ps => f (cons bool b n ps).

Inductive AllVarsAreLessThanN (n : BinPos.positive) : Formula -> Prop :=
  | AllVarsTop : AllVarsAreLessThanN n ⊤
  | AllVarsBottom : AllVarsAreLessThanN n ⊥
  | AllVarsVar : forall (v : V), Pos.lt v n -> AllVarsAreLessThanN n (Var v)
  | AllVarsNot : forall (ψ : Formula),
    AllVarsAreLessThanN n ψ -> AllVarsAreLessThanN n (¬ ψ)
  | AllVarsConj : forall (ψ γ : Formula),
    AllVarsAreLessThanN n ψ -> AllVarsAreLessThanN n γ -> AllVarsAreLessThanN n (ψ ∧ γ)
  | AllVarsDisj : forall (ψ γ : Formula),
      AllVarsAreLessThanN n ψ -> AllVarsAreLessThanN n γ -> AllVarsAreLessThanN n (ψ ∨ γ).

Fixpoint init (n : nat) : Vars n:=
  match n with
  | S n' => cons _ (Pos.of_nat n) n' (init n')
  | Z => nil _
  end.

Definition emptyIsAlwaysNil {A : Type} (a: t A 0) : a = nil A :=
  match a with nil _ => eq_refl end.

Lemma if_true_false : forall b : bool, (if b then true else false) = b.
Proof. intros []; reflexivity. Qed.

Ltac crush3 := idtac.
Ltac crush2 ::=
  let H' := fresh "H" in
  match goal with
  | [ ps : t _ 0 |- _ ] => pose (H' := emptyIsAlwaysNil ps); subst ps
  | [ |- (exists (ps : t ?V 0), _) ] => exists (nil V)
  | [ |- AllVarsAreLessThanN _ _ ] => constructor
  | [ |- context[if _ then true else false] ] => rewrite if_true_false
  | [ H : (?X < ?Y)%positive |- (?X < Pos.succ ?Y)%positive ] => auto using Pos.lt_lt_succ
  | [ |- (?X < Pos.succ ?X)%positive ] => apply Pos.lt_succ_diag_r
  | _ => crush3
  end.

Arguments Pos.of_nat: simpl nomatch.

Theorem lt_ind
  (P : nat -> Prop)
  (POK : P 0)
  (ind: forall x y, x < y -> P x -> P y)
  : forall n, P n.
Proof.
  intros.
  induction n; auto.
  specialize (ind n (S n)).
  intuition.
Qed.

(* Exercise *)
(* Функции f : B^n → B называются булевыми от n аргументов. Докажите теорему о представимости булевых функций: каждая булева функция представима некоторой формулой логики высказываний. *)
Theorem Task_6 :
  forall (n : nat) (f : BooleanFunction n),
  exists (φ : Formula),
  AllVarsAreLessThanN (Pos.of_succ_nat n) φ /\
    forall (M : Model), Eval M φ = f (map M (init n)).
Proof.
  (* we need to find f value for each model and build CNF or whatever *)
  apply (lt_ind (fun (n : nat) => forall (f : BooleanFunction n), exists φ : Formula, AllVarsAreLessThanN (Pos.of_succ_nat n) φ /\ (forall M : Model, Eval M φ = f (map M (init n))))).
  { intros.
    simpl.
    destruct (f (nil bool)).
    1: exists Top.
    2: exists Bottom.
    all: split; intuition; constructor. }
  intros.
  eexists.
Admitted.
End Task_6.
