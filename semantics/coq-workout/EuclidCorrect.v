Require Import List.
Import ListNotations.
Require Import Lia.

Require Import BinInt ZArith_dec Zorder ZArith.
Require Export Id State Expr Stmt Hoare.
Require Znumtheory.

From hahn Require Import HahnBase.

Lemma unfold_eval_var
  { m st a }
  (M : [| Var m |] st => a)
  : st / m => a.
Proof.
  inv M.
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

  Lemma euclid_correct m0 n0 :
    {{ fun st =>
         << MINIT : st / m => m0 >> /\
         << NINIT : st / n => n0 >> /\
         << MOK    : (m0 > 0)%Z >> /\
         << NOK    : (n0 > 0)%Z >>
    }} euclid {{
       fun st' => exists g,
         << GVAL : st' / m => g >> /\
         << GPOS : (g >= 0)%Z >> /\
         << GPROP : Znumtheory.Zis_gcd m0 n0 g >>
    }}.
  Proof.
    assert (exists g, Znumtheory.Zis_gcd m0 n0 g /\ (g >= 0)%Z).
    { exists (Z.gcd m0 n0).
      splits.
      { apply Znumtheory.Zgcd_is_gcd. }
      remember (Z.gcd_nonneg m0 n0).
      lia. }
    inversion H as [g gg].
    remember (fun st =>
      exists mv nv,
        << MINIT : st / m => mv >> /\
        << NINIT : st / n => nv >> /\
        << MOK    : (mv > 0)%Z >> /\
        << NOK    : (nv > 0)%Z >> /\
        << GPOS : (g >= 0)%Z >> /\
        << GPROP' : Znumtheory.Zis_gcd mv nv g >>
    ) as INV.
    eapply hoare_consequence.
    { eapply hoare_while with (P := INV).
      eapply hoare_if.
      all:
        eapply hoare_consequence with (Q' := INV);
        try (eapply hoare_assign).
      2, 4: now ins.
      1-2:
        ins; red; simpl; desf.
      1: exists (nv - mv)%Z.
      2: exists (mv - nv)%Z.
      1-2: splits.
      1, 3: repeat econstructor; eauto.
      1: exists mv, (nv - mv)%Z.
      2: exists (mv - nv)%Z, nv.
      all: splits; auto.
      1, 6: now unfold m, n; constructor; auto.
      1, 4: now apply update_eq.
      1, 3:
        inv PP1;
        rewrite <- (state_deterministic MINIT (unfold_eval_var VALA)) in *;
        rewrite <- (state_deterministic NINIT (unfold_eval_var VALB)) in *;
        clear VALA; clear VALB;
        inv PP0;
        rewrite <- (state_deterministic MINIT (unfold_eval_var VALA)) in *;
        rewrite <- (state_deterministic NINIT (unfold_eval_var VALB)) in *;
        unfold Z.eq in *;
        lia.
      1: apply Znumtheory.Zis_gcd_sym.
      2: apply Znumtheory.Zis_gcd_sym in GPROP'.
      all: eapply Znumtheory.Zis_gcd_for_euclid with (q := (-1)%Z).
      1: assert (nv - mv - -1 * mv = nv)%Z as RR; try lia.
      2: assert (mv - nv - -1 * nv = mv)%Z as RR; try lia.
      all: now rewrite -> RR; auto. }
    all: ins; desf.
    { exists m0.
      exists n0.
      splits; eauto. }
    exists mv.
    splits; eauto.
    { lia. }
    inv QQ0.
    unfold Z.eq in *; subst.
    rewrite <- (state_deterministic MINIT (unfold_eval_var VALA)) in *.
    rewrite <- (state_deterministic NINIT (unfold_eval_var VALB)) in *.
    enough (nv = g).
    { subst. auto. }
    remember (Znumtheory.Zis_gcd_refl nv) as NVR.
    remember (Znumtheory.Zis_gcd_unique _ _ _ g NVR) as OI.
    clear HeqOI.
    specialize (OI GPROP').
    lia.
  Qed.
End Euclid.
