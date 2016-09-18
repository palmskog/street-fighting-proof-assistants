Require Import List.
Require Import String.
Require Import ZArith.

Open Scope list_scope.
Open Scope string_scope.
Open Scope Z_scope.

Require Import StructTactics.
Require Import ImpSyntax.
Require Import ImpCommon.
Require Import ImpEval.

Import ListNotations.

Lemma eval_stmt_while_elim :
  forall (I : store -> heap -> Prop) env s h e p s' h',
    I s h ->
    (forall s0 h0 s1 h1,
        I s0 h0 ->
        eval_e s0 h0 e (Vbool true) ->
        eval_s env s0 h0 p s1 h1 ->
        I s1 h1) ->
    eval_s env s h (Swhile e p) s' h' ->
    I s' h' /\ eval_e s' h' e (Vbool false).
Proof.
  intros.
  prep_induction H1.
  induction H1; intros; subst;
    try discriminate; find_inversion; eauto.
Qed.


Fixpoint array_at' (base : Z) (contents : list Z) (h : heap) : Prop :=
  match contents with
  | [] => True
  | z :: contents => read h base = Some (Vint z) /\ array_at' (base + 1) contents h
  end.

Lemma array_at'_read_nth_error :
  forall contents base h x i,
    array_at' base contents h ->
    0 <= i < Zlength contents ->
    read h (base + i) = Some (Vint x) ->
    nth_error contents (Z.to_nat i) = Some x.
Proof.
  induction contents; simpl; intros.
  - rewrite Zlength_nil in *. omega.
  - rewrite Zlength_cons in *. break_and.
    destruct (Z.to_nat i) eqn:?.
    + simpl. change 0%nat with (Z.to_nat 0) in Heqn.
      apply Z2Nat.inj in Heqn; try omega.
      subst i.
      rewrite Z.add_0_r in *. congruence.
    + simpl. zify.
      rewrite Z2Nat.id in * by auto.
      assert (0 < i) by omega.
      subst i.
      rewrite <- Nat2Z.id with (n := n).
      eapply IHcontents; eauto.
      * omega.
      * rewrite <- H1. f_equal. omega.
Qed.

Definition array_at (base : Z) (contents : list Z) (h : heap) : Prop :=
  match read h base with
  | None => False
  | Some l => l = Vint (Zlength contents) /\
             array_at' (base + 1) contents h
  end.

Lemma lkup_update :
  forall s x1 x2 v,
    lkup (update s x1 v) x2 = if String.string_dec x1 x2 then Some v else lkup s x2.
Proof.
  induction s; simpl; intros.
  - repeat break_if; congruence.
  - repeat (break_match; simpl in * ); try congruence.
    + rewrite IHs. break_if; congruence.
    + rewrite IHs. break_if; congruence.
Qed.

Lemma lkup_update_neq :
  forall s x1 x2 v,
    x1 <> x2 ->
    lkup (update s x1 v) x2 = lkup s x2.
Proof.
  intros.
  rewrite lkup_update.
  break_if; congruence.
Qed.

Lemma lkup_update_same :
  forall s x v,
    lkup (update s x v) x = Some v.
Proof.
  intros.
  rewrite lkup_update.
  break_if; congruence.
Qed.

Lemma array_at_read_nth_error :
  forall a contents h i x,
    array_at a contents h ->
    0 <= i < Zlength contents ->
    read h (Z.succ (a + i)) = Some (Vint x) ->
    nth_error contents (Z.to_nat i) = Some x.
Proof.
  unfold array_at.
  intros.
  break_match; intuition.
  subst v.
  eapply array_at'_read_nth_error. eauto. omega.
  rewrite <- H1. f_equal. omega.
Qed.

Ltac break_eval_expr :=
  repeat match goal with
  | [ H : eval_unop _ _ ?x |- _ ] => remember x; invc H
  | [ H : eval_binop _ _ _ ?x |- _ ] => remember x; invc H
  | [ H : eval_e _ _ (Eval _) ?x |- _ ] => remember x; invc H
  | [ H : eval_e _ _ (Evar _) ?x |- _ ] => remember x; invc H
  | [ H : eval_e _ _ (Eop1 _ _) ?x |- _ ] => remember x; invc H
  | [ H : eval_e _ _ (Eop2 _ _ _) ?x |- _ ] => remember x; invc H
  | [ H : eval_e _ _ (Eidx _ _) ?x |- _ ] => remember x; invc H
  | [ H : eval_e _ _ (Elen _) ?x |- _ ] => remember x; invc H
  end.

Ltac step_forward :=
  match goal with
  | [ H : eval_s _ _ _ Snop _ _ |- _ ] => invc H
  | [ H : eval_s _ _ _ (Sset _ _) _ _ |- _ ] => invc H
  | [ H : eval_s _ _ _ (Swrite _ _ _) _ _ |- _ ] => invc H
  | [ H : eval_s _ _ _ (Salloc _ _ _) _ _ |- _ ] => invc H
  | [ H : eval_s _ _ _ (Scall _ _ _) _ _ |- _ ] => invc H
  | [ H : eval_s _ _ _ (Sseq _ _) _ _ |- _ ] => invc H
  | [ H : eval_s _ _ _ (Sifelse _ _ _) _ _ |- _ ] => invc H
  end.

Lemma pred_of_dec_true_elim :
  forall A (B : A -> A -> Prop)
    (dec : (forall a1 a2 : A, {B a1 a2} + {~ B a1 a2})) a1 a2,
    pred_of_dec dec a1 a2 = true ->
    B a1 a2.
Proof.
  unfold pred_of_dec.
  intros.
  break_if; congruence.
Qed.

Lemma array_at_read_length :
  forall a contents h,
    array_at a contents h ->
    read h a = Some (Vint (Zlength contents)).
Proof.
  unfold array_at.
  intros.
  break_match; intuition.
  congruence.
Qed.
