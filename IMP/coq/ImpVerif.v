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
Require Import ImpSemanticsFacts.

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

Lemma read_write_same :
  forall h h' a x,
    write h a x = Some h' ->
    read h' a = Some x.
Proof.
  induction h; simpl; intros.
  - discriminate.
  - repeat break_match; repeat find_inversion; auto; try congruence.
    all: cbn [read]; auto.
Qed.

Lemma read_write_neq :
  forall h h' a b x,
    write h a x = Some h' ->
    a <> b ->
    read h' b = read h b.
Proof.
  induction h; simpl; intros.
  - discriminate.
  - repeat break_match; repeat find_inversion; try congruence.
    all: cbn[read]; eauto.
    all: eapply IHh; eauto; omega.
Qed.

Lemma read_write_nop :
  forall h a x,
    read h a = Some x ->
    write h a x = Some h.
Proof.
  induction h; simpl; intros.
  - discriminate.
  - destruct a0.
    + solve_by_inversion.
    + rewrite IHh; auto.
    + rewrite IHh; auto.
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

Lemma array_at_array_at' :
  forall a l h,
    array_at a l h ->
    array_at' (a + 1) l h.
Proof.
  unfold array_at.
  intros.
  break_match; intuition.
Qed.

Lemma array_at'_extend_r :
  forall l h a i x,
    array_at' a l h ->
    read h i = Some (Vint x) ->
    i = a + Zlength l ->
    array_at' a (l ++ [x]) h.
Proof.
  induction l; intros.
  - rewrite Zlength_correct in *.
    simpl in *.
    intuition.
    assert (i = a) by omega.
    subst a.
    auto.
  - rewrite Zlength_correct in *.
    simpl in *. intuition.
    eapply IHl; eauto.
    zify. omega.
Qed.


Lemma array_at'_extend_l :
  forall l h a x,
    array_at' (a + 1) l h ->
    read h a = Some (Vint x) ->
    array_at' a (x :: l) h.
Proof.
  intros.
  simpl.
  intuition.
Qed.

Lemma array_at'_write_preserve :
  forall l h h' a i x,
    array_at' a l h ->
    write h i x = Some h' ->
    ~ a <= i < a + Zlength l ->
    array_at' a l h'.
Proof.
  induction l; intros.
  - simpl. auto.
  - cbn [array_at'] in *. break_and.
    rewrite Zlength_correct in *.
    cbn [Datatypes.length] in *.
    split.
    + erewrite read_write_neq; eauto.
      zify. omega.
    + eapply IHl; eauto.
      zify. omega.
Qed.

Lemma array_at'_write_extend_r :
  forall l h h' a i x,
    array_at' a l h ->
    write h i (Vint x) = Some h' ->
    i = a + Zlength l ->
    array_at' a (l ++ [x]) h'.
Proof.
  intros.
  eapply array_at'_extend_r.
  eapply array_at'_write_preserve.
  eauto.
  eauto.
  omega.
  erewrite read_write_same; eauto.
  auto.
Qed.


Lemma array_at'_write_extend_l :
  forall l h h' a x,
    array_at' (a + 1) l h ->
    write h a (Vint x) = Some h' ->
    array_at' a (x :: l) h'.
Proof.
  intros.
  eapply array_at'_extend_l.
  eapply array_at'_write_preserve.
  eauto.
  eauto.
  omega.
  erewrite read_write_same; eauto.
Qed.

Lemma array_at'_shrink_r :
  forall l a h,
    array_at' a l h ->
    array_at' a (removelast l) h.
Proof.
  induction l; simpl; repeat break_match; intuition.
  cbn [array_at']. intuition.
Qed.

Lemma array_at'_read_nth :
  forall contents base h i d,
    array_at' base contents h ->
    0 <= i < Zlength contents ->
    read h (base + i) = Some (Vint (nth (Z.to_nat i) contents d)).
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
      replace (base + Z.succ (Z.of_nat n)) with ((base + 1) + Z.of_nat n) by omega.
      erewrite IHcontents; eauto; try omega.
      rewrite !Nat2Z.id. eauto.
Qed.

Lemma array_at'_app :
  forall l1 a1 a2 l2 h,
    array_at' a1 l1 h ->
    array_at' a2 l2 h ->
    a2 = a1 + Zlength l1 ->
    array_at' a1 (l1 ++ l2) h.
Proof.
  induction l1; simpl; intuition.
  - rewrite Zlength_nil in *.
    assert (a2 = a1) by omega.
    subst a1.
    auto.
  - rewrite Zlength_correct in *.
    cbn [Datatypes.length] in *.
    eapply IHl1; eauto.
    zify. omega.
Qed.


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


Hint Constructors eval_e.
Hint Constructors eval_binop.
Hint Extern 3 (lkup (update _ _ _) _ = _) => rewrite lkup_update_neq by discriminate.

Ltac break_eval_expr :=
  repeat match goal with
  | [ H : eval_unop _ _ ?x |- _ ] => remember x; invc H; [idtac]
  | [ H : eval_binop ?op _ _ ?x |- _ ] => remember x; invc H; [idtac]
  | [ H : eval_e _ _ (Eval _) ?x |- _ ] => remember x; invc H; [idtac]
  | [ H : eval_e _ _ (Evar _) ?x |- _ ] => remember x; invc H; [idtac]
  | [ H : eval_e _ _ (Eop1 _ _) ?x |- _ ] => remember x; invc H; [idtac]
  | [ H : eval_e _ _ (Eop2 _ _ _) ?x |- _ ] => remember x; invc H; [idtac]
  | [ H : eval_e _ _ (Eidx _ _) ?x |- _ ] => remember x; invc H; [idtac]
  | [ H : eval_e _ _ (Eidx ?a ?b) _ |- _ ] =>
    eapply eval_e_idx_a_inv with (e1 := a) (e2 := b) in H; eauto; [idtac]
  | [ H : eval_e _ _ (Elen _) ?x |- _ ] => remember x; invc H; [idtac]
  | [ H : eval_e _ _ (Elen _) ?x |- _ ] =>
    eapply eval_e_len_a_inv in H; eauto using array_at_read_length; [idtac]
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

Lemma pred_of_dec_false_elim :
  forall A (B : A -> A -> Prop)
    (dec : (forall a1 a2 : A, {B a1 a2} + {~ B a1 a2})) a1 a2,
    pred_of_dec dec a1 a2 = false ->
    ~ B a1 a2.
Proof.
  unfold pred_of_dec.
  intros.
  break_if; congruence.
Qed.

Ltac normalize_Z :=
      repeat rewrite !Z.add_assoc in *;
      repeat
        match goal with
        | [ H : array_at' ?x _ _ |- _ ] => revert H
        | [ H : read _ ?x = _  |- _ ] => revert H
        | [ H : write _ ?x _ = _  |- _ ] => revert H
        end;
      repeat (match goal with
        | [ |- array_at' ?x _ _ -> _ ] => ring_simplify x
        | [ |- read _ ?x = _ -> _ ] => ring_simplify x
        | [ |- write _ ?x _ = _ -> _ ] => ring_simplify x
        end; intro);
      repeat match goal with
      | [ |- array_at' ?x _ _ ] => ring_simplify x
      end;
      repeat match goal with
      | [ |- read _ ?x = _ ] => ring_simplify x
      end;
      repeat match goal with
      | [ |- write _ ?x _ = _ ] => ring_simplify x
      end.

Definition after env s h p (Q : store -> heap -> Prop) : Prop :=
  exists s' h',
    eval_s env s h p s' h' /\ Q s' h'.

Lemma after_seq :
  forall env s h p1 p2 Q,
    after env s h p1 (fun s' h' => after env s' h' p2 Q) ->
    after env s h (Sseq p1 p2) Q.
Proof.
  unfold after.
  intros.
  break_exists.
  break_and.
  break_exists.
  break_and.
  eauto using eval_seq.
Qed.

Lemma after_set :
  forall env s h x e v (Q : store -> heap -> Prop),
    eval_e s h e v ->
    Q (update s x v) h ->
    after env s h (Sset x e) Q.
Proof.
  unfold after.
  intros.
  eauto using eval_set.
Qed.

Lemma eval_stmt_while_intro :
  forall (I : store -> heap -> Prop) (f : store -> nat) env s h e p,
    I s h ->
    (forall s0 h0,
        I s0 h0 ->
        exists b,
          eval_e s0 h0 e (Vbool b)) ->
    (forall s0 h0,
        I s0 h0 ->
        eval_e s0 h0 e (Vbool true) ->
        exists s1 h1,
          eval_s env s0 h0 p s1 h1 /\
          I s1 h1 /\
          (f s1 < f s0)%nat) ->
    exists s' h',
      eval_s env s h (Swhile e p) s' h' /\
      I s' h' /\
      eval_e s' h' e (Vbool false).
Proof.
  intros.
  assert (forall n s h, (f s < n)%nat -> I s h ->
                   exists s1 h1,
                     eval_s env s h (Swhile e p) s1 h1 /\
                     I s1 h1 /\
                     eval_e s1 h1 e (Vbool false) /\
                     (f s1 <= f s)%nat).
  {
    induction n; intros.
    - omega.
    - copy_apply H0 H3.
      break_exists.
      destruct b.
      + copy_eapply H1 H4; eauto.
        break_exists. break_and.
        eapply IHn in H6; [|omega].
        break_exists_exists.
        intuition.
        eauto using eval_while_t.
      + eauto 10 using eval_while_f.
  }

  apply H2 with (n := S (f s)) in H; [|omega].
  break_exists_exists.
  intuition.
Qed.

Lemma after_while :
  forall env s h e p (I Q : store -> heap -> Prop) (f : store -> nat),
    (forall s0 h0, I s0 h0 -> exists b, eval_e s0 h0 e (Vbool b)) ->
    I s h ->
    (forall s0 h0, I s0 h0 -> eval_e s0 h0 e (Vbool true) ->
              after env s0 h0 p (fun s1 h1 => I s1 h1 /\ (f s1 < f s0)%nat)) ->
    (forall s0 h0, I s0 h0 -> eval_e s0 h0 e (Vbool false) -> Q s0 h0) ->
    after env s h (Swhile e p) Q.
Proof.
  unfold after.
  intros.
  pose proof eval_stmt_while_intro I f env s h e p.
  repeat concludes.
  firstorder.
Qed.

Lemma nth_error_nth :
  forall A (l : list A) n x d,
    nth_error l n = Some x ->
    nth n l d = x.
Proof.
  induction l; destruct n; simpl; intros; try discriminate.
  - congruence.
  - eauto.
Qed.

Lemma nth_nth_error :
  forall A (l : list A) n d,
    (0 <= n < Datatypes.length l)%nat ->
    nth_error l n = Some (nth n l d).
Proof.
  induction l; destruct n; simpl; intros.
  - omega.
  - omega.
  - auto.
  - apply IHl. omega.
Qed.

Lemma array_at'_nth_error_read :
  forall contents base h x i,
    array_at' base contents h ->
    0 <= i < Zlength contents ->
    nth_error contents (Z.to_nat i) = Some x ->
    read h (base + i) = Some (Vint x).
Proof.
  induction contents; simpl; intros.
  - rewrite Zlength_nil in *. omega.
  - break_and.
    generalize dependent i.
    refine (natlike_ind _ _ _); intros.
    + simpl in *. find_inversion. rewrite Z.add_0_r. auto.
    + rewrite Z2Nat.inj_succ in * by auto.
      simpl in *.
      rewrite <- Z.add_succ_comm.
      apply IHcontents; auto.
      rewrite Zlength_cons in *. omega.
Qed.

Lemma array_at'_nth_read :
  forall contents base h i,
    array_at' base contents h ->
    0 <= i < Zlength contents ->
    read h (base + i) = Some (Vint (nth (Z.to_nat i) contents 0)).
Proof.
  intros.
  assert (exists x, nth_error contents (Z.to_nat i) = Some x).
  {
    destruct (nth_error contents (Z.to_nat i)) eqn:?; eauto.
    exfalso.
    find_apply_lem_hyp nth_error_None.
    rewrite Zlength_correct in *.
    zify. rewrite Z2Nat.id in * by omega. omega. }
  break_exists.
  eapply array_at'_nth_error_read; eauto.
  erewrite nth_error_nth; eauto.
Qed.

Lemma array_at_read_nth :
  forall contents base h i,
    array_at base contents h ->
    0 <= i < Zlength contents ->
    read h (Z.succ (base + i)) = Some (Vint (nth (Z.to_nat i) contents 0)).
Proof.
  intros.
  rewrite <- Z.add_succ_l.
  eapply array_at'_nth_read.
  eauto using array_at_array_at'.
  auto.
Qed.


