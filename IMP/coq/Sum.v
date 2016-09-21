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
Require Import ImpInterp.
Require Import ImpInterpNock.
Require Import ImpInterpProof.
Require Import ImpInterpNockProof.
Require Import ImpVerif.
Require Import ImpSemanticsFacts.

Import ListNotations.

Definition sum_body :=
  (Sseq
  (Sset "i" (Eval (Vint 0)))
  (Sseq
  (Sset "result" (Eval (Vint 0)))
  (Swhile (Eop2 Olt (Evar "i") (Elen (Evar "a")))
    (Sseq
    (Sset "result" (Eop2 Oadd (Evar "result") (Eidx (Evar "a") (Evar "i"))))
    (Sset "i" (Eop2 Oadd (Evar "i") (Eval (Vint 1)))))))).

Definition sum_ret :=
  (Evar "result").

Definition sum_func :=
  (Func "sum" ("a" :: nil)
      sum_body
      sum_ret).

(* Carefully designed to match control flow of loop body above. *)
Fixpoint sum_Zlist (acc : Z) (l : list Z) : Z :=
  match l with
  | [] => acc
  | z :: l => sum_Zlist (acc + z) l
  end.

Lemma skipn_none :
  forall A (l : list A),
    skipn (List.length l) l = [].
Proof. induction l; simpl; auto using f_equal. Qed.

Lemma skipn_nth_error_unroll :
  forall A n (l : list A) a,
    nth_error l n = Some a ->
    skipn n l = a :: skipn (S n) l.
Proof.
  induction n; destruct l; simpl; intros; try congruence.
  erewrite IHn by eauto. destruct l; auto.
Qed.

Lemma sum_spec :
  forall env s h s' h' a_val contents,
    lkup s "a" = Some (Vaddr a_val) ->
    array_at a_val contents h ->
    eval_s env s h sum_body s' h' ->
    h = h' /\
    lkup s' "result" = Some (Vint (sum_Zlist 0 contents)).
Proof.
  intros env s h s' h' a_val contents Ha Harr Heval.
  unfold sum_body in *.
  repeat (step_forward; break_eval_expr).
  pose proof (array_at_read_length _ _ _ Harr).
  eapply eval_stmt_while_elim
  with (I := fun s h => h = h0 /\
    exists i_val acc,
      lkup s "a" = Some (Vaddr a_val) /\
      lkup s "i" = Some (Vint i_val) /\
      0 <= i_val <= Zlength contents /\
      lkup s "result" = Some (Vint acc) /\
      sum_Zlist acc (skipn (Z.to_nat i_val) contents) = sum_Zlist 0 contents)
    in H7.
  - (* loop invariant /\ false -> postcondition *)
    break_and. break_exists. break_and.
    break_eval_expr.
    repeat find_rewrite.
    repeat find_injection.
    unfold imp_lt, pred_of_dec in *. break_if; try discriminate.
    assert (i1 = Zlength contents) by omega. subst.
    rewrite Zlength_correct, Nat2Z.id, skipn_none in *.
    auto using f_equal.
  - (* precondition -> loop invariant *)
    split; auto.
    exists 0, 0.
    rewrite !lkup_update_neq by discriminate.
    rewrite !lkup_update_same.
    intuition.
    rewrite Zlength_correct. zify. auto.
  - (* condition = true -> loop body preserves invariant *)
    match goal with
    | [ H : eval_s _ _ _ _ _ _ |- _ ] => clear H
    end.
    intros.
    break_and. subst.
    break_exists. break_and.
    break_eval_expr.
    step_forward.
    step_forward.
    break_eval_expr.
    step_forward.
    break_eval_expr.
    repeat find_rewrite.
    repeat find_injection.
    break_eval_expr.
    split; auto.
    rewrite !lkup_update_neq in * by discriminate.
    rewrite !lkup_update_same in *.
    repeat find_rewrite.
    repeat find_injection.
    exists (i0 + 1), (acc + i3).
    intuition.
    + unfold imp_lt in *.
      find_apply_lem_hyp pred_of_dec_true_elim.
      omega.
    + rewrite !lkup_update_neq in * by discriminate.
      rewrite !lkup_update_same in *.
      auto.
    + rewrite Z.add_1_r.
      rewrite Z2Nat.inj_succ by auto.
      unfold imp_lt, pred_of_dec in *. break_if; try discriminate.
      find_eapply_lem_hyp  array_at_read_nth_error; eauto.
      erewrite skipn_nth_error_unroll in * by eauto.
      cbn [sum_Zlist] in *. auto.
Qed.

Lemma sum_total_spec :
  forall env s h a_val contents,
    lkup s "a" = Some (Vaddr a_val) ->
    array_at a_val contents h ->
    after env s h sum_body (fun s' h' =>
      h' = h /\
      lkup s' "result" = Some (Vint (sum_Zlist 0 contents))).
Proof.
  intros.
  unfold sum_body.

  apply after_seq.
  eapply after_set; eauto.

  apply after_seq.
  eapply after_set; eauto.

  apply after_while
  with (I := fun s0 h0 =>
             h0 = h /\
             lkup s0 "a" = Some (Vaddr a_val) /\
             exists i_val acc,
               lkup s0 "i" = Some (Vint i_val) /\
               0 <= i_val <= Zlength contents /\
               lkup s0 "result" = Some (Vint acc) /\
               sum_Zlist acc (skipn (Z.to_nat i_val) contents) = sum_Zlist 0 contents)
       (f := fun s0 =>
             match lkup s0 "i" with
             | Some (Vint i) =>
               Z.to_nat (Zlength contents - i)
             | _ => 0%nat
             end).
  - (* I -> condition safety *)
    intuition.
    break_exists. break_and.
    subst.
    eauto 10 using array_at_read_length.
  - (* precondition *)
    intuition.
    exists 0, 0.
    rewrite !lkup_update_neq by discriminate.
    rewrite !lkup_update_same.
    intuition.
    rewrite Zlength_correct.
    zify. omega.
  - (* body obligation *)
    intuition. subst.
    break_exists.
    break_and.
    break_eval_expr.
    repeat find_rewrite.
    repeat find_injection.
    unfold imp_lt in *.
    find_eapply_lem_hyp pred_of_dec_true_elim.
    apply after_seq.
    eapply after_set.
    eauto 10 using array_at_read_length, array_at_read_nth with *.

    eapply after_set.
    eauto.

    rewrite !lkup_update_neq by discriminate.
    rewrite !lkup_update_same.
    rewrite !lkup_update_neq by discriminate.
    rewrite !lkup_update_same.
    intuition.
    + do 2 eexists.
      intuition eauto.
      omega.
      omega.
      erewrite skipn_nth_error_unroll with (a := nth (Z.to_nat i1) contents 0) in *|-.
      * cbn [sum_Zlist] in *.
        etransitivity; [|eauto].
        f_equal.
        f_equal.
        zify. rewrite !Z2Nat.id by omega. omega.
      * apply nth_nth_error.
        rewrite Zlength_correct in *.
        zify.
        rewrite Z2Nat.id in * by auto.
        omega.
    + rewrite Zlength_correct in *.
      zify. rewrite !Z2Nat.id in * by omega. omega.
- (* postcondition *)
  intuition.
  break_exists. break_and. subst.
  break_eval_expr.
  repeat find_rewrite.
  repeat find_injection.
  unfold imp_lt in *.
  find_apply_lem_hyp pred_of_dec_false_elim.
  assert (i1 = Zlength contents) by omega.
  subst.
  rewrite Zlength_correct in *.
  rewrite Nat2Z.id in *.
  rewrite skipn_none in *.
  cbn [sum_Zlist] in *.
  congruence.
Qed.
