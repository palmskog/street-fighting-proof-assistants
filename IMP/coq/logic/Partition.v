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

Import ListNotations.

Definition partition :=
(Sseq
(Sset "l" (Eval (Vint 0)))
(Sseq
(Sset "h" (Elen (Evar "a")))
(Sseq
(Sset "i" (Eval (Vint 0)))
(Sseq
(Swhile (Eop2 Olt (Evar "i") (Evar "h"))
  (Sifelse (Eop2 Olt (Eidx (Evar "a") (Evar "i")) (Evar "pivot"))
    (Sseq
    (Sset "tmp" (Eidx (Evar "a") (Evar "l")))
    (Sseq
    (Swrite "a" (Evar "l") (Eidx (Evar "a") (Evar "i")))
    (Sseq
    (Swrite "a" (Evar "i") (Evar "tmp"))
    (Sseq
    (Sset "l" (Eop2 Oadd (Evar "l") (Eval (Vint 1))))
    (Sset "i" (Eop2 Oadd (Evar "i") (Eval (Vint 1))))))))
    (Sifelse (Eop2 Oeq (Eidx (Evar "a") (Evar "i")) (Evar "pivot"))
      (Sset "i" (Eop2 Oadd (Evar "i") (Eval (Vint 1))))
      (Sseq
      (Sset "tmp" (Eidx (Evar "a") (Eop2 Osub (Evar "h") (Eval (Vint 1)))))
      (Sseq
      (Swrite "a" (Eop2 Osub (Evar "h") (Eval (Vint 1))) (Eidx (Evar "a") (Evar "i")))
      (Sseq
      (Swrite "a" (Evar "i") (Evar "tmp"))
      (Sset "h" (Eop2 Osub (Evar "h") (Eval (Vint 1))))))))))
(Sset "result" (Evar "a")))))).

Definition rotate_right {A} (l : list A) : list A :=
  match l with
  | [] => []
  | a :: l' => last l a :: removelast l
  end.

Definition rotate_left {A} (l : list A) : list A :=
  match l with
  | [] => []
  | a :: l' => l' ++ [a]
  end.

Lemma last_snoc :
  forall A (l : list A) a a0,
    last (l ++ [a]) a0 = a.
Proof.
  induction l; intros.
  - auto.
  - destruct l.
    + auto.
    + change (last ((a :: a2 :: l) ++ [a0]) a1) with (last ((a2 :: l) ++ [a0]) a1).
      auto.
Qed.

Lemma removelast_snoc :
  forall A (l : list A) a,
    removelast (l ++ [a]) = l.
Proof.
  induction l; intros.
  - auto.
  - destruct l.
    + auto.
    + change (removelast ((a :: a1 :: l) ++ [a0])) with (a :: removelast ((a1 :: l) ++ [a0])).
      auto using f_equal.
Qed.

Lemma rev_rotate_right :
  forall A (l : list A),
    rev (rotate_right l) = rotate_left (rev l).
Proof.
  unfold rotate_left, rotate_right.
  destruct l.
  - auto.
  - break_match.
    + simpl in * |-. find_apply_lem_hyp app_eq_nil. intuition discriminate.
    + pose proof @app_removelast_last A (a :: l) a. conclude_using discriminate.
      cbn [rev].
      apply f_equal with (f := @rev _) in Heql0.
      rewrite rev_involutive in *. simpl in Heql0.
      rewrite Heql0 in *.
      rewrite last_snoc.
      rewrite removelast_snoc.
      now rewrite rev_involutive.
Qed.


Fixpoint partition_list' (fuel : nat) (pivot : Z) (l : list Z) (los : list Z) (eqs : list Z) (his : list Z)
  : option (list Z * list Z * list Z) :=
  match fuel with
  | 0%nat => None
  | S n =>
  match l with
  | [] => Some (los, eqs, his)
  | z :: l => if z <? pivot
             then partition_list' n pivot l (z :: los) (rotate_right eqs) his
             else if z =? pivot
             then partition_list' n pivot l los (z :: eqs) his
             else (* z > pivot *)
                  partition_list' n pivot (rotate_right l) los eqs (z :: his)
  end end.

Lemma partition_list'_unroll :
  forall fuel pivot l los eqs his,
    partition_list' (S fuel) pivot l los eqs his =
    match l with
    | [] => Some (los, eqs, his)
    | z :: l => if z <? pivot
               then partition_list' fuel pivot l (z :: los) (rotate_right eqs) his
               else if z =? pivot
                    then partition_list' fuel pivot l los (z :: eqs) his
                    else (* z > pivot *)
                      partition_list' fuel pivot (rotate_right l) los eqs (z :: his)
    end.
Proof. reflexivity. Qed.

Lemma partition_list'_monotone :
  forall fuel' fuel pivot l los eqs his x,
    (fuel <= fuel')%nat ->
    partition_list' fuel pivot l los eqs his = Some x ->
    partition_list' fuel' pivot l los eqs his = Some x.
Proof.
  induction fuel'; intros.
  - assert (fuel = 0%nat) by omega. subst fuel. auto.
  - destruct fuel; try discriminate.
    simpl in *.
    repeat break_match; eauto with *.
Qed.

Lemma removelast_length :
  forall A (l : list A),
    List.length (removelast l) = pred (List.length l).
Proof.
  induction l; simpl.
  - auto.
  - destruct l.
    + auto.
    + cbn [Datatypes.length]. rewrite IHl. auto.
Qed.

Lemma rotate_right_length :
  forall A (l : list A),
    List.length (rotate_right l) = List.length l.
Proof.
  unfold rotate_right.
  intros.
  break_match.
  - auto.
  - cbn [Datatypes.length]. rewrite removelast_length. auto.
Qed.


Lemma partition_list'_sufficient_fuel :
  forall pivot l los eqs his,
    exists x,
      partition_list' (S (List.length l)) pivot l los eqs his = Some x.
Proof.
  intros.
  remember (S (List.length l)) as n.
  assert (S (List.length l) <= n)%nat by omega. clear Heqn.
  revert los eqs his.
  generalize dependent l.
  induction n; intros.
  - omega.
  - destruct n.
    + destruct l; simpl in *; try omega. eauto.
    + remember (S n).
      cbn [partition_list'].
      repeat break_match.
      eauto.
      eauto with *.
      eauto with *.
      apply IHn. rewrite rotate_right_length. simpl in *. omega.
Qed.

Require Import Permutation.

Lemma array_at_array_at' :
  forall a l h,
    array_at a l h ->
    array_at' (a + 1) l h.
Proof.
  unfold array_at.
  intros.
  break_match; intuition.
Qed.


Lemma partition_list'_length :
  forall n p rest los eqs his los' eqs' his',
    partition_list' n p rest los eqs his = Some (los', eqs', his') ->
    (List.length rest + List.length los + List.length eqs + List.length his =
     List.length los' + List.length eqs' + List.length his')%nat.
Proof.
  induction n; simpl; intros.
  - discriminate.
  - break_match.
    + find_inversion. auto.
    + repeat break_if.
      * apply IHn in H. simpl in *.
        rewrite rotate_right_length in *. omega.
      * apply IHn in H. simpl in *. omega.
      * apply IHn in H. simpl in *.
        rewrite rotate_right_length in *. omega.
Qed.

Lemma read_write_same :
  forall h h' a x,
    write h a x = Some h' ->
    read h' a = Some x.
Proof.
Admitted.

Lemma read_write_neq :
  forall h h' a b x,
    write h a x = Some h' ->
    a <> b ->
    read h' b = read h b.
Proof.
Admitted.

Lemma read_write_nop :
  forall h a x,
    read h a = Some x ->
    write h a x = Some h.
Admitted.

Lemma array_at'_extend_r :
  forall l h a i x,
    array_at' a l h ->
    read h i = Some (Vint x) ->
    i = a + Zlength l ->
    array_at' a (l ++ [x]) h.
Admitted.

Lemma array_at'_extend_l :
  forall l h a x,
    array_at' (a + 1) l h ->
    read h a = Some (Vint x) ->
    array_at' a (x :: l) h.
Admitted.

Lemma array_at'_write_preserve :
  forall l h h' a i x,
    array_at' a l h ->
    write h i x = Some h' ->
    ~ a <= i < a + Zlength l ->
    array_at' a l h'.
Admitted.

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

Lemma nth_last :
  forall A (l : list A) n d1 d2,
    List.length l = S n ->
    nth n l d1 = last l d2.
Proof.
  induction l; cbn [nth]; intros; destruct n.
  - simpl in *. omega.
  - simpl in *. omega.
  - destruct l; auto. simpl in *; omega.
  - destruct l; [simpl in *; omega |].
    change (last (a :: a0 :: l) d2) with (last (a0 :: l) d2).
    auto.
Qed.

Lemma array_at'_app :
  forall l1 a1 a2 l2 h,
    array_at' a1 l1 h ->
    array_at' a2 l2 h ->
    a2 = a1 + Zlength l1 ->
    array_at' a1 (l1 ++ l2) h.
Proof.
Admitted.

Lemma rotate_right_permutation :
  forall A (l : list A), Permutation l (rotate_right l).
Proof.
  unfold rotate_right.
  intros.
  break_match; auto.
  pose proof fun H => @app_removelast_last A l a H. conclude_using congruence.
  subst.
  rewrite H at 1.
  apply Permutation_sym.
  apply Permutation_cons_app.
  rewrite app_nil_r.
  auto.
Qed.

Lemma partition_list'_permutation :
  forall fuel pivot l los eqs his los' eqs' his',
    partition_list' fuel pivot l los eqs his = Some (los', eqs', his') ->
    Permutation (l ++ los ++ eqs ++ his) (los' ++ eqs' ++ his').
Proof.
  induction fuel; simpl; intros.
  - discriminate.
  - repeat break_match.
    + find_inversion. auto.
    + find_apply_hyp_hyp. eapply Permutation_trans; [|eauto].
      rewrite <- !app_ass.
      apply Permutation_app_tail.
      apply Permutation_app.
      * simpl. apply Permutation_cons_app. auto.
      * auto using rotate_right_permutation.
    + find_apply_hyp_hyp. eapply Permutation_trans; [|eauto].
      rewrite <- !app_ass.
      apply Permutation_app_tail.
      simpl.
      apply Permutation_cons_app.
      auto.
    + find_apply_hyp_hyp. eapply Permutation_trans; [|eauto].
      rewrite <- !app_ass.
      simpl.
      apply Permutation_cons_app.
      repeat apply Permutation_app_tail.
      auto using rotate_right_permutation.
Qed.

Lemma partition_list'_correct :
  forall fuel pivot l los eqs his los' eqs' his',
    partition_list' fuel pivot l los eqs his = Some (los', eqs', his') ->

    (forall z : Z, In z los -> z < pivot) ->
    (forall z : Z, In z eqs -> z = pivot) ->
    (forall z : Z, In z his -> z > pivot) ->

    (forall z : Z, In z los' -> z < pivot) /\
    (forall z : Z, In z eqs' -> z = pivot) /\
    (forall z : Z, In z his' -> z > pivot).
Proof.
  induction fuel; simpl; intros.
  - discriminate.
  - repeat break_match.
    + find_inversion. auto.
    + rewrite Z.ltb_lt in *.
      eapply IHfuel; eauto.
      * simpl. intuition.
      * eauto using Permutation_in, rotate_right_permutation, Permutation_sym.
    + rewrite Z.ltb_nlt in *.
      rewrite Z.eqb_eq in *.
      eapply IHfuel; eauto.
      simpl. intuition.
    + rewrite Z.ltb_nlt in *.
      rewrite Z.eqb_neq in *.
      eapply IHfuel; eauto.
      simpl. intuition.
Qed.


Lemma in_rev' :
  forall A (a : A) l,
    In a (rev l) ->
    In a l.
Proof.
  intros.
  now rewrite in_rev.
Qed.

Lemma partition_spec :
  forall env s h s' h' a_val pivot_val contents,
    lkup s "a" = Some (Vaddr a_val) ->
    lkup s "pivot" = Some (Vint pivot_val) ->
    array_at a_val contents h ->
    eval_s env s h partition s' h' ->
    exists los eqs his,
      let new_contents := (los ++ eqs ++ his)%list in
      array_at a_val new_contents h' /\
      Permutation contents new_contents /\
      (forall z, In z los -> z < pivot_val) /\
      (forall z, In z eqs -> z = pivot_val) /\
      (forall z, In z his -> z > pivot_val).
Proof.
  intros env s h s' h' a_val pivot_val contents Ha Hpiv Harr Heval.
  unfold partition in *.
  repeat step_forward; break_eval_expr.
  rewrite lkup_update_neq in * by discriminate.
  assert (a_val = a) by congruence. subst a.
  copy_apply array_at_read_length Harr.
  assert (l = Zlength contents) by congruence. subst l.
  eapply eval_stmt_while_elim
  with (I := fun s h =>
    exists i_val l_val h_val los eqs his rest,
      lkup s "a" = Some (Vaddr a_val) /\
      lkup s "pivot" = Some (Vint pivot_val) /\
      lkup s "i" = Some (Vint i_val) /\
      lkup s "l" = Some (Vint l_val) /\
      lkup s "h" = Some (Vint h_val) /\
      read h a_val = Some (Vint (Zlength contents)) /\
      array_at' (a_val + 1) (rev los) h /\ l_val = Zlength los /\
      array_at' (a_val + 1 + l_val) (rev eqs) h /\ i_val = l_val + Zlength eqs /\
      array_at' (a_val + 1 + i_val) rest h /\
      array_at' (a_val + 1 + h_val) his h /\ h_val = Zlength contents - Zlength his /\
      partition_list' (S (List.length rest)) pivot_val rest los eqs his =
      partition_list' (S (List.length contents)) pivot_val contents [] [] [])
    in H3.
  - (* loop invariant /\ condition false -> post condition *)
    break_and. break_exists. break_and. subst.
    break_eval_expr. find_injection.
    unfold imp_lt in *.
    find_apply_lem_hyp pred_of_dec_false_elim.
    repeat find_rewrite.
    repeat find_injection.
(* can't find los *)
(*
    assert (Zlength los + Zlength eqs + Zlength rest + Zlength his = Zlength contents).
    { destruct (partition_list'_sufficient_fuel pivot_val rest los eqs his) as [[[? ?] ?] ?].
      destruct (partition_list'_sufficient_fuel pivot_val contents [] [] []) as [[[? ?] ?] ?].
      repeat find_rewrite.
      find_inversion.
      repeat find_apply_lem_hyp partition_list'_length.
      cbn [length] in *.
      rewrite !Zlength_correct.
      zify. omega. }
    assert (Zlength rest = 0).
    { rewrite !Zlength_correct in *.
      zify. omega. }
    repeat find_rewrite.
    find_apply_lem_hyp Zlength_nil_inv.
    subst.
    cbn [length] in *.
    rewrite partition_list'_unroll with (fuel := 0%nat) in *.
    exists (rev los), (rev eqs), his.
    split; [|split].
    + red.
      find_rewrite.
      split.
      * rewrite !Zlength_correct, !app_length, !rev_length in *. f_equal. zify. omega.
      * eapply array_at'_app; [| | eauto].
        auto.
        eapply array_at'_app.
        rewrite !Zlength_correct, rev_length in *. auto.
        eauto.
        rewrite !Zlength_correct, !rev_length in *. zify. omega.
    + pose proof partition_list'_permutation _ _ _ _ _ _ _ _ _ (eq_sym H17).
      rewrite app_nil_r in *.
      eapply Permutation_trans. eauto.
      auto using Permutation_app, Permutation_rev.
    + pose proof partition_list'_correct _ _ _ _ _ _ _ _ _ (eq_sym H17).
      repeat conclude_using ltac:(simpl; intuition).
      intuition auto using in_rev'.
  - (* precondition -> loop invariant *)
    clear H3.
    exists 0, 0, (Zlength contents), [], [], [], contents.
    repeat rewrite ?lkup_update_same, ?lkup_update_neq by discriminate.
    intuition.
    + now compute.
    + now compute.
    + rewrite Z.add_0_r. auto using array_at_array_at'.
    + now compute.
    + rewrite Zlength_nil. omega.
  - (* condition true -> body preserves loop *)
    repeat match goal with
           | [ H : _ |- _ ] => clear H
           end.
    intros s0 h0 s1 h1 Hinv Hcond Hbody.
    break_exists. break_and.
    break_eval_expr.
    repeat find_rewrite.
    repeat find_injection.
    unfold imp_lt in *.
    find_apply_lem_hyp pred_of_dec_true_elim.

    assert (Zlength los + Zlength eqs + Zlength rest + Zlength his = Zlength contents).
    { destruct (partition_list'_sufficient_fuel pivot_val rest los eqs his) as [[[? ?] ?] ?].
      destruct (partition_list'_sufficient_fuel pivot_val contents [] [] []) as [[[? ?] ?] ?].
      repeat find_rewrite.
      find_inversion.
      repeat find_apply_lem_hyp partition_list'_length.
      cbn [length] in *.
      rewrite !Zlength_correct.
      zify. omega. }

    destruct rest as [|z rest].
    { exfalso. rewrite Zlength_nil in *. omega. }
    match goal with
    | [ H : array_at' _ (_ :: _) _ |- _ ] => cbn [array_at'] in H; destruct H
    end.
    rewrite Zlength_cons in *.
    rewrite partition_list'_unroll in * |-.
    repeat (step_forward; break_eval_expr).
    + (* a[i] < pivot *)
      repeat rewrite ? lkup_update_same, ? lkup_update_neq in * by discriminate.
      repeat find_rewrite.
      repeat find_injection.
      repeat find_rewrite.
      repeat find_injection.
      normalize_Z.

      match goal with
      | [ H : read ?h ?i = Some (Vint ?x), H' : read ?h ?j = Some (Vint ?y) |- _ ] =>
        assert (x = y) by congruence; subst
      end.
      repeat find_rewrite.
      unfold imp_lt in *. find_apply_lem_hyp pred_of_dec_true_elim.
      break_if; [| now rewrite Z.ltb_nlt in *].
      do 3 eexists. exists (i1 :: los), (rotate_right eqs), his, rest; intuition.
      * erewrite read_write_neq; [|eauto|].
        erewrite read_write_neq; eauto.
        all: omega.
      * destruct (Z.eq_dec (Zlength eqs) 0).
        -- (* The swap works even when i == l, but it's "for a different reason" *)
          repeat find_rewrite. rewrite Z.add_0_r in *.
           rewrite read_write_nop in * by auto.
           repeat find_injection.
           rewrite read_write_nop in * by auto.
           repeat find_injection.
           simpl.
           eapply array_at'_extend_r.
           auto.
           eauto.
           rewrite !Zlength_correct, rev_length. omega.
        -- eapply array_at'_write_preserve; [|solve[eauto]|].
           2: rewrite !Zlength_correct, rev_length in *; simpl; zify; omega.
           simpl.
           eapply array_at'_write_extend_r; eauto.
           rewrite !Zlength_correct, rev_length. omega.
      * rewrite Zlength_cons. omega.
      * rewrite rev_rotate_right.
        destruct (rev eqs) eqn:?.
        -- now compute.
        -- cbn [rotate_left].
           apply f_equal with (f := @rev _) in Heql.
           cbn [rev] in Heql.
           rewrite rev_involutive in *. subst eqs.
           match goal with
           | [ H : array_at' _ (_ :: _) _ |- _ ] => cbn [array_at'] in H; destruct H
           end.
           eapply array_at'_write_extend_r; [| |eauto].
           eapply array_at'_write_preserve.
           eapply eq_rect with (P := fun x => _ x _ _).
           all: eauto.
           omega.
           omega.
           eapply eq_rect with (P := fun x => _ x _ = _).
           eapply eq_rect with (P := fun x => _ x = _).
           eauto.

           assert (Z.succ (a3 + Zlength los) = a3 + 1 + Zlength los) by omega.
           congruence.
           rewrite !Zlength_correct, app_length, rev_length. simpl. zify. omega.
      * rewrite !Zlength_correct, rotate_right_length. omega.
      * eapply array_at'_write_preserve; eauto.
        eapply array_at'_write_preserve; eauto.
        eapply eq_rect with (P := fun x => _ x _ _).
        eauto.
        omega.
        rewrite !Zlength_correct in *. zify. omega.
        rewrite !Zlength_correct in *. zify. omega.
      * eapply array_at'_write_preserve.
        eapply array_at'_write_preserve.
        eapply eq_rect with (P := fun x => _ x _ _).
        all: eauto.
        omega.
        rewrite !Zlength_correct in *. zify. omega.
        rewrite !Zlength_correct in *. zify. omega.
    + repeat rewrite ? lkup_update_same, ? lkup_update_neq in * by discriminate.
      repeat find_rewrite.
      repeat find_injection.
      repeat find_rewrite.
      repeat find_injection.

      normalize_Z.

      unfold imp_eq in *.
      find_apply_lem_hyp pred_of_dec_true_elim.
      find_injection.
      assert (z = i2) by congruence. subst z.
      break_if.
      rewrite Z.ltb_lt in *. omega.
      break_if; [| rewrite Z.eqb_neq in *; congruence].
      do 3 eexists. exists los, (i2 :: eqs), his, rest.
      intuition eauto; normalize_Z; auto.
      * simpl. eapply array_at'_extend_r;eauto.
        rewrite !Zlength_correct, rev_length. omega.
      * rewrite Zlength_cons. omega.
    + repeat rewrite ? lkup_update_same, ? lkup_update_neq in * by discriminate.
      repeat find_rewrite.
      repeat find_injection.
      repeat find_rewrite.
      repeat find_injection.
      normalize_Z.
      repeat find_apply_lem_hyp pred_of_dec_false_elim.
      assert (z = i1) by congruence. subst z.
      break_if.
      rewrite Z.ltb_lt in *; congruence.
      break_if.
      rewrite Z.eqb_eq in *. congruence.
      do 3 eexists. exists los, eqs, (i1 :: his), (rotate_right rest).
      intuition eauto; normalize_Z.
      * erewrite read_write_neq; [|eauto|].
        erewrite read_write_neq; eauto.
        all: omega.
      * eapply array_at'_write_preserve.
        eapply array_at'_write_preserve.
        all: eauto.
        all: rewrite !Zlength_correct, rev_length in *.
        all: zify; omega.
      * eapply array_at'_write_preserve.
        eapply array_at'_write_preserve.
        all: eauto.
        all: rewrite !Zlength_correct, rev_length in *.
        all: zify; omega.
      * unfold rotate_right.
        break_match.
        -- exact I.
        -- eapply array_at'_write_extend_l.
           eapply array_at'_write_preserve.
           eapply array_at'_shrink_r.
           eapply eq_rect with (P := fun x => _ x _ _).
           eauto.
           omega.
           eauto.
           rewrite !Zlength_correct, removelast_length in *.
           simpl in *. zify. omega.
           eapply eq_rect with (P := fun x => _ x = _).
           eauto.




           pose proof fun H => array_at'_read_nth _ _ _ (Zlength l) 0 H11 H.
           rewrite !Zlength_correct in *. cbn[length] in *. conclude_using ltac:(zify; omega).
           assert
             (a4 + Z.of_nat (length los) + Z.of_nat (length eqs) + 2 + Z.of_nat (length l) =
              a4 + Z.of_nat (length contents) - Z.of_nat (length his)) by (zify; omega).
           repeat find_rewrite.
           remember (z :: l) in *.
           find_injection.
           rewrite Nat2Z.id in *.

            auto using f_equal, nth_last.
      * destruct rest as [|z rest].
        -- rewrite Zlength_nil in *.
           assert (a4 + Zlength los + Zlength eqs + 1 = a4 + Zlength contents - Zlength his)
             by omega.
           repeat find_rewrite.
           repeat find_injection.
           rewrite read_write_nop in * by auto.
           repeat find_injection.
           rewrite read_write_nop in * by auto.
           repeat find_injection.
           apply array_at'_extend_l; auto.
        -- eapply array_at'_write_preserve.
           eapply array_at'_write_extend_l.
           all: eauto.
           rewrite !Zlength_correct in *. cbn [length] in *. zify. omega.
      * rewrite !Zlength_correct in *. cbn [length] in *. zify. omega.
      * cbn [length] in *. rewrite rotate_right_length. auto.
Qed.
*)
Admitted.
