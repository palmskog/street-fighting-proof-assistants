Require Import Common.

Module MyList.
  Inductive list (A : Type) : Type :=
  | nil : list A
  | cons : A -> list A -> list A.
  Arguments nil {_}.


  Notation "[ ]" := nil (format "[ ]").
  Notation "x :: xs" := (cons x xs).
  Notation "[ x ]" := (cons x nil).
  Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..)).

  Fixpoint app A (xs ys : list A) : list A :=
    match xs with
    | [] => ys
    | x :: xs => x :: app xs ys
    end.

  Notation "xs ++ ys" := (app xs ys) (right associativity, at level 60).

  Lemma app_nil_r : forall A (xs : list A), xs ++ [] = xs.
  Proof.
    induction xs.
    - simpl.
      reflexivity.
    - simpl.
      rewrite IHxs.
      reflexivity.
  Qed.

  Lemma app_assoc : forall A (xs ys zs : list A), (xs ++ ys) ++ zs = xs ++ (ys ++ zs).
  (* Detailed paper proof.
     By induction on xs.
     - xs is nil,
         goal is forall ys zs, ([] ++ ys) ++ zs = [] ++ (ys ++ zs).
       let ys and zs be arbitrary,
         goal is ([] ++ ys) ++ zs = [] ++ (ys ++ zs).
       ([] ++ ys) computes to ys; [] ++ (ys ++ zs) computes to ys ++ zs.
         goal is ys ++ zs = ys ++ zs.
       conclude by reflexivity.
     - xs is x :: xs,
         goal is forall ys zs, ((x :: xs) ++ ys) ++ zs = (x :: xs) ++ (ys ++ zs)
         IH is forall ys zs, (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
       let ys and zs be arbitrary.
         goal is ((x :: xs) ++ ys) ++ zs = (x :: xs) ++ (ys ++ zs)
       (x :: xs) ++ ys computes to x :: (xs ++ ys)
         goal is (x :: (xs ++ ys)) ++ zs = (x :: xs) ++ (ys ++ zs)
       (x :: (xs ++ ys)) ++ zs computes to x :: ((xs ++ ys) ++ zs)
         goal is x :: ((xs ++ ys) ++ zs) = (x :: xs) ++ (ys ++ zs)
       (x :: xs) ++ (ys ++ zs) computes to x :: (xs ++ (ys ++ zs))
         goal is x :: ((xs ++ ys) ++ zs) = x :: (xs ++ (ys ++ zs))
       use IH instantiated with (ys := ys) and (zs := zs)
       and conclude by reflexivity
   *)
  Proof.
    induction xs as [|x xs].
    - (* xs is [] *)
      intros ys zs.
      simpl.
      reflexivity.
    - (* xs is x :: xs *)
      intros ys zs.
      simpl.
      rewrite IHxs.
      reflexivity.
  Qed.

  Fixpoint rev A (xs : list A) : list A :=
    match xs with
    | [] => []
    | x :: xs => rev xs ++ [x]
    end.

  Fixpoint rev_tail' A (xs : list A) (acc : list A) : list A :=
    match xs with
    | [] => acc
    | x :: xs => rev_tail' xs (x :: acc)
    end.

  Definition rev_tail A (xs : list A) : list A := rev_tail' xs [].

  Theorem rev_is_rev_tail :
    forall A (xs : list A),
      rev_tail xs = rev xs.
  Proof.
    induction xs.
    - simpl. unfold rev_tail. simpl. reflexivity.
    - simpl. unfold rev_tail. simpl. (* ? *) rewrite <- IHxs. (* ??? *)
  Abort.

  (* Rule of thumb: if a function is a fixpoint, statements about it should be
     proved by induction. If it's a definition, induction is unlikely to be
     effective.

     Since rev_tail is a definition, theorems about it should just unfold it and
     then use some lemma about rev_tail'.

     Since rev_tail' is a fixpoint, statements about it should be proved by
     induction.
   *)

  (* There are three flavors of argument to a fixpoint:
     1) the "structural" argument (the one being recursed on)
     2) "constant" arguments, which don't change through any recursive calls
     3) "variable" arguments, which change on recursive calls

     Rule of thumb: in order for a statement about a fixpoint to be provable by
     induction, the structural and variable arguments should be
     forall-quantified.

     Pro tip: the structural argument should be quantified before *any*
     variable arguments.
   *)

  (* So, we're looking for a stament about rev_tail' that forall-quantifies
     over `xs` and `acc`, and which implies `rev_is_rev_tail`. Something
     like this:

     forall A (xs : list A) acc,
        rev_tail' xs acc = (* ??? *)

     How would you describe the general behavior of `rev_tail'`? You might say
     something like "it reverses `xs` and prepends the result to `acc`". This
     turns out to work!
   *)

  Lemma rev_tail'_is_rev_then_prepend :
    forall A (xs acc : list A),
      rev_tail' xs acc = rev xs ++ acc.
  (* Detailed paper proof:
     By induction on xs.
     - x is [],
         goal becomes forall acc, rev_tail [] acc = rev [] ++ acc.
       let acc be arbitrary,
         goal becomes rev_tail [] acc = rev [] ++ acc.
       rev_tail [] acc computes to acc,
         goal becomes acc = rev [] ++ acc.
       rev [] computes to [],
         goal becomes acc = [] ++ acc.
       [] ++ acc computes to acc,
         goal becomes acc = acc.
       conclude by reflexivity.
     - xs is x :: xs,
         goal becomes forall acc, rev_tail (x :: xs) acc = rev (x :: xs) ++ acc.
         IH is forall acc, rev_tail xs acc = rev xs ++ acc.
       let acc be arbitrary,
         goal becomes rev_tail (x :: xs) acc = rev (x :: xs) ++ acc.
       rev_tail (x :: xs) acc computes to rev_tail xs (x :: acc)
         goal becomes rev_tail xs (x :: acc) = rev (x :: xs) ++ acc.
       rev (x :: xs) computes to rev xs ++ [x]
         goal becomes rev_tail xs (x :: acc) = (rev xs ++ [x]) ++ acc.
       instantiate IH with (x :: acc)
         IH becomes rev_tail xs (x :: acc) = rev xs ++ x :: acc.
       use IH in goal,
         goal becomes rev xs ++ x :: acc = (rev xs ++ [x]) ++ acc.
       use associativity of append (lemma)
         goal becomes rev xs ++ x :: acc = rev xs ++ ([x] ++ acc).
       [x] ++ acc computes to x :: acc,
         goal becomes rev xs ++ x :: acc = rev xs ++ x :: acc.
       conclude by reflexivity. *)
  Proof.
    induction xs as [|x xs].
    - intros acc.
      simpl.
      reflexivity.
    - intros acc.
      simpl.
      specialize (IHxs (x :: acc)).
      rewrite IHxs.
      rewrite app_assoc.
      simpl.
      reflexivity.
  Qed.

  Theorem rev_tail_is_rev :
    forall A (xs : list A),
      rev_tail xs = rev xs.
  Proof.
    unfold rev_tail.
    intros.
    rewrite rev_tail'_is_rev_then_prepend.
    rewrite app_nil_r.
    reflexivity.
  Qed.

  (* Proof engineering tip: unfold at most one definition per theorem.

     Even better: rely on computational behavior of at most one definition per
     theorem.
   *)
End MyList.

(* Switch back to stdlib lists and nats, since what we're about to do isn't
   there already. *)
Require Import List.
Import ListNotations.

Fixpoint sum (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | x :: xs => x + sum xs
  end.

Fixpoint sum_tail' (xs : list nat) (acc : nat) : nat :=
  match xs with
  | [] => acc
  | x :: xs => sum_tail' xs (x + acc)
  end.

Definition sum_tail (xs : list nat) : nat := sum_tail' xs 0.

Theorem sum_tail_is_sum :
  forall xs, sum_tail xs = sum xs.
Proof.
  induction xs.
  - simpl. unfold sum_tail. simpl. reflexivity.
  - simpl. unfold sum_tail. simpl.
Abort.

Lemma sum_tail'_is_sum_plus_acc :
  forall xs acc, sum_tail' xs acc = sum xs + acc.
Proof.
  induction xs.
  - intros acc.
    simpl.
    reflexivity.
  - intros acc.
    simpl.
    rewrite IHxs.
    omega.
Qed.

Theorem sum_tail_is_sum :
  forall xs, sum_tail xs = sum xs.
Proof.
  intros xs.
  unfold sum_tail.
  rewrite sum_tail'_is_sum_plus_acc.
  omega.
Qed.

Fixpoint sum_cps' (xs : list nat) A (k : nat -> A) : A :=
  match xs with
  | [] => k 0

  (* See what happens if you change x + n to n + x in the following line.

     Nothing too bad, but the proof below breaks because we need an extra
     commutativity step. Carefully designed to make proofs simple. This is
     something that will come up again and again. *)
  | x :: xs => sum_cps' xs (fun n => k (x + n))
  end.

Definition sum_cps (xs : list nat) : nat := sum_cps' xs (fun x => x).

(* TODO: probably worth getting stuck here when attempting to fix k as fun x => x. *)

Lemma sum_cps'_calls_k_with_sum :
  forall xs A (k : nat -> A),
    sum_cps' xs k = k (sum xs).
Proof.
  induction xs.
  - intros.
    simpl.
    reflexivity.
  - intros.
    simpl.
    rewrite IHxs.
    reflexivity.
Qed.

Theorem sum_cps_is_sum :
  forall xs, sum_cps xs = sum xs.
Proof.
  intros.
  unfold sum_cps.
  rewrite sum_cps'_calls_k_with_sum.
  reflexivity.
Qed.



Inductive expr :=
| Const (n : nat)
| Plus (e1 e2 : expr).

Fixpoint eval (e : expr) : nat :=
  match e with
  | Const n => n
  | Plus e1 e2 => eval e1 + eval e2
  end.

Fixpoint eval_cps' (e : expr) A (k : nat -> A) : A :=
  match e with
  | Const n => k n

  (* Change n1 + n2 to n2 + n1 for a good time. *)
  | Plus e1 e2 => eval_cps' e1 (fun n1 => eval_cps' e2 (fun n2 => k (n1 + n2)))
  end.

Definition eval_cps (e : expr) : nat := eval_cps' e (fun x => x).

Lemma eval_cps'_calls_k_with_eval :
  forall e A (k : nat -> A),
    eval_cps' e k = k (eval e).
Proof.
  induction e.
  - intros.
    simpl.
    reflexivity.
  - intros.
    simpl.
    rewrite IHe1.
    rewrite IHe2.
    reflexivity.
Qed.

Theorem eval_cps_is_eval : forall e, eval_cps e = eval e.
Proof.
  intros.
  unfold eval_cps.
  rewrite eval_cps'_calls_k_with_eval.
  reflexivity.
Qed.




(* Stack machine *)

Inductive instr :=
| Push (n : nat)
| Add.

Definition prog := list instr.

Definition stack := list nat.

Definition exec_instr (i : instr) (s : stack) : stack :=
  match i with
  | Push n => n :: s
  | Add => match s with
          | x :: y :: s => y + x :: s (* forth order *)
          | _ => s (* bogus!

                     TODO: interesting point here about doing a type-correct but
                     wrong thing vs introducing options to capture failure;
                     corresponding proof engineering tradeoffs *)
          end
  end.

Fixpoint exec_prog' (p : prog) (s : stack) : stack :=
  match p with
  | [] => s
  | i :: p => exec_prog' p (exec_instr i s)
  end.

Definition exec_prog (p : prog) : nat := hd 0 (exec_prog' p []).
(* TODO: Could also return stack here. jrw thinks stack is right thing, but also
   that readers won't agree :) But returning nat has advantage of making things
   a little harder. *)

Fixpoint compile (e : expr) : prog :=
  match e with
  | Const n => [Push n]
  | Plus e1 e2 => compile e1 ++ compile e2 ++ [Add]
  end.

Theorem compile_correct :
  forall e,
    exec_prog (compile e) = eval e.
Proof.
  (* TODO: get stuck*)
Abort.

(* Nothing obviously wrong with this lemma statement.

   TODO: Brings up interesting discussion of rule of thumb, since we're
   forall-quantified over e, but then call compile, instead of just being
   forall-quantified over a program. *)
Lemma exec_prog'_of_compile_is_push_eval :
  forall e s,
    exec_prog' (compile e) s = eval e :: s.
Proof.
  induction e.
  - intros.
    simpl.
    reflexivity.
  - intros.
    simpl.
    Fail rewrite IHe1. (* oh no! *)
    (* We need to know that exec_prog' executes appends in the right way.
       Two reasonable ways of proceeding: prove exec_prog'_app lemma or
       generalize current lemma statement to account for it. Showing both
       is interesting. *)

    Lemma exec_prog'_app :
      forall p1 p2 s,
        exec_prog' (p1 ++ p2) s = exec_prog' p2 (exec_prog' p1 s).
    Proof.
      induction p1.
      - intros.
        simpl.
        reflexivity.
      - intros.
        simpl.
        rewrite IHp1.
        reflexivity.
    Qed.

    rewrite exec_prog'_app.
    rewrite IHe1.

    rewrite exec_prog'_app.
    rewrite IHe2.
    simpl. (* Notice we can skip the error case. *)
    reflexivity.
Qed.

Theorem compile_correct :
  forall e,
    exec_prog (compile e) = eval e.
Proof.
  unfold exec_prog.
  intros.
  rewrite exec_prog'_of_compile_is_push_eval.
  simpl. (* Notice we can skip the error case. *)
  reflexivity.
Qed.

(* Other way of doing it in one go. *)
Lemma exec_prog'_of_compile_of_e_appended_to_p_is_exec_prog'_of_p_with_eval_e_pushed :
  forall e p s,
    exec_prog' (compile e ++ p) s = exec_prog' p (eval e :: s).
Proof.
  induction e.
  - intros.
    simpl.
    reflexivity.
  - intros.
    simpl.
    rewrite app_ass.
    rewrite IHe1.
    rewrite app_ass.
    rewrite IHe2.
    simpl.
    reflexivity.
Qed.

Theorem compile_correct_another_way :
  forall e,
    exec_prog (compile e) = eval e.
Proof.
  intros.
  unfold exec_prog.
  rewrite <- app_nil_r with (l := compile e).
  rewrite exec_prog'_of_compile_of_e_appended_to_p_is_exec_prog'_of_p_with_eval_e_pushed.
  simpl.
  reflexivity.
Qed.



(* Insertion sort *)

(* TODO: Discussion of spec for sorting. Usually if you ask people who haven't
   thought about it before, they will say "well it should be sorted" and not
   remember to say permutation. *)

Fixpoint insert (a : nat) (xs : list nat) : list nat :=
  match xs with
  | [] => [a]
  | x :: xs => if a <=? x then a :: x :: xs
              else x :: (insert a xs)
  end.

(* Just for fun... *)
Fixpoint insert_tail' (a : nat) (xs acc : list nat) : list nat :=
  match xs with
  | [] => List.rev' (a :: acc)
  | x :: xs => if a <=? x then List.rev_append acc (a :: x :: xs)
              else insert_tail' a xs (x :: acc)
  end.

Definition insert_tail (a : nat) (xs : list nat) : list nat :=
  insert_tail' a xs [].

(* :D *)
Lemma insert_tail'_is_prepend_reversed_acc_to_insert_xs :
  forall a xs acc,
    insert_tail' a xs acc = List.rev acc ++ insert a xs.
Proof.
  induction xs.
  - intros.
    simpl.
    unfold rev'.
    simpl.
    rewrite rev_append_rev.
    simpl.
    reflexivity.
  - intros.
    simpl.
    break_if.
    + rewrite rev_append_rev.
      reflexivity.
    + rewrite IHxs.
      simpl.
      rewrite app_ass.
      simpl.
      reflexivity.
Qed.

Theorem insert_tail_is_insert :
  forall a xs,
    insert_tail a xs = insert a xs.
Proof.
  intros.
  unfold insert_tail.
  rewrite insert_tail'_is_prepend_reversed_acc_to_insert_xs.
  simpl.
  reflexivity.
Qed.

Lemma insert_insert_comm :
  forall a b xs,
    insert a (insert b xs) = insert b (insert a xs).
Proof.
  induction xs.
  - simpl.
    repeat break_if.
    + rewrite Nat.leb_le in *.
      assert (a = b) by omega.
      subst.
      reflexivity.
    + reflexivity.
    + reflexivity.
    + rewrite Nat.leb_nle in *.
      omega.
  - simpl.
    repeat (break_if; simpl).
    all: try rewrite Nat.leb_le in *.
    all: try rewrite Nat.leb_nle in *.
    all: auto.
    all: try omega.
    all: try discriminate.
    + assert (a = b) by omega.
      subst.
      reflexivity.
    + rewrite IHxs.
      reflexivity.
Qed.

Fixpoint insertion_sort (xs : list nat) : list nat :=
  match xs with
  | [] => []
  | x :: xs => insert x (insertion_sort xs)
  end.

Fixpoint insertion_sort_tail' (xs acc : list nat) : list nat :=
  match xs with
  | [] => acc
  | x :: xs => insertion_sort_tail' xs (insert_tail x acc)
  end.

Definition insertion_sort_tail (xs : list nat) : list nat :=
  insertion_sort_tail' xs [].

Theorem insertion_sort_tail_is_insertion_sort :
  forall xs,
    insertion_sort_tail xs = insertion_sort xs.
Proof.
  intros.
  unfold insertion_sort_tail.
  induction xs.
  - simpl.
    reflexivity.
  - simpl.
    rewrite <- IHxs.
    rewrite insert_tail_is_insert.

    Lemma insertion_sort_tail'_insert_comm :
      forall xs a ys,
        insertion_sort_tail' xs (insert a ys) = insert a (insertion_sort_tail' xs ys).
    Proof.
      induction xs.
      - intros.
        simpl.
        reflexivity.
      - intros.
        simpl.
        rewrite insert_tail_is_insert.
        rewrite insert_tail_is_insert.
        rewrite insert_insert_comm.
        rewrite IHxs.
        reflexivity.
    Qed.

    rewrite insertion_sort_tail'_insert_comm.
    reflexivity.
Qed.

(* Roll our own sorted because it's a good exercise and the stdlib is more
   general than we need. *)
Inductive sorted : list nat -> Prop :=
| sorted_nil : sorted []
| sorted_cons : forall a xs, sorted xs -> List.Forall (fun x => a <= x) xs -> sorted (a :: xs).

Theorem insertion_sort_sorted :
  forall xs, sorted (insertion_sort xs).
Proof.
  induction xs.
  - simpl.
    apply sorted_nil.
  - simpl.

    Lemma insert_sorted :
      forall a xs,
        sorted xs ->
        sorted (insert a xs).
    Proof.
      induction xs.
      - intros.
        simpl.
        apply sorted_cons.
        + apply sorted_nil.
        + apply Forall_nil.
      - intros.
        simpl.
        break_if.
        + rewrite Nat.leb_le in *.
          apply sorted_cons.
          * assumption.
          * invc H.
            apply Forall_cons.
            -- assumption.
            -- eapply Forall_impl; try eassumption.
               intros.
               simpl in *.
               omega.
        + rewrite Nat.leb_nle in *.
          invc H.
          apply sorted_cons.
          * apply IHxs. assumption.
          *
            Lemma insert_Forall_le:
              forall (a b : nat) (xs : list nat),
                a <= b ->
                Forall (fun x : nat => a <= x) xs -> Forall (fun x : nat => a <= x) (insert b xs).
            Proof.
              intros.
              (* Pro tip: induct on the Forall instead of the xs. In general,
                 induct on the "most dependent" thing you have. *)
              induction H0.
              - simpl.
                apply Forall_cons.
                + assumption.
                + apply Forall_nil.
              - simpl.
                break_if.
                + apply Forall_cons.
                  * assumption.
                  * apply Forall_cons.
                    -- assumption.
                    -- assumption.
                + apply Forall_cons.
                  * assumption.
                  * assumption.
            Qed.

            apply insert_Forall_le.
            -- omega.
            -- assumption.
    Qed.

    apply insert_sorted.
    assumption.
Qed.

(* The permutation library is pretty good already, so we can just use it directly. *)

Require Import Permutation.

Theorem insertion_sort_perm :
  forall xs, Permutation (insertion_sort xs) xs.
Proof.
  induction xs.
  - simpl.
    reflexivity.
  - simpl.

    Lemma insert_perm :
      forall a xs, Permutation (insert a xs) (a :: xs).
    Proof.
      induction xs.
      - simpl.
        reflexivity.
      - simpl.
        break_if.
        + reflexivity.
        + (* Pro tip: rewriting with Permutations works and is typically more
             convenient than trying to apply lemmas directly. *)
          rewrite perm_swap.
          apply Permutation_cons.
          * reflexivity.
          * apply IHxs.
    Qed.

    rewrite insert_perm.
    apply Permutation_cons.
    + reflexivity.
    + apply IHxs.
Qed.

(* We have proved that insertion_sort is correct (sorted and permutation) and
   that insertion_sort_tail (which is the code we actually want to run) is
   equivalent to it. We can combine these to get correctness of
   insertion_sort_tail. *)

Theorem insertion_sort_tail_sorted :
  forall xs, sorted (insertion_sort_tail xs).
Proof.
  intros.
  rewrite insertion_sort_tail_is_insertion_sort.
  apply insertion_sort_sorted.
Qed.

Theorem insertion_sort_tail_perm :
  forall xs, Permutation (insertion_sort_tail xs) xs.
Proof.
  intros.
  rewrite insertion_sort_tail_is_insertion_sort.
  apply insertion_sort_perm.
Qed.
