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
      rev xs = rev_tail xs.
  Proof.
    induction xs.
    - simpl. unfold rev_tail. simpl. reflexivity.
    - simpl. unfold rev_tail. simpl. rewrite IHxs. (* ??? *)
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

  Theorem rev_is_rev_tail :
    forall A (xs : list A),
      rev xs = rev_tail xs.
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