Module MyBool. (* Use a module so that we don't clobber stdlib. *)
  Inductive bool := true | false.

  Definition negb (x : bool) : bool :=
    match x with
    | true => false
    | false => true
    end.

  (* 'if' works out of the box *)
  Definition negb' (x : bool) : bool :=
    if x then false else true.

  Set Printing All.
  (* just syntactic sugar for match on a type with two constructors. *)
  Print negb'.
  Unset Printing All.

  (* TODO: talk about definitional equalities here with examples using
    `Eval compute`. *)

  Lemma negb_negb_id : forall x : bool, negb (negb x) = x.
  (* Detailed paper proof:
     By case analysis on x.
     - x is true,
         goal becomes `negb (negb true) = true`.
       inner `negb true` *computes* to false,
         goal is now `negb false = true`.
       `negb false` computes to true,
         goal is now `true = true`
       conclude by reflexivity
     - x is false,
         goal becomes `negb (negb false) = false`.
       similar to previous case, everything computes,
         goal is now `false = false`
       conclude by reflexivity *)
  Proof.
    destruct x. (* case analysis on x *)
    - (* x is true. *)
      simpl. (* reason by computation *)
      reflexivity.
    - (* x is false. *)
      simpl.
      reflexivity.
  Qed.

  Definition andb (x y : bool) : bool :=
    if x then y else false.

  Lemma andb_comm : forall x y, andb x y = andb y x.
  (* Detailed paper proof:
     By case analysis on x and y.
     In each of the four cases, both sides compute to the same value.
     Conclude by reflexivity. *)
  Proof.
    destruct x, y. (* case analysis on x and y *)
    all: simpl.
    all: reflexivity.
  Qed.

End MyBool.


Module MyNat.
  Inductive nat := O | S (n : nat).

  Fixpoint add (x y : nat) : nat :=
    match x with
    | O => y
    | S x => S (add x y)
    end.

  (* TODO: Describe here the resulting definitional equalities:
     add O y computes to y
     add (S x) y computes to S (add x y)

     but add x O does not compute
     neither does add x (S y)
   *)
End MyNat.