(* Four different ways of proving the same theorem: evenb (double x 0) = true. *)

Fixpoint evenb (n:nat) : bool :=
  match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
  end.


(* double: computes 2x using an accumulator *)
Fixpoint double (x y : nat) : nat :=
  match x with
    | O => y
    | S x' => double x' (S (S y))
  end.




Theorem even_double_1 : forall x:nat,
  evenb (double x 0) = true.
Proof.
  (* METHOD 1: PE with loop detection (automatic) *)
  intros.

  (* initial *)
  induction x.
  reflexivity.

  (* recursive case *)
  simpl.                        (* unable to use IHx *)
  induction x.
  reflexivity.

  (* back to the recursive case *)
  simpl.

  (* Now we know this is going to go on forever, we find that the only
  thing that is changing is the second argument to double (y). It
  changes from y to (S (S y)) at every iteration. *)

  assert (forall x y : nat,
    evenb (double x y) = evenb (double x (S (S y)))).
  induction x0.
  reflexivity.
  intros.
  apply IHx1.
  rewrite <- H.
  apply IHx.
  (* Done *)
Qed.




(* METHOD 2: use lemma even_ss extracted from METHOD 1 *)
Lemma even_ss : 
  forall x y : nat,
    evenb (double x y) = evenb (double x (S (S y))).
Proof.
  induction x.
  reflexivity.

  intros y.
  simpl. apply IHx.
Qed.

Theorem even_double_2 :
  forall x : nat, 
    evenb (double x 0) = true.
Proof.
  intros.
  induction x.
  reflexivity.
  simpl.
  rewrite <- even_ss.
  apply IHx.
Qed.





Lemma even_ss_b :
  forall x y : nat,
    evenb (double x y) = true -> evenb (double x (S (S y))) = true.
Proof.
  induction x.
  intros.
  simpl in *.
  apply H.

  simpl. 
  intros y. apply IHx.
Qed.

Theorem even_double_2b :
  forall x : nat, 
    evenb (double x 0) = true.
Proof.
  intros.
  induction x.
  reflexivity.
  simpl.
  apply even_ss2.
  apply IHx.
Qed.





(* METHOD 3: use lemma even_y *)
Lemma even_y : 
  forall x y : nat,
    evenb y = true -> evenb (double x y) = true.
Proof.
  (* METHOD 1: the dumb way *)
  induction x; intros; simpl.
  apply H.
  apply IHx.
  simpl.
  apply H.

  (* METHOD 2: use ; and auto *)
  Restart.
  induction x; simpl; auto.
Qed.


Theorem even_double_3 :
  forall x : nat,
    evenb (double x 0) = true.
Proof.
  intros.
  apply even_y.
  reflexivity.
Qed.




(* By Rebecca Swords *)
Lemma double_s :
  forall x y : nat, 
    double (S x) y = S (S (double x y)).
Proof.
  intros x.
  induction x.
  reflexivity.

  intros y.
  simpl in *.
  apply IHx.
Qed.


Theorem even_double_4 :
  forall x : nat, 
    evenb (double x 0) = true.
Proof.
  induction x.
  reflexivity.

  rewrite double_s.
  simpl.
  apply IHx.
Qed.




(* proof terms

METHOD 1:
---------------------------------------------------------------
even_double_1 =
fun x : nat =>
nat_ind (fun x0 : nat => evenb (double x0 0) = true) eq_refl
  (fun (x0 : nat) (IHx : evenb (double x0 0) = true) =>
   nat_ind
     (fun x1 : nat =>
      evenb (double x1 0) = true -> evenb (double x1 2) = true)
     (fun _ : evenb (double 0 0) = true => eq_refl)
     (fun (x1 : nat)
        (_ : evenb (double x1 0) = true -> evenb (double x1 2) = true)
        (IHx1 : evenb (double (S x1) 0) = true) =>
      (fun
         H : forall x2 y : nat,
             evenb (double x2 y) = evenb (double x2 (S (S y))) =>
       eq_ind (evenb (double x1 2)) (fun b : bool => b = true) IHx1
         (evenb (double x1 4)) (H x1 2))
        (fun x2 : nat =>
         nat_ind
           (fun x3 : nat =>
            forall y : nat, evenb (double x3 y) = evenb (double x3 (S (S y))))
           (fun y : nat => eq_refl)
           (fun (x3 : nat)
              (IHx2 : forall y : nat,
                      evenb (double x3 y) = evenb (double x3 (S (S y))))
              (y : nat) => IHx2 (S (S y))) x2)) x0 IHx) x
     : forall x : nat, evenb (double x 0) = true



METHOD 2:
-----------------------------------------------------
even_double_2 =
fun x : nat =>
nat_ind (fun x0 : nat => evenb (double x0 0) = true) eq_refl
  (fun (x0 : nat) (IHx : evenb (double x0 0) = true) =>
   eq_ind (evenb (double x0 0)) (fun b : bool => b = true) IHx
     (evenb (double x0 2)) (even_ss x0 0)) x
     : forall x : nat, evenb (double x 0) = true

even_ss =
fun x : nat =>
nat_ind
  (fun x0 : nat =>
   forall y : nat, evenb (double x0 y) = evenb (double x0 (S (S y))))
  (fun y : nat => eq_refl)
  (fun (x0 : nat)
     (IHx : forall y : nat, evenb (double x0 y) = evenb (double x0 (S (S y))))
     (y : nat) => IHx (S (S y))) x
     : forall x y : nat, evenb (double x y) = evenb (double x (S (S y)))



METHOD 3:
------------------------------------------------------
even_double_3 =
fun x : nat => even_y x 0 eq_refl
     : forall x : nat, evenb (double x 0) = true

even_y =
fun x : nat =>
nat_ind
  (fun x0 : nat =>
   forall y : nat, evenb y = true -> evenb (double x0 y) = true)
  (fun (y : nat) (H : evenb y = true) => H)
  (fun (x0 : nat)
     (IHx : forall y : nat, evenb y = true -> evenb (double x0 y) = true)
     (y : nat) (H : evenb y = true) => IHx (S (S y)) H) x
     : forall x y : nat, evenb y = true -> evenb (double x y) = true

*)
