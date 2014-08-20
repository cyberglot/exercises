Module Basics.

  Definition nandb (b1: bool) (b2: bool): bool :=
    match b1, b2 with
      | false, _ => true
      | _, false => true
      | _, _ => false
    end.

  Example test_nandb1: (nandb true false) = true.
  Proof. reflexivity. Qed.
  Example test_nandb2: (nandb false false) = true.
  Proof. reflexivity. Qed.
  Example test_nandb3: (nandb false true) = true.
  Proof. reflexivity. Qed.
  Example test_nandb4: (nandb true true) = false.
  Proof. reflexivity. Qed.

  Definition andb3 (b1: bool) (b2: bool) (b3: bool): bool :=
    match b1, b2, b3 with
      | true, true, true => true
      | _, _, _ => false
    end.

  Example test_andb31: (andb3 true true true) = true.
  Proof. reflexivity. Qed.
  Example test_andb32: (andb3 false true true) = false.
  Proof. reflexivity. Qed.
  Example test_andb33: (andb3 true false true) = false.
  Proof. reflexivity. Qed.
  Example test_andb34: (andb3 true true false) = false.
  Proof. reflexivity. Qed.

  Fixpoint factorial (n: nat): nat :=
    match n with
      | 0 => 1
      | S n' => n * (factorial n')
    end.

  Example test_factorial1: (factorial 3) = 6.
  Proof. reflexivity. Qed.
  Example test_factorial2: (factorial 5) = (mult 10 12).
  Proof. reflexivity. Qed.

  Definition blt_nat (n m: nat): bool :=
    match m - n with
      | O => false
      | S _ => true
    end.

  Fixpoint beq_nat (n m : nat) : bool :=
    match n with
      | O => match m with
              | O => true
              | S m' => false
            end
      | S n' => match m with
                 | O => false
                 | S m' => beq_nat n' m'
               end
    end.

  Example test_blt_nat1: (blt_nat 2 2) = false.
  Proof. reflexivity. Qed.
  Example test_blt_nat2: (blt_nat 2 4) = true.
  Proof. reflexivity. Qed.
  Example test_blt_nat3: (blt_nat 4 2) = false.
  Proof. reflexivity. Qed.

  Theorem plus_O_n: forall n: nat, O + n = n.
  Proof.
    intros n.
    reflexivity.
  Qed.

  Theorem plus_1_l: forall n: nat, 1 + n = S n.
  Proof.
    intros n.
    reflexivity.
  Qed.

  Theorem mult_0_l: forall n: nat, 0 * n = 0.
  Proof.
    intros n.
    reflexivity.
  Qed.

  Theorem plus_id_example: forall n m: nat, n = m -> n + n = m + m.
  Proof.
    intros n m.
    intros H.
    rewrite -> H.
    reflexivity.
  Qed.

  Theorem plus_id_exercise: forall n m o: nat, n = m -> m = o -> n + m = m + o.
  Proof.
    intros n m o.
    intros H.
    intros H'.
    rewrite -> H.
    rewrite -> H'.
    reflexivity.
  Qed.

  Theorem mult_S_1: forall n m: nat, m = S n -> m * (1 + n) = m * m.
  Proof.
    intros n m.
    intros H.
    rewrite -> H.
    reflexivity.
  Qed.

  Theorem plus_1_neq_0: forall n: nat, beq_nat (n + 1) 0 = false.
  Proof.
    intros n.
    destruct n as [| n'].
    reflexivity.
    reflexivity.
  Qed.

  Theorem identity_fn_applied_twice:
    forall (f: bool -> bool),
      (forall (x: bool), f x = x) -> forall (b: bool), f (f b) = b.
  Proof.
    intros f.
    intros Id.
    intros b.
    destruct b.
    rewrite -> Id.
    rewrite -> Id.
    reflexivity.
    rewrite -> Id.
    rewrite -> Id.
    reflexivity.
  Qed.

  Theorem negation_fn_applied_twice:
    forall (f: bool -> bool),
      (forall (x: bool), f x = negb x) -> forall (b: bool), f (f b) = b.
  Proof.
    intros f.
    intros Neg.
    intros b.
    destruct b.
    rewrite Neg.
    rewrite Neg.
    reflexivity.
    rewrite Neg.
    rewrite Neg.
    reflexivity.
  Qed.

  Inductive bin: Type :=
  | O: bin
  | T: bin -> bin
  | TP: bin -> bin.

  Fixpoint bin_inc (b: bin): bin :=
    match b with
      | O => TP O
      | T b' => TP b'
      | TP b' => T (bin_inc b')
    end.

  Fixpoint bin_to_nat (b: bin): nat :=
    match b with
      | O => 0
      | T b' => 2 * (bin_to_nat b')
      | TP b' => 1 + (2 * (bin_to_nat b'))
    end.

  (* Theorem bin_inc_conv: *)
  (*   forall b: bin, bin_to_nat (bin_inc b) = (1 + (bin_to_nat b)). *)
  (* Proof. *)
  (*   intros b. *)

End Basics.
