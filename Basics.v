Module Basics.

  Definition nandb (b1: bool) (b2: bool) : bool :=
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

  Fixpoint factorial (n:nat) : nat :=
    match n with
      | 0 => 1
      | S n' => n * (factorial n')
    end.

  Example test_factorial1: (factorial 3) = 6.
  Proof. reflexivity. Qed.
  Example test_factorial2: (factorial 5) = (mult 10 12).
  Proof. reflexivity. Qed.

  Definition blt_nat (n m : nat) : bool :=
    match m - n with
      | O => false
      | S _ => true
    end.

  Example test_blt_nat1: (blt_nat 2 2) = false.
  Proof. reflexivity. Qed.
  Example test_blt_nat2: (blt_nat 2 4) = true.
  Proof. reflexivity. Qed.
  Example test_blt_nat3: (blt_nat 4 2) = false.
  Proof. reflexivity. Qed.

End Basics.
