
Inductive bool : Type :=
  | true : bool
  | false : bool.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1:  (orb true  false) = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb2:  (orb false false) = false.
Proof. simpl. reflexivity.  Qed.
Example test_orb3:  (orb false true)  = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb4:  (orb true  true)  = true.
Proof. simpl. reflexivity.  Qed.

(** We can also introduce some familiar syntax for the boolean
    operations we have just defined. The [Notation] command defines a new
    symbolic notation for an existing definition. *)

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5:  false || false || true = true.
Proof. simpl. reflexivity. Qed.

(* SeanP : may have better solution *)
Definition nandb (b1:bool) (b2:bool) : bool :=
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *) (* . Admitted. *)
  match b1 with
  | false => true
  | true => match b2 with
            | true => false
            | false => true
            end
  end.

Example test_nandb1:               (nandb true false) = true.
(* FILL IN HERE *) (* Admitted. *)
Proof. simpl. reflexivity. Qed.

Example test_nandb2:               (nandb false false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb3:               (nandb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb4:               (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

(** [] *)

(* Sean nandb solution 2 *)
Definition nandb_1 (b1:bool) (b2:bool) : bool :=
  match b1, b2 with
  | true , true => false
  | _ , _ => true
  end.
Example test_nandb_1_1:               (nandb_1 true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb_1_2:               (nandb_1 false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb_1_3:               (nandb_1 false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb_1_4:               (nandb_1 true true) = false.
Proof. simpl. reflexivity. Qed.

(** [] *)

(** **** Exercise: 1 star (andb3)  *)
(** Do the same for the [andb3] function below. This function should
    return [true] when all of its inputs are [true], and [false]
    otherwise. *)

(* SeanE *)
Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1, b2, b3 with
  | true , true , true => true
  | _ , _ , _ => false
  end.

Example test_andb31:                 (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32:                 (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33:                 (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34:                 (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.
(** [] *)

(* ================================================================= *)
(** ** Function Types *)

Check true.
(* ===> true : bool *)
Check (negb true).
(* ===> negb true : bool *)

(** Functions like [negb] itself are also data values, just like
    [true] and [false].  Their types are called _function types_, and
    they are written with arrows. *)

Check negb.
(* ===> negb : bool -> bool *)

(* ================================================================= *)
(** ** Module *)
Module NatPlayground.

(* ================================================================= *)
(** ** Numbers *)
Inductive nat : Type :=
  | O : nat (* Sean c1 : which is 0 *)
  | S : nat -> nat.

(* SeanQ : self defined nat is in this scope *)
End NatPlayground.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

(* Sean q : how minus two work? *)
Compute (minustwo 4).
  (* ===> 2 : nat *)
Compute (minustwo 0).
  (* ===> 0 : nat *)
Compute (minustwo 1).
  (* ===> 0 : nat *)
Compute (minustwo 2).
  (* ===> 0 : nat *)
Compute (minustwo 3).
  (* ===> 1 : nat *)

(* SeanE *)
Definition minusthree (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S (O)) => O  (* 2 return 0 *)
    | S (S (S n')) => n' 
  end.

Compute (minusthree 2).
  (* ===> 0 : nat *)
Compute (minusthree 3).
  (* ===> 0 : nat *)
Compute (minusthree 4).
  (* ===> 1 : nat *)

(* Recursion Function *)
Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

(* SeanQ ? SeanE *)
(* exp is defined
exp is recursively defined (decreasing on 2nd argument) *)

Compute (exp 0 5).
  (* ===> 0 : nat *)
Compute (exp 1 5).
  (* ===> 1 : nat *)
Compute (exp 2 5).
  (* ===> 32 : nat *)

(** **** Exercise: 1 star (factorial)  *)
(** Recall the standard mathematical factorial function:

       factorial(0)  =  1
       factorial(n)  =  n * factorial(n-1)     (if n>0)

    Translate this into Coq. *)

Fixpoint factorial (n:nat) : nat := 
  match n with
    | O => S ( O )
    | S n' => mult n ( factorial n' )
  end.

Example test_factorial1:          (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2:          (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.
(** [] *)

(* SeanQ : what is structurally recursive definition *)
(* an example of a structurally recursive definition of 
the fibonnaci function that Coq accepts as terminating: *)
Fixpoint fibonacci (n:nat) : nat :=
  match n with
    O => 1
  | (S n') =>
       match n' with
         O => 1
       | (S n'') => (fibonacci n'') + (fibonacci n')
       end
  end.

Example test_fibonacci1:          (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

(** We can make numerical expressions a little easier to read and
    write by introducing _notations_ for addition, multiplication, and
    subtraction. *)

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

Check ((0 + 1) + 1).