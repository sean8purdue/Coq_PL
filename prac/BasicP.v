
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

(** Every expression in Coq has a type, describing what sort of
    thing it computes. The [Check] command asks Coq to print the type
    of an expression. *)

Check true.
(* ===> true : bool *)
Check (negb true).
(* ===> negb true : bool *)

(** Functions like [negb] itself are also data values, just like
    [true] and [false].  Their types are called _function types_, and
    they are written with arrows. *)

Check negb.
(* ===> negb : bool -> bool *)