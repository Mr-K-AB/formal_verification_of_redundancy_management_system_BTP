Require Import Nat.
Require Import Bool.


(* ---------------------------------- *)
(* Listing 3.5 Voter Helper functions *)

Definition MCthresh : nat := 2.

(* ---------------------------------- *)



(* Absolute difference function *)
Definition adiff (n m : nat) : nat :=
  match  n <? m with
  | true => m - n
  | false => n - m
  end.





(* ------------------------ *)
(* Listing 3.1 Helper Types *)

Inductive SIGNAL  : Type := 
  | good  : nat -> SIGNAL
  | bad  : nat -> SIGNAL .

(* ------------------------ *)




(* ---------------------------------- *)
(* Listing 3.5 Voter Helper functions *)

Inductive sensorId :=
| first : sensorId
| second : sensorId
| third : sensorId.

(* ---------------------------------- *)



(* --------------------------- *)
(* Listing 3.7 Current Sensors *)

Inductive axis := 
| x_ax : axis
| y_ax : axis
| z_ax : axis.

(* --------------------------- *)