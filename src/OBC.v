Require Import Nat.
Require Import Bool.
Require Import List.
Import ListNotations.
Require Import MyProject.library.
Require Import MyProject.test_inputs.
Require Import ZArith.



(* ---------------------------------- *)
(* Listing 3.5 Voter Helper functions *)

Definition mis_comp_h (xi xj: nat ) : bool := (MCthresh <? (adiff xi xj)).


Definition mis_comp (X1 X2 X3: nat) : bool := andb (mis_comp_h X1 X2) (mis_comp_h X1 X3).


(* ---------------------------------- *)



(* ----------------- *)
(* Listing 3.6 Voter *)

Definition voter_helper (iX1 iX2 iX3: SIGNAL*sensorId ) : SIGNAL*sensorId := 
  let X1 := fst iX1 in
  let X2 := fst iX2 in
  let X3 := fst iX3 in
  let s1 := snd iX1 in
  let s2 := snd iX2 in
  let s3 := snd iX3 in

  match X1,X2,X3 with 
  | good x1, good x2, good x3 => match mis_comp x1 x2 x3 with
                                 | false => (X1,s1)
                                 | true => match mis_comp_h x2 x3 with
                                           | false =>	(X2,s2) 
                                           | true => (bad x1, s1) end
                                 end
  | good x1, good x2, bad x3 => match mis_comp_h x1 x2 with 
                                 | false => (X1,s1)
                                 | true => (bad x1, s1) end

  | good x1, bad x2, good x3 => match mis_comp_h x1 x3 with 
                                 | false => (X1,s1)
                                 | true => (bad x1, s1) end

  | bad x1, good x2, good x3 => match mis_comp_h x2 x3 with 
                                 | false => (X2,s2)
                                 | true => (bad x2, s2) end

  | good x1, bad x2, bad x3 => (X1,s1)

  | bad x1, good x2, bad x3 => (X2,s2)

  | bad x1, bad x2, good x3 => (X3,s3)

  | bad x1, bad x2, bad x3 => (bad x1, s1)

  end.



Definition voter (X1 X2 X3: SIGNAL) (S : sensorId) : SIGNAL*sensorId :=
match S with 
| first => voter_helper (X1,first) (X2,second) (X3,third)
| second => voter_helper (X2,second) (X3,third) (X1,first)
| third => voter_helper (X3,third) (X1,first) (X2,second)
end.




Fixpoint OBC (input_list : list (SIGNAL*SIGNAL*SIGNAL) ) (current_sensor: SIGNAL*sensorId ) (cycles : nat) :  SIGNAL*sensorId  := 
match cycles with
            | O => current_sensor
            | S n => match input_list with
                     | nil => current_sensor
                     | x :: xs => match x with 
                                  | (x1,x2,x3) => let next_sensor := (voter x1 x2 x3 (snd current_sensor)) in
                                                  OBC xs next_sensor n 
                                  end
                      end	
end.




Definition multiAxisOBC (x_list : list (SIGNAL*SIGNAL*SIGNAL)) 
                        (y_list : list (SIGNAL*SIGNAL*SIGNAL)) 
                        (z_list : list (SIGNAL*SIGNAL*SIGNAL)) 
                        (current_sensor: SIGNAL*sensorId ) (cycles : nat) 
                        : (SIGNAL*sensorId)*(SIGNAL*sensorId)*(SIGNAL*sensorId) := 
  (OBC x_list current_sensor cycles,  OBC y_list current_sensor cycles,  OBC z_list current_sensor cycles) .





Definition LastFive (x: nat) (l : list nat) : list nat :=
  match l with
  | a::b::c::d::_ => x::a::b::c::d::nil
  | _ => x::l
  end .






Fixpoint SumList (l : list nat) : nat :=
  match l with
  | nil => 0
  | x :: xs => x + SumList xs
  end.

Definition AverageOfList (l : list nat ) : SIGNAL:=   
  match l with
  | nil => bad 0
  | _ => good ((SumList l)/(length l))
  end .

Definition UpdateList (l : list nat) (n: SIGNAL) : (list nat) * SIGNAL :=
  match n with
  | bad _ => (l, AverageOfList l )
  | good n0 => let newl := LastFive n0 l in
             (newl, AverageOfList newl)
  end .



