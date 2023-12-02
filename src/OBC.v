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



(* ----------------- *)