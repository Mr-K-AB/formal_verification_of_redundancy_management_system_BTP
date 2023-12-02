(* ------------------ *)
(* Listing 3.2 Sensor *)

Definition sensor :=  @relay nat.

(* ------------------ *)



(* ----------------------------------- *)
(* Listing 3.3 Acquisition Electronics *)

Definition accusition :=  @relay sensor.

(* ----------------------------------- *)



(* ------------------------------ *)
(* Listing 3.4 Communication Link *)

Definition communication := @relay accusition.

(* ------------------------------ *)







Definition convert (i : communication) := match i with
                                          | correct(correct(correct n)) => Some n
                                          | correct(correct(unhealthy n)) => None n
                                          | correct(unhealthy(correct n)) => None n
                                          | unhealthy(correct(correct n)) => None n
                                          | correct(unhealthy(unhealthy n)) => None n
                                          | unhealthy(correct(unhealthy n)) => None n
                                          | unhealthy(unhealthy(correct n)) => None n
                                          | unhealthy(unhealthy(unhealthy n)) => None n
end.
