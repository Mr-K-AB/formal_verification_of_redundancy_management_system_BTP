(* ------------------------ *)
(* Listing 3.1 Helper Types *)

Inductive SIGNAL  : Type := 
  | good  : nat -> SIGNAL
  | bad  : nat -> SIGNAL .

(* ------------------------ *)



(* ------------------ *)
(* Listing 3.2 Sensor *)

Definition sensor :=  @relay nat.

(* ------------------ *)



(* ----------------------------------- *)
(* Listing 3.3 Acquisition Electronics *)

Definition acquisition := @relay sensor .

(* ----------------------------------- *)



(* ------------------------------ *)
(* Listing 3.4 Communication Link *)

Definition communication := @relay acquisition .

(* ------------------------------ *)



(* ---------------------------------- *)
(* Listing 3.5 Voter Helper functions *)

(* Mis - comparison threshold *)
Definition MCthresh : nat := 2.

(* Function that checks if there is mis - comparison between two values *)
Definition mis_comp_h ( xi xj : nat ) : bool := ( MCthresh <? ( adiff xi xj ) ) .

(* Function that checks X1 miscompares with X2 and X3 *)
Definition mis_comp ( X1 X2 X3 : nat ) : bool := andb ( mis_comp_h X1 X2 ) ( mis_comp_h X1 X3 ) .

(* A data type to specify the ID of a sensor along an axis *)
Inductive sensorId :=
 | first : sensorId
 | second : sensorId
 | third : sensorId .

(* ---------------------------------- *)



(* ----------------- *)
(* Listing 3.6 Voter *)

(* Voter helper function *)
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


(* Voter function (calls voter_helper functions for the current sensor) *)
Definition voter (X1 X2 X3: SIGNAL) (S : sensorId) : SIGNAL*sensorId :=
match S with 
| first => voter_helper (X1,first) (X2,second) (X3,third)
| second => voter_helper (X2,second) (X3,third) (X1,first)
| third => voter_helper (X3,third) (X1,first) (X2,second)
end.


(* ----------------- *)




(* --------------------------- *)
(* Listing 3.7 Current Sensors *)

Inductive axis := 
| x_ax : axis
| y_ax : axis
| z_ax : axis.


Inductive currSensor : axis ->  Type :=
  SID (ax : axis) : sensorId -> currSensor ax.

(* --------------------------- *)



(* ---------------------------- *)
(* Listing 3.8 Isolation Status *)


(* iso x_ax ( true , true , true ) means all the sensors are isolated *)

Inductive IsolatedSensors : axis -> Type :=
 iso ( ax : axis ) : bool * bool * bool -> IsolatedSensors ax .

Inductive AllIsolatedSensors : Type :=
 alliso : ( IsolatedSensors x_ax ) *( IsolatedSensors y_ax ) *( IsolatedSensors z_ax ) -> AllIsolatedSensors .

Inductive AcquisitionIsolated : Type :=
 AcqIso : bool * bool * bool -> AcquisitionIsolated .

Inductive CommIsolated : Type :=
 CommIso : bool * bool * bool -> CommIsolated .

(* ---------------------------- *)



(* ----------------------------------- *)
(* Listing 3.9 Cumulative Health count *)

Inductive SensorCumulativeHealthFailure : axis -> Type :=
  SenHFcount (ax : axis) : nat*nat*nat -> SensorCumulativeHealthFailure ax.

Inductive AllSensorCumulativeHealthFailure : Type :=
  allSenHFcount : ( SensorCumulativeHealthFailure x_ax )*( SensorCumulativeHealthFailure y_ax )*( SensorCumulativeHealthFailure z_ax ) -> AllSensorCumulativeHealthFailure.

Inductive CumulativeHealthFailureAcq : Type :=
  AcqHFcount : nat*nat*nat -> CumulativeHealthFailureAcq.
 
Inductive CumulativeHealthFailureComm : Type :=
 CommHFcount : nat*nat*nat -> CumulativeHealthFailureComm.

(* ----------------------------------- *)



(* --------------------------------- *)
(* Listing 3.10 Mis-comparison count *)

Inductive MiscomparisonCount : axis -> Type :=
  misCount (ax : axis) : nat*nat*nat -> MiscomparisonCount ax.


Inductive AllMiscomparisonCount : Type :=
  AllmisCount : (MiscomparisonCount x_ax)*(MiscomparisonCount y_ax)*(MiscomparisonCount z_ax) -> AllMiscomparisonCount.


(* --------------------------------- *)



(* ------------------------ *)
(* Listing 3.11 Switch Flag *)

Inductive OBCFlag : Type :=
| raised : OBCFlag
| notRaised : OBCFlag.

(* ------------------------ *)



(* ----------------------------- *)
(* Listing 3.12 Sensor Isolation *)

Definition AssignIsolation (status : bool) (count : nat) : bool :=
  match status with
  | true => true
  | false => 4 <? count  
  end .

Definition SingleSensorIsolationHelper (iso : bool) (cumm : nat) (miscomp : nat) : bool :=
  orb (AssignIsolation iso  cumm ) (AssignIsolation iso miscomp).

Definition SensorIsolationHelper ( iso  :bool*bool*bool) ( cumm :nat*nat*nat ) ( miscomp :nat*nat*nat) : bool*bool*bool :=
  match iso,cumm,miscomp with
  | (b1,b2,b3), (cn1,cn2,cn3), (mn1,mn2,mn3) =>  (SingleSensorIsolationHelper b1 cn1 mn1,
                                                 SingleSensorIsolationHelper b2 cn2 mn2,
                                                 SingleSensorIsolationHelper b3 cn3 mn3)
  end.

Definition SingleAxisSensorIsolations {ax : axis} (misComp : MiscomparisonCount ax ) ( cummHealth : SensorCumulativeHealthFailure ax ) ( isos : IsolatedSensors ax ) : IsolatedSensors ax :=
  match misComp, cummHealth, isos  with
  | (misCount _ mcs), (SenHFcount _ chs), (iso _ iss) => iso ax (SensorIsolationHelper iss chs mcs)
  end .


Definition SensorIsoation ( miscompCount  :  AllMiscomparisonCount ) ( cummHealth : AllSensorCumulativeHealthFailure ) (isos : AllIsolatedSensors) : AllIsolatedSensors :=
  match miscompCount, cummHealth, isos with
  | (AllmisCount (xmc, ymc, zmc) ),(allSenHFcount (xh,yh,zh)),(alliso (xiso,yiso,ziso) ) => alliso (
                                                                                          SingleAxisSensorIsolations xmc xh xiso,
                                                                                          SingleAxisSensorIsolations ymc yh yiso,
                                                                                          SingleAxisSensorIsolations zmc zh ziso)
  end.

(* ----------------------------- *)



(* ---------------------------------------------- *)
(* Listing 3.13 OBC Switching Transition function *)

Definition ManageOBCSwitchFlag (commIso : CommIsolated) (obcSwitch : OBCFlag) : OBCFlag:=
  match obcSwitch with
  | raised => raised
  | notRaised => match commIso with
                 |CommIso (true, true, true) => raised
                 | _ => notRaised end
  end .

(* ---------------------------------------------- *)



(* -------------------------------- *)
(* Listing 3.14 OBC Switching Lemma *)

Lemma RaisedFlagStayForever : forall  (commIso : CommIsolated), ManageOBCSwitchFlag commIso raised = raised.
  intros.
  unfold ManageOBCSwitchFlag.
  trivial.
Qed.

(* -------------------------------- *)



(* ---------------------------- *)
(* Listing 3.15 Isolation Lemma *)

Lemma CumulativeCountGt5LeadsToIsolation : forall  (count : nat) (isoStatus : bool ), count > 5 -> AssignIsolation  isoStatus count = true. 
intros.  
unfold AssignIsolation.
destruct isoStatus.
- trivial.
- apply Nat.ltb_lt. lia.
Qed.

(* ---------------------------- *)