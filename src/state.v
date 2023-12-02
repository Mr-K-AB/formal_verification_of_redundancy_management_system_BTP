Require Import MyProject.library.

(*------------------------------Current Sensors----------------------------*)
Inductive currSensor : axis ->  Type :=
  SID (ax : axis) : sensorId -> currSensor ax.

(*-----------------------------Isolation Status----------------------------*)
(* iso x_ax (true,true,true) means all the sensors are isolated*)
Inductive IsolatedSensors : axis -> Type :=
  iso (ax : axis) : bool*bool*bool -> IsolatedSensors ax.


Inductive AllIsolatedSensors : Type :=
  alliso : (IsolatedSensors x_ax)*(IsolatedSensors y_ax)*(IsolatedSensors z_ax) -> AllIsolatedSensors.

(*Isolation status of each system*)
Inductive AcquisitionIsolated : Type :=
  AcqIso : bool*bool*bool -> AcquisitionIsolated.

(* Communication (to OBC) status of each communication interface 3 for each OBC *)
Inductive CommIsolated : Type :=
  CommIso : bool*bool*bool -> CommIsolated.
                  


(*---------------------Cumulative Health Count-----------------------------*)


Inductive SensorCumulativeHealthFailure : axis -> Type :=
  SenHFcount (ax : axis) : nat*nat*nat -> SensorCumulativeHealthFailure ax.

Inductive AllSensorCumulativeHealthFailure : Type :=
  allSenHFcount : ( SensorCumulativeHealthFailure x_ax )*( SensorCumulativeHealthFailure y_ax )*( SensorCumulativeHealthFailure z_ax ) -> AllSensorCumulativeHealthFailure.

Inductive CumulativeHealthFailureAcq : Type :=
  AcqHFcount : nat*nat*nat -> CumulativeHealthFailureAcq.
 
Inductive CumulativeHealthFailureComm : Type :=
 CommHFcount : nat*nat*nat -> CumulativeHealthFailureComm.



(*----------------------------Miscomparison Count-------------------------*)

Inductive MiscomparisonCount : axis -> Type :=
  misCount (ax : axis) : nat*nat*nat -> MiscomparisonCount ax.


Inductive AllMiscomparisonCount : Type :=
  AllmisCount : (MiscomparisonCount x_ax)*(MiscomparisonCount y_ax)*(MiscomparisonCount z_ax) -> AllMiscomparisonCount.



Inductive OBCFlag : Type :=
| raised : OBCFlag
| notRaised : OBCFlag.


