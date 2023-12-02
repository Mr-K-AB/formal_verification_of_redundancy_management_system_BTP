Require Import MyProject.test_inputs.
Require Import MyProject.state.
Require Import MyProject.OBC.
Require Import MyProject.library.
Require Import Bool.
Require Import Coq.Arith.Arith.
Require Import Lia.



(* Health and Miscomparison Incrementer *)
Definition CumulativeIncrement (count : nat) (status : bool): nat  :=
  match status with
  | true => 0
  | false => count + 1
  end.




(* ----------------------------- *)
(* Listing 3.12 Sensor Isolation *)

(* Isolation *)
Definition AssignIsolation (status : bool) (count : nat) : bool :=
  match status with
  | true => true
  | false => 4 <? count  
  end .


(* Sensor Management  *)
 Definition ManageCurSensorX {ax : axis} (curS : currSensor ax) (v1 v2 v3 : SIGNAL): currSensor ax :=
  match curS with
  | SID axs sid =>SID axs ( snd (voter v1 v2 v3 sid))
  end.



(* Isolation Management *)

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

(* Switch Flags *)
Definition ManageOBCSwitchFlag (commIso : CommIsolated) (obcSwitch : OBCFlag) : OBCFlag:=
  match obcSwitch with
  | raised => raised
  | notRaised => match commIso with
                 |CommIso (true, true, true) => raised
                 | _ => notRaised end
  end .

(* ---------------------------------------------- *)



Definition FlagMisComparison  (v1 v2 v3 :nat): option sensorId  :=
  let ms1 := mis_comp v1 v2 v3 in
  let ms2 := mis_comp v2 v1 v3 in
  let ms3 := mis_comp v3 v1 v2 in
  match ms1 with
  | true => Some (first)
  | false => match ms2 with
            | true => Some (second)
            | false => match ms3 with
                      | true => Some (third)
                      |false => None
                      end
            end
  end.





Definition UpdateMisCompCount  (v1 v2 v3 : nat) (misCC  : nat*nat*nat) : nat*nat*nat :=
  let '(b1,b2,b3) := misCC in
  match FlagMisComparison v1 v2 v3 with
  | Some(first) =>  (CumulativeIncrement b1 true, 0, 0)
  | Some(second) => (0, CumulativeIncrement b2 true, 0)
  | Some(third) =>  (0, 0, CumulativeIncrement b3 true)
  | None =>  (0,0,0)  
  end.







(* -------------------------------- *)
(* Listing 3.14 OBC Switching Lemma *)

(* Prove once OBC is switched flag is raised the flag remains raised *)

Lemma RaisedFlagStayForever : forall  (commIso : CommIsolated), ManageOBCSwitchFlag commIso raised = raised.
  intros.
  unfold ManageOBCSwitchFlag.
  trivial.
Qed.


(* -------------------------------- *)




(* ---------------------------- *)
(* Listing 3.15 Isolation Lemma *)

(* When cumulative miscomparison or health failure > 5 leads to isolation *)

Lemma CumulativeCountGt5LeadsToIsolation : forall  (count : nat) (isoStatus : bool ), count > 5 -> AssignIsolation  isoStatus count = true. 
intros.  
unfold AssignIsolation.
destruct isoStatus.
- trivial.
- apply Nat.ltb_lt. lia.
Qed.


(* ---------------------------- *)
