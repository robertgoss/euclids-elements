(** * Book I: Definitions and Axioms *)

Module Euclid.

(** ** Definitions *)

(* We close the nat scope as we will want to use the addition operator for magnitudes. *)
Close Scope nat_scope.

(**** Coq Note
We move the notition of a magnitude to the start of this note.

A magnitude appears in the form of length and angle. It should be thought of as a positive unit with equality , comparison and summation relations but no units of measurement.*)

(** General Axioms
-1. Things which are equal to the same thing are equal to one another.
-2. If equals be added to equals, the wholes are equal.
-3. If equals be taken from equals the remainders are equal.
-4. If equals be added to unequals, the whole are unequal, the greater sum being that which includes the greater of the unequals.
-5. If equals be taken from unequals, the remainders are unequal, the greater remainder being that which is left from the greater of the unequals.
-6. Things which are doubles of the same thing, or of equal things, are equal to each other.
-7. Things which are halves of the same thing, or of equal things, are equal to each other.
The eighth axiom is geometric in nature and has thus been placed later
-9. The whole is greater than it's parts.
*)

Class Magnitude {M : Type} (add : M -> M -> M) (greaterThan : M -> M -> Prop): Type := {
  general_axiom_1 : forall x y z : M, x=y -> x=z -> y=z;
  general_axiom_2 : forall x1 x2 y1 y2 : M, x1=x2 -> y1=y2 -> (add x1 y1)=(add x2 y2);
  general_axiom_3 : forall x1 x2 y1 y2 : M, x1=x2 -> (add x1 y1)=(add x2 y2) -> y1=y2;
  general_axiom_4 : forall x1 x2 y1 y2 : M, x1=x2 -> y1<>y2 -> (add x1 y1)<>(add x2 y2);
  general_axiom_4_1 : forall x1 x2 y1 y2 : M, x1=x2 -> greaterThan y1 y2 -> greaterThan (add x1 y1) (add x2 y2);
  general_axiom_4_2 : forall x1 x2 y1 y2 : M, x1=x2 -> greaterThan y2 y1 -> greaterThan (add x2 y2) (add x1 y1);
  general_axiom_5 : forall x1 x2 y1 y2 : M, x1=x2 -> (add x1 y1)<>(add x2 y2) -> y1<>y2;
  general_axiom_5_1 : forall x1 x2 y1 y2 : M, x1=x2 -> greaterThan (add x1 y1) (add x2 y2) -> greaterThan y1 y2;
  general_axiom_5_2 : forall x1 x2 y1 y2 : M, x1=x2 -> greaterThan (add x2 y2) (add x1 y1) -> greaterThan y2 y1;
  general_axiom_6 : forall x y : M, x = y -> (add x x)=(add y y);
  general_axiom_7 : forall x y : M, (add x x)=(add y y) -> x=y;
  general_axiom_9 : forall x y : M, greaterThan (add x y) x;
}.


(**
-1. A [Point] is that which has position, but no [Magnitude]
*) 
Definition Point : Type. Admitted.
(**
-2. A [Line] is that which has length without breadth 
*)
Definition Line : Type. Admitted.

Definition lineLength : Line -> Magnitude. Admitted.
(**
-3. The [extremities] of a [Line] are [Point]s, and the [intersection] of two [Line]s is a [Point]. 
*)

Definition extremals : Line -> Point * Point. Admitted.
(* Helper funtion to see if a point is one of the extremals of a line. *) 
Definition isExtremal (l : Line) (p : Point) : Prop :=
  match (extremals l) with
    | (p1, p2) => p1 = p /\ p2 = p
  end.

Definition intersection : Line -> Line -> Point -> Prop. Admitted.

(** 
-4. A [StraightLine] is that which evenly between its extreme points. Any portion cut off from a straight line is called a segment of it.
*)
Definition straightLine (l : Line) : Prop. Admitted.

(* Set of helper types for a pair of line and proof of straightness *)
Inductive StraightLine : Type :=
  straightLineCons (l : Line) : straightLine l -> StraightLine.
Definition line (s : StraightLine) : Line :=
  match s with
    | straightLineCons l _ => l
  end.

Definition straightLineDeterminedByExtremals (p1 p2 q1 q2 : Point) 
                                 (l1 l2 : Line) : 
    straightLine l1 -> straightLine l2 -> 
    extremals l1 = (p1,p2) -> extremals l2 = (q1,q2) ->
                              (p1 = q1) -> (p2 = q2) -> l1 = l2.
Admitted.

Definition segmentOf : StraightLine -> StraightLine -> Prop. Admitted.
(**
-5. A [Surface] (or superficies) is that which has length and breadth, but no thickness.
*)
Definition Surface : Type. Admitted.

(**
-6. The boundaries of a [Surface] are [Line]s.
*)
Definition surfaceBoundary : Surface -> list Line. Admitted.

(**
-7. A plane surface is one in which any [DistinctPoints] being taken the [Line] between them lies wholly in that [Surface]. A plane surface is frequently referred to as a [Plane].
*)
Definition pointOnSurface : Point -> Surface -> Prop. Admitted.
Definition lineOnSurface : Line -> Surface -> Prop. Admitted.

Definition planeSurface (s : Surface) : Prop :=
  forall (p1 p2 : Point) (l : Line),
    pointOnSurface p1 s -> pointOnSurface p2 s ->
    (p1 , p2) = extremals l -> straightLine l ->
    lineOnSurface l s.

(* Helper type for a pair of a surface and a proof that it is a plane *)
Inductive PlaneSurface : Type :=
  plane (s : Surface) : planeSurface s -> PlaneSurface.

(**
-8. A plane angle is the inclination of two [Line]s to each other which meet together, but are not in the same direction.
(Definition 8. is not required in Euclid's geometry the only angles employed by him being those formed by [StraightLine]s.
*)

(**
-9. A plane rectilinear angle is the inclination of two [StraightLine]s to one another, which meet together, but are not in the same [StraightLine].
The [Point] at which the [StraightLine] meet is called the [vertex] of the angle, and the [StraightLine]s themselves the [arms] of the [Angle]. 
*)


Definition colinear (l1 l2 : StraightLine) : Prop :=
  exists (l : StraightLine), (segmentOf l1 l) /\ (segmentOf l2 l).

Inductive Angle : Type :=
  angle (l1 l2 : StraightLine) (p : Point) : 
       not (colinear l1 l2) -> isExtremal (line l1) p -> isExtremal (line l2) p -> Angle.

Definition vertex (a : Angle) : Point :=
  match a with
    angle _ _ p _ _ _ => p
  end.

Definition arms (a : Angle) : StraightLine * StraightLine :=
  match a with
    angle l1 l2 _ _ _ _ => (l1, l2)
  end.

(**** Note.
When there are several [Angle]s at one [Point] each is expressed by three letters, of which the letter that refers to the vertex is put between the other two.
Thus the angle contained by the [StraightLine]s OA, OB is named the angle AOB or BOA; and the angle contained by OA, OC is named the angle AOC or COA.
But if there is only one [Angle] at a [Point], it may be expressed by a single letter, as the angle at O.

Of the two [StraightLine]s OB, OC shewn in the adjoining diagram, we recognize that OC is more inclined than OB to the [StraightLine] OA : this we express by saying that the [Angle] AOC is greater thn the angle AOB.
Thus the [Angle] must be regarded as having a [Magnitude].
*)
Definition angleMagnitude : Angle -> Magnitude. Admitted.

(**
It must be carefully observed that the size of an angle in no way depends on the length of its arms, but only on their inclination to one another.
The angle AOC is the sum of the angles AOB and BOC; and AOB is the difference of the angles AOC and BOC.
*)

(* Add comment as to the formation of this definition *)
Definition angleSum (a1 a2 asum : Angle) : Prop :=
  match (arms a1, arms a2,arms asum) with
    | ((l1,l2), (l3,l4), (l5,l6)) => vertex a1 = vertex a2
                                     /\ vertex a1 = vertex asum
                                     /\ colinear l2 l3
                                     /\ colinear l1 l4
                                     /\ colinear l2 l5
  end.

(* Implicit assertation that the sum of angles goes to the sum of magnitudes *)
Definition angleSumToMagSum (a1 a2 asum : Angle) :
  angleSum a1 a2 asum -> 
       (angleMagnitude a1 + angleMagnitude a2) = angleMagnitude asum.
Admitted.

(* Helper defintions for when [Angle]s are equal in magnitude *)
Definition equalAngleMagnitude (a1 a2 : Angle) : Prop :=
  angleMagnitude a1 = angleMagnitude a2.

Definition angleGreaterEqual (a1 a2 : Angle) : Prop :=
  ex (fun adiff => angleSum a1 adiff a2). 

(* Helper defintions for when [Angle]s are greater than or equal in magnitude *)
Definition greaterEqualAngleMagnitude (a1 a2 : Angle) : Prop :=
  angleMagnitude a1 <= angleMagnitude a2.





(** ( Another view of an [Angle] is recognized in many branches of mathematics; and though not employed by Euclid, it is here given because it furnishes more clearly than any other a conception of what is meant by the [Magnitude] of an [Angle].
Suppose that the [StraightLine] OP in the diagram is capable of revolution about the [Point] O like the hands of a watch, but in the opposite direction; and suppose that in this way it has passed successively from the positions OA to the positions occupied by OB and OC. Such a [Line] must have undergone more turning in passing from OA to OC than in passing from OA to OB; and consequently the [Angle] AOC is said to be greater than the [Angle] AOB. )  *)

(** 
[Angle]s which lie on either side of a common arm are called [adjacent] angles.
For example, when one [StraightLine] OC is drawn from a [Point] in another [StraightLine] AB, the angles COA, COB are adjacent.
*)

Definition adjancent (a1 a2 : Angle) : Prop :=
  ex (fun asum => angleSum a1 a2 asum).
 
(**
When two [StraightLine]s, such as AB, CD, cross one another at E the two [Angle]s CEA, BED are said to be vertically opposite.
The two [Angle]s CEB, AED are also vertically opposite to one another.
*)

(* Define a helper method wherre we make explicit the lines we assue exist*)
Definition verticallyOppositeLines' (a1 a2 : Angle) (lA lB : StraightLine) : Prop :=
  match (arms a1, arms a2) with
    | ((l1,l2),(l3,l4)) => vertex a1 = vertex a2
                        /\ segmentOf l1 lA
                        /\ segmentOf l2 lB
                        /\ segmentOf l3 lA
                        /\ segmentOf l4 lB
  end.

Definition verticallyOpposite (a1 a2 : Angle) : Prop :=
  ex (fun lA => ex (fun lB => verticallyOppositeLines' a1 a2 lA lB)).

(**
-10. When a [StraightLine] standing on another makes the [adjancent] [Angle]s equal to one another, each of the [Angle]s is called a [rightAngle]; and the [StraightLine] which stands on the other is called [perpendicular] to it.
*)

(* Define helper method which add extra lines which are assumed to exist *)
Definition perpendicularDiagram (lBase lStanding : StraightLine) (pMeeting : Point) : Prop :=
  intersection lBase lStanding pMeeting
  /\ isExtremal lStanding pMeeting
  /\ not (isExtremal lBase pMeeting) 
  /\ not (colinear lBase lStanding)
  
(* To pove we can form an angle need to prove that 

Definition rightAngle (a : Angle) : Prop :=
  ex (
