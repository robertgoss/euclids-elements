(** * Book I: Definitions and Axioms *)

Module Euclid.

(** ** Definitions *)

(** **** Coq note  
We make a few pre-emptive definitions about the notion of a magnitude which is a quantity with a notion of size comparison and addition. 
With the natural notations *)
Definition Magnitude : Type. Admitted.

Definition add : Magnitude -> Magnitude -> Magnitude. Admitted.
Definition greaterEqual : Magnitude -> Magnitude -> Prop. Admitted.

Notation "x + y" := (add x y)  
                       (at level 50, left associativity) 
                       : magnitude_scope.
Notation "x <= y" := (greaterEqual x y)  
                       (at level 70, no associativity) 
                       : magnitude_scope.
(**
-1. A [Point] is that which has position, but no [Magnitude]
*) 
Definition Point : Type. Admitted.
(**
-2. A [Line] is that which has length without breadth 
*)
Definition Line : Type. Admitted.
(**
-3. The [extremities] of a [Line] are [Point]s, and the [intersection] of two [Line]s is a [Point]. 
*)
Inductive DistinctPoints : Type :=
  distinctPoints (p1 p2 : Point) : p1 <> p2 -> DistinctPoints.

Definition extremities : Line -> DistinctPoints. Admitted.
Definition intersection : Line -> Line -> Point -> Prop. Admitted.
(** 
-4. A [StraightLine] is that which evenly between its extreme points. Any portion cut off from a straight line is called a segment of it.
*)
Definition StraightLine : Type. Admitted.
Definition line : StraightLine -> Line. Admitted.

Definition lineBetweenExtreme : DistinctPoints -> StraightLine. Admitted.

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

Definition planeProp (s : Surface) : Prop :=
  forall (p1 p2 : Point) (dist : p1 <> p2)
         (_ : pointOnSurface p1 s) (_ : pointOnSurface p2 s),
    lineOnSurface (line (lineBetweenExtreme (distinctPoints p1 p2 dist))) s.

Inductive Plane : Type :=
  plane (s : Surface) : planeProp s -> Plane.

(**
-8. A plane angle is the inclination of two [Line]s to each other which meet together, but are not in the same direction.
(Definition 8. is not required in Euclid's geometry the only angles employed by him being those formed by [StraightLine]s.
*)

(**
-9. A plane rectilinear angle is the inclination of two [StraightLine]s to one another, which meet together, but are not in the same [StraightLine].
The [Point] at which the [StraightLine] meet is called the vertex of the angle, and the [StraightLine]s themselves the arms of the angle. 
*)
Definition notColinear (l1 l2 : StraightLine) : Prop :=
  forall (l : StraightLine), ~(segmentOf l1 l) \/ ~(segmentOf l2 l).

Inductive Angle (l1 : StraightLine) (p : Point) (l2 : StraightLine) : Type :=
  angle : notColinear l1 l2 -> intersection (line l1) (line l2) p -> Angle l1 p l2.

(**** Note.
When there are several [Angle]s at one [Point] each is expressed by three letters, of which the letter that refers to the vertex is put between the other two.
Thus the angle contained by the [StraightLine]s OA, OB is named the angle AOB or BOA; and the angle contained by OA, OC is named the angle AOC or COA.
But if there is only one [Angle] at a [Point], it may be expressed by a single letter, as the angle at O.

Of the two [StraightLine]s OB, OC shewn in the adjoining diagram, we recognize that OC is more inclined than OB to the [StraightLine] OA : this we express by saying that the [Angle] AOC is greater thn the angle AOB.
Thus the [Angle] must be regarded as having a [Magnitude].
*)
Definition angleMagnitude (l1 l2 : StraightLine) (p : Point) : Angle l1 p l2 -> Magnitude. Admitted.

(**
It must be carefully observed that the size of an angle in no way depends on the length of its arms, but only on their inclination to one another.
The angle AOC is the sum of the angles AOB and BOC; and AOB is the difference of the angles AOC and BOC.
*)

Definition angleSum (l1 l2 l3 : StraightLine) (p : Point) : Angle l1 p l2 -> Angle l2 p l3 -> Angle l1 p l3 -> Prop. Admitted.
Definition angleDiff (l1 l2 l3 : StraightLine) (p : Point) : Angle l1 p l2 -> Angle l1 p l3 -> Angle l2 p l3 -> Prop. Admitted.

Definition angleGreaterEqual (l1 l2 l3 : StraightLine) (p : Point) : Angle l1 p l2 -> Angle l2 p l3 -> Prop. Admitted.
Notation "x <= y" := (angleGreaterEqual x y)  
                       (at level 70, no associativity) 
                       : angle_scope.

(** Note in book type later *)

(** 
[Angle]s which lie on either side of a common arm are called [adjacent] angles.
For example, when one [StraightLine] OC is drawn from a [Point] in another [StraightLine] AB, the angles COA, COB are adjacent.

When two [StraightLine]s, such as AB, CD, cross one another at E the two [Angle]s CEA, BED are said to be vertically opposite.
The two [Angle]s CEB, AED are also vertically opposite to one another.
*)

