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
Definition notColinear (l1 l2 : StraightLine) : Prop :=
  forall (l : StraightLine), ~(segmentOf l1 l) \/ ~(segmentOf l2 l).

Inductive Angle : Type :=
  angle (l1 l2 : StraightLine) (p : Point) : 
       notColinear l1 l2 -> isExtremal (line l1) p -> isExtremal (line l2) p -> Angle.

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

Definition angleSum (a1 a2 asum : Angle) (l1 l2 l3 : StraightLine) (p : Point) : 
           p = vertex a1 -> p = vertex a2 -> p = vertex asum ->
           (l1,l2) = arms a1 -> (l2,l3) = arms a2 -> (l1,l3) = arms asum ->
           Prop.
Admitted.

Definition angleGreaterEqual (a1 a2 : Angle) (l1 l2 l3 : StraightLine) (p : Point) : 
           p = vertex a1 -> p = vertex a2 -> 
           (l1,l2) = arms a1 -> (l2,l3) = arms a2 -> Prop. 
Admitted.

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


