(** * Book I: Definitions and Axioms *)

(** ** Definitions 

-1. A [Point] is that which has position, but no [Magnitude]
*) 
Definition Point : Type. Admitted.
Definition Magnitude : Type. Admitted.
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
The [Point] at which the [StraightLine] meet is called the [Vertex] of the angle, and the [StraightLine]s themselves the [Arm]s of the angle. 
*)
Definition notColinear (l1 l2 : StraightLine) : Prop :=
  forall (l : StraightLine), ~(segmentOf l1 l) \/ ~(segmentOf l2 l).

Inductive Angle (l1 l2 : StraightLine) (p : Point) : Type :=
  angle : notColinear l1 l2 -> intersection (line l1) (line l2) p -> Angle l1 l2 p.
