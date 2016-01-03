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
Definition intersection : Line -> Line -> option Point. Admitted.
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

