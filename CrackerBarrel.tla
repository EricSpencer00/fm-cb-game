---------------------------- MODULE CrackerBarrel ----------------------------
EXTENDS Naturals, FiniteSets, TLC

(***************************************************************************)
(* Explicit positions for the 4-row triangular peg board                   *)
(***************************************************************************)

InitialEmpty == <<2, 1>>

Positions ==
  { <<1,1>>,
    <<2,1>>, <<2,2>>,
    <<3,1>>, <<3,2>>, <<3,3>>,
    <<4,1>>, <<4,2>>, <<4,3>>, <<4,4>> }

(***************************************************************************)
(* Explicit list of all legal triples (start, over, dest) for this board   *)
(***************************************************************************)

Moves ==
  {
  (* Horizontal row 3 *)
    [ start |-> <<3,1>>, over |-> <<3,2>>, dest |-> <<3,3>> ],
    [ start |-> <<3,3>>, over |-> <<3,2>>, dest |-> <<3,1>> ],

  (* Horizontal row 4 *)
    [ start |-> <<4,1>>, over |-> <<4,2>>, dest |-> <<4,3>> ],
    [ start |-> <<4,3>>, over |-> <<4,2>>, dest |-> <<4,1>> ],
    [ start |-> <<4,2>>, over |-> <<4,3>>, dest |-> <<4,4>> ],
    [ start |-> <<4,4>>, over |-> <<4,3>>, dest |-> <<4,2>> ],

  (* Down-left direction *)
    [ start |-> <<1,1>>, over |-> <<2,1>>, dest |-> <<3,1>> ],
    [ start |-> <<3,1>>, over |-> <<2,1>>, dest |-> <<1,1>> ],

    [ start |-> <<2,1>>, over |-> <<3,1>>, dest |-> <<4,1>> ],
    [ start |-> <<4,1>>, over |-> <<3,1>>, dest |-> <<2,1>> ],

    [ start |-> <<2,2>>, over |-> <<3,2>>, dest |-> <<4,2>> ],
    [ start |-> <<4,2>>, over |-> <<3,2>>, dest |-> <<2,2>> ],

  (* Down-right direction *)
    [ start |-> <<1,1>>, over |-> <<2,2>>, dest |-> <<3,3>> ],
    [ start |-> <<3,3>>, over |-> <<2,2>>, dest |-> <<1,1>> ],

    [ start |-> <<2,1>>, over |-> <<3,2>>, dest |-> <<4,3>> ],
    [ start |-> <<4,3>>, over |-> <<3,2>>, dest |-> <<2,1>> ],

    [ start |-> <<2,2>>, over |-> <<3,3>>, dest |-> <<4,4>> ],
    [ start |-> <<4,4>>, over |-> <<3,3>>, dest |-> <<2,2>> ]
  }

(***************************************************************************)
(* Legal move and state variables                                          *)
(***************************************************************************)

LegalMove(m, S) ==
  /\ m \in Moves
  /\ m.start \in S
  /\ m.over \in S
  /\ m.dest \notin S

VARIABLES Pegs

Init ==
  /\ InitialEmpty \in Positions
  /\ Pegs = Positions \ { InitialEmpty }

MakeMove ==
  \E m \in Moves :
    /\ LegalMove(m, Pegs)
    /\ Pegs' = (Pegs \ { m.start, m.over }) \cup { m.dest }

Vars == << Pegs >>

Next == MakeMove

(***************************************************************************)
(* Helpful predicates for TLC / specs                                       *)
(***************************************************************************)

PegCount(S) == Cardinality(S)

PegCountBounds == PegCount(Pegs) \in 0..9

OneLeft(S) == PegCount(S) = 1

TypeOK == Pegs \subseteq Positions

Inv == TypeOK

(***************************************************************************)
(* Specification and liveness                                              *)
(***************************************************************************)

Spec == Init /\ [][Next]_Vars

WinEventually == <> (OneLeft(Pegs))

==============================================================================
