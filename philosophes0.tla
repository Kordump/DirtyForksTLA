---------------- MODULE philosophes0 ----------------
(* Dining philosophers problem. Chandy/Misra solution. *)

EXTENDS Naturals

(* Number of philosophers. *)
CONSTANT N

(* The fork i is between the philosopher (i+N-1)%N and the philosopher i. *)
Philos == 0..N-1
Forks  == 0..N-1

(* Gives the left ident or the right relative to the ident i. *)
get_left_ident(i)  == (i+N-1)%N
get_right_ident(i) == (i+1)%N

(* Philosophers' states. *)
Thinking == "T"
Hungry   == "H"
Eating   == "E"

(* Forks' fairness states. *)
Clean == "C"
Dirty == "D"

(* Forks' positions between a pair of philosophers. *)
Left  == "L"
Right == "R"

VARIABLES
    state,       (* Philosophers' state vector *)
    forks_state, (* Forks' fairness state vector. *)
    forks_side   (* Forks' positions in a pair vector. *)

(* Boolean values - Check philosopher's state. *)
is_eating(i) ==
    state[i] = Eating
is_hungry(i) ==
    state[i] = Hungry
is_thinking(i) ==
    state[i] = Thinking

(* Boolean answering this question:
    Being in position i, is my side fork clean ? *)
is_clean(side, i) ==
    \/ (/\ side = Left
        /\ forks_state[get_left_ident(i)] = Clean)
    \/ (/\ side = Right
        /\ forks_state[i] = Clean)

(* Boolean answering this question:
    Being in position i, is my side fork dirty ? *)
is_dirty(side, i) ==
    \/ (/\ side = Left
        /\ forks_state[get_left_ident(i)] = Dirty)
    \/ (/\ side = Right
        /\ forks_state[i] = Dirty)

(* Boolean answering this question:
    Being in position i, do I need to ask to my side neighbour his fork ? *)
must_request_fork(side, i) ==
    \/ (/\ side = Left
        /\ forks_side[get_left_ident(i)] /= Right)
    \/ (/\ side = Right
        /\ forks_side[i] /= Left)

(* Type Invariant *)
TypeInvariant ==
    [] (/\ state \in [Philos -> {Hungry, Thinking, Eating}]
        /\ forks_state \in [Forks -> {Clean, Dirty}]
        /\ forks_side  \in [Forks -> {Left,  Right}])

(* Mutual Exclusion *)
MutualExclusion ==
    (\A i \in {j \in Philos: state[j] = Eating}:
        \/ ~is_eating(get_left_ident(i))
        \/ ~is_eating(get_right_ident(i)))

(* Individual vivacity *)
IndividualVivacity == (\A i \in Philos: is_hungry(i) ~> is_eating(i))

(* Global vivacity *)
GlobalVivacity == (\E i \in Philos: is_hungry(i)) ~> (\E j \in Philos: is_eating(j))

----------------------------------------------------------------

(* Initial state: Forks' distribution must be asymetric. *)
(* → A symetric system leads to a deadlock, an asymetric one stays asymetric (without deadlock). *)
Init ==
    /\ state = [i \in Philos |-> Thinking]
    /\ forks_state = [i \in Forks |-> Dirty]
    /\ forks_side = [[i \in Forks |-> Left ] EXCEPT ![0] = Right]

(* demand: When I think, I get hungry. *)
demand(i) ==
    /\ is_thinking(i)
    /\ state' = [state EXCEPT ![i] = Hungry]
    /\ UNCHANGED forks_state
    /\ UNCHANGED forks_side

(* request_left_fork: I don't have my left fork. I request it from my left neighbour if it's dirty, then I clean it. *)
request_left_fork(i) ==
    /\ is_hungry(i)
    (* I have to request my left fork. *)
    /\ must_request_fork(Left, i)
    (* I ask my neighbour only if his fork is dirty. *)
    /\ is_dirty(Left, i)
    (* I take my neighbour's fork and clean it. *)
    /\ forks_side'  = [forks_side  EXCEPT ![get_left_ident(i)] = Right]
    /\ forks_state' = [forks_state EXCEPT ![get_left_ident(i)] = Clean]
    /\ UNCHANGED state

(* request_right_fork: I don't have my right fork. I request it from my right neighbour if it's dirty, then I clean it. *)
request_right_fork(i) ==
    /\ is_hungry(i)
    (* I have to request my right fork. *)
    /\ must_request_fork(Right, i)
    (* I ask my neighbour only if his fork is dirty. *)
    /\ is_dirty(Right, i)
    (* I take my neighbour's fork and clean it. *)
    /\ forks_side' = [forks_side EXCEPT ![i] = Left]
    /\ forks_state' = [forks_state EXCEPT ![i] = Clean]
    /\ UNCHANGED state

(* eat: I can only eat if I had my forks. *)
eat(i) ==
    /\ is_hungry(i)
    (* My neighbours aren't eating now. *)
    (* (Ensure that a fork can't be used in two different places at the same time. *)
    /\ ~is_eating(get_left_ident(i))
    /\ ~is_eating(get_right_ident(i))
    (* I've already got my forks. *)
    /\ ~must_request_fork(Left, i)
    /\ ~must_request_fork(Right, i)
    (* Unchanged forks. *)
    /\ UNCHANGED forks_state
    /\ UNCHANGED forks_side
    (* I eat. *)
    /\ state' = [state EXCEPT ![i] = Eating]

(* think: I'm a stuttering thinker, otherwise I just stopped eating. *)
think(i) ==
    /\ ((* My forks gets dirty if I just stopped eating. *)
        /\ is_eating(i)
        /\ ((* I clean and give my forks to my hungry neighbours. *)
            /\ forks_state' = [forks_state EXCEPT
                ![get_left_ident(i)] = IF is_hungry(get_left_ident(i))  THEN Clean ELSE Dirty,
                ![i]                 = IF is_hungry(get_right_ident(i)) THEN Clean ELSE Dirty]
            /\ forks_side' = [forks_side EXCEPT
                ![get_left_ident(i)] = IF is_hungry(get_left_ident(i))  THEN Left  ELSE @,
                ![i]                 = IF is_hungry(get_right_ident(i)) THEN Right ELSE @]
           )
       )
    /\ state' = [state EXCEPT ![i] = Thinking]

(* Weak fairness only. *)
Fairness ==
    \A i \in Philos:
        /\ WF_<<state, forks_state, forks_side>>(eat(i))
        /\ WF_<<state, forks_state, forks_side>>(think(i))
        /\ WF_<<state, forks_state, forks_side>>(request_left_fork(i))
        /\ WF_<<state, forks_state, forks_side>>(request_right_fork(i))

Next ==
  \E i \in Philos:  \/ eat(i)
                    \/ think(i)
                    \/ demand(i)
                    \/ request_left_fork(i)
                    \/ request_right_fork(i)

Spec ==
  /\ Init
  /\ [][Next]_<<state, forks_state, forks_side>>
  /\ Fairness

================================
