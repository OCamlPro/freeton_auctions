---- MODULE blind_auction ----

    EXTENDS Integers, Sequences, std

    CONSTANTS 
        max_time_bid, (* The max time the bidders can bid *)
        max_time_reveal, (* The max time bidders can reveal *)
        max_time_pay, (* The max time a winner has to pay.
                         If he misses it, he loses the auction. *)
        bidders, (* The set of bidders (only required for TLA+) *)
        max_bid (* The maximal bid (only required for TLA+) *)

    VARIABLES 
        time, (* The time (only required for TLA+) *)
        hidden_bids, (* The hidden bids*)
        valid_bids, (* The validated bids, sorted by the amount (decr) *)
        winner, (* The winner (only required for TLA+) *)
        curr_state (* Current state, only for TLA+ *)
    
    vars == <<time, hidden_bids, valid_bids, winner, curr_state>>

    Init == 
        /\ time = 0
        /\ hidden_bids = {}
        /\ valid_bids = <<>>
        /\ winner = <<0,0>>
        /\ curr_state = "Init"

    (* Adds a bid, in a sorted way *)
    add_valid(b) ==
        IF Len(valid_bids) = 0 
        THEN valid_bids' = <<b>>
        ELSE IF valid_bids[1][2] > b[2]
        THEN valid_bids' = <<b>> \o valid_bids
        ELSE
        \E i \in DOMAIN(valid_bids):
        \A j \in 1..i:
        /\ valid_bids[j][2] > b[2]
        /\ valid_bids'[j] = valid_bids[j]
        /\ valid_bids'[i+1] = b
        /\ \A k \in (i+1)..Len(valid_bids):
            /\ valid_bids[k][2] <= b[2]
            /\ valid_bids'[k+1] = valid_bids[k]
    
    bidder_set == 1 .. bidders

    reveal_time == 
        /\ time >= max_time_bid 
        /\ time < max_time_bid + max_time_reveal

    claim_time ==
        /\ time >=
            max_time_bid + 
            max_time_reveal
        /\ winner = <<0,0>>

    time_has_passed ==
        \/ /\ time >=
               max_time_bid + 
               max_time_reveal
           /\ valid_bids = <<>>
        \/ ~(winner = <<0,0>>) 
    
    bidding(bidder, bid) == 
        hidden_bids' = hidden_bids \union {Hash(<<bidder, bid>>)}
    
    bid == 
        /\ UNCHANGED <<winner, valid_bids>> 
        /\ \E bidder \in bidder_set: 
           \E bid \in 0..max_bid :
              bidding(bidder, Hash(bid))

    revealing(bidder, val) == 
        \E b \in hidden_bids:
        /\ b = Hash(<<bidder, val>>)
        /\ hidden_bids' = hidden_bids \ {b}
        /\ add_valid(<<bidder, val>>)
        /\ UNCHANGED winner

    reveal ==
        \E bidder \in bidder_set:
        \E val \in 0..max_bid:
        revealing(bidder, val)

    claiming(bidder) == 
        /\ bidder = valid_bids[1][1] 
        /\ winner' = valid_bids[1]
        /\ valid_bids' = <<>>
        /\ UNCHANGED hidden_bids
    
    claim == \E b \in bidder_set: claiming(b)

    no_action == UNCHANGED <<hidden_bids, winner, valid_bids>>

    no_claim == 
        IF (time - max_time_bid - max_time_reveal) % max_time_pay = 0
        THEN 
            /\ valid_bids' = Tail(valid_bids)
            /\ UNCHANGED <<hidden_bids, winner>>
        ELSE no_action
    
    time_passes == time' = time + 1

    Next ==
            IF time_has_passed
            THEN UNCHANGED vars 
            ELSE 
            /\ time_passes
            /\  IF reveal_time 
                THEN
                 /\ curr_state' = "Reveal"
                 /\ \/ reveal
                    \/ no_action
                ELSE IF claim_time
                THEN 
                 /\ curr_state' = "Claim"
                 /\ \/ claim 
                    \/ no_claim
                ELSE(* Bidding time *) 
                 /\ curr_state' = "Bidding"
                 /\ \/ bid
                    \/ no_action

    prop == <>(valid_bids = <<<<1,1>>>>)
====