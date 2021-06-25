---- MODULE blind_auction ----

    EXTENDS Integers, std

    CONSTANTS 
        bidders,
        max_time_bid,
        max_time_reveal,
        max_bid

    VARIABLES 
        time,
        hidden_bids, 
        winner
    
    vars == <<time, hidden_bids, winner>>

    Init == 
        /\ time = 0
        /\ hidden_bids = {}
        /\ winner = <<0,0>>

    bidder_set == 1 .. bidders

    reveal_time == 
        /\ time >= max_time_bid 
        /\ time < max_time_reveal

    time_has_passed ==
        time = max_time_bid + max_time_reveal
    
    bidding(bidder, bid) == 
        hidden_bids' = hidden_bids \union {Hash(<<bidder, bid>>)}
    
    bid == 
        /\ UNCHANGED winner 
        /\ \E bidder \in bidder_set: 
           \E bid \in 0..max_bid :
              bidding(bidder, Hash(bid))

    revealing(bidder, val) == 
        \E b \in hidden_bids:
        /\ b = Hash(<<bidder, val>>)
        /\ hidden_bids' = hidden_bids \ {b}
        /\ winner' = 
            IF winner[1] = 0 \/ winner[2] < val
            THEN <<b[1], val>> 
            ELSE winner

    reveal ==
        \E bidder \in 1..bidders:
        \E val \in Int:
        revealing(bidder, val)

    no_action == UNCHANGED <<hidden_bids, winner>>
    
    time_passes == time' = time + 1

    Next ==
        /\ time_passes
        /\
            IF time_has_passed
            THEN UNCHANGED vars 
            ELSE IF reveal_time 
            THEN \/ reveal
                 \/ no_action
            ELSE (* Bidding time *)
                 \/ bid
                 \/ no_action 

====