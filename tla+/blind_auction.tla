---- MODULE blind_auction ----

    EXTENDS Integers

    CONSTANTS 
        bidders,
        max_time_bid,
        max_time_reveal,
        max_bid

    VARIABLES 
        time,
        hidden_bids,
        revealed_bids

    Hash(i) == i
    max(i,j) == IF i > j THEN i ELSE j
    
    vars == <<time, hidden_bids, revealed_bids>>

    Init == 
        /\ time = 0
        /\ hidden_bids = {}
        /\ revealed_bids = {}

    reveal_time == 
        /\ time >= max_time_bid 
        /\ time < max_time_reveal

    time_has_passed ==
        time = max_time_bid + max_time_reveal
    
    bidding(bidder, bid) == 
        /\ revealed_bids' = revealed_bids \union {<<bidder, bid>>}
        /\ UNCHANGED hidden_bids
    
    bid == 
        \E bidder \in 1..bidders: 
        \E bid \in 0..max_bid :
            bidding(bidder, Hash(bid))

    revealing(bidder, val) == 
        \E b \in hidden_bids:
        /\ b[1] = bidder 
        /\ b[2] = Hash(val)
        /\ hidden_bids' = hidden_bids \ {b}
        /\ revealed_bids' = revealed_bids \union {<<bidder, val>>}

    reveal ==
        \E bidder \in 1..bidders:
        \E val \in Int:
        revealing(bidder, val)

    no_action == UNCHANGED <<hidden_bids, revealed_bids>>
    
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