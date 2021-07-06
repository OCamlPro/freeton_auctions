---- MODULE english_auction ----

    EXTENDS Integers, std

    CONSTANTS 
        starting_price, (* The auction starting price *) 
        max_tick, (* After max_tick, the auction ends *)
        max_time, (* After max_time, the auction ends *)
        num_bidders, (* The number of bidders (only required for TLA) *)
        max_bid (* The maximal bid (only required for TLA) *)


    VARIABLES
        highest_bidder, (* The highest bidder *)
        tick, (* The current tick (only required for TLA) *)
        time (* The current time (only required for TLA)  *)

    vars == <<highest_bidder, tick, time>>

    Init == 
        /\ highest_bidder = auction!unsafe_bid(0, starting_price)
        /\ tick = 0
        /\ time = 0

    time_has_passed == 
        \/ time = max_time 
        \/ /\ tick = max_tick
           /\ auction!has_a_winner(highest_bidder)
    
    time_passes == time' = time + 1

    bid(bidder, price) ==
        /\ (price > auction!amount(highest_bidder))
        /\ highest_bidder' = auction!bid(bidder, price)
        /\ tick' = 0

    bidders == auction!bidder_set(num_bidders)

    can_bid ==
        \E b \in bidders:
        \E p \in 1..max_bid:
            bid(b,p)

    no_bid == 
        /\ tick' = tick + 1
        /\ UNCHANGED <<highest_bidder>>

    Next == 
        IF time_has_passed
        THEN UNCHANGED vars 
        ELSE /\ time_passes
             /\ \/ no_bid
                \/ can_bid

    (* Invariants *)
    type_check ==
        /\ \/ tick \in 0..max_tick
           \/ auction!has_no_winner(highest_bidder)
        /\ time \in 0..max_time
        /\ auction!bidder(highest_bidder) \in {0} \union bidders
        /\ auction!amount(highest_bidder) \in starting_price..(starting_price + time * max_bid)

    never_lower == auction!amount(highest_bidder') >= auction!amount(highest_bidder)
====