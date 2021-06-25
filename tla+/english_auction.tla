---- MODULE english_auction ----

    EXTENDS Integers

    CONSTANTS 
        starting_price, (* The auction starting price *) 
        max_tick, (* After max_tick, the auction ends *)
        max_time, (* After max_time, the auction ends *)
        bidders, (* The number of bidders (only required for TLA) *)
        max_bid (* The maximal bid (only required for TLA) *)


    VARIABLES 
        current_price, (* The current auction price *)
        highest_bidder, (* The highest bidder *)
        tick, (* The current tick (only required for TLA) *)
        time (* The current time (only required for TLA)  *)

    vars == <<current_price, highest_bidder, tick, time>>

    Init == 
        /\ current_price = starting_price
        /\ highest_bidder = 0 (* Not a real bidder *)
        /\ tick = 0
        /\ time = 0

    time_has_passed == time = max_time \/ tick = max_tick
    
    time_passes == time' = time + 1

    bid(bidder, price) ==
        /\ (price > current_price) 
        /\ current_price' = price
        /\ highest_bidder' = bidder
        /\ tick' = 0

    can_bid ==
        \E b \in 1..bidders:
        \E p \in 1..max_bid:
            bid(b,p)

    no_bid == 
        /\ tick' = tick + 1
        /\ UNCHANGED <<current_price, highest_bidder>>


    Next == 
        IF time_has_passed
        THEN UNCHANGED vars 
        ELSE /\ time_passes
             /\ \/ no_bid
                \/ can_bid

    
    (* Invariants *)
    type_check ==
        /\ tick \in 0..max_tick
        /\ time \in 0..max_time
        /\ highest_bidder \in 0..bidders
        /\ current_price \in starting_price..(starting_price + time * max_bid)

    never_lower == current_price' >= current_price

====