---- MODULE english_reverse_auction ----

    EXTENDS Integers

    CONSTANTS 
        starting_price, (* The auction starting price *) 
        max_tick, (* After max_tick, the auction ends *)
        max_time, (* After max_time, the auction ends *)
        sellers (* The number of sellers *)


    VARIABLES 
        current_price, (* The current auction price *)
        lowest_seller, (* The lowest seller *)
        tick, (* The current tick *)
        time (* The current time *)

    vars == <<current_price, lowest_seller, tick, time>>

    Init == 
        /\ current_price = starting_price
        /\ lowest_seller = 0 (* Not a real bidder *)
        /\ tick = 0
        /\ time = 0

    time_has_passed == time = max_time \/ tick = max_tick
    
    time_passes == time' = time + 1

    bid(seller, price) ==
        /\ (price < current_price) 
        /\ current_price' = price
        /\ lowest_seller' = seller
        /\ tick' = 0

    can_bid ==
        \E b \in 1..sellers:
        \E p \in 1..starting_price:
            bid(b,p)

    no_bid == 
        /\ tick' = tick + 1
        /\ UNCHANGED <<current_price, lowest_seller>>


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
        /\ lowest_seller \in 0..sellers
        /\ current_price \in 0..starting_price

    never_lower == current_price' >= current_price

====