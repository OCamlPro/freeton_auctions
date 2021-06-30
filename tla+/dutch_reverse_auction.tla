---- MODULE dutch_reverse_auction ----

    EXTENDS Integers, std

    CONSTANTS 
        starting_price, (* The auction starting price *) 
        limit_price, (* The minimal price the seller will accept *)
        price_delta, (* The price increment for each tick*)
        time_delta

    VARIABLES 
        winner, (* The winner *)
        time, (* time *)
        current_price_var (* Useless variable, used for readable cexs *)

    vars == <<winner, time, current_price_var>>

    current_price ==
        IF auction!has_a_winner(winner)
        THEN auction!amount(winner)
        ELSE
          LET delta == time \div time_delta IN
          min(starting_price + delta * price_delta, limit_price)

    Init == 
        /\ starting_price < limit_price
        /\ winner = auction!no_winner
        /\ time = 0
        /\ current_price_var = starting_price

    time_has_passed == 
        \/ auction!has_a_winner(winner)
        \/ (
            /\ current_price = limit_price
            /\ (time + 1) % time_delta = 0
           )

    time_passes == time' = time + 1

    bid == 
        /\ winner'= auction!bid(1, current_price)
        /\ UNCHANGED current_price_var
    
    no_bid == 
        /\ UNCHANGED winner
        /\ IF (time' % time_delta = 0)
           THEN 
             current_price_var' = 
             min(limit_price, current_price_var + price_delta)
           ELSE 
             UNCHANGED current_price_var
    
    Next == 
        IF time_has_passed
        THEN UNCHANGED vars 
        ELSE /\ time_passes
             /\ \/ no_bid
                \/ bid

    type_check ==
        current_price_var = current_price
    
    test == <>(auction!has_a_winner(winner))
====