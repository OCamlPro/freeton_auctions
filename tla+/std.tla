---- MODULE std ----
    EXTENDS Integers, TLC, Sequences

    assert(Predicate, Msg) ==
        Assert(Predicate, "Assertion failure: " \o Msg)

    assert_all(Predicates) ==
        \A Pair \in Predicates : assert(Pair[1], Pair[2])

    min(i,j) == IF i < j THEN i ELSE j
    
    max(i,j) == IF i > j THEN i ELSE j

    Hash(i) == i

    ---- MODULE auction ----

    unsafe_bid(bidder, amount) == <<bidder, amount>>

    bid(bidder, amount) ==
        LET check ==
            assert_all
            (<<
                <<bidder > 0, "Incorrect bidder " \o bidder>>,
                <<amount > 0, "Incorrect amount " \o amount>>
            >>) IN 
        unsafe_bid(bidder, amount)
    
    (* No winner *)
    no_winner == unsafe_bid(0,0)

    bidder(b) == b[1]
    amount(b) == b[2]

    has_no_winner(winner) == bidder(winner) = 0
    has_a_winner(winner) == ~(has_no_winner(winner))


    bidder_set(bidders) == 1..bidders

    ====

    auction == INSTANCE auction
====