pragma ton-solidity >=0.44;

import "Constants.sol";
import "interfaces/IAuction.sol";
import "interfaces/IProcessWinner.sol";
import "Buildable.sol";
import "interfaces/IBidBuilder.sol";
import "interfaces/IBid.sol";

// The main contract for the Dutch and Reverse Dutch Auction
// https://en.wikipedia.org/wiki/Dutch_auction

abstract contract VDutchAuction is Constants, Buildable {
    address static s_owner; // The owner of the auction
    uint256 static s_limit_price; // The limit price
    uint256 static s_auction_start; // The starting time
    uint256 static s_id; // Unique ID of the auction    
    address static s_bid_builder_address; // The address of the bid builder
    address static s_winner_processor_address; // The Winner processor
    uint256 static s_bidding_time; // The duration of the bidding phase
    uint256 static s_reveal_time; // The duration of the revelation phase
    uint256 static s_payment_time; // The duration of the payment phase for each winner
    uint128 static s_entry_amount; // The amount of crystals to transfer to this contract for being allowed to participate.

    uint32 m_num_revealed_bids;
    BidderLinkedList m_revealed_bids; // The valid bids. TODO: as a contract linked list

    constructor() public{
        tvm.accept();
        s_auction_start = now;
        m_num_revealed_bids = 0;
    }

    function biddingPhase() public view responsible returns(bool) {
        return (now <= s_auction_start + s_bidding_time);
    }

    function revealPhase() public view responsible returns(bool) {
        return (!(biddingPhase()) && 
                now <= s_auction_start + s_bidding_time + s_reveal_time);
    }

    function paymentPhase public view responsible returns(bool) {
        return (!(revealPhase()) &&
                now <= s_auction_start + s_bidding_time + s_reveal_time + m_valid_bids * s_payment_time
        );
    }

    // There is a maximum of 'n' payment phases, where 'n' is the number of revealed valid bids.  
    function paymentPhaseOf() internal view returns(optional(Bidder)){
        uint256 payment_time_spent = now - (s_auction_start + s_bidding_time + s_reveal_time);
        optional(Bidder) b;
        if (paiment_time_spend >= 0) {
            uint32 pos = paiment_time_spend / s_payment_time;
            if (pos < m_num_revealed_bids){
                b.set(m_revealed_bids[pos]);
            }
        }
        return b;
    }

    function bid(uint256 commitment) public view {
        require (msg.value >= s_entry_amount, E_VALUE_TOO_LOW);
        IBidBuilder(s_bid_builder_address).deployBid(commitment);
    }

    function validateBid(Bidder auction_winner) external override onlyFrom(s_bid_builder_address) {
        m_revealed_bids.add()
    }


}