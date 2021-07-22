pragma ton-solidity >=0.44;

import "Constants.sol";
import "interfaces/IAuction.sol";
import "interfaces/IProcessWinner.sol";
import "Buildable.sol";
import "interfaces/IBidBuilder.sol";
import "interfaces/IBid.sol";

// The main contract for the Dutch and Reverse Dutch Auction
// https://en.wikipedia.org/wiki/Dutch_auction

abstract contract VDutchAuction is Constants, Buildable, IAuction {
    address static s_owner; // The owner of the auction
    uint256 static s_starting_price; // The starting price
    uint256 static s_auction_start; // The starting time
    uint256 static s_limit_price; // The limit price
    uint256 static s_price_delta; // The price decrement over time
    uint256 static s_time_delta; // The time after which the time
    uint256 static s_id; // Unique ID of the auction
    address static s_bid_builder_address; // The address of the bid builder
    address static s_winner_processor_address; // The Winner processor

    constructor() public{
        tvm.accept();
        s_auction_start = now;
    }

    // This funcion will calculate the current price given the starting price
    // and its evolution through time.
    // * Forward : the current price starts with s_starting_price and is 
    //   decremented of s_price_delta after s_time_delta. 
    //   Its minimum is s_limit_price.
    //   Returns true if the value in argument is higher or equal to the 
    //   current price.
    //
    // * Backward : the current price starts with s_starting_price and is 
    //   incremented of s_price_delta after s_time_delta. 
    //   Its maximum is s_limit_price.
    //   Returns true if the value in argument is higher or equal to the 
    //   current price.
    function betterPriceThanCurrent(uint256) internal virtual returns(bool);

    // Processes the winner
    // In Forward, transfer the vault content to the auctioneer
    // In Reverse, transfer some of the vault content to the seller
    function processWinner(Bidder) internal virtual;

    // Validates a bid.
    // In the Dutch version, a valid bid automatically ends the auction
    function validateBid(Bidder auction_winner) external override onlyFrom(s_bid_builder_address) {
        tvm.accept ();
        if (betterPriceThanCurrent(auction_winner.bid)){
            emit Winner(auction_winner.bidder, auction_winner.bid);
            processWinner(auction_winner);
        } else {
            emit InvalidBid();
        }
    }

    // Starts the bid process
    // In Forward, commitment = amount of bid
    // In Reverse, commitment = address
    // In Blind, commitment = hash(salt, amount)
    // In Blind Reverse, commitment = hash(salt, address)
    function bid(uint256 commitment) external override {
        IBidBuilder(s_bid_builder_address).
          deployBid{value: 0, flag: 128}(commitment);
    }
    
    // Ends an auction.
    // If no bid has been done and the limit price is the best price,
    // the auction can be terminated.
    function endAuction() external override {
        tvm.accept();
        if (betterPriceThanCurrent(s_limit_price)) {
            emit NoWinner();
            IProcessWinner(s_winner_processor_address).acknowledgeNoWinner{value:0, flag: 128}();
            selfdestruct(s_owner);
        }
    }
}